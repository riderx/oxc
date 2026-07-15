//! Reachability for recursively referenced function declarations (#13105).
//!
//! Reference counting removes an acyclic unused declaration once its last
//! reference disappears, but it cannot remove `function a() { b() }
//! function b() { a() }`: each function keeps the other's count non-zero.
//! For strict ES modules, this module adds the missing reachability question:
//! can executing code reach a candidate function declaration?
//!
//! Four concepts define the analysis:
//!
//! 1. **Candidates** are function declarations. Other declaration kinds keep
//!    using the ordinary resolved-reference count.
//! 2. **Ownership** comes from semantic scopes. A reference whose scope is
//!    nested in a candidate function is an edge from that function; every
//!    other reference is a root.
//! 3. **External observability** is stable metadata collected from module
//!    exports. It protects every count-based consumer, not only declaration
//!    removal, because importers can observe a binding with no in-module
//!    references.
//! 4. **Analysis runs after scoping is flushed.** Every result is derived from
//!    the settled resolved-reference lists, so AST rewrites need no parallel
//!    collection hooks or behind-the-cursor repair log.
//!
//! The graph is module-only. Script and CommonJS observability includes
//! script globals and Annex B aliases that are intentionally outside this
//! first version.

use oxc_allocator::{Allocator, BitSet, Vec as ArenaVec};
use oxc_ast::ast::*;
#[cfg(debug_assertions)]
use oxc_ast_visit::{Visit, walk::walk_function};
use oxc_ecmascript::BoundNames;
use oxc_index::IndexVec;
use oxc_semantic::Scoping;
use oxc_span::SourceType;
use oxc_syntax::{scope::ScopeId, symbol::SymbolId};

use crate::{CompressOptions, CompressOptionsUnused, TraverseCtx};

/// Whether unused-declaration removal is enabled for this program state.
/// Any direct eval marks the root scope through ancestor propagation; once
/// the eval is removed, `flush_pass_dirty` refreshes the flags and the next
/// analysis can proceed.
pub fn removal_enabled(scoping: &Scoping, options: &CompressOptions) -> bool {
    options.unused != CompressOptionsUnused::Keep
        && !scoping.root_scope_flags().contains_direct_eval()
}

/// Stable module-wide symbol facts plus the optional recursive-function graph.
///
/// This is present for every ES module: export observability also protects
/// count-based optimizations when recursive function removal is disabled.
pub struct SymbolReachability<'a> {
    externally_observable: BitSet<'a>,
    functions: Option<FunctionGraph<'a>>,
}

impl<'a> SymbolReachability<'a> {
    pub fn new(
        source_type: SourceType,
        options: &CompressOptions,
        scoping: &Scoping,
        allocator: &'a Allocator,
    ) -> Option<Self> {
        if !source_type.is_module() {
            return None;
        }
        let symbols_len = scoping.symbols_len();
        let functions = (options.unused != CompressOptionsUnused::Keep)
            .then(|| FunctionGraph::new(scoping, allocator));
        Some(Self { externally_observable: BitSet::new_in(symbols_len, allocator), functions })
    }

    #[inline]
    pub fn is_externally_observable(&self, symbol_id: SymbolId) -> bool {
        self.externally_observable.contains(symbol_id.index())
    }

    #[inline]
    pub fn function_is_dead(&self, symbol_id: SymbolId) -> bool {
        self.functions.as_ref().is_some_and(|graph| graph.is_dead(symbol_id))
    }

    fn mark_externally_observable(&mut self, symbol_id: SymbolId) {
        self.externally_observable.set_bit(symbol_id.index());
    }

    fn register_function(&mut self, function: &Function<'_>) {
        let Some(graph) = &mut self.functions else { return };
        let Some(symbol_id) = function.id.as_ref().and_then(|id| id.symbol_id.get()) else {
            return;
        };
        let Some(scope_id) = function.scope_id.get() else { return };
        graph.register(scope_id, symbol_id);
    }

    fn analyze(&mut self, scoping: &Scoping) -> bool {
        let Some(graph) = &mut self.functions else { return false };
        graph.analyze(scoping, &self.externally_observable)
    }

    #[cfg(debug_assertions)]
    fn dead_functions(&self) -> Option<&BitSet<'a>> {
        self.functions.as_ref().map(|graph| &graph.dead)
    }
}

/// Stable candidate metadata, the published result, and one private set of
/// allocation buffers reused by `analyze`.
struct FunctionGraph<'a> {
    candidates: BitSet<'a>,
    /// Direct mapping only. Owner lookup walks the current semantic parent
    /// chain, so scopes inserted or reparented after Normalize remain correct.
    function_by_scope: IndexVec<ScopeId, Option<SymbolId>>,
    dead: BitSet<'a>,
    scratch: GraphScratch<'a>,
}

impl<'a> FunctionGraph<'a> {
    fn new(scoping: &Scoping, allocator: &'a Allocator) -> Self {
        let symbols_len = scoping.symbols_len();
        let mut function_by_scope = IndexVec::with_capacity(scoping.scopes_len());
        function_by_scope.resize_with(scoping.scopes_len(), || None);
        Self {
            candidates: BitSet::new_in(symbols_len, allocator),
            function_by_scope,
            dead: BitSet::new_in(symbols_len, allocator),
            scratch: GraphScratch::new(symbols_len, allocator),
        }
    }

    fn register(&mut self, scope_id: ScopeId, symbol_id: SymbolId) {
        self.candidates.set_bit(symbol_id.index());
        self.function_by_scope[scope_id] = Some(symbol_id);
    }

    #[inline]
    fn is_dead(&self, symbol_id: SymbolId) -> bool {
        self.dead.contains(symbol_id.index())
    }

    fn owner(&self, scoping: &Scoping, scope_id: ScopeId) -> Option<SymbolId> {
        scoping
            .scope_ancestors(scope_id)
            .find_map(|scope_id| self.function_by_scope.get(scope_id).copied().flatten())
    }

    fn analyze(&mut self, scoping: &Scoping, externally_observable: &BitSet<'_>) -> bool {
        if scoping.root_scope_flags().contains_direct_eval() {
            // The minifier may remove direct eval, but must never form one.
            // Therefore a graph already carrying dead functions cannot become
            // disabled later without violating the existing direct-eval guard.
            debug_assert!(self.dead.is_empty(), "direct eval formed after liveness was published");
            self.dead.clear();
            return false;
        }

        self.scratch.reset();

        for bit in externally_observable.ones() {
            if self.candidates.contains(bit) {
                self.scratch.mark_live_root(SymbolId::from_usize(bit));
            }
        }

        for bit in self.candidates.ones() {
            let target = SymbolId::from_usize(bit);
            for &reference_id in scoping.get_resolved_reference_ids(target) {
                let reference = scoping.get_reference(reference_id);
                if let Some(owner) = self.owner(scoping, reference.scope_id()) {
                    self.scratch.edges.push((owner, target));
                } else {
                    self.scratch.mark_live_root(target);
                }
            }
        }

        self.scratch.propagate(&self.candidates);

        for bit in self.candidates.ones() {
            if !self.scratch.live.contains(bit) {
                self.scratch.next_dead.set_bit(bit);
            }
        }

        #[cfg(debug_assertions)]
        for bit in self.dead.ones() {
            assert!(
                self.scratch.next_dead.contains(bit),
                "function liveness resurrected dead symbol {bit}; transforms must not create a \
                 new path to a previously unreachable binding",
            );
        }

        let found_new_dead = self.scratch.next_dead.ones().any(|bit| !self.dead.contains(bit));
        std::mem::swap(&mut self.dead, &mut self.scratch.next_dead);
        found_new_dead
    }
}

struct GraphScratch<'a> {
    live: BitSet<'a>,
    roots: ArenaVec<'a, SymbolId>,
    edges: ArenaVec<'a, (SymbolId, SymbolId)>,
    next_dead: BitSet<'a>,
}

impl<'a> GraphScratch<'a> {
    fn new(symbols_len: usize, allocator: &'a Allocator) -> Self {
        Self {
            live: BitSet::new_in(symbols_len, allocator),
            roots: ArenaVec::new_in(&allocator),
            edges: ArenaVec::new_in(&allocator),
            next_dead: BitSet::new_in(symbols_len, allocator),
        }
    }

    fn reset(&mut self) {
        self.live.clear();
        self.roots.clear();
        self.edges.clear();
        self.next_dead.clear();
    }

    fn mark_live_root(&mut self, symbol_id: SymbolId) {
        let bit = symbol_id.index();
        if !self.live.contains(bit) {
            self.live.set_bit(bit);
            self.roots.push(symbol_id);
        }
    }

    fn propagate(&mut self, candidates: &BitSet<'_>) {
        self.edges.sort_unstable_by_key(|&(from, _)| from.index());
        while let Some(symbol_id) = self.roots.pop() {
            if !candidates.contains(symbol_id.index()) {
                continue;
            }
            let start = self.edges.partition_point(|&(from, _)| from.index() < symbol_id.index());
            for &(from, target) in &self.edges[start..] {
                if from != symbol_id {
                    break;
                }
                let bit = target.index();
                if !self.live.contains(bit) {
                    self.live.set_bit(bit);
                    self.roots.push(target);
                }
            }
        }
    }
}

/// Normalize hook: register stable function-declaration candidacy metadata.
pub fn register_function(function: &Function<'_>, ctx: &mut TraverseCtx<'_>) {
    if !function.is_declaration() {
        return;
    }
    if let Some(reachability) = &mut ctx.state.symbol_reachability {
        reachability.register_function(function);
    }
}

/// Normalize hook: record runtime bindings exposed by a named export.
pub fn register_named_export(declaration: &ExportNamedDeclaration<'_>, ctx: &mut TraverseCtx<'_>) {
    if ctx.state.symbol_reachability.is_none() {
        return;
    }

    if !declaration.export_kind.is_type()
        && let Some(inner) = &declaration.declaration
    {
        let reachability = ctx.state.symbol_reachability.as_mut().unwrap();
        inner.bound_names(&mut |ident| {
            if let Some(symbol_id) = ident.symbol_id.get() {
                reachability.mark_externally_observable(symbol_id);
            }
        });
    }

    if declaration.source.is_some() || declaration.export_kind.is_type() {
        return;
    }

    for specifier in &declaration.specifiers {
        if specifier.export_kind.is_type() {
            continue;
        }
        let ModuleExportName::IdentifierReference(local) = &specifier.local else { continue };
        let Some(reference_id) = local.reference_id.get() else { continue };
        let symbol_id = {
            let reference = ctx.scoping().get_reference(reference_id);
            (!reference.flags().is_type_only()).then(|| reference.symbol_id()).flatten()
        };
        if let Some(symbol_id) = symbol_id
            && let Some(reachability) = &mut ctx.state.symbol_reachability
        {
            reachability.mark_externally_observable(symbol_id);
        }
    }
}

/// Normalize hook: record the local binding of a named default function or
/// class declaration. `export default identifier` is intentionally excluded:
/// it exports the evaluated value, not subsequent writes to that local binding.
pub fn register_default_export(
    declaration: &ExportDefaultDeclaration<'_>,
    ctx: &mut TraverseCtx<'_>,
) {
    let symbol_id = match &declaration.declaration {
        ExportDefaultDeclarationKind::FunctionDeclaration(function) => {
            function.id.as_ref().and_then(|id| id.symbol_id.get())
        }
        ExportDefaultDeclarationKind::ClassDeclaration(class) => {
            class.id.as_ref().and_then(|id| id.symbol_id.get())
        }
        _ => None,
    };
    if let Some(symbol_id) = symbol_id
        && let Some(reachability) = &mut ctx.state.symbol_reachability
    {
        reachability.mark_externally_observable(symbol_id);
    }
}

/// Analyze the settled semantic reference lists and publish the next dead set.
/// Called only after `flush_pass_dirty`.
pub fn analyze<'a>(program: &Program<'a>, ctx: &mut TraverseCtx<'a>) -> bool {
    let _ = program;
    #[cfg(debug_assertions)]
    if let Some(dead) =
        ctx.state.symbol_reachability.as_ref().and_then(SymbolReachability::dead_functions)
    {
        debug_assert_dead_function_declarations_removed(program, ctx.scoping(), dead);
    }

    let TraverseCtx { state, scoping, .. } = ctx;
    state
        .symbol_reachability
        .as_mut()
        .is_some_and(|reachability| reachability.analyze(scoping.scoping()))
}

/// Debug contract for the set consumed by the completed pass: graph deadness
/// is used only at function-declaration sites, and every such site must be gone.
#[cfg(debug_assertions)]
fn debug_assert_dead_function_declarations_removed(
    program: &Program<'_>,
    scoping: &Scoping,
    dead: &BitSet<'_>,
) {
    if dead.is_empty() {
        return;
    }
    DeadFunctionSweep { scoping, dead }.visit_program(program);
}

#[cfg(debug_assertions)]
struct DeadFunctionSweep<'s, 'd, 'a> {
    scoping: &'s Scoping,
    dead: &'d BitSet<'a>,
}

#[cfg(debug_assertions)]
impl<'a> Visit<'a> for DeadFunctionSweep<'_, '_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: oxc_syntax::scope::ScopeFlags) {
        if function.is_declaration()
            && let Some(symbol_id) = function.id.as_ref().and_then(|id| id.symbol_id.get())
        {
            assert!(
                !self.dead.contains(symbol_id.index()),
                "dead function `{}` survived the pass that consumed its liveness bit",
                self.scoping.symbol_name(symbol_id),
            );
        }
        walk_function(self, function, flags);
    }
}
