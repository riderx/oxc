//! Reachability for recursively referenced function declarations (#13105).
//!
//! Reference counting removes an acyclic unused declaration once its last
//! reference disappears, but it cannot remove `function a() { b() }
//! function b() { a() }`: each function keeps the other's count non-zero.
//! This module adds the missing reachability question: can executing code
//! reach a candidate function declaration?
//!
//! Four concepts define the analysis:
//!
//! 1. **Candidates** are function declarations with at least one reference
//!    owned by another function declaration. Functions with only root
//!    references become count-unused when those roots disappear, so they do
//!    not need graph tracking. Other declaration kinds also keep using counts.
//! 2. **Ownership** comes from semantic scopes. A reference whose scope is
//!    nested in a candidate function is an edge from that function; every
//!    other reference is a root.
//! 3. **External observability** is stable metadata collected from module
//!    exports and Script-root bindings. It protects every count-based
//!    consumer, not only declaration removal, because code outside the current
//!    program can observe a binding with no resolved references in this AST.
//! 4. **Analysis runs after scoping is flushed.** Every result is derived from
//!    the settled resolved-reference lists, so AST rewrites need no parallel
//!    collection hooks or behind-the-cursor repair log.
//!
//! ## Transform contract
//!
//! The graph is registered once during Normalize and recomputed only when its
//! settled inputs can change. Peephole transforms must preserve three
//! invariants:
//!
//! 1. **Do not create function declarations.** A new declaration would have no
//!    entry in `function_by_scope` and therefore could not own references or
//!    become a candidate. Removing an existing declaration is supported.
//! 2. **Do not move an existing reference across function owners.** Ownership
//!    comes from `Reference::scope_id()` and the registered function-scope
//!    ancestors. A transform that changes the nearest owning function must
//!    instead drop and recreate the reference, so the dirty gate requests a
//!    new analysis.
//! 3. **Do not create a path to a function already published as dead.** Deadness
//!    is monotonic. Transforms may duplicate an already-live reference, but
//!    must not make an unreachable binding reachable; debug builds assert that
//!    a dead function never becomes live again.
//!
//! A transform that needs to violate one of these invariants must first extend
//! function registration or the dirty-analysis signal. Keeping this boundary
//! explicit is what allows the recurring traversal collector and mint log to
//! remain removed.
//!
//! ES module bindings and CommonJS top-level bindings are local to their module
//! or wrapper. Script root bindings are visible to later scripts, so root
//! function declarations are observability-only, not graph candidates; their
//! body references naturally root local candidates. Local declarations inside
//! Script functions and strict blocks can still be removed. The first eligible
//! Annex B declaration is hoisted to a var-scope symbol; any declaration left
//! with a sloppy block-scoped symbol is excluded from registration below.
//!
//! Treating a count-dead non-candidate owner's body as unreachable requires
//! that the declaration itself cannot execute without a resolved reference.
//! Registration therefore excludes Script-root declarations and sloppy Annex
//! B block functions whose runtime var-alias write is not fully represented by
//! their block-scoped symbol.

use oxc_allocator::{Allocator, BitSet, GetAllocator, Vec as ArenaVec};
use oxc_ast::ast::*;
#[cfg(debug_assertions)]
use oxc_ast_visit::{Visit, walk::walk_function};
use oxc_ecmascript::BoundNames;
use oxc_index::IndexVec;
use oxc_semantic::Scoping;
use oxc_span::SourceType;
use oxc_syntax::{reference::ReferenceId, scope::ScopeId, symbol::SymbolId};

use crate::{CompressOptions, CompressOptionsUnused, TraverseCtx};

/// Stable program-wide symbol facts plus the optional recursive-function graph.
///
/// This is always present for ES modules: export observability also protects
/// count-based optimizations when recursive function removal is disabled. For
/// CommonJS and Script sources it exists only when the function graph is used.
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
        let functions_enabled = options.unused != CompressOptionsUnused::Keep;
        if !source_type.is_module() && !functions_enabled {
            return None;
        }
        let symbols_len = scoping.symbols_len();
        let mut externally_observable = BitSet::new_in(symbols_len, allocator);
        if source_type.is_script() {
            let root_scope_id = scoping.root_scope_id();
            for symbol_id in scoping.symbol_ids() {
                if scoping.symbol_scope_id(symbol_id) == root_scope_id {
                    externally_observable.set_bit(symbol_id.index());
                }
            }
        }
        Some(Self { externally_observable, functions: None })
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

    fn register_function(
        &mut self,
        function: &Function<'_>,
        source_type: SourceType,
        scoping: &Scoping,
        allocator: &'a Allocator,
    ) {
        let Some(symbol_id) = function.id.as_ref().and_then(|id| id.symbol_id.get()) else {
            return;
        };
        let Some(scope_id) = function.scope_id.get() else { return };

        let binding_scope_id = scoping.symbol_scope_id(symbol_id);

        // Annex B block functions also assign their function object to a
        // var-like binding when the block executes. Semantic hoisting records
        // that alias when possible, but duplicates and TypeScript declarations
        // can retain a block-scoped symbol even though the runtime alias write
        // still occurs. Such a declaration may therefore execute with no
        // resolved reference to its own symbol and cannot participate in this
        // graph.
        let binding_scope_flags = scoping.scope_flags(binding_scope_id);
        if !function.r#async
            && !function.generator
            && !binding_scope_flags.is_var()
            && !binding_scope_flags.is_strict_mode()
        {
            return;
        }

        if source_type.is_script() && binding_scope_id == scoping.root_scope_id() {
            self.mark_externally_observable(symbol_id);
            return;
        }

        let graph = self.functions.get_or_insert_with(|| FunctionGraph::new(scoping, allocator));
        graph.register(scope_id, symbol_id);
    }

    fn analyze(&mut self, scoping: &Scoping) -> bool {
        let Some(graph) = &mut self.functions else { return false };
        graph.analyze(scoping, &self.externally_observable)
    }

    fn contains_candidate(&self, symbol_id: SymbolId) -> bool {
        self.functions.as_ref().is_some_and(|graph| graph.candidates.contains(symbol_id.index()))
    }

    #[cfg(debug_assertions)]
    fn dead_functions(&self) -> Option<&BitSet<'a>> {
        self.functions.as_ref().map(|graph| &graph.dead)
    }
}

/// Registered function scopes, the current candidate/dead sets, and private
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
        self.function_by_scope[scope_id] = Some(symbol_id);
        self.candidates.set_bit(symbol_id.index());
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
            let mut has_function_owner = false;
            for &reference_id in scoping.get_resolved_reference_ids(target) {
                let reference = scoping.get_reference(reference_id);
                if let Some(owner) = self.owner(scoping, reference.scope_id()) {
                    has_function_owner = true;
                    if !self.candidates.contains(owner.index()) {
                        // A non-candidate owner is either permanently observable,
                        // reachable through a root reference, or count-dead.
                        // Only the first two can make their body execute; registration
                        // excludes declarations whose runtime semantics violate that
                        // count-dead implication.
                        if externally_observable.contains(owner.index())
                            || !scoping.symbol_is_unused(owner)
                        {
                            self.scratch.mark_live_root(target);
                        }
                        continue;
                    }
                    if externally_observable.contains(owner.index()) {
                        // An edge from a permanently live function is itself a
                        // root. Avoid storing and sorting the common observable
                        // owner case while preserving the same result.
                        self.scratch.mark_live_root(target);
                    } else {
                        self.scratch.edges.push((owner, target));
                    }
                } else {
                    self.scratch.mark_live_root(target);
                }
            }
            if !has_function_owner && !self.dead.contains(bit) {
                self.scratch.next_dead.set_bit(bit);
            }
        }

        // Functions with only root references never need graph deadness: once
        // those roots disappear, their ordinary count reaches zero. Convert
        // their outgoing edges to roots when the owner is currently count-live,
        // then remove them from the candidate set permanently. `next_dead` is
        // empty on entry and is reused as this short-lived removal set before
        // reachability fills it with the actual next dead set below.
        for index in 0..self.scratch.edges.len() {
            let (owner, target) = self.scratch.edges[index];
            if self.scratch.next_dead.contains(owner.index()) && !scoping.symbol_is_unused(owner) {
                self.scratch.mark_live_root(target);
            }
        }
        for bit in self.scratch.next_dead.ones() {
            self.candidates.unset_bit(bit);
        }
        self.scratch.edges.retain(|(owner, _)| !self.scratch.next_dead.contains(owner.index()));
        self.scratch.next_dead.clear();

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

/// Normalize hook: register a function-declaration scope as a potential graph
/// candidate. The first settled-reference analysis discards declarations that
/// ordinary counts can handle by themselves.
pub fn register_function(function: &Function<'_>, ctx: &mut TraverseCtx<'_>) {
    if !function.is_declaration() {
        return;
    }
    if ctx.state.options.unused == CompressOptionsUnused::Keep {
        return;
    }
    let allocator = ctx.allocator();
    let TraverseCtx { state, scoping, .. } = ctx;
    if let Some(reachability) = &mut state.symbol_reachability {
        reachability.register_function(function, state.source_type, scoping.scoping(), allocator);
    }
}

/// Normalize hook: record runtime bindings exposed by a named export.
pub fn register_named_export(declaration: &ExportNamedDeclaration<'_>, ctx: &mut TraverseCtx<'_>) {
    let TraverseCtx { state, scoping, .. } = ctx;
    let Some(reachability) = &mut state.symbol_reachability else { return };

    if !declaration.export_kind.is_type()
        && let Some(inner) = &declaration.declaration
    {
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
            let reference = scoping.scoping().get_reference(reference_id);
            (!reference.flags().is_type_only()).then(|| reference.symbol_id()).flatten()
        };
        if let Some(symbol_id) = symbol_id {
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

/// Whether pruning this pass's dead references can change a graph input.
///
/// Reachability reads only resolved-reference lists of candidate symbols.
/// Fresh references cannot resurrect a published dead function, so additions
/// alone need no recompute; removals from non-candidate lists cannot affect an
/// edge or root. Scope-only rewrites preserve the nearest function owner.
pub fn dead_references_affect_analysis(ctx: &TraverseCtx<'_>) -> bool {
    let Some(reachability) = &ctx.state.symbol_reachability else { return false };
    ctx.state.dirty.dead_refs.ones().any(|bit| {
        ctx.scoping()
            .get_reference(ReferenceId::from_usize(bit))
            .symbol_id()
            .is_some_and(|symbol_id| reachability.contains_candidate(symbol_id))
    })
}

/// Check the consumed set, then optionally analyze the settled semantic
/// reference lists and publish the next dead set. Called only after
/// `flush_pass_dirty`.
pub fn analyze<'a>(program: &Program<'a>, ctx: &mut TraverseCtx<'a>, recompute: bool) -> bool {
    #[cfg(not(debug_assertions))]
    let _ = program;

    #[cfg(debug_assertions)]
    if let Some(dead) =
        ctx.state.symbol_reachability.as_ref().and_then(SymbolReachability::dead_functions)
    {
        debug_assert_dead_function_declarations_removed(program, ctx.scoping(), dead);
    }

    if !recompute {
        return false;
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
