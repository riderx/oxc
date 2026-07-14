//! The invariant corpus for `symbol_liveness`.
//!
//! Five generations of wrong-code bugs in the dead-cycle analysis were all the
//! same shape: a declaration site candidacy ADMITS at the enter hook, but the
//! pass that consumes the dead bit cannot delete cleanly — because no removal
//! site reaches that slot, because a rewrite RELOCATED the declaration out of a
//! removable slot mid-pass, or because a fold/normalizer changed the SHAPE the
//! gate was judged on. Each was found by a generator over
//! (victim declaration) x (wrapper a rewrite dissolves) x (dead cycle peer),
//! never by reading the code — two separate audits asserted "this is the only
//! mover" and both were wrong.
//!
//! So the enumeration lives here as a fixture instead of in a comment. These
//! programs assert nothing about their output: every one is a dead 2-cycle whose
//! declarator member sits in a position or shape some rewrite disturbs, and the
//! ASSERTIONS ARE THE DEBUG BUILD'S — the ground-truth oracle
//! (`compute_dead_symbols`, which re-derives the analysis on the settled tree)
//! and the contract sweep (`debug_assert_dead_declarations_removed`, which
//! checks the contract itself: nothing dead-marked may still have a declaration
//! standing). A regression here is a panic, in debug, in CI.
//!
//! Add a shape whenever a new rewrite learns to move or reshape a declaration.

use cow_utils::CowUtils;

use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_minifier::{CompressOptions, Compressor};
use oxc_parser::Parser;
use oxc_span::SourceType;

/// Compress in both modes (full minify, and DCE-only — rolldown's per-module
/// treeshake preprocess, where these bugs are equally reachable), then re-parse
/// and re-compress the output: a stranded declaration usually only becomes
/// visible on the pass that consumes the bit, so the second round matters.
#[track_caller]
fn compress_both_modes(source_text: &str, source_type: SourceType) {
    for dce in [false, true] {
        let mut input = source_text.to_string();
        for round in 0..2 {
            let allocator = Allocator::default();
            let ret = Parser::new(&allocator, &input, source_type).parse();
            assert!(
                !ret.panicked,
                "round {round}: input does not parse: {input}\nfrom: {source_text}"
            );
            let mut program = ret.program;
            let options = if dce { CompressOptions::dce() } else { CompressOptions::smallest() };
            if dce {
                Compressor::new(&allocator).dead_code_elimination(&mut program, options);
            } else {
                Compressor::new(&allocator).build(&mut program, options);
            }
            input = Codegen::new().build(&program).code;
        }
    }
}

/// A dead `a <-> b` cycle whose `b` member is the declaration under test. `a` is
/// a function declaration, which every statement slot CAN remove — so whenever
/// `b`'s site cannot be removed, `b` must be pinned or the analysis strands it
/// referencing a deleted `a`.
const VICTIMS: &[&str] = &[
    "var b = a;",
    "var b = function () { a(); };",
    "var b = a, b2 = a;",
    "for (var b = a; g2; ) ;",
    "for (var b = a; 0; ) ;",
    "var b = [a];",
    "let b = a;",
    "const b = a;",
    "class b extends a {}",
    // Shape axis: `Normalize` strips the parens after the gate has judged the
    // init, so the removal site faces a residue-leaving kind the gate never saw.
    "var b = (class { static x = a; });",
    "var b = ([a]);",
    "var b = (0, a);",
];

/// Wrappers a rewrite dissolves or drains mid-pass, moving the victim into a
/// slot the collection did not classify it in. `{V}` is the victim; the padding
/// is what makes the relocation land on the pass whose stale set still calls the
/// cycle live — without it the removal simply happens first and nothing strands.
const WRAPPERS: &[&str] = &[
    "{V}",
    "if (g) { {V} }",                       // block unwrap -> bare consequent
    "if (g) { {V} let c = 1; 0 && c; a; }", // ...delayed by one pass
    "if (g) { } else { {V} }",
    "while (g) { {V} }",
    "l: { {V} }",
    "for (;g;) { {V} }",
    "if (g) return; {V}", // if-inversion drains the tail
    "if (g) return; {V} let c = 1; 0 && c;",
    "switch (g) { case 1: {V} }",
    "try { {V} } catch {}",
    "{ { {V} } }",
];

#[test]
fn liveness_invariant_corpus() {
    for victim in VICTIMS {
        for wrapper in WRAPPERS {
            let body = wrapper.cow_replace("{V}", victim);
            // TOP LEVEL, with a live statement after it. This placement is
            // load-bearing: nested inside a function the whole body collapses
            // cleanly and nothing can strand, which silently made an earlier
            // version of this corpus vacuous — it passed with the relocation
            // force-root deleted. `console.log` keeps the program from folding
            // away entirely, and `globalThis.g` keeps the branch tests opaque.
            // `return` is only legal inside a function, so those wrappers run
            // in the nested form only.
            if !body.contains("return") {
                let top = format!(
                    "globalThis.g = 1;\nfunction a() {{ b(); }}\n{body}\nconsole.log('ok');"
                );
                compress_both_modes(&top, SourceType::mjs());
                compress_both_modes(&top, SourceType::cjs());
            }

            // The same shape one scope in: a function body is a statement list
            // too. The `.cjs` runs take the analysis-off path (the collection
            // arms for ESM modules only) — they sweep that the OFF path stays
            // byte-stable and oracle-clean on every shape.
            let nested = format!(
                "function a() {{ b(); }}\nfunction outer() {{ {body} }}\nouter();\nconsole.log('ok');"
            );
            compress_both_modes(&nested, SourceType::mjs());
            compress_both_modes(&nested, SourceType::cjs());
        }
    }
}
