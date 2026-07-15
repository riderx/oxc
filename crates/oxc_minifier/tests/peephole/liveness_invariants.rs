//! Focused repeat-compression corpus for recursive function reachability.
//!
//! Expected output is covered by the neighboring declaration tests. This
//! corpus exercises the lifecycle contract in both full-minify and DCE modes:
//! compressing settled output again must be byte-identical, and the debug
//! sweep must find no declaration for a dead bit consumed by the prior pass.

use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_minifier::{CompressOptions, Compressor};
use oxc_parser::Parser;
use oxc_span::SourceType;

#[track_caller]
fn compress_twice(source_text: &str, source_type: SourceType, dce: bool) {
    let mut input = source_text.to_string();
    let mut first = None;
    for round in 0..2 {
        let allocator = Allocator::default();
        let ret = Parser::new(&allocator, &input, source_type).parse();
        assert!(!ret.panicked, "round {round}: input does not parse: {input}");
        assert!(ret.diagnostics.is_empty(), "round {round}: {:?}", ret.diagnostics);
        let mut program = ret.program;
        if dce {
            Compressor::new(&allocator).dead_code_elimination(&mut program, CompressOptions::dce());
        } else {
            Compressor::new(&allocator).build(&mut program, CompressOptions::smallest());
        }
        input = Codegen::new().build(&program).code;
        if round == 0 {
            first = Some(input.clone());
        }
    }
    assert_eq!(first.unwrap(), input, "repeat compression changed output for {source_text}");
}

const MODULE_CASES: &[&str] = &[
    // Self/mutual recursion and a nested dead cycle.
    "function self() { self() } function a() { b() } function b() { a() }",
    "function live() { function a(p = b) { return () => b() } function b() { a() } return 1 } use(live)",
    // Function/var redeclaration needs the post-flush count pass.
    "function f() { f() } var f;",
    // Non-function declaration sites root candidates without candidacy pins.
    "function a() { b() } if (opaque) var b = a;",
    "function f() { f() } class C { method() { f() } } use(C)",
    // Stable export observability and evaluated default exports.
    "export var value = {}; value.x = 1; function a() { value; b() } function b() { a() }",
    "function exported() { exported() } export { exported }",
    "function value() { value() } export default value",
    // Direct eval can disappear before analysis activates.
    "if (false) eval('x'); function f() { f() }",
    // Using and for-head RHS references are ordinary roots.
    "function f() { f() } using resource = f",
    "function f() { f() } for (var item of [f]);",
];

const NON_ESM_CASES: &[&str] = &[
    "function a() { b() } function b() { a() } console.log('keep')",
    "function outer() { function f() { f() } return 1 } use(outer)",
    "if (false) g(); function g() { f() } function f() { f() }",
];

#[test]
fn liveness_repeat_compression_corpus() {
    for source in MODULE_CASES {
        for dce in [false, true] {
            compress_twice(source, SourceType::mjs(), dce);
        }
    }

    for source in NON_ESM_CASES {
        for source_type in [SourceType::cjs(), SourceType::cjs().with_script(true)] {
            for dce in [false, true] {
                compress_twice(source, source_type, dce);
            }
        }
    }
}
