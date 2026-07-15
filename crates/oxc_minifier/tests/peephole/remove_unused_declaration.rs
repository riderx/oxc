use oxc_span::SourceType;

use crate::{
    CompressOptions, CompressOptionsUnused, TreeShakeOptions, test_options,
    test_options_source_type, test_same_options, test_same_options_source_type, test_same_smallest,
    test_smallest,
};

// Leak regression: dropping an unused declarator must walk the whole
// declarator, not just the init — references can also live in the binding's
// TS type annotation (e.g. computed keys in a type literal). A leaked type
// ref makes the symbol look used, blocking its own removal.
#[test]
fn remove_unused_declarator_walks_type_annotation_refs() {
    let options = CompressOptions::smallest();
    test_options_source_type(
        "function f() { const a = Symbol('a'); const b = Symbol('b'); const reg: { [a]: string; [b]: string } = { foo: 1, bar: 2 }; return 1; } g(f());",
        "function f() { return 1; } g(f());",
        SourceType::ts(),
        &options,
    );
}

// Leak regression (single-use inlining, `stmts.pop()` site): after the lone
// declarator's init is inlined into the next statement, the whole declaration
// statement is popped — the discarded declarator's type annotation still holds
// a ref to `a`.
#[test]
fn single_use_inline_pop_walks_type_annotation_refs() {
    let options = CompressOptions::smallest();
    test_options_source_type(
        "function f() { const a = Symbol('a'); const x: { [a]: string } = g(); return x; } h(f());",
        "function f() { return g(); } h(f());",
        SourceType::ts(),
        &options,
    );
}

// Leak regression (single-use inlining, `declarations.truncate()` site): only
// the tail declarator `x` is inlined; the truncate discards it while `keep`
// survives — `x`'s type annotation still holds a ref to `a`.
#[test]
fn single_use_inline_truncate_walks_type_annotation_refs() {
    let options = CompressOptions::smallest();
    test_options_source_type(
        "function f() { const a = Symbol('a'); const keep = g(), x: { [a]: string } = h(); return [keep, keep, x]; } j(f());",
        "function f() { let keep = g(); return [keep, keep, h()]; } j(f());",
        SourceType::ts(),
        &options,
    );
}

// Leak regression (single-use inlining, `declarations.drain()` site): `x` is
// inlined into the sibling declarator `y`'s init within the same declaration;
// the drain discards `x`'s declarator — its type annotation still holds a ref
// to `a`.
#[test]
fn single_use_inline_drain_walks_type_annotation_refs() {
    let options = CompressOptions::smallest();
    test_options_source_type(
        "function f() { const a = Symbol('a'); const x: { [a]: string } = g(), y = [x]; return y; } j(f());",
        "function f() { return [g()]; } j(f());",
        SourceType::ts(),
        &options,
    );
}

// Leak regression (dead-code identity-drop site): an init-less `var` after
// `return` is classified as an identity drop (KeepVar re-emits it), skipping
// the drop walk — but KeepVar's re-emit strips the type annotation, so the
// annotation's ref to `b` leaks.
#[test]
fn dead_code_identity_drop_checks_type_annotation() {
    let options = CompressOptions::smallest();
    test_options_source_type(
        "function f() { const b = Symbol('b'); return 1; var a: { [b]: string }; } g(f());",
        "function f() { return 1; } g(f());",
        SourceType::ts(),
        &options,
    );
}

// Near-miss: dropping the annotated declarator must only kill the annotation's
// own ref — `a`'s other (value) uses keep `const a = Symbol('a')` alive.
#[test]
fn type_annotation_drop_keeps_symbol_used_elsewhere() {
    let options = CompressOptions::smallest();
    test_options_source_type(
        "function f() { const a = Symbol('a'); const x: { [a]: string } = g(); return [x, a, a]; } h(f());",
        "function f() { let a = Symbol('a'); return [g(), a, a]; } h(f());",
        SourceType::ts(),
        &options,
    );
}

#[test]
fn remove_unused_variable_declaration() {
    let options = CompressOptions::smallest();
    test_options("var x", "", &options);
    test_options("var x = 1", "", &options);
    test_options("var x = foo", "foo", &options);

    test_options("var [] = []", "", &options);
    test_options("var [] = [1]", "", &options);
    test_options("var [] = [foo]", "foo", &options);
    test_options("var [] = 'foo'", "", &options);
    test_same_options("export var f = () => { var [] = arguments }", &options);
    test_options(
        "export function f() { var [] = arguments }",
        "export function f() { arguments; }",
        &options,
    );
    test_options(
        "function foo() {return (()=>{ var []=arguments })()};foo()",
        "function foo() {arguments;} foo();",
        &options,
    );
    test_same_options_source_type(
        "globalThis.f = function () { var [] = arguments }",
        SourceType::cjs(),
        &options,
    );
    test_same_options("var [] = arguments", &options);
    test_same_options("var [] = null", &options);
    test_same_options("var [] = void 0", &options);
    test_same_options("var [] = 1", &options);
    test_same_options("var [] = a", &options);

    test_options("var {} = {}", "", &options);
    test_options("var {} = { a: 1 }", "", &options);
    test_options("var {} = { foo }", "foo", &options);
    test_same_options("var {} = null", &options);
    test_same_options("var {} = a", &options);
    test_same_options("var {} = null", &options);
    test_same_options("var {} = void 0", &options);

    test_same_options("var x; foo(x)", &options);
    test_same_options("export var x", &options);
    test_same_options("using x = foo", &options);
    test_same_options("await using x = foo", &options);

    test_options("for (var x; ; );", "for (; ;);", &options);
    test_options("for (var x = 1; ; );", "for (; ;);", &options);
    test_same_options("for (var x = foo; ; );", &options); // can be improved
}

#[test]
fn remove_unused_pure_iife_init() {
    // https://github.com/oxc-project/oxc/issues/17480
    test_smallest("var x = /* @__PURE__ */ foo()", "");
    test_smallest("var x = /* @__PURE__ */ new Foo()", "");
    test_smallest("var x = /* @__PURE__ */ foo(a)", "a;");
    test_smallest("var x = /* @__PURE__ */ foo(bar())", "bar();");
    test_smallest("var x = /* @__PURE__ */ new Foo(bar())", "bar();");
    test_smallest("var x = /* @__PURE__ */ foo(/* @__PURE__ */ bar(z))", "z;");

    test_smallest("var x = /* @__PURE__ */ (() => foo())()", "");
    test_smallest("var x = /* @__PURE__ */ (() => new Foo())()", "");
    test_smallest("var x = /* @__PURE__ */ (() => { return foo() })()", "");
    test_smallest("var x = /* @__PURE__ */ (() => { foo() })()", "");

    test_smallest("var x = /* @__PURE__ */ (() => g.x)()", "");
    test_smallest("var x = /* @__PURE__ */ (() => g[k])()", "");
    test_smallest("var x = /* @__PURE__ */ (() => foo`tpl`)()", "");
    test_smallest("var x = /* @__PURE__ */ (() => [a, b])()", "");
    test_smallest("var x = /* @__PURE__ */ (() => ({ a }))()", "");
    test_smallest("var x = /* @__PURE__ */ (() => a + b)()", "");
    test_smallest("var x = /* @__PURE__ */ (() => `${a}`)()", "");
    test_smallest("var x = /* @__PURE__ */ (() => foo()?.bar())()", "");
    test_smallest("var x = /* @__PURE__ */ (() => a ? b : c)()", "");

    test_smallest("var x = /* @__PURE__ */ (function() { return foo() })()", "");

    test_smallest("let x = /* @__PURE__ */ (() => g.x)()", "");
    test_smallest("const x = /* @__PURE__ */ (() => g.x)()", "");

    test_smallest("var x = /* @__PURE__ */ foo(), y = bar(); use(y);", "var y = bar(); use(y);");

    // Referenced bindings keep the declarator — `symbol_is_unused` blocks
    // the drop. Propagation still inlines the IIFE body.
    test_same_smallest("var x = /* @__PURE__ */ foo(); use(x);");
    test_smallest(
        "var x = /* @__PURE__ */ (() => foo())(); use(x);",
        "var x = /* @__PURE__ */ foo(); use(x);",
    );
    test_smallest("var x = /* @__PURE__ */ (() => g.x)(); use(x);", "var x = g.x; use(x);");
    test_smallest(
        "var x = /* @__PURE__ */ (() => { return foo() })(); use(x);",
        "var x = /* @__PURE__ */ foo(); use(x);",
    );
    // Conditional body — propagation only fires on Call/New, so the
    // top-level conditional is inlined without an annotation.
    test_smallest(
        "var x = /* @__PURE__ */ (() => a ? b : c)(); use(x);",
        "var x = a ? b : c; use(x);",
    );

    // Exported bindings are cross-module reachable — the export-ancestor
    // check blocks the early drop.
    test_smallest("export var x = /* @__PURE__ */ foo()", "export var x = /* @__PURE__ */ foo();");
    test_smallest(
        "export const x = /* @__PURE__ */ (() => foo())();",
        "export const x = /* @__PURE__ */ foo();",
    );
    test_smallest("export const x = /* @__PURE__ */ (() => g.x)();", "export const x = g.x;");
    test_same_smallest("var x = /* @__PURE__ */ foo(); export { x }");

    test_smallest("var x = (() => g.x)();", "g.x;");

    // `using` runs `[Symbol.dispose]` at scope exit, so the declarator stays.
    test_smallest("using x = /* @__PURE__ */ (() => foo())()", "using x = /* @__PURE__ */ foo();");
    test_smallest(
        "await using x = /* @__PURE__ */ (() => foo())()",
        "await using x = /* @__PURE__ */ foo();",
    );

    // Function-local var inside an exported function — the export ancestor
    // walk must not be fooled by `f` being exported. `x` is a local.
    test_smallest(
        "export function f() { var x = /* @__PURE__ */ (() => foo())(); } f();",
        "export function f() {} f();",
    );

    // Empty async/generator IIFE in unused-var-init position now collapses
    // through `is_expression_result_unused` (which the widening newly covers).
    test_smallest("var x = (async () => {})()", "");
    test_smallest("var x = (function* () {})()", "");

    // `can_remove_unused_declarators` blocks top-level `var` drops in script
    // mode (the binding is an observable global). The IIFE inlines with
    // propagation as in any other position, but the declarator stays.
    test_options_source_type(
        "var x = /* @__PURE__ */ (() => stuff())()",
        "var x = /* @__PURE__ */ stuff();",
        SourceType::cjs().with_script(true),
        &CompressOptions::smallest(),
    );

    // Direct eval at the root scope blocks the drop — eval might reference
    // the binding even when static analysis sees no use.
    test_smallest(
        "eval('x'); var x = /* @__PURE__ */ (() => stuff())()",
        "eval('x'); var x = /* @__PURE__ */ stuff();",
    );
}

#[test]
fn remove_unused_function_declaration() {
    let options = CompressOptions::smallest();
    test_options("function foo() {}", "", &options);
    test_same_options("function foo() { bar } foo()", &options);
    test_same_options("export function foo() {} foo()", &options);
    test_same_options("function foo() { bar } eval('foo()')", &options);
}

#[test]
fn remove_unused_declaration_after_dead_direct_eval() {
    let options = CompressOptions::smallest();
    test_options("function f(){if(false)eval('x');var x}f()", "", &options);
    // Live eval still keeps `var x` alive after the refresh.
    test_same_options("function f(){eval('x');var x}f()", &options);
    // Parenthesized eval is still direct eval; the wrapped form must keep `var x` alive.
    test_options(
        "function f(){if(false)y;(eval)('x');var x}f()",
        "function f(){(eval)('x');var x}f()",
        &options,
    );
    // Eval nested inside another call's arguments still keeps `var x` alive.
    // The dead `if(false)y` triggers a peephole change so the refresh actually runs.
    test_options(
        "function f(){if(false)y;foo(eval('x'));var x}f()",
        "function f(){foo(eval('x'));var x}f()",
        &options,
    );
    // Eval in a nested scope: clearing must propagate up through both nested and
    // outer chains, then re-set only what's still live (here, nothing).
    test_options(
        "function outer(){function inner(){if(false)eval('x')}inner();var x}outer()",
        "",
        &options,
    );
    // Live eval at the program root keeps an otherwise-unused `var x` alive
    // (the root flag is the global witness checked by `can_remove_unused_declarators`).
    test_same_options("eval('x');var x", &options);
}

#[test]
fn remove_unused_declaration_with_optional_eval() {
    let options = CompressOptions::smallest();
    test_options("function f(){if(false)eval?.('x');var x}f()", "", &options);
    // Live optional eval is indirect — it doesn't set `DirectEval`, so `var x` is
    // removable even though the call itself stays as a side-effectful expression.
    // Contrast with the live-direct-eval root case above, where `var x` is kept.
    test_options("eval?.('x');var x", "eval?.('x');", &options);
}

#[test]
fn remove_unused_class_declaration() {
    let options = CompressOptions::smallest();
    test_options("class C {}", "", &options);
    test_same_options("export class C {}", &options);
    test_options("class C {} C", "", &options);
    test_same_options("class C {} eval('C')", &options);

    // extends
    test_options("class C {}", "", &options);
    test_options("class C extends Foo {}", "Foo", &options);

    // static block
    test_options("class C { static {} }", "", &options);
    test_same_options("class C { static { foo } }", &options);

    // method
    test_options("class C { foo() {} }", "", &options);
    test_options("class C { [foo]() {} }", "foo", &options);
    test_options("class C { static foo() {} }", "", &options);
    test_options("class C { static [foo]() {} }", "foo", &options);
    test_options("class C { [1]() {} }", "", &options);
    test_options("class C { static [1]() {} }", "", &options);

    // property
    test_options("class C { foo }", "", &options);
    test_options("class C { foo = bar }", "", &options);
    test_options("class C { foo = 1 }", "", &options);
    // TODO: would be nice if this is removed but the one with `this` is kept.
    test_same_options("class C { static foo = bar }", &options);
    test_same_options("class C { static foo = this.bar = {} }", &options);
    test_options("class C { static foo = 1 }", "", &options);
    test_options("class C { [foo] = bar }", "foo", &options);
    test_options("class C { [foo] = 1 }", "foo", &options);
    test_same_options("class C { static [foo] = bar }", &options);
    test_options("class C { static [foo] = 1 }", "foo", &options);

    // accessor
    test_options("class C { accessor foo = 1 }", "", &options);
    test_options("class C { accessor [foo] = 1 }", "foo", &options);

    // order
    test_options("class _ extends A { [B] = C; [D]() {} }", "A, B, D", &options);

    // decorators
    test_same_options("class C { @dec foo() {} }", &options);
    test_same_options("@dec class C {}", &options);

    // TypeError
    test_same_options("class C extends (() => {}) {}", &options);
}

#[test]
fn keep_in_script_mode() {
    let options = CompressOptions::smallest();
    let source_type = SourceType::cjs().with_script(true);
    test_same_options_source_type("var x = 1; x = 2;", source_type, &options);
    test_same_options_source_type("var x = 1; x = 2, foo(x)", source_type, &options);
    test_options_source_type("var x = 1; x = 2;", "", SourceType::cjs(), &options);

    test_options_source_type("class C {}", "class C {}", source_type, &options);
}

// #13105: a declaration whose every reference lives inside its own body (or
// inside the bodies of a cycle it belongs to) can never execute — no live
// code can reach it, so the whole group is removable. Reference counting
// alone can't see this: the internal references keep the count above zero.
#[test]
fn remove_recursive_unused_function_declaration() {
    // Self-recursion.
    test_smallest("function f() { f() }", "");
    // Side effects inside the dead body never run.
    test_smallest("function f() { console.log(1); f() }", "");
    // Mutual recursion.
    test_smallest("function c() { d() } function d() { c() }", "");
    // Self-reference as a value.
    test_smallest("function f() { return f }", "");
    test_smallest("function f() { g(f) }", "");
    // The cycle's only external reference is inside dead code.
    test_smallest("if (false) c(); function c() { d() } function d() { c() }", "");
}

// Declarator and class cycles are KEPT: candidacy is functions-only, because
// declarator/class candidacy measured zero output bytes on real bundles
// while owning most of the analysis's hazard surface (see the
// `symbol_liveness` module doc). These pin the deliberate keeps — the
// declarators' interior references root their targets, so the whole shape
// survives.
#[test]
fn keep_recursive_declarator_and_class_cycles() {
    // const arrow cycle.
    test_smallest(
        "const a = () => b(); const b = () => a();",
        "const a = () => b(), b = () => a();",
    );
    // var closing over its own binding.
    test_same_smallest("var f = function() {\n\tf();\n};");
    // Class cycle with side-effect-free evaluation.
    test_same_smallest(
        "class A {\n\tm() {\n\t\tnew B();\n\t}\n}\nclass B {\n\tm() {\n\t\tnew A();\n\t}\n}",
    );
    // Mixed function / const arrow / class cycle: the non-function members
    // root the function member, so nothing is removed.
    test_smallest(
        "function a() { b() } const b = () => { new C() }; class C { m() { a() } }",
        "function a() {\n\tb();\n}\nconst b = () => {\n\tnew C();\n};\nclass C {\n\tm() {\n\t\ta();\n\t}\n}",
    );
}

#[test]
fn remove_recursive_unused_nested_in_live_function() {
    // Dead recursion inside a used function: statement-level tree shaking
    // (rolldown's linker) cannot see inside bodies, so this must be handled
    // here.
    test_smallest(
        "function live() { function inner() { inner() } return 1; } g(live());",
        "function live() { return 1; } g(live());",
    );
}

#[test]
fn keep_recursive_multi_declarator_cycle() {
    // The declarator member of the cycle roots the function member, so the
    // cycle survives even after the used sibling declarator is inlined.
    test_smallest(
        "const a = () => b(), keep = 1; function b() { a() } console.log(keep);",
        "const a = () => b();\nfunction b() {\n\ta();\n}\nconsole.log(1);",
    );
}

#[test]
fn keep_recursive_function_with_live_references() {
    // A read from live code roots the cycle.
    test_same_smallest("function f() { f() } console.log(f);");
    // A write from live code also roots it (dropping the function would leave
    // `f = null` assigning to a missing binding).
    test_same_smallest("function f() { f() } f = null;");
    // Exports are roots.
    test_same_smallest("export function f() { f() }");
    test_same_smallest("function f() { f() } export { f };");
    test_same_smallest("export default function f() { f() }");
    // Direct eval in the declaring scope blocks removal.
    test_same_smallest("function o() { function f() { f() } eval('x') } o();");
}

#[test]
fn keep_recursive_cycle_with_side_effectful_evaluation() {
    // The side-effectful initializer survives, and its reference to `b`
    // roots the cycle.
    test_smallest(
        "const a = (console.log(1), () => b()); const b = () => a();",
        "const a = (console.log(1), () => b()), b = () => a();",
    );
    // Side-effectful heritage keeps the class cycle.
    test_same_smallest(
        "class A extends (console.log(1), Object) { m() { new B() } } class B { m() { new A() } }",
    );
    // A PURE static value still keeps the class cycle: `remove_unused_class`
    // extracts every present static value, so removal would not be clean —
    // the extracted `B` would reference a removed cycle member (see
    // `classify_class_removability`).
    test_same_smallest("class A { static x = B; m() { new B() } } class B { m() { new A() } }");
}

#[test]
fn keep_class_cycle_with_wrapped_arrow_heritage() {
    // `classify_class_removability` must see the arrow heritage through a
    // pure sequence/paren wrapper: liveness classifies the pre-fold shape,
    // but a fold surfaces the literal arrow before the removal site
    // re-classifies, and the Keep flip would strand `A` referencing a
    // removed `B`.
    test_smallest(
        "class A extends (0, () => {}) { m() { new B() } } class B { m() { new A() } } console.log(1);",
        "class A extends (() => {}) {\n\tm() {\n\t\tnew B();\n\t}\n}\nclass B {\n\tm() {\n\t\tnew A();\n\t}\n}\nconsole.log(1);",
    );
    // The single, fully-unused class is kept for the same reason a literal
    // arrow heritage is kept: evaluating it is a guaranteed TypeError.
    test_smallest("class C extends (0, () => {}) {}", "class C extends (() => {}) {}");
}

#[test]
fn keep_class_with_tdz_or_undefined_heritage() {
    // test262 language/statements/class/name-binding/in-extends-expression.js:
    // the class's own name is in its TDZ while the heritage evaluates, so the
    // declaration is a guaranteed ReferenceError that must survive.
    test_same_smallest("class C extends C {}");
    // The test262 shape: the class lives in a callback whose call is live.
    // (A NAMED function wrapper additionally hits a pre-existing hole in the
    // pure-function model — `may_have_side_effects` does not model heritage
    // TDZ throws, so `f` reads as pure and the call is dropped on `main`
    // too; that is a separate `oxc_ecmascript` issue, not covered here.)
    test_same_smallest("g(function() {\n\tclass C extends C {}\n});");
    // The wrapped variant classifies through the same heritage unwrap.
    test_smallest("class C extends (0, C) {}", "class C extends C {}");
    // A forward lexical heritage also evaluates in its TDZ; reference order
    // cannot be proven mid-minification (transforms copy and move spans), so
    // any class/lexical/`var` heritage keeps the class.
    test_same_smallest(
        "class A extends B {\n\tm() {\n\t\tnew A();\n\t}\n}\nclass B {\n\tm() {\n\t\tnew A();\n\t}\n}",
    );
    // `var` heritage: a hoisted-but-unassigned binding is `undefined`, and
    // `extends undefined` is a TypeError.
    test_same_smallest("var B = class {};\nclass A extends B {\n\tm() {\n\t\tnew A();\n\t}\n}");
}

#[test]
fn keep_class_cycle_with_hoisted_function_heritage() {
    // The class is not a candidate, and its heritage reference roots `F`.
    test_same_smallest("function F() {}\nclass A extends F {\n\tm() {\n\t\tnew A();\n\t}\n}");
}

// Classes are never candidates, so a logical fold (`0 || Y` -> `Y`)
// surfacing a risky heritage mid-pass can no longer flip a dead-marked
// class at its removal site — the historical wrong-code shape these pin.
// Everything is kept; only the fold itself changes the output.
#[test]
fn keep_class_cycle_with_fold_unstable_heritage() {
    // Risky identifier (initialized var) inside a foldable wrapper.
    test_smallest(
        "class B { m() { new A() } } var Y = class {}; class A extends (0 || Y) { [B]() {} }",
        "class B {\n\tm() {\n\t\tnew A();\n\t}\n}\nvar Y = class {};\nclass A extends Y {\n\t[B]() {}\n}",
    );
    // Arrow inside the same wrapper (`extends` an arrow is a guaranteed
    // TypeError, so surfacing it also flips to `Keep`).
    test_smallest(
        "class B { m() { new A() } } class A extends (0 || (() => {})) { [B]() {} }",
        "class B {\n\tm() {\n\t\tnew A();\n\t}\n}\nclass A extends (() => {}) {\n\t[B]() {}\n}",
    );
}

#[test]
fn keep_class_cycle_with_wrapped_heritage() {
    // The `0 || F` fold still surfaces `F`; the class is kept either way
    // (classes are not candidates), and the heritage reference roots `F`.
    test_smallest(
        "function F() {}\nclass A extends (0 || F) {\n\tm() {\n\t\tnew A();\n\t}\n}",
        "function F() {}\nclass A extends F {\n\tm() {\n\t\tnew A();\n\t}\n}",
    );
}

#[test]
fn keep_recursive_function_in_script_mode_top_level() {
    let options = CompressOptions::smallest();
    let source_type = SourceType::cjs().with_script(true);
    test_same_options_source_type("function f() { f() }", source_type, &options);
}

#[test]
fn keep_recursive_function_with_unused_keep_option() {
    let options =
        CompressOptions { unused: CompressOptionsUnused::Keep, ..CompressOptions::smallest() };
    test_same_options("function f() { f() }", &options);
}

// Candidacy is granted per declaration SITE but the dead bit is consumed per
// SYMBOL, so a declaration site the removal machinery can never remove —
// export-wrapped, script top-level (including bindings var-hoisted to the
// script root from inside blocks), for-in/of heads, Annex-B block-level
// functions — must force-root its symbol: one ineligible site keeps the
// whole symbol alive even when another site of the same symbol is removable.
#[test]
fn keep_recursive_cycle_with_exported_redeclaration() {
    // `export var f;` carries no reference, but importers observe the
    // binding: removing the initializing redeclaration would export
    // undefined.
    test_same_smallest("export var f; var f = function() { setTimeout(f) };");
}

#[test]
fn keep_recursive_cycle_in_for_in_head() {
    // No removal site handles for-in/of head declarators, so the head
    // survives; its Annex-B initializer must keep referencing a live `p`.
    let options = CompressOptions::smallest();
    let source_type = SourceType::cjs().with_script(true);
    test_same_options_source_type(
        "function o() { var p = function() { console.log(x) }; for (var x = p in {}); return 1; } g(o());",
        source_type,
        &options,
    );
}

// A declarator in a bare single-statement slot (if consequent/alternate,
// loop/label/with body) has NO removal site: `exit_statements` fires on
// statement lists only and the for-init retain covers for-inits only.
// Candidacy must refuse the position, or the dead mark deletes the cycle
// peer while the untouchable declarator survives referencing it
// (ReferenceError once `g` is truthy). The peephole loop can even create
// the shape itself by flattening `if (g) { var b = a; }` into the bare
// slot.
#[test]
fn keep_declarator_cycle_in_bare_statement_slot() {
    test_same_smallest("function a() {\n\tb();\n}\nif (g) var b = a;");
    // The loop body slot (`while` normalizes to `for`).
    test_smallest(
        "function a() { b() } while (g) var b = a;",
        "function a() {\n\tb();\n}\nfor (; g;) var b = a;",
    );
    // The with-body slot, inside a function so script-mode root protection
    // is not what keeps it.
    let options = CompressOptions::smallest();
    let source_type = SourceType::cjs().with_script(true);
    test_same_options_source_type(
        "function q() { function a() { b() } with (o) var b = a; return 1 } g(q());",
        source_type,
        &options,
    );
    // The braced form behaves identically: declarators are never
    // analysis-removed, in a list slot or not.
    test_smallest(
        "function a() { b() } if (g) { var b = a; }",
        "function a() {\n\tb();\n}\nif (g) var b = a;",
    );
}

// The same hole one nesting level deeper: `handle_for_statement`'s retain —
// the only for-init removal site — is reached from the statement-LIST loop,
// so a `for` in a bare slot cannot have its init declarators removed either.
// Candidacy must ask where the `for` itself sits.
#[test]
fn keep_declarator_cycle_in_bare_slot_for_init() {
    test_same_smallest("function a() {\n\tb();\n}\nif (g) for (var b = a; g2;) ;");
    // Else-arm, loop body and label body slots.
    test_same_smallest("function a() {\n\tb();\n}\nif (g) g2(); else for (var b = a; g2;) ;");
    test_same_smallest("function a() {\n\tb();\n}\nfor (; g;) for (var b = a; g2;) ;");
    test_same_smallest("function a() {\n\tb();\n}\nlbl: for (var b = a; g;) break lbl;");
    // Script mode, inside a function (root protection is not what keeps it).
    let options = CompressOptions::smallest();
    let source_type = SourceType::cjs().with_script(true);
    test_same_options_source_type(
        "function q() {\n\tfunction a() {\n\t\tb();\n\t}\n\tif (g) for (var b = a; g2;) ;\n\treturn 1;\n}\ng(q());",
        source_type,
        &options,
    );
    // A `for` that IS a statement-list member keeps its init declarator
    // just the same.
    test_smallest(
        "function a() { b() } for (var b = a; g;) g2();",
        "function a() {\n\tb();\n}\nfor (var b = a; g;) g2();",
    );
}

// The block unwrap (`try_optimize_block`) relocates the declarator into the
// bare if-consequent slot mid-pass. Declarators are never candidates, so
// the relocation cannot strand anything — `b`'s init roots `a` from
// wherever the statement lands. Historically this shape shipped wrong code
// (a relocation force-root was needed while declarator candidacy existed);
// the multi-pass timing scaffolding is kept so the shape still exercises
// the relocation on the exact pass cadence that used to break.
#[test]
fn keep_declarator_cycle_relocated_by_block_unwrap() {
    test_smallest(
        "function a() { b() } function p1() {} function p2() { p1() } if (g) { p2(); p1(b); var b = a; }",
        "function a() {\n\tb();\n}\nif (g) var b = a;",
    );
    // The `for` variant relocates the `for` itself into the bare slot.
    test_smallest(
        "function a() { b() } function p1() {} function p2() { p1() } if (g) { p2(); p1(b); for (var b = a; g2;) ; }",
        "function a() {\n\tb();\n}\nif (g) for (var b = a; g2;) ;",
    );
    // Any pair of drops one pass apart opens the same window — here a live
    // `let` that outlives the reference that roots `b`, rather than a pure
    // call. Both shapes must stay pinned: the timing is the bug, not the
    // mechanism that produces it.
    test_smallest(
        "function a() { b() } if (g) { var b = a; let c = 1; 0 && c; a; }",
        "function a() {\n\tb();\n}\nif (g) var b = a;",
    );
    test_smallest(
        "function a() { b() } if (g) { for (var b = a;;) break; let c = 1; 0 && c; a; }",
        "function a() {\n\tb();\n}\nif (g) for (var b = a;;) break;",
    );
}

// The `if (t) return; TAIL` inversion drains the tail into `if (!t) { TAIL }`,
// and a tail of exactly one statement becomes a BARE consequent — the second
// relocation shape that historically stranded a declarator while declarator
// candidacy existed. Now the declarator roots its cycle from any slot; the
// trailing statements still fold away and leave it alone in the tail.
#[test]
fn keep_declarator_cycle_relocated_by_if_inversion() {
    test_smallest(
        "function outer() { function a() { b(); } if (g) return; var b = a; function blocker() {} 0 && blocker; a; } outer();",
        "function outer() {\n\tfunction a() {\n\t\tb();\n\t}\n\tif (!g) var b = a;\n}\nouter();",
    );
}

// The for-body unwrap in `minimize_for_statement` folds a leading
// `if (x) break;` into the loop test and moves the surviving statement into
// the `for`'s bare body slot — the third relocation shape that shipped
// wrong code while declarator candidacy existed (`void a` drops the same
// pass, so the {a, b} cycle used to flush dead in exactly the pass whose
// exit hook relocated the declarator). Declarators root their cycles now,
// wherever they sit.
#[test]
fn keep_declarator_cycle_relocated_by_for_body_unwrap() {
    test_smallest(
        "function a() { return b; } for (;;) { if (x) break; var b = a; } void a;",
        "function a() {\n\treturn b;\n}\nfor (; !x;) var b = a;",
    );
    // The `for` variant relocates an inner `for` with a var init into the
    // bare body slot.
    test_smallest(
        "function a() { return b; } for (;;) { if (x) break; for (var b = a;;) break; } void a;",
        "function a() {\n\treturn b;\n}\nfor (; !x;) for (var b = a;;) break;",
    );
}

// A symbol declared both by a candidate site and a non-candidate site must
// stay consistent at BOTH removal sites.
#[test]
fn recursive_function_with_var_redeclaration() {
    // The array init has a specialized (residue-leaving) handler, so the
    // declarator site is a non-candidate and its references root from live
    // context: the function site's removal is enabled, the residue survives.
    test_smallest("function f() { f() } var f = [g()];", "g();");
    test_same_smallest("function f() { f() } var f = [f];");
}

// For-init declarators are not candidates either; the self-referencing
// init roots its own binding.
#[test]
fn keep_recursive_for_init_declarator() {
    test_same_smallest("for (let f = () => f();;) break;");
}

// A dead peer's removal (`g2`) frees the single-use temp `t` mid-pass, and
// substitution rewrites `d`'s init — historically the poisoning shape while
// declarator candidacy existed. Now `d` is never a candidate: its init
// roots `g` from any shape, so the cycle survives the rewrite untouched.
#[test]
fn keep_cycle_after_single_use_substitution_into_declarator() {
    test_smallest(
        "var t = console.log(1); var d = [t, g, ...'xy'].length; function g() { d(), g() } function g2() { t; g2() } let flag = false; if (flag) d;",
        "var d = [console.log(1), g, ...'xy'].length; function g() { d(), g() }",
    );
}

// `using` is a position gate (removal always bails on `using` declarators)
// and it is load-bearing wrong-code protection: without it `u` would be
// admitted (identifier init, pure and non-specialized), the u<->p cycle
// would be dead, and `var p` removed — while `using u = p` survives,
// referencing a deleted binding.
#[test]
fn keep_using_declarator_cycle() {
    test_same_smallest(
        "function o() { using u = p; var p = function() { u() }; return 1 } g(o());",
    );
    test_same_smallest(
        "async function o() { await using u = p; var p = function() { u() }; return 1 } g(o());",
    );
}

// The class arm of the position force-root is a separate code path from the
// function arm (`collect_enter_class` / the debug walk's `visit_class`):
// `export class` carries no reference, so without the class-site force-root
// the A<->B cycle would be dead and a live module export deleted.
#[test]
fn keep_exported_class_cycle() {
    test_same_smallest("export class A { m() { new B() } } class B { m() { new A() } }");
    test_same_smallest("export default class A { m() { new B() } } class B { m() { new A() } }");
}

// Script-root class bindings are cross-script observable, like vars — and
// classes are not candidates in any mode, so both modes keep the cycle.
#[test]
fn keep_recursive_class_in_script_mode_top_level() {
    let options = CompressOptions::smallest();
    test_same_options_source_type(
        "class A { m() { new B() } } class B { m() { new A() } }",
        SourceType::cjs().with_script(true),
        &options,
    );
    test_same_smallest(
        "class A {\n\tm() {\n\t\tnew B();\n\t}\n}\nclass B {\n\tm() {\n\t\tnew A();\n\t}\n}",
    );
}

// A dropped direct eval must re-enable the analysis: the initial compute
// skips the whole program while the root scope carries `DirectEval`, so only
// the `eval_dropped` recompute trigger lets a later pass remove the cycle.
#[test]
fn remove_recursive_function_after_eval_dropped() {
    test_smallest("if (false) eval('x'); function f() { f() }", "");
}

#[test]
fn remove_unused_import_specifiers() {
    let options = CompressOptions::smallest();

    test_options("import a from 'a'", "import 'a';", &options);
    test_options("import a from 'a'; foo()", "import 'a'; foo();", &options);
    test_same_options(
        "import a from 'a'",
        &CompressOptions {
            treeshake: TreeShakeOptions {
                invalid_import_side_effects: true,
                ..TreeShakeOptions::default()
            },
            ..CompressOptions::smallest()
        },
    );

    test_options("import { a } from 'a'", "import 'a';", &options);
    test_options("import { a, b } from 'a'", "import 'a';", &options);

    test_options("import * as a from 'a'", "import 'a';", &options);

    test_options("import a, { b } from 'a'", "import 'a';", &options);
    test_options("import a, * as b from 'a'", "import 'a';", &options);

    test_same_options("import a from 'a'; foo(a);", &options);
    test_same_options("import { a } from 'a'; foo(a);", &options);
    test_same_options("import * as a from 'a'; foo(a);", &options);
    test_same_options("import a, { b } from 'a'; foo(a, b);", &options);

    test_options("import { a, b } from 'a'; foo(a);", "import { a } from 'a'; foo(a);", &options);
    test_options(
        "import { a, b, c } from 'a'; foo(b);",
        "import { b } from 'a'; foo(b);",
        &options,
    );
    test_options("import a, { b } from 'a'; foo(a);", "import a from 'a'; foo(a);", &options);
    test_options("import a, { b } from 'a'; foo(b);", "import { b } from 'a'; foo(b);", &options);

    test_options(
        "import a from 'a'; import { b } from 'b'; if (false) { console.log(b) }",
        "import 'a'; import 'b';",
        &options,
    );

    test_same_options("import 'a';", &options);

    test_options("import {} from 'a'", "import 'a';", &options);

    test_options(
        "import a from 'a' with { type: 'json' }",
        "import 'a' with { type: 'json' };",
        &options,
    );
    test_options(
        "import {} from 'a' with { type: 'json' }",
        "import 'a' with { type: 'json' };",
        &options,
    );

    test_options("import { a as b } from 'a'", "import 'a';", &options);
    test_same_options("import { a as b } from 'a'; foo(b);", &options);

    test_same_options("import { a } from 'a'; export { a };", &options);
    // Keep imports when direct eval is present
    test_same_options("import { a } from 'a'; eval('a');", &options);
    test_same_options("import a from 'a'; eval('a');", &options);
    test_same_options("import * as a from 'a'; eval('a');", &options);
    test_same_options("import { a } from 'a'; function f() { eval('a'); }", &options);
}

#[test]
fn remove_unused_import_source_statement() {
    let options = CompressOptions::smallest();

    test_options("import source a from 'a'", "", &options);
    test_options("import source a from 'a'; if (false) { console.log(a) }", "", &options);
    test_same_options("import source a from 'a'; foo(a);", &options);
    test_same_options(
        "import source a from 'a'",
        &CompressOptions {
            treeshake: TreeShakeOptions {
                invalid_import_side_effects: true,
                ..TreeShakeOptions::default()
            },
            ..CompressOptions::smallest()
        },
    );
}

// `Normalize` strips these parens at `exit_expression`, after the
// declarator's enter hook ran — the shape-staleness axis that made
// declarator candidacy expensive to keep sound. Declarators are never
// candidates now, so the class init's reference to `a` is a root and the
// whole shape survives every paren/fold rewrite.
#[test]
fn keep_cycle_with_parenthesized_residue_init() {
    // The parens in the INPUT are the whole point: they are what the enter
    // hook sees and `Normalize` then strips.
    test_smallest(
        "function a() { b(); } var b = (class { static x = a; });",
        "function a() {\n\tb();\n}\nvar b = class {\n\tstatic x = a;\n};",
    );
    // Same shift through the other residue-leaving kinds.
    test_smallest(
        "function a() { b(); } var b = ([a]); console.log(1);",
        "function a() {\n\tb();\n}\nvar b = [a];\nconsole.log(1);",
    );
}

// A force-root only keeps a symbol out of the DEAD set. The removal sites also
// ask `symbol_is_unused` — and this analysis is what drives a count to zero, by
// deleting the dead cycle that held the last reference. So a force-rooted symbol
// whose surviving references all sat inside a dead cycle reaches refcount 0 and
// the COUNT arm deletes it, defeating the force-root entirely. Both shapes below
// were wrong code; both are fixed by `symbol_is_pinned`.

// The position force-root, same bypass. `export var f;` carries no reference, so
// only the position gate keeps `f` live — but the initializing redeclaration is a
// perfectly removable site, and once the d1<->d2 cycle holding `f`'s only
// reference is deleted, the count arm strips the initializer and importers see
// `undefined`. Silent, idempotent, and reachable in DCE mode (rolldown's
// per-module treeshake preprocess), which is what makes it worth pinning.
#[test]
fn keep_exported_var_initializer_when_a_dead_cycle_held_its_only_reference() {
    test_smallest(
        "export var f;\nvar f = function () { return 'F' };\nfunction d1() { console.log(f); return d2() }\nfunction d2() { return d1() }",
        "export var f;\nvar f = function() {\n\treturn 'F';\n};",
    );
}

// Pins must protect every count-based removal, not only declaration sites.
// Deleting the dead cycle removes the last ordinary read of `f`; assignments
// and member writes are still observable through the exported binding.
#[test]
fn keep_exported_binding_writes_when_a_dead_cycle_held_its_other_reads() {
    test_smallest(
        "export var f; var f = 0; function d1() { console.log(f); d2() } function d2() { d1() } f = 1;",
        "export var f;\nvar f = 0;\nf = 1;",
    );
    test_smallest(
        "export var f; var f = {}; function d1() { console.log(f); d2() } function d2() { d1() } f.x = 1;",
        "export var f;\nvar f = {};\nf.x = 1;",
    );
}

// The collection arms for ESM modules only: in a script or CommonJS source
// the feature's core shape — a dead function cycle — must survive
// byte-unchanged (exactly `main`'s behavior, at zero cost). Sloppy sources
// carry observability the reference model cannot express (script-globals,
// Annex B block-function aliases); enabling them is deliberate follow-up
// work, and this test is the OFF-path proof until then.
#[test]
fn analysis_off_for_non_module_sources() {
    let options = CompressOptions::smallest();
    let cycle = "function c() {\n\td();\n}\nfunction d() {\n\tc();\n}\nconsole.log(\"k\");";
    test_same_options_source_type(cycle, SourceType::cjs().with_script(true), &options);
    test_same_options_source_type(cycle, SourceType::cjs(), &options);
}

// A pin can be released when unreachable-code removal deletes a `for..of`
// head. Usually the binding disappears with it; a `var` head can also share
// its symbol with a surviving sibling declaration, in which case the stale
// pin may have vetoed a removal and its release must request another pass.
#[test]
fn remove_unreachable_for_of_head_with_pinned_binding() {
    test_smallest(
        "export function f() { return 1; for (const x of arr) g(x); }",
        "export function f() {\n\treturn 1;\n}",
    );
    test_smallest(
        "var f = 1; function d1() { f; d2() } function d2() { d1() } if (false) for (var f of xs) {} export {};",
        "export {};",
    );
    test_smallest("if (false) for (var f of xs) {} f = 1; export {};", "export {};");
}

// The pin veto must also gate `is_expression_result_unused`
// (`substitute_alternate_syntax`): it consults the same reference count the
// removal sites do, and a dead cycle's removal discards the references it
// held, so an exported binding reaches count zero while importers still
// observe it. Without the veto, the empty async/generator IIFE arms
// collapse the initializer to `void 0` — importers would read `undefined`
// instead of a Promise / Generator object. (The pure-arrow arms share the
// gate but their shapes dissolve on pass 1 via `try_take_iife_body`,
// before the count can zero; the async/generator family keeps its shape,
// which is what makes this reachable.)
#[test]
fn keep_exported_iife_init_when_a_dead_cycle_held_its_only_reference() {
    test_smallest(
        "export var f; var f = (async () => {})(); function d1() { f(); return d2() } function d2() { return d1() }",
        "export var f;\nvar f = (async () => {})();",
    );
    test_smallest(
        "export var g; var g = (function* () {})(); function d1() { g; return d2() } function d2() { return d1() }",
        "export var g;\nvar g = (function* () {})();",
    );
}

#[test]
fn remove_unused_import_defer_statements() {
    let options = CompressOptions::smallest();

    test_options("import defer * as a from 'a'", "", &options);
    test_options("import defer * as a from 'a'; if (false) { console.log(a.foo) }", "", &options);
    test_same_options("import defer * as a from 'a'; foo(a);", &options);
    test_same_options("import defer * as a from 'a'; foo(a.bar);", &options);
    test_same_options(
        "import defer * as a from 'a'",
        &CompressOptions {
            treeshake: TreeShakeOptions {
                invalid_import_side_effects: true,
                ..TreeShakeOptions::default()
            },
            ..CompressOptions::smallest()
        },
    );
}

// The debug oracle's export flag must not leak through an arrow:
// `export default (w) => { function f() {} }` declares an ordinary
// candidate, not an exported binding. Pre-fix, the ground-truth walk
// demanded a pin for `f` that the (correct) collection never granted,
// panicking the pin net on any flush that carried new dead bits — found
// by monitor-oxc on less@4.6.4's error-reporting.js within minutes of
// the oracle landing.
#[test]
fn pin_oracle_ignores_declarations_inside_exported_arrow() {
    test_smallest(
        "export default () => { function pinned() {} pinned(); }; function dead1() { dead2() } function dead2() { dead1() }",
        "export default () => {};",
    );
}
