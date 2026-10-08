import Tests.Harness

-- Portado de `MiniC/tests/parser.rs`. O nome de cada teste é o da função em Rust.
-- Fora de escopo, de propósito:
--   * `test_pointer_*` (5 testes): ponteiros ficam fora da primeira versão (DECISOES #11).
--   * `test_identifier_reject_*` tal como no Rust: lá o sub-parser `identifier` recusa
--     "1var"/"int"; aqui a recusa é do programa inteiro, então o teste checa isso.
-- Divergências de desenho, já testadas como tal:
--   * `-17` é `neg 17` (decisão #50), não um literal negativo como no Rust.
--   * `True` e `abc` são identificadores válidos; no Rust o sub-parser de literal os recusa.

-- ── Literais ───────────────────────────────────

def literais : List Test := [
  allOf "test_integer_positive"
    [expectExpr "42" (eInt 42), expectExpr "0" (eInt 0), expectExpr "12345" (eInt 12345)],
  allOf "test_integer_negative (vira neg)"
    [expectExpr "-17" (eNeg (eInt 17)), expectExpr "-0" (eNeg (eInt 0))],
  allOf "test_integer_reject (abc é id, 12.34 é real)"
    [expectExpr "abc" (eVar "abc"), expectExpr "12.34" (eFloat 12.34)],
  allOf "test_float"
    [expectExpr "3.14" (eFloat 3.14), expectExpr "0.5" (eFloat 0.5),
     expectExpr "-0.25" (eNeg (eFloat 0.25))],
  allOf "test_boolean" [expectExpr "true" (eBool true), expectExpr "false" (eBool false)],
  allOf "test_boolean_reject (True é id, 1 é inteiro)"
    [expectExpr "True" (eVar "True"), expectExpr "1" (eInt 1)],
  allOf "test_literal_combined"
    [expectExpr "42" (eInt 42), expectExpr "3.14" (eFloat 3.14), expectExpr "true" (eBool true)],
]

-- ── Identificadores ────────────────────────────

def identificadores : List Test := [
  allOf "test_identifier_simple"
    [expectExpr "x" (eVar "x"), expectExpr "count" (eVar "count"), expectExpr "_temp" (eVar "_temp")],
  allOf "test_identifier_with_digits"
    [expectExpr "var1" (eVar "var1"), expectExpr "max_value_42" (eVar "max_value_42")],
  allOf "test_identifier_reject_digit_start" [rejectExpr "1var"],
  allOf "test_identifier_reject_reserved"
    [rejectStmt "int true = 1;", rejectStmt "int false = 1;",
     rejectStmt "int int = 1;", rejectStmt "int void = 1;"],
  allOf "test_identifier_accept_true_prefix"
    [expectExpr "tru" (eVar "tru"), expectExpr "truex" (eVar "truex"),
     expectExpr "intx" (eVar "intx")]
]

-- ── Expressões ─────────────────────────────────

def expressoes : List Test := [
  allOf "test_primary_literal"
    [expectExpr "42" (eInt 42), expectExpr "true" (eBool true), expectExpr "x" (eVar "x")],
  allOf "test_arithmetic"
    [expectExpr "1 + 2" (eBin .add (eInt 1) (eInt 2)),
     expectExpr "10 - 3" (eBin .sub (eInt 10) (eInt 3)),
     expectExpr "4 * 5" (eBin .mul (eInt 4) (eInt 5)),
     expectExpr "-x" (eNeg (eVar "x"))],
  allOf "test_precedence_arithmetic"
    [expectExpr "1 + 2 * 3" (eBin .add (eInt 1) (eBin .mul (eInt 2) (eInt 3)))],
  allOf "test_parentheses"
    [expectExpr "(1 + 2) * 3" (eBin .mul (eBin .add (eInt 1) (eInt 2)) (eInt 3))],
  allOf "test_relational"
    [expectExpr "a == b" (eBin .eq (eVar "a") (eVar "b")),
     expectExpr "x < 5" (eBin .lt (eVar "x") (eInt 5)),
     expectExpr "1 + 2 < 5" (eBin .lt (eBin .add (eInt 1) (eInt 2)) (eInt 5))],
  allOf "test_complex_expression"
    [expectExpr "a >= (pi * r * r) + epsilon"
      (eBin .ge (eVar "a")
        (eBin .add (eBin .mul (eBin .mul (eVar "pi") (eVar "r")) (eVar "r")) (eVar "epsilon")))],
  allOf "test_boolean_expr"
    [expectExpr "true and false" (eBin .and (eBool true) (eBool false)),
     expectExpr "!x" (eNot (eVar "x")),
     expectExpr "x < 5 and y > 0"
       (eBin .and (eBin .lt (eVar "x") (eInt 5)) (eBin .gt (eVar "y") (eInt 0)))],
  allOf "test_invalid_trailing_op" [rejectExpr "1 +"],
  allOf "test_invalid_unbalanced_paren" [rejectExpr "(1 + 2", rejectExpr "1 + 2)"],
  -- Não vêm do Rust: travam o contrato da conversão (decisões #14 e #49).
  allOf "assoc_esquerda (a - b - c)"
    [expectExpr "a - b - c" (eBin .sub (eBin .sub (eVar "a") (eVar "b")) (eVar "c")),
     expectExpr "a / b * c" (eBin .mul (eBin .div (eVar "a") (eVar "b")) (eVar "c"))],
  allOf "not_abaixo_da_comparacao (!a == b)"
    [expectExpr "!a == b" (eNot (eBin .eq (eVar "a") (eVar "b")))]
]

-- ── Chamadas ───────────────────────────────────

def chamadas : List Test := [
  allOf "test_call_as_expression"
    [expectExpr "foo(1, 2)" (eCall "foo" [eInt 1, eInt 2])],
  allOf "test_call_no_args" [expectExpr "baz()" (eCall "baz" [])],
  allOf "test_call_in_expression"
    [expectExpr "foo(1) + 2" (eBin .add (eCall "foo" [eInt 1]) (eInt 2))],
  allOf "test_call_as_statement"
    [expectStmt "foo(1, 2);" (.call "foo" [eInt 1, eInt 2])]
]

-- ── Arrays ─────────────────────────────────────

def arrays : List Test := [
  allOf "test_array_literal"
    [expectExpr "[1, 2, 3]" (eArr [eInt 1, eInt 2, eInt 3])],
  allOf "test_empty_array" [expectExpr "[]" (eArr [])],
  allOf "test_index_read" [expectExpr "arr[i]" (eIdx (eVar "arr") (eVar "i"))],
  allOf "test_indexed_assignment"
    [expectStmt "arr[i] = 1;" (.assign (eIdx (eVar "arr") (eVar "i")) (eInt 1))],
  allOf "test_multidimensional_indexed_assignment"
    [expectStmt "arr[i][j] = x;"
      (.assign (eIdx (eIdx (eVar "arr") (eVar "i")) (eVar "j")) (eVar "x"))],
  allOf "test_nested_index"
    [expectExpr "arr[i][j]" (eIdx (eIdx (eVar "arr") (eVar "i")) (eVar "j"))],
  allOf "test_array_in_expression"
    [expectExpr "[1, 2][0]" (eIdx (eArr [eInt 1, eInt 2]) (eInt 0))]
]

-- ── Comandos ───────────────────────────────────

private def asg (x : String) (e : E) : S := .assign (eVar x) e

def comandos : List Test := [
  allOf "test_simple_assignment"
    [expectStmt "x = 42;" (asg "x" (eInt 42)), expectStmt "count = 0;" (asg "count" (eInt 0))],
  allOf "test_assignment_with_expression"
    [expectStmt "sum = a + b;" (asg "sum" (eBin .add (eVar "a") (eVar "b"))),
     expectStmt "flag = x < 5;" (asg "flag" (eBin .lt (eVar "x") (eInt 5)))],
  allOf "test_assignment_whitespace"
    [expectStmt "x=1;" (asg "x" (eInt 1)), expectStmt "x = 1;" (asg "x" (eInt 1)),
     expectStmt "x  =  1;" (asg "x" (eInt 1))],
  allOf "test_invalid_assignment"
    [rejectStmt "= 1", rejectStmt "x", rejectStmt "1 = x;"],
  allOf "test_decl_statement"
    [expectStmt "int x = 42;" (.decl .int "x" (eInt 42)),
     expectStmt "float y = 3.14;" (.decl .float "y" (eFloat 3.14)),
     expectStmt "int[] arr = [1, 2, 3];"
       (.decl (.array .int) "arr" (eArr [eInt 1, eInt 2, eInt 3]))],
  allOf "decl_array_multidimensional (Rust limita a 2, DECISOES #17)"
    [expectStmt "int[][][] m = [];" (.decl (.array (.array (.array .int))) "m" (eArr []))],
  allOf "test_if_without_else"
    [expectStmt "if x { y = 1; }" (.ifElse (eVar "x") (.block [asg "y" (eInt 1)]) none)],
  allOf "test_if_with_else"
    [expectStmt "if x { y = 1; } else { y = 0; }"
      (.ifElse (eVar "x") (.block [asg "y" (eInt 1)]) (some (.block [asg "y" (eInt 0)])))],
  allOf "test_nested_if"
    [expectStmt "if a { if b { x = 1; } else { x = 2; } }"
      (.ifElse (eVar "a")
        (.block [.ifElse (eVar "b") (.block [asg "x" (eInt 1)])
          (some (.block [asg "x" (eInt 2)]))])
        none)],
  allOf "test_if_whitespace"
    [expectStmt "if x { y = 1; }" (.ifElse (eVar "x") (.block [asg "y" (eInt 1)]) none),
     expectStmt "if  x  { y  =  1; }" (.ifElse (eVar "x") (.block [asg "y" (eInt 1)]) none)],
  allOf "test_invalid_if" [rejectStmt "if x", rejectStmt "if x y = 1;"],
  allOf "test_simple_while"
    [expectStmt "while x { y = 1; }" (.while (eVar "x") (.block [asg "y" (eInt 1)]))],
  allOf "test_while_with_expression"
    [expectStmt "while i < 10 { i = i + 1; }"
      (.while (eBin .lt (eVar "i") (eInt 10))
        (.block [asg "i" (eBin .add (eVar "i") (eInt 1))]))],
  allOf "test_nested_while"
    [expectStmt "while a { while b { x = 1; } }"
      (.while (eVar "a") (.block [.while (eVar "b") (.block [asg "x" (eInt 1)])]))],
  allOf "test_while_whitespace"
    [expectStmt "while x { y = 1; }" (.while (eVar "x") (.block [asg "y" (eInt 1)])),
     expectStmt "while  x  { y  =  1; }" (.while (eVar "x") (.block [asg "y" (eInt 1)]))],
  allOf "test_invalid_while" [rejectStmt "while x", rejectStmt "while x y = 1;"],
  allOf "test_empty_block" [expectStmt "{}" (.block [])],
  allOf "test_block_single_statement"
    [expectStmt "{ x = 1; }" (.block [asg "x" (eInt 1)])],
  allOf "test_block_multiple_statements"
    [expectStmt "{ x = 1; y = 2; }" (.block [asg "x" (eInt 1), asg "y" (eInt 2)])],
  allOf "test_block_in_if_body"
    [expectStmt "if x { a = 1; b = 2; }"
      (.ifElse (eVar "x") (.block [asg "a" (eInt 1), asg "b" (eInt 2)]) none)],
  allOf "test_block_in_while_body"
    [expectStmt "while x { a = 1; b = 2; }"
      (.while (eVar "x") (.block [asg "a" (eInt 1), asg "b" (eInt 2)]))],
  -- `return` não é testado em parser.rs; só aparece nos fixtures e no interpretador.
  allOf "return_com_e_sem_valor"
    [expectStmt "return 1;" (.ret (some (eInt 1))), expectStmt "return;" (.ret none)]
]

-- ── Funções ────────────────────────────────────

def funcoes : List Test := [
  allOf "test_fun_decl_with_params"
    [expectFun "void foo(int x, int y) { x = x + y; }"
      { name := "foo", params := [(.int, "x"), (.int, "y")], ret := .void
        body := .block [asg "x" (eBin .add (eVar "x") (eVar "y"))] }],
  allOf "test_fun_decl_old_syntax_reject"
    [rejectFun "def foo(int x) void x = 1", rejectFun "void bar(x) x = 1"],
  allOf "test_fun_decl_no_params"
    [expectFun "void bar() { x = 1; }"
      { name := "bar", params := [], ret := .void, body := .block [asg "x" (eInt 1)] }],
  allOf "test_block_in_function_body"
    [expectFun "void foo(int x, int y) { x = x + 1; y = y + 1; }"
      { name := "foo", params := [(.int, "x"), (.int, "y")], ret := .void
        body := .block [asg "x" (eBin .add (eVar "x") (eInt 1)),
                        asg "y" (eBin .add (eVar "y") (eInt 1))] }],
  allOf "tipo_de_retorno_e_array_nos_parametros"
    [expectFun "int[] f(float[] v, bool b) { return v; }"
      { name := "f", params := [(.array .float, "v"), (.bool, "b")], ret := .array .int
        body := .block [.ret (some (eVar "v"))] }]
]
