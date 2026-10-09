import Parser

-- ══════════════════════════════════════════════
-- TESTES DO PARSER  (rodar com `lake test`)
-- ══════════════════════════════════════════════
-- Executável compilado: no interpretador (`#guard`) cada teste reconstruiria o DFA do scanner.
-- Sai com código 1 se algum teste falhar.

private def accepts (src : String) : Bool :=
  match parseSource src with | .ok _ => true | .error _ => false

/-- Rejeitado exatamente em `line:col`? -/
private def rejectsAt (src : String) (line col : Nat) : Bool :=
  match parseSource src with
  | .ok _ => false
  | .error e => e.found.line == line && e.found.column == col

/-- A expressão de `int main() { return <e>; }`, impressa. -/
private def exprOf (e : String) : String :=
  match parseProgram s!"int main() \{ return {e}; }" with
  | .ok [{ body := .block [.ret (some x)], .. }] => x.show
  | .ok _ => "?"
  | .error m => "erro: " ++ m

/-- Troca quebras de linha e espaços repetidos por um espaço só. -/
private def squash (s : String) : String :=
  String.ofList ((s.toList.map fun c => if c.isWhitespace then ' ' else c).foldr
    (fun c acc => match acc with | ' ' :: _ => if c == ' ' then acc else c :: acc | _ => c :: acc) [])

/-- O corpo de `int main() { <s> }`, impresso numa linha. -/
private def stmtOf (s : String) : String :=
  match parseProgram s!"int main() \{ {s} }" with
  | .ok [{ body := .block [x], .. }] =>
      squash (x.show "")
  | .ok _ => "?"
  | .error m => "erro: " ++ m

def checks : List (String × Bool) := [
  ("gramática: 42 não-terminais e 85 produções",
    minicGrammar.nonterminals.length == 42 && minicGrammar.prods.size == 85),
  ("tabela LL(1) sem conflitos",
    match buildTable minicGrammar with | .ok _ => true | .error _ => false),
  ("aceita o programa de exemplo",
    accepts "int fatorial(int n) {\n  // comentário\n  if (n <= 1) { return 1; }\n  float x = 3.14;\n  return n * fatorial(n - 1);\n}"),
  ("aceita while, if/else, arrays e chamadas",
    accepts "int main() { int[] v = [1, 2]; int i = 0; while i < 2 { if v[i] > 0 { print(v[i]); } else { v[i] = -1; } i = i + 1; } return 0; }"),
  ("aceita programa vazio", accepts ""),
  ("rejeita operando faltando em 1:25", rejectsAt "int main() { return a - ; }" 1 25),
  ("rejeita ; faltando em 1:24",        rejectsAt "int main() { int x = 1 }" 1 24),
  ("rejeita lixo depois do programa em 1:16", rejectsAt "int main() { } x" 1 16),
  -- AST
  ("AST: a - b - c é (a - b) - c",
    match parseProgram "int main() { return a - b - c; }" with
    | .error _ => false
    | .ok p => p == [{ name := "main", params := [], ret := .int, body := .block [.ret (some
        (.bin .sub (.bin .sub (.var "a" ()) (.var "b" ()) ()) (.var "c" ()) ()))] }]),
  ("AST: precedência 2 * 3 + 4",   exprOf "2 * 3 + 4" == "((2 * 3) + 4)"),
  ("AST: 1 + 2 * 3",               exprOf "1 + 2 * 3" == "(1 + (2 * 3))"),
  ("AST: a or b and c",            exprOf "a or b and c" == "(a or (b and c))"),
  ("AST: chamada, menos e índice", exprOf "f(x, -y)[0]" == "f(x, -y)[0]"),
  ("AST: !(a == b)",               exprOf "!(a == b)" == "!(a == b)"),
  ("AST: ! abaixo da comparação",  exprOf "!a == b" == "!(a == b)"),
  ("AST: a[i][j]",                 exprOf "a[i][j]" == "a[i][j]"),
  ("AST: real 3.14",               exprOf "3.14" == "3.140000"),
  ("AST: x = [1, 2];",             stmtOf "x = [1, 2];" == "x = [1, 2];"),
  ("AST: m[i][j] = 0;",            stmtOf "m[i][j] = 0;" == "m[i][j] = 0;"),
  ("AST: int[][] m = g();",        stmtOf "int[][] m = g();" == "int[][] m = g();"),
  ("AST: if/else",                 stmtOf "if x { f(); } else { g(1); }" == "if x { f(); } else { g(1); }"),
  ("AST: while e return vazio",    stmtOf "while i < 2 { return; }" == "while (i < 2) { return; }"),
  ("AST: parâmetros",
    match parseProgram "void f(int a, float[] b) { }" with
    | .ok [f] => f.params == [(.int, "a"), (.array .float, "b")] && f.ret == .void
    | _ => false),
  ("AST: erro de sintaxe sai como mensagem",
    match parseProgram "int main() { return a - ; }" with
    | .ok _ => false
    | .error m => m == "1:25: encontrei ';', esperava identificador, '(', '[', '-', número inteiro, número real, texto, 'true' ou 'false'")
]

def main : IO UInt32 := do
  let mut failed := 0
  for (name, ok) in checks do
    IO.println s!"{if ok then "ok    " else "FALHOU"} {name}"
    if !ok then failed := failed + 1
  IO.println s!"{checks.length - failed}/{checks.length} testes passaram."
  return (if failed == 0 then 0 else 1)
