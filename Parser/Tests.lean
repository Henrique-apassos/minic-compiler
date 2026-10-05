import Parser

-- ══════════════════════════════════════════════
-- TESTES DO GERADOR DE PARSER  (rodar com `lake test`)
-- ══════════════════════════════════════════════
-- Executável compilado, não `#guard`: no interpretador cada teste reconstruiria o DFA do
-- scanner (10 mil transições) e a bateria levaria minutos. Compilado, roda em segundos.
-- Sai com código 1 se algum teste falhar, o que deixa o CI vermelho.

structure Check where
  name : String
  ok   : Bool
  info : String := ""

private def sameSet [BEq α] (a b : List α) : Bool :=
  a.all b.contains && b.all a.contains

private def isOk : Except ε α → Bool
  | .ok _ => true | .error _ => false

/-- O programa é aceito? Em caso de erro, devolve a mensagem para o relatório. -/
private def accepts (src : String) : Check :=
  match parseSource src with
  | .ok _ => { name := s!"aceita: {src}", ok := true }
  | .error e => { name := s!"aceita: {src}", ok := false, info := e.message }

/-- O programa é rejeitado exatamente na posição `line:col`? -/
private def rejectsAt (src : String) (line col : Nat) : Check :=
  match parseSource src with
  | .ok _ => { name := s!"rejeita: {src}", ok := false, info := "foi aceito" }
  | .error e =>
      { name := s!"rejeita em {line}:{col}: {src}", ok := e.line == line && e.column == col,
        info := e.message }

private def errMsg (r : Except ParseError ParseTree) : String :=
  match r with | .ok _ => "<aceito>" | .error e => e.message

-- ── 1. A gramática ─────────────────────────────

def grammarChecks : List Check := [
  { name := "miniC tem 42 não-terminais", ok := minicGrammar.nonterminals.length == 42 },
  { name := "miniC tem 85 produções",     ok := minicGrammar.prods.size == 85 },
  { name := "miniC sem não-terminal indefinido", ok := minicGrammar.undefinedNonterminals.isEmpty },
  { name := "gramática de livro sem não-terminal indefinido", ok := exprGrammar.undefinedNonterminals.isEmpty }
]

-- ── 2. Nulável, FIRST e FOLLOW (gramática de livro: respostas conhecidas) ──

def ea : Analysis := analyze exprGrammar

def analysisChecks : List Check := [
  { name := "nuláveis = {E', T'}",          ok := sameSet ea.nullable ["E'", "T'"] },
  { name := "FIRST(E) = { (, id }",         ok := sameSet (ea.firstOf "E")  [.lparen, .id] },
  { name := "FIRST(T) = { (, id }",         ok := sameSet (ea.firstOf "T")  [.lparen, .id] },
  { name := "FIRST(F) = { (, id }",         ok := sameSet (ea.firstOf "F")  [.lparen, .id] },
  { name := "FIRST(E') = { + }",            ok := sameSet (ea.firstOf "E'") [.plus] },
  { name := "FIRST(T') = { * }",            ok := sameSet (ea.firstOf "T'") [.times] },
  { name := "FOLLOW(E) = { ), eof }",       ok := sameSet (ea.followOf "E")  [.rparen, .eof] },
  { name := "FOLLOW(E') = { ), eof }",      ok := sameSet (ea.followOf "E'") [.rparen, .eof] },
  { name := "FOLLOW(T) = { +, ), eof }",    ok := sameSet (ea.followOf "T")  [.plus, .rparen, .eof] },
  { name := "FOLLOW(T') = { +, ), eof }",   ok := sameSet (ea.followOf "T'") [.plus, .rparen, .eof] },
  { name := "FOLLOW(F) = { *, +, ), eof }", ok := sameSet (ea.followOf "F")  [.times, .plus, .rparen, .eof] },
  { name := "miniC: FIRST(AddTail) = { +, - }",
    ok := sameSet (minicTable.analysis.firstOf "AddTail") [.plus, .minus] },
  { name := "miniC: FOLLOW(Expr) tem ; ) ] , {",
    ok := [TokenKind.semi, .rparen, .rbracket, .comma, .lbrace].all (minicTable.analysis.followOf "Expr").contains }
]

-- ── 3. A tabela LL(1) ──────────────────────────

def exprTable : LL1Table :=
  match buildTable exprGrammar with
  | .ok t => t
  | .error _ => panic! "a gramática de livro deveria ser LL(1)"

private def altOf (t : LL1Table) (a : String) (k : TokenKind) : Option Nat :=
  (t.lookup a k).map (·.alt)

def tableChecks : List Check := [
  { name := "gramática de livro é LL(1)", ok := isOk (buildTable exprGrammar) },
  { name := "tabela de livro tem 13 células", ok := exprTable.size == 13 },
  { name := "tabela[E, id] = T E'",    ok := altOf exprTable "E" .id == some 0 },
  { name := "tabela[E', )] = ε",       ok := altOf exprTable "E'" .rparen == some 1 },
  { name := "tabela[T', +] = ε",       ok := altOf exprTable "T'" .plus == some 1 },
  { name := "tabela[T', *] = * F T'",  ok := altOf exprTable "T'" .times == some 0 },
  { name := "tabela[F, id] = id",      ok := altOf exprTable "F" .id == some 1 },
  { name := "tabela[F, +] vazia (erro)", ok := (exprTable.lookup "F" .plus).isNone },
  { name := "gramática com conflito é recusada",
    ok := match buildTable conflictGrammar with
      | .error [c] => c.nt == "S" && c.tok == .id && c.prods == [0, 1]
      | _ => false },
  { name := "mensagem de conflito",
    ok := match buildTable conflictGrammar with
      | .error [c] => c.message conflictGrammar == "conflito em S com id: S.0 vs S.1"
      | _ => false },
  { name := "miniC é LL(1) (0 conflitos)", ok := isOk (buildTable minicGrammar) }
]

-- ── 4. O motor, na gramática de livro ──────────

private def parseExpr (src : String) : Except ParseError ParseTree :=
  parse exprTable (scan lexDFA src)

def exprEngineChecks : List Check := [
  { name := "a + b * c: árvore de derivação",
    ok := (parseExpr "a + b * c").toOption.map (·.toSExpr) ==
      some "(E.0 (T.0 (F.1 a) (T'.1)) (E'.0 + (T.0 (F.1 b) (T'.0 * (F.1 c) (T'.1))) (E'.1)))" },
  { name := "a + * c: erro",
    ok := errMsg (parseExpr "a + * c") == "1:5: encontrei '*', esperava '(' ou identificador",
    info := errMsg (parseExpr "a + * c") },
  { name := "a + b ): sobra token",
    ok := errMsg (parseExpr "a + b )") == "1:7: encontrei ')', esperava fim do arquivo",
    info := errMsg (parseExpr "a + b )") },
  { name := "(a + b: parêntese aberto",
    ok := errMsg (parseExpr "(a + b") == "1:7: encontrei fim do arquivo, esperava ')'",
    info := errMsg (parseExpr "(a + b") },
  { name := "a @ b: caractere inválido",
    ok := errMsg (parseExpr "a @ b") == "1:3: caractere não reconhecido '@'",
    info := errMsg (parseExpr "a @ b") }
]

-- ── 5. O motor no miniC: o contrato com a conversão para AST ──

/-- Um operando simples `x` como o motor o produz (cadeia Mul → Unary → Postfix → Atom). -/
private def opnd (x : String) : String :=
  s!"(Unary.1 (Postfix.0 (Atom.5 {x} (AtomRest.1)) (PostTail.1)))"

private def addOf (src : String) : Option ParseTree :=
  (parseSource src).toOption.bind (·.find? "Add")

def contractChecks : List Check := [
  { name := "a - b - c gera exatamente ParseTree.Example.subChain (com posições)",
    ok := (addOf "int main() { return a - b - c; }").map reprStr ==
      some (reprStr ParseTree.Example.subChain) },
  { name := "a * b + c: o * fica dentro do primeiro Mul (precedência)",
    ok := (addOf "int main() { return a * b + c; }").map (·.toSExpr) ==
      some s!"(Add.0 (Mul.0 {opnd "a"} (MulTail.0 (MulOp.0 *) {opnd "b"} (MulTail.1))) (AddTail.0 (AddOp.0 +) (Mul.0 {opnd "c"} (MulTail.1)) (AddTail.1)))" },
  { name := "programa vazio vira Program.0 (FunList.1) <eof>",
    ok := (parseSource "").toOption.map (·.toSExpr) == some "(Program.0 (FunList.1) <eof>)" }
]

-- ── 6. Programas miniC aceitos ─────────────────

def acceptChecks : List Check := [
  accepts "",
  accepts "int fatorial(int n) {\n  // comentário\n  if (n <= 1) { return 1; }\n  float x = 3.14;\n  int intx = 42;\n  return n * fatorial(n - 1);\n}",
  accepts "void main() { return; }",
  accepts "int f() return 1;",
  accepts "int soma(int a, int b) { return a + b; } int main() { int x = soma(1, 2); print(x); return 0; }",
  accepts "int main() { int i = 0; while i < 10 { i = i + 1; } return i; }",
  accepts "int main() { if x > 0 { y = 1; } else { y = -1; } }",
  accepts "int main() { if (a == b) { } }",
  accepts "bool f(bool a, bool b) { return !(a == b) and a or not_b; }",
  accepts "int main() { bool t = true; bool f = false; return 0; }",
  accepts "int[][] matriz(int n) { int[][] m = [[1, 2], [3, 4]]; m[0][1] = n; return m; }",
  accepts "int main() { int x = f(a, -b)[0] * (c + 2) / d; }",
  accepts "int main() { { { return 1; } } }",
  accepts "float media(float a, float b) { return (a + b) / 2.0; }",
  accepts "int main() { int x = - - 1; bool y = ! ! true; }",
  accepts "int main() { return a <= b; }"
]

-- ── 7. Programas miniC rejeitados, com a posição do erro ──

def rejectChecks : List Check := [
  rejectsAt "int main() { return a - ; }" 1 25,             -- falta operando
  rejectsAt "int main() { int x = 1 }" 1 24,                -- falta ;
  rejectsAt "int main() { int x; }" 1 19,                   -- declaração sem valor inicial
  rejectsAt "int main() { x + 1; }" 1 16,                   -- expressão solta não é comando
  rejectsAt "int main() { if x return 1; }" 1 19,           -- if sem bloco
  rejectsAt "int main() { } x" 1 16,                        -- lixo depois do programa
  rejectsAt "int main() { return (1 + 2; }" 1 27,           -- parêntese sem fechar
  rejectsAt "int main() { int y = &x; }" 1 22,              -- ponteiros fora da linguagem
  rejectsAt "int main() { return 1; } @" 1 26,              -- caractere desconhecido
  rejectsAt "int main( { }" 1 11,                           -- parâmetros malformados
  rejectsAt "main() { }" 1 1,                               -- função sem tipo de retorno
  rejectsAt "int main() {\n  return 1;\n" 3 1               -- bloco sem fechar: erro no eof
]

-- ══════════════════════════════════════════════

def allChecks : List (String × List Check) := [
  ("Gramática", grammarChecks),
  ("Nulável, FIRST e FOLLOW", analysisChecks),
  ("Tabela LL(1)", tableChecks),
  ("Motor (gramática de livro)", exprEngineChecks),
  ("Contrato com a AST", contractChecks),
  ("miniC aceitos", acceptChecks),
  ("miniC rejeitados", rejectChecks)
]

def main : IO UInt32 := do
  let mut failed := 0
  let mut total := 0
  for (group, checks) in allChecks do
    IO.println s!"── {group}"
    for c in checks do
      total := total + 1
      let mark := if c.ok then "ok  " else "FALHOU"
      let extra := if c.info.isEmpty then "" else s!"   ⟶ {c.info}"
      if !c.ok then failed := failed + 1
      IO.println s!"  {mark} {c.name.replace "\n" " "}{if c.ok then "" else extra}"
  IO.println s!"\n{total - failed}/{total} testes passaram."
  return (if failed == 0 then 0 else 1)
