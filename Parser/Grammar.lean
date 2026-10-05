import Scanner.Basic

-- ══════════════════════════════════════════════
-- 1. A GRAMÁTICA COMO DADO
-- ══════════════════════════════════════════════
-- Mesmo desenho do scanner: as regras são uma lista (como `lexicalRules`),
-- e o gerador (`Parser/First.lean`, `Parser/Table.lean`) calcula a tabela a partir dela.

/-- Símbolo de uma produção: terminal (um token do scanner) ou não-terminal (um nome). -/
inductive Sym where
  | t  (k : TokenKind)
  | nt (name : String)
  deriving Repr, BEq, Inhabited

/-- Uma produção `lhs := rhs`. `rhs = []` é ε. -/
structure Production where
  id  : Nat        -- posição global na gramática (0, 1, 2, ...)
  lhs : String
  alt : Nat        -- índice da alternativa dentro de `lhs` (0 = primeira)
  rhs : List Sym
  deriving Repr, Inhabited

structure Grammar where
  start : String
  prods : Array Production
  deriving Repr, Inhabited

namespace Grammar

/-- Não-terminais, na ordem em que aparecem. -/
def nonterminals (g : Grammar) : List String :=
  (g.prods.toList.map (·.lhs)).eraseDups

/-- Terminais usados nas produções, mais `eof`. -/
def terminals (g : Grammar) : List TokenKind :=
  let ts := g.prods.toList.flatMap fun p =>
    p.rhs.filterMap fun | .t k => some k | .nt _ => none
  (ts ++ [TokenKind.eof]).eraseDups

def prodsOf (g : Grammar) (a : String) : List Production :=
  g.prods.toList.filter (·.lhs == a)

/-- Não-terminais usados em algum lado direito mas sem nenhuma produção (deve ser vazio). -/
def undefinedNonterminals (g : Grammar) : List String :=
  let used := g.prods.toList.flatMap fun p =>
    p.rhs.filterMap fun | .nt n => some n | .t _ => none
  (used.filter (fun n => !(g.nonterminals.contains n))).eraseDups

end Grammar

/-- Monta a gramática a partir de `(não-terminal, [alternativa, alternativa, ...])`,
    numerando produções e alternativas automaticamente. -/
def mkGrammar (start : String) (rules : List (String × List (List Sym))) : Grammar :=
  let prods := rules.foldl (init := #[]) fun acc (lhs, alts) =>
    (alts.zipIdx).foldl (init := acc) fun acc (rhs, a) =>
      acc.push { id := acc.size, lhs := lhs, alt := a, rhs := rhs }
  { start := start, prods := prods }

private abbrev N := Sym.nt
private abbrev T := Sym.t

-- ══════════════════════════════════════════════
-- 2. GRAMÁTICA DO MINIC (forma LL(1))
-- ══════════════════════════════════════════════
-- Extraída do parser Rust de referência e reescrita para LL(1):
-- laços viram caudas recursivas à direita com ε, e prefixos comuns são fatorados
-- (`ID IdStmt` e `ID AtomRest` resolvem o que pediria 2 tokens de lookahead).
-- 42 não-terminais, 85 produções. A ORDEM DAS ALTERNATIVAS É O CONTRATO com a conversão para AST.

def minicGrammar : Grammar := mkGrammar "Program" [
  -- Programa e funções
  ("Program",    [[N "FunList", T .eof]]),
  ("FunList",    [[N "FunDecl", N "FunList"], []]),
  ("FunDecl",    [[N "Type", T .id, T .lparen, N "Params", T .rparen, N "Stmt"]]),
  ("Params",     [[N "Param", N "ParamsTail"], []]),
  ("ParamsTail", [[T .comma, N "Param", N "ParamsTail"], []]),
  ("Param",      [[N "Type", T .id]]),
  -- Tipos
  ("Type",       [[N "BaseType", N "Dims"]]),
  ("Dims",       [[T .lbracket, T .rbracket, N "Dims"], []]),
  ("BaseType",   [[T .kwInt], [T .kwFloat], [T .kwBool], [T .kwStr], [T .kwVoid]]),
  -- Comandos
  ("Stmt",       [[N "Block"], [N "IfStmt"], [N "WhileStmt"], [N "ReturnStmt"], [N "DeclStmt"],
                  [T .id, N "IdStmt", T .semi]]),
  ("IdStmt",     [[T .lparen, N "Args", T .rparen], [N "Indices", T .assign, N "Expr"]]),
  ("Indices",    [[T .lbracket, N "Expr", T .rbracket, N "Indices"], []]),
  ("Block",      [[T .lbrace, N "StmtList", T .rbrace]]),
  ("StmtList",   [[N "Stmt", N "StmtList"], []]),
  ("IfStmt",     [[T .kwIf, N "Expr", N "Block", N "ElseOpt"]]),
  ("ElseOpt",    [[T .kwElse, N "Block"], []]),
  ("WhileStmt",  [[T .kwWhile, N "Expr", N "Block"]]),
  ("ReturnStmt", [[T .kwReturn, N "OptExpr", T .semi]]),
  ("OptExpr",    [[N "Expr"], []]),
  ("DeclStmt",   [[N "Type", T .id, T .assign, N "Expr", T .semi]]),
  ("Args",       [[N "Expr", N "ArgsTail"], []]),
  ("ArgsTail",   [[T .comma, N "Expr", N "ArgsTail"], []]),
  -- Expressões, da precedência mais fraca para a mais forte
  ("Expr",       [[N "Or"]]),
  ("Or",         [[N "And", N "OrTail"]]),
  ("OrTail",     [[T .kwOr, N "And", N "OrTail"], []]),
  ("And",        [[N "Not", N "AndTail"]]),
  ("AndTail",    [[T .kwAnd, N "Not", N "AndTail"], []]),
  ("Not",        [[T .not, N "Not"], [N "Rel"]]),
  ("Rel",        [[N "Add", N "RelTail"]]),
  ("RelTail",    [[N "RelOp", N "Add", N "RelTail"], []]),
  ("Add",        [[N "Mul", N "AddTail"]]),
  ("AddTail",    [[N "AddOp", N "Mul", N "AddTail"], []]),
  ("Mul",        [[N "Unary", N "MulTail"]]),
  ("MulTail",    [[N "MulOp", N "Unary", N "MulTail"], []]),
  ("Unary",      [[T .minus, N "Unary"], [N "Postfix"]]),
  ("Postfix",    [[N "Atom", N "PostTail"]]),
  ("PostTail",   [[T .lbracket, N "Expr", T .rbracket, N "PostTail"], []]),
  ("Atom",       [[T .numInt], [T .numFloat], [T .stringLit], [T .kwTrue], [T .kwFalse],
                  [T .id, N "AtomRest"], [T .lbracket, N "Args", T .rbracket],
                  [T .lparen, N "Expr", T .rparen]]),
  ("AtomRest",   [[T .lparen, N "Args", T .rparen], []]),
  ("RelOp",      [[T .eq], [T .neq], [T .lt], [T .le], [T .gt], [T .ge]]),
  ("AddOp",      [[T .plus], [T .minus]]),
  ("MulOp",      [[T .times], [T .div]])
]

-- ══════════════════════════════════════════════
-- 3. GRAMÁTICA DE EXPRESSÕES DOS LIVROS-TEXTO (para testar o gerador)
-- ══════════════════════════════════════════════
-- E := T E' · E' := + T E' | ε · T := F T' · T' := * F T' | ε · F := ( E ) | id
-- FIRST/FOLLOW e tabela conhecidos (Aho et al., "Dragon Book", seção 4.4).

def exprGrammar : Grammar := mkGrammar "E" [
  ("E",  [[N "T", N "E'"]]),
  ("E'", [[T .plus, N "T", N "E'"], []]),
  ("T",  [[N "F", N "T'"]]),
  ("T'", [[T .times, N "F", N "T'"], []]),
  ("F",  [[T .lparen, N "E", T .rparen], [T .id]])
]

/-- Gramática com conflito de propósito: S := id | id + id (as duas começam com `id`). -/
def conflictGrammar : Grammar := mkGrammar "S" [
  ("S", [[T .id], [T .id, T .plus, T .id]])
]
