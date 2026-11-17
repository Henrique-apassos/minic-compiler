import Scanner.Basic

-- ══════════════════════════════════════════════
-- 1. A GRAMÁTICA COMO DADO + AÇÕES SEMÂNTICAS
-- ══════════════════════════════════════════════

/-- Símbolo de uma produção: terminal (um token do scanner) ou não-terminal (um nome). -/
inductive Sym where
  | t  (k : TokenKind)
  | nt (name : String)
  deriving Repr, BEq, Inhabited

/-- Papel semântico do não-terminal para geração automática de `Parser/ToAst.lean`. -/
inductive NtKind where
  | baseType  -- `toBaseType : ParseTree → Except String MType`
  | type      -- `toType : ParseTree → Except String MType` (recursiva à esquerda: `Type [ ]`)
  | binOp     -- `toBinOp : ParseTree → Except String BinOp`
  | expr      -- `toExpr : ParseTree → Except String (Expr Unit)`
  | args      -- `toArgs : ParseTree → Except String (List (Expr Unit))`
  | optExpr   -- `toOptExpr : ParseTree → Except String (Option (Expr Unit))`
  | stmt      -- `toStmt : ParseTree → Except String (Stmt Unit)`
  | elseOpt   -- `toElseOpt : ParseTree → Except String (Option (Stmt Unit))`
  | block     -- `toBlock : ParseTree → Except String (Stmt Unit)`
  | stmtList  -- `toStmtList : ParseTree → Except String (List (Stmt Unit))`
  | param     -- `toParam : ParseTree → Except String (MType × String)`
  | params    -- `toParams : ParseTree → Except String (List (MType × String))`
  | funDecl   -- `toFun : ParseTree → Except String (FunDecl Unit)`
  | funList   -- `toFunList : ParseTree → Except String (Program Unit)`
  | program   -- `toProgram : ParseTree → Except String (Program Unit)`
  | custom    -- gramáticas de teste sem geração de AST
  deriving Repr, BEq, Inhabited

/-- Uma produção `lhs := rhs` com sua ação de construção da AST (`action`). -/
structure Production where
  id     : Nat        -- posição global na gramática (0, 1, 2, ...)
  lhs    : String
  alt    : Nat        -- índice da alternativa dentro de `lhs` (0 = primeira)
  rhs    : List Sym
  kind   : NtKind := .custom
  action : String := ""
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

end Grammar

/-- Construtor simples de gramática (sem ações de AST, usado nos testes do gerador). -/
def mkGrammar (start : String) (rules : List (String × List (List Sym))) : Grammar :=
  let prods := rules.foldl (init := #[]) fun acc (lhs, alts) =>
    (alts.zipIdx).foldl (init := acc) fun acc (rhs, a) =>
      acc.push { id := acc.size, lhs := lhs, alt := a, rhs := rhs }
  { start := start, prods := prods }

/-- Construtor de gramática com ações semânticas para geração automática da AST. -/
def mkAstGrammar (start : String) (rules : List (String × NtKind × List (List Sym × String))) : Grammar :=
  let prods := rules.foldl (init := #[]) fun acc (lhs, kind, alts) =>
    (alts.zipIdx).foldl (init := acc) fun acc ((rhs, act), a) =>
      acc.push { id := acc.size, lhs := lhs, alt := a, rhs := rhs, kind := kind, action := act }
  { start := start, prods := prods }

private abbrev N := Sym.nt
private abbrev T := Sym.t

/-- Nível binário com token direto (`or`, `and`): `nt := nt TOK next | next`.
Recursão à esquerda: o LR(1) a aceita, e a árvore já pende para a esquerda. -/
private def binTokLevel (nt : String) (opTok : TokenKind) (opAst : String) (nextNt : String) :
    List (String × NtKind × List (List Sym × String)) := [
  (nt, .expr, [
    ([N nt, T opTok, N nextNt], s!"do pure (.bin {opAst} (← toExpr s0) (← toExpr s2) ())"),
    ([N nextNt],                "toExpr s0")
  ])
]

/-- Nível binário com não-terminal de operador (`Rel`, `Add`, `Mul`): `nt := nt OP next | next`. -/
private def binNtLevel (nt opNt nextNt : String) :
    List (String × NtKind × List (List Sym × String)) := [
  (nt, .expr, [
    ([N nt, N opNt, N nextNt], "do pure (.bin (← toBinOp s1) (← toExpr s0) (← toExpr s2) ())"),
    ([N nextNt],               "toExpr s0")
  ])
]

-- ══════════════════════════════════════════════
-- 2. GRAMÁTICA DO MINIC (FONTE ÚNICA DA VERDADE)
-- ══════════════════════════════════════════════

def minicGrammar : Grammar := mkAstGrammar "Program" ([
  -- Programa e funções
  ("Program", .program, [
    ([N "FunList", T .eof], "toFunList s0")
  ]),
  ("FunList", .funList, [
    ([N "FunList", N "FunDecl"], "do pure ((← toFunList s0) ++ [← toFun s1])"),
    ([],                         "pure []")
  ]),
  ("FunDecl", .funDecl, [
    ([N "Type", T .id, T .lparen, N "Params", T .rparen, N "Stmt"],
     "do pure { name := ← lexeme s1, params := ← toParams s3, ret := ← toType s0, body := ← toStmt s5 }")
  ]),
  ("Params", .params, [
    ([N "ParamList"], "toParams s0"),
    ([],              "pure []")
  ]),
  ("ParamList", .params, [
    ([N "ParamList", T .comma, N "Param"], "do pure ((← toParams s0) ++ [← toParam s2])"),
    ([N "Param"],                          "do pure [← toParam s0]")
  ]),
  ("Param", .param, [
    ([N "Type", T .id], "do pure (← toType s0, ← lexeme s1)")
  ]),

  -- Tipos: `T[][]` é `Type [ ]` aplicado duas vezes
  ("Type", .type, [
    ([N "Type", T .lbracket, T .rbracket], "do pure (.array (← toType s0))"),
    ([N "BaseType"],                       "toBaseType s0")
  ]),
  ("BaseType", .baseType, [
    ([T .kwInt],   "pure .int"),
    ([T .kwFloat], "pure .float"),
    ([T .kwBool],  "pure .bool"),
    ([T .kwStr],   "pure .str"),
    ([T .kwVoid],  "pure .void")
  ]),

  -- Comandos
  ("Stmt", .stmt, [
    ([N "Block"],                                    "toBlock s0"),
    ([N "IfStmt"],                                   "toStmt s0"),
    ([N "WhileStmt"],                                "toStmt s0"),
    ([N "ReturnStmt"],                               "toStmt s0"),
    ([N "DeclStmt"],                                 "toStmt s0"),
    ([T .id, T .lparen, N "Args", T .rparen, T .semi],
     "do pure (.call (← lexeme s0) (← toArgs s2))"),
    ([N "LValue", T .assign, N "Expr", T .semi],     "do pure (.assign (← toExpr s0) (← toExpr s2))")
  ]),
  -- Alvo de atribuição: `x`, `a[i]`, `a[i][j]`. O LR(1) decide entre `f(...)` e `x = ...`
  -- olhando o token depois do `id`, então não precisa fatorar `id`.
  ("LValue", .expr, [
    ([N "LValue", T .lbracket, N "Expr", T .rbracket], "do pure (.index (← toExpr s0) (← toExpr s2) ())"),
    ([T .id],                                          "do pure (.var (← lexeme s0) ())")
  ]),
  ("Block", .block, [
    ([T .lbrace, N "StmtList", T .rbrace], "do pure (.block (← toStmtList s1))")
  ]),
  ("StmtList", .stmtList, [
    ([N "StmtList", N "Stmt"], "do pure ((← toStmtList s0) ++ [← toStmt s1])"),
    ([],                       "pure []")
  ]),
  ("IfStmt", .stmt, [
    ([T .kwIf, N "Expr", N "Block", N "ElseOpt"],
     "do pure (.ifElse (← toExpr s1) (← toBlock s2) (← toElseOpt s3))")
  ]),
  ("ElseOpt", .elseOpt, [
    ([T .kwElse, N "Block"], "some <$> toBlock s1"),
    ([],                     "pure none")
  ]),
  ("WhileStmt", .stmt, [
    ([T .kwWhile, N "Expr", N "Block"], "do pure (.while (← toExpr s1) (← toBlock s2))")
  ]),
  ("ReturnStmt", .stmt, [
    ([T .kwReturn, N "OptExpr", T .semi], "do pure (.ret (← toOptExpr s1))")
  ]),
  ("OptExpr", .optExpr, [
    ([N "Expr"], "some <$> toExpr s0"),
    ([],         "pure none")
  ]),
  ("DeclStmt", .stmt, [
    ([N "Type", T .id, T .assign, N "Expr", T .semi],
     "do pure (.decl (← toType s0) (← lexeme s1) (← toExpr s3))")
  ]),
  ("Args", .args, [
    ([N "ArgList"], "toArgs s0"),
    ([],            "pure []")
  ]),
  ("ArgList", .args, [
    ([N "ArgList", T .comma, N "Expr"], "do pure ((← toArgs s0) ++ [← toExpr s2])"),
    ([N "Expr"],                        "do pure [← toExpr s0]")
  ]),

  -- Expressões, da precedência mais fraca para a mais forte
  ("Expr", .expr, [
    ([N "Or"], "toExpr s0")
  ])
]
++ binTokLevel "Or"  .kwOr  ".or"  "And"
++ binTokLevel "And" .kwAnd ".and" "Not"
++ [
  ("Not", .expr, [
    ([T .not, N "Not"], "do pure (.not (← toExpr s1) ())"),
    ([N "Rel"],         "toExpr s0")
  ])
]
++ binNtLevel "Rel" "RelOp" "Add"
++ binNtLevel "Add" "AddOp" "Mul"
++ binNtLevel "Mul" "MulOp" "Unary"
++ [
  ("Unary", .expr, [
    ([T .minus, N "Unary"], "do pure (.neg (← toExpr s1) ())"),
    ([N "Postfix"],         "toExpr s0")
  ]),
  ("Postfix", .expr, [
    ([N "Postfix", T .lbracket, N "Expr", T .rbracket], "do pure (.index (← toExpr s0) (← toExpr s2) ())"),
    ([N "Atom"],                                        "toExpr s0")
  ]),
  ("Atom", .expr, [
    ([T .numInt],                          "do pure (.lit (.int (← parseInt (← lexeme s0))) ())"),
    ([T .numFloat],                        "do pure (.lit (.float (← parseFloat (← lexeme s0))) ())"),
    ([T .stringLit],                       "do pure (.lit (.str (unquote (← lexeme s0))) ())"),
    ([T .kwTrue],                          "pure (.lit (.bool true) ())"),
    ([T .kwFalse],                         "pure (.lit (.bool false) ())"),
    ([T .id],                              "do pure (.var (← lexeme s0) ())"),
    ([T .id, T .lparen, N "Args", T .rparen], "do pure (.call (← lexeme s0) (← toArgs s2) ())"),
    ([T .lbracket, N "Args", T .rbracket], "do pure (.array (← toArgs s1) ())"),
    ([T .lparen, N "Expr", T .rparen],     "toExpr s1")
  ]),
  ("RelOp", .binOp, [
    ([T .eq],  "pure .eq"),
    ([T .neq], "pure .ne"),
    ([T .lt],  "pure .lt"),
    ([T .le],  "pure .le"),
    ([T .gt],  "pure .gt"),
    ([T .ge],  "pure .ge")
  ]),
  ("AddOp", .binOp, [
    ([T .plus],  "pure .add"),
    ([T .minus], "pure .sub")
  ]),
  ("MulOp", .binOp, [
    ([T .times], "pure .mul"),
    ([T .div],   "pure .div")
  ])
])
