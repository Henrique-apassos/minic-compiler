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
  | dims      -- `wrapDims (base : MType) : ParseTree → Except String MType`
  | type      -- `toType : ParseTree → Except String MType`
  | binOp     -- `toBinOp : ParseTree → Except String BinOp`
  | expr      -- `toExpr : ParseTree → Except String (Expr Unit)`
  | atomRest  -- `toAtomRest (idName : String) : ParseTree → Except String (Expr Unit)`
  | exprTail  -- `foldTail (acc : Expr Unit) : ParseTree → Except String (Expr Unit)`
  | indexTail -- `foldIndex (acc : Expr Unit) : ParseTree → Except String (Expr Unit)`
  | args      -- `toArgs : ParseTree → Except String (List (Expr Unit))`
  | optExpr   -- `toOptExpr : ParseTree → Except String (Option (Expr Unit))`
  | idStmt    -- `toIdStmt (idName : String) : ParseTree → Except String (Stmt Unit)`
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

/-- Auxiliar para nível de operador binário com token direto (`or`, `and`). -/
private def binTokLevel (nt tailNt : String) (opTok : TokenKind) (opAst : String) (nextNt : String) :
    List (String × NtKind × List (List Sym × String)) := [
  (nt, .expr, [
    ([N nextNt, N tailNt], "do foldTail (← toExpr s0) s1")
  ]),
  (tailNt, .exprTail, [
    ([T opTok, N nextNt, N tailNt], s!"do foldTail (.bin {opAst} acc (← toExpr s1) ()) s2"),
    ([], "pure acc")
  ])
]

/-- Auxiliar para nível de operador binário com não-terminal de operador (`Rel`, `Add`, `Mul`). -/
private def binNtLevel (nt tailNt opNt nextNt : String) :
    List (String × NtKind × List (List Sym × String)) := [
  (nt, .expr, [
    ([N nextNt, N tailNt], "do foldTail (← toExpr s0) s1")
  ]),
  (tailNt, .exprTail, [
    ([N opNt, N nextNt, N tailNt], "do foldTail (.bin (← toBinOp s0) acc (← toExpr s1) ()) s2"),
    ([], "pure acc")
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
    ([N "FunDecl", N "FunList"], "do pure ((← toFun s0) :: (← toFunList s1))"),
    ([],                         "pure []")
  ]),
  ("FunDecl", .funDecl, [
    ([N "Type", T .id, T .lparen, N "Params", T .rparen, N "Stmt"],
     "do pure { name := ← lexeme s1, params := ← toParams s3, ret := ← toType s0, body := ← toStmt s5 }")
  ]),
  ("Params", .params, [
    ([N "Param", N "ParamsTail"], "do pure ((← toParam s0) :: (← toParams s1))"),
    ([],                          "pure []")
  ]),
  ("ParamsTail", .params, [
    ([T .comma, N "Param", N "ParamsTail"], "do pure ((← toParam s1) :: (← toParams s2))"),
    ([],                                    "pure []")
  ]),
  ("Param", .param, [
    ([N "Type", T .id], "do pure (← toType s0, ← lexeme s1)")
  ]),

  -- Tipos
  ("Type", .type, [
    ([N "BaseType", N "Dims"], "do wrapDims (← toBaseType s0) s1")
  ]),
  ("Dims", .dims, [
    ([T .lbracket, T .rbracket, N "Dims"], "wrapDims (.array base) s2"),
    ([],                                   "pure base")
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
    ([N "Block"],                  "toBlock s0"),
    ([N "IfStmt"],                 "toStmt s0"),
    ([N "WhileStmt"],              "toStmt s0"),
    ([N "ReturnStmt"],             "toStmt s0"),
    ([N "DeclStmt"],               "toStmt s0"),
    ([T .id, N "IdStmt", T .semi], "do toIdStmt (← lexeme s0) s1")
  ]),
  ("IdStmt", .idStmt, [
    ([T .lparen, N "Args", T .rparen], "do pure (.call idName (← toArgs s1))"),
    ([N "Indices", T .assign, N "Expr"], "do pure (.assign (← foldIndex (.var idName ()) s0) (← toExpr s2))")
  ]),
  ("Indices", .indexTail, [
    ([T .lbracket, N "Expr", T .rbracket, N "Indices"], "do foldIndex (.index acc (← toExpr s1) ()) s3"),
    ([],                                                "pure acc")
  ]),
  ("Block", .block, [
    ([T .lbrace, N "StmtList", T .rbrace], "do pure (.block (← toStmtList s1))")
  ]),
  ("StmtList", .stmtList, [
    ([N "Stmt", N "StmtList"], "do pure ((← toStmt s0) :: (← toStmtList s1))"),
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
    ([N "Expr", N "ArgsTail"], "do pure ((← toExpr s0) :: (← toArgs s1))"),
    ([],                       "pure []")
  ]),
  ("ArgsTail", .args, [
    ([T .comma, N "Expr", N "ArgsTail"], "do pure ((← toExpr s1) :: (← toArgs s2))"),
    ([],                                 "pure []")
  ]),

  -- Expressões, da precedência mais fraca para a mais forte
  ("Expr", .expr, [
    ([N "Or"], "toExpr s0")
  ])
]
++ binTokLevel "Or"  "OrTail"  .kwOr  ".or"  "And"
++ binTokLevel "And" "AndTail" .kwAnd ".and" "Not"
++ [
  ("Not", .expr, [
    ([T .not, N "Not"], "do pure (.not (← toExpr s1) ())"),
    ([N "Rel"],         "toExpr s0")
  ])
]
++ binNtLevel "Rel" "RelTail" "RelOp" "Add"
++ binNtLevel "Add" "AddTail" "AddOp" "Mul"
++ binNtLevel "Mul" "MulTail" "MulOp" "Unary"
++ [
  ("Unary", .expr, [
    ([T .minus, N "Unary"], "do pure (.neg (← toExpr s1) ())"),
    ([N "Postfix"],         "toExpr s0")
  ]),
  ("Postfix", .expr, [
    ([N "Atom", N "PostTail"], "do foldIndex (← toExpr s0) s1")
  ]),
  ("PostTail", .indexTail, [
    ([T .lbracket, N "Expr", T .rbracket, N "PostTail"], "do foldIndex (.index acc (← toExpr s1) ()) s3"),
    ([],                                                 "pure acc")
  ]),
  ("Atom", .expr, [
    ([T .numInt],                     "do pure (.lit (.int (← parseInt (← lexeme s0))) ())"),
    ([T .numFloat],                   "do pure (.lit (.float (← parseFloat (← lexeme s0))) ())"),
    ([T .stringLit],                  "do pure (.lit (.str (unquote (← lexeme s0))) ())"),
    ([T .kwTrue],                     "pure (.lit (.bool true) ())"),
    ([T .kwFalse],                    "pure (.lit (.bool false) ())"),
    ([T .id, N "AtomRest"],           "do toAtomRest (← lexeme s0) s1"),
    ([T .lbracket, N "Args", T .rbracket], "do pure (.array (← toArgs s1) ())"),
    ([T .lparen, N "Expr", T .rparen],     "toExpr s1")
  ]),
  ("AtomRest", .atomRest, [
    ([T .lparen, N "Args", T .rparen], "do pure (.call idName (← toArgs s1) ())"),
    ([],                               "pure (.var idName ())")
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
