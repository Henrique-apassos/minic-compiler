-- ════════════════════════════════════════════════════════════════════
-- ARQUIVO GERADO AUTOMATICAMENTE POR `lake exe gen-parser`
-- Conversão ParseTree → AST gerada a partir de `Parser/Grammar.lean`.
-- NÃO EDITE MANUALMENTE.
-- ════════════════════════════════════════════════════════════════════
import Parser.Ast
import Parser.Engine

private def FormatError (t : ParseTree) : Except String α :=
  match t with
  | .node nt alt _ => throw s!"árvore mal formada em {nt}.{alt}"
  | .leaf tok => throw s!"árvore mal formada no token '{tok.lexeme}'"

private def lexeme (t : ParseTree) : Except String String :=
  match t with
  | .leaf tok => pure tok.lexeme
  | _ => FormatError t

private def parseInt (s : String) : Except String Int :=
  match s.toNat? with
  | some v => pure v
  | none => throw s!"número inteiro inválido '{s}'"

private def parseFloat (s : String) : Except String Float :=
  match s.splitOn "." with
  | [int, float] =>
    match int.toNat?, float.toNat? with
    | some i, some f => pure (Float.ofScientific (i * 10 ^ float.length + f) true float.length)
    | _, _ => throw s!"número real inválido '{s}'"
  | _ => throw s!"número real inválido '{s}'"

private def unquote (s : String) : String :=
  if s.length >= 2 && s.startsWith "\"" && s.endsWith "\"" then
    String.ofList (s.toList.drop 1).dropLast
  else s

-- ── Tipos ──────────────────────────────────────

private def toBaseType : ParseTree → Except String MType
  | .node "BaseType" 0 [_] => pure .int
  | .node "BaseType" 1 [_] => pure .float
  | .node "BaseType" 2 [_] => pure .bool
  | .node "BaseType" 3 [_] => pure .str
  | .node "BaseType" 4 [_] => pure .void
  | t => FormatError t

private def wrapDims (base : MType) : ParseTree → Except String MType
  | .node "Dims" 0 [_, _, s2] => wrapDims (.array base) s2
  | .node "Dims" 1 [] => pure base
  | t => FormatError t

def toType : ParseTree → Except String MType
  | .node "Type" 0 [s0, s1] => do wrapDims (← toBaseType s0) s1
  | t => FormatError t

-- ── Operadores Binários ────────────────────────

private def toBinOp : ParseTree → Except String BinOp
  | .node "RelOp" 0 [_] => pure .eq
  | .node "RelOp" 1 [_] => pure .ne
  | .node "RelOp" 2 [_] => pure .lt
  | .node "RelOp" 3 [_] => pure .le
  | .node "RelOp" 4 [_] => pure .gt
  | .node "RelOp" 5 [_] => pure .ge
  | .node "AddOp" 0 [_] => pure .add
  | .node "AddOp" 1 [_] => pure .sub
  | .node "MulOp" 0 [_] => pure .mul
  | .node "MulOp" 1 [_] => pure .div
  | t => FormatError t

-- ── Expressões ─────────────────────────────────

mutual

def toExpr : ParseTree → Except String (Expr Unit)
  | .node "Expr" 0 [s0] => toExpr s0
  | .node "Or" 0 [s0, s1] => do foldTail (← toExpr s0) s1
  | .node "And" 0 [s0, s1] => do foldTail (← toExpr s0) s1
  | .node "Not" 0 [_, s1] => do pure (.not (← toExpr s1) ())
  | .node "Not" 1 [s0] => toExpr s0
  | .node "Rel" 0 [s0, s1] => do foldTail (← toExpr s0) s1
  | .node "Add" 0 [s0, s1] => do foldTail (← toExpr s0) s1
  | .node "Mul" 0 [s0, s1] => do foldTail (← toExpr s0) s1
  | .node "Unary" 0 [_, s1] => do pure (.neg (← toExpr s1) ())
  | .node "Unary" 1 [s0] => toExpr s0
  | .node "Postfix" 0 [s0, s1] => do foldIndex (← toExpr s0) s1
  | .node "Atom" 0 [s0] => do pure (.lit (.int (← parseInt (← lexeme s0))) ())
  | .node "Atom" 1 [s0] => do pure (.lit (.float (← parseFloat (← lexeme s0))) ())
  | .node "Atom" 2 [s0] => do pure (.lit (.str (unquote (← lexeme s0))) ())
  | .node "Atom" 3 [_] => pure (.lit (.bool true) ())
  | .node "Atom" 4 [_] => pure (.lit (.bool false) ())
  | .node "Atom" 5 [s0, s1] => do toAtomRest (← lexeme s0) s1
  | .node "Atom" 6 [_, s1, _] => do pure (.array (← toArgs s1) ())
  | .node "Atom" 7 [_, s1, _] => toExpr s1
  | t => FormatError t

def toAtomRest (idName : String) : ParseTree → Except String (Expr Unit)
  | .node "AtomRest" 0 [_, s1, _] => do pure (.call idName (← toArgs s1) ())
  | .node "AtomRest" 1 [] => pure (.var idName ())
  | t => FormatError t

def foldTail (acc : Expr Unit) : ParseTree → Except String (Expr Unit)
  | .node "OrTail" 0 [_, s1, s2] => do foldTail (.bin .or acc (← toExpr s1) ()) s2
  | .node "OrTail" 1 [] => pure acc
  | .node "AndTail" 0 [_, s1, s2] => do foldTail (.bin .and acc (← toExpr s1) ()) s2
  | .node "AndTail" 1 [] => pure acc
  | .node "RelTail" 0 [s0, s1, s2] => do foldTail (.bin (← toBinOp s0) acc (← toExpr s1) ()) s2
  | .node "RelTail" 1 [] => pure acc
  | .node "AddTail" 0 [s0, s1, s2] => do foldTail (.bin (← toBinOp s0) acc (← toExpr s1) ()) s2
  | .node "AddTail" 1 [] => pure acc
  | .node "MulTail" 0 [s0, s1, s2] => do foldTail (.bin (← toBinOp s0) acc (← toExpr s1) ()) s2
  | .node "MulTail" 1 [] => pure acc
  | t => FormatError t

def foldIndex (acc : Expr Unit) : ParseTree → Except String (Expr Unit)
  | .node "Indices" 0 [_, s1, _, s3] => do foldIndex (.index acc (← toExpr s1) ()) s3
  | .node "Indices" 1 [] => pure acc
  | .node "PostTail" 0 [_, s1, _, s3] => do foldIndex (.index acc (← toExpr s1) ()) s3
  | .node "PostTail" 1 [] => pure acc
  | t => FormatError t

def toArgs : ParseTree → Except String (List (Expr Unit))
  | .node "Args" 0 [s0, s1] => do pure ((← toExpr s0) :: (← toArgs s1))
  | .node "Args" 1 [] => pure []
  | .node "ArgsTail" 0 [_, s1, s2] => do pure ((← toExpr s1) :: (← toArgs s2))
  | .node "ArgsTail" 1 [] => pure []
  | t => FormatError t

end

-- ── Comandos ───────────────────────────────────

private def toOptExpr : ParseTree → Except String (Option (Expr Unit))
  | .node "OptExpr" 0 [s0] => some <$> toExpr s0
  | .node "OptExpr" 1 [] => pure none
  | t => FormatError t

private def toIdStmt (idName : String) : ParseTree → Except String (Stmt Unit)
  | .node "IdStmt" 0 [_, s1, _] => do pure (.call idName (← toArgs s1))
  | .node "IdStmt" 1 [s0, _, s2] => do pure (.assign (← foldIndex (.var idName ()) s0) (← toExpr s2))
  | t => FormatError t

mutual

def toStmt : ParseTree → Except String (Stmt Unit)
  | .node "Stmt" 0 [s0] => toBlock s0
  | .node "Stmt" 1 [s0] => toStmt s0
  | .node "Stmt" 2 [s0] => toStmt s0
  | .node "Stmt" 3 [s0] => toStmt s0
  | .node "Stmt" 4 [s0] => toStmt s0
  | .node "Stmt" 5 [s0, s1, _] => do toIdStmt (← lexeme s0) s1
  | .node "IfStmt" 0 [_, s1, s2, s3] => do pure (.ifElse (← toExpr s1) (← toBlock s2) (← toElseOpt s3))
  | .node "WhileStmt" 0 [_, s1, s2] => do pure (.while (← toExpr s1) (← toBlock s2))
  | .node "ReturnStmt" 0 [_, s1, _] => do pure (.ret (← toOptExpr s1))
  | .node "DeclStmt" 0 [s0, s1, _, s3, _] => do pure (.decl (← toType s0) (← lexeme s1) (← toExpr s3))
  | t => FormatError t

def toElseOpt : ParseTree → Except String (Option (Stmt Unit))
  | .node "ElseOpt" 0 [_, s1] => some <$> toBlock s1
  | .node "ElseOpt" 1 [] => pure none
  | t => FormatError t

def toBlock : ParseTree → Except String (Stmt Unit)
  | .node "Block" 0 [_, s1, _] => do pure (.block (← toStmtList s1))
  | t => FormatError t

def toStmtList : ParseTree → Except String (List (Stmt Unit))
  | .node "StmtList" 0 [s0, s1] => do pure ((← toStmt s0) :: (← toStmtList s1))
  | .node "StmtList" 1 [] => pure []
  | t => FormatError t

end

-- ── Funções e Programa ─────────────────────────

private def toParam : ParseTree → Except String (MType × String)
  | .node "Param" 0 [s0, s1] => do pure (← toType s0, ← lexeme s1)
  | t => FormatError t

private def toParams : ParseTree → Except String (List (MType × String))
  | .node "Params" 0 [s0, s1] => do pure ((← toParam s0) :: (← toParams s1))
  | .node "Params" 1 [] => pure []
  | .node "ParamsTail" 0 [_, s1, s2] => do pure ((← toParam s1) :: (← toParams s2))
  | .node "ParamsTail" 1 [] => pure []
  | t => FormatError t

def toFun : ParseTree → Except String (FunDecl Unit)
  | .node "FunDecl" 0 [s0, s1, _, s3, _, s5] => do pure { name := ← lexeme s1, params := ← toParams s3, ret := ← toType s0, body := ← toStmt s5 }
  | t => FormatError t

private def toFunList : ParseTree → Except String (Program Unit)
  | .node "FunList" 0 [s0, s1] => do pure ((← toFun s0) :: (← toFunList s1))
  | .node "FunList" 1 [] => pure []
  | t => FormatError t

def toProgram : ParseTree → Except String (Program Unit)
  | .node "Program" 0 [s0, _] => toFunList s0
  | t => FormatError t

/-- De ponta a ponta: Scanner, motor LR(1) e conversão para AST. -/
def parseProgram (src : String) : Except String (Program Unit) :=
  match parseSource src with
  | .error e => throw e.message
  | .ok tree => toProgram tree
