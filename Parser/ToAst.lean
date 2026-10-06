import Parser.Ast
import Parser.Engine

-- ══════════════════════════════════════════════
-- 1. DA ÁRVORE DE DERIVAÇÃO PARA A AST
-- ══════════════════════════════════════════════
-- Cada função olha o nome do não-terminal e a alternativa usada (`alt`, na ordem de
-- `Parser/Grammar.lean`), converte os filhos e monta o nó da AST.
-- Uma árvore fora do formato não deveria acontecer (seria bug no motor), então as
-- funções devolvem `Except String` em vez de travar.

private def malformada (t : ParseTree) : Except String α :=
  match t with
  | .node nt alt _ => throw s!"árvore malformada em {nt}.{alt}"
  | .leaf tok      => throw s!"árvore malformada no token '{tok.lexeme}'"

private def lexeme : ParseTree → Except String String
  | .leaf tok => pure tok.lexeme
  | t => malformada t

/-- `"3.14"` → `3.14`. O scanner só produz `dígitos.dígitos`. -/
private def parseFloat (s : String) : Except String Float :=
  match s.splitOn "." with
  | [ip, fp] =>
    match ip.toNat?, fp.toNat? with
    | some i, some f => pure (Float.ofScientific (i * 10 ^ fp.length + f) true fp.length)
    | _, _ => throw s!"número real inválido '{s}'"
  | _ => throw s!"número real inválido '{s}'"

/-- Tira as aspas de um literal de texto, se vierem no lexema. -/
private def unquote (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then String.ofList (s.toList.drop 1).dropLast else s

-- ── Tipos ──────────────────────────────────────

private def toBaseType : ParseTree → Except String MType
  | .node "BaseType" 0 _ => pure .int
  | .node "BaseType" 1 _ => pure .float
  | .node "BaseType" 2 _ => pure .bool
  | .node "BaseType" 3 _ => pure .str
  | .node "BaseType" 4 _ => pure .void
  | t => malformada t

/-- `Dims` conta os `[]`: cada um embrulha o tipo em `array`. -/
private def wrapDims (base : MType) : ParseTree → Except String MType
  | .node "Dims" 0 [_, _, rest] => wrapDims (.array base) rest
  | .node "Dims" 1 [] => pure base
  | t => malformada t

def toType : ParseTree → Except String MType
  | .node "Type" 0 [base, dims] => do wrapDims (← toBaseType base) dims
  | t => malformada t

/-- Operador binário a partir do token (direto, como `and`/`or`, ou dentro de `RelOp`/`AddOp`/`MulOp`). -/
private def toBinOp : ParseTree → Except String BinOp
  | .node _ _ [op] => toBinOp op
  | t@(.leaf tok) =>
    match tok.kind with
    | .plus => pure .add | .minus => pure .sub | .times => pure .mul | .div => pure .div
    | .eq => pure .eq | .neq => pure .ne | .lt => pure .lt | .le => pure .le
    | .gt => pure .gt | .ge => pure .ge | .kwAnd => pure .and | .kwOr => pure .or
    | _ => malformada t
  | t => malformada t

-- ── Expressões ─────────────────────────────────

mutual

def toExpr : ParseTree → Except String (Expr Unit)
  | .node "Expr" 0 [e] => toExpr e
  -- níveis binários: primeiro operando, depois a cauda dobrada à esquerda
  | .node "Or"  0 [a, tail] => do foldTail (← toExpr a) tail
  | .node "And" 0 [a, tail] => do foldTail (← toExpr a) tail
  | .node "Rel" 0 [a, tail] => do foldTail (← toExpr a) tail
  | .node "Add" 0 [a, tail] => do foldTail (← toExpr a) tail
  | .node "Mul" 0 [a, tail] => do foldTail (← toExpr a) tail
  -- unários
  | .node "Not"   0 [_, e] => do pure (.not (← toExpr e) ())
  | .node "Not"   1 [e]    => toExpr e
  | .node "Unary" 0 [_, e] => do pure (.neg (← toExpr e) ())
  | .node "Unary" 1 [e]    => toExpr e
  | .node "Postfix" 0 [a, tail] => do foldIndex (← toExpr a) tail
  -- átomos
  | .node "Atom" 0 [n] => do
      let s ← lexeme n
      match s.toNat? with
      | some v => pure (.lit (.int v) ())
      | none => throw s!"número inteiro inválido '{s}'"
  | .node "Atom" 1 [n] => do pure (.lit (.float (← parseFloat (← lexeme n))) ())
  | .node "Atom" 2 [s] => do pure (.lit (.str (unquote (← lexeme s))) ())
  | .node "Atom" 3 _   => pure (.lit (.bool true) ())
  | .node "Atom" 4 _   => pure (.lit (.bool false) ())
  | .node "Atom" 5 [x, .node "AtomRest" 0 [_, args, _]] => do
      pure (.call (← lexeme x) (← toArgs args) ())
  | .node "Atom" 5 [x, .node "AtomRest" 1 []] => do pure (.var (← lexeme x) ())
  | .node "Atom" 6 [_, args, _] => do pure (.array (← toArgs args) ())
  | .node "Atom" 7 [_, e, _]    => toExpr e     -- parênteses somem
  | t => malformada t

/-- Caudas `OrTail`, `AndTail`, `RelTail`, `AddTail`, `MulTail`: pendem para a direita na
    árvore; o acumulador as junta à esquerda. `a - b - c` vira `(a - b) - c`. -/
def foldTail (acc : Expr Unit) : ParseTree → Except String (Expr Unit)
  | .node _ 0 [op, rhs, rest] => do foldTail (.bin (← toBinOp op) acc (← toExpr rhs) ()) rest
  | .node _ 1 [] => pure acc
  | t => malformada t

/-- `PostTail` e `Indices` (mesmo formato): `a[i][j]` vira `index (index a i) j`. -/
def foldIndex (acc : Expr Unit) : ParseTree → Except String (Expr Unit)
  | .node _ 0 [_, i, _, rest] => do foldIndex (.index acc (← toExpr i) ()) rest
  | .node _ 1 [] => pure acc
  | t => malformada t

/-- `Args` e `ArgsTail`: viram uma lista, na ordem em que aparecem. -/
def toArgs : ParseTree → Except String (List (Expr Unit))
  | .node "Args"     0 [e, rest]    => do pure ((← toExpr e) :: (← toArgs rest))
  | .node "ArgsTail" 0 [_, e, rest] => do pure ((← toExpr e) :: (← toArgs rest))
  | .node _ 1 [] => pure []
  | t => malformada t

end

-- ── Comandos ───────────────────────────────────

mutual

def toStmt : ParseTree → Except String (Stmt Unit)
  | .node "Stmt" 0 [b] => toBlock b
  | .node "Stmt" 1 [.node "IfStmt" 0 [_, c, b, els]] => do
      let e ← match els with
        | .node "ElseOpt" 0 [_, eb] => some <$> toBlock eb
        | .node "ElseOpt" 1 [] => pure none
        | t => malformada t
      pure (.ifElse (← toExpr c) (← toBlock b) e)
  | .node "Stmt" 2 [.node "WhileStmt" 0 [_, c, b]] => do pure (.while (← toExpr c) (← toBlock b))
  | .node "Stmt" 3 [.node "ReturnStmt" 0 [_, .node "OptExpr" 0 [e], _]] => do
      pure (.ret (some (← toExpr e)))
  | .node "Stmt" 3 [.node "ReturnStmt" 0 [_, .node "OptExpr" 1 [], _]] => pure (.ret none)
  | .node "Stmt" 4 [.node "DeclStmt" 0 [ty, x, _, e, _]] => do
      pure (.decl (← toType ty) (← lexeme x) (← toExpr e))
  -- comando que começa com identificador: chamada ou atribuição, conforme `IdStmt`
  | .node "Stmt" 5 [x, .node "IdStmt" 0 [_, args, _], _] => do
      pure (.call (← lexeme x) (← toArgs args))
  | .node "Stmt" 5 [x, .node "IdStmt" 1 [idx, _, e], _] => do
      pure (.assign (← foldIndex (.var (← lexeme x) ()) idx) (← toExpr e))
  | t => malformada t

def toBlock : ParseTree → Except String (Stmt Unit)
  | .node "Block" 0 [_, ss, _] => do pure (.block (← toStmtList ss))
  | t => malformada t

def toStmtList : ParseTree → Except String (List (Stmt Unit))
  | .node "StmtList" 0 [s, rest] => do pure ((← toStmt s) :: (← toStmtList rest))
  | .node "StmtList" 1 [] => pure []
  | t => malformada t

end

-- ── Funções e programa ─────────────────────────

private def toParam : ParseTree → Except String (MType × String)
  | .node "Param" 0 [ty, x] => do pure (← toType ty, ← lexeme x)
  | t => malformada t

/-- `Params` e `ParamsTail`. -/
private def toParams : ParseTree → Except String (List (MType × String))
  | .node "Params"     0 [p, rest]    => do pure ((← toParam p) :: (← toParams rest))
  | .node "ParamsTail" 0 [_, p, rest] => do pure ((← toParam p) :: (← toParams rest))
  | .node _ 1 [] => pure []
  | t => malformada t

def toFun : ParseTree → Except String (FunDecl Unit)
  | .node "FunDecl" 0 [ty, x, _, ps, _, body] => do
      pure { name := ← lexeme x, params := ← toParams ps, ret := ← toType ty, body := ← toStmt body }
  | t => malformada t

private def toFunList : ParseTree → Except String (Program Unit)
  | .node "FunList" 0 [f, rest] => do pure ((← toFun f) :: (← toFunList rest))
  | .node "FunList" 1 [] => pure []
  | t => malformada t

def toProgram : ParseTree → Except String (Program Unit)
  | .node "Program" 0 [fs, _] => toFunList fs
  | t => malformada t

-- ══════════════════════════════════════════════
-- 2. DE PONTA A PONTA: TEXTO → AST
-- ══════════════════════════════════════════════

/-- Scanner, motor LL(1) e conversão. Erro de sintaxe sai como `linha:coluna: ...`. -/
def parseProgram (src : String) : Except String (Program Unit) :=
  match parseSource src with
  | .error e => throw e.message
  | .ok tree => toProgram tree
