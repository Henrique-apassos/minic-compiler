-- ══════════════════════════════════════════════
-- AST (ÁRVORE SINTÁTICA ABSTRATA) DO MINIC
-- ══════════════════════════════════════════════
-- Só o significado do programa: sem parênteses, sem `;`, sem caudas da gramática.
-- Modelo: `src/ir/ast.rs` do exemplo em Rust, sem ponteiros.
--
-- `Ty` é o tipo anotado em cada expressão. O parser usa `Unit` (nada ainda);
-- o verificador de tipos, no futuro, troca por `MType` sem reescrever a AST.

/-- Os tipos da linguagem. `int[][]` é `array (array int)`. -/
inductive MType where
  | int | float | bool | str | void
  | array (elem : MType)
  deriving Repr, BEq, Inhabited

inductive Lit where
  | int   (n : Int)
  | float (x : Float)
  | str   (s : String)
  | bool  (b : Bool)
  deriving Repr, BEq, Inhabited

inductive BinOp where
  | add | sub | mul | div
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, Inhabited

inductive Expr (Ty : Type) where
  | lit   (l : Lit) (ty : Ty)
  | var   (name : String) (ty : Ty)
  | neg   (e : Expr Ty) (ty : Ty)                       -- -e
  | not   (e : Expr Ty) (ty : Ty)                       -- !e
  | bin   (op : BinOp) (a b : Expr Ty) (ty : Ty)
  | call  (f : String) (args : List (Expr Ty)) (ty : Ty)
  | array (elems : List (Expr Ty)) (ty : Ty)            -- [1, 2, 3]
  | index (a i : Expr Ty) (ty : Ty)                     -- a[i]
  deriving Repr, BEq, Inhabited

inductive Stmt (Ty : Type) where
  | decl   (t : MType) (name : String) (init : Expr Ty)
  | assign (target value : Expr Ty)                     -- x = e;  a[i] = e;
  | block  (body : List (Stmt Ty))
  | call   (f : String) (args : List (Expr Ty))         -- f(x);
  | ifElse (cond : Expr Ty) (thenB : Stmt Ty) (elseB : Option (Stmt Ty))
  | while  (cond : Expr Ty) (body : Stmt Ty)
  | ret    (e : Option (Expr Ty))
  deriving Repr, BEq, Inhabited

structure FunDecl (Ty : Type) where
  name   : String
  params : List (MType × String)
  ret    : MType
  body   : Stmt Ty
  deriving Repr, BEq, Inhabited

abbrev Program (Ty : Type) := List (FunDecl Ty)

-- ══════════════════════════════════════════════
-- IMPRESSÃO LEGÍVEL (usada pelo Main)
-- ══════════════════════════════════════════════
-- Toda operação binária sai entre parênteses, para a associatividade ficar visível:
-- `a - b - c` imprime `((a - b) - c)`.

def MType.show : MType → String
  | .int => "int" | .float => "float" | .bool => "bool" | .str => "str" | .void => "void"
  | .array t => t.show ++ "[]"

def BinOp.show : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "and" | .or => "or"

def Lit.show : Lit → String
  | .int n => toString n | .float x => toString x | .str s => s.quote
  | .bool b => if b then "true" else "false"

def Expr.show {Ty : Type} : Expr Ty → String
  | .lit l _ => l.show
  | .var x _ => x
  | .neg e _ => "-" ++ e.show
  | .not e _ => "!" ++ e.show
  | .bin op a b _ => s!"({a.show} {op.show} {b.show})"
  | .call f args _ => f ++ "(" ++ ", ".intercalate (args.map Expr.show) ++ ")"
  | .array es _ => "[" ++ ", ".intercalate (es.map Expr.show) ++ "]"
  | .index a i _ => s!"{a.show}[{i.show}]"

def Stmt.show {Ty : Type} (ind : String) : Stmt Ty → String
  | .decl t x e => s!"{ind}{t.show} {x} = {e.show};"
  | .assign a v => s!"{ind}{a.show} = {v.show};"
  | .block ss => ind ++ "{\n" ++ String.join (ss.map (Stmt.show (ind ++ "  ") · ++ "\n")) ++ ind ++ "}"
  | .call f args => ind ++ f ++ "(" ++ ", ".intercalate (args.map Expr.show) ++ ");"
  | .ifElse c t e =>
      s!"{ind}if {c.show}\n" ++ t.show ind ++
      (match e with | some e => s!"\n{ind}else\n" ++ e.show ind | none => "")
  | .while c b => s!"{ind}while {c.show}\n" ++ b.show ind
  | .ret (some e) => s!"{ind}return {e.show};"
  | .ret none => s!"{ind}return;"

def FunDecl.show {Ty : Type} (f : FunDecl Ty) : String :=
  let ps := ", ".intercalate (f.params.map fun (t, x) => s!"{t.show} {x}")
  s!"{f.ret.show} {f.name}({ps})\n" ++ f.body.show ""

def Program.show {Ty : Type} (p : Program Ty) : String :=
  "\n\n".intercalate (p.map FunDecl.show)
