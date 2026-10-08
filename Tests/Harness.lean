import Parser

-- ══════════════════════════════════════════════
-- HARNESS DE TESTES
-- ══════════════════════════════════════════════
-- Portado de `MiniC/tests/parser.rs` e `MiniC/tests/program.rs` (o exemplo em Rust).
-- O Rust testa sub-parsers soltos (`expression`, `statement`, `fun_decl`); aqui só existe
-- `parseProgram` (a gramática começa em `Program`), então expressão e comando são
-- embrulhados numa função `void t() { ... }` e extraídos da AST.

structure Test where
  name    : String
  ok      : Bool
  detail  : String := ""
  /-- Lacuna conhecida do compilador. Falhar é o esperado; passar vira erro (tirar a marca). -/
  pending : Option String := none

def Test.pend (t : Test) (why : String) : Test := { t with pending := some why }

/-- Um teste do Rust com várias asserções vira um só: passa se todas passarem. -/
def allOf (name : String) (ts : List Test) : Test :=
  let bad := ts.filter (!·.ok)
  { name, ok := bad.isEmpty
    detail := "; ".intercalate (bad.map fun t => s!"[{t.name}] {t.detail}") }

-- ── Construtores curtos de AST (Ty = Unit) ─────

abbrev E := Expr Unit
abbrev S := Stmt Unit

def eInt (n : Int) : E := .lit (.int n) ()
def eFloat (x : Float) : E := .lit (.float x) ()
def eStr (s : String) : E := .lit (.str s) ()
def eBool (b : Bool) : E := .lit (.bool b) ()
def eVar (x : String) : E := .var x ()
def eNeg (e : E) : E := .neg e ()
def eNot (e : E) : E := .not e ()
def eBin (op : BinOp) (a b : E) : E := .bin op a b ()
def eCall (f : String) (args : List E) : E := .call f args ()
def eArr (es : List E) : E := .array es ()
def eIdx (a i : E) : E := .index a i ()

-- ── Embrulhos: texto → pedaço da AST ───────────

def parseFun (src : String) : Except String (FunDecl Unit) := do
  match ← parseProgram src with
  | [f] => pure f
  | fs => throw s!"esperava 1 função, veio {fs.length}"

def parseBody (src : String) : Except String (List S) := do
  let f ← parseFun ("void t() { " ++ src ++ " }")
  match f.body with
  | .block ss => pure ss
  | _ => throw "corpo da função de teste não é bloco"

def parseStmt (src : String) : Except String S := do
  match ← parseBody src with
  | [s] => pure s
  | ss => throw s!"esperava 1 comando, veio {ss.length}"

def parseExpr (src : String) : Except String E := do
  match ← parseStmt ("int x = " ++ src ++ ";") with
  | .decl _ _ e => pure e
  | _ => throw "comando de teste não é declaração"

-- ── Asserções ──────────────────────────────────

def expectEq {α : Type} [BEq α] (name : String) (got : Except String α) (want : α)
    (sh : α → String) : Test :=
  match got with
  | .ok g => { name, ok := g == want, detail := s!"obtido {sh g}, esperado {sh want}" }
  | .error e => { name, ok := false, detail := s!"erro de sintaxe: {e}" }

def expectErr {α : Type} (name : String) (got : Except String α) (sh : α → String) : Test :=
  match got with
  | .ok g => { name, ok := false, detail := s!"deveria recusar, mas aceitou: {sh g}" }
  | .error _ => { name, ok := true }

/-- O nome do teste é o próprio texto-fonte. -/
def expectExpr (src : String) (want : E) : Test :=
  expectEq src (parseExpr src) want fun e => e.show

def rejectExpr (src : String) : Test :=
  expectErr src (parseExpr src) fun e => e.show

def expectStmt (src : String) (want : S) : Test :=
  expectEq src (parseStmt src) want fun s => s.show ""

def rejectStmt (src : String) : Test :=
  expectErr src (parseStmt src) fun s => s.show ""

def expectFun (src : String) (want : FunDecl Unit) : Test :=
  expectEq src (parseFun src) want fun f => f.show

def rejectFun (src : String) : Test :=
  expectErr src (parseFun src) fun f => f.show

-- ── Execução ───────────────────────────────────

/-- Imprime só o que falhou ou está pendente, e o total. Sai com 1 se algo falhou. -/
def runAll (groups : List (String × List Test)) : IO UInt32 := do
  let mut pass := 0
  let mut fail := 0
  let mut pend := 0
  for (g, ts) in groups do
    IO.println s!"── {g} ({ts.length})"
    for t in ts do
      match t.pending, t.ok with
      | none, true => pass := pass + 1
      | none, false =>
        fail := fail + 1
        IO.println s!"  FALHOU   {t.name}\n           {t.detail}"
      | some why, false =>
        pend := pend + 1
        IO.println s!"  PENDENTE {t.name} — {why}"
      | some why, true =>
        fail := fail + 1
        IO.println s!"  FALHOU   {t.name}: passou, mas estava pendente ({why}); remova a marca"
  IO.println s!"{pass + fail + pend} testes: {pass} passaram, {fail} falharam, {pend} pendentes"
  return if fail == 0 then 0 else 1
