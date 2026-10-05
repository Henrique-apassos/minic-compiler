import Parser.Grammar
import Std.Data.HashMap

-- ══════════════════════════════════════════════
-- 1. CONJUNTOS DE TOKENS
-- ══════════════════════════════════════════════
-- `TokenKind` não deriva `Hashable`; os conjuntos são pequenos (≤ 40 tokens),
-- então uma lista sem repetição, na ordem de inserção, basta.

abbrev TokSet := List TokenKind

def TokSet.add (s : TokSet) (k : TokenKind) : TokSet :=
  if s.contains k then s else s ++ [k]

def TokSet.union (s r : TokSet) : TokSet :=
  r.foldl TokSet.add s

-- ══════════════════════════════════════════════
-- 2. RESULTADO DA ANÁLISE
-- ══════════════════════════════════════════════

structure Analysis where
  nullable : List String
  first    : Std.HashMap String TokSet
  follow   : Std.HashMap String TokSet

def Analysis.isNullable (a : Analysis) (n : String) : Bool := a.nullable.contains n
def Analysis.firstOf  (a : Analysis) (n : String) : TokSet := a.first.getD n []
def Analysis.followOf (a : Analysis) (n : String) : TokSet := a.follow.getD n []

/-- FIRST de uma sequência e se ela é nulável -/
def Analysis.firstOfSeq (a : Analysis) : List Sym → TokSet × Bool
  | [] => ([], true)
  | .t k :: _ => ([k], false)
  | .nt n :: rest =>
    if a.isNullable n then
      let (f, nul) := a.firstOfSeq rest
      (TokSet.union (a.firstOf n) f, nul)
    else (a.firstOf n, false)

/-- Quantidade total de informação acumulada (cresce monotonicamente). -/
private def Analysis.measure (a : Analysis) : Nat :=
  a.nullable.length + a.first.fold (fun acc _ s => acc + s.length) 0
    + a.follow.fold (fun acc _ s => acc + s.length) 0

-- ══════════════════════════════════════════════
-- 3. PONTO FIXO COM COMBUSTÍVEL
-- ══════════════════════════════════════════════
-- Repete `step` até a medida parar de crescer. Sem `partial`: o combustível
-- limita o número de rodadas (ver `analyze` para a justificativa do limite).

private def iterate (fuel : Nat) (step : Analysis → Analysis) (a : Analysis) : Analysis :=
  match fuel with
  | 0 => a
  | n + 1 =>
    let a' := step a
    if a'.measure == a.measure then a else iterate n step a'

private def addTo (m : Std.HashMap String TokSet) (n : String) (s : TokSet) :
    Std.HashMap String TokSet :=
  m.insert n (TokSet.union (m.getD n []) s)

/-- Uma passada de nullable + FIRST sobre todas as produções. -/
private def firstStep (g : Grammar) (a : Analysis) : Analysis :=
  g.prods.foldl (init := a) fun a p =>
    let (f, nul) := a.firstOfSeq p.rhs
    let nullable := if nul && !a.isNullable p.lhs then a.nullable ++ [p.lhs] else a.nullable
    { a with nullable, first := addTo a.first p.lhs f }

/-- Uma passada de FOLLOW: para `A := ... B β`, FIRST(β) ⊆ FOLLOW(B) e,
    se β é nulável, FOLLOW(A) ⊆ FOLLOW(B). -/
private def followStep (g : Grammar) (a : Analysis) : Analysis :=
  g.prods.foldl (init := a) fun a p =>
    let rec go (a : Analysis) : List Sym → Analysis
      | [] => a
      | .t _ :: rest => go a rest
      | .nt b :: rest =>
        let (f, nul) := a.firstOfSeq rest
        let f := if nul then TokSet.union f (a.followOf p.lhs) else f
        go { a with follow := addTo a.follow b f } rest
    go a p.rhs

-- ══════════════════════════════════════════════
-- 4. ANÁLISE COMPLETA
-- ══════════════════════════════════════════════
-- Combustível: cada rodada que muda algo acrescenta ≥ 1 elemento. Na fase 1 há
-- no máximo |N| nuláveis + |N|·|T| pares em FIRST = |N|·(|T|+1); na fase 2,
-- no máximo |N|·|T| pares em FOLLOW. Logo |N|·(|T|+1) + 1 rodadas (a última
-- só confirma que nada mudou) bastam para cada fase.

def analyze (g : Grammar) : Analysis :=
  let nts := g.nonterminals
  let fuel := nts.length * (g.terminals.length + 1) + 1
  let a0 : Analysis := { nullable := [], first := {}, follow := {} }
  let a1 := iterate fuel (firstStep g) a0
  let a1 := { a1 with follow := ({} : Std.HashMap String TokSet).insert g.start [TokenKind.eof] }
  iterate fuel (followStep g) a1
