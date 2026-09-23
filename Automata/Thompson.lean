import Automata.Common
import Automata.NFA

-- ══════════════════════════════════════════════
-- 1. ÁRVORE DE SINTAXE DA EXPRESSÃO REGULAR (AST)
-- ══════════════════════════════════════════════

inductive Regex where
  | epsilon : Regex
  | literal (s : Symbol) : Regex
  | concat  (r1 r2 : Regex) : Regex
  | union   (r1 r2 : Regex) : Regex
  | star    (r : Regex) : Regex
  deriving Repr


-- ══════════════════════════════════════════════
-- 2. ESTRUTURA INTERMÉDIA DO NFA
-- ══════════════════════════════════════════════
-- Como o tipo `NFA` em `NFA.lean` exige provas rigorosas (ex: `validTransitions`),
-- usamos um `RawNFA` durante o processo de construção algorítmica.
structure RawNFA where
  start       : State
  accept      : State
  transitions : List Transition
  deriving Repr

-- Mônada de Estado para gerar IDs numéricos únicos para os estados
abbrev BuilderM := StateM State

def freshState : BuilderM State := do
  let id ← get
  set (id + 1)
  return id


-- ══════════════════════════════════════════════
-- 3. ALGORITMO DE THOMPSON
-- ══════════════════════════════════════════════

def buildThompson (r : Regex) : BuilderM RawNFA := do
  match r with
  | Regex.epsilon =>
      let s ← freshState
      let f ← freshState
      return { start := s, accept := f, transitions := [((s, "ε"), f)] }

  | Regex.literal c =>
      let s ← freshState
      let f ← freshState
      return { start := s, accept := f, transitions := [((s, c), f)] }

  | Regex.concat r1 r2 =>
      let n1 ← buildThompson r1
      let n2 ← buildThompson r2
      -- Transição "ε" do final do primeiro para o início do segundo
      let t := n1.transitions ++ n2.transitions ++ [((n1.accept, "ε"), n2.start)]
      return { start := n1.start, accept := n2.accept, transitions := t }

  | Regex.union r1 r2 =>
      let n1 ← buildThompson r1
      let n2 ← buildThompson r2
      let s ← freshState
      let f ← freshState
      -- Bifurcação inicial e convergência final via "ε"
      let t := n1.transitions ++ n2.transitions ++
               [((s, "ε"), n1.start), ((s, "ε"), n2.start),
                ((n1.accept, "ε"), f), ((n2.accept, "ε"), f)]
      return { start := s, accept := f, transitions := t }

  | Regex.star r1 =>
      let n1 ← buildThompson r1
      let s ← freshState
      let f ← freshState
      -- Loops e bypass do Fecho de Kleene via "ε"
      let t := n1.transitions ++
               [((s, "ε"), n1.start), ((s, "ε"), f),
                ((n1.accept, "ε"), n1.start), ((n1.accept, "ε"), f)]
      return { start := s, accept := f, transitions := t }

-- ══════════════════════════════════════════════
-- 4. FUNÇÃO DE ENTRADA
-- ══════════════════════════════════════════════

/-- Converte uma Regex num NFA bruto, iniciando a contagem de estados no 0 -/
def regexToRawNFA (r : Regex) : RawNFA :=
  let (nfa, _) := (buildThompson r).run 0
  nfa
