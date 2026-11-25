-- ─────────────────────────────────────────────
-- DFA.lean
-- ─────────────────────────────────────────────

import Automata.Common
import Automata.NFA

-- ══════════════════════════════════════════════
-- ESTRUTURA DFA
-- ══════════════════════════════════════════════

structure DFA where
  mBase             : NFA
  deterministicT    : dfaUniqueTargetState mBase.q mBase.alphabet mBase.t ∧
                      dfaTotal mBase.q mBase.alphabet mBase.t
  allElementHasANeg : allElementsExistsN mBase.alphabet

-- ══════════════════════════════════════════════
-- CONSTRUTOR AUXILIAR
-- ══════════════════════════════════════════════

def createDFA
    (mBase             : NFA)
    (deterministicT    : dfaUniqueTargetState mBase.q mBase.alphabet mBase.t ∧
                         dfaTotal mBase.q mBase.alphabet mBase.t)
    (allElementHasANeg : allElementsExistsN mBase.alphabet)
    : DFA :=
  { mBase, deterministicT, allElementHasANeg }

-- ══════════════════════════════════════════════
-- CODIFICAÇÃO DE SÍMBOLO E DELTA
-- ══════════════════════════════════════════════

def encodeSymbolDFA (m : DFA) (portInput : Symbol) (sig : Bool) : Symbol :=
  encodeSymbolNFA m.mBase portInput sig

def deltaDFA (t : List Transition) (q : State) (sym : Symbol) : State :=
  match t with
  | [] => q
  | ((q0, s), qf) :: ts =>
      if q0 == q && s == sym then qf else deltaDFA ts q sym
