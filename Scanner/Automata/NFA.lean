import Automata.Common

-- ══════════════════════════════════════════════
-- ESTRUTURA NFA
-- ══════════════════════════════════════════════

structure NFA where
  q                    : List State
  alphabet             : List Symbol
  t                    : List Transition
  q0                   : State
  f                    : List State
  qNonEmpty            : q ≠ []
  q0InQ                : q0 ∈ q
  noRepetitionQ        : q.Nodup
  noRepetitionAlphabet : alphabet.Nodup
  noRepetitionT        : t.Nodup
  noRepetitionF        : f.Nodup
  validTransitions     : eachTransitionIsValid t q alphabet
  acceptanceState      : eachAcceptanceStateIsValid f q

-- ══════════════════════════════════════════════
-- CODIFICAÇÃO DE SÍMBOLO
-- ══════════════════════════════════════════════

def encodeSymbolNFA (m : NFA) (portInput : Symbol) (sig : Bool) : Symbol :=
  match sig with
  | true  => if portInput ∈ m.alphabet then portInput else "X"
  | false => if portInput ∈ m.alphabet then "N_" ++ portInput else "X"

-- ══════════════════════════════════════════════
-- FUNÇÃO DE TRANSIÇÃO (delta)
-- ══════════════════════════════════════════════

def deltaNFA (t : List Transition) (q : State) (sym : Symbol) : List State :=
  match t with
  | [] => []
  | ((q0, "ε"), qf) :: ts =>
      if q0 == q then qf :: deltaNFA ts q sym else deltaNFA ts q sym
  | ((q0, s), qf) :: ts =>
      if q0 == q && s == sym then qf :: deltaNFA ts q sym else deltaNFA ts q sym

-- ══════════════════════════════════════════════
-- TESTES
-- ══════════════════════════════════════════════

#eval deltaNFA [((0, "a"), 1), ((1, "b"), 2)] 0 "a"  -- [1]
#eval deltaNFA [((0, "ε"), 1), ((1, "b"), 2)] 0 "x"  -- [1]
