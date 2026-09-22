-- ─────────────────────────────────────────────
-- Simulation.lean
-- ─────────────────────────────────────────────

import Automata.Common
import Automata.NFA
import Automata.DFA

-- ══════════════════════════════════════════════
-- RECORDS DE SIMULAÇÃO
-- ══════════════════════════════════════════════

structure SimulationDFA where
  wfCollectionDFA  : List Waveform
  mDFA             : DFA
  waveformNotEmpty : wfCollectionDFA.length > 0
  sameLength       : checkWaveformSameLength wfCollectionDFA (headWF wfCollectionDFA)

structure SimulationNFA where
  wfCollectionNFA  : List Waveform
  mNFA             : NFA
  waveformNotEmpty : wfCollectionNFA.length > 0
  sameLength       : checkWaveformSameLength wfCollectionNFA (headWF wfCollectionNFA)

-- ══════════════════════════════════════════════
-- CONSTRUTORES AUXILIARES
-- ══════════════════════════════════════════════

def makeSimulationDFA
    (wf : List Waveform) (m : DFA)
    (hEmpty : wf.length > 0)
    (hLen   : checkWaveformSameLength wf (headWF wf))
    : SimulationDFA :=
  { wfCollectionDFA := wf, mDFA := m, waveformNotEmpty := hEmpty, sameLength := hLen }

def makeSimulationNFA
    (wf : List Waveform) (m : NFA)
    (hEmpty : wf.length > 0)
    (hLen   : checkWaveformSameLength wf (headWF wf))
    : SimulationNFA :=
  { wfCollectionNFA := wf, mNFA := m, waveformNotEmpty := hEmpty, sameLength := hLen }

-- ══════════════════════════════════════════════
-- BUSCA DO PRÓXIMO ESTADO
-- ══════════════════════════════════════════════

def findNextStateDFA (wf : List Waveform) (m : DFA) (currState : State) : State :=
  match wf with
  | []                            => currState
  | (_, []) :: tlWF               => findNextStateDFA tlWF m currState
  | (port, currSig :: _) :: tlWF  =>
      let next := deltaDFA m.mBase.t currState (encodeSymbolDFA m port currSig)
      if next != currState then next
      else findNextStateDFA tlWF m currState

def findNextStateNFA (wf : List Waveform) (m : NFA) (currState : State) : List State :=
  match wf with
  | []                            => [currState]
  | (_, []) :: tlWF               => findNextStateNFA tlWF m currState
  | (port, currSig :: _) :: tlWF  =>
      let dests := deltaNFA m.t currState (encodeSymbolNFA m port currSig)
      match dests with
      | []  => findNextStateNFA tlWF m currState
      | _   =>
          if currState ∉ dests then dests
          else findNextStateNFA tlWF m currState

-- ══════════════════════════════════════════════
-- EXECUÇÃO DO DFA
-- ══════════════════════════════════════════════

def dfaExecutionFuel : Nat → List Waveform → DFA → State → List State
  | 0,        _,                        _, currState => [currState]
  | _,        [],                       _, currState => [currState]
  | _,        (_, []) :: _,            _, currState => [currState]
  | fuel + 1, wf@((_, _ :: _) :: _),  m,  currState =>
      currState :: dfaExecutionFuel fuel (dropHeads wf) m (findNextStateDFA wf m currState)

def dfaExecution (wf : List Waveform) (m : DFA) (currState : State) : List State :=
  dfaExecutionFuel (totalLength wf) (clockFilter wf) m currState

-- ══════════════════════════════════════════════
-- EXECUÇÃO DO NFA
-- ══════════════════════════════════════════════

def nfaExecutionFuel : Nat → List Waveform → NFA → State → List (List State)
  | 0,        _,                        _, currState => [[currState]]
  | _,        [],                       _, currState => [[currState]]
  | _,        (_, []) :: _,            _, currState => [[currState]]
  | fuel + 1, wf@((_, _ :: _) :: _),  m,  currState =>
      let nextStates := findNextStateNFA wf m currState
      nextStates.flatMap fun ns =>
        (nfaExecutionFuel fuel (dropHeads wf) m ns).map (currState :: ·)

def nfaExecution (wf : List Waveform) (m : NFA) (currState : State) : List (List State) :=
  nfaExecutionFuel (totalLength wf) (clockFilter wf) m currState

-- ══════════════════════════════════════════════
-- PREDICADO: TERMINA NUM ESTADO
-- ══════════════════════════════════════════════

inductive EndsInDFA (s : State) : List State → Prop where
  | base : EndsInDFA s [s]
  | step : ∀ h tl, EndsInDFA s tl → EndsInDFA s (h :: tl)

inductive EndsInNFA (s : State) : List State → Prop where
  | base : EndsInNFA s [s]
  | step : ∀ h tl, EndsInNFA s tl → EndsInNFA s (h :: tl)

-- ══════════════════════════════════════════════
-- ACEITAÇÃO
-- ══════════════════════════════════════════════

def dfaAccepts (m : DFA) (wf : List Waveform) : Prop :=
  ∃ s, EndsInDFA s (dfaExecution wf m m.mBase.q0) ∧ s ∈ m.mBase.f

def nfaAccepts (m : NFA) (wf : List Waveform) : Prop :=
  ∃ path s, path ∈ nfaExecution wf m m.q0 ∧ EndsInNFA s path ∧ s ∈ m.f

-- ══════════════════════════════════════════════
-- EXECUTORES DE SIMULAÇÃO
-- ══════════════════════════════════════════════

def runDFA (s : SimulationDFA) : List State :=
  dfaExecution s.wfCollectionDFA s.mDFA s.mDFA.mBase.q0

def runNFA (s : SimulationNFA) : List (List State) :=
  nfaExecution s.wfCollectionNFA s.mNFA s.mNFA.q0

def stopInAcceptanceStateDFA (s : SimulationDFA) : Prop :=
  dfaAccepts s.mDFA s.wfCollectionDFA

def stopInAcceptanceStateNFA (s : SimulationNFA) : Prop :=
  nfaAccepts s.mNFA s.wfCollectionNFA

-- ══════════════════════════════════════════════
-- TESTES RÁPIDOS
-- ══════════════════════════════════════════════

#eval recordPosedgeClock [false, true, false, true, false, true] 0
-- esperado: [1, 3, 5]

#eval dropHeads [("A", [true, false]), ("B", [false, true])]
-- esperado: [("A", [false]), ("B", [true])]
