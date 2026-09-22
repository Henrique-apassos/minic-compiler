-- ─────────────────────────────────────────────
-- Common.lean
-- Definições base compartilhadas por NFA, DFA,
-- Simulation e Safety.
-- ─────────────────────────────────────────────

-- ══════════════════════════════════════════════
-- 1. TIPOS BASE
-- ══════════════════════════════════════════════

abbrev State      := Nat
abbrev Symbol     := String
abbrev Transition := (State × Symbol) × State
abbrev Signal     := Bool
abbrev Waveform   := Symbol × List Signal

-- ══════════════════════════════════════════════
-- 2. PREDICADOS SOBRE TRANSIÇÕES E ESTADOS
-- ══════════════════════════════════════════════

def eachTransitionIsValid
    (t : List Transition) (q : List State) (alphabet : List Symbol) : Prop :=
  match t with
  | [] => True
  | ((st1, tr), st2) :: tl =>
      st1 ∈ q ∧ tr ∈ alphabet ∧ st2 ∈ q ∧
      eachTransitionIsValid tl q alphabet

def eachAcceptanceStateIsValid (f : List State) (q : List State) : Prop :=
  ∀ s, s ∈ f → s ∈ q

-- ══════════════════════════════════════════════
-- 3. PREDICADOS SOBRE O ALFABETO (prefixo "N_")
-- ══════════════════════════════════════════════

def hasNPrefix (s : Symbol) : Bool :=
  s.startsWith "N_"

def existsWithNPrefix (s : Symbol) (l : List Symbol) : Prop :=
  ("N_" ++ s) ∈ l

def allElementsExistsN : List Symbol → Prop
  | []     => True
  | h :: t =>
      if !hasNPrefix h then
        existsWithNPrefix h (h :: t) ∧ allElementsExistsN t
      else
        allElementsExistsN t

-- ══════════════════════════════════════════════
-- 4. PROPRIEDADES DO DFA
-- ══════════════════════════════════════════════

def dfaUniqueTargetState
    (q : List State) (alphabet : List Symbol) (t : List Transition) : Prop :=
  ∀ (st : State) (a : Symbol) (q1 q2 : State),
    st ∈ q → a ∈ alphabet →
    ((st, a), q1) ∈ t → ((st, a), q2) ∈ t → q1 = q2

def dfaTotal
    (q : List State) (alphabet : List Symbol) (t : List Transition) : Prop :=
  ∀ (st : State) (a : Symbol),
    st ∈ q → a ∈ alphabet → ∃ q', ((st, a), q') ∈ t

-- ══════════════════════════════════════════════
-- 5. FUNÇÕES AUXILIARES SOBRE WAVEFORMS
-- ══════════════════════════════════════════════

def headWF (wf : List Waveform) : List Signal :=
  match wf.head? with
  | some (_, sig) => sig
  | none          => []

def checkWaveformSameLength : List Waveform → List Signal → Prop
  | [],              _     => True
  | (_, sig) :: tl,  first =>
      sig.length = first.length ∧ checkWaveformSameLength tl first

-- ══════════════════════════════════════════════
-- 6. FUNÇÕES DE CLOCK E POSEDGE
-- ══════════════════════════════════════════════

def nextSignal : List Bool → Bool
  | _ :: sig2 :: _ => sig2
  | _              => false

def recordPosedgeClock : List Bool → Nat → List Nat
  | [],        _    => []
  | sig :: tl, step =>
      if !sig && nextSignal (sig :: tl) then
        (step + 1) :: recordPosedgeClock tl (step + 1)
      else
        recordPosedgeClock tl (step + 1)

def selectPositions {α : Type} (pos : List Nat) (l : List α) : List α :=
  pos.filterMap (fun i => l[i]?)

def lookupWaveform (p : Symbol) : List Waveform → Option (List Bool)
  | []              => none
  | (q, sig) :: tl  => if p == q then some sig else lookupWaveform p tl

def getWaveform (p : Symbol) (wf : List Waveform) : List Bool :=
  (lookupWaveform p wf).getD []

def restrictPosedge (trigger : List Nat) : List Waveform → List Waveform
  | []                  => []
  | (port, sig) :: rest =>
      if port != "clk" then
        (port, selectPositions trigger sig) :: restrictPosedge trigger rest
      else
        restrictPosedge trigger rest

def clockFilter (wf : List Waveform) : List Waveform :=
  restrictPosedge (recordPosedgeClock (getWaveform "clk" wf) 0) wf

def dropHeads : List Waveform → List Waveform
  | []                      => []
  | (port, []) :: tl        => (port, []) :: dropHeads tl
  | (port, _ :: rest) :: tl => (port, rest) :: dropHeads tl

def totalLength : List Waveform → Nat
  | []           => 0
  | (_, s) :: tl => s.length + totalLength tl
