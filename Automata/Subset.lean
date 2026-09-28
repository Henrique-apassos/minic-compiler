import Automata.Common
import Automata.Thompson

-- ══════════════════════════════════════════════
-- 0. ESTRUTURA DO DFA GERADO
-- ══════════════════════════════════════════════
-- Uma versão sem provas do DFA

structure RawDFA where
  q        : List State
  alphabet : List Symbol
  t        : List Transition
  q0       : State
  f        : List State
  deriving Repr

-- ══════════════════════════════════════════════
-- 1. NORMALIZAÇÃO DE CONJUNTOS DE ESTADOS
-- ══════════════════════════════════════════════

def insertState (s : State) : List State → List State
  | [] => [s]
  | h :: t =>
      if s < h then s :: h :: t
      else if s == h then h :: t
      else h :: insertState s t

def canonizeStates (l : List State) : List State :=
  l.foldl (fun acc s => insertState s acc) []

-- ══════════════════════════════════════════════
-- 2. FECHO-ÉPSILON E MOVE
-- ══════════════════════════════════════════════

partial def epsilonClosure (t : List Transition) (current : List State) : List State :=
  let nextStates := current.flatMap (fun q =>
    t.filterMap (fun ((q0, sym), qf) =>
      if q0 == q && sym == "ε" then some qf else none
    )
  )
  let combined := canonizeStates (current ++ nextStates)

  if combined.length == current.length then combined
  else epsilonClosure t combined

def move (t : List Transition) (states : List State) (sym : Symbol) : List State :=
  let nextStates := states.flatMap (fun q =>
    t.filterMap (fun ((q0, s), qf) =>
      if q0 == q && s == sym then some qf else none
    )
  )
  canonizeStates nextStates

-- ══════════════════════════════════════════════
-- 3. O MOTOR DO ALGORITMO (SUBSET CONSTRUCTION)
-- ══════════════════════════════════════════════

def getId (q : List State) (map : List (List State × State)) : Option State :=
  match map with
  | [] => none
  | (k, v) :: tail => if k == q then some v else getId q tail

structure SubsetEnv where
  nextDfaId : State
  qMap      : List (List State × State)
  workList  : List (List State)
  dfaTrans  : List Transition
  alphabet  : List Symbol

partial def subsetLoop (env : SubsetEnv) (nfaTrans : List Transition) : SubsetEnv :=
  match env.workList with
  | [] => env
  | q :: restWorkList =>
      let qId := (getId q env.qMap).get!

      let newEnv := env.alphabet.foldl (fun currEnv c =>
        let deltaQC := move nfaTrans q c
        let t := epsilonClosure nfaTrans deltaQC

        if t.isEmpty then currEnv
        else
          match getId t currEnv.qMap with
          | some tId =>
              { currEnv with
                dfaTrans := ((qId, c), tId) :: currEnv.dfaTrans
              }
          | none =>
              let newTId := currEnv.nextDfaId
              { currEnv with
                nextDfaId := currEnv.nextDfaId + 1,
                qMap      := (t, newTId) :: currEnv.qMap,
                workList  := t :: currEnv.workList,
                dfaTrans  := ((qId, c), newTId) :: currEnv.dfaTrans
              }
      ) { env with workList := restWorkList }

      subsetLoop newEnv nfaTrans

-- ══════════════════════════════════════════════
-- 4. FUNÇÃO DE ENTRADA
-- ══════════════════════════════════════════════

/-- Transforma um RawNFA num RawDFA determinístico -/
def constructDFA (raw : RawNFA) (alphabet : List Symbol) : RawDFA :=
  let q0 := epsilonClosure raw.transitions [raw.start]

  let initialEnv : SubsetEnv := {
    nextDfaId := 1,
    qMap      := [(q0, 0)],
    workList  := [q0],
    dfaTrans  := [],
    alphabet  := alphabet
  }

  let finalEnv := subsetLoop initialEnv raw.transitions

  -- Qualquer estado do DFA que contenha o estado de aceitação do NFA também é um estado de aceitação
  let dfaAcceptStates := finalEnv.qMap.filterMap (fun (states, id) =>
    if raw.accept ∈ states then some id else none
  )

  {
    q        := finalEnv.qMap.map (fun (_, id) => id),
    alphabet := alphabet,
    t        := finalEnv.dfaTrans,
    q0       := 0,
    f        := dfaAcceptStates
  }


-- ══════════════════════════════════════════════
-- TESTE
-- ══════════════════════════════════════════════

-- Definição da Regex: a(b|c)*
def testeRegex : Regex :=
  Regex.concat
    (Regex.literal "a")
    (Regex.star
      (Regex.union
        (Regex.literal "b")
        (Regex.literal "c")
      )
    )

-- 1. Gera o NFA
def myNFA := regexToRawNFA testeRegex

-- 2. Converte para DFA passando o alfabeto explícito
#eval constructDFA myNFA ["a", "b", "c"]
