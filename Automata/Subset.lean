import Automata.Common
import Automata.Thompson
import Std.Data.HashMap

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
-- As transições do NFA são indexadas uma vez por (estado, símbolo): assim cada
-- passo acha os destinos direto, em vez de percorrer a lista inteira de transições.

abbrev TransIndex := Std.HashMap (State × Symbol) (List State)

def indexTransitions (t : List Transition) : TransIndex :=
  t.foldl (fun m ((q0, sym), qf) => m.insert (q0, sym) (qf :: m.getD (q0, sym) [])) {}

/-- Estados alcançáveis por ε a partir de `current` (busca com pilha; resultado canônico). -/
partial def epsilonClosure (idx : TransIndex) (current : List State) : List State :=
  go current (canonizeStates current)
where
  go (pending seen : List State) : List State :=
    match pending with
    | [] => seen
    | q :: rest =>
      let new := (idx.getD (q, "ε") []).filter (· ∉ seen)
      go (new ++ rest) (new.foldl (fun acc s => insertState s acc) seen)

def move (idx : TransIndex) (states : List State) (sym : Symbol) : List State :=
  canonizeStates (states.flatMap (fun q => idx.getD (q, sym) []))

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
  qIndex    : Std.HashMap (List State) State   -- o mesmo que `qMap`, para busca direta
  workList  : List (List State)
  dfaTrans  : List Transition
  alphabet  : List Symbol

/-- Ambiente inicial: só o estado `q0` (o fecho-ε do início do NFA), com id 0. -/
def SubsetEnv.init (q0 : List State) (alphabet : List Symbol) : SubsetEnv :=
  { nextDfaId := 1, qMap := [(q0, 0)], qIndex := ({} : Std.HashMap _ _).insert q0 0,
    workList := [q0], dfaTrans := [], alphabet := alphabet }

partial def subsetLoop (env : SubsetEnv) (nfaTrans : TransIndex) : SubsetEnv :=
  match env.workList with
  | [] => env
  | q :: restWorkList =>
      let qId := env.qIndex.getD q 0

      let newEnv := env.alphabet.foldl (fun currEnv c =>
        let deltaQC := move nfaTrans q c
        let t := epsilonClosure nfaTrans deltaQC

        if t.isEmpty then currEnv
        else
          match currEnv.qIndex[t]? with
          | some tId =>
              { currEnv with
                dfaTrans := ((qId, c), tId) :: currEnv.dfaTrans
              }
          | none =>
              let newTId := currEnv.nextDfaId
              { currEnv with
                nextDfaId := currEnv.nextDfaId + 1,
                qMap      := (t, newTId) :: currEnv.qMap,
                qIndex    := currEnv.qIndex.insert t newTId,
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
  let idx := indexTransitions raw.transitions
  let q0 := epsilonClosure idx [raw.start]

  let finalEnv := subsetLoop (SubsetEnv.init q0 alphabet) idx

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
