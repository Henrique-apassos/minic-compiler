import Scanner.Basic
import Std.Data.HashMap
import Std.Data.HashSet

-- ══════════════════════════════════════════════
-- 1. NFA COMBINADO (todas as regras num só autómato)
-- ══════════════════════════════════════════════
-- Um novo estado inicial liga por ε ao início de cada regra.
-- `accepts` guarda (estado de aceitação, token) NA ORDEM DAS REGRAS:
-- a posição na lista é a prioridade (a primeira regra ganha empates).

structure TaggedNFA where
  start       : State
  transitions : List Transition
  accepts     : List (State × TokenKind)

def buildCombined (rules : List (Regex × TokenKind)) : BuilderM TaggedNFA := do
  let s0 ← freshState
  let mut trans : List Transition := []
  let mut accepts : List (State × TokenKind) := []
  for (r, k) in rules do
    let n ← buildThompson r
    trans := trans ++ n.transitions ++ [((s0, "ε"), n.start)]
    accepts := accepts ++ [(n.accept, k)]
  return { start := s0, transitions := trans, accepts := accepts }

-- ══════════════════════════════════════════════
-- 2. ALFABETO EXTRAÍDO DAS REGRAS
-- ══════════════════════════════════════════════
-- `Regex.symbols` está em Automata/Thompson.lean.

-- ══════════════════════════════════════════════
-- 3. DFA DO SCANNER (com tabela de transições e etiquetas)
-- ══════════════════════════════════════════════

structure LexDFA where
  start     : State
  trans     : Std.HashMap (State × Symbol) State
  accepting : Std.HashMap State TokenKind
  /-- Caracteres que alguma regra menciona; qualquer outro vira `otherSym`. -/
  alphabet  : Std.HashSet Symbol

/-- Reaproveita `epsilonClosure` e `subsetLoop` de `Automata.Subset`.
    Cada estado do DFA aceita o token da PRIMEIRA regra cujo estado de
    aceitação do NFA pertence ao conjunto. -/
def buildLexDFA (rules : List (Regex × TokenKind)) : LexDFA :=
  let (tnfa, _) := (buildCombined rules).run 0
  let alphabet := (rules.flatMap (fun (r, _) => r.symbols)).eraseDups
  let idx := indexTransitions tnfa.transitions
  let q0 := epsilonClosure idx [tnfa.start]
  let env := subsetLoop (SubsetEnv.init q0 alphabet) idx
  let trans := env.dfaTrans.foldl
    (fun m ((s, c), d) => m.insert (s, c) d) {}
  let accepting := env.qMap.foldl (fun m (states, id) =>
    match tnfa.accepts.find? (fun (a, _) => a ∈ states) with
    | some (_, k) => m.insert id k
    | none        => m) {}
  { start := 0, trans := trans, accepting := accepting, alphabet := Std.HashSet.ofList alphabet }

-- ══════════════════════════════════════════════
-- 4. MAXIMAL MUNCH
-- ══════════════════════════════════════════════
-- Corre o DFA o mais longe possível e devolve o último ponto onde
-- estava num estado de aceitação: (fim do lexema, token).

-- Símbolo do DFA para um caractere: ele mesmo se alguma regra o menciona, senão
-- `otherSym` (o "qualquer outro" das classes de caracteres, como em `"olá"`).
-- A quebra de linha nunca é `otherSym`: assim ela encerra o literal de string.
def LexDFA.symbolOf (dfa : LexDFA) (c : Char) : Symbol :=
  if c == '\n' || dfa.alphabet.contains c.toString then c.toString else otherSym

def longestMatch (dfa : LexDFA) (cs : Array Char) (i : Nat) : Option (Nat × TokenKind) :=
  go i dfa.start none
where
  go (j : Nat) (st : State) (best : Option (Nat × TokenKind)) : Option (Nat × TokenKind) :=
    if h : j < cs.size then
      match dfa.trans[(st, dfa.symbolOf cs[j])]? with
      | none    => best
      | some st' =>
          let best' := match dfa.accepting[st']? with
            | some k => some (j + 1, k)
            | none   => best
          go (j + 1) st' best'
    else best
  termination_by cs.size - j

def skipLineComment (cs : Array Char) (i : Nat) : Nat :=
  if h : i < cs.size then
    if cs[i] == '\n' then i else skipLineComment cs (i + 1)
  else i
termination_by cs.size - i

/-- Depois de `/*`: posição, linha e coluna logo após o `*/`, ou `none` se o comentário
    não fecha. Conta as quebras de linha que atravessa. -/
def skipBlockComment (cs : Array Char) (i line col : Nat) : Option (Nat × Nat × Nat) :=
  if h : i < cs.size then
    if cs[i] == '*' && cs[i + 1]? == some '/' then some (i + 2, line, col + 2)
    else if cs[i] == '\n' then skipBlockComment cs (i + 1) (line + 1) 1
    else skipBlockComment cs (i + 1) line (col + 1)
  else none
termination_by cs.size - i

def sliceString (cs : Array Char) (i j : Nat) : String :=
  String.ofList (cs.extract i j).toList

-- ══════════════════════════════════════════════
-- 5. SCANNER
-- ══════════════════════════════════════════════

partial def scanLoop (dfa : LexDFA) (cs : Array Char)
    (i line col : Nat) (acc : Array Token) : Array Token :=
  if i ≥ cs.size then
    acc.push { kind := .eof, lexeme := "", line := line, column := col }
  else
    let c := cs[i]!
    if c == '\n' then scanLoop dfa cs (i + 1) (line + 1) 1 acc
    else if c.isWhitespace then scanLoop dfa cs (i + 1) line (col + 1) acc
    else if c == '/' && cs[i + 1]? == some '/' then
      let j := skipLineComment cs i
      scanLoop dfa cs j line (col + (j - i)) acc
    else if c == '/' && cs[i + 1]? == some '*' then
      match skipBlockComment cs (i + 2) line (col + 2) with
      | some (j, line', col') => scanLoop dfa cs j line' col' acc
      | none =>
          -- comentário sem fechar: token de erro no `/*` e o resto do arquivo é descartado
          scanLoop dfa cs cs.size line col
            (acc.push { kind := .error, lexeme := "/*", line := line, column := col })
    else
      match longestMatch dfa cs i with
      | some (j, k) =>
          let tok : Token := { kind := k, lexeme := sliceString cs i j, line := line, column := col }
          scanLoop dfa cs j line (col + (j - i)) (acc.push tok)
      | none =>
          -- caractere que nenhuma regra reconhece: token de erro e segue
          let tok : Token := { kind := .error, lexeme := c.toString, line := line, column := col }
          scanLoop dfa cs (i + 1) line (col + 1) (acc.push tok)

def scan (dfa : LexDFA) (src : String) : Array Token :=
  scanLoop dfa src.toList.toArray 0 1 1 #[]
