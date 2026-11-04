import Tests.Harness

-- ══════════════════════════════════════════════
-- TESTES DO SCANNER E DOS AUTÔMATOS (partes novas)
-- ══════════════════════════════════════════════
-- Cobre o que entrou nos PRs #6 e #7 e só era testado de passagem pelo parser:
--   * minimização do DFA (Automata/Minimize.lean)             — EaC §2.4.4
--   * classe de caracteres `Regex.anyOf` (Automata/Thompson)   — EaC §2.3, §2.4.2
--   * literais de string e o símbolo "qualquer outro"          — EaC §2.5.1, decisão 20
--   * comentários de bloco                                     — EaC §2.5
-- Cada teste diz o que verifica (nome), de onde vem a exigência (`ref`) e por que importa
-- (`why`). `lake test -- --verbose` lista tudo isso.

private def t (ref why : String) (x : Test) : Test := x.doc ref why

-- ── Ferramentas ────────────────────────────────

/-- Tipo e lexema de cada token, sem o `eof` final. -/
private def toks (dfa : LexDFA) (src : String) : List (TokenKind × String) :=
  ((scan dfa src).toList.filter fun tk => tk.kind != .eof).map fun tk => (tk.kind, tk.lexeme)

private def tokensAre (name src : String) (want : List (TokenKind × String)) : Test :=
  let got := toks lexDFA src
  { name, ok := got == want, detail := s!"obtido {repr got}, esperado {repr want}" }

private def firstIs (name src : String) (want : TokenKind) : Test :=
  match toks lexDFA src with
  | (k, _) :: _ => { name, ok := k == want, detail := s!"primeiro token: {repr k}, esperado {repr want}" }
  | [] => { name, ok := false, detail := "nenhum token" }

/-- O `n`-ésimo token (contando o `eof`) está em `linha:coluna`. -/
private def posIs (name src : String) (n line col : Nat) : Test :=
  match (scan lexDFA src)[n]? with
  | some tk =>
    { name, ok := tk.line == line && tk.column == col,
      detail := s!"token {n} em {tk.line}:{tk.column}, esperado {line}:{col}" }
  | none => { name, ok := false, detail := s!"não há token {n}" }

private def rawLexDFA : LexDFA := buildLexDFA lexicalRules false

private def table (edges : List (Nat × String × Nat)) : Std.HashMap (State × Symbol) State :=
  edges.foldl (fun m (s, c, d) => m.insert (s, c) d) {}

/-- Classes da minimização de um DFA escrito à mão (`labels[s]` = rótulo do estado `s`). -/
private def classes (labels : List Nat) (edges : List (Nat × String × Nat)) : Array Nat :=
  minimizeClasses labels.length ["a", "b", "c"] (table edges) fun s => labels.getD s 0

private def nClasses (cls : Array Nat) : Nat := cls.toList.eraseDups.length

-- ── 1. Minimização ─────────────────────────────

def scannerMinimizacao : List Test := [
  t "EaC §2.4.4 (Hopcroft)"
    "É o caso mínimo do que a minimização faz: 1 e 2 têm o mesmo futuro, 3 e 4 também. Se não fundir, o DFA do scanner não encolhe."
    (let c := classes [0, 0, 0, 1, 1] [(0, "a", 1), (0, "b", 2), (1, "c", 3), (2, "c", 4)]
     { name := "estados com o mesmo futuro são fundidos"
       ok := c[1]! == c[2]! && c[3]! == c[4]! && nClasses c == 3,
       detail := s!"classes {c}" }),
  t "EaC §2.4.4: a partição inicial separa por rótulo"
    "Dois tokens diferentes (por exemplo kwInt e id) nunca podem virar o mesmo estado, mesmo com transições idênticas."
    (let c := classes [1, 2] []
     { name := "estados que aceitam tokens diferentes nunca se fundem",
       ok := nClasses c == 2, detail := s!"classes {c}" }),
  t "EaC §2.4.4"
    "Aceitar e não aceitar são comportamentos diferentes; fundi-los mudaria a linguagem reconhecida."
    (let c := classes [0, 1] []
     { name := "estado que aceita e estado que não aceita não se fundem",
       ok := nClasses c == 2, detail := s!"classes {c}" }),
  t "DFA parcial do scanner (Subset.lean:89 descarta o conjunto vazio)"
    "Transição ausente é um destino próprio: quem tem 'a' e quem não tem não são equivalentes. Errar aqui faria o scanner aceitar lexemas a mais."
    (let c := classes [0, 0, 0, 1] [(1, "a", 3)]
     { name := "transição ausente conta como destino distinto",
       ok := c[1]! != c[2]!, detail := s!"classes {c}" }),
  t "EaC §2.4.4: o refinamento roda até estabilizar"
    "Os estados 0 e 3 só diferem duas transições adiante. Uma única rodada os fundiria; o laço com combustível tem de repetir."
    (let c := classes [0, 0, 1, 0, 0, 2] [(0, "a", 1), (1, "a", 2), (3, "a", 4), (4, "a", 5)]
     { name := "diferença a duas transições de distância ainda separa os estados",
       ok := c[0]! != c[3]! && c[1]! != c[4]!, detail := s!"classes {c}" }),
  t "EaC §2.4.4"
    "O fecho a* gera um ciclo; estados num ciclo equivalente devem fundir sem o algoritmo girar para sempre."
    (let c := classes [1, 1] [(0, "a", 1), (1, "a", 0)]
     { name := "ciclo de estados equivalentes vira um estado só",
       ok := nClasses c == 1, detail := s!"classes {c}" }),
  t "Automata/Minimize.lean"
    "Se minimizar de novo ainda reduzisse, a primeira passada estaria incompleta."
    (let cls := minimizeClasses lexDFA.numStates lexDFA.alphabet.toList lexDFA.trans
      (fun s => match lexDFA.accepting[s]? with | some k => k.ctorIdx + 1 | none => 0)
     { name := "o DFA minimizado do scanner já é mínimo",
       ok := nClasses cls == lexDFA.numStates,
       detail := s!"{lexDFA.numStates} estados, {nClasses cls} classes ao minimizar de novo" }),
  t "Scanner/Lexer.lean:buildLexDFA; PR #6"
    "A minimização não pode mover nenhuma fronteira de token. Compara o DFA bruto com o mínimo em lexemas de cada categoria."
    (let inputs := ["", "int", "intx", "if", "iff", "<=", "<", "=", "==", "!=", "!", "3.14", "3.", ".5",
      "a_b9", "_", "9a", "\"s\"", "// c\n x", "/* c */ x", "@", "x=1;"]
     let bad := inputs.filter fun s => toks lexDFA s != toks rawLexDFA s
     { name := "bruto e mínimo geram os mesmos tokens em 22 entradas",
       ok := bad.isEmpty, detail := s!"entradas que divergem: {bad}" })
]

-- ── 2. Classe de caracteres ────────────────────

def scannerClasse : List Test := [
  t "EaC §2.4.2 (um fragmento por operador)"
    "A classe de caracteres é um fragmento só (2 estados), em vez de uma cadeia de uniões com 2 estados por letra. É o que impede o NFA e o DFA de inchar."
    (let n := regexToRawNFA (Regex.anyOf ["a", "b", "c"])
     { name := "anyOf de 3 símbolos cria 2 estados e 3 transições",
       ok := n.start == 0 && n.accept == 1 && n.transitions.length == 3
         && n.transitions.all fun ((s, _), d) => s == n.start && d == n.accept,
       detail := s!"{repr n}" }),
  t "EaC §2.3 (classes de caracteres)"
    "Uma classe vazia não casa nada; o caso de borda não pode virar casar tudo."
    (let d := buildLexDFA [(Regex.anyOf [], .id)]
     { name := "anyOf vazio nunca casa", ok := (longestMatch d #['a'] 0).isNone, detail := "casou" }),
  t "EaC §2.3"
    "A classe reconhece exatamente um dos símbolos dados."
    (let d := buildLexDFA [(Regex.anyOf ["a", "b", "c"], .id)]
     { name := "anyOf casa um símbolo da classe e só um",
       ok := longestMatch d #['b'] 0 == some (1, .id) && (longestMatch d #['d'] 0).isNone
         && longestMatch d #['a', 'b'] 0 == some (1, .id),
       detail := "casamento inesperado" }),
  t "EaC §2.4.2: a classe equivale à união dos literais"
    "Troca de implementação sem mudar a linguagem: a regra antiga (uniões) e a nova (anyOf) devem dar os mesmos tokens."
    (let viaUnion := buildLexDFA [(Regex.union (Regex.literal "a") (Regex.union (Regex.literal "b") (Regex.literal "c")), .id)]
     let viaClass := buildLexDFA [(Regex.anyOf ["a", "b", "c"], .id)]
     let inputs := ["a", "b", "c", "d", "ab", ""]
     { name := "anyOf e cadeia de uniões geram os mesmos tokens",
       ok := inputs.all fun s => toks viaUnion s == toks viaClass s, detail := "tokens divergem" })
]

-- ── 3. Strings ─────────────────────────────────

def scannerStrings : List Test := [
  t "decisão 20; EaC §2.5.1"
    "O caso mais simples: o literal vira um token só, com as aspas no lexema (o ToAst as retira)."
    (tokensAre "uma string simples é um token" "\"abc\"" [(.stringLit, "\"abc\"")]),
  t "decisão 20"
    "A string vazia é o caso de borda do corpo (zero repetições)."
    (tokensAre "a string vazia" "\"\"" [(.stringLit, "\"\"")]),
  t "decisão 20; maximal munch (EaC §2.5.1)"
    "Duas strings coladas são dois tokens: o casamento para no primeiro fecha-aspas."
    (tokensAre "duas strings coladas" "\"a\"\"b\"" [(.stringLit, "\"a\""), (.stringLit, "\"b\"")]),
  t "decisão 20"
    "Dentro da string não há comentário nem palavra-chave: tudo é texto."
    (tokensAre "// e palavra-chave dentro da string não contam"
      "\"int // x\"" [(.stringLit, "\"int // x\"")]),
  t "PR #7: comentário de bloco é tratado em scanLoop"
    "O scanLoop olha '/*' antes do DFA; uma string que contém '/*' não pode ser engolida como comentário."
    (tokensAre "/* dentro da string não abre comentário" "\"a/*b\"" [(.stringLit, "\"a/*b\"")]),
  t "símbolo 'qualquer outro' (otherSym)"
    "O alfabeto vem das regras e é fechado; sem otherSym, 'á' dentro de aspas não teria transição."
    (tokensAre "caractere fora do alfabeto dentro da string" "\"olá 日本\"" [(.stringLit, "\"olá 日本\"")]),
  t "decisão 63 (escapes)"
    "O escape \\\" mantém o literal aberto; sem ele não haveria como escrever aspas dentro da string."
    (tokensAre "aspas escapadas ficam no literal" "\"a\\\"b\"" [(.stringLit, "\"a\\\"b\"")]),
  t "decisão 63 (escapes)"
    "Só \\\" \\\\ \\n \\t são escapes; outro é erro léxico em vez de passar calado."
    (firstIs "escape desconhecido é erro" "\"a\\qb\"" .error),
  t "decisão 63"
    "Uma barra seguida de aspas é escape, então esta string não fecha."
    (firstIs "\"\\\" não fecha" "\"\\\"" .error),
  t "EaC §2.5: um literal não atravessa linhas"
    "Esquecer o fecha-aspas não pode engolir o arquivo inteiro; a quebra de linha encerra o erro perto de onde ele está."
    (firstIs "quebra de linha dentro da string é erro" "\"ab\ncd\"" .error),
  t "contagem de coluna"
    "O token depois da string tem de ficar na coluna certa, senão todas as mensagens de erro seguintes mentem."
    (posIs "posição do token depois de uma string" "x = \"ab\"; y" 4 1 11)
]

-- ── 4. Comentários ─────────────────────────────

def scannerComentarios : List Test := [
  t "PR #7"
    "Caso de borda: o '*' do abre e o '*' do fecha não podem ser o mesmo."
    (tokensAre "comentário vazio /**/" "a /**/ b" [(.id, "a"), (.id, "b")]),
  t "PR #7"
    "O comentário sai do fluxo de tokens, como o espaço."
    (tokensAre "comentário de bloco entre tokens" "a /* x */ b" [(.id, "a"), (.id, "b")]),
  t "PR #7: sem aninhamento"
    "Documenta a escolha, igual à do C: o primeiro */ fecha. O resto vira tokens comuns. Se o grupo quiser aninhar, este teste muda."
    (tokensAre "comentários não aninham" "/* /* */ x */" [(.id, "x"), (.times, "*"), (.div, "/")]),
  t "PR #7"
    "O '/' do abre também é o '/' do fecha em '/*/': não pode contar como fechado."
    (firstIs "/*/ não fecha" "/*/" .error),
  t "PR #7"
    "Comentário sem fecha vira um erro no '/*' e o resto é descartado, em vez de travar ou sumir sem aviso."
    (tokensAre "comentário sem fechar" "a /* b c" [(.id, "a"), (.error, "/*")]),
  t "PR #7; contagem de linha"
    "O comentário atravessa linhas; a linha e a coluna do que vem depois têm de refletir isso."
    (posIs "posição depois de um comentário de várias linhas" "a /* l1\nl2\nl3 */ b" 1 3 7),
  t "comentário de linha continua valendo"
    "A mudança para os blocos não pode ter quebrado o '//': ele acaba na quebra de linha, não depois."
    (posIs "// vai até a quebra de linha" "a // x\nb" 1 2 1),
  t "EaC §2.5.1: maximal munch"
    "O '/' sozinho continua sendo divisão; só '/*' abre comentário."
    (tokensAre "/ e * separados não abrem comentário" "a / * b"
      [(.id, "a"), (.div, "/"), (.times, "*"), (.id, "b")]),
  t "PR #7"
    "Um */ solto não é comentário nem erro: são dois operadores."
    (tokensAre "*/ solto são dois operadores" "a */ b" [(.id, "a"), (.times, "*"), (.div, "/"), (.id, "b")])
]

-- ── 5. Caracteres fora do alfabeto ─────────────

def scannerForaDoAlfabeto : List Test := [
  t "símbolo 'qualquer outro' só vale dentro da string"
    "Fora de string, um caractere que nenhuma regra conhece continua sendo erro léxico."
    (firstIs "@ fora de string é erro" "@" .error),
  t "símbolo 'qualquer outro' só vale dentro da string"
    "Mesma regra para caracteres não ASCII: é o otherSym que existe só no corpo da string."
    (firstIs "á fora de string é erro" "á" .error),
  t "EaC §2.5: o scanner continua depois do erro"
    "Um erro léxico não pode esconder os tokens seguintes; o parser decide quando parar."
    (tokensAre "o scanner segue depois de um caractere inválido" "a @ b"
      [(.id, "a"), (.error, "@"), (.id, "b")])
]
