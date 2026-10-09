import Parser.Table
import Parser.Tree
import Scanner.Lexer

-- ══════════════════════════════════════════════
-- 1. ERRO DE SINTAXE
-- ══════════════════════════════════════════════

structure ParseError where
  found    : Token
  expected : List TokenKind
  deriving Repr

/-- Como o token aparece para o usuário nas mensagens de erro. -/
def TokenKind.describe : TokenKind → String
  | .kwInt => "'int'" | .kwFloat => "'float'" | .kwBool => "'bool'" | .kwStr => "'str'"
  | .kwVoid => "'void'" | .kwIf => "'if'" | .kwElse => "'else'" | .kwWhile => "'while'"
  | .kwReturn => "'return'" | .kwTrue => "'true'" | .kwFalse => "'false'"
  | .kwAnd => "'and'" | .kwOr => "'or'"
  | .id => "identificador" | .numInt => "número inteiro" | .numFloat => "número real"
  | .stringLit => "texto"
  | .plus => "'+'" | .minus => "'-'" | .times => "'*'" | .div => "'/'"
  | .eq => "'=='" | .neq => "'!='" | .lt => "'<'" | .le => "'<='" | .gt => "'>'" | .ge => "'>='"
  | .not => "'!'" | .assign => "'='"
  | .lparen => "'('" | .rparen => "')'" | .lbrace => "'{'" | .rbrace => "'}'"
  | .lbracket => "'['" | .rbracket => "']'" | .comma => "','" | .semi => "';'"
  | .eof => "fim do arquivo" | .error => "caractere não reconhecido"

/-- "a", "a ou b", "a, b ou c". -/
private def joinOu : List String → String
  | [] => ""
  | [x] => x
  | xs => ", ".intercalate xs.dropLast ++ " ou " ++ xs.getLast!

/-- `3:12: encontrei ';', esperava identificador, número inteiro ou '('` -/
def ParseError.message (e : ParseError) : String :=
  let pos := s!"{e.found.line}:{e.found.column}: "
  if e.found.kind == .error then
    pos ++ s!"caractere não reconhecido '{e.found.lexeme}'"
  else
    let msg := s!"encontrei {e.found.kind.describe}"
    let exp := e.expected.map TokenKind.describe
    pos ++ (if exp.isEmpty then msg else msg ++ ", esperava " ++ joinOu exp)

-- ══════════════════════════════════════════════
-- 2. MOTOR PREDITIVO COM PILHA EXPLÍCITA
-- ══════════════════════════════════════════════
-- Pilha de trabalho: símbolos a reconhecer e marcadores `close`, que dizem
-- "os últimos `n` valores formam o nó `nt.alt`". Pilha de valores: as subárvores prontas.
-- Cada passo olha só o topo e o token atual: sem retrocesso.

private inductive Item where
  | sym   (s : Sym)
  | close (nt : String) (alt : Nat) (n : Nat)

/-- O que pode vir agora, segundo a própria pilha: FIRST de cada símbolo, do topo para baixo,
    enquanto eles puderem ser vazios. Mais exato que a linha da tabela, que inclui o FOLLOW de
    todos os contextos (ex.: depois de `int x = 1`, só `;` fecha a expressão; `)` não). -/
private def expectedAt (tbl : LL1Table) (work : List Item) : List TokenKind :=
  let rec go : List Item → TokSet → TokSet
    | [], acc => acc
    | .close .. :: rest, acc => go rest acc
    | .sym (.t k) :: _, acc => acc.add k
    | .sym (.nt n) :: rest, acc =>
      let acc := TokSet.union acc (tbl.analysis.firstOf n)
      if tbl.analysis.isNullable n then go rest acc else acc
  let set := go work []
  tbl.grammar.terminals.filter set.contains

-- Termina: numa gramática LL(1) sem conflitos não há recursão à esquerda, então entre
-- dois consumos de token só cabem finitas expansões; e cada `close` encolhe a pilha.
private partial def loop (tbl : LL1Table) (toks : Array Token) (i : Nat)
    (work : List Item) (vals : List ParseTree) : Except ParseError ParseTree :=
  -- além do fim, o último token (o `eof` que o scanner sempre coloca)
  let cur := toks[i]?.getD (toks.back?.getD { kind := .eof, lexeme := "", line := 1, column := 1 })
  match work with
  | [] =>
      match vals with
      | [tree] => .ok tree
      | _ => .error { found := cur, expected := [] }   -- impossível: cada `close` deixa um valor
  | .sym (.t k) :: rest =>
      if cur.kind == k then loop tbl toks (i + 1) rest (.leaf cur :: vals)
      else .error { found := cur, expected := [k] }
  | .sym (.nt a) :: rest =>
      match tbl.lookup a cur.kind with
      | none => .error { found := cur, expected := expectedAt tbl work }
      | some p => loop tbl toks i (p.rhs.map .sym ++ .close a p.alt p.rhs.length :: rest) vals
  | .close a alt n :: rest =>
      -- `vals` está invertida: os `n` primeiros são os filhos, do último para o primeiro
      loop tbl toks i rest (.node a alt (vals.take n).reverse :: vals.drop n)

/-- Analisa os tokens a partir do símbolo inicial da gramática. -/
def parse (tbl : LL1Table) (toks : Array Token) : Except ParseError ParseTree :=
  loop tbl toks 0 [.sym (.nt tbl.grammar.start)] []

-- ══════════════════════════════════════════════
-- 3. ATALHOS PARA O MINIC
-- ══════════════════════════════════════════════

def parseMiniC (toks : Array Token) : Except ParseError ParseTree :=
  parse minicTable toks

def lexDFA : LexDFA := buildLexDFA lexicalRules

def parseSource (src : String) : Except ParseError ParseTree :=
  parseMiniC (scan lexDFA src)
