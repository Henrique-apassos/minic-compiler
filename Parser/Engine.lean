import Parser.Table
import Parser.Tree
import Scanner.Lexer

-- ══════════════════════════════════════════════
-- 1. ERROS DE SINTAXE
-- ══════════════════════════════════════════════

structure ParseError where
  line     : Nat
  column   : Nat
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

/-- `3:12: encontrei ';', esperava identificador, número inteiro ou '('`. -/
def ParseError.message (e : ParseError) : String :=
  let pos := s!"{e.line}:{e.column}: "
  if e.found.kind == .error then
    pos ++ s!"caractere não reconhecido '{e.found.lexeme}'"
  else
    let exp := (e.expected.eraseDups.map TokenKind.describe)
    let msg := s!"encontrei {e.found.kind.describe}"
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

private def eofTok : Token := { kind := .eof, lexeme := "", line := 1, column := 1 }

/-- Token na posição `i`; além do fim do vetor, o último token (o `eof`). -/
private def tokAt (toks : Array Token) (i : Nat) : Token :=
  toks[i]?.getD (toks.back?.getD eofTok)

private def errAt (tok : Token) (exp : List TokenKind) : ParseError :=
  { line := tok.line, column := tok.column, found := tok, expected := exp }

-- Termina: numa gramática LL(1) sem conflitos não há recursão à esquerda, então entre
-- dois consumos de token só cabem finitas expansões; e cada `close` encolhe a pilha.
private partial def loop (tbl : LL1Table) (toks : Array Token) (i : Nat)
    (work : List Item) (vals : List ParseTree) : Except ParseError ParseTree :=
  let cur := tokAt toks i
  match work with
  | [] =>
      match vals with
      | [tree] =>
          if i < toks.size && cur.kind != .eof then .error (errAt cur [.eof]) else .ok tree
      | _ => .error (errAt cur [])   -- impossível: cada `close` deixa um único valor
  | .sym (.t k) :: rest =>
      if cur.kind == k then loop tbl toks (i + 1) rest (.leaf cur :: vals)
      else .error (errAt cur [k])
  | .sym (.nt a) :: rest =>
      match tbl.lookup a cur.kind with
      | none => .error (errAt cur (tbl.expected a))
      | some p => loop tbl toks i (p.rhs.map .sym ++ .close a p.alt p.rhs.length :: rest) vals
  | .close a alt n :: rest =>
      -- `vals` está invertida: os `n` primeiros são os filhos, do último para o primeiro
      loop tbl toks i rest (.node a alt (vals.take n).reverse :: vals.drop n)

def parseFrom (tbl : LL1Table) (start : String) (toks : Array Token) : Except ParseError ParseTree :=
  loop tbl toks 0 [.sym (.nt start)] []

def parse (tbl : LL1Table) (toks : Array Token) : Except ParseError ParseTree :=
  parseFrom tbl tbl.grammar.start toks

-- ══════════════════════════════════════════════
-- 3. ATALHOS PARA O MINIC
-- ══════════════════════════════════════════════

def parseMiniC (toks : Array Token) : Except ParseError ParseTree :=
  parse minicTable toks

def lexDFA : LexDFA := buildLexDFA lexicalRules

def parseSource (src : String) : Except ParseError ParseTree :=
  parseMiniC (scan lexDFA src)
