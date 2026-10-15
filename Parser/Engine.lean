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
-- 2. MOTOR LR(1) (SHIFT-REDUCE) COM PILHA EXPLÍCITA
-- ══════════════════════════════════════════════
-- Pilha de estados e pilha de valores (as subárvores prontas), lado a lado.
-- Cada passo olha o estado do topo e o token atual em ACTION:
-- * shift s  : empilha o estado `s` e a folha do token, avança um token;
-- * reduce p : desempilha |rhs| estados e valores, monta o nó `lhs.alt` com eles
--              e empilha GOTO[estado do topo, lhs];
-- * accept   : a pilha de valores tem a árvore do símbolo inicial.
-- Sem retrocesso. Como o LR(1) canônico nunca reduz com um token inválido, o erro aparece
-- no estado do último shift, e os esperados são exatamente as ações desse estado.

-- Termina: cada shift consome um token, e entre dois shifts só cabem finitas reduções
-- (a gramática não tem conflitos, logo não é ambígua nem tem ciclos A ⇒+ A).
private partial def loop (tbl : LR1Table) (toks : Array Token) (i : Nat)
    (states : List Nat) (vals : List ParseTree) : Except ParseError ParseTree :=
  -- além do fim, o último token (o `eof` que o scanner sempre coloca)
  let cur := toks[i]?.getD (toks.back?.getD { kind := .eof, lexeme := "", line := 1, column := 1 })
  let s := states.headD 0
  match tbl.actionAt s cur.kind with
  | none => .error { found := cur, expected := tbl.expected s }
  | some (.shift t) => loop tbl toks (i + 1) (t :: states) (.leaf cur :: vals)
  | some (.reduce p) =>
    match tbl.grammar.prods[p]? with
    | none => .error { found := cur, expected := [] }     -- impossível: `p` vem da própria gramática
    | some prod =>
      let n := prod.rhs.length
      let states := states.drop n
      -- `vals` está invertida: os `n` primeiros são os filhos, do último para o primeiro
      let node := ParseTree.node prod.lhs prod.alt (vals.take n).reverse
      match tbl.gotoAt (states.headD 0) prod.lhs with
      | some t => loop tbl toks i (t :: states) (node :: vals.drop n)
      | none => .error { found := cur, expected := [] }   -- impossível: houve shift de `lhs` aqui
  | some .accept =>
    match vals with
    | [tree] => .ok tree
    | _ => .error { found := cur, expected := [] }        -- impossível: só aceita com S' → S •

/-- Analisa os tokens a partir do estado inicial do autômato. -/
def parse (tbl : LR1Table) (toks : Array Token) : Except ParseError ParseTree :=
  loop tbl toks 0 [0] []

-- ══════════════════════════════════════════════
-- 3. ATALHOS PARA O MINIC
-- ══════════════════════════════════════════════

def parseMiniC (toks : Array Token) : Except ParseError ParseTree :=
  parse minicTable toks

def lexDFA : LexDFA := buildLexDFA lexicalRules

def parseSource (src : String) : Except ParseError ParseTree :=
  parseMiniC (scan lexDFA src)
