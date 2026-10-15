import Parser.Table

-- ══════════════════════════════════════════════
-- GERADOR DE CÓDIGO DO PARSER LR(1)
-- ══════════════════════════════════════════════
-- Serializa `LR1Table` num arquivo `.lean` autônomo que recebe `String` (ou `Array Token`)
-- e devolve `Except String (Program Unit)`, pronto para a fase de Análise de Tipos.

private def emitTokenKind (k : TokenKind) : String :=
  let s := reprStr k
  match s.splitOn "." with
  | _ :: tail => "." ++ ".".intercalate tail
  | _ => s

private def emitAction (a : Action) : String :=
  match a with
  | .shift s  => s!".shift {s}"
  | .reduce p => s!".reduce {p}"
  | .accept   => ".accept"

/-- Gera o código-fonte completo de `Parser/Generated.lean` a partir da tabela LR(1). -/
def generateParserCode (tbl : LR1Table) : String :=
  -- 1. Produções: (lhs, alt, |rhs|)
  let prodsCode := tbl.grammar.prods.toList.map fun p =>
    s!"  ({p.lhs.quote}, {p.alt}, {p.rhs.length})"

  -- 2. Entradas de ACTION ordenadas por (estado, tokIdx)
  let actionsSorted := tbl.action.toArray.qsort fun ((s1, k1), _) ((s2, k2), _) =>
    s1 < s2 || (s1 == s2 && k1 < k2)
  let actionsCode := actionsSorted.toList.map fun ((s, k), act) =>
    s!"  (({s}, {k}), {emitAction act})"

  -- 3. Entradas de GOTO ordenadas por (estado, não-terminal)
  let gotosSorted := tbl.goto.toArray.qsort fun ((s1, n1), _) ((s2, n2), _) =>
    s1 < s2 || (s1 == s2 && n1 < n2)
  let gotosCode := gotosSorted.toList.map fun ((s, n), dst) =>
    s!"  (({s}, {n.quote}), {dst})"

  -- 4. Tokens esperados por estado (para diagnóstico de erro sintático)
  let expectedCode := (List.range tbl.states).map fun s =>
    let toks := (tbl.expected s).map emitTokenKind
    s!"  #[{", ".intercalate toks}]"

  String.intercalate "\n" [
    "-- ════════════════════════════════════════════════════════════════════",
    "-- ARQUIVO GERADO AUTOMATICAMENTE PELO GERADOR DE PARSER LR(1)",
    s!"-- Estados: {tbl.states} | Produções: {tbl.grammar.prods.size} | Ações: {tbl.action.size} | Gotos: {tbl.goto.size}",
    "-- NÃO EDITE MANUALMENTE.",
    "-- ════════════════════════════════════════════════════════════════════",
    "import Std.Data.HashMap",
    "import Scanner.Lexer",
    "import Parser.Tree",
    "import Parser.Ast",
    "",
    "namespace GeneratedParser",
    "",
    "inductive Action where",
    "  | shift  (s : Nat)",
    "  | reduce (p : Nat)",
    "  | accept",
    "  deriving Repr, BEq, Inhabited",
    "",
    "/-- Produções da gramática: `(lhs, alt, rhsLen)` indexadas pelo ID da produção. -/",
    "def prods : Array (String × Nat × Nat) := #[",
    ",\n".intercalate prodsCode,
    "]",
    "",
    "/-- Tabela ACTION[(estado, tokIdx)] gerada pelo autômato LR(1) canônico. -/",
    "def actionMap : Std.HashMap (Nat × Nat) Action := Std.HashMap.ofList [",
    ",\n".intercalate actionsCode,
    "]",
    "",
    "/-- Tabela GOTO[(estado, não-terminal)] gerada pelo autômato LR(1) canônico. -/",
    "def gotoMap : Std.HashMap (Nat × String) Nat := Std.HashMap.ofList [",
    ",\n".intercalate gotosCode,
    "]",
    "",
    "/-- Tokens esperados em cada estado para mensagens de erro. -/",
    "def expectedByState : Array (Array TokenKind) := #[",
    ",\n".intercalate expectedCode,
    "]",
    "",
    "-- ══════════════════════════════════════════════",
    "-- MOTOR SHIFT-REDUCE SOBRE A TABELA GERADA",
    "-- ══════════════════════════════════════════════",
    "",
    "structure ParseError where",
    "  found    : Token",
    "  expected : List TokenKind",
    "  deriving Repr",
    "",
    "def TokenKind.describe : TokenKind → String",
    "  | .kwInt => \"'int'\" | .kwFloat => \"'float'\" | .kwBool => \"'bool'\" | .kwStr => \"'str'\"",
    "  | .kwVoid => \"'void'\" | .kwIf => \"'if'\" | .kwElse => \"'else'\" | .kwWhile => \"'while'\"",
    "  | .kwReturn => \"'return'\" | .kwTrue => \"'true'\" | .kwFalse => \"'false'\"",
    "  | .kwAnd => \"'and'\" | .kwOr => \"'or'\"",
    "  | .id => \"identificador\" | .numInt => \"número inteiro\" | .numFloat => \"número real\"",
    "  | .stringLit => \"texto\"",
    "  | .plus => \"'+'\" | .minus => \"'-'\" | .times => \"'*'\" | .div => \"'/'\"",
    "  | .eq => \"'=='\" | .neq => \"'!='\" | .lt => \"'<'\" | .le => \"'<='\" | .gt => \"'>'\" | .ge => \"'>='\"",
    "  | .not => \"'!'\" | .assign => \"'='\"",
    "  | .lparen => \"'('\" | .rparen => \"')'\" | .lbrace => \"'{'\" | .rbrace => \"'}'\"",
    "  | .lbracket => \"'['\" | .rbracket => \"']'\" | .comma => \"','\" | .semi => \"';'\"",
    "  | .eof => \"fim do arquivo\" | .error => \"caractere não reconhecido\"",
    "",
    "private def joinOu : List String → String",
    "  | [] => \"\"",
    "  | [x] => x",
    "  | xs => \", \".intercalate xs.dropLast ++ \" ou \" ++ xs.getLast!",
    "",
    "def ParseError.message (e : ParseError) : String :=",
    "  let pos := s!\"{e.found.line}:{e.found.column}: \"",
    "  if e.found.kind == .error then",
    "    pos ++ s!\"caractere não reconhecido '{e.found.lexeme}'\"",
    "  else",
    "    let msg := s!\"encontrei {e.found.kind.describe}\"",
    "    let exp := e.expected.map TokenKind.describe",
    "    pos ++ (if exp.isEmpty then msg else msg ++ \", esperava \" ++ joinOu exp)",
    "",
    "private partial def loop (toks : Array Token) (i : Nat)",
    "    (states : List Nat) (vals : List ParseTree) : Except ParseError ParseTree :=",
    "  let cur := toks[i]?.getD (toks.back?.getD { kind := .eof, lexeme := \"\", line := 1, column := 1 })",
    "  let s := states.headD 0",
    "  match actionMap.get? (s, cur.kind.ctorIdx) with",
    "  | none =>",
    "    let exp := (expectedByState[s]?.getD #[]).toList",
    "    .error { found := cur, expected := exp }",
    "  | some (.shift t) => loop toks (i + 1) (t :: states) (.leaf cur :: vals)",
    "  | some (.reduce p) =>",
    "    match prods[p]? with",
    "    | none => .error { found := cur, expected := [] }",
    "    | some (lhs, alt, n) =>",
    "      let states := states.drop n",
    "      let node := ParseTree.node lhs alt (vals.take n).reverse",
    "      match gotoMap.get? (states.headD 0, lhs) with",
    "      | some t => loop toks i (t :: states) (node :: vals.drop n)",
    "      | none => .error { found := cur, expected := [] }",
    "  | some .accept =>",
    "    match vals with",
    "    | [tree] => .ok tree",
    "    | _ => .error { found := cur, expected := [] }",
    "",
    "def parseTokens (toks : Array Token) : Except ParseError ParseTree :=",
    "  loop toks 0 [0] []",
    "",
    "end GeneratedParser"
  ]
