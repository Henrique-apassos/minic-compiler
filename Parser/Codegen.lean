import Parser.Table

-- ══════════════════════════════════════════════
-- GERADOR DE CÓDIGO DO PARSER LR(1)
-- ══════════════════════════════════════════════

private def emitTokenKind (k : TokenKind) : String :=
  let s := reprStr k
  match s.splitOn "." with
  | _ :: tail => "." ++ ".".intercalate tail
  | _ => s

private def emitSym : Sym → String
  | .t k  => s!".t {emitTokenKind k}"
  | .nt n => s!".nt {n.quote}"

private def emitAction : Action → String
  | .shift s  => s!".shift {s}"
  | .reduce p => s!".reduce {p}"
  | .accept   => ".accept"

/-- Divide uma lista em blocos de tamanho máximo `size`. -/
private def chunkList (size : Nat) (xs : List String) : List (List String) :=
  let (chunks, cur, _) := xs.foldl (init := ([], [], 0)) fun (chunks, cur, count) x =>
    if count + 1 >= size then
      ((x :: cur).reverse :: chunks, [], 0)
    else
      (chunks, x :: cur, count + 1)
  if cur.isEmpty then chunks.reverse else (cur.reverse :: chunks).reverse

/-- Gera definições `private def` separadas para cada bloco de 40 entradas,
    evitando árvores LCNF profundas numa única definição. -/
private def emitChunkDefs (baseName : String) (elemType : String) (entries : List String) :
    List String × String :=
  let chunks := chunkList 40 entries
  let defs := (chunks.zipIdx).map fun (c, i) =>
    let body := ",\n".intercalate (c.map ("  " ++ ·))
    s!"private def {baseName}_{i} : List ({elemType}) := [\n{body}\n]"
  let names := ", ".intercalate ((chunks.zipIdx).map fun (_, i) => s!"{baseName}_{i}")
  (defs, s!"[{names}]")

/-- Gera o código-fonte Lean completo do parser a partir de uma `LR1Table`. -/
def emitParserCode (tbl : LR1Table) : String :=
  -- 1. Produções da gramática
  let prodsLines := tbl.grammar.prods.toList.map fun p =>
    let rhsStr := ", ".intercalate (p.rhs.map emitSym)
    s!"    \{ id := {p.id}, lhs := {p.lhs.quote}, alt := {p.alt}, rhs := [{rhsStr}] }"

  -- 2. Entradas da tabela ACTION em definições separadas
  let actionsSorted := tbl.action.toArray.qsort fun ((s1, k1), _) ((s2, k2), _) =>
    s1 < s2 || (s1 == s2 && k1 < k2)
  let actionLines := actionsSorted.toList.map fun ((s, k), act) =>
    s!"(({s}, {k}), {emitAction act})"
  let (actionDefs, actionListRef) := emitChunkDefs "actionChunk" "(Nat × Nat) × Action" actionLines

  -- 3. Entradas da tabela GOTO em definições separadas
  let gotosSorted := tbl.goto.toArray.qsort fun ((s1, n1), _) ((s2, n2), _) =>
    s1 < s2 || (s1 == s2 && n1 < n2)
  let gotoLines := gotosSorted.toList.map fun ((s, n), dst) =>
    s!"(({s}, {n.quote}), {dst})"
  let (gotoDefs, gotoListRef) := emitChunkDefs "gotoChunk" "(Nat × String) × Nat" gotoLines

  String.intercalate "\n" ([
    "-- ════════════════════════════════════════════════════════════════════",
    "-- FICHEIRO GERADO AUTOMATICAMENTE POR `lake exe gen-parser`",
    s!"-- Estados LR(1): {tbl.states} | Produções: {tbl.grammar.prods.size} | ACTION: {tbl.action.size} | GOTO: {tbl.goto.size}",
    "-- NÃO EDITE MANUALMENTE.",
    "-- ════════════════════════════════════════════════════════════════════",
    "import Std.Data.HashMap",
    "import Parser.Engine",
    "import Parser.ToAst",
    "",
    "set_option maxRecDepth 100000",
    "",
    "namespace GeneratedParser",
    "",
    "private def mkMap {α β : Type} [BEq α] [Hashable α] (chunks : List (List (α × β))) : Std.HashMap α β :=",
    "  chunks.foldl (fun m chunk => chunk.foldl (fun m (k, v) => m.insert k v) m) {}",
    "",
    "/-- Gramática embutida no código gerado. -/",
    "def generatedGrammar : Grammar := {",
    s!"  start := {tbl.grammar.start.quote},",
    "  prods := #[",
    ",\n".intercalate prodsLines,
    "  ]",
    "}",
    ""
  ] ++ actionDefs ++ [""] ++ gotoDefs ++ [
    "",
    "/-- Tabela LR(1) canónica pré-calculada em código-fonte. -/",
    "def generatedTable : LR1Table := {",
    "  grammar := generatedGrammar,",
    s!"  states  := {tbl.states},",
    s!"  action  := mkMap {actionListRef},",
    s!"  goto    := mkMap {gotoListRef}",
    "}",
    "",
    "/-- Analisa um array de tokens usando a tabela gerada estaticamente. -/",
    "def parseTokens (toks : Array Token) : Except ParseError ParseTree :=",
    "  parse generatedTable toks",
    "",
    "/-- Analisa código-fonte Mini-C e devolve a Árvore de Derivação (`ParseTree`). -/",
    "def parseSource (src : String) : Except ParseError ParseTree :=",
    "  parseTokens (scan lexDFA src)",
    "",
    "/-- Analisa código-fonte Mini-C e devolve a AST (`Program Unit`). -/",
    "def parseProgram (src : String) : Except String (Program Unit) :=",
    "  match parseSource src with",
    "  | .error e => throw e.message",
    "  | .ok tree => toProgram tree",
    "",
    "end GeneratedParser",
    ""
  ])
