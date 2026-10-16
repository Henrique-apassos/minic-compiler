import Parser.Table

-- ══════════════════════════════════════════════
-- 1. GERADOR AUTOMÁTICO DE `Parser/ToAst.lean`
-- ══════════════════════════════════════════════

/-- Verifica se a variável `s{i}` é usada na expressão `action`. -/
private def usesVar (action : String) (i : Nat) : Bool :=
  (action.splitOn s!"s{i}").length > 1

/-- Emite o ramo `| .node "<lhs>" <alt> [s0, _, s2] => <action>` de uma produção. -/
private def emitProdArm (p : Production) : String :=
  let vars := (List.range p.rhs.length).map fun i =>
    if usesVar p.action i then s!"s{i}" else "_"
  let pat := ", ".intercalate vars
  s!"  | .node {p.lhs.quote} {p.alt} [{pat}] => {p.action.trimAscii}"

/-- Emite todos os ramos das produções que pertencem ao grupo `k`. -/
private def emitGroupArms (g : Grammar) (k : NtKind) : List String :=
  (g.prods.toList.filter (·.kind == k)).map emitProdArm

/-- Gera o código completo de `Parser/ToAst.lean` a partir das ações em `Grammar.lean`. -/
def emitToAstCode (g : Grammar) : String :=
  String.intercalate "\n" ([
    "-- ════════════════════════════════════════════════════════════════════",
    "-- ARQUIVO GERADO AUTOMATICAMENTE POR `lake exe gen-parser`",
    "-- Conversão ParseTree → AST gerada a partir de `Parser/Grammar.lean`.",
    "-- NÃO EDITE MANUALMENTE.",
    "-- ════════════════════════════════════════════════════════════════════",
    "import Parser.Ast",
    "import Parser.Engine",
    "",
    "private def FormatError (t : ParseTree) : Except String α :=",
    "  match t with",
    "  | .node nt alt _ => throw s!\"árvore mal formada em {nt}.{alt}\"",
    "  | .leaf tok => throw s!\"árvore mal formada no token '{tok.lexeme}'\"",
    "",
    "private def lexeme (t : ParseTree) : Except String String :=",
    "  match t with",
    "  | .leaf tok => pure tok.lexeme",
    "  | _ => FormatError t",
    "",
    "private def parseInt (s : String) : Except String Int :=",
    "  match s.toNat? with",
    "  | some v => pure v",
    "  | none => throw s!\"número inteiro inválido '{s}'\"",
    "",
    "private def parseFloat (s : String) : Except String Float :=",
    "  match s.splitOn \".\" with",
    "  | [int, float] =>",
    "    match int.toNat?, float.toNat? with",
    "    | some i, some f => pure (Float.ofScientific (i * 10 ^ float.length + f) true float.length)",
    "    | _, _ => throw s!\"número real inválido '{s}'\"",
    "  | _ => throw s!\"número real inválido '{s}'\"",
    "",
    "private def unquote (s : String) : String :=",
    "  if s.length >= 2 && s.startsWith \"\\\"\" && s.endsWith \"\\\"\" then",
    "    String.ofList (s.toList.drop 1).dropLast",
    "  else s",
    "",
    "-- ── Tipos ──────────────────────────────────────",
    "",
    "private def toBaseType : ParseTree → Except String MType"
  ] ++ emitGroupArms g .baseType ++ [
    "  | t => FormatError t",
    "",
    "private def wrapDims (base : MType) : ParseTree → Except String MType"
  ] ++ emitGroupArms g .dims ++ [
    "  | t => FormatError t",
    "",
    "def toType : ParseTree → Except String MType"
  ] ++ emitGroupArms g .type ++ [
    "  | t => FormatError t",
    "",
    "-- ── Operadores Binários ────────────────────────",
    "",
    "private def toBinOp : ParseTree → Except String BinOp"
  ] ++ emitGroupArms g .binOp ++ [
    "  | t => FormatError t",
    "",
    "-- ── Expressões ─────────────────────────────────",
    "",
    "mutual",
    "",
    "def toExpr : ParseTree → Except String (Expr Unit)"
  ] ++ emitGroupArms g .expr ++ [
    "  | t => FormatError t",
    "",
    "def toAtomRest (idName : String) : ParseTree → Except String (Expr Unit)"
  ] ++ emitGroupArms g .atomRest ++ [
    "  | t => FormatError t",
    "",
    "def foldTail (acc : Expr Unit) : ParseTree → Except String (Expr Unit)"
  ] ++ emitGroupArms g .exprTail ++ [
    "  | t => FormatError t",
    "",
    "def foldIndex (acc : Expr Unit) : ParseTree → Except String (Expr Unit)"
  ] ++ emitGroupArms g .indexTail ++ [
    "  | t => FormatError t",
    "",
    "def toArgs : ParseTree → Except String (List (Expr Unit))"
  ] ++ emitGroupArms g .args ++ [
    "  | t => FormatError t",
    "",
    "end",
    "",
    "-- ── Comandos ───────────────────────────────────",
    "",
    "private def toOptExpr : ParseTree → Except String (Option (Expr Unit))"
  ] ++ emitGroupArms g .optExpr ++ [
    "  | t => FormatError t",
    "",
    "private def toIdStmt (idName : String) : ParseTree → Except String (Stmt Unit)"
  ] ++ emitGroupArms g .idStmt ++ [
    "  | t => FormatError t",
    "",
    "mutual",
    "",
    "def toStmt : ParseTree → Except String (Stmt Unit)"
  ] ++ emitGroupArms g .stmt ++ [
    "  | t => FormatError t",
    "",
    "def toElseOpt : ParseTree → Except String (Option (Stmt Unit))"
  ] ++ emitGroupArms g .elseOpt ++ [
    "  | t => FormatError t",
    "",
    "def toBlock : ParseTree → Except String (Stmt Unit)"
  ] ++ emitGroupArms g .block ++ [
    "  | t => FormatError t",
    "",
    "def toStmtList : ParseTree → Except String (List (Stmt Unit))"
  ] ++ emitGroupArms g .stmtList ++ [
    "  | t => FormatError t",
    "",
    "end",
    "",
    "-- ── Funções e Programa ─────────────────────────",
    "",
    "private def toParam : ParseTree → Except String (MType × String)"
  ] ++ emitGroupArms g .param ++ [
    "  | t => FormatError t",
    "",
    "private def toParams : ParseTree → Except String (List (MType × String))"
  ] ++ emitGroupArms g .params ++ [
    "  | t => FormatError t",
    "",
    "def toFun : ParseTree → Except String (FunDecl Unit)"
  ] ++ emitGroupArms g .funDecl ++ [
    "  | t => FormatError t",
    "",
    "private def toFunList : ParseTree → Except String (Program Unit)"
  ] ++ emitGroupArms g .funList ++ [
    "  | t => FormatError t",
    "",
    "def toProgram : ParseTree → Except String (Program Unit)"
  ] ++ emitGroupArms g .program ++ [
    "  | t => FormatError t",
    "",
    "/-- De ponta a ponta: Scanner, motor LR(1) e conversão para AST. -/",
    "def parseProgram (src : String) : Except String (Program Unit) :=",
    "  match parseSource src with",
    "  | .error e => throw e.message",
    "  | .ok tree => toProgram tree",
    ""
  ])

-- ══════════════════════════════════════════════
-- 2. GERADOR DE `GeneratedParser.lean` (TABELAS LR(1))
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

private def chunkList (size : Nat) (xs : List String) : List (List String) :=
  let (chunks, cur, _) := xs.foldl (init := ([], [], 0)) fun (chunks, cur, count) x =>
    if count + 1 >= size then
      ((x :: cur).reverse :: chunks, [], 0)
    else
      (chunks, x :: cur, count + 1)
  if cur.isEmpty then chunks.reverse else (cur.reverse :: chunks).reverse

private def emitChunkDefs (baseName : String) (elemType : String) (entries : List String) :
    List String × String :=
  let chunks := chunkList 40 entries
  let defs := (chunks.zipIdx).map fun (c, i) =>
    let body := ",\n".intercalate (c.map ("  " ++ ·))
    s!"private def {baseName}_{i} : List ({elemType}) := [\n{body}\n]"
  let names := ", ".intercalate ((chunks.zipIdx).map fun (_, i) => s!"{baseName}_{i}")
  (defs, s!"[{names}]")

/-- Gera o código-fonte Lean completo das tabelas LR(1) a partir de uma `LR1Table`. -/
def emitParserCode (tbl : LR1Table) : String :=
  let prodsLines := tbl.grammar.prods.toList.map fun p =>
    let rhsStr := ", ".intercalate (p.rhs.map emitSym)
    s!"    \{ id := {p.id}, lhs := {p.lhs.quote}, alt := {p.alt}, rhs := [{rhsStr}] }"

  let actionsSorted := tbl.action.toArray.qsort fun ((s1, k1), _) ((s2, k2), _) =>
    s1 < s2 || (s1 == s2 && k1 < k2)
  let actionLines := actionsSorted.toList.map fun ((s, k), act) =>
    s!"(({s}, {k}), {emitAction act})"
  let (actionDefs, actionListRef) := emitChunkDefs "actionChunk" "(Nat × Nat) × Action" actionLines

  let gotosSorted := tbl.goto.toArray.qsort fun ((s1, n1), _) ((s2, n2), _) =>
    s1 < s2 || (s1 == s2 && n1 < n2)
  let gotoLines := gotosSorted.toList.map fun ((s, n), dst) =>
    s!"(({s}, {n.quote}), {dst})"
  let (gotoDefs, gotoListRef) := emitChunkDefs "gotoChunk" "(Nat × String) × Nat" gotoLines

  String.intercalate "\n" ([
    "-- ════════════════════════════════════════════════════════════════════",
    "-- ARQUIVO GERADO AUTOMATICAMENTE POR `lake exe gen-parser`",
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
