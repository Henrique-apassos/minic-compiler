import Parser.Grammar
import Parser.Table
import Parser.Codegen

def main (args : List String) : IO UInt32 := do
  let outPath := args.headD "GeneratedParser.lean"
  match buildTable minicGrammar with
  | .error (.conflicts cs) =>
      IO.eprintln s!"erro: a gramática possui {cs.length} conflitos LR(1):"
      for c in cs do
        IO.eprintln s!"  estado {c.state}, token {reprStr c.tok}: {reprStr c.actions}"
      return 1
  | .error (.tooManyStates n) =>
      IO.eprintln s!"erro: limite de estados LR(1) excedido ({n})."
      return 1
  | .ok tbl =>
      let code := emitParserCode tbl
      IO.FS.writeFile outPath code
      let (actSz, gotoSz) := tbl.size
      IO.println s!"Gerado '{outPath}': {tbl.states} estados, {actSz} ações, {gotoSz} gotos."
      return 0
