import Parser.Grammar
import Parser.Table
import Parser.Codegen

def main (args : List String) : IO UInt32 := do
  let parserOutPath := args.headD "GeneratedParser.lean"
  let toAstOutPath  := "Parser/ToAst.lean"
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
      -- 1. Gera a conversão ParseTree → AST a partir das ações de Grammar.lean
      let toAstCode := emitToAstCode minicGrammar
      IO.FS.writeFile toAstOutPath toAstCode
      IO.println s!"Gerado '{toAstOutPath}' ({minicGrammar.prods.size} ações semânticas)."

      -- 2. Gera as tabelas estáticas LR(1)
      let parserCode := emitParserCode tbl
      IO.FS.writeFile parserOutPath parserCode
      let (actSz, gotoSz) := tbl.size
      IO.println s!"Gerado '{parserOutPath}': {tbl.states} estados, {actSz} ações, {gotoSz} gotos."
      return 0
