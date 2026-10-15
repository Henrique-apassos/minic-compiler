import Parser.Grammar
import Parser.Table
import Parser.Codegen

def main (args : List String) : IO UInt32 := do
  let outputFile := args.headD "Parser/Generated.lean"
  match buildTable minicGrammar with
  | .error (.conflicts cs) =>
      IO.eprintln s!"Erro: gramática possui {cs.length} conflitos LR(1)!"
      return 1
  | .error (.tooManyStates n) =>
      IO.eprintln s!"Erro: limite de estados excedido ({n})!"
      return 1
  | .ok tbl =>
      let code := generateParserCode tbl
      IO.FS.writeFile outputFile code
      IO.println s!"Arquivo '{outputFile}' gerado com sucesso ({tbl.states} estados)."
      return 0
