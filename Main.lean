import GeneratedParser
import Parser.TypeCheck
import Lean.Data.Json

open GeneratedParser
open Lean (ToJson toJson)

/-- Exporta a estrutura em formato JSON formatado (pretty) para um arquivo local. -/
def exportToJson {α : Type} [ToJson α] (data : α) (filename : String) : IO Unit := do
  let jsonStr := Lean.Json.pretty (toJson data)
  IO.FS.writeFile filename jsonStr
  IO.println s!"[Exportação] Arquivo salvo: {filename}"

/-- `lake exe minic-compiler [arquivo.minic]`: sem arquivo, usa o programa de exemplo.
    Texto → tokens → árvore de derivação → AST tipada, e imprime a AST (ou o erro). -/
def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.eprintln "Uso: lake exe minic <arquivo_fonte.minic>"
    return

  let filePath := args.head!
  let src ← IO.FS.readFile filePath

  match GeneratedParser.parseProgram src with
  | .error err =>
      IO.eprintln s!"Erro Sintático: {err}"
  | .ok rawAst =>
      IO.println "Parser concluído."
      -- Exporta a AST sem tipos (Unit)
      exportToJson rawAst "Outputs/ast_raw.json"

      match typeCheckProgram rawAst with
      | .error err =>
          IO.eprintln s!"Erro Semântico: {err}"
      | .ok typedAst =>
          IO.println "Type Checker concluído."
          -- Exporta a AST anotada com os tipos (MType)
          exportToJson typedAst "Outputs/ast_typed.json"

          IO.println "Front-end executado com sucesso."
