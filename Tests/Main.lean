import Tests
import Tests.Syntax
import Tests.Programs
import Tests.Scanner

/-- `lake test` (ou `lake test -- --verbose` para listar cada teste com referência e motivo).
    Sai com 1 se algum teste falhar. Testes pendentes não falham a execução. -/
def main (args : List String) : IO UInt32 := do
  runAll [
    ("gerador, motor e AST", checks.map fun (name, ok) => ({ name, ok } : Test)),
    ("literais", literais),
    ("identificadores", identificadores),
    ("expressões", expressoes),
    ("chamadas", chamadas),
    ("arrays", arrays),
    ("comandos", comandos),
    ("funções", funcoes),
    ("programas (fixtures)", ← programas),
    ("scanner: minimização do DFA", scannerMinimizacao),
    ("scanner: classe de caracteres (anyOf)", scannerClasse),
    ("scanner: literais de string", scannerStrings),
    ("scanner: comentários de bloco", scannerComentarios),
    ("scanner: caracteres fora do alfabeto", scannerForaDoAlfabeto)
  ] (verbose := args.contains "--verbose")
