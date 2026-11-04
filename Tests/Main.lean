import Tests
import Tests.Syntax
import Tests.Programs
import Tests.TypeCheck

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
    ("tipos: expressões e operadores", tiposExpressoes),
    ("tipos: escopo e declarações", tiposEscopo),
    ("tipos: subsunção, arrays e junções", tiposSubsuncao),
    ("tipos: funções e chamadas", tiposChamadas),
    ("tipos: comandos e retorno", tiposComandos),
    ("tipos: propriedades do conjunto", tiposPropriedades),
    ("tipos: lacunas conhecidas (pendentes)", tiposLacunas)
  ] (verbose := args.contains "--verbose")
