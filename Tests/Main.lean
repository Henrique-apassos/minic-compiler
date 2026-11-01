import Tests
import Tests.Syntax
import Tests.Programs

/-- `lake test`. Sai com 1 se algum teste falhar. Testes pendentes não falham a execução. -/
def main : IO UInt32 := do
  runAll [
    ("gerador, motor e AST", checks.map fun (name, ok) => ({ name, ok } : Test)),
    ("literais", literais),
    ("identificadores", identificadores),
    ("expressões", expressoes),
    ("chamadas", chamadas),
    ("arrays", arrays),
    ("comandos", comandos),
    ("funções", funcoes),
    ("programas (fixtures)", ← programas)
  ]
