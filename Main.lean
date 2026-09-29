import Scanner
import Automata.DFA

def sample : String :=
"int fatorial(int n) {
  // comentário
  if (n <= 1) { return 1; }
  float x = 3.14;
  int intx = 42;
  return n * fatorial(n - 1);
}
a == b != c @"

def main : IO Unit := do
  IO.println "Compilador Mini-C pronto para execução."
  let dfa := buildLexDFA lexicalRules
  IO.println s!"Estados do DFA: {dfa.trans.size} transições, {dfa.accepting.size} estados de aceitação"
  for t in scan dfa sample do
    IO.println s!"{t.line}:{t.column}\t{repr t.kind}\t{t.lexeme.quote}"
