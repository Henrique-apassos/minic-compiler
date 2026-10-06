import Parser

def sample : String :=
"int fatorial(int n) {
  // comentário
  if n <= 1 { return 1; }
  float x = 3.14;
  int[] v = [1, 2, 3];
  v[0] = -v[1] * 2;
  return n * fatorial(n - 1 - 0);
}"

/-- `lake exe minic-compiler [arquivo.c]`: sem arquivo, usa o programa de exemplo.
    Texto → tokens → árvore de derivação → AST, e imprime a AST (ou o erro com linha:coluna). -/
def main (args : List String) : IO UInt32 := do
  let src ← match args with
    | path :: _ => IO.FS.readFile path
    | [] => pure sample
  match parseProgram src with
  | .ok prog =>
    IO.println prog.show
    return 0
  | .error msg =>
    IO.eprintln s!"erro: {msg}"
    return 1
