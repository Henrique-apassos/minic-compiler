import GeneratedParser

def sample : String :=
"int fatorial(int n) {
  // comentário
  if n <= 1 { return 1; }
  float x = 3.14;
  int[] v = [1, 2, 3];
  v[0] = -v[1] * 2;
  return n * fatorial(n - 1 - 0);
}"

/-- `lake exe minic-compiler [arquivo.minic]`: sem arquivo, usa o programa de exemplo.
    Texto → tokens → árvore de derivação → AST tipada, e imprime a AST (ou o erro). -/
def main (args : List String) : IO UInt32 := do
  let src ← match args with
    | path :: _ =>
      if !path.endsWith ".minic" then
        IO.eprintln s!"erro: o arquivo '{path}' deve usar a extensão .minic"
        return 1
      IO.FS.readFile path
    | [] => pure sample
  match GeneratedParser.checkProgram src with
  | .ok prog =>
    IO.println prog.show
    return 0
  | .error msg =>
    IO.eprintln s!"erro: {msg}"
    return 1
