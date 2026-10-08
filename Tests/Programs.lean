import Tests.Harness

-- Portado de `MiniC/tests/program.rs`. Os fixtures são cópias de `MiniC/tests/fixtures/`
-- (só os que o parser consome). Lê relativo à raiz do pacote: `lake test` já roda de lá.
-- Fora de escopo: `pointer_*.minic` (DECISOES #11) e `interpreter_*`/`cli_*` (sem interpretador).

private def fixtureDir : String := "Tests/fixtures/"

private def load (name : String) : IO (Except String (Program Unit)) := do
  pure (parseProgram (← IO.FS.readFile (fixtureDir ++ name)))

private def expectProg (name : String) (want : Program Unit) : IO Test := do
  pure (expectEq name (← load name) want fun p => p.show)

private def rejectProg (name : String) : IO Test := do
  pure (expectErr name (← load name) fun p => p.show)

private def asg (x : String) (e : E) : S := .assign (eVar x) e

def programas : IO (List Test) := do
  pure [
    ← expectProg "empty.minic" [],
    ← expectProg "statements_only.minic"
      [{ name := "main", params := [], ret := .void
         body := .block [.decl .int "x" (eInt 1), .decl .int "y" (eInt 2)] }],
    ← expectProg "function_single.minic"
      [{ name := "foo", params := [], ret := .void, body := .decl .int "x" (eInt 1) }],
    ← expectProg "function_with_block.minic"
      [{ name := "add", params := [(.int, "x"), (.int, "y")], ret := .void
         body := .block [asg "x" (eBin .add (eVar "x") (eVar "y")), asg "x" (eVar "x")] }],
    ← expectProg "full_program.minic"
      [{ name := "inc", params := [(.int, "x")], ret := .void
         body := .block [asg "x" (eBin .add (eVar "x") (eInt 1)), asg "x" (eVar "x")] },
       { name := "main", params := [], ret := .void
         body := .block [.call "inc" [eInt 1], .decl .int "y" (eInt 42)] }],
    ← rejectProg "invalid_syntax.minic",
    ← rejectProg "top_level_statements.minic"
  ]
