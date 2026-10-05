import Scanner.Basic

-- ══════════════════════════════════════════════
-- ÁRVORE DE DERIVAÇÃO (o contrato entre o motor e a conversão para AST)
-- ══════════════════════════════════════════════
-- O motor LL(1) devolve esta árvore; a conversão para AST a consome.
--
-- * `leaf tok`            : um terminal lido, com o token inteiro (linha e coluna).
-- * `node nt alt kids`    : um não-terminal `nt`, expandido pela alternativa `alt`
--                           (0 = primeira alternativa de `nt` na gramática, 1 = segunda, ...).
--                           Uma produção ε aparece como `kids = []`.
--
-- Os nomes dos não-terminais e a ordem das alternativas são os de `Parser/Grammar.lean`.

inductive ParseTree where
  | leaf (tok : Token)
  | node (nt : String) (alt : Nat) (kids : List ParseTree)
  deriving Repr

instance : Inhabited ParseTree := ⟨.node "" 0 []⟩

namespace ParseTree

/-- Forma compacta, sem posições: `(Add.0 (Mul.0 ...) (AddTail.1))`.
    Usada nos testes para comparar árvores. -/
partial def toSExpr : ParseTree → String
  | .leaf tok =>
      if tok.kind == .eof then "<eof>" else tok.lexeme
  | .node nt alt [] => s!"({nt}.{alt})"
  | .node nt alt kids => s!"({nt}.{alt} " ++ " ".intercalate (kids.map toSExpr) ++ ")"

/-- Desenho indentado, para ler a árvore no terminal. -/
partial def pretty (t : ParseTree) (indent : String := "") : String :=
  match t with
  | .leaf tok =>
      let lex := if tok.kind == .eof then "<eof>" else tok.lexeme.quote
      s!"{indent}{lex}  [{tok.line}:{tok.column}]\n"
  | .node nt alt kids =>
      let head := if kids.isEmpty then s!"{indent}{nt}.{alt}  (ε)\n" else s!"{indent}{nt}.{alt}\n"
      head ++ String.join (kids.map (pretty · (indent ++ "  ")))

/-- Primeiro nó (em pré-ordem) com o não-terminal dado. -/
partial def find? (nt : String) : ParseTree → Option ParseTree
  | t@(.node n _ kids) => if n == nt then some t else kids.findSome? (find? nt)
  | .leaf _ => none

end ParseTree

-- ══════════════════════════════════════════════
-- EXEMPLO À MÃO: a expressão `a - b - c`
-- ══════════════════════════════════════════════
-- Subárvore `Add` que o motor produz para `int main() { return a - b - c; }`.
-- Serve para a conversão para AST ser escrita e testada sem depender do motor.
-- (Um teste em `Parser/Tests.lean` confere que o motor gera exatamente esta forma.)
--
--   Add.0
--   ├─ Mul.0 ── a           (cadeia Mul → Unary → Postfix → Atom → id)
--   └─ AddTail.0
--      ├─ AddOp.1 ── '-'
--      ├─ Mul.0 ── b
--      └─ AddTail.0
--         ├─ AddOp.1 ── '-'
--         ├─ Mul.0 ── c
--         └─ AddTail.1      (ε)

namespace ParseTree.Example

private def tok (k : TokenKind) (lex : String) (col : Nat) : Token :=
  { kind := k, lexeme := lex, line := 1, column := col }

/-- Um operando simples: o identificador `x` na coluna `col`.
    Mul.0 = Unary MulTail · Unary.1 = Postfix · Postfix.0 = Atom PostTail
    Atom.5 = id AtomRest · AtomRest.1 = ε · PostTail.1 = ε · MulTail.1 = ε -/
def operand (x : String) (col : Nat) : ParseTree :=
  .node "Mul" 0 [
    .node "Unary" 1 [
      .node "Postfix" 0 [
        .node "Atom" 5 [.leaf (tok .id x col), .node "AtomRest" 1 []],
        .node "PostTail" 1 []]],
    .node "MulTail" 1 []]

/-- `a - b - c`, com as colunas que têm em `int main() { return a - b - c; }`. -/
def subChain : ParseTree :=
  .node "Add" 0 [
    operand "a" 21,
    .node "AddTail" 0 [
      .node "AddOp" 1 [.leaf (tok .minus "-" 23)],
      operand "b" 25,
      .node "AddTail" 0 [
        .node "AddOp" 1 [.leaf (tok .minus "-" 27)],
        operand "c" 29,
        .node "AddTail" 1 []]]]

end ParseTree.Example
