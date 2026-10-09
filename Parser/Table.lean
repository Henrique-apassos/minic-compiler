import Parser.First

-- ══════════════════════════════════════════════
-- 1. TIPOS DA TABELA
-- ══════════════════════════════════════════════
-- Sem `Hashable` para `TokenKind`, a chave usa o índice do construtor.

def tokIdx (k : TokenKind) : Nat := k.ctorIdx

structure Conflict where
  nt    : String
  tok   : TokenKind
  prods : List Nat          -- ids (Production.id) das produções que disputam a célula
  deriving Repr

structure LL1Table where
  grammar  : Grammar
  analysis : Analysis
  cells    : Std.HashMap (String × Nat) Nat   -- (não-terminal, tokIdx) → Production.id

instance : Inhabited LL1Table := ⟨{ grammar := default, analysis := ⟨[], {}, {}⟩, cells := {} }⟩

-- ══════════════════════════════════════════════
-- 2. CONSTRUÇÃO
-- ══════════════════════════════════════════════

/-- PREDICT(p) = FIRST(rhs) ∪ (FOLLOW(lhs) se rhs é nulável) -/
def predict (a : Analysis) (p : Production) : TokSet :=
  let (f, nul) := a.firstOfSeq p.rhs
  if nul then TokSet.union f (a.followOf p.lhs) else f

/-- Monta a tabela; se alguma célula tiver mais de uma produção, devolve TODOS os conflitos. -/
def buildTable (g : Grammar) : Except (List Conflict) LL1Table :=
  let a := analyze g
  let preds := g.prods.toList.map fun p => (p, predict a p)
  let (cells, conflicts) := g.nonterminals.foldl (init := (({} : Std.HashMap (String × Nat) Nat), ([] : List Conflict)))
    fun acc n =>
      g.terminals.foldl (init := acc) fun (cells, cs) k =>
        let ps := preds.filterMap fun (p, s) =>
          if p.lhs == n && s.contains k then some p.id else none
        match ps with
        | []  => (cells, cs)
        | [i] => (cells.insert (n, tokIdx k) i, cs)
        | _   => (cells, cs ++ [{ nt := n, tok := k, prods := ps }])
  if conflicts.isEmpty then .ok { grammar := g, analysis := a, cells }
  else .error conflicts

-- ══════════════════════════════════════════════
-- 3. CONSULTAS
-- ══════════════════════════════════════════════

def LL1Table.lookup (t : LL1Table) (a : String) (k : TokenKind) : Option Production :=
  (t.cells.get? (a, tokIdx k)).bind (t.grammar.prods[·]?)

-- ══════════════════════════════════════════════
-- 4. TABELA DO MINIC
-- ══════════════════════════════════════════════

/-- Tabela do miniC. A gramática é LL(1); se um dia tiver conflito, `panic!` com os conflitos. -/
def minicTable : LL1Table :=
  match buildTable minicGrammar with
  | .ok t => t
  | .error cs =>
    panic! s!"minicGrammar não é LL(1): {reprStr cs}"
