import Parser.First

-- ══════════════════════════════════════════════
-- 1. TIPOS DA TABELA LR(1)
-- ══════════════════════════════════════════════
-- Sem `Hashable` para `TokenKind`, as chaves usam o índice do construtor.
-- Conjuntos de lookahead são máscaras de bits (`Nat`): o bit `tokIdx k` diz se `k` está no conjunto.

def tokIdx (k : TokenKind) : Nat := k.ctorIdx

inductive Action where
  | shift  (s : Nat)        -- empilha o token e vai para o estado `s`
  | reduce (p : Nat)        -- reduz pela produção `p` (Production.id)
  | accept
  deriving Repr, BEq, Inhabited

structure Conflict where
  state   : Nat
  tok     : TokenKind
  actions : List Action     -- ações que disputam a célula ACTION[state, tok]
  deriving Repr

inductive BuildError where
  | conflicts     (cs : List Conflict)
  | tooManyStates (n : Nat)
  deriving Repr

structure LR1Table where
  grammar : Grammar
  states  : Nat
  action  : Std.HashMap (Nat × Nat) Action      -- (estado, tokIdx) → ação
  goto    : Std.HashMap (Nat × String) Nat      -- (estado, não-terminal) → estado

instance : Inhabited LR1Table := ⟨{ grammar := default, states := 0, action := {}, goto := {} }⟩

-- ══════════════════════════════════════════════
-- 2. ITENS LR(1)
-- ══════════════════════════════════════════════
-- Um item é `(produção, ponto, lookaheads)`: `A → α • β, L`. Itens com o mesmo núcleo
-- `(produção, ponto)` têm os lookaheads unidos numa máscara só; um estado é então
-- um mapa núcleo → máscara, e dois estados são iguais se os mapas forem iguais.
-- A produção `g.prods.size` é a aumentada, `S' → S`, que só existe aqui dentro.

abbrev LRItem := Nat × Nat × Nat

private def tokMask (k : TokenKind) : Nat := 1 <<< tokIdx k

private def maskOf (s : TokSet) : Nat := s.foldl (fun m k => m ||| tokMask k) 0

/-- O que o gerador precisa, pré-calculado a partir da gramática. -/
private structure Ctx where
  g        : Grammar
  rhs      : Array (Array Sym)                 -- inclui a aumentada no fim
  prodsOf  : Std.HashMap String (List Nat)     -- produções de cada não-terminal
  suffix   : Array (Array (Nat × Bool))        -- FIRST e nulável de `rhs[p][d:]`, por `p` e `d`
  maxItems : Nat                               -- quantidade de núcleos, para o combustível

private def mkCtx (g : Grammar) : Ctx :=
  let a := analyze g
  let rhs := g.prods.map (·.rhs.toArray) |>.push #[.nt g.start]
  let prodsOf := g.prods.foldl (init := ({} : Std.HashMap String (List Nat)))
    fun m p => m.insert p.lhs (m.getD p.lhs [] ++ [p.id])
  let suffix := rhs.map fun r =>
    (List.range (r.size + 1)).toArray.map fun d =>
      let (f, nul) := a.firstOfSeq (r.toList.drop d)
      (maskOf f, nul)
  let maxItems := rhs.foldl (fun n r => n + r.size + 1) 0
  { g, rhs, prodsOf, suffix, maxItems }

private def Ctx.symAt (cx : Ctx) (p d : Nat) : Option Sym :=
  (cx.rhs[p]?.getD #[])[d]?

-- ══════════════════════════════════════════════
-- 3. FECHO
-- ══════════════════════════════════════════════
-- Para `A → α • B β, L`, cada `B → • γ` entra com lookahead FIRST(β), mais `L` se β é nulável.
-- Combustível: cada item da lista de trabalho acrescentou um núcleo ou ao menos um bit de
-- lookahead, então núcleos · (terminais + 1) + |kernel| + 1 passos bastam.

private def closure (cx : Ctx) (kernel : List LRItem) : Array LRItem :=
  let init := kernel.foldl (init := ({} : Std.HashMap (Nat × Nat) Nat))
    fun m (p, d, la) => m.insert (p, d) (m.getD (p, d) 0 ||| la)
  let fuel := cx.maxItems * (cx.g.terminals.length + 1) + kernel.length + 1
  let m := go fuel init kernel
  (m.toArray.map fun ((p, d), la) => (p, d, la)).qsort
    fun (p, d, _) (q, e, _) => p < q || (p == q && d < e)
where
  go : Nat → Std.HashMap (Nat × Nat) Nat → List LRItem → Std.HashMap (Nat × Nat) Nat
    | 0, m, _ | _, m, [] => m
    | f + 1, m, (p, d, la) :: rest =>
      match cx.symAt p d with
      | some (.nt b) =>
        let (fm, nul) := (cx.suffix[p]?.getD #[])[d + 1]?.getD (0, true)
        let la' := if nul then fm ||| la else fm
        let (m, new) := (cx.prodsOf.getD b []).foldl (init := (m, ([] : List LRItem)))
          fun (m, new) q =>
            let old := m.getD (q, 0) 0
            if m.contains (q, 0) && (old ||| la') == old then (m, new)
            else (m.insert (q, 0) (old ||| la'), (q, 0, old ||| la') :: new)
        go f m (new ++ rest)
      | _ => go f m rest

-- ══════════════════════════════════════════════
-- 4. AUTÔMATO LR(1) CANÔNICO E TABELAS ACTION/GOTO
-- ══════════════════════════════════════════════
-- Os estados são identificados pelo kernel (itens que não vêm do fecho), ordenado.
-- `explore` processa os estados na ordem em que são descobertos.

private structure Build where
  kernels : Array (List LRItem)
  index   : Std.HashMap (List LRItem) Nat
  action  : Std.HashMap (Nat × Nat) (List Action)
  goto    : Std.HashMap (Nat × String) Nat

private def addAction (b : Build) (s : Nat) (k : Nat) (act : Action) : Build :=
  let old := b.action.getD (s, k) []
  if old.contains act then b else { b with action := b.action.insert (s, k) (old ++ [act]) }

/-- Estado com esse kernel; cria um novo se ainda não existe. -/
private def stateOf (b : Build) (kernel : List LRItem) : Build × Nat :=
  match b.index.get? kernel with
  | some j => (b, j)
  | none =>
    let j := b.kernels.size
    ({ b with kernels := b.kernels.push kernel, index := b.index.insert kernel j }, j)

/-- Reduções (e o aceite) dos itens completos do estado `s`. -/
private def reductions (cx : Ctx) (s : Nat) (items : Array LRItem) (b : Build) : Build :=
  let aug := cx.g.prods.size
  items.foldl (init := b) fun b (p, d, la) =>
    if d < (cx.rhs[p]?.getD #[]).size then b
    else cx.g.terminals.foldl (init := b) fun b k =>
      if la &&& tokMask k == 0 then b
      else addAction b s (tokIdx k) (if p == aug then .accept else .reduce p)

/-- Transições do estado `s`: agrupa os itens pelo símbolo depois do ponto e avança o ponto. -/
private def transitions (cx : Ctx) (s : Nat) (items : Array LRItem) (b : Build) : Build :=
  let groups := items.foldl (init := ([] : List (Sym × List LRItem))) fun gs (p, d, la) =>
    match cx.symAt p d with
    | none => gs
    | some x =>
      if gs.any (·.1 == x) then gs.map fun (y, its) => if y == x then (y, its ++ [(p, d + 1, la)]) else (y, its)
      else gs ++ [(x, [(p, d + 1, la)])]
  groups.foldl (init := b) fun b (x, kernel) =>
    let (b, j) := stateOf b kernel
    match x with
    | .t k  => addAction b s (tokIdx k) (.shift j)
    | .nt n => { b with goto := b.goto.insert (s, n) j }

private def explore (cx : Ctx) : Nat → Nat → Build → Build × Bool
  | 0, i, b => (b, i ≥ b.kernels.size)
  | f + 1, i, b =>
    match b.kernels[i]? with
    | none => (b, true)
    | some kernel =>
      let items := closure cx kernel
      explore cx f (i + 1) (transitions cx i items (reductions cx i items b))

/-- Limite de estados. O do miniC fica bem abaixo; ver o teste em `Tests.lean`. -/
def maxStates : Nat := 100000

/-- Monta o autômato e as tabelas; se alguma célula de ACTION tiver mais de uma ação
    (shift/reduce ou reduce/reduce), devolve TODOS os conflitos. -/
def buildTable (g : Grammar) : Except BuildError LR1Table :=
  let cx := mkCtx g
  let start : List LRItem := [(g.prods.size, 0, tokMask .eof)]
  let b0 : Build := { kernels := #[start], index := ({} : Std.HashMap _ _).insert start 0,
                      action := {}, goto := {} }
  let (b, done) := explore cx maxStates 0 b0
  if !done then .error (.tooManyStates b.kernels.size) else
  let cells := b.action.toList
  let conflicts := (cells.filterMap fun ((s, ki), acts) =>
      if acts.length ≤ 1 then none
      else (g.terminals.find? (tokIdx · == ki)).map fun k => { state := s, tok := k, actions := acts })
    |>.toArray.qsort (fun c d => c.state < d.state || (c.state == d.state && tokIdx c.tok < tokIdx d.tok))
    |>.toList
  if !conflicts.isEmpty then .error (.conflicts conflicts) else
  let action := cells.foldl (init := ({} : Std.HashMap (Nat × Nat) Action))
    fun m (key, acts) => match acts with | [a] => m.insert key a | _ => m
  .ok { grammar := g, states := b.kernels.size, action, goto := b.goto }

-- ══════════════════════════════════════════════
-- 5. CONSULTAS
-- ══════════════════════════════════════════════

def LR1Table.actionAt (t : LR1Table) (s : Nat) (k : TokenKind) : Option Action :=
  t.action.get? (s, tokIdx k)

def LR1Table.gotoAt (t : LR1Table) (s : Nat) (n : String) : Option Nat :=
  t.goto.get? (s, n)

/-- Tokens com ação no estado `s`, na ordem de `g.terminals`. No LR(1) canônico o erro é
    detectado no estado do último shift, então esta é exatamente a lista do que podia vir. -/
def LR1Table.expected (t : LR1Table) (s : Nat) : List TokenKind :=
  t.grammar.terminals.filter fun k => t.action.contains (s, tokIdx k)

/-- Quantidade de células preenchidas em ACTION e GOTO. -/
def LR1Table.size (t : LR1Table) : Nat × Nat := (t.action.size, t.goto.size)

-- ══════════════════════════════════════════════
-- 6. TABELA DO MINIC
-- ══════════════════════════════════════════════

/-- Tabela do miniC. A gramática é LR(1); se um dia tiver conflito, `panic!` com os conflitos. -/
def minicTable : LR1Table :=
  match buildTable minicGrammar with
  | .ok t => t
  | .error e => panic! s!"minicGrammar não é LR(1): {reprStr e}"
