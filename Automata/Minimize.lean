import Automata.Common
import Std.Data.HashMap

-- ══════════════════════════════════════════════
-- MINIMIZAÇÃO DE DFA POR REFINAMENTO DE PARTIÇÕES
-- ══════════════════════════════════════════════
-- Dois estados são equivalentes quando têm o mesmo rótulo e, para cada símbolo, vão
-- para classes equivalentes (ou ambos não têm transição). Começa com a partição por
-- rótulo e refina até estabilizar (Moore; o resultado é o mesmo de Hopcroft, que só
-- muda a ordem de refinamento). O DFA pode ser parcial: transição ausente conta como
-- um destino "morto" próprio.

/-- Numera as assinaturas na ordem em que aparecem (0, 1, 2, ...). -/
private def renumber (sigs : Array (Nat × List Nat)) : Array Nat :=
  let (res, _) := sigs.foldl (init := (#[], ({} : Std.HashMap (Nat × List Nat) Nat)))
    fun (res, ids) sig =>
      match ids[sig]? with
      | some i => (res.push i, ids)
      | none => (res.push ids.size, ids.insert sig ids.size)
  res

/-- Quantidade de classes de uma partição já renumerada (0..k-1). -/
private def classCount (cls : Array Nat) : Nat := cls.foldl max 0 + 1

private def refine (n : Nat) (alphabet : List Symbol)
    (trans : Std.HashMap (State × Symbol) State) (cls : Array Nat) : Array Nat :=
  renumber ((Array.range n).map fun s =>
    (cls[s]!, alphabet.map fun c =>
      match trans[(s, c)]? with
      | some t => cls[t]! + 1
      | none => 0))

/-- Classe de cada estado `0..n-1`. `label s` separa estados de rótulos diferentes
    desde o início (por exemplo, o token que o estado aceita, ou 0 se não aceita).
    A partição só refina, então parar quando o número de classes não cresce basta;
    `n + 1` rodadas bastam porque cada rodada que muda algo cria uma classe nova. -/
def minimizeClasses (n : Nat) (alphabet : List Symbol)
    (trans : Std.HashMap (State × Symbol) State) (label : State → Nat) : Array Nat :=
  go (n + 1) (renumber ((Array.range n).map fun s => (label s, [])))
where
  go : Nat → Array Nat → Array Nat
    | 0, cls => cls
    | f + 1, cls =>
      let next := refine n alphabet trans cls
      if classCount next == classCount cls then cls else go f next
