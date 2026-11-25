import Automata.NFA
import Automata.DFA
import Automata.Thompson
import Automata.Subset
import Automata.Simulation

-- Exemplos executáveis dos autômatos (NFA, DFA, Thompson, subconjuntos, simulação).
-- Fora de `defaultTargets` de propósito: os `#eval` imprimem a cada compilação
-- do módulo e poluiriam o `lake build` do `minic-compiler`.
--
-- Rodar (sempre imprime):        lake lean Exemplos/Automata.lean
-- Rodar via build (usa cache):   lake build Exemplos

-- NFA
#eval deltaNFA [((0, "a"), 1), ((1, "b"), 2)] 0 "a"  -- [1]
#eval deltaNFA [((0, "ε"), 1), ((1, "b"), 2)] 0 "x"  -- [1]

-- DFA
#eval deltaDFA [((0, "a"), 1), ((1, "b"), 2)] 0 "a"  -- 1
#eval deltaDFA [((0, "a"), 1), ((1, "b"), 2)] 1 "b"  -- 2
#eval deltaDFA [((0, "a"), 1), ((1, "b"), 2)] 0 "b"  -- 0 (sem transição → estado atual)

-- Thompson
#eval regexToRawNFA (Regex.literal "a")
#eval regexToRawNFA (Regex.concat (Regex.literal "a") (Regex.literal "b"))
#eval regexToRawNFA (Regex.union (Regex.literal "a") (Regex.literal "b"))
#eval regexToRawNFA (Regex.star (Regex.literal "a"))

-- a(b|c)*
def testeRegexABC : Regex :=
  Regex.concat
    (Regex.literal "a")
    (Regex.star
      (Regex.union
        (Regex.literal "b")
        (Regex.literal "c")
      )
    )

#eval regexToRawNFA testeRegexABC

-- Subconjuntos: a(b|c)* → DFA com alfabeto explícito
#eval constructDFA (regexToRawNFA testeRegexABC) ["a", "b", "c"]

-- Simulação
#eval recordPosedgeClock [false, true, false, true, false, true] 0  -- [1, 3, 5]
#eval dropHeads [("A", [true, false]), ("B", [false, true])]       -- [("A", [false]), ("B", [true])]
