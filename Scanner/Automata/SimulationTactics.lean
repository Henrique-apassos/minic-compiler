-- ─────────────────────────────────────────────
-- SimulationTactics.lean
-- Macros de tática equivalentes às Ltac do Coq.
-- ─────────────────────────────────────────────

import Automata.Common

-- Coq: prove_wf_not_empty  →  simpl; lia
-- Lean: `decide` ou `omega` resolvem metas de desigualdade em listas concretas.
macro "prove_wf_not_empty" : tactic =>
  `(tactic| first | decide | omega |
            fail "Cannot prove the Waveform Collection isn't empty")

-- Coq: prove_str_waveform  →  simpl; repeat split; reflexivity
-- Lean: `simp` + `decide` provam igualdades de comprimento em listas concretas.
macro "prove_str_waveform" : tactic =>
  `(tactic| first | (simp; done) | decide |
            fail "Cannot prove the Waveform Collection is a structured table")
