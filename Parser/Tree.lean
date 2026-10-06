import Scanner.Basic

-- ══════════════════════════════════════════════
-- ÁRVORE DE DERIVAÇÃO (saída do motor, entrada da conversão para AST)
-- ══════════════════════════════════════════════
-- * `leaf tok`         : um terminal lido, com o token inteiro (linha e coluna).
-- * `node nt alt kids` : o não-terminal `nt`, expandido pela alternativa `alt`
--                        (0 = primeira alternativa de `nt` em `Parser/Grammar.lean`).
--                        Uma produção ε aparece como `kids = []`.

inductive ParseTree where
  | leaf (tok : Token)
  | node (nt : String) (alt : Nat) (kids : List ParseTree)
  deriving Repr

instance : Inhabited ParseTree := ⟨.node "" 0 []⟩
