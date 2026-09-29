-- ══════════════════════════════════════════════
-- 1. TIPOS DE TOKENS (CATEGORIAS LÉXICAS)
-- ══════════════════════════════════════════════

inductive TokenKind where
  -- Tipos base e Palavras-chave
  | kwInt | kwFloat | kwBool | kwStr | kwVoid
  | kwIf | kwElse | kwWhile | kwReturn
  | kwTrue | kwFalse
  | kwAnd | kwOr

  -- Literais e Identificadores
  | id          -- Nomes de variáveis/funções (ex: "x", "factorial")
  | numInt      -- Inteiros (ex: "42")
  | numFloat    -- Ponto flutuante (ex: "3.14")
  | stringLit   -- Textos (ex: "hello")

  -- Operadores Aritiméticos
  | plus | minus | times | div

  -- Operadores relacionais  e lógicos
  | eq      --"=="
  | neq     --"!="
  | lt      --"<"
  | le      --"<="
  | gt      --">"
  | ge      --">="
  | not     --"!"

  -- Pontuação e atribuição
  | assing --"="
  | lparen | rparen --"(" e ")"
  | lbrace | rbrace --"{" e "}"
  | lbracket | rbracket --"[" e "]"
  | comma --","
  | semi --";"

  -- Sistema
  | eof
  | error

  deriving Repr, BEq
