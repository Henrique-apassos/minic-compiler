import Automata.Thompson
import Automata.Subset
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

-- ══════════════════════════════════════════════
-- 2. ESTRUTURA DO TOKEN
-- ══════════════════════════════════════════════
structure Token where
  kind  : TokenKind
  lexeme  : String
  line : Nat
  column : Nat
  deriving Repr

-- ══════════════════════════════════════════════
-- 3. FUNÇÕES AUXILIARES DE REGEX
-- ══════════════════════════════════════════════
-- Transforma uma string literal (ex: "int") numa sequência concatenada de Regex
def regexFromString (s : String) : Regex :=
  let chars := s.toList.map (fun c => Regex.literal c.toString)
  match chars with
  | [] => Regex.epsilon
  | h :: t => t.foldl Regex.concat h

-- Auxiliar genérico para "um ou mais" (r+)
def regexPlus (r : Regex) : Regex :=
  Regex.concat r (Regex.star r)

-- ══════════════════════════════════════════════
-- 4. ALFABETO BASE E CLASSES DE CARACTERES
-- ══════════════════════════════════════════════

def digitRegex : Regex :=
  List.foldl Regex.union (Regex.literal "0")
    (["1", "2", "3", "4", "5", "6", "7", "8", "9"].map Regex.literal)

def lowerRegex : Regex :=
  List.foldl Regex.union (Regex.literal "a")
    (["b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
      "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"].map Regex.literal)

def upperRegex : Regex :=
  List.foldl Regex.union (Regex.literal "A")
    (["B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
      "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z"].map Regex.literal)

def alphaRegex : Regex :=
  Regex.union lowerRegex (Regex.union upperRegex (Regex.literal "_"))

def intRegex : Regex := regexPlus digitRegex
def floatRegex : Regex := Regex.concat intRegex (Regex.concat (Regex.literal ".") intRegex)
def idRegex : Regex := Regex.concat alphaRegex (Regex.star (Regex.union alphaRegex digitRegex))
