# minic-compiler

Compilador para **Mini-C**, um subconjunto da linguagem C, escrito em **Lean 4**.

O projeto tem a **análise léxica (scanner)**, o **gerador de parser LL(1)** com seu motor, e a **AST** com a conversão da árvore de derivação. O executável lê um programa e imprime a AST. O scanner foi construído do zero sobre uma pequena biblioteca de autômatos: as regras léxicas são expressões regulares, convertidas em NFA pelo algoritmo de Thompson e depois em DFA pela construção de subconjuntos. Por fim, o DFA é executado com *maximal munch* sobre o código-fonte.

```
Regras (Regex × TokenKind) ──Thompson──▶ NFA combinado ──Subset construction──▶ DFA ──maximal munch──▶ Tokens
```

O parser segue o mesmo desenho: a gramática é escrita como dado, o gerador calcula nulável, FIRST e FOLLOW por ponto fixo e monta a tabela LL(1), e um motor genérico com pilha explícita lê os tokens e devolve a árvore de derivação.

```
Gramática (produções) ──ponto fixo──▶ nulável/FIRST/FOLLOW ──▶ tabela LL(1) ──motor com pilha──▶ Árvore de derivação
```

Por fim, a árvore de derivação é convertida na AST, que guarda só o significado do programa:

```
texto ──scan──▶ tokens ──parse──▶ árvore de derivação ──toProgram──▶ AST
```

## Requisitos

- [elan](https://github.com/leanprover/elan), que instala automaticamente a versão do Lean fixada em `lean-toolchain` (`leanprover/lean4:v4.34.0`)

## Como compilar e executar

```bash
lake build
```

```bash
lake exe minic-compiler programa.c
```

Sem arquivo, o executável usa o programa de exemplo de `Main.lean`. Ele imprime a AST, com toda operação binária entre parênteses para a associatividade ficar visível. Se houver erro de sintaxe, imprime `erro: linha:coluna: ...` e sai com código 1.

## Estrutura do projeto

```
.
├── Main.lean                  # Ponto de entrada: texto → AST, imprime a AST ou o erro
├── Scanner.lean               # Raiz da biblioteca Scanner
├── Scanner/
│   ├── Basic.lean             # Tipos de token, classes de caracteres e regras léxicas
│   └── Lexer.lean             # NFA combinado, DFA do scanner e o laço de varredura
├── Tests/                     # Testes (`lake test`): Harness, Syntax, Programs, Main e fixtures/
├── Parser.lean                # Raiz da biblioteca Parser
├── Parser/
│   ├── Tree.lean              # ParseTree: o contrato entre o motor e a conversão para AST
│   ├── Grammar.lean           # Sym, Production, Grammar e a gramática LL(1) do miniC
│   ├── First.lean             # Nulável, FIRST e FOLLOW por ponto fixo
│   ├── Table.lean             # Tabela LL(1) com detecção de conflitos
│   ├── Engine.lean            # Motor preditivo com pilha explícita
│   ├── Ast.lean               # Tipos da AST (MType, Expr, Stmt, FunDecl) e impressão
│   └── ToAst.lean             # Árvore de derivação → AST, e parseProgram (texto → AST)
├── docs/DECISOES.md           # Decisões do projeto e de onde vieram
├── Automata/
│   ├── Common.lean            # Tipos base (State, Symbol, Transition) e predicados
│   ├── NFA.lean               # Estrutura NFA com invariantes provadas + deltaNFA
│   ├── DFA.lean               # Estrutura DFA (determinismo e totalidade) + deltaDFA
│   ├── Thompson.lean          # AST de Regex e algoritmo de Thompson (Regex → NFA)
│   ├── Subset.lean            # Fecho-ε, move e construção de subconjuntos (NFA → DFA)
│   ├── Simulation.lean        # Execução/aceitação de NFA e DFA sobre formas de onda
│   └── SimulationTactics.lean # Macros de tática (portadas de Ltac do Coq)
├── lakefile.toml
└── .github/workflows/lean_action_ci.yml  # CI: lake build a cada push/PR
```

## O que foi feito

### 1. Biblioteca de autômatos (`Automata/`)

- **`NFA` e `DFA` verificados.** As estruturas carregam provas das suas invariantes: estados sem repetição, estado inicial pertencente a `Q`, transições válidas sobre o alfabeto e estados de aceitação contidos em `Q`. O `DFA` exige ainda alvo único por `(estado, símbolo)` e função de transição total.
- **Simulação** (`Simulation.lean`). Executa NFA e DFA sobre coleções de *waveforms* (sinais booleanos amostrados na borda de subida do `clk`) e define aceitação como proposições (`dfaAccepts` e `nfaAccepts`). A parte de waveforms e as táticas em `SimulationTactics.lean` são uma portabilidade de uma formalização anterior em Coq.
- **Algoritmo de Thompson** (`Thompson.lean`). Define a AST `Regex` (`epsilon`, `literal`, `concat`, `union`, `star`) e a converte num `RawNFA` com transições `ε`. IDs únicos de estados vêm de uma mônada de estado (`BuilderM`).
- **Construção de subconjuntos** (`Subset.lean`). Implementa o fecho-ε, `move` e o laço com *worklist* que gera um `RawDFA`. Conjuntos de estados ficam em forma canônica (lista ordenada sem duplicatas) para poderem ser comparados.

`RawNFA` e `RawDFA` são versões "sem provas" usadas durante a construção algorítmica. As estruturas `NFA` e `DFA` verificadas ainda não são produzidas a partir delas.

### 2. Scanner do Mini-C (`Scanner/`)

- **Tokens** (`Basic.lean`). `TokenKind` cobre:
  - palavras-chave: `int float bool str void if else while return true false and or`
  - identificadores e literais inteiros e de ponto flutuante
  - operadores: `+ - * / == != < <= > >= ! =`
  - pontuação: `( ) { } [ ] , ;`
  - `eof` e `error`

  Cada `Token` guarda tipo, lexema, linha e coluna.
- **Regras léxicas.** São uma lista ordenada de `(Regex, TokenKind)` montada com auxiliares: `regexFromString`, `regexPlus` e classes de dígitos e letras. A **ordem é a prioridade**: palavras-chave vêm antes de `id`, por isso `int` é `kwInt` e não identificador.
- **Lexer** (`Lexer.lean`):
  - Todas as regras viram um único **NFA combinado**, com um novo estado inicial ligado por `ε` ao início de cada regra.
  - O alfabeto é extraído das próprias regras.
  - A construção de subconjuntos gera o **`LexDFA`**, com tabelas `HashMap`. Cada estado de aceitação recebe o token da primeira regra que ele reconhece.
  - `longestMatch` implementa o **maximal munch**: avança o DFA o máximo possível e volta ao último estado de aceitação. Por isso `intx` vira `id` e `<=` vira `le`, não `lt` + `assign`.
  - `scan` ignora espaços em branco e comentários de linha (`//`) e conta linha e coluna. Um caractere não reconhecido gera um token `error` e a varredura continua; o último token é sempre `eof`.

### 3. Gerador de parser LL(1) (`Parser/`)

- **Gramática como dado** (`Grammar.lean`). A gramática do miniC, extraída do parser Rust de referência e reescrita para LL(1): laços viram caudas recursivas à direita com ε (`AddTail`, `MulTail`...) e prefixos comuns são fatorados (`ID IdStmt`, `ID AtomRest`). São **42 não-terminais e 85 produções**. A ordem das alternativas faz parte do contrato com a conversão para AST.
- **Nulável, FIRST e FOLLOW** (`First.lean`). Calculados por ponto fixo, com um combustível limitado que basta (sem `partial`).
- **Tabela LL(1)** (`Table.lean`). PREDICT(A → α) = FIRST(α), mais FOLLOW(A) se α é nulável. Se duas produções caem na mesma célula, a gramática é recusada com a lista de conflitos. A do miniC tem **0 conflitos** e 313 células.
- **Motor** (`Engine.lean`). Uma pilha de trabalho (símbolos e marcadores de "fechar nó") e uma pilha de valores. Não há retrocesso: cada passo olha só o topo e o token atual. Para no primeiro erro, com uma mensagem em português: `1:19: encontrei ';', esperava '='`.

- **Árvore de derivação** (`Tree.lean`). `leaf tok` guarda o token inteiro; `node nt alt kids` guarda o não-terminal, a alternativa usada (0 = primeira) e os filhos (ε = sem filhos).
- **Pontos de entrada**: `parseMiniC (toks : Array Token)` e `parseSource (src : String)`.

### 4. AST e conversão (`Parser/Ast.lean`, `Parser/ToAst.lean`)

- **Tipos da AST**: `MType` (com `array` para `T[]`), `Lit`, `BinOp`, `Expr Ty`, `Stmt Ty`, `FunDecl Ty` e `Program Ty`. O modelo é o `ast.rs` do exemplo em Rust, sem ponteiros. `Ty` é o tipo anotado em cada expressão: o parser usa `Unit`, e o verificador de tipos poderá usar `MType` sem reescrever a AST.
- **Conversão**: uma função por grupo de não-terminais (`toProgram`, `toFun`, `toType`, `toStmt`, `toExpr`), escolhendo pelo nome e pela alternativa. Uma árvore fora do formato vira `Except.error` ("árvore malformada em Atom.5") em vez de travar. Recursão estrutural, sem `partial`.
- **Associatividade**: as caudas (`AddTail`, `MulTail`...) pendem para a direita na árvore; um acumulador as dobra à esquerda, e `a - b - c` vira `(a - b) - c`. Uma função só (`foldTail`) serve para os cinco níveis binários, e outra (`foldIndex`) para `a[i][j]`.
- **De ponta a ponta**: `parseProgram (src : String) : Except String (Program Unit)`.

Exemplo: `lake exe minic-compiler` sobre o programa de `Main.lean` imprime

```
int fatorial(int n)
{
  if (n <= 1)
  {
    return 1;
  }
  float x = 3.140000;
  int[] v = [1, 2, 3];
  v[0] = (-v[1] * 2);
  return (n * fatorial(((n - 1) - 0)));
}
```

e um programa com erro imprime `erro: 1:25: encontrei ';', esperava identificador, '(', '[', ...`.

### Exemplo do scanner

Entrada:

```c
int fatorial(int n) {
  // comentário
  if (n <= 1) { return 1; }
  float x = 3.14;
  int intx = 42;
  return n * fatorial(n - 1);
}
a == b != c @
```

Saída (trecho):

```
1:1   TokenKind.kwInt     "int"
1:5   TokenKind.id        "fatorial"
1:13  TokenKind.lparen    "("
...
3:9   TokenKind.le        "<="
...
4:13  TokenKind.numFloat  "3.14"
5:7   TokenKind.id        "intx"
...
8:13  TokenKind.error     "@"
8:14  TokenKind.eof       ""
```

## Testes

```bash
lake test
```

Roda `Tests/Main.lean` (71 testes, 3 pendentes em 8 de outubro de 2026). Os casos vêm de `MiniC/tests/parser.rs` e `program.rs`, com os mesmos nomes; os fixtures `.minic` estão em `Tests/fixtures/`. Pendente = lacuna conhecida do compilador (hoje, literais de string): não falha a execução, mas se passar o teste falha pedindo para remover a marca. Detalhes em `docs/DECISOES.md` (#37 e #59).

## Limitações atuais e próximos passos

- `stringLit` existe em `TokenKind`, mas ainda não há regra léxica para literais de string.
- Comentários de bloco (`/* ... */`) não são tratados.
- `epsilonClosure`, `subsetLoop` e `scanLoop` são `partial`, ou seja, não têm prova de terminação.
- Não há prova formal de que o DFA gerado é equivalente ao NFA ou à regex. As estruturas verificadas `NFA`/`DFA` e o pipeline `Raw*` ainda não estão conectados.
- O motor de parser é `partial`; o ponto fixo de FIRST/FOLLOW não é.
- Próximas fases do compilador: análise semântica (tipos), interpretador e geração de código.

As decisões de projeto, com origem e o que ainda precisa ser confirmado, estão em [docs/DECISOES.md](docs/DECISOES.md).
