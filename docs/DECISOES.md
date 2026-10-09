# Decisões do projeto miniC

Registro das decisões que moldam o compilador. Cada uma diz **de onde veio** e se ainda **precisa ser confirmada**.

Legenda de origem:
- **Professor**: pedido do professor (relatado no grupo).
- **Grupo**: decidido no chat do grupo.
- **Proposta**: sugestão do roteiro ou desta implementação. O grupo pode trocar.
- **Implementação**: escolha técnica feita ao escrever o código (branches `dev/parser-generator` e `dev/ast`).

Atualizado em 6 de outubro de 2026.

## Escopo e organização

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 1 | O compilador é escrito em **Lean 4** (Lake). | Professor | Fechada |
| 2 | Primeiro implementar a linguagem (scanner, parser); semântica (tipos, interpretador) depois da primeira entrega. | Professor / Grupo | Fechada |
| 3 | A linguagem é o **miniC** do repositório de referência em Rust. Linguagem, AST e testes vêm de lá; a estratégia de parser não. | Grupo | Fechada |
| 4 | O scanner é construído por **regex → NFA (Thompson) → DFA (subconjuntos)**, com maximal munch. | Grupo (votação) | Fechada, implementada |
| 58 | A construção do DFA do scanner (`buildLexDFA`) leva **cerca de 4 minutos** e é refeita a cada execução do compilador. A tabela LL(1) e a conversão levam milissegundos. | Medição | Resolvida: transições e estados indexados em `HashMap`, ~2 s (PR #3, na `main`) |
| 5 | O parser é um **gerador LL(1) dirigido por tabela**: a gramática é dado, o gerador calcula FIRST/FOLLOW e a tabela, um motor genérico com pilha a executa. Mesmo desenho do scanner. | Professor | Fechada: é um gerador mesmo |
| 6 | Reserva: se o tempo apertar, um parser recursivo à mão sobre a mesma gramática garante "algo funcional". | Proposta | Descartada: o professor quer o gerador |
| 7 | Divisão: Henrique e Felipe no scanner; Caio e Daniel no parser. | Grupo | **Confirmar** (deduzida de uma mensagem) |
| 8 | Dentro do parser: **Caio** faz o gerador e o motor (gramática, FIRST/FOLLOW, tabela, motor, `ParseTree`); **Daniel** faz AST, conversão árvore → AST, testes de ponta a ponta e o `Main.lean`. | Proposta | Fechada |
| 9 | Minimização de Hopcroft: opcional, fora da primeira entrega. | Grupo | Fechada |
| 10 | Verificador de tipos, interpretador e codegen: sem dono, depois da primeira entrega. | Grupo | Aberta |

## A linguagem

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 11 | **Ponteiros** (`&e`, `*e`, `T*`) ficam fora da primeira versão. O scanner não tem `&`, e `*` unário colide com multiplicação. | Proposta / Caio | Fechada |
| 12 | O programa **termina obrigatoriamente em `eof`**: lixo depois da última função é erro com posição. O Rust para em silêncio no primeiro lixo. | Proposta / Caio | Fechada (`Program := FunList eof`) |
| 13 | **`;` obrigatório** depois de comandos simples (declaração, atribuição, chamada, `return`). | Proposta (segue o código Rust) / Caio | Fechada |
| 14 | **Precedência do `!`** abaixo da comparação: `!a == b` é `!(a == b)`. Segue o código Rust (de onde vêm os testes), não o guia da linguagem nem o C. | Proposta / Caio | Fechada — **avisar o grupo**, porque difere do C |
| 15 | `if` e `while` exigem bloco `{ }`; a condição não precisa de parênteses (parênteses são só uma expressão entre parênteses). | Exemplo Rust | Adotada |
| 16 | Corpo de função pode ser qualquer comando, não só bloco. | Exemplo Rust | Adotada |
| 17 | Tipos de array `T[]` com **qualquer número de dimensões** (o Rust limita a 2). | Proposta | Adotada (`Dims`) |
| 18 | Toda declaração tem valor inicial: `int x = 1;`. `int x;` é erro. | Exemplo Rust | Adotada |
| 19 | Expressão solta não é comando: `x + 1;` é erro. Só chamada (`f(x);`) e atribuição (`x = 1;`, `a[i] = 1;`) começam com identificador. | Exemplo Rust | Adotada |
| 20 | Literais de string fazem parte da linguagem, mas o scanner **ainda não tem a regra de `stringLit`**. A gramática já aceita o token. | Grupo | **Pendente** (Henrique e Felipe) |

## Gramática

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 21 | A gramática é a do Rust reescrita para LL(1): laços viram **caudas recursivas à direita com ε** (`AddTail`, `MulTail`...) e prefixos comuns são **fatorados** (`ID IdStmt`, `ID AtomRest`). | Proposta | Implementada |
| 22 | Tamanho: **42 não-terminais, 85 produções, 0 conflitos, 313 células na tabela** (verificado pelo próprio gerador). | Implementação | Verificada |
| 23 | Um nível de não-terminal por nível de precedência: `Or` < `And` < `Not` < `Rel` < `Add` < `Mul` < `Unary` < `Postfix`/`Atom`. Todos os binários são associativos à esquerda **na AST** (a árvore de derivação pende para a direita; a conversão do Daniel corrige). | Proposta | Implementada |
| 24 | A **ordem das alternativas** em `Parser/Grammar.lean` é parte do contrato: `alt = 5` em `Atom` significa "identificador seguido de `AtomRest`". Mudar a ordem quebra a conversão para AST. | Implementação | Fechada |

## O contrato entre gerador e AST (`Parser/Tree.lean`)

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 25 | A saída do motor é uma **árvore de derivação** `ParseTree`, não a AST. A AST é responsabilidade da conversão (Daniel). | Proposta | Implementada |
| 26 | `leaf tok`: guarda o **`Token` inteiro** (com linha e coluna) para mensagens de erro nas fases seguintes. | Proposta | Implementada |
| 27 | `node nt alt kids`: não-terminal **por nome (`String`)**, igual à gramática; `alt` = **índice da alternativa dentro do não-terminal** (0 = primeira); ε = `kids` vazio. | Proposta | Fechada (Daniel de acordo) |
| 28 | Sem árvore de exemplo nem funções de visualização no `Tree.lean`: só o tipo. O Daniel pode imprimir a árvore com o `Repr` derivado. | Caio (enxugar ao necessário) | Fechada |

## O gerador e o motor

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 29 | Nulável, FIRST e FOLLOW por **ponto fixo** (repetir até nada mudar), como o `epsilonClosure` do scanner. | Proposta | Implementada |
| 30 | O ponto fixo usa **combustível com limite provado suficiente** (não-terminais × (terminais + 1) + 1), em vez de `partial`. | Implementação | Implementada |
| 31 | `FOLLOW(início)` começa com `eof`. No miniC o próprio `Program` consome o `eof`. | Implementação | Implementada |
| 32 | A tabela recusa a gramática se houver **qualquer conflito** e lista todos (não-terminal, token, produções em disputa). | Proposta | Implementada |
| 33 | A tabela é indexada por (nome do não-terminal, índice do construtor do token — `TokenKind.ctorIdx`), sem alterar o `TokenKind` do scanner. | Implementação | Implementada |
| 34 | O motor usa **pilha explícita** (itens "símbolo" e "fechar nó") e não recursão, para ser fiel ao algoritmo dirigido por tabela. O laço é `partial` (como o `scanLoop`): termina porque toda gramática sem conflitos aqui consome token ou desempilha. | Implementação | Implementada |
| 35 | Erro: **para no primeiro erro** (sem recuperação). A mensagem é **em português**, com linha:coluna, o que foi encontrado e o que era esperado (`1:19: encontrei ';', esperava '='`). Token `error` do scanner vira "caractere não reconhecido". | Caio | Implementada |
| 36 | Pontos de entrada para o Daniel: `parseMiniC (toks : Array Token)` e `parseSource (src : String)`. | Implementação | Implementada |
| 42 | A lista de esperados de um erro é exatamente a linha da tabela. Num erro dentro de uma cauda nulável (ex.: `return 1 }`), ela fica longa (FIRST ∪ FOLLOW). Mantido para o motor seguir só a tabela. | Implementação | Pode melhorar |

## A AST e a conversão (`Parser/Ast.lean`, `Parser/ToAst.lean`)

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 46 | A AST segue o `ast.rs` do exemplo Rust, **sem ponteiros**: `MType`, `Lit`, `BinOp`, `Expr Ty`, `Stmt Ty`, `FunDecl Ty`, `Program Ty = List (FunDecl Ty)`. | Proposta (roteiro) | Implementada |
| 47 | Cada expressão carrega um **tipo anotado `Ty`**. O parser usa `Unit`; o verificador de tipos poderá usar `MType` sem reescrever a AST. | Proposta (roteiro) | Implementada |
| 48 | A conversão devolve **`Except String`**: uma árvore fora do formato (bug no motor) vira erro `árvore malformada em NT.alt` em vez de travar. | Proposta (roteiro) | Implementada |
| 49 | **Associatividade à esquerda por acumulador**: as caudas da árvore pendem para a direita, e `foldTail` as dobra à esquerda. Uma função só para os cinco níveis binários (`Or`, `And`, `Rel`, `Add`, `Mul`): o operador vem do token, direto (`and`, `or`) ou dentro de `RelOp`/`AddOp`/`MulOp`. `PostTail` e `Indices` têm o mesmo formato e usam a mesma `foldIndex`. | Implementação | Implementada |
| 50 | Parênteses somem na AST. `-5` é `neg (lit 5)`, não um literal negativo. Comando `x = e;` e `a[i] = e;` viram `assign` com o alvo como expressão (`var` ou `index`). | Implementação | Implementada |
| 51 | Números: inteiro pelo lexema (`toNat?`); real montado exatamente a partir de `dígitos.dígitos` com `Float.ofScientific` (Lean não tem `String.toFloat`). Texto: aspas retiradas, se vierem no lexema. | Implementação | Implementada |
| 52 | A conversão usa **recursão estrutural** (o Lean prova sozinho que termina): sem `partial`. | Implementação | Implementada |
| 53 | Ponto de entrada de ponta a ponta: `parseProgram (src : String) : Except String (Program Unit)`. O erro de sintaxe já sai como a mensagem em português com `linha:coluna`. | Implementação | Implementada |
| 54 | O `Main.lean` lê o arquivo passado como argumento (ou usa um exemplo), **imprime a AST** e, em erro, imprime `erro: ...` no stderr e sai com código 1. A listagem de tokens do `Main` original saiu. | Proposta (roteiro, passo F) | Implementada — **avisar o Henrique** |
| 55 | Impressão da AST com **toda operação binária entre parênteses** (`((a - b) - c)`), para a associatividade ficar visível. | Implementação | Implementada |

## Em aberto

- Confirmar a divisão scanner × parser no grupo (7).
- Avisar o grupo da precedência do `!` (14).
- Regra de `stringLit` no scanner (20).
- Avisar o Henrique da troca do `Main.lean` (54).
- Definir quem faz tipos, interpretador e codegen (10).
