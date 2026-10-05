# Decisões do projeto miniC

Registro das decisões que moldam o compilador. Cada uma diz **de onde veio** e se ainda **precisa ser confirmada**.

Legenda de origem:
- **Professor**: pedido do professor (relatado no grupo).
- **Grupo**: decidido no chat do grupo.
- **Proposta**: sugestão do roteiro ou desta implementação. O grupo pode trocar.
- **Implementação**: escolha técnica feita ao escrever o código da branch `dev/parser-generator`.

Atualizado em 5 de outubro de 2026.

## Escopo e organização

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 1 | O compilador é escrito em **Lean 4** (Lake). | Professor | Fechada |
| 2 | Primeiro implementar a linguagem (scanner, parser); semântica (tipos, interpretador) depois da primeira entrega. | Professor / Grupo | Fechada |
| 3 | A linguagem é o **miniC** do repositório de referência em Rust. Linguagem, AST e testes vêm de lá; a estratégia de parser não. | Grupo | Fechada |
| 4 | O scanner é construído por **regex → NFA (Thompson) → DFA (subconjuntos)**, com maximal munch. | Grupo (votação) | Fechada, implementada |
| 5 | O parser é um **gerador LL(1) dirigido por tabela**: a gramática é dado, o gerador calcula FIRST/FOLLOW e a tabela, um motor genérico com pilha a executa. Mesmo desenho do scanner. | Professor | **Confirmar com o professor** que é isso que ele espera |
| 6 | Reserva: se o tempo apertar, um parser recursivo à mão sobre a mesma gramática garante "algo funcional". | Proposta | Não foi necessário até agora |
| 7 | Divisão: Henrique e Felipe no scanner; Caio e Daniel no parser. | Grupo | **Confirmar** (deduzida de uma mensagem) |
| 8 | Dentro do parser: **Caio** faz o gerador e o motor (gramática, FIRST/FOLLOW, tabela, motor, `ParseTree`); **Daniel** faz AST, conversão árvore → AST, testes de ponta a ponta e o `Main.lean`. | Proposta | **Confirmar com o Daniel** |
| 9 | Minimização de Hopcroft: opcional, fora da primeira entrega. | Grupo | Fechada |
| 10 | Verificador de tipos, interpretador e codegen: sem dono, depois da primeira entrega. | Grupo | Aberta |

## A linguagem

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 11 | **Ponteiros** (`&e`, `*e`, `T*`) ficam fora da primeira versão. O scanner não tem `&`, e `*` unário colide com multiplicação. | Proposta | Adotada na gramática |
| 12 | O programa **termina obrigatoriamente em `eof`**: lixo depois da última função é erro com posição. O Rust para em silêncio no primeiro lixo. | Proposta | Adotada (`Program := FunList eof`) |
| 13 | **`;` obrigatório** depois de comandos simples (declaração, atribuição, chamada, `return`). | Proposta (segue o código Rust) | Adotada |
| 14 | **Precedência do `!`** abaixo da comparação: `!a == b` é `!(a == b)`. Segue o código Rust, não o guia da linguagem. | Proposta | Adotada |
| 15 | `if` e `while` exigem bloco `{ }`; a condição não precisa de parênteses (parênteses são só uma expressão entre parênteses). | Exemplo Rust | Adotada |
| 16 | Corpo de função pode ser qualquer comando, não só bloco. | Exemplo Rust | Adotada |
| 17 | Tipos de array `T[]` com **qualquer número de dimensões** (o Rust limita a 2). | Proposta | Adotada (`Dims`) |
| 18 | Toda declaração tem valor inicial: `int x = 1;`. `int x;` é erro. | Exemplo Rust | Adotada |
| 19 | Expressão solta não é comando: `x + 1;` é erro. Só chamada (`f(x);`) e atribuição (`x = 1;`, `a[i] = 1;`) começam com identificador. | Exemplo Rust | Adotada |
| 20 | Literais de string fazem parte da linguagem, mas o scanner **ainda não tem a regra de `stringLit`**. A gramática já aceita o token; os testes evitam strings até a regra existir. | Grupo | **Pendente** (Henrique e Felipe) |

## Gramática

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 21 | A gramática é a do Rust reescrita para LL(1): laços viram **caudas recursivas à direita com ε** (`AddTail`, `MulTail`...) e prefixos comuns são **fatorados** (`ID IdStmt`, `ID AtomRest`). | Proposta | Implementada |
| 22 | Tamanho: **42 não-terminais, 85 produções, 0 conflitos, 313 células na tabela** (verificado pelo próprio gerador, ver testes). | Implementação | Verificada |
| 23 | Um nível de não-terminal por nível de precedência: `Or` < `And` < `Not` < `Rel` < `Add` < `Mul` < `Unary` < `Postfix`/`Atom`. Todos os binários são associativos à esquerda **na AST** (a árvore de derivação pende para a direita; a conversão do Daniel corrige). | Proposta | Implementada |
| 24 | A **ordem das alternativas** em `Parser/Grammar.lean` é parte do contrato: `alt = 5` em `Atom` significa "identificador seguido de `AtomRest`". Mudar a ordem quebra a conversão para AST. | Implementação | Fechada |

## O contrato entre gerador e AST (`Parser/Tree.lean`)

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 25 | A saída do motor é uma **árvore de derivação** `ParseTree`, não a AST. A AST é responsabilidade da conversão (Daniel). | Proposta | Implementada |
| 26 | `leaf tok`: guarda o **`Token` inteiro** (com linha e coluna) para mensagens de erro nas fases seguintes. | Proposta | Implementada |
| 27 | `node nt alt kids`: não-terminal **por nome (`String`)**, igual à gramática; `alt` = **índice da alternativa dentro do não-terminal** (0 = primeira); ε = `kids` vazio. | Proposta | Implementada — **combinar com o Daniel** |
| 28 | `Parser/Tree.lean` traz uma **árvore de exemplo feita à mão** (`ParseTree.Example.subChain`, de `a - b - c`) para a conversão ser escrita antes do motor. Um teste garante que o motor produz exatamente essa forma. | Proposta | Implementada |

## O gerador e o motor

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 29 | Nulável, FIRST e FOLLOW por **ponto fixo** (repetir até nada mudar), como o `epsilonClosure` do scanner. | Proposta | Implementada |
| 30 | O ponto fixo usa **combustível com limite provado suficiente** (não-terminais × (terminais + 1) + 1), em vez de `partial`. | Implementação | Implementada |
| 31 | `FOLLOW(início)` começa com `eof`. No miniC o próprio `Program` consome o `eof`. | Implementação | Implementada |
| 32 | A tabela recusa a gramática se houver **qualquer conflito** e lista todos (não-terminal, token, produções em disputa). | Proposta | Implementada |
| 33 | A tabela é indexada por (nome do não-terminal, índice do construtor do token — `TokenKind.ctorIdx`), sem alterar o `TokenKind` do scanner. | Implementação | Implementada |
| 34 | O motor usa **pilha explícita** (itens "símbolo" e "fechar nó") e não recursão, para ser fiel ao algoritmo dirigido por tabela. O laço é `partial` (como o `scanLoop`): termina porque toda gramática sem conflitos aqui consome token ou desempilha. | Implementação | Implementada |
| 35 | Erro: **para no primeiro erro** (sem recuperação). A mensagem tem linha:coluna, o que foi encontrado e a lista do que era esperado. Token `error` do scanner vira "caractere não reconhecido". | Proposta | Implementada |
| 36 | Pontos de entrada para o Daniel: `parseMiniC (toks : Array Token)` e `parseSource (src : String)`. | Implementação | Implementada |

## Testes, CI e repositório

| # | Decisão | Origem | Situação |
|---|---|---|---|
| 37 | Testes num **executável compilado** (`parserTests`, `Parser/Tests.lean`) rodado por **`lake test`** (é o `testDriver`), e não com `#guard`: no interpretador cada teste reconstruiria o DFA do scanner (10 mil transições) e a bateria passava de 5 minutos; compilada, roda em segundos. O executável sai com código 1 se algum teste falhar, e está em `defaultTargets`, então `lake build` também o compila. | Implementação | Implementada (64 testes passando) |
| 38 | O gerador é testado primeiro na **gramática de expressões dos livros** (respostas conhecidas) e depois no miniC; há uma gramática com conflito de propósito para testar a recusa. | Proposta | Implementada |
| 39 | A parte do Caio vive na branch **`dev/parser-generator`** (mesmo padrão do `dev/automata` do Felipe). | Grupo (padrão existente) | Fechada |
| 40 | O `Main.lean` **não foi alterado** nesta branch: ligar o parser lá é do Daniel. | Proposta | Fechada |
| 41 | O guia em PDF (`guia-do-projeto.pdf`) fica **fora dos commits**. | Caio | Fechada |
| 42 | A lista de "esperados" de um erro é exatamente a linha da tabela. Quando o erro cai numa cauda nulável (ex.: `return 1 }`), a lista é longa (FIRST ∪ FOLLOW). Mantido assim para o motor continuar puramente dirigido pela tabela; dá para encurtar depois sem mudar a gramática. | Implementação | Pode melhorar |
| 43 | O executável de testes se chama `parserTests` (sem hífen): o Lake não aceita `testDriver = "parser-tests"`. | Implementação | Fechada |
| 44 | O CI (`lean-action`) roda `lake build`; como existe `testDriver`, ele também deve rodar `lake test`. **Conferir no primeiro push** se os testes aparecem no log do CI. | Implementação | Conferir |

## Em aberto

- Confirmar com o professor o escopo "gerador de parser" (decisão 5).
- Confirmar a divisão do grupo (7 e 8) e o formato do `ParseTree` com o Daniel (27).
- Regra de `stringLit` no scanner (20).
- Definir quem faz tipos, interpretador e codegen (10).
