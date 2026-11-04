import Tests.Harness

-- ══════════════════════════════════════════════
-- TESTES DO VERIFICADOR DE TIPOS (Parser/TypeCheck.lean)
-- ══════════════════════════════════════════════
-- Cada teste diz o que verifica (o nome), de onde vem a exigência (`ref`: seção do TAPL,
-- decisão do projeto ou linha do código) e por que importa (`why`). `lake test -- --verbose`
-- lista tudo isso. Referências do TAPL: cap. 11 (extensões simples), 14 (exceções),
-- 15 (subtipagem), 16 (tipagem algorítmica, joins), 22 (reconstrução), 23 (polimorfismo).
--
-- Seis grupos documentam o que o verificador já faz. O sétimo, "lacunas conhecidas",
-- escreve o comportamento que o livro pede e o código ainda não tem: cada teste está
-- marcado como pendente (falha esperada). Quando a lacuna for fechada o teste passa e a
-- execução avisa para tirar a marca.

private def mentions (s frag : String) : Bool := (s.splitOn frag).length > 1

/-- Atalho: `t ref why teste` anexa a referência e o motivo ao teste. -/
private def t (ref why : String) (x : Test) : Test := x.doc ref why

/-- O verificador aceita o programa. -/
def typeOk (name src : String) : Test :=
  match parseProgram src with
  | .error e => { name, ok := false, detail := s!"o programa de teste nem passa no parser: {e}" }
  | .ok p =>
    match typeCheckProgram p with
    | .ok _ => { name, ok := true }
    | .error e => { name, ok := false, detail := s!"deveria aceitar, mas recusou: {e}" }

/-- O verificador recusa o programa, e a mensagem contém `frag`. Exigir o trecho evita que o
    teste passe por recusar pelo motivo errado. -/
def typeErr (name src frag : String) : Test :=
  match parseProgram src with
  | .error e => { name, ok := false, detail := s!"o programa de teste nem passa no parser: {e}" }
  | .ok p =>
    match typeCheckProgram p with
    | .ok _ => { name, ok := false, detail := "deveria recusar, mas aceitou" }
    | .error e =>
      { name, ok := mentions e frag, detail := s!"recusou por outro motivo: {e} (esperava “{frag}”)" }

/-- Tipo anotado no inicializador do primeiro comando de `void f() { ... }`. -/
def initTy (src : String) : Except String MType := do
  let p ← parseProgram s!"void f() \{ {src} }"
  match ← typeCheckProgram p with
  | [{ body := .block (.decl _ _ e :: _), .. }] => pure e.ty
  | _ => throw "forma inesperada do programa de teste"

/-- O inicializador da primeira declaração sai da checagem com o tipo `want`. -/
def tyIs (name src : String) (want : MType) : Test :=
  match initTy src with
  | .ok got => { name, ok := got == want, detail := s!"tipo anotado {got.show}, esperado {want.show}" }
  | .error e => { name, ok := false, detail := e }

-- Apaga as anotações de tipo, para comparar com o programa de origem.
partial def eraseE : Expr MType → Expr Unit
  | .lit l _ => .lit l ()
  | .var x _ => .var x ()
  | .neg e _ => .neg (eraseE e) ()
  | .not e _ => .not (eraseE e) ()
  | .bin op a b _ => .bin op (eraseE a) (eraseE b) ()
  | .call f args _ => .call f (args.map eraseE) ()
  | .array es _ => .array (es.map eraseE) ()
  | .index a i _ => .index (eraseE a) (eraseE i) ()

partial def eraseS : Stmt MType → Stmt Unit
  | .decl ty n e => .decl ty n (eraseE e)
  | .assign a v => .assign (eraseE a) (eraseE v)
  | .block ss => .block (ss.map eraseS)
  | .call f args => .call f (args.map eraseE)
  | .ifElse c th el => .ifElse (eraseE c) (eraseS th) (el.map eraseS)
  | .while c b => .while (eraseE c) (eraseS b)
  | .ret e => .ret (e.map eraseE)

def eraseProgram (p : Program MType) : Program Unit :=
  p.map fun f => { name := f.name, params := f.params, ret := f.ret, body := eraseS f.body }

/-- Checar tipos só anota: apagando as anotações volta-se exatamente ao programa de entrada. -/
def erasesBack (name src : String) : Test :=
  match parseProgram src with
  | .error e => { name, ok := false, detail := s!"parser: {e}" }
  | .ok p =>
    match typeCheckProgram p with
    | .error e => { name, ok := false, detail := s!"recusou: {e}" }
    | .ok typed => { name, ok := eraseProgram typed == p, detail := "a AST mudou além das anotações" }

-- ── 1. Expressões e operadores ─────────────────

def tiposExpressoes : List Test := [
  t "TAPL §11.1 (T-Base); decisão 46"
    "Sem a regra dos tipos base nenhum programa é tipável; é o ponto de partida do sistema."
    (typeOk "um literal de cada tipo base é aceito"
      "void f() { int a = 1; float b = 2.5; bool c = true; str s = \"x\"; }"),
  t "TAPL §11.1; Parser/TypeCheck.lean:95"
    "O tipo anotado na AST é o que o interpretador e o gerador de código vão ler."
    (tyIs "int + int tem tipo int" "int z = 1 + 2;" .int),
  t "TAPL §16.3 (junção de tipos)"
    "Mostra que a aritmética mista promove ao menor tipo comum aos dois operandos, não ao do primeiro."
    (tyIs "int + float tem tipo float" "float z = 1 + 2.5;" .float),
  t "TAPL §11.1"
    "Condições de if e while dependem de a comparação ter tipo bool."
    (tyIs "uma comparação tem tipo bool" "bool z = 1 < 2;" .bool),
  t "TAPL §15.2 (T-Sub vale de int para float, nunca o inverso)"
    "Perder precisão em silêncio seria um erro de tipo que o verificador precisa impedir."
    (typeErr "int não aceita float sem conversão explícita"
      "void f() { int x = 1.5; }" "incompatível"),
  t "TAPL §11.1; sem 'truthiness' (decisão 15)"
    "Garante que só bool serve de condição, sem a confusão do C entre int e bool."
    (typeErr "bool não aceita int" "void f() { bool b = 1; }" "incompatível"),
  t "Parser/TypeCheck.lean:76-81"
    "O menos unário só existe para números."
    (typeErr "o menos unário recusa bool" "void f() { int x = -true; }" "unário"),
  t "Parser/TypeCheck.lean:83-87"
    "O não lógico só existe para bool."
    (typeErr "o ! recusa int" "void f() { bool b = !1; }" "espera 'bool'"),
  t "Parser/TypeCheck.lean:108-112"
    "and e or exigem bool nos dois lados; o teste usa int no esquerdo para provar que ele é checado."
    (typeErr "and recusa operando int" "void f() { bool b = 1 and true; }" "espera 'bool'"),
  t "Parser/TypeCheck.lean:108-112"
    "Caso positivo que acompanha o negativo: lógica sobre bool é aceita."
    (typeOk "!, and e or combinam bool" "void f() { bool b = !(true and false) or true; }"),
  t "Parser/TypeCheck.lean:99-102"
    "Ordem só faz sentido entre números."
    (typeErr "< recusa bool" "void f() { bool b = true < false; }" "comparação"),
  t "Parser/TypeCheck.lean:103-107"
    "Igualdade entre tipos sem relação seria sempre falsa; é erro, não valor."
    (typeErr "== recusa int contra bool" "void f() { bool b = 1 == true; }" "comparação"),
  t "Parser/TypeCheck.lean:103-107"
    "Fixa que igualdade vale para tipos iguais, inclusive str."
    (typeOk "== aceita str contra str" "void f() { bool b = \"a\" == \"b\"; }"),
  t "decisões 20 e 63: strings só têm literal e escapes"
    "Documenta que não há concatenação; se o grupo quiser +, este teste muda de propósito."
    (typeErr "str + str é recusado" "void f() { str s = \"a\" + \"b\"; }" "incompatível")
]

-- ── 2. Escopo e declarações ────────────────────

def tiposEscopo : List Test := [
  t "TAPL §11.5 (T-Let)"
    "Na regra do let a variável entra no ambiente só depois do inicializador; usar antes lê lixo."
    (typeErr "usar uma variável antes de declará-la"
      "void f() { int y = x; int x = 1; }" "não declarada"),
  t "TAPL §11.5 (T-Let)"
    "Mesma regra: o inicializador não enxerga a variável que está sendo definida."
    (typeErr "o inicializador não vê a própria variável" "void f() { int x = x; }" "não declarada"),
  t "decisão 62 (aberta)"
    "Duas variáveis com o mesmo nome no mesmo bloco tornam o nome ambíguo."
    (typeErr "redeclarar no mesmo bloco" "void f() { int x = 1; int x = 2; }" "já foi declarada"),
  t "decisão 62 (aberta)"
    "Parâmetro e local compartilham o escopo da função."
    (typeErr "local com o nome de um parâmetro" "void f(int x) { int x = 1; }" "já foi declarada"),
  t "decisão 62 (aberta); TAPL §11.5 permitiria sombrear"
    "Registra a política atual (sombreamento proibido). Se o grupo adotar sombreamento, este teste vira o contrário."
    (typeErr "sombreamento em bloco interno é recusado"
      "void f() { int x = 1; if true { int x = 2; } }" "já foi declarada"),
  t "TAPL §11.5: o escopo do let termina com o corpo"
    "Prova que o ambiente é restaurado ao sair do bloco: o nome pode ser reusado em blocos irmãos."
    (typeOk "blocos irmãos reutilizam o mesmo nome"
      "void f() { if true { int x = 1; } if true { int x = 2; } }"),
  t "TAPL §11.5"
    "Variável de bloco não pode ser lida depois que o bloco fecha."
    (typeErr "a variável de um bloco não vaza" "void f() { if true { int y = 1; } y = 2; }" "não declarada"),
  t "Parser/TypeCheck.lean:183-184"
    "void é ausência de valor; variável void não tem o que guardar."
    (typeErr "variável do tipo void é recusada" "void f() { void x = 1; }" "void"),
  t "Parser/TypeCheck.lean:262-264"
    "Mesmo motivo, para parâmetros."
    (typeErr "parâmetro do tipo void é recusado" "void f(void x) { }" "void"),
  t "Parser/TypeCheck.lean:265-266"
    "Dois parâmetros com o mesmo nome tornam a chamada ambígua."
    (typeErr "parâmetro duplicado" "void f(int x, int x) { }" "duplicado")
]

-- ── 3. Subsunção, arrays e junções ─────────────

def tiposSubsuncao : List Test := [
  t "TAPL §15.2 (T-Sub), §15.5 (Int <: Float)"
    "É a única aresta do subtipo do miniC; vale em declaração, atribuição, argumento e retorno."
    (typeOk "int vira float em declaração" "void f() { float x = 1; }"),
  t "TAPL §15.2 (T-Sub)"
    "Mesma regra no ponto de atribuição."
    (typeOk "int vira float em atribuição" "void f() { float x = 1.5; x = 2; }"),
  t "TAPL §15.2 (T-Sub); T-App"
    "A subsunção na aplicação é o uso central da regra no livro."
    (typeOk "int vira float como argumento" "void g(float v) { } void f() { g(1); }"),
  t "TAPL §15.2 (T-Sub)"
    "Mesma regra no ponto de retorno."
    (typeOk "int vira float no retorno" "float f() { return 1; }"),
  t "TAPL §15.2: a subsunção não é simétrica"
    "O inverso do teste anterior precisa falhar, senão float e int seriam o mesmo tipo."
    (typeErr "float não vira int como argumento"
      "void g(int v) { } void f() { g(1.5); }" "incompatível"),
  t "TAPL §15.2"
    "Mesma assimetria no retorno."
    (typeErr "float não vira int no retorno" "int f() { return 1.5; }" "tipo de retorno"),
  t "TAPL §15.5 (S-Array); ArrayStoreException do Java"
    "Arrays são mutáveis: aceitar int[] onde se espera float[] deixaria gravar um float num int[]. O livro mostra que o Java paga por isso em tempo de execução."
    (typeErr "int[] não vira float[] (arrays são invariantes)"
      "void g(float[] v) { } void f() { int[] a = [1]; g(a); }" "incompatível"),
  t "TAPL §15.5 (S-Array)"
    "A invariância precisa valer também na declaração, não só no argumento."
    (typeErr "…também em declaração"
      "void f() { int[] a = [1]; float[] b = a; }" "incompatível"),
  t "TAPL §16.3 (joins)"
    "O tipo do literal é a junção dos tipos dos elementos: int e float juntam em float."
    (tyIs "o literal [1, 2.5] tem tipo float[]" "float[] a = [1, 2.5];" (.array .float)),
  t "TAPL §16.3: sem junção não há tipo"
    "Quando os elementos não têm tipo comum o programa é recusado, em vez de escolher um às cegas."
    (typeErr "o literal [1, true] não tem tipo" "void f() { int[] a = [1, true]; }" "elementos incompatíveis"),
  t "TAPL §11.12 (listas: head)"
    "Indexar devolve o tipo do elemento."
    (typeOk "indexar um int[] dá int" "void f() { int[] a = [1]; int x = a[0]; }"),
  t "TAPL §11.12"
    "O mesmo para dimensões a mais: a[i][j] tem o tipo do elemento mais interno."
    (typeOk "matriz: m[0][0] tem tipo int" "void f() { int[][] m = [[1]]; int x = m[0][0]; }"),
  t "Parser/TypeCheck.lean:137-138"
    "O índice é sempre int."
    (typeErr "índice float é recusado" "void f() { int[] a = [1]; int x = a[1.0]; }" "índice de array deve ser 'int'"),
  t "Parser/TypeCheck.lean:139-141"
    "Só arrays podem ser indexados."
    (typeErr "indexar um não-array" "void f() { int x = 1; int y = x[0]; }" "não-array"),
  t "TAPL §15.5: gravar em um array é o lado perigoso da covariância"
    "A atribuição a um elemento usa a mesma compatibilidade da atribuição simples."
    (typeErr "gravar float em int[]" "void f() { int[] a = [1]; a[0] = 2.5; }" "atribuição incompatível")
]

-- ── 4. Funções e chamadas ──────────────────────

def tiposChamadas : List Test := [
  t "TAPL §11.1 (T-App)"
    "Chamar com número errado de argumentos é erro de tipo da aplicação."
    (typeErr "aridade errada" "void g(int v) { } void f() { g(); }" "espera 1 argumento"),
  t "TAPL §11.1 (T-App)"
    "Cada argumento é comparado com o parâmetro correspondente."
    (typeErr "tipo de argumento errado" "void g(int v) { } void f() { g(true); }" "argumento incompatível"),
  t "Parser/TypeCheck.lean:158"
    "Nome desconhecido não é função."
    (typeErr "função não declarada" "void f() { g(); }" "não declarada"),
  t "TAPL §11.11 (general recursion)"
    "O corpo vê a assinatura da própria função; sem isso o fatorial não tipa."
    (typeOk "recursão direta" "int fat(int n) { return n * fat(n - 1); }"),
  t "TAPL §11.11 (letrec e recursão mútua)"
    "A primeira passada coleta todas as assinaturas antes dos corpos, como o livro exige; por isso a ordem das funções não importa."
    (typeOk "chamar função declarada depois" "void f() { g(); } void g() { }"),
  t "Parser/TypeCheck.lean:283"
    "Duas funções com o mesmo nome tornam a chamada ambígua."
    (typeErr "função redeclarada" "void f() { } void f() { }" "redeclarada"),
  t "Parser/TypeCheck.lean:191"
    "Uma função void não produz valor; usá-la numa expressão é erro."
    (typeErr "usar função void numa expressão" "void g() { } void f() { int x = g(); }" "incompatível"),
  t "TAPL §11.3 (curinga: t1;t2 descarta o valor de t1)"
    "Chamada como comando pode ignorar o resultado; a regra de sequência do livro admite isso."
    (typeOk "chamada como comando descarta o valor" "int g() { return 1; } void f() { g(); }"),
  t "TAPL cap. 23 (∀T. T → void)"
    "print é o único polimórfico; aceitar qualquer tipo não-void é o que o checker faz no lugar de variáveis de tipo."
    (typeOk "print aceita int, str, bool e arrays"
      "void f() { print(1); print(\"x\"); print(true); print([1, 2]); }"),
  t "Parser/TypeCheck.lean:154"
    "Aridade também vale para o embutido."
    (typeErr "print sem argumento" "void f() { print(); }" "espera 1 argumento"),
  t "Parser/TypeCheck.lean:152"
    "Não há valor void para imprimir."
    (typeErr "print de uma chamada void" "void g() { } void f() { print(g()); }" "void"),
  t "Parser/TypeCheck.lean:283"
    "O nome do embutido é reservado."
    (typeErr "redefinir print" "void print(int x) { }" "redeclarada")
]

-- ── 5. Comandos e retorno ──────────────────────

def tiposComandos : List Test := [
  t "Parser/TypeCheck.lean:242-245"
    "O valor retornado precisa caber no tipo declarado da função."
    (typeErr "retornar tipo errado" "int f() { return true; }" "tipo de retorno"),
  t "Parser/TypeCheck.lean:238-239"
    "Função com resultado não pode retornar sem valor."
    (typeErr "return vazio em função int" "int f() { return; }" "retorno vazio"),
  t "Parser/TypeCheck.lean:240-241"
    "Função void não tem valor para entregar."
    (typeErr "return com valor em função void" "void f() { return 1; }" "não deve retornar"),
  t "Parser/TypeCheck.lean:237"
    "Caso positivo do retorno vazio."
    (typeOk "return vazio em função void" "void f() { return; }"),
  t "TAPL §11.1 (T-If)"
    "A condição do if é bool; o teste usa int para provar que é checada."
    (typeErr "if com condição int" "void f() { if 1 { } }" "condição do 'if'"),
  t "TAPL §11.11 (laço como recursão)"
    "Mesma regra para o while."
    (typeErr "while com condição int" "void f() { while 1 { } }" "condição do 'while'"),
  t "Parser/TypeCheck.lean:201-202"
    "A atribuição compara o tipo do alvo com o do valor."
    (typeErr "atribuir bool a int" "void f() { int x = 1; x = true; }" "atribuição incompatível"),
  t "decisão 13; TAPL §11.3"
    "Um programa completo (condição, laço, recursão, arrays e float juntos) tipa de ponta a ponta."
    (typeOk "programa de exemplo do README"
      "int fatorial(int n) { if n <= 1 { return 1; } float x = 3.14; int[] v = [1, 2, 3]; v[0] = -v[1] * 2; return n * fatorial(n - 1 - 0); }")
]

-- ── 6. Propriedades do conjunto ────────────────

def tiposPropriedades : List Test := [
  t "TAPL §9.3 / §16.2: a tipagem só anota, não reescreve"
    "Se a checagem mudasse a estrutura, o interpretador leria uma AST diferente da que o parser entregou."
    (erasesBack "apagar as anotações devolve o programa de entrada (exemplo do README)"
      "int fatorial(int n) { if n <= 1 { return 1; } float x = 3.14; int[] v = [1, 2, 3]; v[0] = -v[1] * 2; return n * fatorial(n - 1 - 0); }"),
  t "TAPL §9.3 / §16.2"
    "Mesma propriedade num programa com promoção int→float e junção de array."
    (erasesBack "…também com subsunção e junção"
      "float g(float a) { return a; } void f() { float[] v = [1, 2.5]; float y = g(3); v[0] = y; }")
]

-- ── 7. Lacunas conhecidas (pendentes) ──────────
-- Comportamento que o livro pede e o verificador ainda não tem. Falhar é o esperado hoje.

def tiposLacunas : List Test := [
  (t "TAPL §15.5 + cap. 22 (tipo esperado)"
    "Com arrays invariantes, só o tipo esperado resolve um literal numérico. Hoje [1, 2] vira int[] e float[] a = [1, 2]; é recusado, embora float x = 1; seja aceito."
    (typeOk "o literal [1, 2] é aceito onde se espera float[]" "void f() { float[] a = [1, 2]; }")).pend
    "o literal é inferido sozinho; falta checar contra o tipo esperado (modo bidirecional)",
  (t "TAPL cap. 22 (tipo esperado) / §11.12 (nil[T])"
    "Hoje só a declaração com tipo aceita []."
    (typeOk "[] é aceito em atribuição" "void f() { int[] a = [1]; a = []; }")).pend
    "inferExpr não recebe o tipo esperado",
  (t "TAPL cap. 22 / §11.12"
    "return [] numa função que devolve int[] é natural."
    (typeOk "[] é aceito como retorno" "int[] f() { return []; }")).pend
    "inferExpr não recebe o tipo esperado",
  (t "TAPL cap. 22 / §11.12"
    "Passar [] a um parâmetro int[] é natural."
    (typeOk "[] é aceito como argumento" "void g(int[] v) { } void f() { g([]); }")).pend
    "inferExpr não recebe o tipo esperado",
  (t "TAPL §15.3 (progresso: um termo bem tipado não trava)"
    "Sem return em algum caminho a função termina sem valor, e a execução trava. É o furo de progresso mais direto do miniC."
    (typeErr "função int sem return é recusada" "int f() { int x = 1; }" "return")).pend
    "o verificador não analisa caminhos de retorno",
  (t "TAPL §15.3 (progresso)"
    "O mesmo furo, mais sutil: só um ramo do if retorna."
    (typeErr "return só num ramo do if é recusado"
      "int f(bool b) { if b { return 1; } }" "return")).pend
    "o verificador não analisa caminhos de retorno",
  (t "Parser/TypeCheck.lean:183 só rejeita void no topo"
    "void[] é um array de nada; a regra de variável void deveria valer para o elemento."
    (typeErr "void[] é recusado" "void f() { void[] v = []; }" "void")).pend
    "só o tipo void simples é checado",
  (t "TAPL §15.6 (semântica de coerção)"
    "O livro avisa que Int <: Float pede conversão explícita porque as representações diferem. A AST tem de carregar essa operação para o interpretador."
    (tyIs "float x = 1; sai com o inicializador do tipo float" "float x = 1;" .float)).pend
    "não existe nó de coerção; o inicializador continua int (decisão 60)",
  (t "legibilidade das mensagens"
    "throwErr concatena sem espaço depois dos dois-pontos: Erro semântico em 'f':variável…"
    (typeErr "a mensagem separa o nome da função do motivo" "void f() { x = 1; }" "': variável")).pend
    "throwErr concatena sem espaço (Parser/TypeCheck.lean:45)"
]
