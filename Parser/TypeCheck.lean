import Parser.Ast
import Std.Data.HashMap

-- ══════════════════════════════════════════════
-- 1. AMBIENTE DE TIPOS E TABELA DE SÍMBOLOS
-- ══════════════════════════════════════════════

structure FunSig where
  params : List MType
  ret    : MType
  deriving Repr, BEq

structure TypeEnv where
  funs    : Std.HashMap String FunSig
  vars    : Std.HashMap String MType
  retType : MType
  fnName  : String

-- Extrai o tipo já anotado na raiz de uma expressão
def Expr.ty : Expr MType → MType
  | .lit _ t       => t
  | .var _ t       => t
  | .neg _ t       => t
  | .not _ t       => t
  | .bin _ _ _ t   => t
  | .call _ _ t    => t
  | .array _ t     => t
  | .index _ _ t   => t
  | .coerce _ t    => t

/-- `void`, ou um array de `void` em qualquer profundidade: não há valor para guardar. -/
def MType.hasVoid : MType → Bool
  | .void    => true
  | .array t => t.hasVoid
  | _        => false

/-- Verifica se um valor do tipo `src` pode ser atribuído/passado para um alvo `dst`.
    Permite promoção implícita de `int` para `float`. -/

def isCompatible (dst src : MType) : Bool :=
  dst == src || (dst == .float && src == .int)

/-- Leva uma expressão já compatível ao tipo `dst`. A promoção `int → float` muda a
    representação do valor, então vira um nó `coerce` na AST (TAPL §15.6). -/
def coerceTo (dst : MType) (e : Expr MType) : Expr MType :=
  if e.ty == dst then e else .coerce e dst

-- Combina os tipos numéricos (`int` e `float`)
def numericComb : MType → MType → Option MType
  | .int, .int     => some .int
  | .float, .float => some .float
  | .int, .float   => some .float
  | .float, .int   => some .float
  | _, _           => none

private def throwErr (env : TypeEnv) (msg : String) : Except String α :=
  throw s!"Erro semântico em '{env.fnName}': {msg}"

-- ══════════════════════════════════════════════
-- 2. FUNÇÕES NATIVAS (BUILT-INS)
-- ══════════════════════════════════════════════
-- `none` na lista de parâmetros indica polimorfismo (qualquer tipo não-void, como `print`).

def builtins : List (String × Option (List MType) × MType) := [
  ("print", none, .void)
]

-- ══════════════════════════════════════════════
-- 3. CHECAGEM DE EXPRESSÕES
-- ══════════════════════════════════════════════
-- Dois modos (TAPL cap. 22): `inferExpr` descobre o tipo da expressão sozinha; `checkExpr`
-- recebe o tipo que o contexto espera (declaração, atribuição, argumento ou retorno).

mutual

partial def inferExpr (env : TypeEnv) : Expr Unit → Except String (Expr MType)
  | .lit l () =>
    let t : MType := match l with
      | .int _   => .int
      | .float _ => .float
      | .str _   => .str
      | .bool _  => .bool
    pure (.lit l t)

  | .var name () =>
    match env.vars[name]? with
    | some t => pure (.var name t)
    | none   => throwErr env s!"variável '{name}' não declarada"

  | .neg e () => do
    let e' ← inferExpr env e
    match e'.ty with
    | .int   => pure (.neg e' .int)
    | .float => pure (.neg e' .float)
    | t      => throwErr env s!"operador unário '-' inválido para o tipo '{t.show}'"

  | .not e () => do
    let e' ← inferExpr env e
    match e'.ty with
    | .bool => pure (.not e' .bool)
    | t     => throwErr env s!"operador lógico '!' espera 'bool', mas encontrou '{t.show}'"

  | .bin op a b () => do
    let a' ← inferExpr env a
    let b' ← inferExpr env b
    let ta := a'.ty
    let tb := b'.ty
    match op with
    | .add | .sub | .mul | .div =>
      match numericComb ta tb with
      | some tres => pure (.bin op (coerceTo tres a') (coerceTo tres b') tres)
      | none => throwErr env s!"operador '{op.show}' incompatível entre '{ta.show}' e '{tb.show}'"
    | .lt | .le | .gt | .ge =>
      match numericComb ta tb with
      | some t => pure (.bin op (coerceTo t a') (coerceTo t b') .bool)
      | none => throwErr env s!"comparação '{op.show}' incompatível entre '{ta.show}' e '{tb.show}'"
    | .eq | .ne =>
      if ta == tb then
        pure (.bin op a' b' .bool)
      else match numericComb ta tb with
        | some t => pure (.bin op (coerceTo t a') (coerceTo t b') .bool)
        | none => throwErr env s!"comparação '{op.show}' incompatível entre '{ta.show}' e '{tb.show}'"
    | .and | .or =>
      if ta == .bool && tb == .bool then
        pure (.bin op a' b' .bool)
      else
        throwErr env s!"operador '{op.show}' espera 'bool', mas encontrou '{ta.show}' e '{tb.show}'"

  | .call f args () => do
    let (args', t) ← checkCall env f args
    pure (.call f args' t)

  | .array elems () => do
    match elems with
    | [] => throwErr env "literal de array vazio '[]' não possui tipo inferível sem contexto"
    | h :: tl =>
      let h' ← inferExpr env h
      let tl' ← inferExprList env tl
      let all := h' :: tl'
      -- Se houver mistura de int e float no literal de array, promove o array para float[]
      let elemTy ← tl'.foldlM (init := h'.ty) fun acc e =>
        if acc == e.ty then pure acc
        else match numericComb acc e.ty with
          | some lub => pure lub
          | none => throwErr env s!"elementos incompatíveis no array: '{acc.show}' e '{e.ty.show}'"
      if elemTy.hasVoid then
        throwErr env s!"array não pode ter elementos do tipo '{elemTy.show}'"
      pure (.array (all.map (coerceTo elemTy)) (.array elemTy))

  | .index arr idx () => do
    let arr' ← inferExpr env arr
    let idx' ← inferExpr env idx
    if idx'.ty != .int then
      throwErr env s!"índice de array deve ser 'int', mas encontrou '{idx'.ty.show}'"
    match arr'.ty with
    | .array elemTy => pure (.index arr' idx' elemTy)
    | t => throwErr env s!"tentativa de indexar um valor não-array do tipo '{t.show}'"

  -- O parser não produz `coerce`; se aparecer, a conversão é decidida de novo aqui.
  | .coerce e () => inferExpr env e

partial def inferExprList (env : TypeEnv) : List (Expr Unit) → Except String (List (Expr MType))
  | []      => pure []
  | e :: es => do pure ((← inferExpr env e) :: (← inferExprList env es))

/-- Verifica `e` contra o tipo `expected`. Um literal de array é checado elemento a elemento, o
    que dá tipo a `[]` e deixa `[1, 2]` valer como `float[]`; qualquer outra expressão é inferida,
    comparada e, se preciso, convertida. `mismatch` monta a mensagem a partir do tipo encontrado. -/
partial def checkExpr (env : TypeEnv) (expected : MType) (e : Expr Unit)
    (mismatch : MType → String) : Except String (Expr MType) := do
  match expected, e with
  | .array elemTy, .array elems () =>
    let elems' ← elems.mapM fun el => checkExpr env elemTy el fun found =>
      s!"elementos incompatíveis no array: esperava '{elemTy.show}', encontrou '{found.show}'"
    pure (.array elems' expected)
  | _, _ =>
    let e' ← inferExpr env e
    if !isCompatible expected e'.ty then
      throwErr env (mismatch e'.ty)
    pure (coerceTo expected e')

/-- Verifica uma chamada e devolve os argumentos anotados e o tipo do resultado. -/
partial def checkCall (env : TypeEnv) (f : String) (args : List (Expr Unit)) :
    Except String (List (Expr MType) × MType) := do
  -- 1. Verifica se é built-in especial (como `print`)
  if f == "print" then
    match args with
    | [a] =>
      let a' ← inferExpr env a
      if a'.ty == .void then
        throwErr env "não é possível passar 'void' para 'print'"
      pure ([a'], .void)
    | _ => throwErr env s!"'print' espera 1 argumento, mas recebeu {args.length}"
  else
    -- 2. Verifica na tabela de funções
    match env.funs[f]? with
    | none => throwErr env s!"função '{f}' não declarada"
    | some sig =>
      if sig.params.length != args.length then
        throwErr env s!"função '{f}' espera {sig.params.length} argumento(s), mas recebeu {args.length}"
      let args' ← (sig.params.zip args).mapM fun (expected, a) => checkExpr env expected a fun found =>
        s!"argumento incompatível em '{f}': esperava '{expected.show}', encontrou '{found.show}'"
      pure (args', sig.ret)

end

-- ══════════════════════════════════════════════
-- 4. CHECAGEM DE COMANDOS (COM ESCOPO BLOQUEADO)
-- ══════════════════════════════════════════════

-- Verifica se a expressão pode figurar no lado esquerdo de uma atribuição
def isLValue : Expr α → Bool
  | .var _ _  => true
  | .index a _ _ => isLValue a
  | _ => false

mutual

partial def checkStmt (env : TypeEnv) : Stmt Unit → Except String (Stmt MType × TypeEnv)
  | .decl t name init => do
    if t.hasVoid then
      throwErr env s!"variável '{name}' não pode ser declarada com tipo '{t.show}'"
    if env.vars.contains name then
      throwErr env s!"variável '{name}' já foi declarada nesta função"
    let init' ← checkExpr env t init fun found =>
      s!"inicialização incompatível em '{name}': esperava '{t.show}', encontrou '{found.show}'"
    let env' := { env with vars := env.vars.insert name t }
    pure (.decl t name init', env')

  | .assign target val => do
    if !isLValue target then
      throwErr env "alvo de atribuição inválido"
    let target' ← inferExpr env target
    let val' ← checkExpr env target'.ty val fun found =>
      s!"atribuição incompatível: alvo é '{target'.ty.show}', valor é '{found.show}'"
    pure (.assign target' val', env)

  | .block stmts => do
    -- Ao sair de um bloco `{ ... }`, o mapa `env.vars` volta ao estado externo,
    -- mas dentro do bloco `env.vars` já contém as variáveis externas (impedindo shadowing).
    let stmts' ← checkStmtList env stmts
    pure (.block stmts', env)

  | .call f args => do
    let (args', _) ← checkCall env f args
    pure (.call f args', env)

  | .ifElse cond thenB elseB => do
    let cond' ← inferExpr env cond
    if cond'.ty != .bool then
      throwErr env s!"condição do 'if' deve ser 'bool', mas encontrou '{cond'.ty.show}'"
    let (thenB', _) ← checkStmt env thenB
    let elseB' ← match elseB with
      | none   => pure none
      | some e => do
        let (e', _) ← checkStmt env e
        pure (some e')
    pure (.ifElse cond' thenB' elseB', env)

  | .while cond body => do
    let cond' ← inferExpr env cond
    if cond'.ty != .bool then
      throwErr env s!"condição do 'while' deve ser 'bool', mas encontrou '{cond'.ty.show}'"
    let (body', _) ← checkStmt env body
    pure (.while cond' body', env)

  | .ret optExpr => do
    match optExpr, env.retType with
    | none, .void => pure (.ret none, env)
    | none, expected =>
      throwErr env s!"retorno vazio em função que retorna '{expected.show}'"
    | some _, .void =>
      throwErr env "função 'void' não deve retornar um valor"
    | some e, expected =>
      let e' ← checkExpr env expected e fun found =>
        s!"tipo de retorno incompatível: esperava '{expected.show}', encontrou '{found.show}'"
      pure (.ret (some e'), env)

partial def checkStmtList (env : TypeEnv) : List (Stmt Unit) → Except String (List (Stmt MType))
  | []      => pure []
  | s :: ss => do
    let (s', env') ← checkStmt env s
    let ss' ← checkStmtList env' ss
    pure (s' :: ss')

end

-- ══════════════════════════════════════════════
-- 5. CHECAGEM DE FUNÇÕES E DO PROGRAMA
-- ══════════════════════════════════════════════

/-- Todo caminho por este comando passa por um `return`. O `while` nunca conta, porque o corpo
    pode não rodar nenhuma vez. -/
def Stmt.alwaysReturns {Ty : Type} : Stmt Ty → Bool
  | .ret _ => true
  | .block ss => ss.attach.any fun ⟨s, _⟩ => s.alwaysReturns
  | .ifElse _ thenB (some elseB) => thenB.alwaysReturns && elseB.alwaysReturns
  | _ => false

def checkFun (funs : Std.HashMap String FunSig) (f : FunDecl Unit) : Except String (FunDecl MType) := do
  if f.ret != .void && f.ret.hasVoid then
    throw s!"erro semântico em '{f.name}': a função não pode retornar '{f.ret.show}'"
  let mut vars : Std.HashMap String MType := {}
  for (pt, pname) in f.params do
    if pt.hasVoid then
      throw s!"erro semântico em '{f.name}': parâmetro '{pname}' não pode ser '{pt.show}'"
    if vars.contains pname then
      throw s!"erro semântico em '{f.name}': parâmetro duplicado '{pname}'"
    vars := vars.insert pname pt

  let env : TypeEnv := { funs := funs, vars := vars, retType := f.ret, fnName := f.name }
  let (body', _) ← checkStmt env f.body
  if f.ret != .void && !f.body.alwaysReturns then
    throw s!"erro semântico em '{f.name}': a função retorna '{f.ret.show}', mas nem todo caminho termina em 'return'"
  pure { name := f.name, params := f.params, ret := f.ret, body := body' }

/-- Analisa semanticamente todo o programa e devolve a AST anotada com `MType`. -/
def typeCheckProgram (prog : Program Unit) : Except String (Program MType) := do
  let mut funs : Std.HashMap String FunSig := {}
  -- Registra built-ins com assinatura fixa
  for (bname, bparams, bret) in builtins do
    if let some ps := bparams then
      funs := funs.insert bname { params := ps, ret := bret }

  -- 1ª Passada: coleta assinaturas de todas as funções (permite recursão mútua)
  for f in prog do
    if f.name == "print" || funs.contains f.name then
      throw s!"erro semântico: função '{f.name}' redeclarada"
    funs := funs.insert f.name { params := f.params.map (·.1), ret := f.ret }

  -- 2ª Passada: verifica o corpo de cada função
  prog.mapM (checkFun funs)
