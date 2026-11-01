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

/-- Verifica se um valor do tipo `src` pode ser atribuído/passado para um alvo `dst`.
    Permite promoção implícita de `int` para `float`. -/

def isCompatible (dst src : MType) : Bool :=
  dst == src || (dst == .float && src == .int)

-- Combina os tipos numéricos (`int` e `float`)
def numericComb : MType → MType → Option MType
  | .int, .int     => some .int
  | .float, .float => some .float
  | .int, .float   => some .float
  | .float, .int   => some .float
  | _, _           => none

private def throwErr (env : TypeEnv) (msg : String) : Except String α :=
  throw s!"Erro semântico em '{env.fnName}':{msg}"

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
      | some tres => pure (.bin op a' b' tres)
      | none => throwErr env s!"operador '{op.show}' incompatível entre '{ta.show}' e '{tb.show}'"
    | .lt | .le | .gt | .ge =>
      match numericComb ta tb with
      | some _ => pure (.bin op a' b' .bool)
      | none => throwErr env s!"comparação '{op.show}' incompatível entre '{ta.show}' e '{tb.show}'"
    | .eq | .ne =>
      if ta == tb || (numericComb ta tb).isSome then
        pure (.bin op a' b' .bool)
      else
        throwErr env s!"comparação '{op.show}' incompatível entre '{ta.show}' e '{tb.show}'"
    | .and | .or =>
      if ta == .bool && tb == .bool then
        pure (.bin op a' b' .bool)
      else
        throwErr env s!"operador '{op.show}' espera 'bool', mas encontrou '{ta.show}' e '{tb.show}'"

  | .call f args () => do
    let args' ← inferExprList env args
    let t ← checkCallSig env f (args'.map Expr.ty)
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
      pure (.array all (.array elemTy))

  | .index arr idx () => do
    let arr' ← inferExpr env arr
    let idx' ← inferExpr env idx
    if idx'.ty != .int then
      throwErr env s!"índice de array deve ser 'int', mas encontrou '{idx'.ty.show}'"
    match arr'.ty with
    | .array elemTy => pure (.index arr' idx' elemTy)
    | t => throwErr env s!"tentativa de indexar um valor não-array do tipo '{t.show}'"

partial def inferExprList (env : TypeEnv) : List (Expr Unit) → Except String (List (Expr MType))
  | []      => pure []
  | e :: es => do pure ((← inferExpr env e) :: (← inferExprList env es))

partial def checkCallSig (env : TypeEnv) (f : String) (argTypes : List MType) : Except String MType := do
  -- 1. Verifica se é built-in especial (como `print`)
  if f == "print" then
    match argTypes with
    | [t] =>
      if t == .void then throwErr env "não é possível passar 'void' para 'print'"
      else pure .void
    | _ => throwErr env s!"'print' espera 1 argumento, mas recebeu {argTypes.length}"
  else
    -- 2. Verifica na tabela de funções
    match env.funs[f]? with
    | none => throwErr env s!"função '{f}' não declarada"
    | some sig =>
      if sig.params.length != argTypes.length then
        throwErr env s!"função '{f}' espera {sig.params.length} argumento(s), mas recebeu {argTypes.length}"
      for (expected, found) in sig.params.zip argTypes do
        if !isCompatible expected found then
          throwErr env s!"argumento incompatível em '{f}': esperava '{expected.show}', encontrou '{found.show}'"
      pure sig.ret

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
    if t == .void then
      throwErr env s!"variável '{name}' não pode ser declarada com tipo 'void'"
    if env.vars.contains name then
      throwErr env s!"variável '{name}' já foi declarada nesta função"
    -- Caso especial: inicialização com array vazio `int[] v = [];`
    let init' ← match t, init with
      | .array _, .array [] () => pure (.array [] t)
      | _, _ => inferExpr env init
    if !isCompatible t init'.ty then
      throwErr env s!"inicialização incompatível em '{name}': esperava '{t.show}', encontrou '{init'.ty.show}'"
    let env' := { env with vars := env.vars.insert name t }
    pure (.decl t name init', env')

  | .assign target val => do
    if !isLValue target then
      throwErr env "alvo de atribuição inválido"
    let target' ← inferExpr env target
    let val' ← inferExpr env val
    if !isCompatible target'.ty val'.ty then
      throwErr env s!"atribuição incompatível: alvo é '{target'.ty.show}', valor é '{val'.ty.show}'"
    pure (.assign target' val', env)

  | .block stmts => do
    -- Ao sair de um bloco `{ ... }`, o mapa `env.vars` volta ao estado externo,
    -- mas dentro do bloco `env.vars` já contém as variáveis externas (impedindo shadowing).
    let stmts' ← checkStmtList env stmts
    pure (.block stmts', env)

  | .call f args => do
    let args' ← inferExprList env args
    let _ ← checkCallSig env f (args'.map Expr.ty)
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
      let e' ← inferExpr env e
      if !isCompatible expected e'.ty then
        throwErr env s!"tipo de retorno incompatível: esperava '{expected.show}', encontrou '{e'.ty.show}'"
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
def checkFun (funs : Std.HashMap String FunSig) (f : FunDecl Unit) : Except String (FunDecl MType) := do
  let mut vars : Std.HashMap String MType := {}
  for (pt, pname) in f.params do
    if pt == .void then
      throw s!"erro semântico em '{f.name}': parâmetro '{pname}' não pode ser 'void'"
    if vars.contains pname then
      throw s!"erro semântico em '{f.name}': parâmetro duplicado '{pname}'"
    vars := vars.insert pname pt

  let env : TypeEnv := { funs := funs, vars := vars, retType := f.ret, fnName := f.name }
  let (body', _) ← checkStmt env f.body
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
