/-
  OpenTheory -> Lean 4 importer: PoC spike.

  A from-scratch OpenTheory article stack-machine replayer, implemented as a
  Lean 4 metaprogram. It parses a (hand-made) OpenTheory-style article, replays
  the primitive commands into real Lean `Expr`s, and hands the result to the
  Lean KERNEL via `addDecl`. The importer is UNTRUSTED: any mistranslation is
  caught because the kernel type-checks the built proof term.

  Commands realized here: name/number literals, nil, cons, typeOp, opType,
  var, varTerm, refl, appThm, thm.

  Encoding used in this spike (kept deliberately tiny):
    HOL type operator "ind" (0-ary)   ->  Lean `Nat`         (a fixed carrier)
    HOL type operator "->"  (2-ary)   ->  Lean arrow `a -> b`
    HOL term variable                 ->  a Lean local fvar
    HOL `refl t`      (|- t = t)      ->  `Eq.refl t`
    HOL `appThm h1 h2`(|- f x = g y)  ->  `congr h1 h2`  (Meta.mkCongr)
  Free HOL term variables are universally closed at `thm` time.
-/
import Lean
open Lean Meta Elab Command Term

namespace OTPoC

/-- Stack-machine objects. HOL types/terms are carried as native Lean `Expr`s. -/
inductive Obj where
  | name (s : String)
  | num  (n : Int)
  | list (xs : Array Obj)
  | tyop (s : String)
  | type (e : Expr)
  | var  (nm : String) (fv : Expr)   -- fv is the introduced Lean fvar
  | term (e : Expr)
  | thm  (concl proof : Expr)        -- hypotheses omitted in this PoC (Gamma = empty)
  deriving Inhabited

def Obj.asType : Obj → MetaM Expr
  | .type e => pure e
  | _ => throwError "expected a Type on the stack, got a different object"
def Obj.asTyop : Obj → MetaM String
  | .tyop s => pure s
  | _ => throwError "expected a TypeOp on the stack"
def Obj.asName : Obj → MetaM String
  | .name s => pure s
  | _ => throwError "expected a Name on the stack"
def Obj.asList : Obj → MetaM (Array Obj)
  | .list xs => pure xs
  | _ => throwError "expected a List on the stack"
def Obj.asTerm : Obj → MetaM Expr
  | .term e => pure e
  | _ => throwError "expected a Term on the stack"

/-- Interpret an applied HOL type operator as a native Lean type `Expr`. -/
def interpTyop (op : String) (args : Array Expr) : MetaM Expr := do
  match op, args with
  | "ind", #[] => pure (mkConst ``Nat)            -- fixed carrier for the demo
  | "->",  #[a, b] => mkArrow a b                 -- HOL function type -> Lean arrow
  | _, _ => throwError "unsupported type operator {op}/{args.size} in PoC"

/-- Classify a raw article token. -/
inductive Tok where
  | name (s : String) | num (n : Int) | cmd (s : String)

def classify (raw : String) : Tok :=
  let s := raw
  if s.startsWith "\"" && s.endsWith "\"" then
    .name (String.ofList ((s.toList.drop 1).dropLast))
  else match s.toInt? with
    | some n => .num n
    | none   => .cmd s

/-- The replay. `vars` accumulates introduced fvars for closing at `thm` time.
    `stk` is the machine stack. Written in continuation-passing so that when a
    `var` is introduced via `withLocalDeclD`, the rest of the article is replayed
    *inside* that local context (so `mkForallFVars`/`mkLambdaFVars` can abstract). -/
partial def go (vars : Array Expr) (stk : Array Obj) : List String → TermElabM Unit
  | [] => throwError "article ended without a `thm` command"
  | rawTok :: rest => do
    let push (o : Obj) := go vars (stk.push o) rest
    let pop : MetaM (Obj × Array Obj) := do
      match stk.back? with
      | some o => pure (o, stk.pop)
      | none => throwError "stack underflow"
    match classify rawTok with
    | .name s => push (.name s)
    | .num n  => push (.num n)
    | .cmd "nil"  => push (.list #[])
    | .cmd "cons" => do
        let (t, stk1) := (← pop)          -- tail (a list) on top
        let hd := stk1.back!
        let l ← t.asList
        go vars (stk1.pop.push (.list (#[hd] ++ l))) rest
    | .cmd "typeOp" => do
        let (n, stk1) := (← pop)
        let s ← n.asName
        go vars (stk1.push (.tyop s)) rest
    | .cmd "opType" => do
        let (lst, stk1) := (← pop)        -- arg list on top
        let opObj := stk1.back!
        let argObjs ← lst.asList
        let args ← show MetaM (Array Expr) from argObjs.mapM Obj.asType
        let op ← opObj.asTyop
        let ty ← interpTyop op args
        go vars (stk1.pop.push (.type ty)) rest
    | .cmd "var" => do
        let (tyObj, stk1) := (← pop)      -- type on top
        let nmObj := stk1.back!
        let ty ← tyObj.asType
        let nm ← nmObj.asName
        withLocalDeclD (Name.mkSimple nm) ty fun fv =>
          go (vars.push fv) (stk1.pop.push (.var nm fv)) rest
    | .cmd "varTerm" => do
        let (v, stk1) := (← pop)
        match v with
        | .var _ fv => go vars (stk1.push (.term fv)) rest
        | _ => throwError "varTerm: expected a Var"
    | .cmd "refl" => do
        let (tObj, stk1) := (← pop)
        let t ← tObj.asTerm
        let proof ← mkEqRefl t
        let concl ← inferType proof
        go vars (stk1.push (.thm concl proof)) rest
    | .cmd "appThm" => do
        let (th2, stk1) := (← pop)        -- |- x = y  (top)
        let (th1, stk2) := (th1p stk1)    -- |- f = g
        match th1, th2 with
        | .thm _ p1, .thm _ p2 =>
            let proof ← mkCongr p1 p2      -- |- f x = g y
            let concl ← inferType proof
            go vars (stk2.push (.thm concl proof)) rest
        | _, _ => throwError "appThm: expected two theorems"
    | .cmd "thm" => do
        let (thObj, _) := (← pop)
        match thObj with
        | .thm concl proof =>
            let stmt ← mkForallFVars vars concl
            let val  ← mkLambdaFVars vars proof
            let name := `OTPoC.imported0
            addDecl (.thmDecl { name, levelParams := [], type := stmt, value := val })
            logInfo m!"imported (kernel-checked): {name} : {stmt}"
        | _ => throwError "thm: expected a theorem on the stack"
    | .cmd other => throwError "unknown command: {other}"
where
  th1p (s : Array Obj) : (Obj × Array Obj) := (s.back!, s.pop)

/-- A hand-made article proving `|- f x = f x` for `f : ind -> ind`, `x : ind`.
    (`ind` is interpreted as `Nat` in this PoC.) Tokens are one-per-entry;
    quoted entries are names, bare words are commands.  Pop-order convention is
    documented inline; it is self-consistent with the replayer above. -/
def article : List String :=
  [ -- build term `f : ind -> ind`
    "\"f\"",                                   -- Name f
    "\"->\"", "typeOp",                        -- TypeOp ->
    "\"ind\"", "typeOp", "nil", "opType",      -- Type ind (=Nat)
    "\"ind\"", "typeOp", "nil", "opType",      -- Type ind (=Nat)
    "nil", "cons", "cons",                     -- List [ind, ind]
    "opType",                                  -- Type (ind -> ind)
    "var", "varTerm",                          -- Term f
    "refl",                                    -- |- f = f
    -- build term `x : ind`
    "\"x\"",                                   -- Name x
    "\"ind\"", "typeOp", "nil", "opType",      -- Type ind
    "var", "varTerm",                          -- Term x
    "refl",                                    -- |- x = x
    "appThm",                                  -- |- f x = f x
    "thm" ]                                    -- export

end OTPoC

open Lean Elab Command in
run_cmd liftTermElabM do
  OTPoC.go #[] #[] OTPoC.article

-- Kernel-checked theorem now exists in the environment:
#check @OTPoC.imported0
#print axioms OTPoC.imported0
