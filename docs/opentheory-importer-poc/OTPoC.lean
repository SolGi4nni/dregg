/-
  OpenTheory -> Lean 4 importer.

  A from-scratch OpenTheory v6 article stack-machine replayer, implemented as a
  Lean 4 metaprogram (`import Lean`, no Mathlib). It parses an OpenTheory article,
  replays the primitive commands into native Lean `Expr`s, and hands each exported
  theorem to the Lean KERNEL via `addDecl`. The importer is UNTRUSTED: any
  mistranslation produces an `Expr` the kernel rejects. The TCB is:
    (1) the Lean kernel, (2) the encoding below, (3) the `axiom` discharge table.
  The parser and the ~20 rule realizations are OUTSIDE the TCB.

  Command semantics follow the reference reader
  (HOL4 `src/opentheory/reader/OpenTheoryReader.sml`), including exact pop orders.

  Encoding (the trusted core, kept tiny):
    HOL `bool`            -> Lean `Prop`            (Sort 0)
    HOL `->` (fun)        -> Lean arrow `a -> b`
    HOL `ind` (infinity)  -> Lean `Nat`             (a fixed infinite carrier)
    HOL type variable     -> a Lean fvar `A : Type`
    HOL term variable     -> a Lean fvar (interned by name+type = HOL var identity)
    HOL `=`               -> `@Eq`
    HOL `T`/`/\`/`==>`/`!`/`?` (Data.Bool.*) -> Lean `True`/`And`/(imp)/(forall)/`Exists`
    HOL Hilbert choice    -> `Classical.epsilon` (see interpConst; not exercised here)

  SOUNDNESS GATE: the `axiom` command resolves ONLY to a pre-proved Lean theorem
  whose statement is DEFEQ to the article's asserted formula (the discharge table
  below). Anything else HARD-ERRORS. An `axiom` NEVER creates a fresh Lean `axiom`
  (that would be a fail-open gate). Each exported theorem is additionally checked
  axiom-clean: `collectAxioms` must be a subset of {propext, Classical.choice,
  Quot.sound} (dregg's classical set), else the import errors.
-/
import Lean
open Lean Meta Elab Command

namespace OTImport

/- ======================================================================
   Axiom discharge table.

   These are ordinary, honestly-proved Lean theorems. Each states that Lean's
   native connective equals the Andrews/HOL definition that the OpenTheory `bool`
   theory imports as an assumption. They are the ONLY facts the `axiom` command
   may resolve to.
   ====================================================================== -/

theorem d_true : True := trivial

theorem d_and_def :
    And = (fun p q : Prop => (fun f : Prop → Prop → Prop => f p q) = (fun f => f True True)) := by
  funext p q
  apply propext
  apply Iff.intro
  · rintro ⟨hp, hq⟩
    funext f
    show f p q = f True True
    rw [eq_true hp, eq_true hq]
  · intro h
    exact ⟨of_eq_true (congrFun h (fun a _ => a)), of_eq_true (congrFun h (fun _ b => b))⟩

theorem d_imp_def :
    (fun p q : Prop => p → q) = (fun p q : Prop => (And p q) = p) := by
  funext p q
  apply propext
  apply Iff.intro
  · intro hpq
    exact propext (Iff.intro (fun h => h.1) (fun hp => ⟨hp, hpq hp⟩))
  · intro heq hp
    exact (cast heq.symm hp).2

theorem d_forall_def {A : Type} :
    (fun (P : A → Prop) => ∀ x, P x) = (fun (P : A → Prop) => P = fun _ => True) := by
  funext P
  apply propext
  apply Iff.intro
  · intro h
    funext x
    exact propext (Iff.intro (fun _ => trivial) (fun _ => h x))
  · intro h x
    exact of_eq_true (congrFun h x)

theorem d_exists_def {A : Type} :
    (@Exists A) = (fun (P : A → Prop) => ∀ q : Prop, (∀ x, P x → q) → q) := by
  funext P
  apply propext
  apply Iff.intro
  · intro h q hq
    exact Exists.elim h hq
  · intro h
    exact h (∃ x, P x) (fun x px => ⟨x, px⟩)

/-- Names of the discharge theorems. `axiom` may resolve to exactly these. -/
def dischargeNames : List Name :=
  [``d_true, ``d_and_def, ``d_imp_def, ``d_forall_def, ``d_exists_def]

/- ======================================================================
   Stack-machine objects and importer state.
   ====================================================================== -/

/-- An OpenTheory sequent `Γ ⊦ φ` realized in Lean. `proof : concl` may reference
    the fvars in `hyps` (each an fvar `h : ψ` standing for a hypothesis `ψ ∈ Γ`). -/
structure Thm where
  hyps  : Array Expr    -- hypothesis fvars (a set; deduped by FVarId)
  concl : Expr          -- the encoded conclusion (a Prop)
  proof : Expr          -- a Lean proof term of `concl`

inductive Obj where
  | num  (n : Int)
  | name (s : String)
  | list (xs : Array Obj)
  | tyop (s : String)
  | type (e : Expr)
  | const (s : String)
  | var  (nm : String) (ty : Expr) (fv : Expr)
  | term (e : Expr)
  | thm  (t : Thm)
  deriving Inhabited

structure St where
  stk     : Array Obj := #[]
  dict    : Array (Int × Obj) := #[]
  tyvars  : Array (String × Expr) := #[]          -- name -> fvar : Type
  tmvars  : Array (String × Expr × Expr) := #[]   -- name × encoded-type × fvar
  hyps    : Array (Expr × Expr) := #[]            -- statement × hyp fvar
  defined : Array (String × Name) := #[]          -- OT const name -> Lean def name
  count   : Nat := 0

/- ---- small helpers on St ---- -/

def dfind (d : Array (Int × Obj)) (k : Int) : Option Obj :=
  (d.find? (·.1 == k)).map (·.2)
def dins (d : Array (Int × Obj)) (k : Int) (o : Obj) : Array (Int × Obj) :=
  (d.filter (·.1 != k)).push (k, o)
def drem (d : Array (Int × Obj)) (k : Int) : Array (Int × Obj) :=
  d.filter (·.1 != k)

/-- set-union of hypothesis-fvar arrays, deduped by FVarId. -/
def hUnion (a b : Array Expr) : Array Expr := Id.run do
  let mut out := a
  for h in b do
    unless out.any (fun x => x.fvarId! == h.fvarId!) do out := out.push h
  return out

def Obj.asName : Obj → MetaM String
  | .name s => pure s | _ => throwError "expected Name"
def Obj.asType : Obj → MetaM Expr
  | .type e => pure e | _ => throwError "expected Type"
def Obj.asTyop : Obj → MetaM String
  | .tyop s => pure s | _ => throwError "expected TypeOp"
def Obj.asList : Obj → MetaM (Array Obj)
  | .list xs => pure xs | _ => throwError "expected List"
def Obj.asTerm : Obj → MetaM Expr
  | .term e => pure e | _ => throwError "expected Term"
def Obj.asConst : Obj → MetaM String
  | .const s => pure s | _ => throwError "expected Const"
def Obj.asThm : Obj → MetaM Thm
  | .thm t => pure t | _ => throwError "expected Thm"
def Obj.asVar : Obj → MetaM (String × Expr × Expr)
  | .var nm ty fv => pure (nm, ty, fv) | _ => throwError "expected Var"

/- ======================================================================
   The encoding.
   ====================================================================== -/

/-- Interpret an applied HOL type operator as a native Lean type `Expr`. -/
def interpTyop (op : String) (args : Array Expr) : MetaM Expr := do
  match op, args with
  | "bool", #[]    => pure (mkSort Level.zero)      -- Prop
  | "ind",  #[]    => pure (mkConst ``Nat)          -- fixed infinite carrier
  | "->",   #[a,b] => mkArrow a b
  | "fun",  #[a,b] => mkArrow a b
  | _, _ => throwError "interpTyop: unsupported type operator {op}/{args.size}"

/-- Interpret a HOL constant at a given (already-encoded) monomorphic type. -/
def interpConst (defined : Array (String × Name)) (nm : String) (ty : Expr) : MetaM Expr := do
  if let some (_, leanNm) := defined.find? (·.1 == nm) then
    return mkConst leanNm
  match nm with
  | "=" =>
      let α := ty.bindingDomain!
      mkAppOptM ``Eq #[α]
  | "Data.Bool.T"   => pure (mkConst ``True)
  | "Data.Bool.F"   => pure (mkConst ``False)
  | "Data.Bool./\\" => pure (mkConst ``And)         -- name after unescape is Data.Bool./\
  | "Data.Bool.\\/" => pure (mkConst ``Or)
  | "Data.Bool.~"   => pure (mkConst ``Not)
  | "Data.Bool.==>" =>
      withLocalDeclD `p (mkSort Level.zero) fun p =>
      withLocalDeclD `q (mkSort Level.zero) fun q => do
        mkLambdaFVars #[p, q] (← mkArrow p q)
  | "Data.Bool.!" =>
      let A := ty.bindingDomain!.bindingDomain!    -- ty = (A -> Prop) -> Prop
      withLocalDeclD `P (← mkArrow A (mkSort Level.zero)) fun P => do
        let body ← withLocalDeclD `x A fun x => mkForallFVars #[x] (mkApp P x)
        mkLambdaFVars #[P] body
  | "Data.Bool.?" =>
      let A := ty.bindingDomain!.bindingDomain!
      mkAppOptM ``Exists #[A]
  | "select" =>
      let A := ty.bindingDomain!.bindingDomain!    -- (A -> Prop) -> A
      mkAppOptM ``Classical.epsilon #[A]
  | _ => throwError "interpConst: unsupported constant {nm}"

/- ======================================================================
   The axiom gate.
   ====================================================================== -/

/-- Try to discharge an `axiom` command's assertion `concl` (with empty Γ) to a
    pre-proved Lean theorem. Returns the proof term, or `none` (⇒ hard error). -/
def tryDischarge (concl : Expr) : MetaM (Option Expr) := do
  for dn in dischargeNames do
    let ci ← getConstInfo dn
    let (mvars, _, dConcl) ← forallMetaTelescope ci.type
    if ← isDefEq dConcl concl then
      let pf := mkAppN (mkConst dn (ci.levelParams.map (fun _ => Level.zero))) mvars
      return some (← instantiateMVars pf)
  return none

/- ======================================================================
   Tokenizer.
   ====================================================================== -/

/-- unescape an OpenTheory quoted-name body (`\\`→`\`, `\"`→`"`). -/
def unquote (s : String) : String := Id.run do
  let cs := s.toList
  let mut out : List Char := []
  let mut i := cs
  while true do
    match i with
    | [] => break
    | '\\' :: c :: rest => out := c :: out; i := rest
    | c :: rest => out := c :: out; i := rest
  return String.ofList out.reverse

inductive Tok where
  | name (s : String) | num (n : Int) | cmd (s : String)

def classify (raw : String) : Tok :=
  if raw.startsWith "\"" && raw.endsWith "\"" && raw.length >= 2 then
    .name (unquote (String.ofList ((raw.toList.drop 1).dropLast)))
  else match raw.toInt? with
    | some n => .num n
    | none   => .cmd raw

/- ======================================================================
   The replay.  CPS over the token list: fvar-introducing commands wrap the
   remainder of the article inside `withLocalDeclD`, so all introduced fvars stay
   in scope until the terminal `thm` closes them.
   ====================================================================== -/

/-- pop the top object. -/
def pop1 (st : St) : MetaM (Obj × St) := do
  match st.stk.back? with
  | some o => pure (o, { st with stk := st.stk.pop })
  | none => throwError "stack underflow"

/-- extract a `destEq`: from `@Eq τ a b` return `(τ, a, b)`. -/
def destEq (e : Expr) : MetaM (Expr × Expr × Expr) := do
  match e.eq? with
  | some (τ, a, b) => pure (τ, a, b)
  | none => throwError "expected an equation, got {e}"

/-- introduce an array of fresh hypotheses `h_i : stmt_i`, run `k` with the fvars. -/
partial def withFreshHyps (stmts : Array Expr) (k : Array Expr → TermElabM Unit) : TermElabM Unit := do
  let rec loop (i : Nat) (acc : Array Expr) : TermElabM Unit := do
    if h : i < stmts.size then
      withLocalDeclD `h stmts[i] fun fv => loop (i+1) (acc.push fv)
    else k acc
  loop 0 #[]

/-- Ensure each `(name, type)` spec is an interned term-variable of `st`, introducing
    the missing ones, then run `k` with the (possibly extended) `st` and the fvars. -/
partial def withEnsuredTmvars (st : St) (specs : Array (String × Expr))
    (k : St → Array Expr → TermElabM Unit) : TermElabM Unit := do
  let rec loop (i : Nat) (st : St) (acc : Array Expr) : TermElabM Unit := do
    if h : i < specs.size then
      let (nm, ty) := specs[i]
      match st.tmvars.find? (fun (n, t, _) => n == nm && t == ty) with
      | some (_, _, fv) => loop (i+1) st (acc.push fv)
      | none =>
        withLocalDeclD (Name.mkSimple nm) ty fun fv => do
          loop (i+1) { st with tmvars := st.tmvars.push (nm, ty, fv) } (acc.push fv)
    else k st acc
  loop 0 st #[]

/-- Ensure each hypothesis `stmt` is an interned hypothesis fvar of `st`. -/
partial def withEnsuredHyps (st : St) (stmts : Array Expr)
    (k : St → Array Expr → TermElabM Unit) : TermElabM Unit := do
  let rec loop (i : Nat) (st : St) (acc : Array Expr) : TermElabM Unit := do
    if h : i < stmts.size then
      let stmt := stmts[i]
      match st.hyps.find? (fun (s, _) => s == stmt) with
      | some (_, fv) => loop (i+1) st (acc.push fv)
      | none =>
        withLocalDeclD `h stmt fun fv => do
          loop (i+1) { st with hyps := st.hyps.push (stmt, fv) } (acc.push fv)
    else k st acc
  loop 0 st #[]

partial def go (st : St) : List String → TermElabM Unit
  | [] => pure ()  -- article may end after its last `thm`
  | rawTok :: rest => do
    let cont (st' : St) := go st' rest
    let push (o : Obj) := cont { st with stk := st.stk.push o }
    match classify rawTok with
    | .name s => push (.name s)
    | .num n  => push (.num n)
    | .cmd c  =>
      match c with
      | "version" => let (_, st) ← pop1 st; cont st
      | "pop"     => let (_, st) ← pop1 st; cont st
      | "nil"     => push (.list #[])
      | "cons"    =>
          let (t, st) ← pop1 st          -- tail (list) on top
          let (h, st) ← pop1 st          -- head
          let l ← t.asList
          cont { st with stk := st.stk.push (.list (#[h] ++ l)) }
      | "def" =>
          let (k, st) ← pop1 st
          let key ← (match k with | .num n => pure n | _ => throwError "def: expected key")
          let x := st.stk.back!          -- peek (stays on stack)
          cont { st with dict := dins st.dict key x }
      | "ref" =>
          let (k, st) ← pop1 st
          let key ← (match k with | .num n => pure n | _ => throwError "ref: expected key")
          match dfind st.dict key with
          | some o => cont { st with stk := st.stk.push o }
          | none => throwError "ref: missing dictionary key {key}"
      | "remove" =>
          let (k, st) ← pop1 st
          let key ← (match k with | .num n => pure n | _ => throwError "remove: expected key")
          match dfind st.dict key with
          | some o => cont { st with stk := st.stk.push o, dict := drem st.dict key }
          | none => throwError "remove: missing dictionary key {key}"
      | "typeOp" =>
          let (n, st) ← pop1 st
          push_st st (.tyop (← n.asName)) rest
      | "varType" =>
          let (n, st) ← pop1 st
          let nm ← n.asName
          match st.tyvars.find? (·.1 == nm) with
          | some (_, fv) => cont { st with stk := st.stk.push (.type fv) }
          | none =>
            withLocalDeclD (Name.mkSimple nm) (mkSort (Level.succ Level.zero)) fun fv =>
              go { st with stk := st.stk.push (.type fv), tyvars := st.tyvars.push (nm, fv) } rest
      | "opType" =>
          let (lst, st) ← pop1 st         -- arg list on top
          let (opO, st) ← pop1 st
          let argObjs ← lst.asList
          let args ← argObjs.mapM (fun o => do return (← o.asType))
          let ty ← interpTyop (← opO.asTyop) args
          cont { st with stk := st.stk.push (.type ty) }
      | "const" =>
          let (n, st) ← pop1 st
          push_st st (.const (← n.asName)) rest
      | "constTerm" =>
          let (tyO, st) ← pop1 st          -- type on top
          let (cO, st) ← pop1 st
          let e ← interpConst st.defined (← cO.asConst) (← tyO.asType)
          cont { st with stk := st.stk.push (.term e) }
      | "var" =>
          let (tyO, st) ← pop1 st          -- type on top
          let (nmO, st) ← pop1 st
          let ty ← tyO.asType
          let nm ← nmO.asName
          match st.tmvars.find? (fun (n, t, _) => n == nm && t == ty) with
          | some (_, _, fv) => cont { st with stk := st.stk.push (.var nm ty fv) }
          | none =>
            withLocalDeclD (Name.mkSimple nm) ty fun fv => do
              let st := { st with stk := st.stk.push (.var nm ty fv), tmvars := st.tmvars.push (nm, ty, fv) }
              go st rest
      | "varTerm" =>
          let (v, st) ← pop1 st
          let (_, _, fv) ← v.asVar
          cont { st with stk := st.stk.push (.term fv) }
      | "absTerm" =>
          let (bO, st) ← pop1 st           -- body term on top
          let (vO, st) ← pop1 st
          let (_, _, fv) ← vO.asVar
          let lam ← mkLambdaFVars #[fv] (← bO.asTerm)
          cont { st with stk := st.stk.push (.term lam) }
      | "appTerm" =>
          let (xO, st) ← pop1 st           -- arg on top
          let (fO, st) ← pop1 st
          cont { st with stk := st.stk.push (.term (mkApp (← fO.asTerm) (← xO.asTerm))) }
      | "refl" =>
          let (tO, st) ← pop1 st
          let t ← tO.asTerm
          let proof ← mkEqRefl t
          let concl ← inferType proof
          push_thm st { hyps := #[], concl, proof } rest
      | "assume" =>
          let (tO, st) ← pop1 st
          let φ ← tO.asTerm
          match st.hyps.find? (fun (s, _) => s == φ) with
          | some (_, fv) => push_thm st { hyps := #[fv], concl := φ, proof := fv } rest
          | none =>
            withLocalDeclD `h φ fun fv => do
              let st := { st with stk := st.stk.push (.thm { hyps := #[fv], concl := φ, proof := fv }), hyps := st.hyps.push (φ, fv) }
              go st rest
      | "betaConv" =>
          let (tO, st) ← pop1 st
          let t ← tO.asTerm
          -- HOL BETA_CONV is a SINGLE outermost beta step (not `headBeta`, which
          -- would over-reduce nested redexes and diverge from the article).
          let reduct := match t with
            | .app (.lam _ _ body _) arg => body.instantiate1 arg
            | _ => t
          let concl ← mkEq t reduct
          let proof ← mkExpectedTypeHint (← mkEqRefl t) concl
          push_thm st { hyps := #[], concl, proof } rest
      | "appThm" =>
          let (xyO, st) ← pop1 st          -- ⊦ x = y  (top)
          let (fgO, st) ← pop1 st          -- ⊦ f = g
          let t1 ← fgO.asThm; let t2 ← xyO.asThm
          let (_, _f, g) ← destEq t1.concl
          let (_, x, _y) ← destEq t2.concl
          let proof ← mkEqTrans (← mkCongrFun t1.proof x) (← mkCongrArg g t2.proof)
          let concl ← inferType proof
          push_thm st { hyps := hUnion t1.hyps t2.hyps, concl, proof } rest
      | "absThm" =>
          let (thO, st) ← pop1 st          -- ⊦ t = u  (top)
          let (vO, st) ← pop1 st
          let t ← thO.asThm
          let (_, _, fv) ← vO.asVar
          let proof ← mkFunExt (← mkLambdaFVars #[fv] t.proof)
          let concl ← inferType proof
          push_thm st { hyps := t.hyps, concl, proof } rest
      | "eqMp" =>
          let (fO, st) ← pop1 st           -- ⊦ φ   (top)
          let (fgO, st) ← pop1 st          -- ⊦ φ = ψ
          let f ← fO.asThm; let fg ← fgO.asThm
          let proof ← mkEqMP fg.proof f.proof
          let concl ← inferType proof
          push_thm st { hyps := hUnion f.hyps fg.hyps, concl, proof } rest
      | "deductAntisym" =>
          let (t1O, st) ← pop1 st          -- ⊦ p  (top)
          let (t2O, st) ← pop1 st          -- ⊦ q
          let t1 ← t1O.asThm; let t2 ← t2O.asThm
          let p := t1.concl; let q := t2.concl
          let hp? ← findHyp t2.hyps p
          let hq? ← findHyp t1.hyps q
          -- p → q : discharge the hyp `p` (if present) from t2's proof of q
          let pq ← (match hp? with
                    | some fv => mkLambdaFVars #[fv] t2.proof
                    | none => withLocalDeclD `hp p fun hp => mkLambdaFVars #[hp] t2.proof)
          -- q → p : discharge the hyp `q` (if present) from t1's proof of p
          let qp ← (match hq? with
                    | some fv => mkLambdaFVars #[fv] t1.proof
                    | none => withLocalDeclD `hq q fun hq => mkLambdaFVars #[hq] t1.proof)
          -- The reference reader's DEDUCT_ANTISYM is
          --   IMP_ANTISYM_RULE (DISCH c2 th1) (DISCH c1 th2)  ⟹  ⊦ c2 = c1,
          -- i.e. the BELOW operand's conclusion on the LEFT: result is `q = p`.
          let proof ← mkPropExt (← mkAppM ``Iff.intro #[qp, pq])
          let concl ← inferType proof
          let h1 := t1.hyps.filter (fun h => match hq? with | some x => h.fvarId! != x.fvarId! | none => true)
          let h2 := t2.hyps.filter (fun h => match hp? with | some x => h.fvarId! != x.fvarId! | none => true)
          push_thm st { hyps := hUnion h1 h2, concl, proof } rest
      | "subst" =>
          let (thO, st) ← pop1 st          -- theorem on top
          let (subO, st) ← pop1 st
          let th ← thO.asThm
          let sub ← subO.asList
          let tysO ← sub[0]!.asList
          let tmsO ← sub[1]!.asList
          let mut αfvars : Array Expr := #[]
          let mut Ttys   : Array Expr := #[]
          for e in tysO do
            let pr ← e.asList          -- [Name a, Type t]
            let a ← pr[0]!.asName
            let t ← pr[1]!.asType
            match st.tyvars.find? (·.1 == a) with
            | some (_, fv) => αfvars := αfvars.push fv; Ttys := Ttys.push t
            | none => pure ()          -- type var not in scope ⇒ substitution is a no-op for it
          let mut vfvars : Array Expr := #[]
          let mut tterms : Array Expr := #[]
          for e in tmsO do
            let pr ← e.asList          -- [Var v, Term t]
            let (_, _, fv) ← pr[0]!.asVar
            let t ← pr[1]!.asTerm
            vfvars := vfvars.push fv; tterms := tterms.push t
          -- base substitution (types + the article-provided term substitutions)
          let baseOld := αfvars ++ vfvars
          let baseNew := Ttys ++ tterms
          if αfvars.isEmpty && th.hyps.isEmpty then
            -- pure term substitution, no hypotheses: a direct replaceFVars
            push_thm st { hyps := #[], concl := th.concl.replaceFVars baseOld baseNew,
                          proof := th.proof.replaceFVars baseOld baseNew } rest
          else
            -- INST_TYPE changes the TYPES of the theorem's term variables and
            -- hypotheses. Lean fvars have fixed types, so we RE-INTERN each affected
            -- variable/hypothesis at its substituted type (matching the identity the
            -- article's later commands will use) and rewrite the proof accordingly.
            let appearing := st.tmvars.filter
              (fun (_, _, w) => th.proof.containsFVar w.fvarId! || th.concl.containsFVar w.fvarId!)
            let toRefresh := appearing.filter
              (fun (_, τ, _) => αfvars.any (fun a => τ.containsFVar a.fvarId!))
            let oldWs := toRefresh.map (fun (_, _, w) => w)
            let specs := toRefresh.map (fun (nm, τ, _) => (nm, τ.replaceFVars αfvars Ttys))
            let oldHs := th.hyps
            withEnsuredTmvars st specs fun st newWs => do
              -- hyp statements must be substituted with BOTH the base subst AND the
              -- term-variable refresh (a hyp may mention a refreshed variable).
              let hOld := baseOld ++ oldWs
              let hNew := baseNew ++ newWs
              let newHstmts ← oldHs.mapM (fun h => do return (← inferType h).replaceFVars hOld hNew)
              withEnsuredHyps st newHstmts fun st newHs => do
                let allOld := baseOld ++ oldWs ++ oldHs
                let allNew := baseNew ++ newWs ++ newHs
                let newThm : Thm := { hyps := newHs, concl := th.concl.replaceFVars allOld allNew,
                                      proof := th.proof.replaceFVars allOld allNew }
                push_thm st newThm rest
      | "defineConst" =>
          let (tO, st) ← pop1 st           -- defining term on top
          let (nO, st) ← pop1 st
          let t ← tO.asTerm
          let nm ← nO.asName
          let ty ← inferType t
          -- only closed (monomorphic, variable-free) definitions in this build
          let leanNm := Name.mkSimple s!"otdef_{st.count}"
          addDecl (.defnDecl { name := leanNm, levelParams := [], type := ty, value := t, hints := .abbrev, safety := .safe })
          let cst := mkConst leanNm
          let concl ← mkEq cst t
          let proof ← mkExpectedTypeHint (← mkEqRefl cst) concl
          let st := { st with defined := st.defined.push (nm, leanNm), count := st.count + 1 }
          -- push defining thm, then the const object
          go { st with stk := (st.stk.push (.thm { hyps := #[], concl, proof })).push (.const nm) } rest
      | "axiom" =>
          let (tO, st) ← pop1 st           -- concl term on top
          let (tsO, st) ← pop1 st          -- hyp list
          let φ ← tO.asTerm
          let hyps ← tsO.asList
          unless hyps.isEmpty do
            throwError "axiom: hypotheses on an axiom are not supported (got {hyps.size})"
          match ← tryDischarge φ with
          | some proof =>
              logInfo m!"axiom gate: discharged ⊦ {← ppExpr φ}"
              push_thm st { hyps := #[], concl := φ, proof } rest
          | none =>
              throwError m!"AXIOM GATE (fail-closed): refusing undischarged axiom\n  ⊦ {← ppExpr φ}\nNot defeq to any theorem in the discharge table {dischargeNames}. A fall-through to a fresh Lean `axiom` is forbidden."
      | "thm" =>
          let (cO, st) ← pop1 st           -- desired conclusion term on top
          let (lsO, st) ← pop1 st          -- desired hyp list
          let (thObj, st) ← pop1 st
          let c ← cO.asTerm
          let ls ← lsO.asList
          let th ← thObj.asThm
          unless ls.isEmpty do
            throwError "thm: exporting a theorem with non-empty hypotheses is not supported here (Γ has {ls.size})"
          -- ascribe the proof to the desired (alpha/defeq) conclusion
          let proof0 ← mkExpectedTypeHint th.proof c
          -- close over remaining hypotheses (as implications) and free vars.
          let hypFvars := th.hyps
          let hypTypes ← hypFvars.mapM (fun h => do return (← inferType h))
          let occursE (fv : Expr) (es : Array Expr) : Bool := es.any (·.containsFVar fv.fvarId!)
          -- term vars occurring directly in the statement/proof
          let tmClosed := st.tmvars.filter (fun (_, _, fv) => occursE fv (#[c, proof0] ++ hypTypes))
          let tmClose := tmClosed.map (fun (_, _, fv) => fv)
          let tmTypes := tmClosed.map (fun (_, ty, _) => ty)
          -- type vars occurring in the statement/proof OR in a kept term-var/hyp type
          let tyClose := (st.tyvars.map (·.2)).filter
            (fun fv => occursE fv (#[c, proof0] ++ hypTypes ++ tmTypes))
          let closeVars := tyClose ++ tmClose ++ hypFvars
          let stmt ← mkForallFVars closeVars c
          let val  ← mkLambdaFVars closeVars proof0
          -- pick a globally-fresh name (multiple articles / theorems may co-exist)
          let mut name := `OTImport ++ Name.mkSimple s!"imported{st.count}"
          let mut k := 0
          while (← getEnv).contains name do
            k := k + 1
            name := `OTImport ++ Name.mkSimple s!"imported{st.count}_{k}"
          addDecl (.thmDecl { name := name, levelParams := [], type := stmt, value := val })
          -- axiom-clean gate on the OUTPUT
          let axs ← collectAxioms name
          let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
          let bad := axs.filter (fun a => !allowed.contains a)
          unless bad.isEmpty do
            throwError m!"axiom-clean gate: imported theorem depends on disallowed axioms {bad}"
          logInfo m!"imported (kernel-checked, axioms ⊆ classical set): {name} : {← ppExpr stmt}"
          go { st with count := st.count + 1 } rest
      | other => throwError "unknown command: {other}"
where
  /-- push a plain object and continue (avoids re-taking `rest` in every branch). -/
  push_st (st : St) (o : Obj) (rest : List String) : TermElabM Unit :=
    go { st with stk := st.stk.push o } rest
  push_thm (st : St) (t : Thm) (rest : List String) : TermElabM Unit :=
    go { st with stk := st.stk.push (.thm t) } rest
  findHyp (hyps : Array Expr) (stmt : Expr) : MetaM (Option Expr) := do
    for h in hyps do
      if ← isDefEq (← inferType h) stmt then return some h
    return none

/- ======================================================================
   Entry points.
   ====================================================================== -/

/-- tokenize an article string (one token per non-empty, non-comment line). -/
def tokenize (s : String) : List String :=
  (s.splitOn "\n").filterMap fun ln =>
    let t := if ln.endsWith "\r" then String.ofList ln.toList.dropLast else ln
    if t.isEmpty || t.startsWith "#" then none else some t

def importArticle (label : String) (art : String) : CommandElabM Unit := do
  logInfo m!"=== importing article: {label} ==="
  liftTermElabM do go {} (tokenize art)

/-- expect the import to FAIL (used to test the axiom gate's reject path). -/
def importArticleExpectFail (label : String) (art : String) : CommandElabM Unit := do
  try
    liftTermElabM do go {} (tokenize art)
    logError m!"REJECT-TEST FAILED: article {label} was accepted but should have been rejected"
  catch e =>
    logInfo m!"reject-test OK: article {label} correctly rejected: {← e.toMessageData.toString}"

end OTImport

/- ======================================================================
   Drivers / demonstrations.
   ====================================================================== -/

/-- axiom-gate ACCEPT: assert `⊦ T` (discharges to `d_true`) and export it. Also
    exercises the real parser + dictionary + const/constTerm/opType/typeOp/thm. -/
def acceptArticle : String := String.intercalate "\n"
  ["6","version","nil","\"Data.Bool.T\"","const","\"bool\"","typeOp","nil","opType",
   "constTerm","axiom","nil","\"Data.Bool.T\"","const","\"bool\"","typeOp","nil",
   "opType","constTerm","thm"]

/-- axiom-gate REJECT: a rogue `axiom ⊦ p` (a bare bool variable) is NOT in the
    discharge table and MUST be refused (fail-closed). -/
def rogueArticle : String := String.intercalate "\n"
  ["6","version","nil","\"p\"","\"bool\"","typeOp","nil","opType","var","varTerm","axiom"]

run_cmd OTImport.importArticle "axiom-gate ACCEPT (⊦ T)" acceptArticle

run_cmd OTImport.importArticleExpectFail "axiom-gate REJECT (rogue ⊦ p)" rogueArticle

-- Import a real article from the path in `$OT_ARTICLE` (e.g. prodWitness.art).
run_cmd do
  match ← IO.getEnv "OT_ARTICLE" with
  | some path =>
      let s ← IO.FS.readFile path
      OTImport.importArticle s!"file:{path}" s
  | none => logInfo "OT_ARTICLE not set; skipping real-article import"
