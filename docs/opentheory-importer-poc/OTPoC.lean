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

-- Real OpenTheory articles replay tens of thousands of primitive steps in a single
-- elaboration; the default heartbeat ceiling is for interactive proofs, not this.
set_option maxHeartbeats 0

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

/-- HOL Light's `EXISTS_DEF`: `? = \P. P ((@) P)` — existence via Hilbert choice.
    True in Lean over `Classical.epsilon`; needs the type nonempty (see below). -/
theorem d_exists_select {A : Type} [Nonempty A] :
    (@Exists A) = (fun (P : A → Prop) => P (Classical.epsilon P)) := by
  funext P
  apply propext
  apply Iff.intro
  · intro h; exact Classical.epsilon_spec h
  · intro h; exact ⟨Classical.epsilon P, h⟩

/-- A `bool`-theory clause: `!t. (t <=> T) <=> t`, i.e. `(t = True) = t` on `Prop`. -/
theorem d_t_eq : ∀ (t : Prop), (t = True) = t := by
  intro t; apply propext
  exact Iff.intro (fun h => of_eq_true h) (fun h => eq_true h)

/-- The `bool`-theory clause `!t. (!x:A. t) = t`. This is the assumption that
    WITNESSES HOL's every-type-is-nonempty: it is FALSE in Lean for an empty `A`
    (then `∀x:A,t` is `True` but `t` may be `False`). Discharged only with
    `[Nonempty A]`, which the encoding now threads onto every HOL type variable. -/
theorem d_forall_triv {A : Type} [Nonempty A] : ∀ (t : Prop), (∀ _ : A, t) = t := by
  intro t; apply propext
  apply Iff.intro
  · intro h; exact h (Classical.choice inferInstance)
  · intro h _; exact h

/-- OpenTheory base axiom `axiom-extensionality`: `⊦ !(t:A→B). (\x. t x) = t`.
    Function extensionality in eta form; Lean has definitional eta, so `rfl`.
    (Type-variable domains/codomains are `Type` fvars; `Prop` is also an element
    of `Type`, so instantiating either at `bool` stays well-typed.) -/
theorem d_eta {A B : Type} : ∀ (t : A → B), (fun x => t x) = t := fun _ => rfl

/-- OpenTheory base axiom `axiom-choice` (Hilbert select):
    `⊦ !(p:A→bool)(x:A). p x ⇒ p ((select) p)`.
    `select` is `Classical.epsilon`; needs `A` nonempty (HOL's every-type-nonempty,
    which the encoding threads onto every type variable). -/
theorem d_select_ax {A : Type} [Nonempty A] :
    ∀ (p : A → Prop) (x : A), p x → p (Classical.epsilon p) :=
  fun _ x hpx => Classical.epsilon_spec ⟨x, hpx⟩

/-- Extensionality in the form a bool-INLINING article produces it: the composed
    `pair`/`sum`/`option` articles define `!` and `T` themselves (bool-def), so the
    axiom is `!(\d. (\e. d e) = d)` with `!` = `\P. P = \x.T` and `T` = `(\x.x)=(\x.x)`
    inlined. After the outer beta step (which `isDefEq` performs) this is the
    equation below. `d_eta` (native `∀`) covers the bool-ASSUMING article style. -/
theorem d_eta_bd {A B : Type} :
    (fun d : A → B => (fun e => d e) = d)
      = (fun _ : A → B => (fun c : Prop => c) = (fun c : Prop => c)) := by
  funext d; exact propext ⟨fun _ => rfl, fun _ => rfl⟩

/-- The choice axiom in the SAME fully-bool-inlined form: `!(\d. !(\g. d g ⇒ d (ε d)))`
    with `!` = `\P.P=\x.T`, `⇒` = `\p q. (p∧q)=p`, `∧` = `\p q. (\f.f p q)=\f.f T T`, and
    `T` = `(\x.x)=(\x.x)` all inlined (`select` = `Classical.epsilon`). The proof
    re-establishes that this inlined encoding is the Hilbert choice property. -/
theorem d_select_bd {A : Type} [Nonempty A] :
    (fun d : A → Prop =>
        (fun g : A =>
            ((fun l : Prop → Prop → Prop => l (d g) (d (Classical.epsilon d)))
                = (fun m : Prop → Prop → Prop =>
                    m ((fun c : Prop => c) = (fun c : Prop => c))
                      ((fun c : Prop => c) = (fun c : Prop => c))))
              = d g)
          = (fun _ : A => (fun c : Prop => c) = (fun c : Prop => c)))
      = (fun _ : A → Prop => (fun c : Prop => c) = (fun c : Prop => c)) := by
  funext d
  apply propext; constructor
  · intro _; rfl
  · intro _
    funext g
    apply propext; constructor
    · intro _; rfl
    · intro _
      -- goal: the inlined `d g ⇒ d (ε d)`, i.e. `(AND (d g) (d (ε d))) = d g`
      apply propext; constructor
      · -- (AND …) = d g  ⟹  d g   (apply both sides to `fun a _ => a`)
        intro hX
        exact cast (congrFun hX (fun a _ : Prop => a)).symm rfl
      · -- d g ⟹ (AND …) = d g
        intro hdg
        have hde : d (Classical.epsilon d) := Classical.epsilon_spec ⟨g, hdg⟩
        funext l
        have e1 : d g = ((fun c : Prop => c) = (fun c : Prop => c)) :=
          propext ⟨fun _ => rfl, fun _ => hdg⟩
        have e2 : d (Classical.epsilon d) = ((fun c : Prop => c) = (fun c : Prop => c)) :=
          propext ⟨fun _ => rfl, fun _ => hde⟩
        rw [e1, e2]

/-- Names of the discharge theorems. `axiom` may resolve to exactly these. -/
def dischargeNames : List Name :=
  [``d_true, ``d_and_def, ``d_imp_def, ``d_forall_def, ``d_exists_def,
   ``d_exists_select, ``d_t_eq, ``d_forall_triv, ``d_eta, ``d_select_ax,
   ``d_eta_bd, ``d_select_bd]

/- ======================================================================
   Generic realization of HOL `defineTypeOp` (carve a non-empty subset).

   A HOL type definition supplies `⊦ φ t` (a witness that the predicate `φ` on
   an existing type `σ` is satisfiable) and introduces a new type isomorphic to
   `{x // φ x}` with a total `abs : σ → newT` and `rep : newT → σ`. We realize
   `newT := Subtype φ`, `rep := Subtype.val`, and `abs` sending off-predicate
   junk to the witness (HOL's `abs` is total and underspecified off `φ`). The
   two OpenTheory round-trip theorems are proved generically here, once. -/

/-- `abs`: total; identity-with-proof on `φ`, junk (= the witness) off `φ`. -/
noncomputable def holAbs {σ : Type} (φ : σ → Prop) (w : σ) (hw : φ w) (r : σ) : {x // φ x} := by
  classical
  exact if h : φ r then ⟨r, h⟩ else ⟨w, hw⟩

/-- `rep`: the underlying value. -/
def holRep {σ : Type} (φ : σ → Prop) (a : {x // φ x}) : σ := a.val

theorem holAbs_val_pos {σ : Type} (φ : σ → Prop) (w : σ) (hw : φ w) (r : σ) (h : φ r) :
    (holAbs φ w hw r).val = r := by
  unfold holAbs
  rw [dif_pos h]

/-- OpenTheory `absRep`: `(λa. abs (rep a)) = λa. a`. -/
theorem hol_abs_rep {σ : Type} (φ : σ → Prop) (w : σ) (hw : φ w) :
    (fun a : {x // φ x} => holAbs φ w hw (holRep φ a)) = (fun a => a) := by
  funext a
  show holAbs φ w hw a.val = a
  apply Subtype.ext
  exact holAbs_val_pos φ w hw a.val a.property

/-- OpenTheory `repAbs`: `(λr. rep (abs r) = r) = λr. φ r`. -/
theorem hol_rep_abs {σ : Type} (φ : σ → Prop) (w : σ) (hw : φ w) :
    (fun r => holRep φ (holAbs φ w hw r) = r) = (fun r => φ r) := by
  funext r
  apply propext
  apply Iff.intro
  · intro h
    have hp := (holAbs φ w hw r).property
    have hv : (holAbs φ w hw r).val = r := h
    rwa [hv] at hp
  · intro h
    show (holAbs φ w hw r).val = r
    exact holAbs_val_pos φ w hw r h

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
  tyvars  : Array (String × Expr × Expr) := #[]   -- name × (A : Type) × (hA : Nonempty A) fvar
  tmvars  : Array (String × Expr × Expr) := #[]   -- name × encoded-type × fvar
  hyps    : Array (Expr × Expr) := #[]            -- statement × hyp fvar
  defined : Array (String × Expr) := #[]          -- MONOMORPHIC const -> its meaning Expr
  -- POLYMORPHIC const: name × tyVar-fvars × their Nonempty-witness fvars × generic
  -- type × meaning (all with the tyVar/Nonempty fvars free). Instantiated per use
  -- site by matching the generic type against the `constTerm` type (INST_TYPE).
  polyDefined : Array (String × Array Expr × Array Expr × Expr × Expr) := #[]
  -- OT tyop name -> tyVar-fvars × carrier template (arity = tyVars.size; empty = arity 0)
  definedTyops : Array (String × Array Expr × Expr) := #[]
  tyNonempty : Array (Expr × Expr) := #[]         -- arity-0 carrier type × Nonempty proof
  -- parameterized carrier Nonempty: tyVars × their Nonempty fvars × carrier template
  -- × Nonempty(carrier) template (all with tyVar/Nonempty fvars free)
  polyTyNonempty : Array (Array Expr × Array Expr × Expr × Expr) := #[]
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

/-- Match a template type `gen` (with the given `tyVars` free) against a concrete
    `target`, returning each tyVar's instantiation (aligned to `tyVars`), or `none`.
    Uses fresh metavars + the kernel unifier (`isDefEq`). Type-variable fvars live in
    `Type` (= `Sort 1`); so do the metavars, and every encoded HOL type (`Prop`,
    `Nat`, fvars, `→`, `Subtype _`) is an element of `Type`, so all match. -/
def matchTyVars (tyVars : Array Expr) (gen target : Expr) : MetaM (Option (Array Expr)) := do
  let mvars ← tyVars.mapM (fun _ => mkFreshExprMVar (mkSort (Level.succ Level.zero)))
  let gen' := gen.replaceFVars tyVars mvars
  if ← isDefEq gen' target then
    (some ·) <$> mvars.mapM instantiateMVars
  else
    return none

/-- Build a `Nonempty τ` proof for an encoded type `τ`, threading HOL's
    every-type-is-nonempty invariant. Bare type variables carry their own
    `Nonempty` witness in `st.tyvars`; defined types (subtypes) carry theirs in
    `st.tyNonempty` (arity 0) or `st.polyTyNonempty` (parameterized, matched +
    instantiated); `Prop`/`Nat`/`→` are structural. -/
partial def mkNonempty (st : St) (τ : Expr) : MetaM Expr := do
  if τ.isFVar then
    if let some (_, _, hA) := st.tyvars.find? (fun (_, a, _) => a == τ) then
      return hA
  for (carrier, wit) in st.tyNonempty do
    if ← isDefEq τ carrier then return wit
  -- parameterized defined carriers: match `Subtype p[tyVars]` against τ, then
  -- instantiate its `Nonempty` witness (tyVars ↦ args, Nonempty-fvars ↦ Nonempty args).
  for (tyVars, hAs, carrierT, neT) in st.polyTyNonempty do
    match ← matchTyVars tyVars carrierT τ with
    | some args =>
        let nes ← args.mapM (fun a => mkNonempty st a)
        return neT.replaceFVars (tyVars ++ hAs) (args ++ nes)
    | none => pure ()
  if τ == mkSort Level.zero then
    return ← mkAppM ``Nonempty.intro #[mkConst ``True]
  if τ == mkConst ``Nat then
    return ← mkAppM ``Nonempty.intro #[mkConst ``Nat.zero]
  match τ with
  | .forallE _ a b _ =>
      if b.hasLooseBVars then throwError "mkNonempty: dependent function type {τ}"
      let wB ← mkNonempty st b
      let bElem ← mkAppM ``Classical.choice #[wB]
      let f ← withLocalDeclD `x a fun x => mkLambdaFVars #[x] bElem
      return ← mkAppM ``Nonempty.intro #[f]
  | _ =>
      match ← synthInstance? (← mkAppM ``Nonempty #[τ]) with
      | some e => return e
      | none => throwError "mkNonempty: cannot construct Nonempty for {τ}"

/-- Instantiate a polymorphic body at `args` for `tyVars` (their `hAs` Nonempty
    witnesses traveling as `Nonempty args_i`). This IS HOL's INST_TYPE, and it must
    carry the `Nonempty` witnesses or a `select`/`epsilon` inside `body` keeps a
    `Nonempty tyVar` argument at the substituted type and the kernel rejects it. -/
def instPoly (st : St) (tyVars hAs : Array Expr) (args : Array Expr) (body : Expr) : MetaM Expr := do
  let nes ← args.mapM (fun a => mkNonempty st a)
  return body.replaceFVars (tyVars ++ hAs) (args ++ nes)

/-- Interpret an applied HOL type operator as a native Lean type `Expr`. -/
def interpTyop (st : St) (op : String) (args : Array Expr) : MetaM Expr := do
  if let some (_, tyVars, carrier) := st.definedTyops.find? (·.1 == op) then
    if args.size == tyVars.size then
      -- direct type-arg substitution (carrier is a type expr; no Nonempty needed here)
      return carrier.replaceFVars tyVars args
    else
      throwError "interpTyop: arity mismatch for defined type operator {op}: expected {tyVars.size}, got {args.size}"
  match op, args with
  | "bool", #[]    => pure (mkSort Level.zero)      -- Prop
  | "ind",  #[]    => pure (mkConst ``Nat)          -- fixed infinite carrier
  | "->",   #[a,b] => mkArrow a b
  | "fun",  #[a,b] => mkArrow a b
  | _, _ => throwError "interpTyop: unsupported type operator {op}/{args.size}"

/-- Interpret a HOL constant at a given (already-encoded) monomorphic type. -/
def interpConst (st : St) (nm : String) (ty : Expr) : MetaM Expr := do
  if let some (_, e) := st.defined.find? (·.1 == nm) then
    return e
  -- polymorphic const (from a polymorphic defineConst / an abs|rep of a
  -- parameterized type): match its generic type against the requested use type to
  -- recover the type instantiation, then INST_TYPE its meaning.
  if let some (_, tyVars, hAs, genTy, meaning) := st.polyDefined.find? (·.1 == nm) then
    match ← matchTyVars tyVars genTy ty with
    | some args => return ← instPoly st tyVars hAs args meaning
    | none => throwError "interpConst: cannot instantiate polymorphic const {nm}:\n  generic {genTy}\n  at use  {ty}"
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
      let inst ← mkNonempty st A
      mkAppOptM ``Classical.epsilon #[A, inst]
  | _ => throwError "interpConst: unsupported constant {nm}"

/- ======================================================================
   The axiom gate.
   ====================================================================== -/

/-- Peel a theorem type's leading NON-default binders (type params, instances)
    into fresh metavars, stopping at the first explicit binder. -/
partial def peelImplicit (ty : Expr) (mvars : Array Expr) : MetaM (Expr × Array Expr) := do
  match ty with
  | .forallE _ d b bi =>
      match bi with
      | .default => return (ty, mvars)
      | _ =>
          let mv ← mkFreshExprMVar d
          peelImplicit (b.instantiate1 mv) (mvars.push mv)
  | _ => return (ty, mvars)

/-- Try to discharge an `axiom` command's assertion `concl` (with empty Γ) to a
    pre-proved Lean theorem. Returns the proof term, or `none` (⇒ hard error).

    Only the discharge theorem's leading NON-default binders (its type
    parameters and `[Nonempty _]` instances) are turned into metavars; the first
    explicit binder stops the peel so a formula-level HOL `!` (encoded as a Lean
    `∀`) is matched, not stripped. Instance metavars that proof-irrelevance
    leaves unassigned after unification are then synthesized from the local
    context (where each HOL type variable's `Nonempty` witness lives). -/
def tryDischarge (concl : Expr) : MetaM (Option Expr) := do
  for dn in dischargeNames do
    let ci ← getConstInfo dn
    let (dConcl, mvars) ← peelImplicit ci.type #[]
    if ← isDefEq dConcl concl then
      for mv in mvars do
        let mvId := mv.mvarId!
        unless ← mvId.isAssigned do
          if let some inst ← synthInstance? (← inferType mv) then
            mvId.assign inst
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
          | some (_, fv, _) => cont { st with stk := st.stk.push (.type fv) }
          | none =>
            -- A HOL type variable maps to a Lean `Type` fvar TOGETHER with a
            -- `[Nonempty A]` instance: HOL types are all inhabited, and the
            -- `bool` theory's `!t.(!x:A.t)=t` / `?=\p.p(εp)` assumptions (and
            -- `select`) are unsound over an empty carrier.
            withLocalDeclD (Name.mkSimple nm) (mkSort (Level.succ Level.zero)) fun fv => do
              let ne ← mkAppM ``Nonempty #[fv]
              withLocalDecl (Name.mkSimple s!"ne_{nm}") .instImplicit ne fun hA =>
                go { st with stk := st.stk.push (.type fv), tyvars := st.tyvars.push (nm, fv, hA) } rest
      | "opType" =>
          let (lst, st) ← pop1 st         -- arg list on top
          let (opO, st) ← pop1 st
          let argObjs ← lst.asList
          let args ← argObjs.mapM (fun o => do return (← o.asType))
          let ty ← interpTyop st (← opO.asTyop) args
          cont { st with stk := st.stk.push (.type ty) }
      | "const" =>
          let (n, st) ← pop1 st
          push_st st (.const (← n.asName)) rest
      | "constTerm" =>
          let (tyO, st) ← pop1 st          -- type on top
          let (cO, st) ← pop1 st
          let e ← interpConst st (← cO.asConst) (← tyO.asType)
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
          -- Each HOL type variable `A` carries an instance witness `hA : Nonempty A`.
          -- When `A := τ`, that witness must travel too (`hA ↦ Nonempty τ` proof),
          -- else a `Classical.epsilon`/`select` in the proof keeps a `Nonempty A`
          -- argument at the substituted `τ` and the kernel rejects it.
          let mut neOld : Array Expr := #[]
          let mut neNew : Array Expr := #[]
          for e in tysO do
            let pr ← e.asList          -- [Name a, Type t]
            let a ← pr[0]!.asName
            let t ← pr[1]!.asType
            match st.tyvars.find? (·.1 == a) with
            | some (_, fv, hA) =>
                -- Skip an identity type substitution `α := α`: it changes no type
                -- but would spuriously trigger the INST_TYPE re-intern path, which
                -- then clobbers a term substitution of the same variable.
                unless (← isDefEq fv t) do
                  αfvars := αfvars.push fv; Ttys := Ttys.push t
                  neOld := neOld.push hA; neNew := neNew.push (← mkNonempty st t)
            | none => pure ()          -- type var not in scope ⇒ substitution is a no-op for it
          -- Term-substitution redexes, kept as NOMINAL (name, type, residue). HOL
          -- variables are identified by name+type; INST_TYPE re-interning can leave
          -- two Lean fvars with the same (name,type), so `instTerm` below matches by
          -- (name,type), not FVarId — this IS HOL's `INST`.
          let mut redexes : Array (Name × Expr × Expr) := #[]
          for e in tmsO do
            let pr ← e.asList          -- [Var v, Term t]
            let (vnm, vty, _fv) ← pr[0]!.asVar
            let t ← pr[1]!.asTerm
            redexes := redexes.push (Name.mkSimple vnm, vty, t)
          -- Phase 2 (`INST tms`): nominal simultaneous term substitution.
          let instTerm (e : Expr) : MetaM Expr := do
            let mut oldA : Array Expr := #[]
            let mut newA : Array Expr := #[]
            for d in (← getLCtx) do
              unless d.isImplementationDetail do
                for (rn, rt, res) in redexes do
                  if d.userName == rn then
                    if ← isDefEq d.type rt then
                      oldA := oldA.push (.fvar d.fvarId); newA := newA.push res
                      break
            return e.replaceFVars oldA newA
          -- OpenTheory `subst` = `INST_TYPE tys th` (phase 1) THEN `INST tms th`
          -- (phase 2), SEQUENTIALLY. Doing both in one `replaceFVars` lets the
          -- type re-intern of a variable clobber its term substitution, so the
          -- phases are kept separate.
          if αfvars.isEmpty then
            -- No type substitution: re-intern only hyps whose statement changes
            -- under the term subst, then apply the term subst to concl/proof.
            let finalHstmts ← th.hyps.mapM (fun h => do instTerm (← inferType h))
            withEnsuredHyps st finalHstmts fun st newHs => do
              let concl' ← instTerm (th.concl.replaceFVars th.hyps newHs)
              let proof' ← instTerm (th.proof.replaceFVars th.hyps newHs)
              push_thm st { hyps := newHs, concl := concl', proof := proof' } rest
          else
            -- Phase 1 (INST_TYPE): re-intern each term variable / hypothesis whose
            -- TYPE mentions a substituted type variable (Lean fvars have fixed
            -- types), then rewrite. Phase 2 (the term subst) is applied afterwards.
            let appearing := st.tmvars.filter
              (fun (_, _, w) => th.proof.containsFVar w.fvarId! || th.concl.containsFVar w.fvarId!)
            let toRefresh := appearing.filter
              (fun (_, τ, _) => αfvars.any (fun a => τ.containsFVar a.fvarId!))
            let oldWs := toRefresh.map (fun (_, _, w) => w)
            let specs := toRefresh.map (fun (nm, τ, _) => (nm, τ.replaceFVars αfvars Ttys))
            let oldHs := th.hyps
            withEnsuredTmvars st specs fun st newWs => do
              let tyOld := αfvars ++ neOld ++ oldWs
              let tyNew := Ttys ++ neNew ++ newWs
              -- final hyp statements: type subst THEN term subst
              let finalHstmts ← oldHs.mapM (fun h => do instTerm ((← inferType h).replaceFVars tyOld tyNew))
              withEnsuredHyps st finalHstmts fun st newHs => do
                let concl1 := th.concl.replaceFVars (tyOld ++ oldHs) (tyNew ++ newHs)
                let proof1 := th.proof.replaceFVars (tyOld ++ oldHs) (tyNew ++ newHs)
                let concl2 ← instTerm concl1
                let proof2 ← instTerm proof1
                push_thm st { hyps := newHs, concl := concl2, proof := proof2 } rest
      | "sym" =>
          let (tO, st) ← pop1 st            -- ⊦ t = u  (top)
          let t ← tO.asThm
          let proof ← mkEqSymm t.proof
          let concl ← inferType proof
          push_thm st { hyps := t.hyps, concl, proof } rest
      | "trans" =>
          let (t2O, st) ← pop1 st           -- Δ ⊦ b = c  (top)
          let (t1O, st) ← pop1 st           -- Γ ⊦ a = b
          let t1 ← t1O.asThm; let t2 ← t2O.asThm
          let proof ← mkEqTrans t1.proof t2.proof
          let concl ← inferType proof
          push_thm st { hyps := hUnion t1.hyps t2.hyps, concl, proof } rest
      | "proveHyp" =>
          let (t2O, st) ← pop1 st           -- Δ ⊦ ψ  (top)
          let (t1O, st) ← pop1 st           -- Γ ⊦ φ
          let t1 ← t1O.asThm; let t2 ← t2O.asThm
          -- discharge φ (proved by t1) from Δ's hypotheses of t2, if present.
          match ← findHyp t2.hyps t1.concl with
          | some fv =>
              let proof := t2.proof.replaceFVars #[fv] #[t1.proof]
              let remaining := t2.hyps.filter (fun h => h.fvarId! != fv.fvarId!)
              push_thm st { hyps := hUnion t1.hyps remaining, concl := t2.concl, proof } rest
          | none =>
              push_thm st { hyps := hUnion t1.hyps t2.hyps, concl := t2.concl, proof := t2.proof } rest
      | "defineTypeOp" =>
          let (axO, st) ← pop1 st           -- ⊦ φ t  (top: existence witness)
          let (lsO, st) ← pop1 st           -- list of type-variable-arg names A
          let (repO, st) ← pop1 st          -- rep name
          let (absO, st) ← pop1 st          -- abs name
          let (nO, st) ← pop1 st            -- tyop name
          let ax ← axO.asThm
          let ls ← lsO.asList
          let repNm ← repO.asName
          let absNm ← absO.asName
          let opNm ← nO.asName
          unless ax.hyps.isEmpty do
            throwError "defineTypeOp: the existence theorem must have empty hypotheses"
          -- The type-variable args `A₁..Aₙ` (parameters of the new type operator).
          -- Resolve each to its in-scope `Type` fvar and its `Nonempty` witness; a
          -- parameterized type's abs/rep/carrier are polymorphic in exactly these.
          let mut tyVars : Array Expr := #[]
          let mut hAs : Array Expr := #[]
          for a in ls do
            let anm ← a.asName
            match st.tyvars.find? (·.1 == anm) with
            | some (_, fv, hA) => tyVars := tyVars.push fv; hAs := hAs.push hA
            | none => throwError "defineTypeOp: type-variable arg {anm} not in scope"
          let (φ, wit0) ← (match ax.concl with
            | .app f a => pure (f, a)
            | _ => throwError "defineTypeOp: existence theorem is not an application (φ t)")
          -- The existence WITNESS may be SCHEMATIC (free term variables): `⊢ φ t`
          -- allows them (the predicate φ must be closed, but not `t`). HOL's abs is an
          -- OPAQUE constant, so a `\x y. abs (…)` definition stays closed; but we
          -- INLINE abs as `holAbs φ wit proof`, which would leak the witness's free
          -- vars into every constant defined via abs (the pair constructor), breaking
          -- `defineConst`'s closedness. Close the witness: every HOL type is nonempty,
          -- so substitute each free term var by `Classical.choice` of its type. This
          -- only changes the junk-off-φ value (arbitrary), not the round-trip theorems.
          let freeTm := st.tmvars.filter
            (fun (_, _, w) => wit0.containsFVar w.fvarId! || ax.proof.containsFVar w.fvarId!)
          let mut fvs : Array Expr := #[]
          let mut cvs : Array Expr := #[]
          for (_, vty, w) in freeTm do
            fvs := fvs.push w
            cvs := cvs.push (← mkAppM ``Classical.choice #[← mkNonempty st vty])
          let wit := wit0.replaceFVars fvs cvs
          let witPf := ax.proof.replaceFVars fvs cvs
          -- carrier {x // φ x} (with the tyVars free); rep = .val; abs total
          -- (junk = the closed existence witness off-predicate). For arity 0 these are
          -- closed; for arity>0 they carry the tyVars/Nonempty fvars free and are
          -- instantiated per use site (INST_TYPE) by `interpConst`/`interpTyop`.
          let σ ← inferType wit
          let carrier ← mkAppM ``Subtype #[φ]
          let absE ← mkAppM ``holAbs #[φ, wit, witPf]         -- : σ → carrier
          let repE ← mkAppM ``holRep #[φ]                     -- : carrier → σ
          -- ⟨wit, witPf⟩ : Subtype φ — give the predicate explicitly (HO infer
          -- of `p` from `witPf : p wit` is ambiguous).
          let witElem ← mkAppOptM ``Subtype.mk #[some σ, some φ, some wit, some witPf]
          let neCarrier ← mkAppM ``Nonempty.intro #[witElem]
          let absRepPf ← mkAppM ``hol_abs_rep #[φ, wit, witPf]
          let absRepConcl ← inferType absRepPf
          let repAbsPf ← mkAppM ``hol_rep_abs #[φ, wit, witPf]
          let repAbsConcl ← inferType repAbsPf
          let absTy ← inferType absE
          let repTy ← inferType repE
          let st := { st with definedTyops := st.definedTyops.push (opNm, tyVars, carrier) }
          let st :=
            if tyVars.isEmpty then
              { st with defined := (st.defined.push (absNm, absE)).push (repNm, repE),
                        tyNonempty := st.tyNonempty.push (carrier, neCarrier) }
            else
              { st with
                polyDefined := (st.polyDefined.push (absNm, tyVars, hAs, absTy, absE)).push
                                 (repNm, tyVars, hAs, repTy, repE),
                polyTyNonempty := st.polyTyNonempty.push (tyVars, hAs, carrier, neCarrier) }
          let stk := (((( st.stk.push (.tyop opNm)).push (.const absNm)).push (.const repNm)).push
              (.thm { hyps := #[], concl := absRepConcl, proof := absRepPf })).push
              (.thm { hyps := #[], concl := repAbsConcl, proof := repAbsPf })
          go { st with stk } rest
      | "defineConst" =>
          let (tO, st) ← pop1 st           -- defining term on top
          let (nO, st) ← pop1 st
          let t ← tO.asTerm
          let nm ← nO.asName
          -- The spec forbids free TERM variables. Free TYPE variables (a
          -- polymorphic constant) are a labeled residual — this build inlines
          -- the meaning, which is faithful only for a monomorphic definition.
          let offenders := st.tmvars.filter (fun (_, _, w) => t.containsFVar w.fvarId!)
          unless offenders.isEmpty do
            throwError m!"defineConst {nm}: defining term has free term variable(s) {offenders.map (·.1)}\n  term: {← ppExpr t}"
          -- Free TYPE variables ⇒ a POLYMORPHIC constant. We inline the meaning `t`
          -- and record it as polymorphic in exactly its free type-variable fvars, so
          -- each use site (`constTerm` at a monomorphic type) is instantiated by
          -- `interpConst`. Monomorphic (no free tyvars) stays in `defined`.
          let mut tyVars : Array Expr := #[]
          let mut hAs : Array Expr := #[]
          for (_, a, hA) in st.tyvars do
            if t.containsFVar a.fvarId! then tyVars := tyVars.push a; hAs := hAs.push hA
          -- inline: the new constant IS `t`; the defining theorem `⊦ c = t` is `⊦ t = t`.
          let concl ← mkEq t t
          let proof ← mkExpectedTypeHint (← mkEqRefl t) concl
          let genTy ← inferType t
          let st :=
            if tyVars.isEmpty then { st with defined := st.defined.push (nm, t) }
            else { st with polyDefined := st.polyDefined.push (nm, tyVars, hAs, genTy, t) }
          -- push order per the reader/spec: Const c (below), then Thm (⊦ c = t) on top.
          go { st with stk := (st.stk.push (.const nm)).push (.thm { hyps := #[], concl, proof }) } rest
      | "hdTl" =>
          -- split a list: push head (below) then tail (on top), per the reader.
          let (lO, st) ← pop1 st
          let l ← lO.asList
          unless l.size > 0 do throwError "hdTl: empty list"
          cont { st with stk := (st.stk.push l[0]!).push (.list (l.extract 1 l.size)) }
      | "defineConstList" =>
          -- Simultaneously define constants from a theorem whose hypotheses are the
          -- defining equations `v_i = tm_i`; output = the conclusion with each `v_i`
          -- replaced by its (inlined) constant and those hyps discharged by refl.
          -- This IS Rule.defineConstList (subst {v_i↦c_i} then proveHyp each def).
          let (thO, st) ← pop1 st          -- theorem (top)
          let (lO, st) ← pop1 st           -- list of [Name, Var] pairs (below)
          let th ← thO.asThm
          let nvs ← lO.asList
          -- collect (varFvar, hypFvar, defining-term) from the theorem's hyps
          let mut hypInfo : Array (Expr × Expr × Expr) := #[]
          for h in th.hyps do
            let (_, lhs, rhs) ← destEq (← inferType h)
            hypInfo := hypInfo.push (lhs, h, rhs)
          let mut consts : Array Obj := #[]
          let mut oldVars : Array Expr := #[]     -- the var fvars v_i
          let mut newTms : Array Expr := #[]      -- their defining terms tm_i
          let mut oldHyps : Array Expr := #[]     -- the hyp fvars (v_i = tm_i)
          let mut newHypPfs : Array Expr := #[]   -- refl proofs (tm_i = tm_i)
          let mut st := st
          for nv in nvs do
            let elem ← nv.asList              -- [Name, Var]
            unless elem.size == 2 do throwError "defineConstList: expected a [name, var] pair"
            let nm ← elem[0]!.asName
            let (_, _, vfv) ← elem[1]!.asVar
            let some (_, hfv, tm) := hypInfo.find? (fun (v, _, _) => v == vfv)
              | throwError "defineConstList: no defining hypothesis for constant {nm}"
            -- define const nm := tm (polymorphic if tm has free type variables)
            let mut tyVars : Array Expr := #[]
            let mut hAsv : Array Expr := #[]
            for (_, a, hA) in st.tyvars do
              if tm.containsFVar a.fvarId! then tyVars := tyVars.push a; hAsv := hAsv.push hA
            let genTm ← inferType tm
            st := if tyVars.isEmpty then { st with defined := st.defined.push (nm, tm) }
                  else { st with polyDefined := st.polyDefined.push (nm, tyVars, hAsv, genTm, tm) }
            consts := consts.push (.const nm)
            oldVars := oldVars.push vfv
            newTms := newTms.push tm
            oldHyps := oldHyps.push hfv
            newHypPfs := newHypPfs.push (← mkEqRefl tm)
          let concl' := th.concl.replaceFVars (oldVars ++ oldHyps) (newTms ++ newHypPfs)
          let proof' := th.proof.replaceFVars (oldVars ++ oldHyps) (newTms ++ newHypPfs)
          -- push: List of constants (below), then the specification Thm (on top).
          let stk := (st.stk.push (.list consts)).push
              (.thm { hyps := #[], concl := concl', proof := proof' })
          go { st with stk } rest
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
          -- Non-empty declared Γ is supported: the proof's remaining hypothesis fvars
          -- (`th.hyps`, = Γ for a well-formed article) are closed as implications
          -- below, so the export is `⊢ ⋀Γ → c`.
          unless th.hyps.size == ls.size do
            throwError "thm: declared Γ ({ls.size}) disagrees with the proof's open hypotheses ({th.hyps.size})"
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
          -- type vars occurring anywhere (statement/proof/kept term-var+hyp types),
          -- plus their `[Nonempty A]` witness when the proof actually uses it. `A`
          -- precedes `hA`, and both precede the term vars/hyps that depend on them.
          let occSet := #[c, proof0] ++ hypTypes ++ tmTypes
          let mut tyClose : Array Expr := #[]
          for (_, A, hA) in st.tyvars do
            let aUsed := occursE A occSet
            let hUsed := occursE hA occSet
            if aUsed || hUsed then
              tyClose := tyClose.push A
              if hUsed then tyClose := tyClose.push hA
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

/-- axiom-gate REJECT under the NEW machinery: open a type variable `A` (so the
    `Nonempty`-threaded type-var path is active), then assert a rogue `axiom ⊦ p`.
    It is still not defeq to any discharge theorem and MUST be refused. -/
def rogueArticle2 : String := String.intercalate "\n"
  ["6","version",
   "\"A\"","varType","pop",
   "nil",
   "\"p\"","\"bool\"","typeOp","nil","opType","var","varTerm",
   "axiom"]

run_cmd OTImport.importArticleExpectFail "axiom-gate REJECT (rogue ⊦ p, type-var path)" rogueArticle2

-- Bundled real standard-library article: `unit-def` (the OpenTheory `unit` type
-- definition; exercises defineTypeOp/defineConst/sym/trans/proveHyp/pop). Runs
-- when built from the repo root; a no-op elsewhere.
run_cmd do
  let p : System.FilePath := "docs/opentheory-importer-poc/unit-def.art"
  if ← p.pathExists then
    let s ← IO.FS.readFile p
    OTImport.importArticle "unit-def (bundled OpenTheory stdlib)" s
  else logInfo "unit-def.art not found relative to cwd; import via OT_ARTICLE instead"

-- Real PARAMETERIZED-type article: the OpenTheory standard library `pair` theory
-- (product types), composed self-contained (via the `opentheory` tool) so its only
-- assumptions are the two base axioms (extensionality, choice). Exercises
-- PARAMETERIZED (arity-2) defineTypeOp, POLYMORPHIC defineConst, and 30 `thm`
-- exports end-to-end, kernel-checked + axiom-clean.
run_cmd do
  let p : System.FilePath := "docs/opentheory-importer-poc/pair-closed.art"
  if ← p.pathExists then
    let s ← IO.FS.readFile p
    OTImport.importArticle "pair-closed (OpenTheory stdlib product types)" s
  else logInfo "pair-closed.art not found relative to cwd"

-- Import a real article from the path in `$OT_ARTICLE` (e.g. prodWitness.art).
run_cmd do
  match ← IO.getEnv "OT_ARTICLE" with
  | some path =>
      let s ← IO.FS.readFile path
      OTImport.importArticle s!"file:{path}" s
  | none => logInfo "OT_ARTICLE not set; skipping real-article import"
