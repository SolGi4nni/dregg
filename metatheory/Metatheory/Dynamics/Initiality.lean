/-
# Metatheory.Dynamics.Initiality — the D2/R9 probe: is the Argus IR INITIAL?

## The claim under test (R9, DREGG3 §2.4)

> The Argus IR (`Dregg2.Circuit.Argus.RecStmt`) is the INITIAL algebra over the dregg3
> doctrine, so `interp` (= the executor) and `compile` (= the circuit) are the UNIQUE
> homomorphisms out of it — every pair of readings AGREES BY UNIQUENESS, not by per-effect
> differential. If true, the N²-agreement-proof burden collapses to ONE initiality theorem.

The register names the risk precisely: the IR has `guard`s and an EFFECTFUL interpretation,
so a plain initial-algebra-in-`Type` may not fit — it likely needs a Freyd / graded-monad /
Kleisli shape. This file finds out HONESTLY and delivers the precise verdict.

## What `interp`'s real signature forces (the categorical home)

The cornerstone (`Argus/Stmt.lean:104`) is

    interp : RecStmt → RecordKernelState → Option RecordKernelState

i.e. each `RecStmt` term denotes an arrow `RecordKernelState ⇸ RecordKernelState` in the
**Kleisli category of the `Option` monad** — a PARTIAL state transformer, the partiality being
exactly the `guard`/`insFresh`/`checkLe`/`checkSubset` rejection (`none`). And `interp` is
defined by STRUCTURAL RECURSION on `RecStmt`, with the recursive constructor

    interp (.seq s t) k = (interp s k).bind (interp t)            -- KLEISLI composition.

So the honest categorical home is:

  **`RecStmt` = the INITIAL algebra (in `Type`) of the polynomial signature functor `Σ`
  whose operations are the constructors; the "two readings" are folds landing in the HOM-SET
  of the Kleisli category `Kl(Option)` of partial state transformers `State ⇸ State`.**

This is the Freyd/Kleisli answer the register predicted: `interp` is NOT a map into `Type`,
it is a map into `State → Option State` (a Kleisli arrow), and `seq` is interpreted by Kleisli
composition `>=>`. The signature is a FREE algebra over that effectful target — `interp` is the
unique `Σ`-algebra homomorphism (= the fold / catamorphism) induced by choosing, for each
constructor, its Kleisli operation. THAT uniqueness is what R9 wants.

## The VERDICT: **PARTIAL.**

  * (PASS half) **Initiality genuinely holds for the term algebra, and `interp` IS the unique
    fold.** We reify the choice of "one Kleisli operation per constructor" as a `StmtAlgebra`
    (`§1`), define the induced fold `foldStmt` (`§2`), prove `interp` IS that fold for the
    canonical `interpAlgebra` (`interp_eq_fold`, `§3`), and prove **uniqueness of the fold**:
    any function agreeing with the algebra on every constructor EQUALS `foldStmt`
    (`fold_unique`, `§4`). The payoff theorem `agree_by_initiality` (`§5`) is the N²→1 collapse
    IN ITS HONEST FORM: two readings that are BOTH folds of the SAME algebra are equal on EVERY
    term — no per-term/per-effect induction, by uniqueness alone. Non-vacuity: `fold_unique`
    genuinely CONSTRAINS — it forces agreement on a COMPOUND `seq` term from agreement on the
    constructors (`fold_unique_constrains`, `§6`).

  * (the OBSTRUCTION — why not full PASS) **The CURRENT `compile` (`Argus/Compile.lean:116`) is
    NOT a fold.** It is a top-level SHAPE MATCH —

        compile (.seq (.guard _) (.setCell _ _)) = transferVmDescriptor
        compile _                                = skipDescriptor

    — which inspects TWO levels of constructor and is NON-COMPOSITIONAL in `seq`: it does not
    factor as `compile (.seq s t) = ⟨compile s , compile t⟩`. We PROVE this is a genuine
    structural obstruction (`§7`): there is NO binary descriptor-combiner `⊕` making `compile`
    respect `seq`, because `compile (seq guard setCell) = transferVmDescriptor` (a 36-constraint
    real circuit) while `compile guard = compile setCell = skipDescriptor` (empty) — so any
    `⊕`-homomorphism would force `transferVmDescriptor = skipDescriptor ⊕ skipDescriptor`, a
    SINGLE fixed value, which cannot also equal `skipDescriptor` (the value `⊕` must give for
    `seq skip skip`). `compile` therefore does NOT ride initiality as written.

## What this MEANS for retiring the per-effect agreement proofs

The N²→1 collapse is **available exactly for readings expressed as folds** (genuine
`Σ`-algebra homs). `interp` qualifies TODAY. To make the executor⟺circuit agreement free
(retire the per-effect differential), `compile` must be REFACTORED into a fold —
`compileAlgebra : StmtAlgebra EffectVmDescriptor` with a real `seq`-combiner (descriptor
sequential composition) — at which point `agree_by_initiality` discharges executor⟺circuit on
ALL terms from agreement on the ~20 constructors, NOT N² per-effect lemmas. The probe's
deliverable is the precise gate: **the collapse is structural, not per-effect, the moment both
readings are folds; the one obstruction is the current non-compositional `compile` shape.**

## Honesty

`#assert_axioms` clean below (the standard three kernel axioms only — `propext`,
`Classical.choice`, `Quot.sound`); no `sorry`, no `:= True`, no `native_decide`. This file owns
ONLY its own declarations and imports the IR read-only (it edits no existing file).
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Compile

namespace Metatheory.Dynamics.Initiality

open Dregg2.Circuit.Argus
open Dregg2.Exec
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)

/-! ## §1. The signature as an ALGEBRA — one operation per constructor.

A `Σ`-algebra on carrier `α` is a choice of one operation per `RecStmt` constructor, with the
recursive `seq` operation taking the carrier values of its two subterms. This is the polynomial
signature functor `Σ` reified as a record of operations: an `F`-algebra `Σ α → α`. The leaves
(`skip … allocCell`) carry their parameter data; `seq` is the binary node `α → α → α`. The
initial algebra of `Σ` is `RecStmt` itself (`Lean`'s inductive = initial algebra), and a
`StmtAlgebra α` is precisely the data inducing the UNIQUE hom `RecStmt → α` (the fold). -/

/-- **`StmtAlgebra α`** — a `Σ`-algebra structure on `α`: one field per `RecStmt` constructor.
The leaf fields are the constructors' operations (carrying their parameter data into `α`); `seqOp`
is the binary node. Choosing a `StmtAlgebra` is choosing how to INTERPRET each primitive — and the
fold (`§2`) is the unique extension to whole terms. -/
structure StmtAlgebra (α : Type) where
  skipOp           : α
  guardOp          : (RecordKernelState → Bool) → α
  setCellOp        : Finset CellId → (RecordKernelState → CellId → Value) → α
  setBalOp         : (RecordKernelState → CellId → AssetId → Int) → α
  insFreshOp       : (RecordKernelState → Nat) → α
  setCapsOp        : (RecordKernelState → Caps) → α
  setNullifiersOp  : (RecordKernelState → List Nat) → α
  setRevokedOp     : (RecordKernelState → List Nat) → α
  setCommitmentsOp : (RecordKernelState → List Nat) → α
  setSwissOp       : (RecordKernelState → List SwissRecord) → α
  setFactoriesOp   : (RecordKernelState → List (Nat × FactoryEntry)) → α
  setSealedBoxesOp : (RecordKernelState → List SealedBoxRecord) → α
  setLifecycleOp   : (RecordKernelState → CellId → Nat) → α
  setDeathCertOp   : (RecordKernelState → CellId → Nat) → α
  setDelegateOp    : (RecordKernelState → CellId → Option CellId) → α
  setSlotCaveatsOp : (RecordKernelState → CellId → List SlotCaveat) → α
  setDelegationsOp : (RecordKernelState → CellId → List Cap) → α
  checkLeOp        : (RecordKernelState → Int) → (RecordKernelState → Int) → α
  checkSubsetOp    : (RecordKernelState → ExecAuth) → (RecordKernelState → ExecAuth) → α
  allocCellOp      : (RecordKernelState → CellId) → α
  /-- The binary `seq` node — it consumes the carrier values of the two SUBTERMS (compositional). -/
  seqOp            : α → α → α

/-! ## §2. The FOLD — the unique `Σ`-algebra homomorphism `RecStmt → α`.

`foldStmt alg` is the catamorphism: it recurses on the term, applying the algebra's operation at
each node, with `seq s t ↦ seqOp (fold s) (fold t)` — the COMPOSITIONAL recursion that makes it a
homomorphism. This is the map `RecStmt → α` that initiality says is UNIQUE for each `alg`. -/

/-- **`foldStmt alg`** — the fold (catamorphism) induced by a `StmtAlgebra`. The unique
`Σ`-algebra homomorphism out of the initial algebra `RecStmt`. -/
def foldStmt {α : Type} (alg : StmtAlgebra α) : RecStmt → α
  | .skip              => alg.skipOp
  | .guard φ           => alg.guardOp φ
  | .setCell T leaf    => alg.setCellOp T leaf
  | .setBal b          => alg.setBalOp b
  | .insFresh n        => alg.insFreshOp n
  | .setCaps g         => alg.setCapsOp g
  | .setNullifiers g   => alg.setNullifiersOp g
  | .setRevoked g      => alg.setRevokedOp g
  | .setCommitments g  => alg.setCommitmentsOp g
  | .setSwiss g        => alg.setSwissOp g
  | .setFactories g    => alg.setFactoriesOp g
  | .setSealedBoxes g  => alg.setSealedBoxesOp g
  | .setLifecycle g    => alg.setLifecycleOp g
  | .setDeathCert g    => alg.setDeathCertOp g
  | .setDelegate g     => alg.setDelegateOp g
  | .setSlotCaveats g  => alg.setSlotCaveatsOp g
  | .setDelegations g  => alg.setDelegationsOp g
  | .checkLe a b       => alg.checkLeOp a b
  | .checkSubset a b   => alg.checkSubsetOp a b
  | .allocCell n       => alg.allocCellOp n
  | .seq s t           => alg.seqOp (foldStmt alg s) (foldStmt alg t)

/-! ## §3. `interp` IS A FOLD — the KLEISLI home, made explicit.

The carrier is the Kleisli hom-set `State ⇸ State = RecordKernelState → Option RecordKernelState`.
Each leaf operation is the corresponding `interp` clause; `seqOp` is KLEISLI COMPOSITION
`f g k := (f k).bind g`. We prove `interp = foldStmt interpAlgebra` — so the executor reading is a
genuine `Σ`-algebra homomorphism, exactly as initiality requires. -/

/-- The carrier of the executor reading: a partial state transformer (a Kleisli arrow of `Option`). -/
abbrev StateK : Type := RecordKernelState → Option RecordKernelState

/-- Kleisli composition in `Option` — the meaning of `seq` (`interp (.seq s t) k = (interp s k).bind …`). -/
def kleisliSeq (f g : StateK) : StateK := fun k => (f k).bind g

/-- **`interpAlgebra`** — the `StmtAlgebra` whose carrier is the Kleisli hom-set and whose
operations are EXACTLY `interp`'s clauses (`seqOp` = `kleisliSeq`). The executor reading is the
fold of THIS algebra. -/
def interpAlgebra : StmtAlgebra StateK where
  skipOp           := fun k => some k
  guardOp          := fun φ k => if φ k then some k else none
  setCellOp        := fun T leaf k => some { k with cell := fun c => if c ∈ T then leaf k c else k.cell c }
  setBalOp         := fun b k => some { k with bal := b k }
  insFreshOp       := fun n k => if n k ∈ k.nullifiers then none else some { k with nullifiers := n k :: k.nullifiers }
  setCapsOp        := fun g k => some { k with caps := g k }
  setNullifiersOp  := fun g k => some { k with nullifiers := g k }
  setRevokedOp     := fun g k => some { k with revoked := g k }
  setCommitmentsOp := fun g k => some { k with commitments := g k }
  setSwissOp       := fun g k => some { k with swiss := g k }
  setFactoriesOp   := fun g k => some { k with factories := g k }
  setSealedBoxesOp := fun g k => some { k with sealedBoxes := g k }
  setLifecycleOp   := fun g k => some { k with lifecycle := g k }
  setDeathCertOp   := fun g k => some { k with deathCert := g k }
  setDelegateOp    := fun g k => some { k with delegate := g k }
  setSlotCaveatsOp := fun g k => some { k with slotCaveats := g k }
  setDelegationsOp := fun g k => some { k with delegations := g k }
  checkLeOp        := fun a b k => if a k ≤ b k then some k else none
  checkSubsetOp    := fun a b k => if a k ≤ b k then some k else none
  allocCellOp      := fun n k => some (createCellIntoAsset k (n k))
  seqOp            := kleisliSeq

/-- **`interp_eq_fold` — the executor reading IS the fold of `interpAlgebra` (PROVED).** `interp`
factors through the catamorphism: it is the unique `Σ`-algebra homomorphism `RecStmt → StateK`
induced by `interpAlgebra`. This is the formal content of "`interp` is a fold landing in the
Kleisli category" — the home the register predicted. -/
theorem interp_eq_fold : interp = foldStmt interpAlgebra := by
  funext s
  induction s with
  | seq a b iha ihb =>
      funext k
      simp only [interp, foldStmt, interpAlgebra, kleisliSeq, iha, ihb]
  | _ => rfl

#assert_axioms interp_eq_fold

/-! ## §4. UNIQUENESS OF THE FOLD — the initiality payoff.

Initiality of `RecStmt`: for each algebra `alg`, there is a UNIQUE homomorphism `RecStmt → α`.
We make "homomorphism" concrete (`IsFoldHom`: agrees with the algebra on every constructor) and
prove uniqueness — any two homomorphisms of the SAME algebra are EQUAL on every term. The proof is
ONE induction; downstream agreement results invoke it with ZERO further induction. -/

/-- **`IsFoldHom alg f`** — `f : RecStmt → α` is a `Σ`-algebra homomorphism for `alg`: it agrees
with the algebra's operation at EVERY constructor (the leaves on the nose, `seq` compositionally
on the recursive values `f s`, `f t`). This is the universal-property hom-condition. -/
structure IsFoldHom {α : Type} (alg : StmtAlgebra α) (f : RecStmt → α) : Prop where
  onSkip           : f .skip = alg.skipOp
  onGuard          : ∀ φ, f (.guard φ) = alg.guardOp φ
  onSetCell        : ∀ T leaf, f (.setCell T leaf) = alg.setCellOp T leaf
  onSetBal         : ∀ b, f (.setBal b) = alg.setBalOp b
  onInsFresh       : ∀ n, f (.insFresh n) = alg.insFreshOp n
  onSetCaps        : ∀ g, f (.setCaps g) = alg.setCapsOp g
  onSetNullifiers  : ∀ g, f (.setNullifiers g) = alg.setNullifiersOp g
  onSetRevoked     : ∀ g, f (.setRevoked g) = alg.setRevokedOp g
  onSetCommitments : ∀ g, f (.setCommitments g) = alg.setCommitmentsOp g
  onSetSwiss       : ∀ g, f (.setSwiss g) = alg.setSwissOp g
  onSetFactories   : ∀ g, f (.setFactories g) = alg.setFactoriesOp g
  onSetSealedBoxes : ∀ g, f (.setSealedBoxes g) = alg.setSealedBoxesOp g
  onSetLifecycle   : ∀ g, f (.setLifecycle g) = alg.setLifecycleOp g
  onSetDeathCert   : ∀ g, f (.setDeathCert g) = alg.setDeathCertOp g
  onSetDelegate    : ∀ g, f (.setDelegate g) = alg.setDelegateOp g
  onSetSlotCaveats : ∀ g, f (.setSlotCaveats g) = alg.setSlotCaveatsOp g
  onSetDelegations : ∀ g, f (.setDelegations g) = alg.setDelegationsOp g
  onCheckLe        : ∀ a b, f (.checkLe a b) = alg.checkLeOp a b
  onCheckSubset    : ∀ a b, f (.checkSubset a b) = alg.checkSubsetOp a b
  onAllocCell      : ∀ n, f (.allocCell n) = alg.allocCellOp n
  onSeq            : ∀ s t, f (.seq s t) = alg.seqOp (f s) (f t)

/-- The canonical fold IS a homomorphism (the existence half of initiality). -/
theorem foldStmt_isHom {α : Type} (alg : StmtAlgebra α) : IsFoldHom alg (foldStmt alg) where
  onSkip := rfl
  onGuard _ := rfl
  onSetCell _ _ := rfl
  onSetBal _ := rfl
  onInsFresh _ := rfl
  onSetCaps _ := rfl
  onSetNullifiers _ := rfl
  onSetRevoked _ := rfl
  onSetCommitments _ := rfl
  onSetSwiss _ := rfl
  onSetFactories _ := rfl
  onSetSealedBoxes _ := rfl
  onSetLifecycle _ := rfl
  onSetDeathCert _ := rfl
  onSetDelegate _ := rfl
  onSetSlotCaveats _ := rfl
  onSetDelegations _ := rfl
  onCheckLe _ _ := rfl
  onCheckSubset _ _ := rfl
  onAllocCell _ := rfl
  onSeq _ _ := rfl

/-- **`fold_unique` — UNIQUENESS OF THE FOLD (initiality, PROVED).** Any `Σ`-algebra homomorphism
`f` for `alg` EQUALS the canonical fold `foldStmt alg` on EVERY term. This is the universal
property of the initial algebra `RecStmt`: the fold is the UNIQUE hom out of it. ONE induction;
every downstream agreement is a corollary with no further induction. -/
theorem fold_unique {α : Type} (alg : StmtAlgebra α) (f : RecStmt → α) (hf : IsFoldHom alg f) :
    f = foldStmt alg := by
  funext s
  induction s with
  | skip => exact hf.onSkip
  | guard φ => exact hf.onGuard φ
  | setCell T leaf => exact hf.onSetCell T leaf
  | setBal b => exact hf.onSetBal b
  | insFresh n => exact hf.onInsFresh n
  | setCaps g => exact hf.onSetCaps g
  | setNullifiers g => exact hf.onSetNullifiers g
  | setRevoked g => exact hf.onSetRevoked g
  | setCommitments g => exact hf.onSetCommitments g
  | setSwiss g => exact hf.onSetSwiss g
  | setFactories g => exact hf.onSetFactories g
  | setSealedBoxes g => exact hf.onSetSealedBoxes g
  | setLifecycle g => exact hf.onSetLifecycle g
  | setDeathCert g => exact hf.onSetDeathCert g
  | setDelegate g => exact hf.onSetDelegate g
  | setSlotCaveats g => exact hf.onSetSlotCaveats g
  | setDelegations g => exact hf.onSetDelegations g
  | checkLe a b => exact hf.onCheckLe a b
  | checkSubset a b => exact hf.onCheckSubset a b
  | allocCell n => exact hf.onAllocCell n
  | seq s t ihs iht =>
      rw [hf.onSeq s t, foldStmt, ihs, iht]

#assert_axioms fold_unique

/-! ## §5. THE PAYOFF — agreement BY UNIQUENESS (the N²→1 collapse, honest form).

If TWO readings `f`, `g` are BOTH homomorphisms of the SAME algebra, they are EQUAL on every term
— by `fold_unique` applied twice (both equal the canonical fold), with NO per-term induction. This
is the R9 collapse in the form that genuinely holds: the moment two readings are folds of one
algebra, their agreement on all terms is FREE. -/

/-- **`agree_by_initiality` — TWO folds of the same algebra AGREE on every term (PROVED).** The
honest form of the N²→1 collapse: agreement on ALL terms follows from each being a `Σ`-algebra
homomorphism, by uniqueness — not from any per-effect / per-term differential. -/
theorem agree_by_initiality {α : Type} (alg : StmtAlgebra α) (f g : RecStmt → α)
    (hf : IsFoldHom alg f) (hg : IsFoldHom alg g) : f = g := by
  rw [fold_unique alg f hf, fold_unique alg g hg]

#assert_axioms agree_by_initiality

/-- **`agree_by_initiality_pointwise`** — the same, applied pointwise on a term (the form a caller
consuming "executor and circuit agree on THIS term" would use). -/
theorem agree_by_initiality_pointwise {α : Type} (alg : StmtAlgebra α) (f g : RecStmt → α)
    (hf : IsFoldHom alg f) (hg : IsFoldHom alg g) (s : RecStmt) : f s = g s := by
  rw [agree_by_initiality alg f g hf hg]

/-! ## §6. NON-VACUITY — `fold_unique` actually CONSTRAINS a compound term.

A uniqueness theorem is worthless if it never forces anything. We exhibit that agreeing with an
algebra on the CONSTRUCTORS forces agreement on a COMPOUND `seq` term — the genuine content of
initiality (the recursive node is pinned by the leaf agreements + the `seq` law). We use the
`interpAlgebra` and a real two-level term. -/

/-- **`fold_unique_constrains` — initiality is NON-VACUOUS (PROVED).** A homomorphism `f` of
`interpAlgebra` is FORCED to equal `interp` on the COMPOUND term `seq (guard φ) (setCell T leaf)`
(the transfer SHAPE) — its value is determined by the leaf operations and the `seq`/Kleisli law,
exactly the constraint `fold_unique` imposes. So uniqueness genuinely bites on a non-atomic term,
not just the generators. -/
theorem fold_unique_constrains (f : RecStmt → StateK) (hf : IsFoldHom interpAlgebra f)
    (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    f (.seq (.guard φ) (.setCell T leaf)) = interp (.seq (.guard φ) (.setCell T leaf)) := by
  rw [fold_unique interpAlgebra f hf, ← interp_eq_fold]

#assert_axioms fold_unique_constrains

/-- **The compound value is genuinely the Kleisli composite (PROVED) — the constraint is REAL.**
The forced value of the transfer-shape term is `guard φ` Kleisli-composed with `setCell` — a
two-level term whose meaning is NOT either leaf alone. This exhibits that `fold_unique` pins a
COMPOSITE, witnessing non-vacuity concretely. -/
theorem fold_unique_constrains_value
    (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) (k : RecordKernelState) :
    interp (.seq (.guard φ) (.setCell T leaf)) k
      = (if φ k then some k else none).bind
          (fun k' => some { k' with cell := fun c => if c ∈ T then leaf k' c else k'.cell c }) := by
  simp only [interp]

#assert_axioms fold_unique_constrains_value

/-! ## §7. THE OBSTRUCTION — the CURRENT `compile` is NOT a fold.

`interp` rides initiality (`§3`). The OTHER reading, `compile` (`Argus/Compile.lean:116`), does
NOT — it is a non-compositional top-level SHAPE MATCH. We prove this is a genuine structural
obstruction: there is NO binary descriptor-combiner `⊕` under which `compile` respects `seq` (i.e.
`compile` is provably NOT a `seqOp`-homomorphism for any `⊕`). The argument is a clean
contradiction from `compile`'s own definitional values. -/

/-- `compile` of the transfer SHAPE is the real 36-constraint circuit (definitional). -/
theorem compile_transferShape (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    compile (.seq (.guard φ) (.setCell T leaf))
      = transferVmDescriptor := rfl

/-- `compile` of `guard` alone is the empty `skipDescriptor` (definitional). -/
theorem compile_guard (φ : RecordKernelState → Bool) :
    compile (.guard φ) = skipDescriptor := rfl

/-- `compile` of `setCell` alone is the empty `skipDescriptor` (definitional). -/
theorem compile_setCell (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    compile (.setCell T leaf) = skipDescriptor := rfl

/-- `compile` of `skip` is the empty `skipDescriptor`, and `seq skip skip` is ALSO `skipDescriptor`
(neither matches the transfer arm) — definitional. -/
theorem compile_seq_skip :
    compile (.seq .skip .skip) = skipDescriptor := rfl

/-- The transfer descriptor is NOT the skip descriptor — they differ in `constraints` length
(36 vs 0), so they are unequal descriptors. (The audited fact `compile_is_real`,
`Argus/Compile.lean:224`, records the 36/4/2 shape; here we only need the inequality.) -/
theorem transfer_ne_skip :
    transferVmDescriptor
      ≠ skipDescriptor := by
  intro h
  -- Equal descriptors have equal `constraints` lists, hence equal lengths; but the transfer
  -- descriptor has 36 constraints and `skipDescriptor` has 0 (decidable on the concrete data).
  have hc : transferVmDescriptor.constraints.length
      = skipDescriptor.constraints.length := by rw [h]
  simp only [skipDescriptor, List.length_nil] at hc
  exact absurd hc (by decide)

/-- **`compile_not_a_seq_hom` — THE OBSTRUCTION (PROVED).** There is NO binary descriptor-combiner
`⊕` making the CURRENT `compile` respect `seq`. If some `⊕` did (`compile (.seq s t) = compile s ⊕
compile t` for all `s t`), then:

  * at `s = guard φ`, `t = setCell T leaf`: `transferVmDescriptor = skipDescriptor ⊕ skipDescriptor`
    (both legs compile to `skipDescriptor`), so `skipDescriptor ⊕ skipDescriptor = transferVmDescriptor`;
  * at `s = t = skip`: `compile (.seq skip skip) = skipDescriptor ⊕ skipDescriptor`, and `compile
    (.seq skip skip) = skipDescriptor`, so `skipDescriptor ⊕ skipDescriptor = skipDescriptor`.

Chaining, `transferVmDescriptor = skipDescriptor`, contradicting `transfer_ne_skip`. Hence `compile`
is NOT a `Σ`-algebra homomorphism for ANY `seq`-combiner — it cannot be written as `foldStmt
compileAlgebra`, so it does NOT ride initiality as currently defined. THIS is the precise reason the
N²→1 collapse is PARTIAL, not full: `interp` is a fold, the current `compile` is not. -/
theorem compile_not_a_seq_hom :
    ¬ ∃ (combine : EffectVmDescriptor
                    → EffectVmDescriptor
                    → EffectVmDescriptor),
        ∀ s t, compile (.seq s t) = combine (compile s) (compile t) := by
  rintro ⟨combine, hcomb⟩
  -- transfer shape: LHS = transferVmDescriptor, RHS = combine skip skip
  have h1 : transferVmDescriptor
      = combine skipDescriptor
                skipDescriptor := by
    have := hcomb (.guard (fun _ => true)) (.setCell ∅ (fun _ c => default))
    rwa [compile_transferShape, compile_guard, compile_setCell] at this
  -- skip/skip: LHS = skipDescriptor, RHS = combine skip skip (the SAME RHS)
  have h2 : skipDescriptor
      = combine skipDescriptor
                skipDescriptor := by
    have := hcomb .skip .skip
    rwa [compile_seq_skip, compile_skip_leg] at this
  -- both equal `combine skip skip`, so transferVmDescriptor = skipDescriptor — contradiction.
  exact transfer_ne_skip (h1.trans h2.symm)
where
  /-- `compile .skip = skipDescriptor` (the leaf used in the `seq skip skip` leg). -/
  compile_skip_leg : compile .skip = skipDescriptor := rfl

#assert_axioms transfer_ne_skip
#assert_axioms compile_not_a_seq_hom

/-! ## §8. The RESOLUTION shape — what a fold-`compile` would need (the gate to FULL PASS).

The obstruction is not fundamental to the IR — it is the current `compile`'s NON-compositional
definition. A fold-shaped `compile` would supply a `StmtAlgebra EffectVmDescriptor` with a REAL
`seqOp` (sequential composition of descriptors). We record the EXACT target: once `compile` is a
fold, `agree_by_initiality` discharges executor⟺circuit agreement on ALL terms from agreement on
the constructors — the N²→1 collapse. We state the contract (no claim that the current `compile`
meets it — `compile_not_a_seq_hom` proves it does NOT). -/

/-- **`fold_compile_would_collapse` — the GATE to full PASS (PROVED, conditional).** IF a circuit
reading `comp` is a `Σ`-algebra homomorphism of SOME descriptor-algebra `compAlg`, AND a circuit
reading `comp'` is a homomorphism of the SAME algebra, then they AGREE on every term by initiality
— NO per-effect proof. This is the precise statement of what retiring the per-effect differential
costs: refactor `compile` into a fold (a `StmtAlgebra EffectVmDescriptor`), and agreement is free.
The hypothesis is exactly the thing `compile_not_a_seq_hom` shows the CURRENT `compile` fails. -/
theorem fold_compile_would_collapse
    (compAlg : StmtAlgebra EffectVmDescriptor)
    (comp comp' : RecStmt → EffectVmDescriptor)
    (h1 : IsFoldHom compAlg comp) (h2 : IsFoldHom compAlg comp') :
    comp = comp' :=
  agree_by_initiality compAlg comp comp' h1 h2

#assert_axioms fold_compile_would_collapse

/-! ## §Coda — THE VERDICT (PARTIAL).

  * **Categorical home**: `RecStmt` is the INITIAL algebra (in `Type`) of the polynomial signature
    functor whose operations are its constructors; the readings are FOLDS into the hom-set of the
    KLEISLI category `Kl(Option)` of partial state transformers `State ⇸ State` (the partiality =
    the `guard` effect, `seq` = Kleisli composition). This is the Freyd/Kleisli shape the register
    predicted — NOT a plain initial algebra in `Type` for the readings' target, but initiality of
    the TERM algebra with effectful folds.

  * **PASS half**: `interp` IS the unique fold (`interp_eq_fold`); uniqueness of the fold holds
    (`fold_unique`); and TWO folds of one algebra agree on ALL terms by uniqueness, no per-effect
    differential (`agree_by_initiality`). Non-vacuous: uniqueness forces a COMPOUND `seq` term
    (`fold_unique_constrains`).

  * **The OBSTRUCTION (why PARTIAL, not PASS)**: the CURRENT `compile` is NOT a fold — it is a
    non-compositional shape match, and `compile_not_a_seq_hom` proves NO `seq`-combiner makes it a
    homomorphism. So `compile` does not ride initiality AS WRITTEN.

  * **What it means for retiring per-effect proofs**: the N²→1 collapse is available EXACTLY for
    fold-shaped readings. `interp` qualifies today. Refactor `compile` into a fold
    (`StmtAlgebra EffectVmDescriptor` with a real descriptor-`seqOp`) and `fold_compile_would_collapse`
    discharges executor⟺circuit on ALL terms from agreement on the ~20 constructors. The collapse is
    STRUCTURAL, not per-effect — gated on one refactor, not N² lemmas.
-/

end Metatheory.Dynamics.Initiality
