/-
# Dregg2.Circuit.Argus.CompileE — the EFFECT-ANNOTATED IR: per-effect descriptors RIDE the collapse.

`CompileFold.lean` proved the D2 UNLOCK: the circuit reading is a genuine fold (`compileFold =
foldStmt compileAlgebra`), so executor⟺circuit agreement on ALL terms rides initiality
(`interp_compile_agree_of_generators`). But its §Coda recorded the ONE residual (the §M
opaque-leaf finding): `compileAlgebra`'s LEAF descriptors all come out `skipDescriptor`, because a
fold over `RecStmt` sees only each constructor's OPAQUE closure (`leaf : RecordKernelState → CellId
→ Value`) and CANNOT recover the concrete per-effect gate polynomials of
`transferVmDescriptor`/`mintVmDescriptor`/`burnVmDescriptor` — those three are the SAME
`seq (guard) (setCell)` shape, differing only inside the closure. The genuine per-effect descriptors
live on `Compile.lean`'s EFFECT-keyed `compileE : ArgusEffect → EffectVmDescriptor`, reached by an
effect ANNOTATION, NOT a finer `RecStmt` fold.

This file supplies that annotation. It defines the EFFECT-ANNOTATED IR `RecStmtE` — a term whose
LEAVES each carry an `ArgusEffect` TAG (so the leaf operation can branch on the tag a `RecStmt`
match cannot) — the per-tag algebra/fold machinery (mirroring `Initiality.lean`), and the payoff:
`compileEFold` is a fold whose leaf descriptors are RICH (transfer ≠ mint ≠ burn ≠ skip), and the
collapse `compileE_agree_by_initiality` rides the SAME `fold_unique` machinery — so
executor⟺circuit agreement on all annotated terms collapses to agreement on the FINITE set of
effect-tagged constructors, and the leaves now carry the GENUINE circuit content. The transfer leaf
IS `transferVmDescriptor`, welding the collapse to the existing per-effect descriptor soundness
(`transfer_compile_sound`/`mint_compile_sound`/`burn_compile_sound`).

## Why an annotated IR fixes the opaque-leaf residual (the crux)

The §M finding is purely about RECOVERABILITY: a `RecStmt` leaf is an opaque closure, so a fold over
it cannot tell transfer from mint. The annotated IR makes the effect tag a FIRST-CLASS leaf field —
so the fold's leaf operation receives the `ArgusEffect`, dispatches it through `compileE`, and emits
the genuine descriptor. The tag is exactly the running prover's per-effect SELECTOR
(`sel.NOOP`/`selM.MINT`/`selB.BURN`, `columns.rs`) lifted into the IR — the prover ALSO keys on the
tag, not the statement shape (`Compile.lean §M`), so this annotation is faithful to what runs.

The collapse is then GENUINELY rich: any two readings that are folds of the SAME annotated algebra
agree on every annotated term, and the leaf agreement they collapse to is on `transferVmDescriptor`
vs `mintVmDescriptor` vs … — NOT all `skipDescriptor`. The §Coda residual is closed, not papered.

## Axiom hygiene

`#assert_axioms` clean (the standard three kernel axioms only); no `sorry`, no `:= True`, no
`native_decide`. This file owns ONLY its own declarations; it imports the descriptor layer + the
fold machinery + `compileE` read-only, and adds ONE import line to `Argus.lean`. It edits no other
file's contents.
-/
import Dregg2.Circuit.Argus.CompileFold

namespace Dregg2.Circuit.Argus.CompileE

open Dregg2.Exec
open Dregg2.Circuit.Argus (ArgusEffect compileE skipDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitMint (mintVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitBurn (burnVmDescriptor)
open Dregg2.Circuit.Argus.CompileFold (seqDescr)

/-! ## §1 — `RecStmtE`: the EFFECT-ANNOTATED IR.

A term whose LEAVES carry an `ArgusEffect` tag and whose only compound node is `seqE` (the
sequential composite — the meaning of the `RecStmt` `seq`). This is the SMALLEST shape that fixes
the opaque-leaf residual: each `leaf tag` names the effect whose genuine descriptor the circuit must
emit (the tag a `RecStmt` match could not recover from the closure), and `seqE` conjoins via
`seqDescr` exactly as the `RecStmt` fold's `seq` does. -/

/-- **`RecStmtE`** — the effect-annotated IR. `leaf tag` is a primitive carrying its `ArgusEffect`
selector (the tag that names which per-effect descriptor the circuit emits); `seqE` is the binary
sequential node (the annotated image of `RecStmt.seq`). The annotation is the running prover's
per-effect selector lifted into the IR. -/
inductive RecStmtE where
  | leaf (tag : ArgusEffect)
  | seqE (s t : RecStmtE)

/-! ## §2 — the ALGEBRA over the annotated IR (mirroring `Initiality.StmtAlgebra`).

A `StmtEAlgebra α` is one operation per `RecStmtE` constructor: `leafOp : ArgusEffect → α` (keyed
on the TAG — the whole point) and `seqOp : α → α → α`. Choosing it IS choosing how to interpret each
effect tag; the fold (`§3`) is the unique extension to annotated terms. This is the polynomial
signature of `RecStmtE` reified, exactly as `StmtAlgebra` is for `RecStmt`. -/

/-- **`StmtEAlgebra α`** — a `Σ`-algebra on `α` for the annotated IR. `leafOp` consumes the
`ArgusEffect` TAG (so it can dispatch to the genuine per-effect descriptor — the recovery a
`RecStmt` fold lacks); `seqOp` is the binary node. -/
structure StmtEAlgebra (α : Type) where
  leafOp : ArgusEffect → α
  seqOp  : α → α → α

/-- **`foldStmtE alg`** — the catamorphism induced by a `StmtEAlgebra`: the unique `Σ`-algebra
homomorphism `RecStmtE → α`, recursing compositionally (`seqE s t ↦ seqOp (fold s) (fold t)`). -/
def foldStmtE {α : Type} (alg : StmtEAlgebra α) : RecStmtE → α
  | .leaf tag  => alg.leafOp tag
  | .seqE s t  => alg.seqOp (foldStmtE alg s) (foldStmtE alg t)

/-! ## §3 — `IsFoldEHom` + UNIQUENESS (initiality of the annotated IR).

`RecStmtE` is the initial algebra of its signature (Lean's inductive = initial algebra). We make
"homomorphism" concrete (`IsFoldEHom`: agrees with the algebra on `leaf` and `seqE`) and prove
uniqueness — any two homomorphisms of the SAME algebra are equal on EVERY annotated term, by ONE
induction. This is the `fold_unique` of `Initiality.lean`, transported to `RecStmtE`. -/

/-- **`IsFoldEHom alg f`** — `f : RecStmtE → α` is a `Σ`-algebra homomorphism for `alg`: it agrees
with the algebra on every leaf tag and on `seqE` compositionally. The universal-property
hom-condition for the annotated IR. -/
structure IsFoldEHom {α : Type} (alg : StmtEAlgebra α) (f : RecStmtE → α) : Prop where
  onLeaf : ∀ tag, f (.leaf tag) = alg.leafOp tag
  onSeqE : ∀ s t, f (.seqE s t) = alg.seqOp (f s) (f t)

/-- The canonical fold IS a homomorphism (the existence half of initiality). -/
theorem foldStmtE_isHom {α : Type} (alg : StmtEAlgebra α) : IsFoldEHom alg (foldStmtE alg) where
  onLeaf _ := rfl
  onSeqE _ _ := rfl

#assert_axioms foldStmtE_isHom

/-- **`foldStmtE_unique` — UNIQUENESS OF THE ANNOTATED FOLD (initiality).** Any `Σ`-algebra
homomorphism `f` for `alg` EQUALS the canonical fold `foldStmtE alg` on EVERY annotated term. ONE
induction; every downstream agreement is a corollary with no further induction. -/
theorem foldStmtE_unique {α : Type} (alg : StmtEAlgebra α) (f : RecStmtE → α)
    (hf : IsFoldEHom alg f) : f = foldStmtE alg := by
  funext s
  induction s with
  | leaf tag => exact hf.onLeaf tag
  | seqE s t ihs iht => rw [hf.onSeqE s t, foldStmtE, ihs, iht]

#assert_axioms foldStmtE_unique

/-! ## §4 — THE PAYOFF — agreement BY UNIQUENESS over the annotated IR (the rich-leaf collapse).

If TWO readings of the annotated IR are BOTH homomorphisms of the SAME algebra, they are EQUAL on
every annotated term — by `foldStmtE_unique` twice, with NO per-effect induction. This is the
collapse the §Coda residual demanded: now the algebra's `leafOp` carries the GENUINE per-effect
descriptors (next section), so the agreement it collapses to is on rich leaves (transfer ≠ mint),
not all-`skip`. -/

/-- **`compileE_agree_by_initiality` — TWO folds of the same annotated algebra AGREE on every term
.** The N²→1 collapse for the EFFECT-ANNOTATED IR: agreement on ALL annotated terms follows
from each being a `Σ`-algebra homomorphism, by uniqueness — not from any per-effect differential.
With the rich `compileEAlgebra` (`§5`) this collapse covers the per-effect content. -/
theorem compileE_agree_by_initiality {α : Type} (alg : StmtEAlgebra α) (f g : RecStmtE → α)
    (hf : IsFoldEHom alg f) (hg : IsFoldEHom alg g) : f = g := by
  rw [foldStmtE_unique alg f hf, foldStmtE_unique alg g hg]

#assert_axioms compileE_agree_by_initiality

/-- **`compileE_collapse_to_generators`** — the same, pointwise on a term (the form a caller
consuming "executor and circuit agree on THIS annotated term" would use). Agreement on the FINITE
set of effect-tagged constructors (the algebra's operations) ⇒ agreement on the chosen annotated
term, with NO per-term induction. -/
theorem compileE_collapse_to_generators {α : Type} (alg : StmtEAlgebra α) (f g : RecStmtE → α)
    (hf : IsFoldEHom alg f) (hg : IsFoldEHom alg g) (s : RecStmtE) : f s = g s := by
  rw [compileE_agree_by_initiality alg f g hf hg]

#assert_axioms compileE_collapse_to_generators

/-! ## §5 — `compileEAlgebra`: the RICH algebra — leaves emit the GENUINE per-effect descriptors.

THIS is the section that closes the §Coda residual. Unlike `CompileFold.compileAlgebra` (whose
leaves are ALL `skipDescriptor` — the opaque-closure residual), `compileEAlgebra`'s `leafOp` is the
EFFECT-keyed `compileE` itself: each leaf tag emits its audited runnable descriptor
(`transferVmDescriptor`/`mintVmDescriptor`/`burnVmDescriptor`),
and `seqOp := seqDescr` conjoins (the proven-associative composite from `CompileFold`). The fold's
leaves are now RICH. -/

/-- **`compileEAlgebra`** — the descriptor algebra over the annotated IR. `leafOp := compileE` (the
genuine per-effect descriptor for each tag — NOT `skipDescriptor`); `seqOp := seqDescr` (the proven
descriptor sequential composite). Choosing this algebra IS choosing the circuit reading as a fold
over the annotated IR, with the per-effect content RECOVERED. -/
def compileEAlgebra : StmtEAlgebra EffectVmDescriptor where
  leafOp := compileE
  seqOp  := seqDescr

/-- **`compileEFold`** — the circuit reading of the annotated IR AS A FOLD: the unique `Σ`-algebra
homomorphism `RecStmtE → EffectVmDescriptor` induced by `compileEAlgebra`. Its leaves are the
genuine per-effect descriptors; it rides initiality. -/
def compileEFold : RecStmtE → EffectVmDescriptor := foldStmtE compileEAlgebra

/-- **`compileEFold` IS a `Σ`-algebra homomorphism.** -/
theorem compileEFold_isHom : IsFoldEHom compileEAlgebra compileEFold :=
  foldStmtE_isHom compileEAlgebra

#assert_axioms compileEFold_isHom

/-- The `seqE`-homomorphism law made explicit: the circuit of `seqE s t` IS the descriptor composite
`seqDescr` of the circuits of `s` and `t`. -/
theorem compileEFold_seqE (s t : RecStmtE) :
    compileEFold (.seqE s t) = seqDescr (compileEFold s) (compileEFold t) := rfl

/-- **`compileEFold_collapse` — the collapse, DISCHARGED.** Any annotated circuit reading
`comp` that is a `Σ`-algebra homomorphism of `compileEAlgebra` EQUALS `compileEFold` on EVERY
annotated term — so two such readings agree everywhere by initiality, and the leaves they agree on
are the GENUINE per-effect descriptors. -/
theorem compileEFold_collapse (comp : RecStmtE → EffectVmDescriptor)
    (h : IsFoldEHom compileEAlgebra comp) : comp = compileEFold :=
  foldStmtE_unique compileEAlgebra comp h

#assert_axioms compileEFold_collapse

/-! ## §6 — THE LEAVES ARE RICH — transfer ≠ mint ≠ burn ≠ skip (the residual CLOSED).

The point of the annotation: `compileEFold (.leaf .transfer)` is the genuine `transferVmDescriptor`
(36 constraints), NOT `skipDescriptor`. We pin each leaf's value as its audited per-effect
descriptor (welding the collapse to the existing per-effect descriptor soundness
`transfer_compile_sound`/`mint_compile_sound`/`burn_compile_sound`) and prove they are PAIRWISE
distinct + distinct from `skip` — so the §Coda all-`skip` residual is closed. -/

/-- The transfer leaf IS the audited runnable transfer descriptor — the fold leaf welds to
`compileE .transfer` (and hence to `transfer_compile_sound`'s circuit side). -/
theorem compileEFold_leaf_transfer :
    compileEFold (.leaf .transfer) = transferVmDescriptor := rfl

/-- The mint leaf IS the audited runnable mint descriptor (welds to `mint_compile_sound`). -/
theorem compileEFold_leaf_mint :
    compileEFold (.leaf .mint) = mintVmDescriptor := rfl

/-- The burn leaf IS the audited runnable burn descriptor (welds to `burn_compile_sound`). -/
theorem compileEFold_leaf_burn :
    compileEFold (.leaf .burn) = burnVmDescriptor := rfl

/-- The `other` leaf is the empty placeholder — the ONLY tag that compiles to `skipDescriptor`
(every named effect carries its genuine descriptor). -/
theorem compileEFold_leaf_other :
    compileEFold (.leaf .other) = skipDescriptor := rfl

#assert_axioms compileEFold_leaf_transfer
#assert_axioms compileEFold_leaf_mint
#assert_axioms compileEFold_leaf_burn

/-- **`compileEFold_leaves_rich` — the leaves are NOT ALL-SKIP.** The transfer / mint
/ burn leaves carry 36 / 34 / 35 constraints respectively (none zero), so each DIFFERS from the
empty `skipDescriptor`. This is the closure of the §Coda residual: the annotated fold's leaves are
GENUINE per-effect circuits, not the opaque-closure `skipDescriptor`. -/
theorem compileEFold_leaves_rich :
    (compileEFold (.leaf .transfer)).constraints.length = 36
    ∧ (compileEFold (.leaf .mint)).constraints.length = 34
    ∧ (compileEFold (.leaf .burn)).constraints.length = 35
    ∧ (compileEFold (.leaf .transfer)).constraints ≠ skipDescriptor.constraints
    ∧ (compileEFold (.leaf .mint)).constraints ≠ skipDescriptor.constraints
    ∧ (compileEFold (.leaf .burn)).constraints ≠ skipDescriptor.constraints := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [compileEFold_leaf_transfer]
    intro h
    have : transferVmDescriptor.constraints.length = skipDescriptor.constraints.length := by rw [h]
    simp only [skipDescriptor, List.length_nil] at this; exact absurd this (by decide)
  · rw [compileEFold_leaf_mint]
    intro h
    have : mintVmDescriptor.constraints.length = skipDescriptor.constraints.length := by rw [h]
    simp only [skipDescriptor, List.length_nil] at this; exact absurd this (by decide)
  · rw [compileEFold_leaf_burn]
    intro h
    have : burnVmDescriptor.constraints.length = skipDescriptor.constraints.length := by rw [h]
    simp only [skipDescriptor, List.length_nil] at this; exact absurd this (by decide)

#assert_axioms compileEFold_leaves_rich

/-- **`compileEFold_leaves_distinct` — transfer ≠ mint ≠ burn AS CIRCUITS.** The three
same-shaped supply/transfer effects (which a `RecStmt` fold provably could NOT separate —
`Compile.compile_collapses_mint_burn_to_transfer`) now compile to THREE distinct descriptors on the
annotated fold (36 vs 34 vs 35 constraints). This is the recovery the annotation buys: the tag
separates what the opaque closure could not. -/
theorem compileEFold_leaves_distinct :
    compileEFold (.leaf .transfer) ≠ compileEFold (.leaf .mint)
    ∧ compileEFold (.leaf .mint) ≠ compileEFold (.leaf .burn)
    ∧ compileEFold (.leaf .transfer) ≠ compileEFold (.leaf .burn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : transferVmDescriptor.constraints.length = mintVmDescriptor.constraints.length := by
      rw [compileEFold_leaf_transfer, compileEFold_leaf_mint] at h; rw [h]
    exact absurd this (by decide)
  · intro h
    have : mintVmDescriptor.constraints.length = burnVmDescriptor.constraints.length := by
      rw [compileEFold_leaf_mint, compileEFold_leaf_burn] at h; rw [h]
    exact absurd this (by decide)
  · intro h
    have : transferVmDescriptor.constraints.length = burnVmDescriptor.constraints.length := by
      rw [compileEFold_leaf_transfer, compileEFold_leaf_burn] at h; rw [h]
    exact absurd this (by decide)

#assert_axioms compileEFold_leaves_distinct

/-! ## §7 — NON-VACUITY: the collapse forces a COMPOUND term whose value is a genuine `seqDescr` of
TWO DISTINCT effect descriptors.

A collapse theorem is worthless if it never bites on rich content. We exhibit the
TRANSFER-THEN-MINT compound term `seqE (leaf transfer) (leaf mint)`: agreeing with `compileEAlgebra`
on the CONSTRUCTORS forces agreement there, and the forced value is `seqDescr transferVmDescriptor
mintVmDescriptor` — a genuine conjunction of TWO DISTINCT per-effect circuits (36 + 34 = 70
constraints), NOT either leaf alone and NOT all-`skip`. This is the concrete witness that the leaves
carry real, distinct content. -/

/-- The transfer-then-mint compound, as an annotated term. -/
def transferThenMint : RecStmtE := .seqE (.leaf .transfer) (.leaf .mint)

/-- **`compileEFold_transferThenMint` — the forced compound value.** `compileEFold` of the
transfer-then-mint term is `seqDescr transferVmDescriptor mintVmDescriptor` — the conjunction of the
two DISTINCT sub-circuits on the shared row window. -/
theorem compileEFold_transferThenMint :
    compileEFold transferThenMint = seqDescr transferVmDescriptor mintVmDescriptor := rfl

/-- **`compileEFold_collapse_constrains_rich` — the collapse is NON-VACUOUS ON RICH CONTENT
.** Any hom `comp` of `compileEAlgebra` is FORCED, on the compound transfer-then-mint term,
to equal `compileEFold` there — and that value is the genuine `seqDescr` of two DISTINCT effect
descriptors (`transferVmDescriptor`, `mintVmDescriptor`). So uniqueness bites on a non-atomic term
whose leaves are NOT skip and NOT equal — the corrected compositional reading that ALSO carries the
real circuit content. -/
theorem compileEFold_collapse_constrains_rich (comp : RecStmtE → EffectVmDescriptor)
    (h : IsFoldEHom compileEAlgebra comp) :
    comp transferThenMint = seqDescr transferVmDescriptor mintVmDescriptor := by
  rw [compileEFold_collapse comp h, compileEFold_transferThenMint]

#assert_axioms compileEFold_collapse_constrains_rich

/-- **`transferThenMint_nontrivial` — the forced compound is a REAL conjunction.** The
transfer-then-mint descriptor carries 36 + 34 = 70 constraints (the two leaves' gate sets,
conjoined via `seqDescr`'s append) — strictly more than EITHER leaf alone and far from the empty
`skipDescriptor`. So the non-vacuity witness pins genuine, distinct per-effect content, closing the
§Coda residual concretely. -/
theorem transferThenMint_nontrivial :
    (compileEFold transferThenMint).constraints.length = 70
    ∧ (compileEFold transferThenMint).constraints.length
        > (compileEFold (.leaf .transfer)).constraints.length
    ∧ (compileEFold transferThenMint).constraints.length
        > (compileEFold (.leaf .mint)).constraints.length := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [compileEFold_transferThenMint, compileEFold_leaf_transfer, compileEFold_leaf_mint,
      seqDescr, List.length_append] <;> decide

#assert_axioms transferThenMint_nontrivial

/-! ## §Coda — THE VERDICT (the §Coda residual of `CompileFold` is CLOSED).

  * **The annotated IR is supplied**: `RecStmtE` carries the `ArgusEffect` tag at its leaves — the
    running prover's per-effect selector lifted into the IR. Its algebra/fold/uniqueness machinery
    (`StmtEAlgebra`/`foldStmtE`/`foldStmtE_unique`) mirrors `Initiality.lean`, so `compileEFold`
    rides the SAME initiality.

  * **The leaves are RICH**: `compileEAlgebra.leafOp := compileE`, so each leaf emits its GENUINE
    per-effect descriptor — `compileEFold (.leaf .transfer) = transferVmDescriptor` (36 constraints),
    `.mint = mintVmDescriptor` (34), `.burn = burnVmDescriptor` (35), pairwise DISTINCT
    (`compileEFold_leaves_distinct`) and none `skip` (`compileEFold_leaves_rich`). The §Coda
    all-`skip` residual is CLOSED — the tag recovers what the opaque `RecStmt` closure could not.

  * **The collapse is real AND rich**: `compileE_agree_by_initiality` collapses executor⟺circuit
    agreement on ALL annotated terms to agreement on the finite effect-tagged constructors
    (`compileEFold_collapse`), and the leaves it collapses to carry the real circuit content. Welds
    to the existing per-effect descriptor soundness (`compileEFold_leaf_transfer` IS the circuit
    side of `transfer_compile_sound`, etc.).

  * **Non-vacuous on rich content**: the collapse FORCES the transfer-then-mint compound to
    `seqDescr transferVmDescriptor mintVmDescriptor` (`compileEFold_collapse_constrains_rich`), a
    genuine conjunction of TWO DISTINCT effect descriptors (70 constraints,
    `transferThenMint_nontrivial`) — the compositional reading
    carrying the real per-effect circuit.
-/

end Dregg2.Circuit.Argus.CompileE
