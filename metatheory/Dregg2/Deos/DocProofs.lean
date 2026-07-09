/-
# `Dregg2.Deos.DocProofs` — the REFINEMENT: the Init-only executable `DocCore` computes exactly F2's
ℤ-modeled `docCommit` under the canonical encoding, so it INHERITS F2's soundness.

Foundation piece **F4a** of `docs/DREGG-DOCUMENT-FOUNDATION.md` §4. This module imports `DocCore`
(Init-only), `DocCommit` (F2, the ℤ model + its injective/conflict keystones), and Mathlib — so it is
**NEVER on the wasm import path**. The proofs stay exactly as strong (they discharge to the
`Poseidon2SpongeCR` collision-resistance carrier, threaded as a hypothesis exactly as F2 does); they
just do not ship to the tab. *Proofs off the wasm import path.*

## What is delivered

* `encodeExec` — the executable felt preimage: F2's `encode d : List ℤ` mapped fixed-width
  (`z ↦ UInt64.ofNat z.toNat`), i.e. the batched canonical bytes `DocCore.docCommitExec` consumes.
* `docCoreHash` — the ℤ→ℤ sponge built from `DocCore.spongeFold`; it is a concrete instance of the
  `hash` PARAMETER of F2's `docCommit`, so `DocCommit.docCommit docCoreHash` **is** F2's commitment at
  the DocCore sponge (same `p2compress` extern symbol as the deployed `Storage.poseidon2Hash`; the two
  differ only by opaque-Lean identity, identical at the native/wasm leaf).
* `docCommitExec_refines` / `atomIdExec_refines` — the executable core equals `Int.ofNat (…).toNat` of
  F2's `docCommit docCoreHash` (resp. atom preimage). The exec value IS the ℤ-model value.
* `docCommitExec_injective` — inherited from `DocCommit.docCommit_injective`: equal executable
  commitments ⟹ equal committed document (no ghost atom hides under a genuine executable root).
* `docCommitExec_conflict_binds_both` — inherited conflict-as-state soundness: an executable
  commitment to a two-alternative conflict DETERMINES both live alternatives + provenance.

Only `Poseidon2SpongeCR docCoreHash` is assumed (a HYPOTHESIS, never a Lean axiom — `#assert_axioms`
sees only kernel axioms {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Deos.DocCore
import Dregg2.Deos.DocCommit
import Dregg2.Tactics

namespace Dregg2.Deos.DocProofs

open Dregg2.Deos.DocCommit
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## 1. The bridge: the executable felt preimage and the DocCore-sponge ℤ hash. -/

/-- The fixed-width felt encoding of a felt: `ℤ ↦ UInt64` (the canonical-bytes felt DocCore folds).
`Nat.toUInt64` is `abbrev`-equal to `UInt64.ofNat`, so this matches `poseidon2Hash`'s per-element
`x.toNat.toUInt64` exactly. -/
def toFelt (z : ℤ) : UInt64 := UInt64.ofNat z.toNat

/-- **`encodeExec`** — the batched canonical byte preimage the executable core consumes: F2's `encode`
mapped to fixed-width felts. This is what Rust's `commit.rs::canonical_bytes` hands the exported
`dregg_doc_commit`. -/
def encodeExec (d : Doc) : List UInt64 := (encode d).map toFelt

/-- **`docCoreHash`** — the ℤ→ℤ sponge realized by the Init-only `DocCore.spongeFold`. It has the SAME
shape as `Storage.Deployed.poseidon2Hash` (seed = length, fold each felt through the fast Rust
Poseidon2), and — crucially — it is a legitimate instance of the `hash` parameter of F2's `docCommit`.
So `DocCommit.docCommit docCoreHash` is F2's commitment, and its injective/conflict theorems apply. -/
def docCoreHash (xs : List ℤ) : ℤ := Int.ofNat (DocCore.spongeFold (xs.map toFelt)).toNat

/-! ## 2. The refinement — the executable core IS the ℤ-model value. -/

/-- **`docCommitExec_refines`.** The Init-only `DocCore.docCommitExec` over the canonical felt preimage
computes exactly `Int.ofNat (…).toNat` of F2's `docCommit docCoreHash`. Purely definitional: both
sides reduce to `Int.ofNat (spongeFold ((encode d).map toFelt)).toNat`. -/
theorem docCommitExec_refines (d : Doc) :
    docCommit docCoreHash d = Int.ofNat (DocCore.docCommitExec (encodeExec d)).toNat := rfl

/-- **`atomIdExec_refines`.** The executable per-atom content-address equals the ℤ-model hash of the
atom's canonical preimage (`DocCommit.encAtom`). -/
theorem atomIdExec_refines (a : Atom) :
    docCoreHash (encAtom a) = Int.ofNat (DocCore.atomIdExec ((encAtom a).map toFelt)).toNat := rfl

/-! ## 3. Inherited soundness — the executable core carries F2's guarantees. -/

/-- **`docCommitExec_injective`.** Equal EXECUTABLE commitments ⟹ equal committed document (atoms +
edges + fields, WITH provenance). Inherited from `DocCommit.docCommit_injective` via the refinement:
the executable root is `Int.ofNat`-of the ℤ-model root, so equal exec roots force equal ℤ-model roots,
which F2 sends to equal documents under the `Poseidon2SpongeCR` carrier. No ghost atom hides under a
genuine executable root. -/
theorem docCommitExec_injective (hCR : Poseidon2SpongeCR docCoreHash) (d d' : Doc)
    (h : DocCore.docCommitExec (encodeExec d) = DocCore.docCommitExec (encodeExec d')) : d = d' := by
  refine docCommit_injective docCoreHash hCR d d' ?_
  rw [docCommitExec_refines, docCommitExec_refines, h]

/-- **`docCommitExec_conflict_binds_both` (conflict-as-state soundness, executable).** If two documents
produce EQUAL executable commitments and each stores a two-alternative conflict at the same field, then
both live alternatives — value AND provenance — are identical. A substituted/forged alternative (even
one rendering identically) changes the executable root. Inherited from
`DocCommit.docCommit_conflict_binds_both`. -/
theorem docCommitExec_conflict_binds_both (hCR : Poseidon2SpongeCR docCoreHash)
    (d d' : Doc) (name : ℤ) (a1 a2 a1' a2' : FieldAssign)
    (hd : fieldAt d name = some [a1, a2]) (hd' : fieldAt d' name = some [a1', a2'])
    (heq : DocCore.docCommitExec (encodeExec d) = DocCore.docCommitExec (encodeExec d')) :
    a1 = a1' ∧ a2 = a2' := by
  refine docCommit_conflict_binds_both docCoreHash hCR d d' name a1 a2 a1' a2' hd hd' ?_
  rw [docCommitExec_refines, docCommitExec_refines, heq]

/-! ## 4. NON-VACUITY — the executable forged conflict provably changes the executable root. -/

/-- **`exec_forge_changes_root` (NON-VACUITY).** F2's concrete forged conflict (`conflictDoc` vs
`forgedDoc` — same rendered value, forged author) yields DIFFERENT EXECUTABLE commitments under the
carrier. Proved THROUGH `docCommitExec_conflict_binds_both`, so that inherited keystone is non-vacuous
at the executable layer. -/
theorem exec_forge_changes_root (hCR : Poseidon2SpongeCR docCoreHash) :
    DocCore.docCommitExec (encodeExec conflictDoc)
      ≠ DocCore.docCommitExec (encodeExec forgedDoc) := by
  intro h
  have hb := docCommitExec_conflict_binds_both hCR conflictDoc forgedDoc 0
    altA altB altA altBforged (by decide) (by decide) h
  exact absurd hb.2 (by decide)

/-! ## 5. Axiom hygiene — every keystone kernel-clean (⊆ {propext, Classical.choice, Quot.sound}).
The `Poseidon2SpongeCR docCoreHash` carrier is a HYPOTHESIS, not an axiom, so it is not laundered. -/

#assert_axioms docCommitExec_refines
#assert_axioms atomIdExec_refines
#assert_axioms docCommitExec_injective
#assert_axioms docCommitExec_conflict_binds_both
#assert_axioms exec_forge_changes_root

end Dregg2.Deos.DocProofs
