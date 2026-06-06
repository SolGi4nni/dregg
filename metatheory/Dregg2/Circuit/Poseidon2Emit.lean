/-
# Dregg2.Circuit.Poseidon2Emit — Wave 4: in-circuit Poseidon2 sponge compress via `merkle_hash`.

Reuses PART II's emitted `merkle_hash` / `transition` / `pi_binding` wire forms from
`Exec/CircuitEmit.lean` (the same constraints `descriptors.rs::merkle_poseidon2_descriptor`
and `ConstraintExpr::MerkleHash` enforce). The abstract Layer-A `compress` remains the node
hash; a multi-row trace is a sponge-style fold of rate-4 absorption chunks — NOT an idealized
`ℤ` injectivity portal.

Explicit `sorry` HOLEs (tracked, not silent) remain for wiring this gadget into the full
`StateCommit` frame sponge and the growing log-hash sponge.

Proved theorems are `#assert_axioms`-clean; HOLE theorems intentionally carry `sorry`.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.GadgetRefinement
import Dregg2.Circuit.StateCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Crypto.Merkle

namespace Dregg2.Circuit.Poseidon2Emit

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Exec.CircuitEmit
open Dregg2.Crypto.Merkle
open Dregg2.Circuit.GadgetRefinement
open Dregg2.Circuit.StateCommit

/-! ## §1 — AIR identity + column layout (reuses Merkle `merkle_col`). -/

/-- AIR name for the sponge-compress gadget (distinct from full Merkle membership). -/
def poseidon2CompressAirName : String := "dregg-poseidon2-compress-v1"

/-- Trace width (= `MERKLE_P2_WIDTH` / `merkleTraceWidth`). -/
def poseidon2CompressTraceWidth : Nat := merkleTraceWidth

/-- Public inputs: `[leaf, root]` on the abstract bridge (= first `current`, last `parent`). -/
def poseidon2CompressPublicInputCount : Nat := merklePublicInputCount

/-- Maximum sponge absorption chunks per gadget instance (rate 4 per row). -/
def spongeRate : Nat := 4

/-- Default chunk count for the canonical emitted descriptor (one rate-4 absorption). -/
def spongeChunkCount : Nat := 1

/-! ## §2 — abstract sponge semantics (Layer-A `compress`, no `ℤ` injectivity). -/

/-- One rate-4 absorption: fold `compress` over four digests (balanced pairwise tree). -/
def absorbChunk {Digest : Type} (compress : Digest → Digest → Digest)
    (a b c d : Digest) : Digest :=
  compress (compress a b) (compress c d)

/-- **`spongeCompressN`** — abstract list sponge (uninterpreted; in-circuit realization is the
emitted multi-row `merkle_hash` chain). Parameterized by a caller-supplied `List Digest → Digest`
fold — no `ℤ` injectivity portal. -/
def spongeCompressN {Digest : Type} (compressSponge : List Digest → Digest) (xs : List Digest) :
    Digest :=
  compressSponge xs

/-- Build one sponge trace row from four explicit lane digests (siblings folded into `Row.sib`). -/
def spongeRowOfChunk {Digest : Type} (compress : Digest → Digest → Digest)
    (lane0 lane1 lane2 lane3 : Digest) (position : Nat) : Row Digest :=
  let sib := compress lane1 (compress lane2 lane3)
  { current := lane0
    sib := sib
    position := position
    parent := compress lane0 sib }

/-! ## §3 — emitted descriptor (efficient `merkle_hash` reuse). -/

/-- Wire constraints for a `spongeChunkCount`-row sponge: each row gets `merkle_hash`, rows chain
via `transition`, and the two `pi_binding` boundaries pin the endpoints. Same forms as
`merkleConstraintsWire` (efficient decoder reuse). -/
def spongeCompressConstraintsWire : List EmittedConstraintM := merkleConstraintsWire

/-- **`emittedPoseidon2Compress`** — the Wave-4 sponge-compress gadget descriptor. -/
def emittedPoseidon2Compress : EmittedMerkleDescriptor :=
  { name := poseidon2CompressAirName
    traceWidth := poseidon2CompressTraceWidth
    cols := merkleCols
    constraints := spongeCompressConstraintsWire
    publicInputCount := poseidon2CompressPublicInputCount }

/-- Emitted satisfaction for the sponge gadget (same denotation spine as `satisfiedEmittedMerkle`). -/
def satisfiedEmittedPoseidon2Compress {Digest : Type} (compress : Digest → Digest → Digest)
    (rows : List (Row Digest)) (root leaf : Digest) : Prop :=
  satisfiedEmittedMerkle compress emittedPoseidon2Compress rows root leaf

/-! ## §4 — faithfulness + refinement (compose `GadgetRefinement`). -/

section Faithfulness
variable {Digest : Type}

theorem sponge_constraints_eq :
    spongeCompressConstraintsWire = merkleConstraintsWire := rfl

theorem emitted_poseidon2_eq_merkle_constraints :
    emittedPoseidon2Compress.constraints = emittedMerkle.constraints := by
  simp [emittedPoseidon2Compress, emittedMerkle, spongeCompressConstraintsWire]

/-- **`emit_faithful_poseidon2_compress`** — emitted sponge descriptor ↔ `Merkle.Satisfies`. -/
theorem emit_faithful_poseidon2_compress (compress : Digest → Digest → Digest)
    (rows : List (Row Digest)) (root leaf : Digest) :
    satisfiedEmittedPoseidon2Compress compress rows root leaf
      ↔ Satisfies compress ⟨rows⟩ root leaf := by
  dsimp [satisfiedEmittedPoseidon2Compress, satisfiedEmittedMerkle]
  simpa [emitted_poseidon2_eq_merkle_constraints] using
    (emit_faithful_merkle compress rows root leaf)

/-- Emitted sponge step relation (for refinement composition). -/
def poseidon2CompressEmittedStep (compress : Digest → Digest → Digest) :
    StepRel (Digest × Digest) (List (Row Digest)) (Digest × Digest) :=
  fun (root, leaf) rows (root', leaf') =>
    root' = root ∧ leaf' = leaf ∧
      satisfiedEmittedPoseidon2Compress compress rows root leaf

/-- **`poseidon2_emitted_refines_merkle_portal`** — every emitted sponge witness refines to the
Merkle membership portal (`GadgetRefinement.merklePortalStep`). Composes `emittedMerkle_bridge`
with boundary equalities. -/
theorem poseidon2_emitted_refines_merkle_portal (compress : Digest → Digest → Digest) :
    Refines (poseidon2CompressEmittedStep compress) (GadgetRefinement.merklePortalStep compress) := by
  intro ⟨root, leaf⟩ rows ⟨root', leaf'⟩ h
  obtain ⟨hroot, hleaf, hsat⟩ := h
  rw [hroot, hleaf]
  have hsatM : satisfiedEmittedMerkle compress emittedMerkle rows root leaf := by
    dsimp [satisfiedEmittedPoseidon2Compress, satisfiedEmittedMerkle] at hsat ⊢
    simpa [emitted_poseidon2_eq_merkle_constraints] using hsat
  exact ⟨rfl, rfl, (emittedMerkle_bridge compress root leaf).mp ⟨rows, hsatM⟩⟩

end Faithfulness

/-- Existential emitted sponge satisfaction ⟺ portal membership (headline bridge). -/
theorem poseidon2_emitted_iff_portal {Digest : Type}
    (compress : Digest → Digest → Digest) (root leaf : Digest) :
    (∃ rows, satisfiedEmittedPoseidon2Compress compress rows root leaf)
      ↔ MerkleMembers compress root leaf :=
  emittedMerkle_bridge compress root leaf

/-! ## §5 — explicit HOLE portals (state-commit + log sponges). -/

/-- **HOLE W4:** full `StateCommit` frame sponge (`frameDigest` / `compressN`) arithmetized via
the emitted sponge gadget, replacing the abstract `compressNInjective` portal. -/
def hole_state_commit_sponge_binding (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ) : Prop :=
  sorry

/-- **HOLE W4:** growing log-hash sponge (`logHashInjective`) arithmetized via emitted sponge. -/
def hole_log_hash_sponge_binding (LH : List Turn → ℤ) : Prop :=
  sorry

/-! ## §6 — canonical wire (`#guard`-pinned golden for Rust decoder). -/

/-- Full JSON wire string for the sponge-compress gadget. -/
def poseidon2CompressWire : String := emitMerkleJson emittedPoseidon2Compress

#guard (poseidon2CompressWire ==
  r#"{"name":"dregg-poseidon2-compress-v1","trace_width":6,"public_input_count":2,"constraints":[{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}]}"#)
#guard emittedPoseidon2Compress.name == poseidon2CompressAirName
#guard emittedPoseidon2Compress.constraints.length == 4
#guard emittedPoseidon2Compress.traceWidth == 6

#assert_axioms emit_faithful_poseidon2_compress
#assert_axioms poseidon2_emitted_refines_merkle_portal
#assert_axioms poseidon2_emitted_iff_portal

-- HOLE portals (intentionally omitted from #assert_axioms):
-- hole_state_commit_sponge_binding, hole_log_hash_sponge_binding

end Dregg2.Circuit.Poseidon2Emit