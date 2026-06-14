/-
# `EffectVmEmitBundleFold` — the BUNDLE-TREE FOLD AIR (proof-of-proofs), emitted from Lean (law #1).

The bilateral-bundle "proof-of-proofs" tree fold (`circuit/src/bilateral_aggregation_air.rs::
BundleTreeFoldAir`) is the O(1)-in-children attestation over a set of child `AggregatedBundle`s.
Each child is reduced to a fixed DIGEST (a Poseidon2 hash of its outer PI), and the fold commits a
hash CHAIN over those digests:

  `acc_out[i] = Poseidon2(acc_in[i], digest[i])`   (a 2-to-1 compress per row)
  `acc_in[i+1] = acc_out[i]`                        (chain continuity)

with `acc_in[0]` pinned to the public `initial` accumulator and `acc_out[last]` to the public
`final` accumulator.

## NOT recursion — a hash fold over COMMITMENTS.

Despite the "proof-of-proofs" name, this AIR does NOT verify inner STARK proofs in-circuit. It
folds child bundle DIGESTS (`bundle_digest = Poseidon2(child.outer_pi)` — a hash of public
inputs); the actual per-child STARK verification is done CLASSICALLY by the Rust
`verify_aggregated_tree` (`turn/src/aggregate_bilateral_prover.rs::prove_aggregated_tree` verifies
each child up front, then folds). So the fold is a PURE constraint system — a Merkle/hash chain
over field elements — and is fully expressible as an IR-v2 descriptor (the genuine in-circuit
recursive STARK verification, "CG-1", was always future work and is not what this AIR does).

Until now that AIR was HAND-AUTHORED Rust (a `StarkAir` impl, AIR name `dregg-bundle-tree-fold-v1`)
with a NAMED RESIDUAL: "the row-internal Poseidon2 relation `acc_out == compress(acc_in, digest)`
is enforced cryptographically by the verifier recomputing the chain (custom-STARK has no in-AIR
Poseidon gadget)". THIS module RETIRES that residual: the chip lookup makes the compress a REAL
in-circuit constraint.

## The constraint families (mirrors the Rust AIR, now law-#1, and STRONGER)

* **The compress is REAL** (the chip lookup): `acc_out = Poseidon2(acc_in, digest)` as an arity-2
  chip lookup `(2, [acc_in, digest] padded to CHIP_RATE, acc_out)`. The deployed chip table is the
  REAL permutation with the arity tag at state[4] — byte-identical to `circuit/src/poseidon2.rs::
  hash_2_to_1` (state[0] = acc_in, state[1] = digest, state[4] = 2). This CLOSES the hand-AIR's
  named residual: the row-internal Poseidon2 relation is now an in-circuit constraint, not a
  verifier-side recompute.
* **The boundaries**: `acc_in[0] = pi[initial]` (first-row `piBinding`), `acc_out[last] = pi[final]`
  (last-row `piBinding`).
* **Chain continuity**: `acc_out[i] = acc_in[i+1]` (the two-row `windowGate`).

## The teeth (soundness, proved below)

`fold_rejects_tampered_final` (a last row whose `acc_out` disagrees with the published `final`
accumulator is UNSAT — the Rust `tree_fold_rejects_tampered_final_acc` rejection) and
`fold_compress_is_hashed` (against a sound chip table the `acc_out` column IS the genuine
Poseidon2 of `(acc_in, digest)` — the residual the hand-AIR could only close at the verifier),
axiom-clean.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.EffectVmEmitBundleFold

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The tree-fold trace + PI layout (mirrors the Rust `FOLD_*` constants). -/
namespace Fold

/-- Chain accumulator before absorbing this child. -/
def ACC_IN_COL : Nat := 0
/-- This child's bundle digest. -/
def DIGEST_COL : Nat := 1
/-- Chain accumulator after absorbing this child (`Poseidon2(acc_in, digest)`). -/
def ACC_OUT_COL : Nat := 2
/-- Total trace width. -/
def WIDTH : Nat := 3

/-- Public input: the initial (seed) accumulator. -/
def PI_INITIAL : Nat := 0
/-- Public input: the final accumulator (the outer attestation). -/
def PI_FINAL : Nat := 1
/-- Public input count. -/
def PI_COUNT : Nat := 2

end Fold

/-! ## §2 — Constraint builders. -/

open WindowExpr (loc nxt)

/-- The chip lookup pinning `acc_out = Poseidon2(acc_in, digest)` — an arity-2 absorb of
`[acc_in, digest]` into the `ACC_OUT_COL` digest. (`chipLookupTuple` renders `(2, ins padded to
CHIP_RATE, digestCol)`; the deployed chip table is the REAL permutation with the arity tag at
state[4], byte-identical to `hash_2_to_1`.) This is the constraint the hand-AIR carried as a
verifier-side residual. -/
def compressLookup : VmConstraint2 :=
  .lookup
    { table := .poseidon2
    , tuple := chipLookupTuple [.var Fold.ACC_IN_COL, .var Fold.DIGEST_COL] Fold.ACC_OUT_COL }

/-- First-row boundary `acc_in[0] = pi[initial]`. -/
def firstAccBind : VmConstraint2 :=
  .base (.piBinding .first Fold.ACC_IN_COL Fold.PI_INITIAL)

/-- Last-row boundary `acc_out[last] = pi[final]`. -/
def lastAccBind : VmConstraint2 :=
  .base (.piBinding .last Fold.ACC_OUT_COL Fold.PI_FINAL)

/-- Chain continuity `acc_out[i] = acc_in[i+1]` as a `windowGate`: `local[acc_out] − next[acc_in] = 0`. -/
def chainContinuity : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body := .add (loc Fold.ACC_OUT_COL) (.mul (.const (-1)) (nxt Fold.ACC_IN_COL)) }

/-! ## §3 — Assemble the tree-fold descriptor. -/

/-- The full constraint list of the tree-fold AIR. -/
def foldConstraints : List VmConstraint2 :=
  [ compressLookup
  , firstAccBind
  , lastAccBind
  , chainContinuity ]

/-- The tree-fold descriptor: width 3, 2 public inputs `(initial, final)`, ONE declared table —
the Poseidon2 chip the compress lookup rides. -/
def bundleFoldDescriptor : EffectVmDescriptor2 :=
  { name        := "dregg-bundle-tree-fold-v2"
  , traceWidth  := Fold.WIDTH
  , piCount     := Fold.PI_COUNT
  , tables      := [poseidon2ChipTableDef]
  , constraints := foldConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — Shape tripwires (byte-pinned both sides; the Rust twin pins the same). -/

-- The trace is 3 columns: acc_in, digest, acc_out.
#guard Fold.WIDTH == 3
-- Two public inputs: initial + final accumulator.
#guard bundleFoldDescriptor.piCount == 2
-- 4 constraints: 1 chip lookup + 2 piBindings + 1 window continuity.
#guard foldConstraints.length == 4
-- Exactly one window gate (the chain continuity).
#guard (foldConstraints.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 1
-- Exactly one chip lookup (the compress), and it is arity-2 (the `hash_2_to_1` shape).
#guard (foldConstraints.filter (fun c => match c with | .lookup _ => true | _ => false)).length == 1
-- The descriptor emits a versioned v2 wire string.
#guard (emitVmJson2 bundleFoldDescriptor).startsWith "{\"name\":\"dregg-bundle-tree-fold-v2\",\"ir\":2"

/-! ## §5 — The teeth (soundness): the tampered-final rejection + the real-compress strengthening. -/

/-- The descriptor's per-window denotation against a chip `TraceFamily` and a hash. -/
def foldWindowHolds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ bundleFoldDescriptor.constraints, c.holdsAt hash tf env isFirst isLast

/-- **The tampered-final tooth.** A LAST row whose `acc_out` disagrees with the published `final`
accumulator cannot satisfy the descriptor — exactly the boundary that binds the fold output to the
children (the Rust `tree_fold_rejects_tampered_final_acc` rejection). -/
theorem fold_rejects_tampered_final
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hbad : env.loc Fold.ACC_OUT_COL ≠ env.pub Fold.PI_FINAL) :
    ¬ foldWindowHolds hash tf env false true := by
  intro h
  have hmem : lastAccBind ∈ bundleFoldDescriptor.constraints := by
    show _ ∈ foldConstraints
    simp [foldConstraints]
  have hc := h _ hmem
  -- `lastAccBind` on the last row asserts `loc acc_out = pub final` (the `isLast = true` hyp
  -- discharged by `simp`), contradicting `hbad`.
  simp only [lastAccBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hbad (hc trivial)

/-- **The real-compress tooth (retires the hand-AIR's residual).** Against a SOUND chip table, the
descriptor's compress lookup ENFORCES `acc_out = Poseidon2(acc_in, digest)`: the `acc_out` column
is the genuine hash, not a prover-chosen value the verifier must recompute. The hand-`StarkAir`
carried this as a named verifier-side residual ("custom-STARK has no in-AIR Poseidon gadget"). -/
theorem fold_compress_is_hashed
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hSound : ChipTableSound hash (tf .poseidon2))
    (h : foldWindowHolds hash tf env isFirst isLast) :
    env.loc Fold.ACC_OUT_COL = hash [env.loc Fold.ACC_IN_COL, env.loc Fold.DIGEST_COL] := by
  have hmem : compressLookup ∈ bundleFoldDescriptor.constraints := by
    show _ ∈ foldConstraints
    simp [foldConstraints]
  have hc := h _ hmem
  simp only [compressLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  have hkey := chip_lookup_sound hash (tf .poseidon2) hSound env.loc
    [.var Fold.ACC_IN_COL, .var Fold.DIGEST_COL] Fold.ACC_OUT_COL (by unfold CHIP_RATE; decide) hc
  simpa [EmittedExpr.eval] using hkey

#assert_axioms fold_rejects_tampered_final
#assert_axioms fold_compress_is_hashed

end Dregg2.Circuit.Emit.EffectVmEmitBundleFold
