/-
# Dregg2.Circuit.Emit.BlindedMembershipEmit — the BLINDED RING-MEMBERSHIP descriptor
(Golden Lift, stage 3d-1)

## What this file IS (and the deployed semantics it replaces)

The deployed anonymous-credential show proves `issuer ∈ federation` with a HAND-written blinded STARK
(`air_name = BLINDED_MERKLE`, `circuit/src/poseidon2_air.rs:660` `generate_blinded_*`,
`circuit/src/presentation.rs:1377 generate_blinded_merkle_poseidon2_stark_proof`). Its published pi[0]
is `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)` (`poseidon2_air.rs:720`) where the REAL
member `leaf_hash` and the fresh `blinding_factor` are BOTH hidden; a 4-ary Poseidon2 Merkle path
proves `leaf_hash ∈ tree(root)` (pi[1]). Because the blinding factor is fresh per presentation, two
shows of ONE credential publish two DIFFERENT `blinded_leaf` — the unlinkability the
`credentials/tests/anonymity_soundness.rs` test depends on — yet each is still bound to the same
`leaf_hash` under the same public `root`.

That STARK was an OFF-descriptor named leaf: the executor verified the blinding+membership, but a light
client / the recursion fold saw only the two published felts, with nothing in the light-client-visible
descriptor forcing `blinded_leaf` to actually BE `hash_2_to_1` of a `leaf_hash` that sits under `root`.
`blindedMembershipDesc` closes it: both the blinding and the membership are now genuinely CONSTRAINED
in-circuit PIs (chip lookups + a Merkle chip chain), re-verifiable from the descriptor alone.

## The two constraint mechanisms (the load-bearing edges internalized here)

1. **Unlinkability blinding tooth** — an arity-2 `TID_P2` Poseidon2 chip lookup absorbing
   `[leaf_hash, blinding_factor]` and binding out0 to the `BLINDED_LEAF` column
   (`hash_2_to_1`, arity tag `2` at capacity `state[4]`, `poseidon2.rs:365`). `leaf_hash`
   (`LEAF`) and `blinding_factor` (`BLINDING`) are HIDDEN witness columns — NOT PIs. `blinding_factor`
   being hidden and fresh is precisely what gives UNLINKABILITY: the same `leaf_hash` blinded twice
   with different factors yields two different `blinded_leaf`, each a genuine Poseidon2 image. This
   mirrors `BoundPresentationEmit`'s tag tooth (hidden randomness → published hash), at arity 2.

2. **Ring-membership path** — the same 4-ary Poseidon2 Merkle chip chain as
   `MerkleMembershipEmit.merkleMembershipDesc` (depth 2): two `child → parent` `hash_4_to_1` chip
   lookups (`poseidon2.rs:349`), a chain-continuity gate tying the levels (`CUR1 = PARENT0`, on EVERY
   row — transition gate + last-row boundary fix, the `0f8d478b2` shape), and the last parent
   `PiBinding`-pinned to the public `root` PI. Crucially the path's LEAF column is the SAME `LEAF`
   column the blinding tooth absorbs, so the published `blinded_leaf` commits to exactly the
   `leaf_hash` proven to sit under `root`.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + a genuinely-proven, non-vacuous
shape lemma. `#assert_axioms` ⊆ {}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.BlindedMembershipEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

set_option autoImplicit false

/-! ## §1 — the trace column layout (a single logical row, repeated to a power-of-two height).

The 4-ary depth-2 Merkle path (leaf + two sibling triples + the two parents) sits first — its LEAF
column IS the hidden member `leaf_hash`. Past it sit the blinding witness/PI columns and the three
Poseidon2 chip lane blocks. -/

/-- Merkle level-0 path element = the member `leaf_hash` (HIDDEN; also the blinding tooth's input). -/
def LEAF : Nat := 0
/-- Level-0 siblings (the three other children of the leaf's parent; HIDDEN). -/
def SIB0A : Nat := 1
def SIB0B : Nat := 2
def SIB0C : Nat := 3
/-- Level-0 parent digest = `hash_4_to_1(leaf, sib0a, sib0b, sib0c)` (chip lookup out0; HIDDEN). -/
def PARENT0 : Nat := 4
/-- Level-1 path element (the chained input; the continuity gate forces `CUR1 = PARENT0`; HIDDEN). -/
def CUR1 : Nat := 5
/-- Level-1 siblings (HIDDEN). -/
def SIB1A : Nat := 6
def SIB1B : Nat := 7
def SIB1C : Nat := 8
/-- Level-1 parent digest = the ROOT = `hash_4_to_1(cur1, sib1a, sib1b, sib1c)`; pinned to `ROOT_PI`. -/
def PARENT1 : Nat := 9
/-- The blinding factor — fresh per presentation; HIDDEN (this hiddenness gives unlinkability). -/
def BLINDING : Nat := 10
/-- The published blinded leaf = `hash_2_to_1(leaf_hash, blinding)`; pinned to `BLINDED_LEAF_PI`. -/
def BLINDED_LEAF : Nat := 11

/-- The seven exposed permutation lane columns 1..7 of each chip lookup (out0 is the digest above). -/
def LEVEL0_LANES : List Nat := [12, 13, 14, 15, 16, 17, 18]
def LEVEL1_LANES : List Nat := [19, 20, 21, 22, 23, 24, 25]
def BLIND_LANES  : List Nat := [26, 27, 28, 29, 30, 31, 32]

/-- Total main-trace width: 12 base columns + 7·3 chip lane blocks. -/
def BLINDED_WIDTH : Nat := 33

/-- PI slot 0: the published `blinded_leaf` (the unlinkable commitment). -/
def BLINDED_LEAF_PI : Nat := 0
/-- PI slot 1: the public federation Merkle `root`. -/
def ROOT_PI : Nat := 1
/-- Number of public inputs: `[blinded_leaf, root]`. -/
def PI_COUNT : Nat := 2

/-! ## §2 — the constraint list (Merkle chip chain · blinding chip lookup · pins · continuity). -/

/-- Level-0 `child → parent`: arity-4 `Poseidon2Chip` lookup absorbing `[leaf, sib0a, sib0b, sib0c]`,
binding out0 to `PARENT0`. -/
def level0Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var LEAF, .var SIB0A, .var SIB0B, .var SIB0C] PARENT0 LEVEL0_LANES⟩

/-- Level-1 `child → parent`: arity-4 `Poseidon2Chip` lookup absorbing `[cur1, sib1a, sib1b, sib1c]`,
binding out0 to `PARENT1` (the root). -/
def level1Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var CUR1, .var SIB1A, .var SIB1B, .var SIB1C] PARENT1 LEVEL1_LANES⟩

/-- **The blinding tooth** — an arity-2 `TID_P2` Poseidon2 lookup absorbing `[leaf_hash, blinding]`,
binding out0 to `BLINDED_LEAF`. The in-circuit twin of `blinded_leaf = hash_2_to_1(leaf_hash,
blinding_factor)` (`poseidon2_air.rs:720`). `leaf_hash` is the SAME `LEAF` column the Merkle path
proves under `root`, so the published `blinded_leaf` commits to a genuine member. -/
def blindLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var LEAF, .var BLINDING] BLINDED_LEAF BLIND_LANES⟩

/-- The chain-continuity gate body: `CUR1 - PARENT0` (the next level's path input equals this level's
parent — the emitted twin of `poseidon2_air.rs`'s chain-continuity constraint). -/
def contBody : EmittedExpr := .add (.var CUR1) (.mul (.const (-1)) (.var PARENT0))

/-- The chain-continuity Base gate — a `when_transition` constraint (vacuous on the LAST row). Binds
`CUR1 = PARENT0` on rows `0..n-2`. -/
def continuityGate : VmConstraint2 := .base (.gate contBody)

/-- **The last-row continuity fix** (`adjLastOrderFix` shape, commit `0f8d478b2`): a `.boundary
VmRow.last` counterpart firing on the last row so the level-tie `CUR1 = PARENT0` holds on EVERY row
(a height-1 trace is not under-constrained — the `MerkleMembershipRung2` forgery class). -/
def continuityLastFix : VmConstraint2 := .base (.boundary VmRow.last contBody)

/-- The root pin: `PARENT1` (last parent) equals the public root PI on the first row. -/
def rootPin : VmConstraint2 := .base (.piBinding VmRow.first PARENT1 ROOT_PI)

/-- The blinded-leaf pin: `BLINDED_LEAF` equals the published `blinded_leaf` PI on the first row. -/
def blindedLeafPin : VmConstraint2 := .base (.piBinding VmRow.first BLINDED_LEAF BLINDED_LEAF_PI)

/-- **`blindedMembershipDesc`** — the blinded ring-membership descriptor. PIs `[blinded_leaf, root]`;
hidden witnesses for `leaf_hash`, `blinding_factor`, and the whole Merkle path. Constraints: the two
`child → parent` chip lookups, the arity-2 blinding lookup, the level-tying continuity gate, the two
first-row PI pins, and the last-row continuity fix. The chip table (`TID_P2`) is IMPLICITLY present
(Presence-detected from the lookups), so `tables` is empty exactly as `merkleMembershipDesc` leaves
it. The level-tie is enforced on EVERY row (transition `continuityGate` for rows `0..n-2`,
`continuityLastFix` for the last row). -/
def blindedMembershipDesc : EffectVmDescriptor2 :=
  { name        := "dregg-blinded-membership::v1"
  , traceWidth  := BLINDED_WIDTH
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := [level0Lookup, level1Lookup, blindLookup, continuityGate, rootPin,
                    blindedLeafPin, continuityLastFix]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — the byte-pinned wire golden (the Rust decoder ingests THIS string).

Written verbatim to `circuit/descriptors/by-name/blinded-membership.json`; `parse_vm_descriptor2`
ingests it. A drift on either side breaks THIS `#guard`. -/

#guard emitVmJson2 blindedMembershipDesc ==
  "{\"name\":\"dregg-blinded-membership::v1\",\"ir\":2,\"trace_width\":33,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":10},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":0},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — a genuinely-proven, non-vacuous semantic lemma + shape pins + axiom hygiene. -/

/-- The continuity gate body is zero EXACTLY when the levels chain (`CUR1 = PARENT0`) — TRUE when
they agree, FALSE otherwise. The Lean face of the chain-continuity the emitted `.gate` enforces. -/
theorem continuity_body_zero_iff (a : Assignment) :
    contBody.eval a = 0 ↔ a CUR1 = a PARENT0 := by
  simp only [contBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The blinding chip tuple has the canonical chip width `1 + CHIP_RATE + CHIP_OUT_LANES` (arity tag,
the rate-padded 2-input preimage, out0 = the blinded leaf, and the 7 lanes). -/
theorem blindLookup_tuple_width :
    (chipLookupTuple [.var LEAF, .var BLINDING] BLINDED_LEAF BLIND_LANES).length
      = 1 + CHIP_RATE + CHIP_OUT_LANES := by
  simp [chipLookupTuple, Dregg2.Circuit.DescriptorIR2.padToE, CHIP_RATE, CHIP_OUT_LANES, BLIND_LANES]

-- Non-vacuity witnesses: the gate ACCEPTS a chained assignment and REJECTS an unchained one.
#guard decide (contBody.eval (fun i => if i = CUR1 ∨ i = PARENT0 then 7 else 0) = 0)
#guard decide (¬ (contBody.eval (fun i => if i = CUR1 then 7 else 0) = 0))

-- Shape pins.
#guard blindedMembershipDesc.traceWidth == BLINDED_WIDTH
#guard blindedMembershipDesc.piCount == PI_COUNT
#guard blindedMembershipDesc.constraints.length == 7
#guard blindedMembershipDesc.tables.length == 0
#guard (chipLookupTuple [.var LEAF, .var BLINDING] BLINDED_LEAF BLIND_LANES).length
         == 1 + CHIP_RATE + CHIP_OUT_LANES

#assert_axioms continuity_body_zero_iff

end Dregg2.Circuit.Emit.BlindedMembershipEmit
