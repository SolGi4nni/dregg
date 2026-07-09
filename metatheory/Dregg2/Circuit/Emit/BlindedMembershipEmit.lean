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
   emitVmJson2 WindowExpr WindowConstraint)

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

/-! ============================================================================================
## §5 — the DEPTH-GENERAL, 4-ARY, GENERAL-POSITION blinded ring-membership family
(Golden Lift, stage 3d-DIM).

The depth-2 `blindedMembershipDesc` above is single-row / leftmost-child, so it cannot carry
PRODUCTION presentations (`bridge/present.rs:1871`: DEPTH-8, `position = i % 4`). This section adds
the depth-general twin, mirroring `circuit/src/membership_descriptor_4ary.rs`
(`membership_descriptor_of_depth_4ary`): ONE 4-ary Merkle level per trace row (depth in the trace
HEIGHT + the descriptor NAME), carrying the two position bits + the ordered-children selection gates
+ the arity-4 `hash_4_to_1` parent chip PER ROW, PLUS the arity-2 blinding tooth binding
`blinded_leaf = hash_2_to_1(cur, blinding)` (the row-0 `cur` IS the hidden member `leaf_hash`). PIs
stay `[blinded_leaf, root]`.

The constraint block is depth-UNIFORM (only the `name` carries the depth); the wire golden differs
between depths only in that name digit. The Lean defs mirror the Rust builders term-for-term so the
emitted JSON is byte-identical to what `blinded_membership_descriptor_of_depth_4ary` builds (the Rust
tests cross-check `parse(golden) == builder(depth)`).

### The layout (width 27; path columns 0..17 identical to `membership_descriptor_4ary`). -/

/-- Running hash (row 0 = the hidden member `leaf_hash`; also the blinding tooth's input 0). -/
def gCUR : Nat := 0
/-- The three co-path siblings at this level (HIDDEN). -/
def gSIB0 : Nat := 1
def gSIB1 : Nat := 2
def gSIB2 : Nat := 3
/-- The two position bits (`position = b0 + 2·b1 ∈ {0,1,2,3}`). -/
def gB0 : Nat := 4
def gB1 : Nat := 5
/-- The four ordered children (`children[position] = cur`, siblings fill). -/
def gC0 : Nat := 6
def gC1 : Nat := 7
def gC2 : Nat := 8
def gC3 : Nat := 9
/-- Parent digest = `hash_4_to_1(c0,c1,c2,c3)` (chip out0); last-row PI-pinned to the root. -/
def gPAR : Nat := 10
/-- The 7 witnessed permutation lanes 1..7 of `gPAR`. -/
def gPATH_LANES : List Nat := [11, 12, 13, 14, 15, 16, 17]
/-- The fresh blinding factor (HIDDEN — this hiddenness gives unlinkability). -/
def gBLINDING : Nat := 18
/-- The published blinded leaf = `hash_2_to_1(cur, blinding)`; row-0 PI-pinned. -/
def gBLINDED_LEAF : Nat := 19
/-- The 7 witnessed permutation lanes 1..7 of the blinding tooth. -/
def gBLIND_LANES : List Nat := [20, 21, 22, 23, 24, 25, 26]
/-- Total main-trace width: the 18 path columns + 2 blinding semantic + 7 blinding lanes. -/
def gWIDTH : Nat := 27

/-- PI slot 0: the published `blinded_leaf`. -/
def gPI_BLINDED_LEAF : Nat := 0
/-- PI slot 1: the public federation Merkle `root`. -/
def gPI_ROOT : Nat := 1

/-! ### The arithmetic-expression builders (mirror `membership_descriptor_4ary.rs` term-for-term). -/

def ev (i : Nat) : EmittedExpr := .var i
def ek (c : Int) : EmittedExpr := .const c
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
/-- `-e` = `(-1)·e`. -/
def eneg (e : EmittedExpr) : EmittedExpr := emul (ek (-1)) e
/-- `a - b`. -/
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)
/-- `1 - e`. -/
def eoneMinus (e : EmittedExpr) : EmittedExpr := eadd (ek 1) (eneg e)

/-- `bit·bit - bit` — the `bit ∈ {0,1}` gate body. -/
def bitBinaryBody (bit : Nat) : EmittedExpr := eadd (emul (ev bit) (ev bit)) (eneg (ev bit))

-- The four Lagrange position indicators, as bit products (degree 2, integer coefficients).
def indL0 : EmittedExpr := emul (eoneMinus (ev gB0)) (eoneMinus (ev gB1))
def indL1 : EmittedExpr := emul (ev gB0) (eoneMinus (ev gB1))
def indL2 : EmittedExpr := emul (eoneMinus (ev gB0)) (ev gB1)
def indL3 : EmittedExpr := emul (ev gB0) (ev gB1)

-- The four child-selection gate bodies `c_j - selection_j` (EXACTLY production's arrangement).
def child0Body : EmittedExpr :=
  esub (esub (ev gC0) (ev gSIB0)) (emul indL0 (esub (ev gCUR) (ev gSIB0)))
def child1Body : EmittedExpr :=
  esub (ev gC1)
    (eadd (eadd (emul (ev gSIB0) indL0) (emul (ev gCUR) indL1))
      (emul (ev gSIB1) (eadd indL2 indL3)))
def child2Body : EmittedExpr :=
  esub (ev gC2)
    (eadd (eadd (emul (ev gSIB1) (eadd indL0 indL1)) (emul (ev gCUR) indL2))
      (emul (ev gSIB2) indL3))
def child3Body : EmittedExpr :=
  esub (esub (ev gC3) (ev gSIB2)) (emul indL3 (esub (ev gCUR) (ev gSIB2)))

/-- The per-row constraint bodies (bit-binary ×2 + child-selection ×4), in Rust's order. -/
def gPerRowBodies : List EmittedExpr :=
  [bitBinaryBody gB0, bitBinaryBody gB1, child0Body, child1Body, child2Body, child3Body]

/-! ### The arrangement the child-selection gates enforce (the LEVEL step function).

The four child-selection gates + the two bit-binary gates together PIN the ordered children to the
positional arrangement: the running hash `cur` sits at its `position = b0 + 2·b1` slot and the three
siblings fill the rest in order — EXACTLY `membership_descriptor_4ary::arrange_children`. -/

/-- The ordered-children arrangement at a level given the running hash, siblings, and position bits. -/
def gArrangeList (cur s0 s1 s2 b0 b1 : ℤ) : List ℤ :=
  if b1 = 0 then (if b0 = 0 then [cur, s0, s1, s2] else [s0, cur, s1, s2])
  else (if b0 = 0 then [s0, s1, cur, s2] else [s0, s1, s2, cur])

/-- **`gChildren_arranged`** — the four child columns, on any row satisfying the two bit-binary gates
and the four child-selection gates, ARE the positional arrangement of the running hash and siblings.
This is the tooth that makes the general-position path genuinely bind the member: a forger cannot put
arbitrary children under a level, they must be `cur` (at its slot) plus the real siblings. -/
theorem gChildren_arranged (a : Assignment)
    (hb0 : (bitBinaryBody gB0).eval a = 0) (hb1 : (bitBinaryBody gB1).eval a = 0)
    (h0 : (child0Body).eval a = 0) (h1 : (child1Body).eval a = 0)
    (h2 : (child2Body).eval a = 0) (h3 : (child3Body).eval a = 0) :
    [a gC0, a gC1, a gC2, a gC3]
      = gArrangeList (a gCUR) (a gSIB0) (a gSIB1) (a gSIB2) (a gB0) (a gB1) := by
  simp only [bitBinaryBody, ev, ek, eadd, emul, eneg, EmittedExpr.eval] at hb0 hb1
  have e0 : a gB0 = 0 ∨ a gB0 = 1 := by
    have h : a gB0 * (a gB0 - 1) = 0 := by linear_combination hb0
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have e1 : a gB1 = 0 ∨ a gB1 = 1 := by
    have h : a gB1 * (a gB1 - 1) = 0 := by linear_combination hb1
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  simp only [child0Body, child1Body, child2Body, child3Body,
    indL0, indL1, indL2, indL3, ev, ek, eadd, emul, eneg, esub, eoneMinus, EmittedExpr.eval]
    at h0 h1 h2 h3
  rcases e0 with hb0v | hb0v <;> rcases e1 with hb1v | hb1v
  · have hr : gArrangeList (a gCUR) (a gSIB0) (a gSIB1) (a gSIB2) (a gB0) (a gB1)
        = [a gCUR, a gSIB0, a gSIB1, a gSIB2] := by simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a gCUR) (a gSIB0) (a gSIB1) (a gSIB2) (a gB0) (a gB1)
        = [a gSIB0, a gSIB1, a gCUR, a gSIB2] := by simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a gCUR) (a gSIB0) (a gSIB1) (a gSIB2) (a gB0) (a gB1)
        = [a gSIB0, a gCUR, a gSIB1, a gSIB2] := by simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a gCUR) (a gSIB0) (a gSIB1) (a gSIB2) (a gB0) (a gB1)
        = [a gSIB0, a gSIB1, a gSIB2, a gCUR] := by simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The arity-4 parent chip lookup: `hash_4_to_1(c0,c1,c2,c3)` → `gPAR`, path lanes witnessed. -/
def gParentLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var gC0, .var gC1, .var gC2, .var gC3] gPAR gPATH_LANES⟩

/-- The arity-2 blinding tooth: `hash_2_to_1(cur, blinding)` → `gBLINDED_LEAF`, blind lanes witnessed.
The row-0 `cur` is the hidden `leaf_hash`, so the published `blinded_leaf` commits to the member. -/
def gBlindLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var gCUR, .var gBLINDING] gBLINDED_LEAF gBLIND_LANES⟩

/-- The cross-row continuity gate `next.cur - this.par` (unrolls the level block across rows). -/
def gContWindow : WindowExpr := .add (.nxt gCUR) (.mul (.const (-1)) (.loc gPAR))
def gContinuity : VmConstraint2 := .windowGate ⟨gContWindow, true⟩

/-- The row-0 blinded-leaf pin. -/
def gBlindedLeafPin : VmConstraint2 := .base (.piBinding VmRow.first gBLINDED_LEAF gPI_BLINDED_LEAF)
/-- The last-row root pin (the top parent equals the committed root). -/
def gRootPin : VmConstraint2 := .base (.piBinding VmRow.last gPAR gPI_ROOT)

/-- The last-row re-lowering of the per-row bodies (the transition gates are vacuous on the last row,
so the top level's bits + children would be unconstrained without this). -/
def gLastRowBoundaries : List VmConstraint2 :=
  gPerRowBodies.map (fun b => .base (.boundary VmRow.last b))

/-- The per-row transition gates (bit-binary + child-selection). -/
def gPerRowGates : List VmConstraint2 :=
  gPerRowBodies.map (fun b => .base (.gate b))

/-- The depth-general constraint list, in the EXACT order the Rust builder emits: the 6 per-row
gates, the parent chip, the blinding tooth, the continuity window gate, the two PI pins
(blinded-leaf first / root last), then the 6 last-row re-lowered boundaries. -/
def gConstraints : List VmConstraint2 :=
  gPerRowGates ++ [gParentLookup, gBlindLookup, gContinuity, gBlindedLeafPin, gRootPin]
    ++ gLastRowBoundaries

/-- **`blindedMembership4aryDesc depth`** — the depth-GENERAL, 4-ary, general-position blinded
ring-membership descriptor. Depth-uniform constraints; the depth lives in the trace height + the
`name`. PIs `[blinded_leaf, root]`. The Rust twin is
`blinded_membership_descriptor_of_depth_4ary`. -/
def blindedMembership4aryDesc (depth : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-blinded-membership-4ary-general-depth" ++ toString depth
  , traceWidth  := gWIDTH
  , piCount     := 2
  , tables      := []
  , constraints := gConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ### The byte-pinned wire goldens (depth-2 and the production depth-8; the Rust decoder ingests
these). The constraint block is depth-uniform, so the two strings differ ONLY in the name digit. -/

/-- Byte-pinned depth-2 wire golden (the Rust decoder ingests this). -/
def GOLDEN_4ARY_DEPTH2 : String :=
  "{\"name\":\"dregg-blinded-membership-4ary-general-depth2\",\"ir\":2,\"trace_width\":27,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":18},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":10,\"pi_index\":1},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-- Byte-pinned production depth-8 wire golden (differs from depth-2 only in the name digit). -/
def GOLDEN_4ARY_DEPTH8 : String :=
  "{\"name\":\"dregg-blinded-membership-4ary-general-depth8\",\"ir\":2,\"trace_width\":27,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":18},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":10,\"pi_index\":1},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 (blindedMembership4aryDesc 2) == GOLDEN_4ARY_DEPTH2
#guard emitVmJson2 (blindedMembership4aryDesc 8) == GOLDEN_4ARY_DEPTH8

/-! ### Non-vacuous shape + gate lemmas. -/

/-- The continuity window body vanishes exactly when the levels chain (`next.cur = this.par`). -/
theorem gCont_zero_iff (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv) :
    gContWindow.eval env = 0 ↔ env.nxt gCUR = env.loc gPAR := by
  simp only [gContWindow, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- The blinding tooth tuple has the canonical chip width (arity tag + rate-padded 2 inputs + out0 +
7 lanes) — the arity-2 tooth is well-formed. -/
theorem gBlind_tuple_width :
    (chipLookupTuple [.var gCUR, .var gBLINDING] gBLINDED_LEAF gBLIND_LANES).length
      = 1 + CHIP_RATE + CHIP_OUT_LANES := by
  simp [chipLookupTuple, Dregg2.Circuit.DescriptorIR2.padToE, CHIP_RATE, CHIP_OUT_LANES, gBLIND_LANES]

-- Non-vacuity: the continuity body accepts a chained window and rejects an unchained one.
#guard decide (gContWindow.eval
  ⟨fun i => if i = gPAR then 7 else 0, fun i => if i = gCUR then 7 else 0, fun _ => 0⟩ = 0)
#guard decide (¬ (gContWindow.eval
  ⟨fun _ => 0, fun i => if i = gCUR then 7 else 0, fun _ => 0⟩ = 0))
-- Non-vacuity: a leftmost (pos 0) child arrangement satisfies child0..child3 (b0=b1=0 ⇒ c=cur/sibs),
-- and a MIXED position (b0=1,b1=0 ⇒ pos 1 ⇒ c0=sib0,c1=cur,c2=sib1,c3=sib2) does too — the gates
-- genuinely support general position, not only the leftmost slot.
#guard decide (child0Body.eval (fun i =>
  if i = gCUR then 9 else if i = gSIB0 then 1 else if i = gSIB1 then 2 else if i = gSIB2 then 3
  else if i = gC0 then 9 else if i = gC1 then 1 else if i = gC2 then 2 else if i = gC3 then 3
  else 0) = 0)
#guard decide (child1Body.eval (fun i =>
  if i = gB0 then 1 else if i = gCUR then 9 else if i = gSIB0 then 1 else if i = gSIB1 then 2
  else if i = gSIB2 then 3
  else if i = gC0 then 1 else if i = gC1 then 9 else if i = gC2 then 2 else if i = gC3 then 3
  else 0) = 0)

-- Shape pins.
#guard (blindedMembership4aryDesc 8).traceWidth == gWIDTH
#guard (blindedMembership4aryDesc 8).piCount == 2
#guard (blindedMembership4aryDesc 8).tables.length == 0
#guard gConstraints.length == 17
#guard (blindedMembership4aryDesc 8).name == "dregg-blinded-membership-4ary-general-depth8"
#guard (blindedMembership4aryDesc 2).name == "dregg-blinded-membership-4ary-general-depth2"

#assert_axioms gCont_zero_iff
#assert_axioms gBlind_tuple_width

end Dregg2.Circuit.Emit.BlindedMembershipEmit
