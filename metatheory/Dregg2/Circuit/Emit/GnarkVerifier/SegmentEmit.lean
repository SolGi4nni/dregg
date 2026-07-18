/-
# Dregg2.Circuit.Emit.GnarkVerifier.SegmentEmit — the settlement SEGMENT BIND, emitted +
leaf-refined.

THE CHECK (deployed: `chain/gnark/settlement_circuit.go:241–264`): the first 25 lanes of
the shrink proof's `expose_claim` public values — the transcript-absorbed, AIR-constrained
claim channel — ARE the 25 Groth16 public inputs, lane for lane, in the pinned order
`genesis8 ++ final8 ++ numTurns ++ chainDigest8` (`fri_verifier.go`: `DigestWidth = 8`,
`NumPublicInputs = 3·8+1 = 25`). Four `api.AssertIsEqual` loops, nothing else.

THE SPEC it refines: `verifyAlgo`/`verifyAlgoO` tooth 3 — `FriVerifier.segmentTooth`
(`FriVerifier.lean:700`): `proof.exposedSegment = pub.segment`, the 25 public lanes equal
the exposed claim lanes.

Deliverables (all ∀-theorems over every pair of 25-lane vectors, not `#guard` samples):

  * `segment_refines` — gHolds (the LOWERED genuine R1CS of the emitted package, canonical
    witness) ↔ `claim = stmt`, the deployed check as list equality.
  * `segment_refines_emitted` — the same at the emitted wire form (via `emit_faithful`).
  * `segment_rejects_tamper` — the reject polarity, explicit: ANY divergence kills gHolds.
  * `segment_sound_any_r1cs_witness` — STRONGER than the toy's boolean-hint face: the
    segment bind is purely linear (zero aux variables minted), so ANY satisfying R1CS
    witness agreeing on the frontend lanes forces `claim = stmt` — no hint-honesty
    hypothesis at all (rides the foundation's `lower_sound`).
  * `segment_refines_segmentTooth` — the tie to THE spec: gHolds ↔
    `segmentTooth proof pub = true` for the verifier's own `BatchProofData`/`WrapPublics`.

Layout: vars 0–24 = the 25 public inputs in the pinned order (0–7 GenesisRoot, 8–15
FinalRoot, 16 NumTurns, 17–24 ChainDigest); vars 25–49 = the claim-channel slice of
`PrefixObs` (`claim[0..24]`, witness lanes). `segmentAsserts_go_blocks` pins by `rfl` that
the uniform 25-lane bind IS the Go four-loop structure.

KAT anchor: the gold vector is the REAL deployed claim channel —
`chain/gnark/fixtures/apex_shrink_fri_real.json` `table_publics[claim_instance][0:25]`
(the Rust-emitted apex shrink fixture the Go tests replay; NumTurns lane = 2). `#guard`s
exercise accept, per-lane tamper, and lane-SWAP tamper (order is load-bearing) at all
three levels (frontend / lowered R1CS / emitted wire form).

Classified seam (named): canonicity of the lanes is NOT this check's job — the deployed
circuit range-checks every public lane and every `PrefixObs` lane separately
(`settlement_circuit.go:213–220` + the challenger's observe-side canonicity binding;
Lean side: `CanonicityToy`). This module is exactly the equality tooth, as the Go is.
-/
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr

/-! ## §1 The pinned lane geometry (fri_verifier.go). -/

/-- `DigestWidth` (fri_verifier.go:30): BabyBear lanes per digest. -/
def digestWidth : ℕ := 8

/-- `NumPublicInputs` (fri_verifier.go:34): `3·DigestWidth + 1 = 25` — genesis8 ++
final8 ++ numTurns ++ chainDigest8, the pinned public-statement order. -/
def numPublicLanes : ℕ := 3 * digestWidth + 1

/-- The frontend-variable base of the claim-channel lanes: vars `0–24` are the public
statement, vars `25–49` the claim channel (`claim[0..24]`). -/
def claimBase : ℕ := numPublicLanes

example : numPublicLanes = 25 := rfl

/-! ## §2 The circuit — the Go segment bind as an `R1csFr` op-DAG. -/

/-- One Go bind loop: for `i < n`, `api.AssertIsEqual(claim[off+i], public[off+i])` —
claim lane on the left, public lane on the right, exactly the deployed argument order. -/
def bindBlock (off n : ℕ) : List (Wire × Wire) :=
  (List.range n).map fun i => (Wire.var (claimBase + (off + i)), Wire.var (off + i))

/-- The uniform 25-lane bind: `claim[k] = public[k]` for every `k < 25`. -/
def segmentAsserts : List (Wire × Wire) :=
  (List.range numPublicLanes).map fun k => (Wire.var (claimBase + k), Wire.var k)

/-- **The segment-bind circuit** (settlement_circuit.go:241–264). -/
def segmentCircuit : Circuit := ⟨segmentAsserts⟩

/-- The uniform bind IS the deployed four-loop structure — genesis (k=0..7), final
(k=8..15), numTurns (k=16), chainDigest (k=17..24) — definitionally. -/
theorem segmentAsserts_go_blocks :
    segmentAsserts
      = bindBlock 0 digestWidth ++ bindBlock digestWidth digestWidth
        ++ bindBlock (2 * digestWidth) 1 ++ bindBlock (2 * digestWidth + 1) digestWidth :=
  rfl

/-- The emission package: the 25 named public lanes in pinned order, one recorded
`AssertIsEqual` invocation per lane (claim var, public var), the circuit above. -/
def segmentData : GnarkCircuitData :=
  { name         := "settlement_segment_bind_v1"
    publicInputs :=
      ((List.range digestWidth).map fun i => (s!"genesis_root[{i}]", i))
        ++ ((List.range digestWidth).map fun i => (s!"final_root[{i}]", digestWidth + i))
        ++ [("num_turns", 2 * digestWidth)]
        ++ ((List.range digestWidth).map fun i =>
              (s!"chain_digest[{i}]", 2 * digestWidth + 1 + i))
    gadgets      :=
      (List.range numPublicLanes).map fun k => ⟨"AssertIsEqual", [claimBase + k, k]⟩
    circuit      := segmentCircuit }

/-! ## §3 The witness encoding. -/

/-- **The witness encoding**: public statement lanes on vars `0–24`, claim-channel lanes
on vars `25–49` (out-of-range defaults to `0`; no constraint mentions those). -/
def segAsg (stmt claim : List Fr) : Assignment := fun i =>
  if i < claimBase then stmt.getD i 0 else claim.getD (i - claimBase) 0

theorem segAsg_claim (stmt claim : List Fr) (k : ℕ) :
    segAsg stmt claim (claimBase + k) = claim.getD k 0 := by
  have h : ¬ claimBase + k < claimBase := by omega
  simp [segAsg, h]

theorem segAsg_stmt (stmt claim : List Fr) (k : ℕ) (hk : k < claimBase) :
    segAsg stmt claim k = stmt.getD k 0 := by
  simp [segAsg, hk]

/-! ## §4 The frontend ∀-theorem. -/

/-- Frontend acceptance is the pointwise 25-lane binding. -/
theorem segment_frontend_pointwise (a : Assignment) :
    segmentCircuit.satisfied a ↔ ∀ k, k < numPublicLanes → a (claimBase + k) = a k := by
  show (∀ p ∈ segmentAsserts, p.1.eval a = p.2.eval a) ↔ _
  simp [segmentAsserts, Wire.eval]

/-- Pointwise `getD` agreement below a shared length is list equality. -/
private theorem getD_pointwise_iff (l₁ l₂ : List Fr) (n : ℕ)
    (h₁ : l₁.length = n) (h₂ : l₂.length = n) :
    (∀ k, k < n → l₁.getD k 0 = l₂.getD k 0) ↔ l₁ = l₂ := by
  constructor
  · intro h
    refine List.ext_getElem (h₁.trans h₂.symm) fun i hi₁ hi₂ => ?_
    have hk := h i (h₁ ▸ hi₁)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂, Option.getD_some] at hk
  · rintro rfl k _
    rfl

/-- **The frontend face**: for every pair of 25-lane vectors, the segment circuit under
the encoding accepts IFF the exposed claim lanes EQUAL the public statement lanes —
`segmentTooth`'s list equality, lane for lane in the pinned order. -/
theorem segment_frontend (stmt claim : List Fr)
    (hs : stmt.length = numPublicLanes) (hc : claim.length = numPublicLanes) :
    segmentCircuit.satisfied (segAsg stmt claim) ↔ claim = stmt := by
  rw [segment_frontend_pointwise]
  have hpt : ∀ k, k < numPublicLanes →
      ((segAsg stmt claim (claimBase + k) = segAsg stmt claim k)
        ↔ claim.getD k 0 = stmt.getD k 0) := by
    intro k hk
    rw [segAsg_claim, segAsg_stmt _ _ _ hk]
  constructor
  · intro h
    exact (getD_pointwise_iff claim stmt numPublicLanes hc hs).mp
      fun k hk => (hpt k hk).mp (h k hk)
  · intro heq k hk
    exact (hpt k hk).mpr
      ((getD_pointwise_iff claim stmt numPublicLanes hc hs).mpr heq k hk)

/-! ## §5 THE LEAF REFINEMENT — the deliverables. -/

/-- **`segment_refines`** — the leaf ∀-refinement: the LOWERED genuine R1CS of the
emitted segment-bind package, under the canonical witness extension of the encoding, is
satisfied IFF the 25 exposed claim lanes equal the 25 public statement lanes — for EVERY
pair of 25-lane vectors over `Fr`. Spec side = the deployed check
(settlement_circuit.go:241–264) = `verifyAlgoO`'s `segmentTooth` list equality. -/
theorem segment_refines (stmt claim : List Fr)
    (hs : stmt.length = numPublicLanes) (hc : claim.length = numPublicLanes) :
    gHolds segmentData (segAsg stmt claim) ↔ claim = stmt := by
  unfold gHolds
  rw [← R1csFr.gHolds]
  exact segment_frontend stmt claim hs hc

/-- The same ∀-refinement at the EMITTED wire form (composing `emit_faithful`): the bytes
the JSON grammar renders denote exactly the segment equality. -/
theorem segment_refines_emitted (stmt claim : List Fr)
    (hs : stmt.length = numPublicLanes) (hc : claim.length = numPublicLanes) :
    satisfiedEmitted (emit segmentData) (segAsg stmt claim) ↔ claim = stmt :=
  (emit_faithful segmentData (segAsg stmt claim)).symm.trans
    (segment_refines stmt claim hs hc)

/-- **The reject polarity, explicit**: ANY divergence between the exposed claim lanes and
the public statement — one tampered lane, swapped lanes, anything — makes the lowered
R1CS UNSATISFIABLE by the canonical witness. -/
theorem segment_rejects_tamper (stmt claim : List Fr)
    (hs : stmt.length = numPublicLanes) (hc : claim.length = numPublicLanes)
    (hne : claim ≠ stmt) :
    ¬ gHolds segmentData (segAsg stmt claim) :=
  fun h => hne ((segment_refines stmt claim hs hc).mp h)

/-- **The adversarial face — no hint hypothesis at all.** The segment bind is purely
linear (every wire a `var`; ZERO aux variables minted), so unlike the canonicity toy's
boolean-hint face this needs NO honesty assumption on any witness region: ANY R1CS
witness that satisfies the lowered system and carries the encoded lanes on the frontend
variables forces `claim = stmt`. Rides the foundation's `lower_sound`. -/
theorem segment_sound_any_r1cs_witness (stmt claim : List Fr)
    (hs : stmt.length = numPublicLanes) (hc : claim.length = numPublicLanes)
    (z : RAssignment) (hinl : ∀ v, z (.inl v) = segAsg stmt claim v)
    (hsat : r1csSatisfied segmentData.circuit.lower z) :
    claim = stmt :=
  (segment_frontend stmt claim hs hc).mp
    (lower_sound segmentData.circuit (segAsg stmt claim) z hinl hsat)

/-- **The tie to THE spec**: for the verifier's own `BatchProofData`/`WrapPublics` (the
objects `verifyAlgo`/`verifyAlgoO` consume), gHolds of the emitted segment bind under the
encoding of `pub.segment`/`proof.exposedSegment` IS `segmentTooth proof pub = true` —
tooth 3 of the specified verifier, verbatim. -/
theorem segment_refines_segmentTooth
    (proof : Dregg2.Circuit.FriVerifier.BatchProofData Fr)
    (pub : Dregg2.Circuit.FriVerifier.WrapPublics Fr)
    (hs : pub.segment.length = numPublicLanes)
    (hc : proof.exposedSegment.length = numPublicLanes) :
    gHolds segmentData (segAsg pub.segment proof.exposedSegment)
      ↔ Dregg2.Circuit.FriVerifier.segmentTooth proof pub = true := by
  rw [segment_refines _ _ hs hc]
  simp [Dregg2.Circuit.FriVerifier.segmentTooth]

#assert_axioms segment_frontend
#assert_axioms segment_refines
#assert_axioms segment_refines_emitted
#assert_axioms segment_rejects_tamper
#assert_axioms segment_sound_any_r1cs_witness
#assert_axioms segment_refines_segmentTooth

/-! ## §6 Teeth — the GOLD-VECTOR KAT against the deployed Go.

The 25 claim lanes of the REAL apex shrink fixture
(`chain/gnark/fixtures/apex_shrink_fri_real.json`, `table_publics[claim_instance][0:25]`
— the Rust-emitted fixture `apex_shrink_real_fixture_test.go` replays through the
deployed `SettlementCircuit`): genesis8 ++ final8 ++ [2] (NumTurns) ++ chainDigest8, all
canonical BabyBear residues. The deployed circuit ACCEPTS this claim channel against
these publics; both tampers below are rejected by the same Go asserts. -/

/-- The gold claim channel (25 lanes, pinned order; NumTurns lane = 2). -/
def goldClaimLanes : List Fr :=
  [421210617, 1637814550, 431291584, 1953496675, 369364366, 1006647231, 1866996710,
   48274474,
   475853519, 766719301, 209460128, 156803433, 548349625, 139347276, 174962960,
   1721084437,
   2,
   1452650278, 1371598315, 900534217, 247034909, 1097876273, 883942418, 247917708,
   237544049]

example : goldClaimLanes.length = numPublicLanes := rfl

/-- Per-lane tamper: NumTurns lane (k = 16) bumped 2 → 3. -/
def goldTamperedNumTurns : List Fr := goldClaimLanes.set 16 3

/-- Order tamper: genesis lanes 0 and 1 SWAPPED (same multiset — lane-for-lane order is
what the bind pins). -/
def goldSwapped : List Fr := (goldClaimLanes.set 0 1637814550).set 1 421210617

-- Frontend: the real claim channel accepts; both tampers reject.
#guard segmentCircuit.satisfied (segAsg goldClaimLanes goldClaimLanes)
#guard ¬ segmentCircuit.satisfied (segAsg goldClaimLanes goldTamperedNumTurns)
#guard ¬ segmentCircuit.satisfied (segAsg goldClaimLanes goldSwapped)
-- Lowered R1CS: same three, through the genuine bilinear system.
#guard r1csSatisfied segmentData.circuit.lower
  (segmentData.circuit.extend (segAsg goldClaimLanes goldClaimLanes))
#guard ¬ r1csSatisfied segmentData.circuit.lower
  (segmentData.circuit.extend (segAsg goldClaimLanes goldTamperedNumTurns))
#guard ¬ r1csSatisfied segmentData.circuit.lower
  (segmentData.circuit.extend (segAsg goldClaimLanes goldSwapped))
-- Emitted wire form: same three, on the bytes-side denotation.
#guard satisfiedEmitted (emit segmentData) (segAsg goldClaimLanes goldClaimLanes)
#guard ¬ satisfiedEmitted (emit segmentData) (segAsg goldClaimLanes goldTamperedNumTurns)
#guard ¬ satisfiedEmitted (emit segmentData) (segAsg goldClaimLanes goldSwapped)

end Dregg2.Circuit.Emit.GnarkVerifier
