/-
# Dregg2.Circuit.Emit.BoundPresentationEmit — the BOUND-PRESENTATION descriptor (Golden Lift, stage 1)

## What this file IS (and the gap it closes)

`PresentationEmit.presentationFreshnessDesc` PiBinding-copies the 19 summary felts
(`federation_root, request_predicate(8), timestamp, presentation_tag, revealed_facts(8)`) and
internalizes the freshness range gadget. But `PRESENTATION_TAG` (summary col 10) is bound ONLY as a
narrow PI copy — its HASH well-formedness (`tag = Poseidon2(final_root, randomness, nonce)`,
`binding.rs:302 compute_presentation_tag` → `:345 compute_presentation_tag_narrow`) was left an
OFF-descriptor named STARK leaf, verified by the executor and INVISIBLE to a light client / the
recursion fold. That is a `carried-but-not-constrained` gap of the exact class the adversarial audit
flagged: the tag value rides in the trace as a public input, but nothing in the light-client-visible
descriptor forces it to actually BE the hash of its preimage.

`boundPresentationDesc` closes it: the presentation-tag PI is now a genuinely CONSTRAINED public
input, tied IN-CIRCUIT to `Poseidon2(final_root, presentation_randomness, verifier_nonce)` by an
arity-4 `TID_P2` Poseidon2 chip lookup (the same lever `MerkleMembershipEmit` uses for its
`hash_4_to_1` levels). Now a light client / the aggregation fold re-verifies the tag binding from the
descriptor alone.

## The tag-binding tooth (the load-bearing edge internalized here)

`compute_presentation_tag` seeds a Poseidon2 sponge with `state[0..3] = final_root, randomness,
verifier_nonce` and folds the `BLAKE3(PRESENTATION_TAG_DSK)` domain-separation constant into the
capacity `state[4]`; `compute_presentation_tag_narrow` compresses the squeeze to the 1-felt narrow
tag the summary carries. In the IR the deployed permutation is the abstract NAMED Poseidon2 carrier
(`hash : List ℤ → ℤ`); the chip lookup enforces

    presentation_tag = hash [final_root, presentation_randomness, verifier_nonce, DSK]

where:
  * `final_root` (`FINAL_ROOT`, col 19) and `presentation_randomness` (`RANDOMNESS`, col 20) are
    HIDDEN witness columns — NOT public inputs. `presentation_randomness` being hidden is precisely
    what gives UNLINKABILITY: the same credential shown twice with fresh randomness yields two
    different tags, each still bound to its own `verifier_nonce`.
  * `verifier_nonce` (`VERIFIER_NONCE`, col 21) IS a public input (`PI_NONCE = 19`): the verifier
    chose it, so the light client checks the tag was bound to the specific challenge it issued.
  * `DSK` is the `BLAKE3(PRESENTATION_TAG_DSK) % p` domain-separation constant, folded in as a NAMED
    CARRIER `.const` — the IRREDUCIBLE off-circuit floor (BLAKE3 is not re-derived in-circuit; the
    deployed sponge computes the identical constant and folds it into capacity). It is a carrier
    exactly like the abstract Poseidon2 `hash`, not a residual.

Because the chip lookup binds `loc PRESENTATION_TAG` to the hash AND the summary PiBinding binds
`loc PRESENTATION_TAG = pub PRESENTATION_TAG`, the PUBLIC tag equals the genuine Poseidon2 image.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + a genuinely-proven,
non-vacuous shape lemma. `#assert_axioms` ⊆ {}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.BoundPresentationEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

set_option autoImplicit false

/-! ## §1 — the trace column layout (one logical summary row, repeated to a power-of-two height).

The 19 summary columns mirror the presentation summary (`PresentationEmit`); past them sit the four
tag-binding witness columns and the seven Poseidon2 chip output lanes. -/

/-- Summary col 0: `federation_root`. -/
def FEDERATION_ROOT : Nat := 0
/-- Summary cols 1..8: `request_predicate` (`action_binding`, 8 felts). -/
def REQUEST_PREDICATE_BASE : Nat := 1
/-- Summary col 9: `timestamp`. -/
def TIMESTAMP : Nat := 9
/-- Summary col 10: `presentation_tag` (narrow; now CONSTRAINED in-circuit to its Poseidon2 image). -/
def PRESENTATION_TAG : Nat := 10
/-- Summary cols 11..18: `revealed_facts_commitment` (8 felts). -/
def REVEALED_FACTS_BASE : Nat := 11

/-- The deployed summary width (`1 + 8 + 1 + 1 + 8`). -/
def SUMMARY_WIDTH : Nat := 19

/-- Tag-binding col 19: `final_root` — the end-of-chain state root; a HIDDEN witness (not a PI). -/
def FINAL_ROOT : Nat := 19
/-- Tag-binding col 20: `presentation_randomness` — fresh per presentation; HIDDEN (unlinkability). -/
def RANDOMNESS : Nat := 20
/-- Tag-binding col 21: `verifier_nonce` — the verifier's challenge; a PUBLIC input (`PI_NONCE`). -/
def VERIFIER_NONCE : Nat := 21

/-- The seven exposed Poseidon2 chip output lanes 1..7 (out0 is `PRESENTATION_TAG`). -/
def TAG_LANES : List Nat := [22, 23, 24, 25, 26, 27, 28]

/-- Total base-trace width: 19 summary + `final_root` + `randomness` + `verifier_nonce` + 7 lanes. -/
def BOUND_PRES_WIDTH : Nat := 29

/-- Public-input slot for the `verifier_nonce` (after the 19 summary PIs). -/
def PI_NONCE : Nat := 19

/-- Number of public inputs: the 19 summary slots + the verifier-nonce challenge. -/
def PI_COUNT : Nat := 20

/-- **The presentation-tag domain-separation constant** — `BLAKE3("dregg-presentation-tag-v1")`'s
first 4 bytes read little-endian and reduced mod the BabyBear prime `p = 2013265921`
(`binding.rs:311`, `PRESENTATION_TAG_DSK`). Folded into the tag preimage as a NAMED CARRIER `.const`
(the deployed sponge folds the identical constant into capacity `state[4]`). This is the irreducible
off-circuit BLAKE3 floor — stated as a constant, not re-derived in-circuit, and NOT a residual. -/
def PRESENTATION_TAG_DSK : ℤ := 1066441253

/-! ## §2 — the constraint list (19 summary copies · the nonce PI · the tag-binding chip lookup). -/

/-- The 19 summary copy constraints `row[i] == pi[i]` — `federation_root`, the 8 `action_binding`
felts, `timestamp`, the tag, and the 8 `revealed_facts` felts are ALL PiBinding-CONSTRAINED verified
public inputs (no carried-but-not-asserted felt; parity with `presentationFreshnessDesc`). -/
def summaryPins : List VmConstraint2 :=
  (List.range SUMMARY_WIDTH).map (fun i => .base (.piBinding VmRow.first i i))

/-- The `verifier_nonce` public-input pin: `loc[VERIFIER_NONCE] == pi[PI_NONCE]` (first row). -/
def noncePin : VmConstraint2 := .base (.piBinding VmRow.first VERIFIER_NONCE PI_NONCE)

/-- **The tag-binding chip lookup** — an arity-4 `TID_P2` Poseidon2 lookup absorbing
`[final_root, presentation_randomness, verifier_nonce, DSK]`, binding out0 to `PRESENTATION_TAG`.
This is the in-circuit tooth that forces the narrow tag to be the genuine Poseidon2 image of its
preimage (the gap `presentationFreshnessDesc` left to a named STARK leaf). Fires on EVERY row
(a lookup is never gated), so it also binds the single deployed summary row. -/
def tagLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var FINAL_ROOT, .var RANDOMNESS, .var VERIFIER_NONCE, .const PRESENTATION_TAG_DSK]
      PRESENTATION_TAG TAG_LANES⟩

/-- **`boundPresentationDesc`** — the presentation summary with the presentation-tag PI CONSTRAINED
in-circuit. Constraints: the 19 summary PiBindings, the verifier-nonce PI pin, and the tag-binding
chip lookup. The chip table (`TID_P2`) is IMPLICITLY present (Presence-detected from the lookup), so
`tables` is empty exactly as `merkleMembershipDesc` leaves it. -/
def boundPresentationDesc : EffectVmDescriptor2 :=
  { name        := "dregg-bound-presentation::v1"
  , traceWidth  := BOUND_PRES_WIDTH
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := summaryPins ++ [noncePin, tagLookup]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — the byte-pinned wire golden (the decoder ingests THIS string). -/

#guard emitVmJson2 boundPresentationDesc ==
  "{\"name\":\"dregg-bound-presentation::v1\",\"ir\":2,\"trace_width\":29,\"public_input_count\":20,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":19},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"const\",\"v\":1066441253},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28}]}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — shape pins (genuinely-proven, non-vacuous) + axiom hygiene. -/

/-- The tag-binding chip tuple has the canonical chip width `arity + CHIP_RATE + CHIP_OUT_LANES`
(the arity tag, the rate-padded 4-input preimage, out0 = the tag, and the 7 lanes). -/
theorem tagLookup_tuple_width :
    (chipLookupTuple [.var FINAL_ROOT, .var RANDOMNESS, .var VERIFIER_NONCE,
        .const PRESENTATION_TAG_DSK] PRESENTATION_TAG TAG_LANES).length
      = 1 + CHIP_RATE + CHIP_OUT_LANES := by
  simp [chipLookupTuple, Dregg2.Circuit.DescriptorIR2.padToE, CHIP_RATE, CHIP_OUT_LANES, TAG_LANES]

-- Shape pins.
#guard boundPresentationDesc.traceWidth == BOUND_PRES_WIDTH
#guard boundPresentationDesc.piCount == PI_COUNT
#guard boundPresentationDesc.constraints.length == SUMMARY_WIDTH + 2
#guard boundPresentationDesc.tables.length == 0
-- the tag preimage genuinely includes the domain-separation carrier (not the zero constant):
#guard decide (PRESENTATION_TAG_DSK ≠ 0)

#assert_axioms tagLookup_tuple_width

end Dregg2.Circuit.Emit.BoundPresentationEmit
