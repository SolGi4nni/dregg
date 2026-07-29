import Dregg2.Circuit.Emit.MinaWrapPublicCommGate
import Dregg2.Bridge.MinaStateHashWordGate
/-!
# Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader — the WELD: the 40-word public input the
in-kernel Wrap ladder is stated over is the public input **of the header a devnet node served**.

## The gap this closes

`docs/MINA-REAL-BLOCK-GATE.md` §3 drives one real Mina devnet block (539508) through C1/C3/C5/C8
and rungs 5a–5h. Every one of those is stated over `MinaWrapPublicCommGate.PUBLIC_INPUT` — forty
numbers. Nothing said those numbers were *this block's*. Word 12 is the only one that could say so
(`MinaStateHashWordGate`: it is the 93-element Poseidon over `[VK ‖ state_hash ‖ accumulators]`,
and the extractor measured that swapping only word 12 makes o1-labs' verifier refuse, 30/30).

This file is the equality. After it, "we verified a Wrap proof against 40 numbers" reads
"we verified a Wrap proof against the header `api.minascan.io` served for block 539508".

## The split, stated rather than blurred

  * **KERNEL (here):** the literal identities — word 12 and word 11 of the pinned block ARE
    `PUBLIC_INPUT[12]` and `PUBLIC_INPUT[11]`, and `publicComm` — the point `MinaRealBlockTranscript`
    absorbs third, from which β, γ, α′ and ζ′ descend — is the MSM over a public input whose word
    12 is that digest.
  * **COMPILED (`MinaStateHashWordGate` §4):** that the digest of the SERVED header IS that
    literal, i.e. `word12 B539508.stateHash B539508.accComm B539508.accChals == B539508.word12Gold`. A 93-element
    Poseidon under the kernel is the wall `docs/MINA-REAL-BLOCK-GATE.md` §7 measured; the kernel's
    job is the checker, the differential's job is the instance.

## What this is NOT

It does not make anything a Wrap verification, and it does not make the observer able to refuse a
foreign header on an arbitrary block — see `MinaStateHashWordGate`'s header for the measurement
that refuted the cheap-closed-loop hypothesis. It ties ONE fully-verified block to ONE served
header, which is exactly the block the ladder exists for.

NOT imported by the `Dregg2` root, per house practice for gates.
-/

set_option autoImplicit false

namespace Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurveComplete (projEqM)
open Dregg2.Bridge.MinaStateHashWordGate (B539508 word12 word11)

/-! ## §1 — the identity -/

/-- ⚑ **`word12_is_public_input_12`** — the digest the served header of block 539508 produces IS
public-input word 12 of the object the whole in-kernel ladder is stated over. -/
theorem word12_is_public_input_12 :
    B539508.word12Gold = MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0 := by decide

/-- …and word 11 likewise, so the two Poseidon digests of the statement are both accounted for and
neither is a number nobody derived. -/
theorem word11_is_public_input_11 :
    B539508.word11Gold = MinaWrapPublicCommGate.PUBLIC_INPUT.getD 11 0 := by decide

/-- ⚑ **`public_comm_descends_from_the_served_header`** — therefore the commitment
`MinaRealBlockTranscript` absorbs third into its phase-1 tape, and from which β, γ, α′ and ζ′ all
descend, is the Lagrange MSM over a public input whose ONLY block-dependent word is the digest of
the header the node served. Restating rung 5e over that fact rather than over a literal. -/
theorem public_comm_descends_from_the_served_header :
    MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0 = B539508.word12Gold
    ∧ projEqM pN MinaWrapPublicCommGate.publicComm
        MinaWrapPublicCommGate.PUBLIC_COMM_GOLD = true
    ∧ projEqM pN MinaWrapPublicCommGate.publicComm
        (MinaRealBlockTranscript.PUBCOMM_XY.getD 0 0,
         MinaRealBlockTranscript.PUBCOMM_XY.getD 1 0, 1) = true := by
  refine ⟨(word12_is_public_input_12).symm, ?_, ?_⟩
  · exact MinaWrapPublicCommGate.publicComm_reproduces_kimchi
  · exact MinaWrapPublicCommGate.publicComm_is_the_transcript_preimage

/-- **Non-vacuity of the tie**: no OTHER measured block's word 12 is `PUBLIC_INPUT[12]`. Without
this, `word12_is_public_input_12` is compatible with a constant. -/
theorem no_other_measured_block_is_the_anchor :
    Dregg2.Bridge.MinaStateHashWordGate.B539795.word12Gold
      ≠ MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0
    ∧ Dregg2.Bridge.MinaStateHashWordGate.B539796.word12Gold
      ≠ MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0
    ∧ Dregg2.Bridge.MinaStateHashWordGate.B539797.word12Gold
      ≠ MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0
    ∧ Dregg2.Bridge.MinaStateHashWordGate.B539798.word12Gold
      ≠ MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0
    ∧ Dregg2.Bridge.MinaStateHashWordGate.B539799.word12Gold
      ≠ MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 — the COMPILED half, restated here so the two links are legible in one place.

`word12`/`word11` on the anchor's served `stateHash` and its own wire accumulators reproduce the
literals §1 identifies. These are `#guard`s (the compiled evaluator), not `decide`. -/

#guard word12 B539508.stateHash B539508.accComm B539508.accChals == B539508.word12Gold
#guard word11 B539508.mnwComm B539508.mnwChals == B539508.word11Gold
#guard word12 B539508.stateHash B539508.accComm B539508.accChals
       == MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0
-- ⚑ and a FOREIGN served header does not produce it.
#guard word12 Dregg2.Bridge.MinaStateHashWordGate.B539795.stateHash B539508.accComm B539508.accChals
       != MinaWrapPublicCommGate.PUBLIC_INPUT.getD 12 0

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader

end Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader
