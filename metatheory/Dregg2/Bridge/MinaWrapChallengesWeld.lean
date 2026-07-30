/-
# Dregg2.Bridge.MinaWrapChallengesWeld — **the reality gate: the per-block COMPILED derivation
reproduces, on real devnet block 539508's own wire values, exactly the literals the KERNEL ladder
proved the opening relation over.**

## Why this is a separate file from the thing it welds

`MinaWrapChallenges` imports nothing but the sponge and is rooted in `Dregg2/FFI.lean`, so its
`@[export]` reaches an archive at **zero** added closure cost (measured on the import graph). The
literals it is welded to live in `MinaRealBlockTranscript` / `MinaWrapOpeningGate` — five modules
carrying ~4 minutes of kernel `decide` about ONE block. Rooting those in the archive would put that
four minutes into every build of the node's archive, permanently, to obtain a compiled function that
does not need them at runtime. So the weld lives here, runs under `lake build`, and is **NOT rooted**
— the same off-the-hot-path split `bridge/src/mina_opening_check.rs` documents for descriptor drift.

## What the weld says

`MinaWrapOpeningGate` derives block 539508's challenges from literals — a phase-1 sponge state built
from a hard-coded tape, `ipaTranscript` over hard-coded `LR_XY`. Everything above it (the opening
relation, 26 theorems, 153 s of kernel) is stated over the results. **Nothing said those results were
functions of anything.** This file feeds `MinaWrapChallenges`' parameterised sponges the same block's
values *as wire arguments* and checks the outputs are identical, including through the `String` C-ABI
grammar the runtime actually calls.

After it: "the opening relation holds at challenges we derived in-kernel for one block" reads "…at
challenges a per-block compiled function produces from that block's wire coordinates", and the
`ChallengesUnavailable` refusal in `mina_opening_check.rs` is scoped to its real cause — the
`public_comm` argument, not the transcript.

## ⚑ What is still NOT closed, and it is the whole remaining gap

`pubComm` is fed here from `MinaRealBlockTranscript.PUBCOMM_XY`, a LITERAL. In production it must be
`MinaWrapPublicInput.publicCommOf` over the 40 public-input words, six of which are
`expand_deferred`'s outputs and **do not exist in this tree in any language**. Until they do, the
per-block path terminates at the extractor for one argument, and this file says so rather than
letting a green `#guard` imply otherwise. `cipShifted` is the same word (`combined_inner_product`,
shifted) and has the same status.

Everything else absorbed — the two accumulator commitments, the 15 witness commitments, `z_comm`, the
7 `t_comm` chunks, the 15 `lr` pairs, `delta` — is on the wire and is already WALKED by
`bridge/src/mina_pickles.rs` `decode_proof_at`, which discards it.

Compiled, not kernel: every pin below is `#guard`. That is the point of the file.
-/
import Dregg2.Bridge.MinaWrapChallenges
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.MinaWrapChallengesWeld

open Dregg2.Bridge.MinaWrapChallenges
open Dregg2.Circuit.Emit.MinaRealBlockTranscript
  (VKDIGEST PREVCOMM_XY PUBCOMM_XY WCOMM_XY ZCOMM_XY TCOMM_XY
   BETA_N GAMMA_N ALPHA_CHAL ZETA_CHAL FQ_DIGEST)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate
  (CIP_SHIFTED LR_XY DELTA_XY IPA_PRECHALS C_PRE T_FQ)

/-! ## §1 — block 539508's absorbed objects, assembled as WIRE ARGUMENTS. -/

/-- The real block, as `MinaWrapChallenges` wants it. ⚑ `pubComm` and `cipShifted` are the two
arguments that are not decodable today; every other field is a coordinate `decode_proof_at` walks. -/
def B539508 : WrapAbsorbed :=
  { vkDigest := VKDIGEST
    prevComm := PREVCOMM_XY
    pubComm := PUBCOMM_XY
    wComm := WCOMM_XY
    zComm := ZCOMM_XY
    tComm := TCOMM_XY
    cipShifted := CIP_SHIFTED
    lr := LR_XY
    delta := DELTA_XY
    -- Pallas `endo_r`; carried so the record is complete, not read by the derivation.
    endoR := 26005156700822196841419187675678338661165322343552424574062261873906994770353 }

/- The real block's tape passes the shape gate — so the refusals in `phase1_shape_discriminates`
are not refusing everything. -/
#guard phase1WireOk B539508.prevComm B539508.pubComm B539508.wComm B539508.zComm B539508.tComm
#guard openingWireOk B539508.lr B539508.delta

/-! ## §2 — ⚑⚑ PHASE 1 REPRODUCES THE REAL BLOCK'S CHALLENGES, FROM WIRE ARGUMENTS. -/

/-- Phase 1 of the real block, computed rather than transcribed. -/
def p1 : Phase1 :=
  wrapPhase1Of B539508.vkDigest B539508.prevComm B539508.pubComm B539508.wComm
    B539508.zComm B539508.tComm

/- β, γ, α′, ζ′ and the phase-1 digest — all five, all equal to the values
`MinaRealBlockTranscript` pinned against `proof.oracles(...)` on the real object. -/
#guard p1.beta == BETA_N
#guard p1.gamma == GAMMA_N
#guard p1.alphaChal == ALPHA_CHAL
#guard p1.zetaChal == ZETA_CHAL
#guard p1.fqDigest == FQ_DIGEST

/- …and the state itself is the one `MinaWrapOpeningGate` picked up: `SRS::verify` receives exactly
this sponge. Comparing the STATE, not only its digest, is what makes the continuation in §3 a
continuation of the same transcript rather than of a state that merely agrees at one squeeze. -/
#guard p1.st == Dregg2.Circuit.Emit.MinaWrapOpeningGate.wrapPhase1State

/-! ### §2b — non-vacuity: each absorbed object is actually READ.

A phase-1 function that dropped one of its five tapes would still reproduce nothing but itself; these
say the digest moves when any single coordinate does. -/

/- Bump the VK digest — the FIRST absorb. ⚑ This is the trusted-config argument, so it is the one
whose silence would be most expensive. -/
#guard (wrapPhase1Of (VKDIGEST + 1) PREVCOMM_XY PUBCOMM_XY WCOMM_XY ZCOMM_XY TCOMM_XY).fqDigest
       != FQ_DIGEST
/- Bump a `public_comm` coordinate — the argument `expand_deferred` gates. -/
#guard (wrapPhase1Of VKDIGEST PREVCOMM_XY (PUBCOMM_XY.set 0 0) WCOMM_XY ZCOMM_XY TCOMM_XY).fqDigest
       != FQ_DIGEST
/- Bump an accumulator coordinate — the proof↔proof chain's own object. -/
#guard (wrapPhase1Of VKDIGEST (PREVCOMM_XY.set 3 0) PUBCOMM_XY WCOMM_XY ZCOMM_XY TCOMM_XY).fqDigest
       != FQ_DIGEST
/- Bump the LAST witness commitment coordinate — a fold that stopped early passes the earlier
controls and fails this one. -/
#guard (wrapPhase1Of VKDIGEST PREVCOMM_XY PUBCOMM_XY (WCOMM_XY.set 29 0) ZCOMM_XY TCOMM_XY).fqDigest
       != FQ_DIGEST
/- `z_comm` is absorbed AFTER β and γ, so moving it leaves those two and moves α′ onward. This pins
the ORDER, not just the membership. -/
#guard (wrapPhase1Of VKDIGEST PREVCOMM_XY PUBCOMM_XY WCOMM_XY (ZCOMM_XY.set 0 0) TCOMM_XY).beta
       == BETA_N
#guard (wrapPhase1Of VKDIGEST PREVCOMM_XY PUBCOMM_XY WCOMM_XY (ZCOMM_XY.set 0 0) TCOMM_XY).alphaChal
       != ALPHA_CHAL
/- …and `t_comm` after α′, so moving it leaves α′ and moves ζ′. -/
#guard (wrapPhase1Of VKDIGEST PREVCOMM_XY PUBCOMM_XY WCOMM_XY ZCOMM_XY (TCOMM_XY.set 13 0)).alphaChal
       == ALPHA_CHAL
#guard (wrapPhase1Of VKDIGEST PREVCOMM_XY PUBCOMM_XY WCOMM_XY ZCOMM_XY (TCOMM_XY.set 13 0)).zetaChal
       != ZETA_CHAL

/-! ## §3 — ⚑⚑ THE OPENING ARGUMENT'S 15 CHALLENGES, FROM WIRE ARGUMENTS.

These are the values `mina_opening_check.rs` refuses to invent, and `PINNED_CHALLENGES`' provenance
field describes as "derived by running the block's Fq sponge forward IN THE LEAN KERNEL". Here they
come out of a compiled function of the block's own coordinates. -/

/-- The opening challenges of the real block, computed from the phase-1 state §2 computed. -/
def ic : IpaChallenges := ipaChallengesOf p1.st B539508.cipShifted B539508.lr B539508.delta

/- ⚑ **THE RESULT.** `t`, all fifteen IPA prechallenges and `c′` — identical to the literals rung
5f's 26 kernel theorems are stated over. -/
#guard ic.t == T_FQ
#guard ic.prechals == IPA_PRECHALS
#guard ic.cPre == C_PRE
#guard ic.prechals.length == 15

/- …and the whole derivation, through the fail-closed entry point, in one call. -/
#guard (deriveWrapChallenges B539508).isSome
#guard match deriveWrapChallenges B539508 with
       | some (q, j) => q.fqDigest == FQ_DIGEST && j.prechals == IPA_PRECHALS && j.cPre == C_PRE
       | none => false

/- ⚑ **AND IT REFUSES A MALFORMED TAPE RATHER THAN DERIVING ON IT.** `prev_challenges = 0` — the
shape the retired `prevLen = 0` freeze assumed and that REJECTS real Mina blocks — produces `none`,
not a challenge vector. -/
#guard (deriveWrapChallenges { B539508 with prevComm := [] }).isNone
#guard (deriveWrapChallenges { B539508 with lr := B539508.lr.take 14 }).isNone
#guard (deriveWrapChallenges { B539508 with delta := [] }).isNone

/-! ### §3b — non-vacuity of the continuation, one control per stage of the stream.

Mirrors `MinaWrapOpeningGate`'s own `#guard` battery, but through the PARAMETERISED functions, so a
parameterisation that quietly ignored an argument is caught. -/

/- The absorbed `combined_inner_product` is inside the transcript: move it and `t` moves. -/
#guard (ipaChallengesOf p1.st (CIP_SHIFTED + 1) LR_XY DELTA_XY).t != T_FQ
/- An IPA round point moves its own challenge and every later one, but NOT `t` (absorbed after). -/
#guard (ipaChallengesOf p1.st CIP_SHIFTED (LR_XY.set 0 ((LR_XY.getD 0 []).set 0 0)) DELTA_XY).t
       == T_FQ
#guard (ipaChallengesOf p1.st CIP_SHIFTED
          (LR_XY.set 0 ((LR_XY.getD 0 []).set 0 0)) DELTA_XY).prechals != IPA_PRECHALS
/- The LAST round is read too. -/
#guard (ipaChallengesOf p1.st CIP_SHIFTED
          (LR_XY.set 14 ((LR_XY.getD 14 []).set 3 0)) DELTA_XY).prechals != IPA_PRECHALS
/- `delta` is absorbed AFTER the rounds: it moves `c′` and leaves the fifteen alone. -/
#guard (ipaChallengesOf p1.st CIP_SHIFTED LR_XY (DELTA_XY.set 0 0)).prechals == IPA_PRECHALS
#guard (ipaChallengesOf p1.st CIP_SHIFTED LR_XY (DELTA_XY.set 0 0)).cPre != C_PRE
/- ⚑ And phase 1 is genuinely upstream: a different `public_comm` produces a different phase-1
state and therefore a DIFFERENT fifteen. This is the link that makes the block's public input reach
the opening argument at all — the reason `expand_deferred` is the blocker and not a detail. -/
#guard (ipaChallengesOf
          (wrapPhase1Of VKDIGEST PREVCOMM_XY (PUBCOMM_XY.set 0 0) WCOMM_XY ZCOMM_XY TCOMM_XY).st
          CIP_SHIFTED LR_XY DELTA_XY).prechals != IPA_PRECHALS

/-! ## §4 — ⚑ THROUGH THE C-ABI GRAMMAR, on the real block.

The runtime does not call `deriveWrapChallenges`; it calls `dregg_mina_wrap_challenges` with a
string. This assembles that string from the real block's coordinates and checks the answer — so the
wire layer, the `Nat` parsing and the flat-`lr` re-chunking are exercised on real data rather than on
the synthetic refusals in `MinaWrapChallenges` §4b. -/

/-- Render a list as the gate's `NATS`. -/
def nats (xs : List Nat) : String := String.intercalate "," (xs.map toString)

/-- The real block's wire string. -/
def WIRE_539508 : String :=
  "vk=" ++ toString VKDIGEST ++ ";er=" ++ toString B539508.endoR
  ++ ";pc=" ++ nats PREVCOMM_XY ++ ";pu=" ++ nats PUBCOMM_XY ++ ";wc=" ++ nats WCOMM_XY
  ++ ";zc=" ++ nats ZCOMM_XY ++ ";tc=" ++ nats TCOMM_XY
  ++ ";cs=" ++ toString CIP_SHIFTED
  ++ ";lr=" ++ nats (LR_XY.flatten) ++ ";dl=" ++ nats DELTA_XY

/-- The expected answer, rendered from the pinned literals — assembled from
`MinaRealBlockTranscript`'s and `MinaWrapOpeningGate`'s constants, NOT from the gate's own output. -/
def EXPECTED_539508 : String :=
  "b=" ++ toString BETA_N ++ ";g=" ++ toString GAMMA_N ++ ";a=" ++ toString ALPHA_CHAL
    ++ ";z=" ++ toString ZETA_CHAL ++ ";fq=" ++ toString FQ_DIGEST
    ++ ";t=" ++ toString T_FQ ++ ";c=" ++ toString C_PRE
    ++ ";ch=" ++ nats IPA_PRECHALS

/- ⚑⚑ **THE EXPORTED GATE, ON A REAL MINA BLOCK, END TO END.** -/
#guard minaWrapChallengesGate WIRE_539508 == EXPECTED_539508

/- …and the same wire with ONE coordinate of `public_comm` moved is a different answer, not the
same one — so the string path is not a constant. -/
#guard minaWrapChallengesGate
         ("vk=" ++ toString VKDIGEST ++ ";er=" ++ toString B539508.endoR
          ++ ";pc=" ++ nats PREVCOMM_XY ++ ";pu=" ++ nats (PUBCOMM_XY.set 0 0)
          ++ ";wc=" ++ nats WCOMM_XY ++ ";zc=" ++ nats ZCOMM_XY ++ ";tc=" ++ nats TCOMM_XY
          ++ ";cs=" ++ toString CIP_SHIFTED
          ++ ";lr=" ++ nats (LR_XY.flatten) ++ ";dl=" ++ nats DELTA_XY)
       != EXPECTED_539508

/- …and a wire whose `lr` is 56 numbers instead of 60 is `"ERR"`: the re-chunking drops the short
tail and `openingWireOk` refuses the 14 rounds. A gate that derived on 14 rounds would produce a
plausible vector for a proof of a different index. -/
#guard minaWrapChallengesGate
         ("vk=" ++ toString VKDIGEST ++ ";er=" ++ toString B539508.endoR
          ++ ";pc=" ++ nats PREVCOMM_XY ++ ";pu=" ++ nats PUBCOMM_XY
          ++ ";wc=" ++ nats WCOMM_XY ++ ";zc=" ++ nats ZCOMM_XY ++ ";tc=" ++ nats TCOMM_XY
          ++ ";cs=" ++ toString CIP_SHIFTED
          ++ ";lr=" ++ nats ((LR_XY.flatten).take 56) ++ ";dl=" ++ nats DELTA_XY)
       == "ERR"

end Dregg2.Bridge.MinaWrapChallengesWeld
