/-
# KimchiStepWrapChain — the STEP circuit's own proof driving the WRAP circuit's transcript.

⚑ **THE GAP THIS CLOSES.** `KimchiStepMain` assembles a Vesta/Fp circuit and proves it;
`KimchiWrapMain` assembles a Pallas/Fq circuit and proves it; and **nothing fed one into the
other**. `KimchiWrapMain`'s transcript absorbs `PastaPoseidonFq.WCOMM_XY` &co. — the commitments of
a `create_circuit(0, 5)` proof exported from a third-party checkout (`PastaPoseidonFq` §6). Real,
accepted, and *not dregg's*. This file replaces that tape with the phase-1 Fq tape of a proof of
`KimchiStepMain`'s own emission.

## §0 — THE FIELD/CURVE CROSSING, ESTABLISHED AT SOURCE

The campaign brief said "the step proof's commitments are Vesta points whose coordinates live in
Fp, and the wrap circuit computes in Fq". ⚠ **That is backwards, and the correction is what makes
this file short.**

* A kimchi proof over curve `G` has its circuit in `G`'s SCALAR field and its commitments in `G`'s
  BASE field. A STEP proof is Tick: committed on **Vesta**, scalar field **Fp** (so the step
  circuit is over Fp — `pickles-stepmain-harness` uses `Vesta`/`Fp`), base field **Fq**.
* The WRAP circuit is Tock: `wrap_main_inputs.ml:4,6` sets `Me = Tock`, `Impl = Impls.Wrap`, so its
  native field is `Tock.Field = Fq` and it commits on Pallas.
* Therefore a step proof's commitments are Vesta points with **Fq** coordinates — *the wrap
  circuit's own field*. `wrap_main_inputs.ml:104-105` says so outright:
  `module Inner_curve = struct module C = Kimchi_pasta.Pasta.Vesta`, and
  `wrap_verifier.ml:527` absorbs them through `Inner_curve.to_field_elements`.
  **The commitments cross for free.** That is the point of the 2-cycle.

What does NOT cross for free is the step proof's SCALAR data — evaluations at ζ, `ft_eval1`,
`combined_inner_product`, `b`, `z_1`, `z_2` — which is Fp. Mina records the asymmetry in one line,
`impls.ml:51`: `(* Tick.Field.t = p < q = Tock.Field.t *)`. Hence

* in the **wrap** circuit (native Fq) an Fp value is **ONE** wire — `impls.ml:167-217`,
  `type t = Field.t`, `typ_unchecked = Typ.transport Field.typ ~there:(Tock.Field.of_bits ∘
  Tick.Field.to_bits)`, a bit-reinterpretation that is the identity on the integer because `p < q`;
* in the **step** circuit (native Fp) an Fq value needs **TWO** — `impls.ml:50-103`,
  `type t = (* Low bits, high bit *) Field.t * Boolean.var`.

⚑ And the `Shifted_value` tag keys on **the value's own field, not the circuit's** — the brief had
this right. Fp values are `Type1` (`wrap_verifier.ml:386,392`; the wrap statement at
`wrap_main.ml:108`; `Shifts.tick1 = Type1.Shift.create (module Tick.Field)`, `common.ml:98-99`), Fq
values are `Type2` (`impls.ml:135-136`; and `wrap_main.ml:211` reads the previous STEP proof state
as `Shifted_value.Type2.typ Field.typ` where `Field` is the wrap's own Fq).

Only **one** word of this transcript is a crossed scalar: `combined_inner_product`, absorbed by
`wrap_verifier.ml:395` as `Other_field.Packed.absorb_shifted`. §5 exhibits its arithmetic.

## §0b — WHAT THIS FILE DOES AND DOES NOT ESTABLISH

**Does.** The wrap-side assembly's Fq sponge, driven on dregg's own step proof's phase-1 tape,
reproduces β, γ, α′, ζ′ and the phase-1 digest that `kimchi::verifier`'s `proof.oracles(...)`
computed for that same proof; bending one Fq coordinate of the step proof's `w_comm` moves all five
to the values kimchi computes for the bent tape; and parts of the same proof the tape does not
absorb move nothing.

**Does NOT.** This is not a Mina-valid proof and not a soundness result.

* The step proof's commitments enter as **sponge inputs**, not as curve points a sub-circuit
  consumes. `KimchiWrapMain.WRAP_UNCONSUMED` still carries all **eight** entries. Two of them now
  name an EMITTED sub-circuit rather than a missing one — `x_hat`'s MSM at `w6_xhat` (§15) and
  `ft_comm` at `w8_ftcomm` (§17) — and the census kept them, because emitting a value the prover
  still hands over freely changes the SHAPE of the prover's reach and not its size. The rest still
  need W-COMBINE / W-FINALIZE / W-BULLET.
* ⚑ And neither emitted sub-circuit is in THIS file's object. Everything below emits at
  `Rung.bind` (`w4_bind`), and `rungRows _ .bind _` stops at `closingRows` — `keyRows`,
  `xhatRows`, `splitRows` and `ftcRows` are not in the row list. §1 says what that costs on the
  `x_hat` slot specifically, and `chain_xhat_is_the_step_proofs_not_the_msm_output` exhibits it.
* The opening — `equal_g`, `verified`, the accumulator check — is not in the wrap circuit at all,
  and `verified` remains a witnessed boolean.
* The reality gate below is closed by `native_decide`: 28 Poseidon permutations of 255-bit states,
  which is the same instrument `PastaPoseidonFq` §6 uses and which trusts the compiler.
  `#assert_compiled` is the confession, per `docs/GUARD-DISCIPLINE.md`.

## §0c — OWNERSHIP

`KimchiWrapMain.lean` is a sibling lane's file and is consumed here **read-only**: this module
imports it and substitutes only the `SpAcc` inside a `WrapData`. It adds no `#guard` (every fact
below is a named theorem), so it adds no row to `scripts/guard-discipline-baseline.txt`.
-/
import Dregg2.Circuit.Emit.KimchiWrapMain
import Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

namespace Dregg2.Circuit.Emit.KimchiStepWrapChain

open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiPlacement (inertPublicWords)
open Dregg2.Circuit.Emit.KimchiStepWrapChainFixture
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams newSponge absorbMany challenge digestInto)

/-! ## §1 — THE SHAPE, MEASURED OFF THE STEP PROOF RATHER THAN CHOSEN.

Four of `WrapShape`'s **nine** fields are read out of the tape the step proof actually produced. The
remaining five are taken from `KimchiWrapMain.shapeWrap` unchanged, for two different reasons:

* `emsRows`, `branches`, `pubWords` are wrap-instance parameters with no step-side source —
  `wrap_main` is per-zkApp (`wrap_main.ml:96-105`).
* ⚑ `xhatTerms` and `xhatXY` arrived at `w6_xhat` (W-XHAT, `d89815028`) and are **§15's**, not the
  transcript's. `xhatXY` is a memo carrying `xhatOut xhatTerms`, and copying `shapeWrap`'s pair
  discharges that obligation by construction — `chain_xhat_is_the_step_proofs_not_the_msm_output`
  proves it rather than assuming it, which is the committed-shape half that `KimchiWrapMain` itself
  only closes for `shapeSmoke`.

⚑ **AND THE `x_hat` SLOT IS THE ONE PLACE THE CHAIN OVERRIDES A DERIVED VALUE.** `schedule` absorbs
`s.xhatXY` at `wrap_verifier.ml:617`; `chainSchedule` absorbs `STEP_PUBCOMM_XY`, the public-input
commitment kimchi's own verifier absorbed for THIS step proof. It has to: `chain_reality_gate` is a
claim about what `proof.oracles(...)` computed, and §15's 67 scalars are `xhatScalar =
wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i` — a deterministic filler, not any statement's words. So the
MSM is emitted over the RIGHT SHAPE and the WRONG SCALARS, and closing that is W-PREV's job
(`wrap_main.ml:201-256`'s `exists ~request:Req.Proof_state`), not this file's. §8 states it. -/

def shapeChain : WrapShape :=
  { prevs := STEP_PREVCOMM_XY.length / 2
  , ipaRounds := STEP_IPA_ROUNDS
  , wComms := STEP_WCOMM_XY.length / 2
  , tComms := STEP_TCOMM_XY.length / 2
  , emsRows := shapeWrap.emsRows
  , branches := shapeWrap.branches
  , pubWords := shapeWrap.pubWords
  , xhatTerms := shapeWrap.xhatTerms
  , xhatXY := shapeWrap.xhatXY }

/-! ## §2 — THE TAPE, and the schedule that carries it.

`chainTape` is the phase-1 absorb tape up to β, in `kimchi/src/verifier.rs:162-177` order — which
is the order `wrap_verifier.ml:537-619` re-runs in-circuit. It is assembled from the labelled
blocks, not pasted as one opaque list. -/

def chainTape : List Nat :=
  STEP_VKDIGEST :: (STEP_PREVCOMM_XY ++ STEP_PUBCOMM_XY ++ STEP_WCOMM_XY)

/-- The chain's item values, tag by tag — `KimchiWrapMain.itemVal`'s shape with every entry
resolved against **this** step proof. Nothing falls through to `wrapFixture`: unlike the borrowed
fixture, `lr` and `delta` have a real source here too. -/
def chainItemVal (t i : Nat) : Nat :=
  if t == T_DIGEST then STEP_VKDIGEST
  else if t == T_SGOLD then STEP_PREVCOMM_XY.getD i (wrapFixture T_SGOLD i)
  else if t == T_XHAT then STEP_PUBCOMM_XY.getD i (wrapFixture T_XHAT i)
  else if t == T_WCOMM then STEP_WCOMM_XY.getD i (wrapFixture T_WCOMM i)
  else if t == T_ZCOMM then STEP_ZCOMM_XY.getD i (wrapFixture T_ZCOMM i)
  else if t == T_TCOMM then STEP_TCOMM_XY.getD i (wrapFixture T_TCOMM i)
  else if t == T_CIP then STEP_CIP_WORD_FQ
  else if t == T_LR then STEP_LR_XY.getD i (wrapFixture T_LR i)
  else if t == T_DELTA then STEP_DELTA_XY.getD i (wrapFixture T_DELTA i)
  else wrapFixture t i

/-- `KimchiWrapMain.schedule`'s event list, item for item, with `chainItemVal` in place of
`itemVal`. Same length, same tags, same squeeze positions — so `nItems`/`nSqueezes`/`nChals`, which
`challengeRowsQ` sizes itself by, cannot disagree with the trace this drives. §4 pins that. -/
def chainSchedule (s : WrapShape) : List Ev :=
  [ Ev.abs T_DIGEST (chainItemVal T_DIGEST 0) ]
  ++ (List.range (2 * s.prevs)).map (fun i => Ev.abs T_SGOLD (chainItemVal T_SGOLD i))
  ++ (List.range 2).map (fun i => Ev.abs T_XHAT (chainItemVal T_XHAT i))
  ++ (List.range (2 * s.wComms)).map (fun i => Ev.abs T_WCOMM (chainItemVal T_WCOMM i))
  ++ [ Ev.sq .chal, Ev.sq .chal ]                                    -- beta, gamma
  ++ (List.range 2).map (fun i => Ev.abs T_ZCOMM (chainItemVal T_ZCOMM i))
  ++ [ Ev.sq .chal ]                                                 -- alpha'
  ++ (List.range (2 * s.tComms)).map (fun i => Ev.abs T_TCOMM (chainItemVal T_TCOMM i))
  ++ [ Ev.sq .chal ]                                                 -- zeta'
  ++ [ Ev.sq .fork ]                                                 -- the digest, off-transcript
  ++ [ Ev.abs T_CIP (chainItemVal T_CIP 0) ]                          -- ⚑ the ONE crossed scalar
  ++ [ Ev.sq .full ]                                                 -- u = group_map t
  ++ (List.range s.ipaRounds).flatMap (fun r =>
       (List.range 4).map (fun j => Ev.abs T_LR (chainItemVal T_LR (4 * r + j)))
       ++ [ Ev.sq .chal ])
  ++ (List.range 2).map (fun i => Ev.abs T_DELTA (chainItemVal T_DELTA i))
  ++ [ Ev.sq .chal ]                                                 -- c

/-! ## §3 — ⚑ THE REALITY GATE. The reference Fq sponge over the step proof's own tape.

`PastaPoseidonFq`'s state machine — the one whose gold vectors come from the upstream
`ArithmeticSponge` — run on `chainTape`. If this reproduces what `kimchi::verifier`'s
`proof.oracles(...)` computed, then the Lean Fq transcript and the o1-labs Rust verifier agree
about **dregg's own step proof**, and not merely about a borrowed one. -/

/-- Parametric so the red controls go through the identical code path (`fqPhase1With`'s shape). -/
def chainPhase1With (tape zc tc : List Nat) : Nat × Nat × Nat × Nat × Nat :=
  let s0 := absorbMany fqParams newSponge tape
  let (s1, beta) := challenge fqParams s0
  let (s2, gamma) := challenge fqParams s1
  let s3 := absorbMany fqParams s2 zc
  let (s4, alphaChal) := challenge fqParams s3
  let s5 := absorbMany fqParams s4 tc
  let (s6, zetaChal) := challenge fqParams s5
  (beta, gamma, alphaChal, zetaChal, digestInto fqParams s6 pN)

def chainPhase1 : Nat × Nat × Nat × Nat × Nat :=
  chainPhase1With chainTape STEP_ZCOMM_XY STEP_TCOMM_XY

/-- **`chain_reality_gate`** — ⚑ the whole point. Driving this tree's Fq sponge on the phase-1 tape
of a proof of `KimchiStepMain`'s own emission reproduces, exactly, the five phase-1 outputs
`kimchi::verifier`'s `proof.oracles(...)` produced for that proof — which the exporter additionally
cross-checked against an independent `DefaultFqSponge<VestaParameters>` replay (`assert_eq!`, not a
print). Nothing here is consumed as given: β, γ, α′, ζ′ and the digest are all DERIVED.

⚠ `native_decide`: 28 permutations of a 255-bit state, the same instrument `PastaPoseidonFq` §6
uses for the borrowed fixture. `#assert_compiled` below is the confession. -/
theorem chain_reality_gate :
    chainPhase1 = (STEP_BETA, STEP_GAMMA, STEP_ALPHA_CHAL, STEP_ZETA_CHAL, STEP_DIGEST) := by
  native_decide

#assert_compiled chain_reality_gate

/-! ## §4 — ⚑ THE CIRCUIT'S OWN SPONGE, not just the reference one.

§3 runs `PastaPoseidonFq`'s `SpongeSt`. The EMITTED CIRCUIT runs `KimchiWrapMain.runSpongeQ`, a
different object: an event-driven rate-2 trace that also allocates a variable per lane and records
where every permutation falls. The two must agree, or the rows the harness proves are not the rows
this gate is about. -/

def chainRun : SpAcc := runSpongeQ (baseSp shapeChain) (chainSchedule shapeChain) 99999 0

/-- The `chal` squeezes of the circuit trace, truncated the way `lowest_128_bits` truncates. -/
def chainChals : List Nat := (chalSqueezes chainRun).map (fun e => e.2 % 2 ^ 128)

/-- The FORK squeeze — `sponge_digest_before_evaluations` (`wrap_verifier.ml:646`). -/
def chainForkVal : Nat := ((forkSqueeze chainRun).map (fun e => e.2)).getD 0

/-- **`chain_circuit_sponge_is_the_verifiers`** — the first four `chal` squeezes of the EMITTED
CIRCUIT'S trace are the four challenges kimchi's verifier derived from this step proof. This is the
tie between §3's reference derivation and the rows the Pallas harness actually proves. -/
theorem chain_circuit_sponge_is_the_verifiers :
    chainChals.take 4 = [STEP_BETA, STEP_GAMMA, STEP_ALPHA_CHAL, STEP_ZETA_CHAL] := by
  native_decide

#assert_compiled chain_circuit_sponge_is_the_verifiers

/-- **`chain_schedule_is_the_wrap_schedule`** — the chain's event list differs from
`KimchiWrapMain.schedule` in VALUES only: same length, same tag at every position, same squeeze
positions, and therefore the same `nItems`/`nSqueezes`/`nChals` that `challengeRowsQ` sizes itself
by. A schedule that quietly shortened would leave `challengeRowsQ` folding over `(.external 0, 0)`
padding and the "chain" would be about a shorter transcript than `wrap_main` runs. -/
theorem chain_schedule_is_the_wrap_schedule :
    (chainSchedule shapeChain).length = (schedule shapeChain).length
    ∧ ((chainSchedule shapeChain).zip (schedule shapeChain)).all
        (fun p => match p.1, p.2 with
          | .abs t _, .abs u _ => t == u
          | .sq a, .sq b => a == b
          | _, _ => false) = true
    ∧ (chalSqueezes chainRun).length = nChals shapeChain := by
  native_decide

#assert_compiled chain_schedule_is_the_wrap_schedule

/-! ## §5 — ⚑ THE ONE SCALAR THAT CROSSES FIELDS, and its arithmetic.

Every other word on this tape is an Fq coordinate of a Vesta point and needed no encoding.
`combined_inner_product` is an **Fp** value, and `wrap_main.ml:357-358` reads the step proof's
opening with `let shift = Shifts.tick1`, i.e. `Shifted_value.Type1.Shift.create (module
Tick.Field)` — created over **Fp**, the value's own field, not over the circuit's Fq.
`shifted_value.ml:122-135`:

    c = 2^{F.size_in_bits} + 1 ,  scale = 1/2
    of_field s = (s − c) · scale ,  to_field t = t + t + c        (all in F = Fp)

The shifted Fp element then occupies ONE Fq wire (`impls.ml:196-201`), and `wrap_verifier.ml:395`
absorbs exactly that word. -/

/-- Type1's `c` at `Fp.size_in_bits = 255` (`shifted_value.ml:124`). -/
def TYPE1_C_FP : Nat := (2 ^ 255 + 1) % pN

/-- **`cip_crosses_by_type1_over_Fp`** — the absorbed word IS `Shifted_value.Type1.of_field` of
`combined_inner_product` computed in **Fp**, carried into Fq by the identity on the integer.
`to_field` (`t + t + c`) recovers the raw value, so the shift is the real one and not a relabelling;
and `p < q` is what makes the one-wire carry possible at all (`impls.ml:51`). -/
theorem cip_crosses_by_type1_over_Fp :
    (STEP_CIP_SHIFTED_FP + STEP_CIP_SHIFTED_FP + TYPE1_C_FP) % pN = STEP_CIP_FP
    ∧ STEP_CIP_WORD_FQ = STEP_CIP_SHIFTED_FP
    ∧ STEP_CIP_WORD_FQ < pN
    ∧ pN < qN := by
  native_decide

#assert_compiled cip_crosses_by_type1_over_Fp

/-- **`the_commitments_needed_no_encoding`** — the complementary half, and the correction to the
brief. Every phase-1 tape word is already a legal Fq element, `chainTape` has no `Other_field`
pair anywhere in it, and the ONE crossed scalar is not on it: `T_CIP` is absorbed after the fork
(`wrap_verifier.ml:395`, inside `check_bulletproof`), so no phase-1 challenge depends on a
field-crossed value. -/
theorem the_commitments_needed_no_encoding :
    chainTape.all (fun w => decide (w < qN)) = true
    ∧ chainTape.contains STEP_CIP_WORD_FQ = false
    ∧ chainTape.length = 1 + 2 * shapeChain.prevs + 2 + 2 * shapeChain.wComms := by
  native_decide

#assert_compiled the_commitments_needed_no_encoding

/-! ## §6 — ⚑ THE RED CONTROLS. The property nothing has ever shown: that one half DEPENDS on the
other.

The positive control is not "some value changes" — it is that the wrap transcript moves **to the
value kimchi's own sponge produces for the bent tape**, which the exporter measured by bending the
same coordinate and re-running the same Rust sponge.

The negative control's strong half is also measured in Rust: `export_step_tape.rs` bends `z_1`,
`z_2`, `ft_eval1`, `delta` and `sg` **in the proof object** and re-runs `proof.oracles(...)`,
asserting all five phase-1 outputs are identical. What is checkable here is the reason: those
values are not on the tape, and the derivation is a function of the tape alone. -/

/-- The tape with word `STEP_BENT_INDEX` — the first Fq coordinate of the step proof's `w_comm` —
bent by one in Fq. -/
def chainBentTape : List Nat :=
  chainTape.set STEP_BENT_INDEX (qAdd (chainTape.getD STEP_BENT_INDEX 0) 1)

def chainBentPhase1 : Nat × Nat × Nat × Nat × Nat :=
  chainPhase1With chainBentTape STEP_ZCOMM_XY STEP_TCOMM_XY

/-- **`chain_moves_with_the_step_proof`** — ⚑ bending ONE Fq coordinate of the step proof's `w_comm`
moves β, γ, α′, ζ′ AND the digest, and moves them to exactly the values the exporter measured by
bending the same coordinate and re-running kimchi's own Fq sponge. The bent index really is inside
the `w_comm` block, not in the padding before it. -/
theorem chain_moves_with_the_step_proof :
    chainBentPhase1
      = (STEP_BENT_BETA, STEP_BENT_GAMMA, STEP_BENT_ALPHA_CHAL, STEP_BENT_ZETA_CHAL,
         STEP_BENT_DIGEST)
    ∧ chainBentPhase1.1 ≠ STEP_BETA
    ∧ chainBentPhase1.2.1 ≠ STEP_GAMMA
    ∧ chainBentPhase1.2.2.1 ≠ STEP_ALPHA_CHAL
    ∧ chainBentPhase1.2.2.2.1 ≠ STEP_ZETA_CHAL
    ∧ chainBentPhase1.2.2.2.2 ≠ STEP_DIGEST
    ∧ STEP_BENT_INDEX = 1 + 2 * shapeChain.prevs + 2 := by
  native_decide

#assert_compiled chain_moves_with_the_step_proof

/-- **`chain_block_locality`** — the dependence is the transcript's, not a global smear: `z_comm` is
absorbed after β and γ, so bending it leaves those two FIXED and moves α′ and ζ′; `t_comm` is
absorbed after α′, so bending it leaves α′ fixed and moves ζ′ only. A "chain" that moved everything
under every bend would be consistent with the sponge being seeded by the tape wholesale. -/
theorem chain_block_locality :
    (chainPhase1With chainTape (STEP_ZCOMM_XY.set 0 0) STEP_TCOMM_XY).1 = STEP_BETA
    ∧ (chainPhase1With chainTape (STEP_ZCOMM_XY.set 0 0) STEP_TCOMM_XY).2.1 = STEP_GAMMA
    ∧ (chainPhase1With chainTape (STEP_ZCOMM_XY.set 0 0) STEP_TCOMM_XY).2.2.1 ≠ STEP_ALPHA_CHAL
    ∧ (chainPhase1With chainTape STEP_ZCOMM_XY (STEP_TCOMM_XY.set 13 0)).2.2.1 = STEP_ALPHA_CHAL
    ∧ (chainPhase1With chainTape STEP_ZCOMM_XY (STEP_TCOMM_XY.set 13 0)).2.2.2.1 ≠ STEP_ZETA_CHAL
    := by
  native_decide

#assert_compiled chain_block_locality

/-- **`chain_does_not_move_with_what_it_does_not_read`** — the negative control's checkable half.
`z_1`, `z_2` and `ft_eval1` are Fp scalars of the SAME accepted proof; `delta` and `sg` are Fq
points of it. None is on the phase-1 tape, and `chainPhase1With` is a function of the tape and the
two later blocks alone — so no bend of them can move any of the five outputs. Each is nonzero, so
the non-membership is not vacuous.

⚠ The strong form of this control is MEASURED, not stated here: `export_step_tape.rs` bends all
five in the proof object and re-runs `proof.oracles(...)`, asserting the five outputs are
unchanged. -/
theorem chain_does_not_move_with_what_it_does_not_read :
    chainTape.contains STEP_Z1_FP = false
    ∧ chainTape.contains STEP_Z2_FP = false
    ∧ chainTape.contains STEP_FT_EVAL1_FP = false
    ∧ STEP_DELTA_XY.all (fun w => !chainTape.contains w) = true
    ∧ STEP_SG_XY.all (fun w => !chainTape.contains w) = true
    ∧ STEP_Z1_FP ≠ 0 ∧ STEP_Z2_FP ≠ 0 ∧ STEP_FT_EVAL1_FP ≠ 0
    ∧ STEP_DELTA_XY.length = 2 ∧ STEP_SG_XY.length = 2 := by
  native_decide

#assert_compiled chain_does_not_move_with_what_it_does_not_read

/-- **`chain_unread_bend_is_a_different_proof_with_the_same_tape`** — ⚑ the negative control in its
strong form, carried into Lean. `STEP_UNREAD_*` is a SECOND extraction, taken from the mutated proof
object after `z_1`, `z_2`, `ft_eval1`, `delta` and `sg` were bent: five values that genuinely
changed, a phase-1 tape that is byte-identical, and therefore five phase-1 outputs that are
identical. This is two independent extractions from two different proof objects, not a list
compared with itself. -/
theorem chain_unread_bend_is_a_different_proof_with_the_same_tape :
    STEP_UNREAD_Z1_FP ≠ STEP_Z1_FP
    ∧ STEP_UNREAD_Z2_FP ≠ STEP_Z2_FP
    ∧ STEP_UNREAD_FT_EVAL1_FP ≠ STEP_FT_EVAL1_FP
    ∧ STEP_UNREAD_DELTA_XY ≠ STEP_DELTA_XY
    ∧ STEP_UNREAD_SG_XY ≠ STEP_SG_XY
    ∧ STEP_UNREAD_TAPE = chainTape
    ∧ STEP_UNREAD_ZCOMM_XY = STEP_ZCOMM_XY
    ∧ STEP_UNREAD_TCOMM_XY = STEP_TCOMM_XY
    ∧ chainPhase1With STEP_UNREAD_TAPE STEP_UNREAD_ZCOMM_XY STEP_UNREAD_TCOMM_XY = chainPhase1 := by
  native_decide

#assert_compiled chain_unread_bend_is_a_different_proof_with_the_same_tape

/-- The emission driven by the unread-bent extraction. §10 writes it out and the Pallas harness
asserts it is BYTE-IDENTICAL to the honest one. -/
def chainUnreadSchedule (s : WrapShape) : List Ev :=
  [ Ev.abs T_DIGEST (STEP_UNREAD_TAPE.getD 0 0) ]
  ++ (List.range (2 * s.prevs)).map (fun i => Ev.abs T_SGOLD (STEP_UNREAD_TAPE.getD (1 + i) 0))
  ++ (List.range 2).map (fun i => Ev.abs T_XHAT (STEP_UNREAD_TAPE.getD (1 + 2 * s.prevs + i) 0))
  ++ (List.range (2 * s.wComms)).map (fun i =>
       Ev.abs T_WCOMM (STEP_UNREAD_TAPE.getD (1 + 2 * s.prevs + 2 + i) 0))
  ++ [ Ev.sq .chal, Ev.sq .chal ]
  ++ (List.range 2).map (fun i => Ev.abs T_ZCOMM (STEP_UNREAD_ZCOMM_XY.getD i 0))
  ++ [ Ev.sq .chal ]
  ++ (List.range (2 * s.tComms)).map (fun i => Ev.abs T_TCOMM (STEP_UNREAD_TCOMM_XY.getD i 0))
  ++ [ Ev.sq .chal ]
  ++ [ Ev.sq .fork ]
  ++ [ Ev.abs T_CIP (chainItemVal T_CIP 0) ]
  ++ [ Ev.sq .full ]
  ++ (List.range s.ipaRounds).flatMap (fun r =>
       (List.range 4).map (fun j => Ev.abs T_LR (chainItemVal T_LR (4 * r + j)))
       ++ [ Ev.sq .chal ])
  ++ (List.range 2).map (fun i => Ev.abs T_DELTA (chainItemVal T_DELTA i))
  ++ [ Ev.sq .chal ]

/-! ## §7 — ⚑ IT IS NOT THE BORROWED FIXTURE.

If the chained tape ever coincided with `PastaPoseidonFq`'s, this file would be the same
measurement under a new filename. -/

/-- **`the_chain_is_not_the_borrowed_fixture`** — same LENGTH (both are `prev_challenges = 2`,
15-column, 7-chunk Pasta proofs, so the shape agrees by construction) and a different VALUE in
every labelled block, including the verifier-index digest and all five phase-1 outputs. -/
theorem the_chain_is_not_the_borrowed_fixture :
    chainTape.length = Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape.length
    ∧ chainTape ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape
    ∧ STEP_VKDIGEST ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.VKDIGEST
    ∧ STEP_WCOMM_XY ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.WCOMM_XY
    ∧ STEP_BETA ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
    ∧ STEP_GAMMA ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
    ∧ STEP_ALPHA_CHAL ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
    ∧ STEP_ZETA_CHAL ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL
    ∧ STEP_DIGEST ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.FQDIGEST := by
  native_decide

#assert_compiled the_chain_is_not_the_borrowed_fixture

/-! ## §8 — THE SHAPE WAS MEASURED, NOT CHOSEN.

⚑ A finding worth stating plainly: the four transcript parameters of `KimchiWrapMain.shapeWrap` —
`prevs = 2`, `ipaRounds = 16`, `wComms = 15`, `tComms = 7` — are exactly what dregg's own step proof
produces. `shapeWrap`'s docstring derives them from `Backend.Tick.Rounds.n`, `Plonk_types.Columns.n`
and the devnet wrap VK; this is the independent confirmation, from a proof rather than from a
reading. -/

/-- **`chain_shape_is_the_measured_step_shape`** — and the whole record agrees with `shapeWrap`. -/
theorem chain_shape_is_the_measured_step_shape :
    shapeChain.prevs = 2
    ∧ shapeChain.ipaRounds = 16
    ∧ shapeChain.wComms = 15
    ∧ shapeChain.tComms = 7
    ∧ shapeChain = shapeWrap
    ∧ chainTape.length = 37
    ∧ STEP_LR_XY.length = 4 * shapeChain.ipaRounds
    ∧ STEP_TCOMM_XY.length = 2 * shapeChain.tComms := by
  native_decide

#assert_compiled chain_shape_is_the_measured_step_shape

/-! ### §8b — ⚑ THE ONE SLOT WHERE THE CHAIN OVERRIDES A DERIVED VALUE, exhibited.

W-XHAT (`d89815028`) turned `x_hat` from a fixture into an MSM output, and `schedule` now absorbs
`s.xhatXY`. This file does not, and cannot: the sponge tape has to be the one kimchi's verifier ran
on, or §3 is not a reality gate. The theorem below reads BOTH schedules' `T_XHAT` words off the
emitted event lists — not off the definitions that produced them — and shows they differ. -/

/-- The words the CHAIN's schedule absorbs under `T_XHAT`, read off the emitted event list. -/
def chainXhatAbsorbed : List Nat :=
  (chainSchedule shapeChain).filterMap
    (fun e => match e with | .abs t w => if t == T_XHAT then some w else none | .sq _ => none)

/-- The same for `KimchiWrapMain.schedule` at the same shape. -/
def wrapXhatAbsorbed : List Nat :=
  (schedule shapeChain).filterMap
    (fun e => match e with | .abs t w => if t == T_XHAT then some w else none | .sq _ => none)

/-- **`chain_xhat_is_the_step_proofs_not_the_msm_output`** — ⚑ the substitution, stated rather than
left for a reader to notice, and the memo obligation discharged for the COMMITTED shape.

* The chain absorbs `STEP_PUBCOMM_XY`, this step proof's real public-input commitment.
* `schedule` absorbs `shapeChain.xhatXY`, §15's MSM output.
* They DIFFER — so the override is real, not a relabelling, and §15's MSM is not yet an MSM over
  dregg's step statement. `xhatScalar` is `wrapFixtureQ`'s filler; the 67 real scalars are
  W-PREV's (`wrap_main.ml:201-256`), which is named in `KimchiWrapMain.WRAP_UNCONSUMED` and is why
  `x_hat` stayed on that census when its MSM landed.
* And `shapeChain.xhatXY = xhatOut shapeChain.xhatTerms` — the obligation `EmitWrapMainJson`
  enforces at emission time and `xhat_smoke_shape_absorbs_the_msm_output` closes only for
  `shapeSmoke`. Here it is a theorem at the committed shape. -/
theorem chain_xhat_is_the_step_proofs_not_the_msm_output :
    chainXhatAbsorbed = [STEP_PUBCOMM_XY.getD 0 0, STEP_PUBCOMM_XY.getD 1 0]
    ∧ wrapXhatAbsorbed = [shapeChain.xhatXY.1, shapeChain.xhatXY.2]
    ∧ chainXhatAbsorbed ≠ wrapXhatAbsorbed
    ∧ shapeChain.xhatXY = xhatOut shapeChain.xhatTerms
    ∧ shapeChain.xhatTerms = XHAT_TERMS_FULL
    ∧ STEP_PUBCOMM_XY.length = 2 := by
  native_decide

#assert_compiled chain_xhat_is_the_step_proofs_not_the_msm_output

/-! ## §9 — the emission. `WrapData` with the chained trace substituted, nothing else changed.

⚑ `KimchiWrapMain` is consumed READ-ONLY. `mkWrapWith` builds `sp := runSpongeQ (baseSp s)
(schedule s) bt bw`; this substitutes `chainSchedule` for `schedule` and leaves the branch data,
every row emitter, the placement and the renderer exactly as that file wrote them. Because
`baseCh`/`baseBr` are computed from `t.sp`, the downstream variable bases follow the chained trace
automatically. -/

def chainBranch : BranchData :=
  runBranch shapeChain (min 1 (shapeChain.branches - 1))
    ((List.range shapeChain.branches).map (fun i => min 2 i))
    ((List.range shapeChain.branches).map (fun _ => 16))

def tChain : WrapData := { sh := shapeChain, sp := chainRun, br := chainBranch }

/-- The same `WrapData` on the BENT tape — the emission whose public words must differ. -/
def chainBentItemVal (t i : Nat) : Nat :=
  if t == T_WCOMM && i == 0 then qAdd (chainItemVal T_WCOMM 0) 1 else chainItemVal t i

def chainBentSchedule (s : WrapShape) : List Ev :=
  (chainSchedule s).map (fun e => match e with
    | .abs t w => if t == T_WCOMM && w == chainItemVal T_WCOMM 0
                  then Ev.abs t (qAdd w 1) else Ev.abs t w
    | .sq k => Ev.sq k)

def tChainUnread : WrapData :=
  { sh := shapeChain
  , sp := runSpongeQ (baseSp shapeChain) (chainUnreadSchedule shapeChain) 99999 0
  , br := chainBranch }

def tChainBent : WrapData :=
  { sh := shapeChain
  , sp := runSpongeQ (baseSp shapeChain) (chainBentSchedule shapeChain) 99999 0
  , br := chainBranch }

/-- **`the_emitted_public_vector_moves_with_the_step_proof`** — the closing rung's PUBLIC words,
which are what a verifier sees, differ between the honest and bent emissions, and the assembly's
shape does not. This is §6's property carried all the way to the object the Pallas harness proves.

⚠ `pubWords` is `shapeWrap.pubWords`; `KimchiWrapMain.exposedVars` maps them onto raw prechallenges,
so a word that moved is a challenge that moved. -/
theorem the_emitted_public_vector_moves_with_the_step_proof :
    wrapPublic tChainBent ≠ wrapPublic tChain
    ∧ (rungRows tChainBent .bind true).length = (rungRows tChain .bind true).length
    ∧ (wrapPublic tChain).length = shapeChain.pubWords
    ∧ wrapPublic tChainUnread = wrapPublic tChain := by
  native_decide

#assert_compiled the_emitted_public_vector_moves_with_the_step_proof

/-- **`the_chained_assembly_places`** — `placeChecked` ACCEPTS the chained assembly at the closing
rung, with no inert public word. `KimchiWrapMain`'s placement refuses a declared public word no gate
reads, so a nonempty accepted placement is evidence every exposed word is READ. -/
theorem the_chained_assembly_places :
    (refusalOf shapeChain shapeChain.pubWords (wrapGates (rungRows tChain .bind true)) == none)
       = true
    ∧ (placedOf shapeChain shapeChain.pubWords
         (wrapGates (rungRows tChain .bind true))).length
       = shapeChain.pubWords + (rungRows tChain .bind true).length
    ∧ inertPublicWords shapeChain.pubWords
        (wrapGates (rungRows tChain .bind true)) = [] := by
  native_decide

#assert_compiled the_chained_assembly_places

/-- **`the_chained_control_differs_only_in_the_placement`** — the UNWIRED control is a control: same
row count, same kinds, same coefficients, same probe flags, and the perm columns differ at exactly
the probe rows. -/
theorem the_chained_control_differs_only_in_the_placement :
    (rungRows tChain .bind false).length = (rungRows tChain .bind true).length
    ∧ ((rungRows tChain .bind true).zip (rungRows tChain .bind false)).all
        (fun p => p.1.kind == p.2.kind && p.1.coeffs == p.2.coeffs && p.1.probe == p.2.probe)
       = true
    ∧ (((rungRows tChain .bind true).zip (rungRows tChain .bind false)).filter
         (fun p => p.1.perm != p.2.perm)).length
       = ((rungRows tChain .bind true).filter (fun r => r.probe)).length
    ∧ ((rungRows tChain .bind true).filter (fun r => r.probe)).length > 0 := by
  native_decide

#assert_compiled the_chained_control_differs_only_in_the_placement

/-! ## §10 — the renderer. Same JSON the pickles harnesses parse. -/

def chainJson (t : WrapData) (k : Rung) (wired : Bool) (name : String) : String :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderWrapCircuit name p (p + rows.length)
    (placedOf t.sh p (wrapGates rows)) (wrapWitness t p rows)
    (if p == 0 then [] else wrapPublic t) (rungProbeRows t k)

/-! ⚠ NO `#assert_namespace_axioms` HERE, and the absence is the honest label. Every theorem above
rests on `Lean.ofReduceBool` — they are closed by compiled evaluation, not by the kernel — so a
namespace-wide axiom assertion would either fail or have to be weakened until it said nothing.
`#assert_compiled` under each theorem is the correct, weaker pin: it passes only if the proof rests
on a `native_decide` oracle and nothing worse, and it ERRORS on a kernel-clean proof, so it cannot
launder one downward. See `docs/GUARD-DISCIPLINE.md`. -/

end Dregg2.Circuit.Emit.KimchiStepWrapChain
