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
* ⚑ **THE CEILING IS `w5_key` SINCE 2026-08-05, AND MOVING IT WAS THE WHOLE JOB.** Everything here
  used to stop at `Rung.bind` (`w4_bind`) — not for want of rows, but because `keyRows`' closing
  `digestTie` welds the index sponge's squeeze to the transcript's FIRST absorbed word, the wrap
  circuit committed to **Mina's** `step-transaction` verification key, and this tape is **dregg's
  own** step proof's. Two different circuits, one unsatisfiable `Field.Assert.equal`, and `.key` is
  in `rungsUpto` of every rung above `w4_bind` — so that single row was the ceiling, not W-COMBINE
  and not W-BULLET. `step_keys` is a per-branch vector of the compiled step rules' keys
  (`wrap_main.ml:98-101`), so dregg's step rule now takes an entry beside Mina's
  (`KimchiWrapMain.KEY_CHAIN_BRANCH`) and `tChain.br` selects it.
  `the_chain_climbs_past_bind_at_dreggs_own_step_key` is the tie; the Pallas harness proves the
  1 999-row `chain_w5_key` with `verify() == true`. `xhatRows`, `splitRows` and `ftcRows` are still
  not in the row list. §1 says what that costs on the `x_hat` slot specifically, and
  `chain_xhat_is_the_step_proofs_not_the_msm_output` exhibits it.
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
open Dregg2.Circuit.Emit.KimchiCircuitJson (renderCircuit)
open Dregg2.Circuit.Emit.KimchiPlacement (inertPublicWords)
open Dregg2.Circuit.Emit.KimchiStepWrapChainFixture
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams newSponge absorbMany challenge digestInto)

/-! ## §1 — THE SHAPE, MEASURED OFF THE STEP PROOF RATHER THAN CHOSEN.

**Six** of `WrapShape`'s nine fields are read out of the proof this file is about. The remaining
three — `emsRows`, `branches`, `pubWords` — are wrap-instance parameters with no step-side source at
all, because `wrap_main` is per-zkApp (`wrap_main.ml:96-105`); they stay `shapeWrap`'s.

⚑⚑ **`xhatEntries` AND `xhatXY` ARE THIS PROOF'S SINCE 2026-08-06, AND THAT IS THE OVERRIDE THIS
FILE NO LONGER HAS.** They used to be copied from `shapeWrap` — 67 entries over Mina's packed
`Types.Step.Statement`, whose scalars are a NAMED FIXTURE — and `schedule` absorbed
`STEP_PUBCOMM_XY` in place of the fold's output, because a reality gate about `proof.oracles(...)`
has to absorb the commitment the verifier absorbed. Two objects where upstream has one, and the
theorem that said so (`chain_xhat_is_the_step_proofs_not_the_msm_output`) named the repair:

> To make `x_hat` the step proof's real public-input commitment the MSM has to run over dregg's step
> proof's OWN public input against the step SRS Lagrange basis — `STEP_PUBLIC = 12` terms, not
> `XHAT_TERMS_FULL = 67` … So `shapeWrap.xhatTerms = shapeWrap.xhatTerms` is itself the thing that
> has to go, and `chain_shape_is_the_measured_step_shape`'s `shapeWrap = shapeWrap` conjunct goes
> with it.

Both have gone. `XHAT_OWN_SEL` is twelve entries of a **disjoint index space** whose bases are the
step SRS's Lagrange basis **at this proof's own domain** (`2 ^ STEP_DOMAIN_LOG2 = 4096`, not
`MinaStepSrsLagrange`'s 65536) and whose scalars are the twelve `Fp` public inputs the prover
actually handed `kimchi::verifier`. `xhatOutOf XHAT_OWN_SEL` **is** `STEP_PUBCOMM_XY` —
`the_own_xhat_msm_is_this_proofs_public_input_commitment` in Lean, and the same identity asserted
independently in arkworks by `tape.rs` before the fixture was written.

So `schedule` now absorbs `s.xhatXY` at `wrap_verifier.ml:617` exactly as `schedule` does. The
reality gate holds because the MSM computes the right point, not because the tape was patched around
it — which is a strictly stronger statement about the same five numbers.

⚠ **AND `shapeWrap ≠ shapeWrap` IS NOW A FACT, NOT A REGRESSION.** A `WrapShape` for verifying
dregg's step rule genuinely has that rule's statement width; the two shapes agree on every transcript
parameter and differ in exactly the two x_hat fields.
`chain_shape_is_the_measured_step_shape` states both halves. -/

/-- ⚑⚑ **THE CHAIN'S `WrapData` IS THE COMMITTED ASSEMBLY ITSELF.** There is no second shape and no
substituted sponge: `KimchiWrapMain.mkWrap shapeWrap` absorbs dregg's own step key digest at
`wrap_verifier.ml:537` (`RC_DIGEST`), the 67-entry MSM's output at `:617` — which IS this proof's
`public_comm` — and the same 116 commitment words this file's tape carries, and it selects
`KEY_CHAIN_BRANCH` at this proof's own domain. What is left here is the REALITY GATE: a reference
sponge, a flat tape, and the red controls. -/
def tChain : WrapData := mkWrap shapeWrap

/-! ## §2 — THE TAPE, and the schedule that carries it.

`chainTape` is the phase-1 absorb tape up to β, in `kimchi/src/verifier.rs:162-177` order — which
is the order `wrap_verifier.ml:537-619` re-runs in-circuit. It is assembled from the labelled
blocks, not pasted as one opaque list. -/

def chainTape : List Nat :=
  STEP_VKDIGEST :: (STEP_PREVCOMM_XY ++ STEP_PUBCOMM_XY ++ STEP_WCOMM_XY)

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

/-- ⚑⚑ **AND THOSE FIVE VALUES ARE FIVE OF MINA'S FORTY — so `chain_reality_gate` is not a claim
about a tape, it is a claim about the PUBLIC INPUT the wrap circuit has to produce.**

`MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED` is `PreparedStatement::to_public_input(40)` — the
forty Fq words `make_zkapp_verifier_index` hands `kimchi::verifier::verify`. Slots 5–8 are β, γ, α, ζ
and slot 10 is `sponge_digest_before_evaluations`. This says they are exactly the values kimchi's own
`proof.oracles(...)` computed for the step proof whose tape §3 replays.

⚑ **THIS IS THE JOIN THAT DID NOT EXIST BEFORE 2026-08-05**, and could not have: the forty came from
`pickles_kimchi_marshal`'s step proof and this tape came from a *different* step proof, so the two
lists were about different objects and any equality between them would have been a coincidence
worth investigating rather than a fact. One `prove_step` writes both now.

⚠ **SAY THE SCOPE.** Chaining `chain_reality_gate` with this gives: the Lean-emitted transcript,
driven on the FULL tape of this step proof, reproduces five of Mina's forty. The MAIN assembly
(`KimchiWrapMain.schedule`) does **not** reproduce them, and is not claimed to — it absorbs Mina's
`step-transaction` key digest at `wrap_verifier.ml:537` instead of this proof's, and §15's MSM output
at `:617` instead of this proof's `public_comm`. Both are absorbed BEFORE β, so every challenge below
moves. Those two items are W-KEY's and W-XHAT's remaining distance, and they are the whole of it:
the 116 commitment words between them are already this proof's. -/
theorem the_chains_challenges_are_five_of_minas_forty :
    STEP_BETA = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 5 0
    ∧ STEP_GAMMA = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 6 0
    ∧ STEP_ALPHA_CHAL
        = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 7 0
    ∧ STEP_ZETA_CHAL
        = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 8 0
    ∧ STEP_DIGEST = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 10 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §4 — ⚑ THE CIRCUIT'S OWN SPONGE, not just the reference one.

§3 runs `PastaPoseidonFq`'s `SpongeSt`. The EMITTED CIRCUIT runs `KimchiWrapMain.runSpongeQ`, a
different object: an event-driven rate-2 trace that also allocates a variable per lane and records
where every permutation falls. The two must agree, or the rows the harness proves are not the rows
this gate is about. -/

/-- The `chal` squeezes of the circuit trace, truncated the way `lowest_128_bits` truncates. -/
def chainChals : List Nat := (chalSqueezes tChain.sp).map (fun e => e.2 % 2 ^ 128)

/-- The FORK squeeze — `sponge_digest_before_evaluations` (`wrap_verifier.ml:646`). -/
def chainForkVal : Nat := ((forkSqueeze tChain.sp).map (fun e => e.2)).getD 0

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
    (schedule shapeWrap).length = (schedule shapeWrap).length
    ∧ ((schedule shapeWrap).zip (schedule shapeWrap)).all
        (fun p => match p.1, p.2 with
          | .abs t _, .abs u _ => t == u
          | .sq a, .sq b => a == b
          | _, _ => false) = true
    ∧ (chalSqueezes tChain.sp).length = nChals shapeWrap := by
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
    ∧ chainTape.length = 1 + 2 * shapeWrap.prevs + 2 + 2 * shapeWrap.wComms := by
  native_decide

#assert_compiled the_commitments_needed_no_encoding

/-! ## §6 — ⚑ THE RED CONTROLS. The property nothing has ever shown: that one half DEPENDS on the
other.

The positive control is not "some value changes" — it is that the wrap transcript moves **to the
value kimchi's own sponge produces for the bent tape**, which the exporter measured by bending the
same coordinate and re-running the same Rust sponge.

The negative control's strong half is also measured in Rust: `pickles-extractors/src/tape.rs` bends `z_1`,
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
    ∧ STEP_BENT_INDEX = 1 + 2 * shapeWrap.prevs + 2 := by
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

⚠ The strong form of this control is MEASURED, not stated here: `pickles-extractors/src/tape.rs` bends all
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
  ++ [ Ev.abs T_CIP (itemVal T_CIP 0) ]
  ++ [ Ev.sq .full ]
  ++ (List.range s.ipaRounds).flatMap (fun r =>
       (List.range 4).map (fun j => Ev.abs T_LR (itemVal T_LR (4 * r + j)))
       ++ [ Ev.sq .chal ])
  ++ (List.range 2).map (fun i => Ev.abs T_DELTA (itemVal T_DELTA i))
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

/-- **`chain_shape_is_the_measured_step_shape`** — ⚑⚑ **THE MEASURED STEP SHAPE *IS* THE COMMITTED
WRAP SHAPE, AND THAT COLLAPSE IS THE POINT OF THE COMMIT.**

This file used to carry `shapeChain`, a `WrapShape` of its own. Six of its nine fields were read off
dregg's step proof and three were `shapeWrap`'s; on 2026-08-06 the two x_hat fields — the last that
disagreed — became the same object, because `KimchiWrapMain` §15's MSM now runs over the step proof's
own published `Types.Step.Statement` against its own domain's Lagrange basis. A second shape whose
every field equals the first is two shapes that will disagree later, so `shapeChain` is DELETED and
this theorem is what says the deletion was sound: every parameter this file MEASURES off the proof is
the value `shapeWrap` declares from `Backend.Tick.Rounds.n`, `Plonk_types.Columns.n` and the devnet
wrap VK. Two derivations, one shape.

⚠ The last three legs are the measurement half — the fixture's own lists have the lengths the shape
claims, so a re-export that changed the proof's IPA round count or `t_comm` chunking reds here rather
than three rungs up. -/
theorem chain_shape_is_the_measured_step_shape :
    shapeWrap.prevs = STEP_PREVCOMM_XY.length / 2
    ∧ shapeWrap.ipaRounds = STEP_IPA_ROUNDS
    ∧ shapeWrap.wComms = STEP_WCOMM_XY.length / 2
    ∧ shapeWrap.tComms = STEP_TCOMM_XY.length / 2
    ∧ (shapeWrap.prevs, shapeWrap.ipaRounds, shapeWrap.wComms, shapeWrap.tComms) = (2, 16, 15, 7)
    ∧ shapeWrap.xhatEntries = List.range XHAT_TERMS_FULL
    ∧ shapeWrap.xhatEntries.length = STEP_PUBLIC
    ∧ chainTape.length = 37
    ∧ STEP_LR_XY.length = 4 * shapeWrap.ipaRounds
    ∧ STEP_TCOMM_XY.length = 2 * shapeWrap.tComms := by
  native_decide

#assert_compiled chain_shape_is_the_measured_step_shape

/-! ### §8b — ⚑ THE SLOT THE CHAIN USED TO OVERRIDE, AND NO LONGER DOES.

W-XHAT (`d89815028`) turned `x_hat` from a fixture into an MSM output over Mina's packed statement,
and this file could not absorb that output: the sponge tape has to be the one kimchi's verifier ran
on, or §3 is not a reality gate. So it absorbed `STEP_PUBCOMM_XY` directly and said so.

⚑ **SINCE 2026-08-06 THERE IS NOTHING TO OVERRIDE AND NOTHING TO COMPARE.** The step proof publishes
a `Types.Step.Statement`, `shapeWrap.xhatEntries` is `wrap_verifier.ml:539-548`'s own 67, and the
fold's output IS the public-input commitment `kimchi::verifier` computed for that proof. The chain's
schedule and the wrap assembly's schedule are ONE function. `wrapXhatAbsorbed` is deleted with the
override: a def that read `schedule shapeWrap` beside another that read `schedule shapeWrap` would
have been a control comparing a list with itself. -/

/-- The words the assembly's schedule absorbs under `T_XHAT`, read off the emitted event list rather
than off the definitions that produced them. -/
def chainXhatAbsorbed : List Nat :=
  (schedule shapeWrap).filterMap
    (fun e => match e with | .abs t w => if t == T_XHAT then some w else none | .sq _ => none)

/-- **`chain_xhat_is_the_msm_output_and_the_step_proofs`** — ⚑⚑ **THE ABSORBED PAIR, THE FOLD'S
OUTPUT AND THE VERIFIER'S COMMITMENT ARE ONE VALUE.**

Two predecessors of this theorem carried inequalities and both were defects wearing controls.
`chain_xhat_is_the_step_proofs_not_the_msm_output` said the chain's absorbed pair DIFFERS from §15's
MSM output — true, and a statement that `xhatRows`' closing `caRowQ` (which writes into the
transcript's own `T_XHAT` σ classes) constrained the absorbed pair to a point computed from scalars
belonging to no proof, so `w6_xhat` had no honest witness. Its successor kept a leg requiring the
chain's twelve-entry selection to differ from `shapeWrap`'s sixty-seven. That leg is gone too: the
selections are the same because the statements are.

⚑ **WHAT IS LEFT IS THE SECOND-COPY DETECTOR, AND IT IS THE WHOLE VALUE OF THE FILE HERE.**
`chainTape` and `schedule` are two INDEPENDENT constructions of the same absorbed words — the tape
splices `STEP_PUBCOMM_XY` in directly (§2) and the schedule reads `s.xhatXY`, which the MSM
computes. §3's reality gate runs on the FIRST and §4's emitted trace on the SECOND, so if the memo
ever stopped being this proof's commitment the two would come apart and `chain_reality_gate` would
stay GREEN while the circuit absorbed something else. That is exactly how `whSgOld` — a second copy
of `sg_old` still reading the borrowed proof — kept `xhatOut 67` unchanged while `RC_SGOLD` moved,
and a green refusal was the evidence of the defect rather than of its absence. -/
theorem chain_xhat_is_the_msm_output_and_the_step_proofs :
    chainXhatAbsorbed = [STEP_PUBCOMM_XY.getD 0 0, STEP_PUBCOMM_XY.getD 1 0]
    ∧ chainXhatAbsorbed = [shapeWrap.xhatXY.1, shapeWrap.xhatXY.2]
    ∧ shapeWrap.xhatXY = xhatOutOf shapeWrap.xhatEntries
    ∧ shapeWrap.xhatEntries = List.range XHAT_TERMS_FULL
    ∧ shapeWrap.xhatEntries.length = STEP_PUBLIC
    ∧ STEP_PUBCOMM_XY.length = 2
    -- ⚑⚑ the second-copy detector: the EMITTED trace's `T_XHAT` cells against the REFERENCE tape.
    ∧ ((tChain.sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).map (fun e => e.word))
        = [chainTape.getD (1 + 2 * shapeWrap.prevs) 0,
           chainTape.getD (1 + 2 * shapeWrap.prevs + 1) 0] := by
  native_decide

#assert_compiled chain_xhat_is_the_msm_output_and_the_step_proofs

/-! ## §9 — the emission. `WrapData` with the chained trace substituted, nothing else changed.

⚑⚑ **`KimchiWrapMain` IS CONSUMED READ-ONLY AND NOTHING IS SUBSTITUTED ANY MORE.** This file used to
build a parallel `WrapData` — its own shape, its own `itemVal`, its own `schedule`, its own branch —
because the wrap assembly committed to Mina's `step-transaction` key and ran its MSM over a packed
statement belonging to no proof. Both are fixed at source now (`KimchiWrapMain` §2's `RC_DIGEST`,
§14's `KEY_CHAIN_BRANCH`, §15's published scalars), so `tChain` is `mkWrap shapeWrap` and the
BENT and UNREAD `WrapData`s below are the only ones this file constructs. They are red controls and
they say so. -/

/-- The same `WrapData` on the BENT tape — the emission whose public words must differ. -/
def chainBentItemVal (t i : Nat) : Nat :=
  if t == T_WCOMM && i == 0 then qAdd (itemVal T_WCOMM 0) 1 else itemVal t i

def chainBentSchedule (s : WrapShape) : List Ev :=
  (schedule s).map (fun e => match e with
    | .abs t w => if t == T_WCOMM && w == itemVal T_WCOMM 0
                  then Ev.abs t (qAdd w 1) else Ev.abs t w
    | .sq k => Ev.sq k)

def tChainUnread : WrapData :=
  { sh := shapeWrap
  , sp := runSpongeQ (baseSp shapeWrap) (chainUnreadSchedule shapeWrap) 99999 0
  , br := tChain.br }

def tChainBent : WrapData :=
  { sh := shapeWrap
  , sp := runSpongeQ (baseSp shapeWrap) (chainBentSchedule shapeWrap) 99999 0
  , br := tChain.br }

/-! ### §9a — ⚑ THE RUNG IS PART OF THE STATEMENT, AND A RUNG-BLIND ALIAS MOVED UNDER THIS FILE.

`KimchiWrapMain` used to carry `wrapPublic`/`wrapWitness`, aliases documented as "the closing rung's
… kept for callers that do not carry a `Rung`". "The closing rung" is not a constant. This file's
four emitted-vector facts landed at `b7145476a` (08-03 01:44), when `wrapPublic` had an inline
`t.sh.pubWords`-wide body over the sponge/challenge/branch env; the alias was then REDEFINED FOUR
TIMES in 23 hours as the ladder grew — `wrapPublicAt _ .xhat` (`d89815028`, 08-03 10:23), `.split`
(`a06587ab3`, 17:20), `.ftcomm` (`de39288d2`, 18:11), `.prev` (`5269fa248`, 08-04 00:45, W-PREV) —
and **not one caller's diff shows any of it.**

Three of those four were harmless here, by luck rather than by design: `WitnessBuilder.envIndex`
folds the REVERSED env so a variable's FIRST binding wins, and each rung APPENDS its environment, so
widening `.bind` to `.ftcomm` cannot move a word already bound. The fourth was not:
`rungPub _ .prev = s.pubWords + 1`, because `w9_prev`'s own row ties `messages_for_next_step_proof`
to a 23rd public word (`wrap_main.ml:350-351`).

⚑ **THAT — an off-by-one in a WIDTH — is the whole reason this module was RED**, and the reason the
redness read as something far worse. These four facts used to be ONE conjunction; its third conjunct
said `(wrapPublic tChain).length = shapeWrap.pubWords`, which W-PREV turned into `23 = 22`.
`native_decide` reported *the conjunction* false and `#assert_compiled` correctly caught the
`sorryAx`, so a module whose olean was absent from every build read as **"the wrap chain's
tamper-detection claim is false."** It is not. Measured 2026-08-04 on a clean HEAD worktree, in 5.8
seconds: the tamper claim is TRUE, the shape claim is TRUE, the negative control is TRUE, and only
the width was false. A conjunction that fails tells you nothing about which half failed; each
conjunct is now its own named theorem, so the next such move names itself.

⚑ **AND THE RUNG IS EXPLICIT.** §0b: this file's four emitted-vector facts are at `Rung.bind`
(`w4_bind`), which is the rung they were measured on and the rung §10 pairs them with; `w5_key` is
emitted and proved beside it since the climb, and its own control figures are the harness's. The
old theorem already paired its public vector with `rungRows _ .bind true`. Pairing `.bind` rows with a
`.prev` public vector was never the intended statement. `wrapPublicAt _ .bind` is, and it puts the
vector, the rows, the placement and §10's JSON on one single rung. The aliases are DELETED rather than
repaired: their only two consumers were this file and `EmitStepWrapChainJson`, and a name whose
meaning is a moving target is worse than no name. -/

/-- **`the_emitted_public_vector_is_its_rungs_width`** — the instance of
`KimchiWrapMain.wrapPublicAt_length`, at the committed shape, at BOTH the rung this file emits and
the ladder's closing rung. ⚑ It is an INSTANCE of a general kernel-clean lemma, not a separately
evaluated literal — which is exactly what the false conjunct was, and why a rung change could
falsify it in silence. The `+ 1` is `w9_prev`'s 23rd word. -/
theorem the_emitted_public_vector_is_its_rungs_width :
    (wrapPublicAt tChain .bind).length = WRAP_PRIMARY_LEN
    ∧ (wrapPublicAt tChain .prev).length = WRAP_PRIMARY_LEN :=
  ⟨wrapPublicAt_length tChain .bind, wrapPublicAt_length tChain .prev⟩

#assert_axioms the_emitted_public_vector_is_its_rungs_width

/-- **`the_emitted_public_vector_moves_with_the_step_proof`** — ⚑ THE TAMPER CLAIM, ALONE, so that a
failure names itself. `w4_bind`'s PUBLIC words — what a verifier sees — differ between the honest
emission and the one whose step proof had a single Fq coordinate of `w_comm` bent. This is §6's
property carried all the way to the object the Pallas harness proves.

⚠ `KimchiWrapMain.exposedVars` maps these words onto RAW prechallenges, so a word that moved is a
challenge that moved. -/
theorem the_emitted_public_vector_moves_with_the_step_proof :
    wrapPublicAt tChainBent .bind ≠ wrapPublicAt tChain .bind := by
  native_decide

#assert_compiled the_emitted_public_vector_moves_with_the_step_proof

/-- **`the_bend_moves_every_transcript_derived_public_word`** — ⚑ THE FIGURE, and it is a THEOREM
rather than a count read off a harness artifact. "21 of 22" has been reported repeatedly from the
committed JSON; this states the sharp form the count was standing in for.

`exposedVars` is 4 challenge words + 1 fork digest + 16 bulletproof prechallenges + 1 `branch_data`,
`.take 22`. All but the last are transcript-derived and EVERY ONE of them moves under the bend. The
last is `(branchVars …).packed` — `branch_data`, `4·16 + 2·1 = 66`, which has no transcript
dependence at all — and it does not move. So the honest statement is not "21 of 22 happened to
differ": it is *every transcript-derived public word moves and the one non-transcript word does
not*, with the identity of that word pinned to the variable rather than to an index.

⚠ ⚑ **AND IT IS QUANTIFIED OVER THE SLOTS THIS RUNG DERIVES, NOT OVER `range 21`, SINCE 2026-08-05.**
`wrapPublicAt` returns a vector indexed by **MINA'S SLOT**, 0–39 — it has since the layout landed —
while this statement still read `(List.range 21)`, which was `exposedVars`' POSITION indexing from
when the vector was dense. Those two agree for no index at all: `range 21` names Mina slots 0–20,
eight of which (0, 1, 2, 3, 4, 9, 11, 12) `w4_bind` does not derive and which are therefore ZERO in
BOTH emissions, so the conjunct asserted that a zero differs from itself. **This was a red the
layout commit left behind, not one the pass-through wiring introduced** — `wrapSlots` and
`wrapSlotsAt`'s `.bind` branch are untouched by that change, so the eight non-moving slots are the
same eight before and after it.

The repair is to say what the docblock always meant: quantify over `wrapSlotsAt … .bind`, the slots
the rung actually ties, and exclude `branch_data` by SLOT rather than trimming an index range. -/
theorem the_bend_moves_every_transcript_derived_public_word :
    (exposedVars tChain).length = 22
    ∧ ((wrapSlotsAt shapeWrap .bind).filter (fun s => s != WRAP_SLOT_BRANCH_DATA)).all (fun s =>
        (wrapPublicAt tChainBent .bind).getD s 0 != (wrapPublicAt tChain .bind).getD s 0) = true
    -- ⚑ …and the ONE that does not move is `branch_data`, at Mina's slot 29.
    ∧ (wrapPublicAt tChainBent .bind).getD WRAP_SLOT_BRANCH_DATA 0
        = (wrapPublicAt tChain .bind).getD WRAP_SLOT_BRANCH_DATA 0
    ∧ (wrapSlotsAt shapeWrap .bind).contains WRAP_SLOT_BRANCH_DATA = true
    -- …with its identity pinned to the VARIABLE, which is the point of the whole statement.
    ∧ slotVarAt tChain .bind WRAP_SLOT_BRANCH_DATA
        = some (branchVars shapeWrap (baseBr shapeWrap tChain.sp)).packed
    ∧ (exposedVars tChain).getD 21 PVAR_NOWHERE
        = (branchVars shapeWrap (baseBr shapeWrap tChain.sp)).packed := by
  native_decide

#assert_compiled the_bend_moves_every_transcript_derived_public_word

/-- **`the_emitted_assembly_shape_does_not_move_with_the_step_proof`** — and the assembly does NOT
move: a bend changes the values a verifier reads, not the circuit it reads them from. Without this,
"the public vector moved" would be consistent with having emitted a different circuit. -/
theorem the_emitted_assembly_shape_does_not_move_with_the_step_proof :
    (rungRows tChainBent .bind true).length = (rungRows tChain .bind true).length := by
  native_decide

#assert_compiled the_emitted_assembly_shape_does_not_move_with_the_step_proof

/-- **`the_emitted_public_vector_does_not_move_with_what_it_does_not_read`** — the negative control
carried to the emission. `tChainUnread` is driven by a tape RE-EXTRACTED from a second, genuinely
different proof object whose `z_1`, `z_2`, `ft_eval1`, `delta` and `sg` were bent
(`chain_unread_bend_is_a_different_proof_with_the_same_tape`), and its public vector is identical. -/
theorem the_emitted_public_vector_does_not_move_with_what_it_does_not_read :
    wrapPublicAt tChainUnread .bind = wrapPublicAt tChain .bind := by
  native_decide

#assert_compiled the_emitted_public_vector_does_not_move_with_what_it_does_not_read

/-- **`the_chained_assembly_places`** — `placeChecked` ACCEPTS the chained assembly at the closing
rung, with no inert public word. `KimchiWrapMain`'s placement refuses a declared public word no gate
reads, so a nonempty accepted placement is evidence every exposed word is READ. -/
theorem the_chained_assembly_places :
    (refusalOf shapeWrap .bind (rungPub shapeWrap .bind)
        (wrapGates (rungRows tChain .bind true)) == none) = true
    ∧ (placedOf shapeWrap .bind (rungPub shapeWrap .bind)
         (wrapGates (rungRows tChain .bind true))).length
       = WRAP_PRIMARY_LEN + (rungRows tChain .bind true).length
    ∧ inertSlotsAt shapeWrap .bind
        (wrapGates (rungRows tChain .bind true)) = wrapInertOk shapeWrap .bind := by
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

/-! ## §11 — ⚑ ABSORPTION vs CONSUMPTION, MEASURED — and the two things that USED to block the
stronger claim, both closed 2026-08-05.

§0b's honest sentence has been *"the step proof's commitments enter as **sponge inputs**, not as
curve points a sub-circuit consumes."* W-COMBINE (`w10_combine`, §23) and W-BULLET (`w11_bullet`,
§24) have since landed, and they change that sentence — but not in the direction a reader would
guess, and not for the same reason on both sides of it. So it is measured here rather than restated.

⚑ **THE VARIABLE LAYER ALREADY CONSUMES, AND IT CONSUMES THE CHAIN'S OWN CELLS.** `combPtVar` and
`bullCipV`/`bullLrV`/`bullDeltaV` allocate NOTHING: every one of them reads
`(t.sp.evs.filter (·.isAbs && ·.tag == …)).wordV`, i.e. the very σ class the transcript's absorb
wrote. Driven by `tChain`, that class holds a coordinate of **dregg's own step proof**. So a
`CompleteAdd` in `Split_commitments.combine`'s fold, and an `EndoMul` ladder in `bullet_reduce`,
would read the same cell the sponge absorbed — a GATE READING IT, not a tape seeing it. The
theorems below exhibit that, slot by slot, at the committed shape.

✅ **AND THE VALUE LAYER NOW DOES TOO — CLOSED 2026-08-05.** `combPtVal`, `bullCipVal`, `bullLrVal`
and `bullDeltaVal` answered with `KimchiWrapMain.itemVal`, `PastaPoseidonFq`'s
`create_circuit(0,5)` proof, *regardless of which tape drove the `WrapData`* — invisible for
`tWrap`, because `schedule` absorbs `itemVal` and the two agreed by coincidence of source; for
`tChain` they DISAGREED, so an emitted `.combine` would have carried a fold whose accumulator was
computed from one proof's commitments over cells holding another's, and its honest witness would
have failed `CompleteAdd`. `KimchiWrapMainCore.absVal` is the repair — one function reading
`(sp.evs.filter (·.isAbs && ·.tag == tag)).word`, the value half of the very filter the `V` twins
use — and `prevEnv`'s `assert_on_curve` intermediates and `whSpongeP`'s tape were the same defect in
two more places. `bullLrVal`/`bullDeltaVal` took no `WrapData` AT ALL, which is what made this
structural rather than accidental: a nullary value function cannot follow a tape.
`the_consuming_rungs_values_are_the_chains_own_proof` states the agreement and
`…_are_no_longer_the_borrowed_proofs` states the disagreement with the fixture, so a "repair" that
moved both layers onto the fixture would red.

✅ **AND `rungsUpto .combine` CONTAINS `.key`, WHICH THIS TAPE NO LONGER FALSIFIES.** `keyRows`'
`digestTie` is a `Field.Assert.equal` joining the index sponge's squeeze to the transcript's FIRST
absorbed word. It squeezed the digest of Mina's `step-transaction` index while the chain's first
absorbed word is `STEP_VKDIGEST`, dregg's own step verifier index — so the honest witness failed
that row and no rung above `w4_bind` was emittable on this tape at all.

⚑ **THE FIX WAS NOT "MAKE THE STEP KEY REAL", AND THAT DISTINCTION COST A DAY.** `1687b7f61` DID
make it real — it replaced kimchi's degenerate `create_circuit(0,5)` test index (seven commitments
at infinity, an off-curve `lhs`, `bulletproof_success` with no witness) with o1-labs' released
`step-transaction` blob. That closed a different defect and left this row exactly as unsatisfiable
as it was: **a real key is not the RIGHT key.** What closes it is that `step_keys` is a per-branch
VECTOR of the compiled step rules' verification keys, so dregg's own rule takes an entry beside
Mina's and `choose_key` selects it — which is `choose_key`'s own mechanism and not a workaround for
it. Before this, the five-entry one-hot fold was decoration: `keySchedule` absorbed
`KEY_REAL_BRANCH`'s key whatever branch was selected, so W-KEY had a witness at branch 1 and nowhere
else. `KimchiWrapMainPins04.key_sponge_absorbs_the_selected_branch` is the pin that it no longer is.

⚑ **AND ONE FAMILY IS ABSORBED AND READ BY NOTHING, EVEN AT `w11_bullet`.** `t_comm`. §17's
`ft_comm` ladders run over `ftcTVal` — doublings of SRS Lagrange bases — in cells of their own; no
fold slot and no bullet input is a `T_TCOMM` absorbed cell, and the values are not equal either. So
`WRAP_UNCONSUMED`'s `t_comm` entry is not a bookkeeping leftover: it is the one commitment family
for which "absorbed" is still the whole story. -/

/-- The chain's absorbed word `i` of tag `tag` — its σ class, read off the EMITTED trace.
⚠ `KimchiPlacement.PVar` explicitly: this file's `open`s put a second `PVar` in scope and an
unqualified ascription is a type mismatch, not an ambiguity error. -/
def chainAbsV (tag i : Nat) : KimchiPlacement.PVar :=
  ((tChain.sp.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).wordV

/-- …and the value that class holds. -/
def chainAbsVal (tag i : Nat) : Nat :=
  ((tChain.sp.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).word

/-- **`chain_absorbed_cells_are_the_step_proofs_own_words`** — the premise everything below needs,
and it is not free: the trace's absorbed σ classes hold THIS step proof's tape, not a fixture's.
Without this the two theorems after it would be about cells that happen to be wired together. -/
theorem chain_absorbed_cells_are_the_step_proofs_own_words :
    chainAbsVal T_DIGEST 0 = STEP_VKDIGEST
    ∧ ((List.range (2 * shapeWrap.prevs)).all
        (fun i => chainAbsVal T_SGOLD i == STEP_PREVCOMM_XY.getD i 0)) = true
    ∧ ((List.range 2).all (fun i => chainAbsVal T_XHAT i == STEP_PUBCOMM_XY.getD i 0)) = true
    ∧ ((List.range (2 * shapeWrap.wComms)).all
        (fun i => chainAbsVal T_WCOMM i == STEP_WCOMM_XY.getD i 0)) = true
    ∧ ((List.range 2).all (fun i => chainAbsVal T_ZCOMM i == STEP_ZCOMM_XY.getD i 0)) = true
    ∧ ((List.range (2 * shapeWrap.tComms)).all
        (fun i => chainAbsVal T_TCOMM i == STEP_TCOMM_XY.getD i 0)) = true
    ∧ chainAbsVal T_CIP 0 = STEP_CIP_WORD_FQ := by
  native_decide

#assert_compiled chain_absorbed_cells_are_the_step_proofs_own_words

/-- **`chain_combine_would_fold_over_the_absorbed_cells`** — ⚑ W-COMBINE's 47-term fold, slot by
slot, at the committed shape: nineteen of its inputs ARE the transcript's own σ classes, driven by
this step proof. `combPtVar` allocates none of them (§23's own note), so this is a fact about the
emitted assembly and not about a name.

The three non-transcript families are named too, so the count is exhibited rather than asserted:
`ft_comm` is §17's output, and the twenty-seven index/coefficient/sigma slots are W-KEY's sealed
coordinates. -/
theorem chain_combine_would_fold_over_the_absorbed_cells :
    combTerms shapeWrap = 47
    ∧ ((List.range shapeWrap.prevs).all (fun p =>
        combPtVar tChain p == (chainAbsV T_SGOLD (2 * p), chainAbsV T_SGOLD (2 * p + 1)))) = true
    ∧ combPtVar tChain shapeWrap.prevs == (chainAbsV T_XHAT 0, chainAbsV T_XHAT 1)
    ∧ combPtVar tChain (shapeWrap.prevs + 2) == (chainAbsV T_ZCOMM 0, chainAbsV T_ZCOMM 1)
    ∧ ((List.range shapeWrap.wComms).all (fun j =>
        combPtVar tChain (shapeWrap.prevs + 3 + KEY_SINGLES + j)
          == (chainAbsV T_WCOMM (2 * j), chainAbsV T_WCOMM (2 * j + 1)))) = true
    ∧ combPtVar tChain (shapeWrap.prevs + 1) == ftcOutV shapeWrap tChain.sp := by
  native_decide

#assert_compiled chain_combine_would_fold_over_the_absorbed_cells

/-- **`chain_prev_on_curve_checks_the_absorbed_sg_old_cells`** — the consumer NEAREST to this file's
own rung, and the only one that is not a curve ladder. `w9_prev`'s `assert_on_curve` (three R1CS rows
per point, `wrap_main.ml:201-256`) squares and cubes `sgOldVar`, which is the transcript's own
`sg_old` σ class and not a second copy of it. So `sg_old` has TWO readers in the ladder — this and
W-COMBINE's fold — and both read the cell the sponge wrote. -/
theorem chain_prev_on_curve_checks_the_absorbed_sg_old_cells :
    ((List.range shapeWrap.prevs).all (fun p =>
        sgOldVar tChain p 0 == chainAbsV T_SGOLD (2 * p)
        && sgOldVar tChain p 1 == chainAbsV T_SGOLD (2 * p + 1))) = true := by
  native_decide

#assert_compiled chain_prev_on_curve_checks_the_absorbed_sg_old_cells

/-- **`chain_bullet_would_read_the_absorbed_cells`** — the same for W-BULLET: `combined_inner_product`
is `uc`'s scalar, the `2 · ipaRounds` `lr` points feed `bullet_reduce`'s 32 endo ladders, and `delta`
feeds `lhs`. Thirty-five σ classes, every one of them the transcript's own. -/
theorem chain_bullet_would_read_the_absorbed_cells :
    bullCipV tChain == chainAbsV T_CIP 0
    ∧ bullDeltaV tChain == (chainAbsV T_DELTA 0, chainAbsV T_DELTA 1)
    ∧ ((List.range shapeWrap.ipaRounds).all (fun r => (List.range 2).all (fun j =>
        bullLrV tChain r j
          == (chainAbsV T_LR (4 * r + 2 * j), chainAbsV T_LR (4 * r + 2 * j + 1))))) = true := by
  native_decide

#assert_compiled chain_bullet_would_read_the_absorbed_cells

/-- **`the_consuming_rungs_values_are_the_chains_own_proof`** — ⚑ **BLOCKER ONE, CLOSED 2026-08-05,
AND ITS PREDECESSOR FIRED ON THE WAY OUT.**

The theorem that stood here was `the_consuming_rungs_values_are_still_the_borrowed_proofs`, and it
said the opposite of this one: every `Val` above answered with `KimchiWrapMain.itemVal` — the
borrowed `create_circuit(0,5)` proof — *whatever tape drove the `WrapData`*, while its `V` twin read
`tChain`'s own σ class. Invisible for `tWrap`, because `schedule` absorbs `itemVal` and the two
agreed by coincidence of source; for `tChain` they DISAGREED, so a `.combine` emission would have
folded one proof's commitments over cells holding another's and failed `CompleteAdd`.

⚠ It was written to GO RED when the repair landed, and it did: the arity change on
`bullLrVal`/`bullDeltaVal` (they took no `WrapData` at all — which is what made the defect
structural rather than accidental) turned it into a type error, `#assert_compiled` caught the
resulting `sorryAx`, and the build refused. **That is the mechanism working, and it is why the
pin was worth writing.**

`KimchiWrapMainCore.absVal` is the repair: one function, reading `(sp.evs.filter (·.isAbs && ·.tag
== tag)).word`, which is the value half of the very filter the `V` twins use for the variable. Value
and variable are now ONE object for every `WrapData`, and this states that at every slot the census
names — including `x_hat`, which `schedule` absorbs as `s.xhatXY` and this tape absorbs as the step
proof's own public-input commitment. -/
theorem the_consuming_rungs_values_are_the_chains_own_proof :
    combPtVal tChain 0 = (chainAbsVal T_SGOLD 0, chainAbsVal T_SGOLD 1)
    ∧ combPtVal tChain (shapeWrap.prevs + 2) = (chainAbsVal T_ZCOMM 0, chainAbsVal T_ZCOMM 1)
    ∧ combPtVal tChain (shapeWrap.prevs + 3 + KEY_SINGLES)
        = (chainAbsVal T_WCOMM 0, chainAbsVal T_WCOMM 1)
    ∧ combPtVal tChain shapeWrap.prevs = (chainAbsVal T_XHAT 0, chainAbsVal T_XHAT 1)
    ∧ bullCipVal tChain = chainAbsVal T_CIP 0
    ∧ bullDeltaVal tChain = (chainAbsVal T_DELTA 0, chainAbsVal T_DELTA 1)
    ∧ bullLrVal tChain 0 0 = (chainAbsVal T_LR 0, chainAbsVal T_LR 1) := by
  native_decide

#assert_compiled the_consuming_rungs_values_are_the_chains_own_proof

/-- **`the_consuming_rungs_and_the_wrap_read_one_step_proof`** — ⚑⚑ **THIS REPLACED A CONTROL, AND
THE REPLACEMENT IS WHY, NOT A CLIMBDOWN.**

Its predecessor was `the_consuming_rungs_values_are_no_longer_the_borrowed_proofs`, whose whole
content was `combPtVal tChain ≠ itemVal …` — the chain's consuming rungs read a REAL step proof
while `itemVal` still answered with `PastaPoseidonFq`'s borrowed `create_circuit(0,5)` export. Its
docstring named the repair it was built to catch: *"a repair that made the two layers agree by
moving BOTH onto the fixture."*

⚠ **On 2026-08-05 it went red, and the repair that did it was the opposite one.** `itemVal` moved
onto **this pipeline's own step proof** — the same one this chain is about, and the one whose forty
public words the wrap statement must derive. The layers agree because there is now ONE step proof,
not because both were pushed onto a fixture. Restating the old inequality would have required
keeping a second proof alive purely so a control could stay green, which is the tail wagging the
dog; deleting it outright would have thrown away the check. So it is INVERTED and given the two
teeth the old one had by accident:

  * the six commitment tags agree **and** the tape is not the borrowed proof's
    (`STEP_PREVCOMM_XY ≠ PastaPoseidonFq.PREVCOMM_XY`), so "agree by both moving onto the fixture"
    is exactly what still goes red;
  * the two item tables still **differ at `T_XHAT`** — §15's 67-entry MSM output there, the
    public-input commitment kimchi absorbed here.

⚑⚑ **AND THE `T_DIGEST` LEG IS INVERTED SINCE 2026-08-06, FOR THE SECOND TIME AND THE SAME REASON.**
It used to require the two item tables to DISAGREE at `T_DIGEST`, because `RC_DIGEST` was Mina's
`step-transaction` key digest while this tape's first word is dregg's own step rule's. That
disagreement was never a property worth keeping: it was `keyRows`' `digestTie` having no satisfying
witness, written down as a control. `mkWrapWith` now selects `KEY_CHAIN_BRANCH`, so the wrap
assembly absorbs the digest of the key it committed to and the two tables agree.

⚠ The teeth are kept by naming the collapse that is still refused. `itemVal T_DIGEST 0` must NOT be
`STEP_VK_DIGEST` — a "repair" that moved the chain back onto Mina's key, or left the wrap on it,
reds here — and the branch the committed `WrapData` selects is stated rather than assumed. -/
theorem the_consuming_rungs_and_the_wrap_read_one_step_proof :
    combPtVal tChain 0 = (itemVal T_SGOLD 0, itemVal T_SGOLD 1)
    ∧ combPtVal tChain (shapeWrap.prevs + 2) = (itemVal T_ZCOMM 0, itemVal T_ZCOMM 1)
    ∧ bullCipVal tChain = itemVal T_CIP 0
    ∧ bullDeltaVal tChain = (itemVal T_DELTA 0, itemVal T_DELTA 1)
    ∧ combPtVal (mkWrap shapeWrap) 0 = (itemVal T_SGOLD 0, itemVal T_SGOLD 1)
    ∧ bullCipVal (mkWrap shapeWrap) = itemVal T_CIP 0
    ∧ bullDeltaVal (mkWrap shapeWrap) = (itemVal T_DELTA 0, itemVal T_DELTA 1)
    -- ⚑ they agree on a REAL proof, not on the borrowed one
    ∧ STEP_PREVCOMM_XY ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.PREVCOMM_XY
    ∧ STEP_WCOMM_XY ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.WCOMM_XY
    -- ⚑⚑ …and the two items that used to separate this tape from `KimchiWrapMain.schedule`'s are
    -- GONE, both of them, which is what collapsed the two assemblies into one. `T_DIGEST` is
    -- dregg's own step key's index digest on both sides and `T_XHAT` is the 67-entry MSM's output,
    -- which IS this proof's `public_comm`. The collapse that stays REFUSED is the other one:
    -- `itemVal T_DIGEST 0` must not be Mina's `step-transaction` digest, and the branch the
    -- committed `WrapData` selects is stated rather than assumed.
    ∧ (itemVal T_DIGEST 0 == STEP_VKDIGEST) = true
    ∧ (itemVal T_DIGEST 0 == STEP_VK_DIGEST) = false
    ∧ (mkWrap shapeWrap).br.idx = KEY_CHAIN_BRANCH
    ∧ chainXhatAbsorbed = [STEP_PUBCOMM_XY.getD 0 0, STEP_PUBCOMM_XY.getD 1 0] := by
  native_decide

#assert_compiled the_consuming_rungs_and_the_wrap_read_one_step_proof

/-- ⚑⚑ **AND `combined_inner_product` NOW AGREES ACROSS TWO IMPLEMENTATIONS — a fact that could not
even be STATED while the two layers were about different proofs.**

`itemVal T_CIP` is `STEP_CIP_WORD_FQ`: `tape.rs` takes **kimchi's own** `proof.oracles(...)`
`combined_inner_product` and applies `Shifted_value.Type1.of_field` (`shifted_value.ml:124-131`) in
Fp, then reinterprets it as one Fq wire (`impls.ml:196-201`, valid because `p < q`).

`itemVal T_CIP` is `MinaWrapDeferredWords.DEF_CIP`: slot 0 of `PreparedStatement::to_public_input(40)`,
which Pickles fills from **openmina's `expand_deferred`** (`proofs/step.rs:1915-2072`) — a different
codebase, reached through the statement rather than through the proof.

⚠ **Two implementations, one number, and `wrap_verifier.ml:395` absorbs it as ONE item.** This is
the single scalar that crosses Fp→Fq on this transcript, and it is the slot most likely to be got
wrong silently, because nothing on the wire carries it (`generated.rs:805-810`) and Pickles compares
its recomputation against nothing — a disagreement costs the PUBLIC INPUT, not a verdict. -/
theorem the_deferred_cip_is_kimchis_oracles_and_pickles_expand_deferred :
    STEP_CIP_WORD_FQ = Dregg2.Circuit.Emit.MinaWrapDeferredWords.DEF_CIP
    ∧ itemVal T_CIP 0 = STEP_CIP_WORD_FQ
    ∧ itemVal T_CIP 0 = Dregg2.Circuit.Emit.MinaWrapDeferredWords.DEF_CIP := by
  refine ⟨rfl, rfl, rfl⟩

/-- **`the_chain_climbs_past_bind_at_dreggs_own_step_key`** — ⚑⚑ **BLOCKER TWO, CLOSED 2026-08-05.
THE HEADLINE OF THIS FILE.**

Its predecessor, `the_chain_cannot_climb_past_bind_until_the_step_key_is_real`, said: `keyRows`'
closing `digestTie` puts the index sponge's squeeze and the transcript's FIRST absorbed word in one
σ class, `.key` is in `rungsUpto` of every rung above `w4_bind`, and here those two words were the
digests of **two different circuits** — so that single row, not W-COMBINE and not W-BULLET, was why
the chain stopped where it stopped.

⚠ **AND THE REASON IT KEPT BLOCKING IS NOT THE ONE THAT WAS EXPECTED.** The brief that opened this
work said the blocker had lifted because "the step key is now real" — `1687b7f61` replaced kimchi's
degenerate `create_circuit(0,5)` test index with o1-labs' released `step-transaction` blob. That is
true and it fixed a different defect (seven commitments at infinity, an off-curve `lhs`, a
`bulletproof_success` with no witness). It did NOT unblock this row, and measured, the theorem was
still TRUE: `keyDigestVal` was Mina's `step-transaction` digest and the tape's first word was
`stepmain_smoke_r8_finalize`'s. **A real key is not the same as the RIGHT key** — the wrap circuit
has to commit to the index of the very proof its transcript is verifying.

⚑ **WHAT ACTUALLY CLOSES IT.** `step_keys` is a per-branch VECTOR of the compiled step rules'
verification keys (`wrap_main.ml:98-101`), and `choose_key` one-hot selects from it. So dregg's own
step rule takes an entry — `KEY_CHAIN_BRANCH` — beside Mina's, and this `WrapData` selects it. The
56 coordinates come from `KimchiStepWrapChainKey`, written by the SAME binary, from the SAME
`VerifierIndex`, in the SAME run that wrote this file's tape: the preimage identity is by
construction, not by hygiene.

⚑ **AND `w5_key` IS THE FIRST RUNG THAT WAS EVER EMITTABLE ON A NON-`schedule` TAPE.** The last two
conjuncts say the rung PLACES and that its σ classes are sound at the committed shape, so "the tie
holds" is not a statement about two numbers with no circuit behind them. -/
theorem the_chain_climbs_past_bind_at_dreggs_own_step_key :
    (tChain.sp.evs.getD 0 default).word = STEP_VKDIGEST
    ∧ keyDigestVal shapeWrap tChain.sp tChain.br.idx = STEP_VKDIGEST
    ∧ tChain.br.idx = KEY_CHAIN_BRANCH
    ∧ (rungsUpto .combine).contains .key = true
    ∧ (rungsUpto .bullet).contains .key = true
    ∧ (rungsUpto .bind).contains .key = false
    ∧ (refusalOf shapeWrap .key (rungPub shapeWrap .key)
         (wrapGates (rungRows tChain .key true)) == none) = true
    ∧ regionEscape shapeWrap tChain.sp .key (wrapGates (rungRows tChain .key true)) = none := by
  native_decide

#assert_compiled the_chain_climbs_past_bind_at_dreggs_own_step_key

/-- **`the_chain_would_not_climb_at_any_other_step_key`** — ⚑ the RED CONTROL, and without it the
theorem above is one number agreeing with another. The `digestTie` row is a `Field.Assert.equal`, so
what "the chain climbs" MEANS is that the index sponge's squeeze equals the transcript's first word;
this says that holds at `KEY_CHAIN_BRANCH` and at NO OTHER branch of `step_keys` — including
`KEY_REAL_BRANCH`, Mina's `step-transaction` key, which is the branch the chain was pinned to until
today and the exact reason it stopped at `w4_bind`. -/
theorem the_chain_would_not_climb_at_any_other_step_key :
    ((List.range shapeWrap.branches).filter (fun i =>
        keyDigestVal shapeWrap tChain.sp i == (tChain.sp.evs.getD 0 default).word))
      = [KEY_CHAIN_BRANCH]
    ∧ keyDigestVal shapeWrap tChain.sp KEY_REAL_BRANCH ≠ STEP_VKDIGEST
    ∧ keyDigestVal shapeWrap tChain.sp KEY_REAL_BRANCH = STEP_VK_DIGEST
    ∧ STEP_VKDIGEST ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.VKDIGEST := by
  native_decide

#assert_compiled the_chain_would_not_climb_at_any_other_step_key

/-- **`the_chain_key_is_the_tapes_own_preimage`** — ⚑ the Lean-side re-derivation of what the Rust
exporter asserted before it wrote either module: absorbing exactly the 56 `index_to_field_elements`
coordinates of dregg's step index produces the digest that is the FIRST WORD of the phase-1 tape
`kimchi::verifier` ran on the accepted proof. Committing to those 56 numbers and absorbing that word
are one act.

⚠ The `.getD 0` leg is not decoration: it reads the tape's head off `chainTape` itself, so the
identity is against the object §3's reality gate consumes and not against a constant that happens to
sit beside it. -/
theorem the_chain_key_is_the_tapes_own_preimage :
    Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_DIGEST = STEP_VKDIGEST
    ∧ chainTape.getD 0 0 = STEP_VKDIGEST
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.length = KEY_COORDS
    ∧ (List.range KEY_COORDS).all (fun k =>
        keyConst KEY_CHAIN_BRANCH k
          == Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD k 0) = true := by
  native_decide

#assert_compiled the_chain_key_is_the_tapes_own_preimage

/-- **`the_chain_climbs_past_xhat_at_its_own_public_input_commitment`** — ⚑⚑ **BLOCKER THREE, CLOSED
2026-08-06, AND ITS PREDECESSOR WAS WRITTEN TO GO RED EXACTLY HERE.**

`the_chain_stops_at_xhat_because_the_msm_is_over_a_fixture` said: `xhatRows`' closing `caRowQ`
writes its OUTPUT into `xw` — the transcript's own absorbed `T_XHAT` σ classes — so the emitted
circuit CONSTRAINS the absorbed `x_hat` pair to equal `Ops.add_fast (negate (MSM fold))
Generators.h`; on a `schedule`-driven `WrapData` that holds by construction, and **on this tape it
did not**, because the fold ran over `xhatScalar i = prevWordVal (xhatWordOf i)`, a named fixture.
Its docstring closed with *"it goes RED when the MSM computes this proof's own public-input
commitment."* It does, and this is that.

⚑ **THE FIX WAS THE ONE THAT ROW NAMED, NOT A WAY AROUND IT.** The MSM runs over dregg's step
proof's own public input against the step SRS Lagrange basis at **this proof's domain** — and since
2026-08-06 that public input IS a packed `Types.Step.Statement`, so it is `wrap_verifier.ml:539-548`'s
own sixty-seven entries and not a side table. The `caRowQ` the row was about is satisfied by the
honest witness, so `w6_xhat` places and its σ classes are sound at the committed shape — the last two
conjuncts, which are what stop this being two numbers with no circuit behind them.

⚑⚑ **AND `w7_split` IS NO LONGER A CEILING AT ALL.** Until 2026-08-06 the blocker there was
STRUCTURAL: `splitRows` implements `split_field` (`wrap_main.ml:69-81`) on the packed words of a
`Types.Step.Statement` and dregg's step rule published twelve unconstrained `Fp` elements, so there
was no `split_field` to emit. `stepmain_step_r8_finalize` publishes the statement, both halves of
every `` `Field `` word are entries, and every rung from `.bind` to `.close` PLACES with no refusal
and no region escape. `the_chain_stops_at_the_statements_derived_words` is where the ceiling went. -/
theorem the_chain_climbs_past_xhat_at_its_own_public_input_commitment :
    chainXhatAbsorbed = [STEP_PUBCOMM_XY.getD 0 0, STEP_PUBCOMM_XY.getD 1 0]
    ∧ chainXhatAbsorbed = [shapeWrap.xhatXY.1, shapeWrap.xhatXY.2]
    ∧ shapeWrap.xhatXY = xhatOutOf shapeWrap.xhatEntries
    ∧ shapeWrap.xhatEntries.length = STEP_PUBLIC
    ∧ STEP_PUBLIC = XHAT_TERMS_FULL
    ∧ (rungsUpto .split).contains .xhat = true
    ∧ (rungsUpto .bullet).contains .xhat = true
    ∧ (rungsUpto .key).contains .xhat = false
    -- ⚑ the rung PLACES on this tape, and no gate escapes its region
    ∧ (refusalOf shapeWrap .xhat (rungPub shapeWrap .xhat)
         (wrapGates (rungRows tChain .xhat true)) == none) = true
    ∧ regionEscape shapeWrap tChain.sp .xhat (wrapGates (rungRows tChain .xhat true)) = none := by
  native_decide

#assert_compiled the_chain_climbs_past_xhat_at_its_own_public_input_commitment

/-- **`the_chain_stops_at_the_statements_derived_words`** — ⚑⚑ **THE NEW CEILING, AND IT IS THE
LAST ONE OF ITS KIND: SIX WORDS THE PUBLISHED STATEMENT DOES NOT CARRY.**

Every earlier blocker in this file was a WRONG OBJECT with a right one to be replaced by — a borrowed
proof's commitments, another circuit's verification key, an MSM over scalars belonging to nothing —
and each was replaced. `the_chain_stops_at_split_because_there_is_no_packed_statement` was the one
that had none: `w7_split` emits `split_field` over the packed words of a `Types.Step.Statement` and
dregg's step rule published twelve unconstrained `Fp` elements. **That is closed.**
`stepmain_step_r8_finalize` publishes the statement, and every rung from `.bind` to `.close` places
with no refusal and no region escape.

⚠⚑ **WHAT IS LEFT IS NOT A PLACEMENT AND NO PLACEMENT CHECK CAN SEE IT.** Three sub-circuits tie a
packed statement word to a value the wrap circuit COMPUTES — W-FINSPONGE's three deferred words,
W-WRAPHACK's two `hash_messages_for_next_wrap_proof` squeezes, W-PREV's `messages_for_next_step_
proof` — and the published statement carries synthetic words at all six. Those rows place, emit and
render; they have no satisfying WITNESS. `KimchiWrapMainField.the_published_statement_does_not_carry
_the_derived_words` names the six and `KimchiWrapMain.finsponge_has_no_witness_on_the_published
_statement` evaluates the assert that fails.

✅ ⚑⚑ **AND IT WAS PRICED AS A STEP-SIDE FIXPOINT, WHICH IS WHY IT DID NOT HAPPEN FOR A DAY.**
This paragraph read: *"Each of the six words is an x_hat MSM entry, so writing the derivation into
the statement moves `x_hat`, which moves every challenge below it, which moves the derivation.
Upstream Pickles closes that loop by construction; this pipeline has to bake it."* The first clause
is true and the inference does not follow. `whPrevDigest` reads no packed statement word
(`KimchiWrapMain.the_wraphack_tape_reads_no_published_statement_entry`), so it is computable before
the re-prove and unmoved by it — a STRATIFICATION, not a loop. MEASURED on 2026-08-06: the emit moved
exactly **two of the sixty-seven** entries, the re-prove cost 21.5 s, and 55/56 closed. What is left
at 27/28/37 and 54 is not this shape of thing; see `KimchiWrapMainField
.the_published_statement_carries_every_derived_word_but_the_arity_mismatched_one`.

⚠ The legs are the CLOSURE first — the statement is a real 57-word packed statement whose expansion
is the 67 entries — and then the blocker, exhibited on the one word this file owns the value of. -/
theorem the_chain_stops_at_the_statements_derived_words :
    STEP_PUBLIC = XHAT_TERMS_FULL
    ∧ ((List.range XHAT_TERMS_FULL).map xhatWordOf).eraseDups.length = PREV_WORDS
    ∧ PREV_WORDS = 57
    -- ✅ ⚑ …and the blocker that used to sit here is GONE: words 55 and 56 ARE the two squeezes
    -- `wrap_main.ml:340-348` computes for them, since `KimchiStepMainCore.stmtWrapMsgVal` and a
    -- re-prove on 2026-08-06. This conjunct read `≠` for one day; it is the direction this file
    -- should only ever move in.
    ∧ prevWordVal (PREV_MSG_NEXT_STEP + 1) = whPrevDigest 0
    ∧ prevWordVal (PREV_MSG_NEXT_STEP + 2) = whPrevDigest 1
    -- ⚠ …and what IS left, exhibited rather than described: word 54 is not Mina's slot 12. That is
    -- the step assembly's own segment-D squeeze against the marshaller's
    -- `MessagesForNextStepProof::hash()`, and the two hash preimages of different ARITY.
    ∧ prevWordVal PREV_MSG_NEXT_STEP
        ≠ Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 12 0
    ∧ (rungsUpto .prev).contains .split = true
    ∧ (rungsUpto .wraphack).contains .split = true := by
  native_decide

#assert_compiled the_chain_stops_at_the_statements_derived_words

/-! ⚑⚑ **THE AGREEMENT COUNT LIVES IN `KimchiWrapMainPins12`, NOT HERE, AND THIS NOTE IS THE
DELETION RATHER THAN A SECOND COPY.** A `the_emitted_forty_agree_with_minas_at_every_slot_but_twelve`
stood here for about an hour on 2026-08-06 — same subject, same `wrapPublicAt (mkWrap shapeWrap)
.close`, same `WRAP_PUBLIC_INPUT_MEASURED` — written by this lane while a sibling was writing
`the_forty_agree_but_for_the_arity_mismatched_slot` in §20b⁵. Two lanes measuring one thing in two
modules is the defect this whole campaign has been deleting, and the sibling's is the better
statement: it grades the set `{0..39} \ {11, 12}` rather than a total (so a lane CLOSING a slot does
not red the pin that tracks the closing), it normalises `Int → Fq` before comparing, and its
anti-vacuity leg counts the NONZERO agreements. **39 of 40; 29 of the 30 `wrap_main` reads or
checks; the one left is slot 12.** -/



/-- **`the_combine_and_bullet_families_are_not_what_blocks_them`** — ⚑ the complement, so the row
above is a DIAGNOSIS and not merely a blocker. Every commitment family W-COMBINE's 47-term fold and
W-BULLET's ladders read is, on this tape, the chain's own absorbed σ class holding the chain's own
value — variable AND value, since `absVal`. If `w6_xhat` were passed, nothing in those two rungs
would be reading a borrowed proof.

⚠ ⚑ **`x_hat` WAS THE EXCEPTION AND IS NOT ANY MORE, AND THE LAST CONJUNCT IS THE INVERSION.** It
read `combPtVal tChain shapeWrap.prevs ≠ shapeWrap.xhatXY` — the fold slot held the step proof's
commitment while the MSM that had to produce it ran over a fixture, so the two disagreed and the
disagreement was the blocker. They are one value now, which is `w6_xhat` closing. Written as an
equality against BOTH sources (the absorbed cell and the shape's memo) so a repair that moved either
one alone goes red. -/
theorem the_combine_and_bullet_families_are_not_what_blocks_them :
    ((List.range shapeWrap.prevs).all (fun p =>
        combPtVal tChain p == (chainAbsVal T_SGOLD (2 * p), chainAbsVal T_SGOLD (2 * p + 1)))) = true
    ∧ combPtVal tChain (shapeWrap.prevs + 2) = (chainAbsVal T_ZCOMM 0, chainAbsVal T_ZCOMM 1)
    ∧ ((List.range shapeWrap.wComms).all (fun j =>
        combPtVal tChain (shapeWrap.prevs + 3 + KEY_SINGLES + j)
          == (chainAbsVal T_WCOMM (2 * j), chainAbsVal T_WCOMM (2 * j + 1)))) = true
    ∧ bullCipVal tChain = chainAbsVal T_CIP 0
    ∧ ((List.range shapeWrap.ipaRounds).all (fun r => (List.range 2).all (fun j =>
        bullLrVal tChain r j
          == (chainAbsVal T_LR (4 * r + 2 * j), chainAbsVal T_LR (4 * r + 2 * j + 1))))) = true
    ∧ bullDeltaVal tChain = (chainAbsVal T_DELTA 0, chainAbsVal T_DELTA 1)
    ∧ combPtVal tChain shapeWrap.prevs = (chainAbsVal T_XHAT 0, chainAbsVal T_XHAT 1)
    ∧ combPtVal tChain shapeWrap.prevs = shapeWrap.xhatXY
    ∧ combPtVal tChain shapeWrap.prevs
        = (STEP_PUBCOMM_XY.getD 0 0, STEP_PUBCOMM_XY.getD 1 0) := by
  native_decide

#assert_compiled the_combine_and_bullet_families_are_not_what_blocks_them

/-- **`t_comm_is_absorbed_and_read_by_nothing`** — ⚑ the one commitment family for which
"absorbed, not consumed" is still the WHOLE story, and the census's `t_comm` entry is therefore not
a leftover. §17's `ft_comm` ladders run over `ftcTVal` — doublings of SRS Lagrange bases, in cells
`ftcTV` allocates — so no `T_TCOMM` σ class reaches a gate: not one of W-COMBINE's 47 fold slots,
and not W-BULLET's `lr`/`delta`/`cip` inputs. The value half is stated too, so this is not a claim
about names: the points the ladders multiply are not the points the sponge absorbed. -/
theorem t_comm_is_absorbed_and_read_by_nothing :
    ((List.range (combTerms shapeWrap)).all (fun k =>
        (List.range (2 * shapeWrap.tComms)).all (fun i =>
          (combPtVar tChain k).1 != chainAbsV T_TCOMM i
          && (combPtVar tChain k).2 != chainAbsV T_TCOMM i))) = true
    ∧ ((List.range shapeWrap.tComms).all (fun j =>
        ftcTV shapeWrap tChain.sp j != (chainAbsV T_TCOMM (2 * j), chainAbsV T_TCOMM (2 * j + 1))))
       = true
    ∧ ((List.range shapeWrap.tComms).all (fun j =>
        ftcTVal j != (chainAbsVal T_TCOMM (2 * j), chainAbsVal T_TCOMM (2 * j + 1)))) = true
    ∧ WRAP_UNCONSUMED_KEYS.getD 4 "" = "t_comm" := by
  native_decide

#assert_compiled t_comm_is_absorbed_and_read_by_nothing

/-! ## §10 — the renderer. Same JSON the pickles harnesses parse. -/

/-- ⚠ ⚑ **RUNG-EXPLICIT IN EVERY ARGUMENT.** This read `wrapWitness t p rows` and `wrapPublic t`
until 2026-08-04 — the rung-blind aliases §9a describes. After W-PREV those denoted `.prev`, so
`chainJson t .bind …` would have written `"public_input_size": 22` beside a 23-element
`"public_input"`, with a witness grid built from a different rung's environment than its gates.
`KimchiWrapMain.rungJson` was already rung-explicit; this is now the same shape. -/
def chainJson (t : WrapData) (k : Rung) (wired : Bool) (name : String) : String :=
  renderCircuit (wrapCircuit t k wired name)

/-! ⚠ NO `#assert_namespace_axioms` HERE, and the absence is the honest label. Every theorem above
rests on `Lean.ofReduceBool` — they are closed by compiled evaluation, not by the kernel — so a
namespace-wide axiom assertion would either fail or have to be weakened until it said nothing.
`#assert_compiled` under each theorem is the correct, weaker pin: it passes only if the proof rests
on a `native_decide` oracle and nothing worse, and it ERRORS on a kernel-clean proof, so it cannot
launder one downward. See `docs/GUARD-DISCIPLINE.md`. -/

end Dregg2.Circuit.Emit.KimchiStepWrapChain
