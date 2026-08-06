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
  (`KimchiWrapMain.KEY_CHAIN_BRANCH`) and `chainBranch` selects it.
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
claim about what `proof.oracles(...)` computed, and §15's 67 scalars are not any statement's words.

⚠ **RE-CHECKED 2026-08-04, AFTER W-PREV LANDED (`5269fa248`), AND THE OVERRIDE STAYS.** An earlier
draft of this paragraph said closing the gap was "W-PREV's job", and quoted the scalars as
`wrapFixtureQ 21 i / 7 % 2 ^ xhatBits i`. Both are stale. W-PREV has landed nine wrap rungs, and what
it supplied is the previous STEP statement's **SHAPE**, not its values: `KimchiWrapMainField` §15c′
derives the 57 packed words (`composition_types.ml:1453-1459`) and their expansion to §15a's 67
entries, pins each to the width `spec.ml:374-392` packs it at, boolean-constrains `should_finalize`,
and ties word 54 (`messages_for_next_step_proof`) to `w9_prev`'s 23rd public word. The VALUES are now
`xhatScalar i = prevWordVal (xhatWordOf i)`, i.e. `wrapFixtureQ 34 w` through an `x^9` mixer — still a
named fixture. And §15c now argues that is the FAITHFUL choice rather than a stand-in: upstream's 57
words are a FREE WITNESS, and "a named fixture" and "a free witness" are the same object. So this
override is not pending on any rung; it is what a reality gate about `proof.oracles(...)` requires,
permanently. §8b states it as a theorem. -/

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
* They DIFFER — so the override is real, not a relabelling, and §15's MSM is not an MSM over dregg's
  step statement. ⚠ W-PREV has LANDED (`5269fa248`) and this stays true: it gave those 67 entries the
  previous step statement's SHAPE (§1), not its values, which are still `prevWordVal`'s named
  fixture. `x_hat` remains on `KimchiWrapMain.WRAP_UNCONSUMED` for that reason.
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

/-- ⚑⚑ **THE BRANCH IS `KEY_CHAIN_BRANCH`, AND THAT IS WHAT MAKES THE CHAIN CLIMB.** `choose_key`
(`wrap_verifier.ml:189-204`) one-hot folds `step_keys` — `wrap_main.ml:98-101`'s per-branch vector of
the compiled STEP rules' verification keys — and `keyRows`' closing `digestTie` welds the resulting
index digest to the transcript's FIRST absorbed word. This tape's first word is
`STEP_VKDIGEST`, the verifier-index digest of `stepmain_smoke_r8_finalize`, so the branch this
`WrapData` selects has to be the one holding THAT rule's key. It is, and `KimchiWrapMainPins04`'s
`chain_step_rule_is_a_second_real_key` is where the key itself is pinned.

⚑ And the selection carries a second correction with it: `fz = widths.getD 2 = 2`, so
`Branch_data.proofs_verified` packs as `N2` (`[1,1]`, `Field.pack = 3`) rather than the `N1` the old
`min 1 (branches − 1)` produced — which is the honest value for a wrap whose step rule carries
`STEP_PREV_CHALLENGES = 2` accumulators and whose tape has two `sg_old` points on it. -/
def chainBranch : BranchData :=
  runBranch shapeChain KEY_CHAIN_BRANCH
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
said `(wrapPublic tChain).length = shapeChain.pubWords`, which W-PREV turned into `23 = 22`.
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
    ∧ ((wrapSlotsAt shapeChain .bind).filter (fun s => s != WRAP_SLOT_BRANCH_DATA)).all (fun s =>
        (wrapPublicAt tChainBent .bind).getD s 0 != (wrapPublicAt tChain .bind).getD s 0) = true
    -- ⚑ …and the ONE that does not move is `branch_data`, at Mina's slot 29.
    ∧ (wrapPublicAt tChainBent .bind).getD WRAP_SLOT_BRANCH_DATA 0
        = (wrapPublicAt tChain .bind).getD WRAP_SLOT_BRANCH_DATA 0
    ∧ (wrapSlotsAt shapeChain .bind).contains WRAP_SLOT_BRANCH_DATA = true
    -- …with its identity pinned to the VARIABLE, which is the point of the whole statement.
    ∧ slotVarAt tChain .bind WRAP_SLOT_BRANCH_DATA
        = some (branchVars shapeChain (baseBr shapeChain tChain.sp)).packed
    ∧ (exposedVars tChain).getD 21 PVAR_NOWHERE
        = (branchVars shapeChain (baseBr shapeChain tChain.sp)).packed := by
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
    (refusalOf shapeChain .bind (rungPub shapeChain .bind)
        (wrapGates (rungRows tChain .bind true)) == none) = true
    ∧ (placedOf shapeChain .bind (rungPub shapeChain .bind)
         (wrapGates (rungRows tChain .bind true))).length
       = WRAP_PRIMARY_LEN + (rungRows tChain .bind true).length
    ∧ inertSlotsAt shapeChain .bind
        (wrapGates (rungRows tChain .bind true)) = wrapInertOk shapeChain .bind := by
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
  ((chainRun.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).wordV

/-- …and the value that class holds. -/
def chainAbsVal (tag i : Nat) : Nat :=
  ((chainRun.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).word

/-- **`chain_absorbed_cells_are_the_step_proofs_own_words`** — the premise everything below needs,
and it is not free: the trace's absorbed σ classes hold THIS step proof's tape, not a fixture's.
Without this the two theorems after it would be about cells that happen to be wired together. -/
theorem chain_absorbed_cells_are_the_step_proofs_own_words :
    chainAbsVal T_DIGEST 0 = STEP_VKDIGEST
    ∧ ((List.range (2 * shapeChain.prevs)).all
        (fun i => chainAbsVal T_SGOLD i == STEP_PREVCOMM_XY.getD i 0)) = true
    ∧ ((List.range 2).all (fun i => chainAbsVal T_XHAT i == STEP_PUBCOMM_XY.getD i 0)) = true
    ∧ ((List.range (2 * shapeChain.wComms)).all
        (fun i => chainAbsVal T_WCOMM i == STEP_WCOMM_XY.getD i 0)) = true
    ∧ ((List.range 2).all (fun i => chainAbsVal T_ZCOMM i == STEP_ZCOMM_XY.getD i 0)) = true
    ∧ ((List.range (2 * shapeChain.tComms)).all
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
    combTerms shapeChain = 47
    ∧ ((List.range shapeChain.prevs).all (fun p =>
        combPtVar tChain p == (chainAbsV T_SGOLD (2 * p), chainAbsV T_SGOLD (2 * p + 1)))) = true
    ∧ combPtVar tChain shapeChain.prevs == (chainAbsV T_XHAT 0, chainAbsV T_XHAT 1)
    ∧ combPtVar tChain (shapeChain.prevs + 2) == (chainAbsV T_ZCOMM 0, chainAbsV T_ZCOMM 1)
    ∧ ((List.range shapeChain.wComms).all (fun j =>
        combPtVar tChain (shapeChain.prevs + 3 + KEY_SINGLES + j)
          == (chainAbsV T_WCOMM (2 * j), chainAbsV T_WCOMM (2 * j + 1)))) = true
    ∧ combPtVar tChain (shapeChain.prevs + 1) == ftcOutV shapeChain chainRun := by
  native_decide

#assert_compiled chain_combine_would_fold_over_the_absorbed_cells

/-- **`chain_prev_on_curve_checks_the_absorbed_sg_old_cells`** — the consumer NEAREST to this file's
own rung, and the only one that is not a curve ladder. `w9_prev`'s `assert_on_curve` (three R1CS rows
per point, `wrap_main.ml:201-256`) squares and cubes `sgOldVar`, which is the transcript's own
`sg_old` σ class and not a second copy of it. So `sg_old` has TWO readers in the ladder — this and
W-COMBINE's fold — and both read the cell the sponge wrote. -/
theorem chain_prev_on_curve_checks_the_absorbed_sg_old_cells :
    ((List.range shapeChain.prevs).all (fun p =>
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
    ∧ ((List.range shapeChain.ipaRounds).all (fun r => (List.range 2).all (fun j =>
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
    ∧ combPtVal tChain (shapeChain.prevs + 2) = (chainAbsVal T_ZCOMM 0, chainAbsVal T_ZCOMM 1)
    ∧ combPtVal tChain (shapeChain.prevs + 3 + KEY_SINGLES)
        = (chainAbsVal T_WCOMM 0, chainAbsVal T_WCOMM 1)
    ∧ combPtVal tChain shapeChain.prevs = (chainAbsVal T_XHAT 0, chainAbsVal T_XHAT 1)
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
  * the two item tables still **differ at `T_DIGEST` and `T_XHAT`**, which is the chain's override
    and the reason `tChain` is a different object from `mkWrap shapeChain` at all. `T_DIGEST` is
    Mina's `step-transaction` key digest in the wrap assembly (§14's `choose_key` anchor) and this
    proof's own index digest here; `T_XHAT` is §15's MSM output there and the public-input
    commitment kimchi absorbed here. A repair that collapsed the chain into the wrap would make
    those two agree, and this refuses it. -/
theorem the_consuming_rungs_and_the_wrap_read_one_step_proof :
    combPtVal tChain 0 = (itemVal T_SGOLD 0, itemVal T_SGOLD 1)
    ∧ combPtVal tChain (shapeChain.prevs + 2) = (itemVal T_ZCOMM 0, itemVal T_ZCOMM 1)
    ∧ bullCipVal tChain = itemVal T_CIP 0
    ∧ bullDeltaVal tChain = (itemVal T_DELTA 0, itemVal T_DELTA 1)
    ∧ combPtVal (mkWrap shapeChain) 0 = (itemVal T_SGOLD 0, itemVal T_SGOLD 1)
    ∧ bullCipVal (mkWrap shapeChain) = itemVal T_CIP 0
    ∧ bullDeltaVal (mkWrap shapeChain) = (itemVal T_DELTA 0, itemVal T_DELTA 1)
    -- ⚑ they agree on a REAL proof, not on the borrowed one
    ∧ STEP_PREVCOMM_XY ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.PREVCOMM_XY
    ∧ STEP_WCOMM_XY ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.WCOMM_XY
    -- ⚑ …and the chain's two OVERRIDES are still overrides
    ∧ (chainItemVal T_DIGEST 0 == itemVal T_DIGEST 0) = false
    ∧ ((List.range 2).all (fun i => chainItemVal T_XHAT i == itemVal T_XHAT i)) = false := by
  native_decide

#assert_compiled the_consuming_rungs_and_the_wrap_read_one_step_proof

/-- ⚑⚑ **AND `combined_inner_product` NOW AGREES ACROSS TWO IMPLEMENTATIONS — a fact that could not
even be STATED while the two layers were about different proofs.**

`chainItemVal T_CIP` is `STEP_CIP_WORD_FQ`: `tape.rs` takes **kimchi's own** `proof.oracles(...)`
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
    ∧ chainItemVal T_CIP 0 = STEP_CIP_WORD_FQ
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
    (chainRun.evs.getD 0 default).word = STEP_VKDIGEST
    ∧ keyDigestVal shapeChain chainRun chainBranch.idx = STEP_VKDIGEST
    ∧ chainBranch.idx = KEY_CHAIN_BRANCH
    ∧ (rungsUpto .combine).contains .key = true
    ∧ (rungsUpto .bullet).contains .key = true
    ∧ (rungsUpto .bind).contains .key = false
    ∧ (refusalOf shapeChain .key (rungPub shapeChain .key)
         (wrapGates (rungRows tChain .key true)) == none) = true
    ∧ regionEscape shapeChain chainRun .key (wrapGates (rungRows tChain .key true)) = none := by
  native_decide

#assert_compiled the_chain_climbs_past_bind_at_dreggs_own_step_key

/-- **`the_chain_would_not_climb_at_any_other_step_key`** — ⚑ the RED CONTROL, and without it the
theorem above is one number agreeing with another. The `digestTie` row is a `Field.Assert.equal`, so
what "the chain climbs" MEANS is that the index sponge's squeeze equals the transcript's first word;
this says that holds at `KEY_CHAIN_BRANCH` and at NO OTHER branch of `step_keys` — including
`KEY_REAL_BRANCH`, Mina's `step-transaction` key, which is the branch the chain was pinned to until
today and the exact reason it stopped at `w4_bind`. -/
theorem the_chain_would_not_climb_at_any_other_step_key :
    ((List.range shapeChain.branches).filter (fun i =>
        keyDigestVal shapeChain chainRun i == (chainRun.evs.getD 0 default).word))
      = [KEY_CHAIN_BRANCH]
    ∧ keyDigestVal shapeChain chainRun KEY_REAL_BRANCH ≠ STEP_VKDIGEST
    ∧ keyDigestVal shapeChain chainRun KEY_REAL_BRANCH = STEP_VK_DIGEST
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

/-- **`the_chain_stops_at_xhat_because_the_msm_is_over_a_fixture`** — ⚑⚑ **THE NEXT NAMED ROW, and it
is `w6_xhat`'s LAST one.** Stated as precisely as its two predecessors, and refutable the same way.

`xhatRows`' closing `caRowQ` writes its OUTPUT into `xw` — the transcript's own absorbed `T_XHAT` σ
classes — so the emitted circuit CONSTRAINS the absorbed `x_hat` pair to equal
`Ops.add_fast (negate (MSM fold)) Generators.h` (`wrap_verifier.ml:539-617`, the `x_hat blinding`).
On a `schedule`-driven `WrapData` that holds by construction, because `schedule` absorbs
`s.xhatXY = xhatOut s.xhatTerms` — the fold's own output. **On this tape it does not**, because §1's
override absorbs `STEP_PUBCOMM_XY`, the public-input commitment kimchi's verifier actually ran on,
and the fold is over `xhatScalar i = prevWordVal (xhatWordOf i)` — a NAMED FIXTURE.

⚑ **AND THIS IS A DIFFERENT KIND OF BLOCKER FROM THE KEY, WHICH IS WHY IT IS WORTH SEPARATING.** The
key was a wrong CONSTANT: the wrap circuit committed to another circuit's index, and giving
`step_keys` dregg's own entry fixed it with no new arithmetic. This one is a wrong FUNCTION. To make
`x_hat` the step proof's real public-input commitment the MSM has to run over dregg's step proof's
OWN public input against the step SRS Lagrange basis — `STEP_PUBLIC = 12` terms, not
`XHAT_TERMS_FULL = 67`, because 67 is Mina's `step-transaction` statement width and 12 is
`stepmain_smoke_r8_finalize`'s. So `shapeChain.xhatTerms = shapeWrap.xhatTerms` — §1's deliberate
copy — is itself the thing that has to go, and `chain_shape_is_the_measured_step_shape`'s
`shapeChain = shapeWrap` conjunct goes with it. That is correct rather than costly: a `WrapShape` for
verifying dregg's step rule genuinely has that rule's statement width.

⚠ **`.xhat` is in `rungsUpto` of `.split`, `.ftcomm`, `.prev`, `.combine` and `.bullet`**, so this
one row is the ceiling for all five — exactly as `.key` was the ceiling for everything above
`w4_bind`. The families W-COMBINE and W-BULLET would read (`z_comm`, 15 `w_comm`,
`combined_inner_product`, 32 `lr`, `delta`) are NOT what blocks them.

⚑ It goes RED when the MSM computes this proof's own public-input commitment. -/
theorem the_chain_stops_at_xhat_because_the_msm_is_over_a_fixture :
    chainXhatAbsorbed = [STEP_PUBCOMM_XY.getD 0 0, STEP_PUBCOMM_XY.getD 1 0]
    ∧ chainXhatAbsorbed ≠ [shapeChain.xhatXY.1, shapeChain.xhatXY.2]
    ∧ shapeChain.xhatXY = xhatOut shapeChain.xhatTerms
    ∧ shapeChain.xhatTerms = XHAT_TERMS_FULL
    ∧ XHAT_TERMS_FULL ≠ STEP_PUBLIC
    ∧ (rungsUpto .split).contains .xhat = true
    ∧ (rungsUpto .ftcomm).contains .xhat = true
    ∧ (rungsUpto .prev).contains .xhat = true
    ∧ (rungsUpto .combine).contains .xhat = true
    ∧ (rungsUpto .bullet).contains .xhat = true := by
  native_decide

#assert_compiled the_chain_stops_at_xhat_because_the_msm_is_over_a_fixture

/-- **`the_combine_and_bullet_families_are_not_what_blocks_them`** — ⚑ the complement, so the row
above is a DIAGNOSIS and not merely a blocker. Every commitment family W-COMBINE's 47-term fold and
W-BULLET's ladders read is, on this tape, the chain's own absorbed σ class holding the chain's own
value — variable AND value, since `absVal`. If `w6_xhat` were passed, nothing in those two rungs
would be reading a borrowed proof.

⚠ `x_hat` itself is the exception and is stated as one: its slot is the absorbed cell like the
others, but the cell's VALUE is the step proof's commitment while the fold that must produce it is
over a fixture — which is the row above, in the value layer. -/
theorem the_combine_and_bullet_families_are_not_what_blocks_them :
    ((List.range shapeChain.prevs).all (fun p =>
        combPtVal tChain p == (chainAbsVal T_SGOLD (2 * p), chainAbsVal T_SGOLD (2 * p + 1)))) = true
    ∧ combPtVal tChain (shapeChain.prevs + 2) = (chainAbsVal T_ZCOMM 0, chainAbsVal T_ZCOMM 1)
    ∧ ((List.range shapeChain.wComms).all (fun j =>
        combPtVal tChain (shapeChain.prevs + 3 + KEY_SINGLES + j)
          == (chainAbsVal T_WCOMM (2 * j), chainAbsVal T_WCOMM (2 * j + 1)))) = true
    ∧ bullCipVal tChain = chainAbsVal T_CIP 0
    ∧ ((List.range shapeChain.ipaRounds).all (fun r => (List.range 2).all (fun j =>
        bullLrVal tChain r j
          == (chainAbsVal T_LR (4 * r + 2 * j), chainAbsVal T_LR (4 * r + 2 * j + 1))))) = true
    ∧ bullDeltaVal tChain = (chainAbsVal T_DELTA 0, chainAbsVal T_DELTA 1)
    ∧ combPtVal tChain shapeChain.prevs = (chainAbsVal T_XHAT 0, chainAbsVal T_XHAT 1)
    ∧ combPtVal tChain shapeChain.prevs ≠ shapeChain.xhatXY := by
  native_decide

#assert_compiled the_combine_and_bullet_families_are_not_what_blocks_them

/-- **`t_comm_is_absorbed_and_read_by_nothing`** — ⚑ the one commitment family for which
"absorbed, not consumed" is still the WHOLE story, and the census's `t_comm` entry is therefore not
a leftover. §17's `ft_comm` ladders run over `ftcTVal` — doublings of SRS Lagrange bases, in cells
`ftcTV` allocates — so no `T_TCOMM` σ class reaches a gate: not one of W-COMBINE's 47 fold slots,
and not W-BULLET's `lr`/`delta`/`cip` inputs. The value half is stated too, so this is not a claim
about names: the points the ladders multiply are not the points the sponge absorbed. -/
theorem t_comm_is_absorbed_and_read_by_nothing :
    ((List.range (combTerms shapeChain)).all (fun k =>
        (List.range (2 * shapeChain.tComms)).all (fun i =>
          (combPtVar tChain k).1 != chainAbsV T_TCOMM i
          && (combPtVar tChain k).2 != chainAbsV T_TCOMM i))) = true
    ∧ ((List.range shapeChain.tComms).all (fun j =>
        ftcTV shapeChain chainRun j != (chainAbsV T_TCOMM (2 * j), chainAbsV T_TCOMM (2 * j + 1))))
       = true
    ∧ ((List.range shapeChain.tComms).all (fun j =>
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
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderWrapCircuit name p (p + rows.length)
    (placedOf t.sh k p (wrapGates rows)) (wrapWitnessAt t k p rows)
    (if p == 0 then [] else wrapPublicAt t k) (rungProbeRows t k)
    (if p == 0 then [] else wrapSlotsAt t.sh k) (if p == 0 then [] else wrapInertOk t.sh k)

/-! ⚠ NO `#assert_namespace_axioms` HERE, and the absence is the honest label. Every theorem above
rests on `Lean.ofReduceBool` — they are closed by compiled evaluation, not by the kernel — so a
namespace-wide axiom assertion would either fail or have to be weakened until it said nothing.
`#assert_compiled` under each theorem is the correct, weaker pin: it passes only if the proof rests
on a `native_decide` oracle and nothing worse, and it ERRORS on a kernel-clean proof, so it cannot
launder one downward. See `docs/GUARD-DISCIPLINE.md`. -/

end Dregg2.Circuit.Emit.KimchiStepWrapChain
