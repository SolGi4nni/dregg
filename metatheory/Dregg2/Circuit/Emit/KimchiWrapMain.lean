/-
# Dregg2.Circuit.Emit.KimchiWrapMain — `wrap_main`, assembled in Lean over **Fq**

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate list, the coefficients, the cross-gate placement and
the composed witness grid are authored here. `proof-systems` (tag 0.3.0) is the Rust PROVER that
RUNS the artifact and authors no constraint. House Law #1. No OCaml, no Node, no o1js in this path.

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiStepMain` assembles `step_verifier.verify_one` — the STEP side, over **Fp**, inner curve
Pallas. **This file is the WRAP side and nothing had touched it.** It is a DIFFERENT FIELD (Fq),
a DIFFERENT inner curve (Vesta), a DIFFERENT Poseidon instantiation (`pasta_q_kimchi`), a DIFFERENT
endomorphism constant (`Endo.Step_inner_curve.scalar`, not `Wrap_inner_curve`'s) and a DIFFERENT
public-input width (40, not 67). Nothing here is `KimchiStepMain` re-parameterised; this file shares
no definition with it, by construction, so a sibling's edit there cannot green or red anything here.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** a Mina-valid proof. The
kimchi proof the harness produces is an **INNER** Pallas/Fq proof of a `wrap_main`-SHAPED circuit.

## ⚑ THE SUBSTRATE FACTS, READ AT SOURCE (`~/dev/mina`)

  * `wrap_main_inputs.ml:11-12` — `module Me = Tock`, `module Impl = Impls.Wrap`. **The wrap circuit's
    native field is Tock.Field = Fq.** `read_wrap_circuit_field_element_as_hex` (`:29-33`) reads it
    through `Kimchi_backend.Pasta.Pallas_based_plonk`, i.e. a **Pallas-committed** proof, whose
    scalar field is Fq. So the harness proves over `Pallas`/`Fq`, where the step harness proves over
    `Vesta`/`Fp`.
  * `wrap_main_inputs.ml:14-15` — `sponge_params_constant = Sponge.Params.(map pasta_q_kimchi …)`.
    **The in-circuit transcript sponge is `fq_kimchi`**, which is `PastaPoseidonFq.fqParams`
    (`⟨qN, mdsQ, rcsQ⟩`, every constant emitted by `mina_poseidon::pasta::fq_kimchi::static_params()`).
    The Poseidon GATE COEFFICIENTS therefore differ from the step side's row for row — §0 emits
    `rcsQ`, and §11a pins that they are NOT `rcsN`.
  * `wrap_verifier.ml:45-49` — `Make (Inputs : … with type Impl.field = Backend.Tock.Field.t and type
    Inner_curve.Constant.Scalar.t = Backend.Tick.Field.t)`. A curve whose BASE field is Fq and whose
    SCALAR field is Fp is **Vesta**. The wrap circuit's inner curve is Vesta; the step circuit's is
    Pallas.
  * `wrap_verifier.ml:133-134` — `scalar_to_field s = SC.to_field_checked (module Impl) s
    ~endo:Endo.Step_inner_curve.scalar`, and `endo.ml:14-18` says
    `Step_inner_curve.scalar : Backend.Tock.Field.t = Pasta_bindings.Pallas.endo_scalar ()`.
    ⚑ **The wrap circuit lifts its scalar challenges by PALLAS's endo scalar, an Fq element** — the
    step circuit uses `Wrap_inner_curve.scalar = Vesta.endo_scalar ()`, an Fp element (`endo.ml:5-9`).
    Two different constants in two different fields; §11b pins ours against an INDEPENDENT source.

## ⚑ `wrap_main` MAPPED INTO NAMED SUB-CIRCUITS, FROM SOURCE

Read end to end at `~/dev/mina/src/lib/pickles/wrap_main.ml` (443 lines) and
`wrap_verifier.ml` (1073 lines). `wrap_main`'s `main` (`wrap_main.ml:135-440`) is:

  * **W-BRANCH** `wrap_main.ml:164-199`. `which_branch' = exists ~request:Req.Which_branch`, then
    `Wrap_verifier.One_hot_vector.of_index which_branch' ~length:branches`;
    `actual_proofs_verified_mask = Util.ones_vector ~first_zero:(Pseudo.choose (which_branch,
    step_widths) ~f:Field.of_int) Max_proofs_verified.n |> Vector.rev`;
    `domain_log2 = Pseudo.choose (which_branch, map step_domains ~f:(log2_size ∘ .h))`; then
    `Branch_data.Checked.pack { proofs_verified_mask = extend_front_exn … N2 false_; domain_log2 }
    |> Field.Assert.equal branch_data` — **the tie to wrap public word 29**. §9 emits this.
  * **W-KEY** `wrap_main.ml:215-220` → `wrap_verifier.ml:189-204`. `choose_key which_branch (map
    step_keys ~f:(Plonk_verification_key_evals.map ~f:Inner_curve.constant))` — a one-hot MSM over
    the per-branch STEP verification keys, `Vector.map2 … ~f:(fun b key → g * (b :> t))` reduced by
    `+` and `seal`ed. ⚠ **This is the line that makes wrap PER-ZKAPP rather than canonical**
    (`wrap_main.ml:98-101`, `step_keys : … Vector.t Lazy.t`), so Mina's two blobs are a reference
    implementation to conform to in SHAPE, not a byte target.
  * **W-PREV** `wrap_main.ml:201-256`. `prev_proof_state = exists ~request:Req.Proof_state` at the
    STEP proof-state typ with `~assert_16_bits:(Wrap_verifier.assert_n_bits ~n:16)`;
    `prev_step_accs = exists (Vector.typ Inner_curve.typ Max_proofs_verified.n)`;
    `old_bp_chals = exists … Req.Old_bulletproof_challenges` at `Backend.Tock.Rounds.n` per proof.
  * **W-FINALIZE** `wrap_main.ml:258-338` → `wrap_verifier.ml:820-1049`, run **once per previous
    proof**: a fresh `Sponge.create sponge_params` absorbing `sponge_digest_before_evaluations`,
    `Wrap_hack.Checked.pad_challenges`, then `finalize_other_proof` — the challenge digest, `ft_eval1`,
    the two public-input evaluations, the 43 columns in `to_absorption_sequence` order, the ξ′/r′
    squeezes, `actual_evaluation`, `Plonk_checks.scalars_env` at `~srs_length_log2:wrap_log2`,
    `ft_eval0`, `combined_evaluation`, `challenge_polynomial` for `b`, and `Plonk_checks.checked`
    over **`Scalars.Tock`** and **`Shifted_value.Type2`**. Closed by
    `Boolean.(Assert.any [finalized; not should_finalize])` (`wrap_main.ml:335`).
  * **W-WRAPHACK** `wrap_main.ml:340-355`. `Wrap_hack.Checked.hash_messages_for_next_wrap_proof`
    per previous proof over `{challenge_polynomial_commitment = sacc; old_bulletproof_challenges}`,
    and `Field.Assert.equal messages_for_next_step_proof prev_proof_state.messages_for_next_step_proof`.
  * **W-OPENINGS** `wrap_main.ml:357-383`. `openings_proof = exists (Openings.Bulletproof.typ …
    ~length:(Nat.to_int Backend.Tick.Rounds.n))` — ⚑ **Tick**, i.e. the STEP proof's IPA round count,
    with the scalars stored as `Shifted_value.Type1` over `Backend.Tick.Field` and `Shifts.tick1`.
  * **W-TRANSCRIPT** `wrap_verifier.ml:516-646`. The Fq sponge — §2b is this schedule, item by item.
    ⚑ It is an **`Opt_sponge`** (`wrap_main.ml:397` `Wrap_verifier.Opt.create sponge_params`,
    `wrap_verifier.ml:439-458`), where the step side's `incrementally_verify_proof` sponge is plain.
  * **W-XHAT** `wrap_verifier.ml:539-616`. `multiscale_known`'s wrap analogue, and it is NOT the same
    gadget: the public input is `[`Field of Field.t * Boolean.var | `Packed_bits of Field.t * int]`
    and each `` `Field (x,b) `` becomes **TWO** MSM entries — `(x, Field.size_in_bits)` as
    `Add_with_correction` via `Ops.scale_fast2' (module Other_field.With_top_bit0)` and
    `((b :> Field.t), 1)` as **`Cond_add`** via `Inner_curve.if_ b ~then_:(Ops.add_fast g acc)
    ~else_:acc` (`:573-577,599-609`). Constant words are partitioned out into `lagrange` /
    `scaled_lagrange` (`:550-565`) and folded into the `~init` alongside the corrections. Then
    `Inner_curve.negate` (`:610`) and `x_hat blinding` (`:612-616`).
  * **W-SPLIT** `wrap_main.ml:51-81`. `split_field x` — the `(hi, is_odd)` decomposition asserted by
    `Field.(Assert.equal ((of_int 2 * y) + (is_odd :> t)) x)`, with the hi-bit range check
    **deferred to `scale_fast2`** (`:64-68`, stated in upstream's own comment). Every STEP statement
    `Field` word passes through it; that is where the doubling of the MSM term count comes from.
  * **W-FTCOMM** `wrap_verifier.ml:655-666`. `Common.ft_comm` at
    `~scale:(scale_fast ~num_bits:Other_field.Packed.Constant.size_in_bits)`.
  * **W-COMBINE** `wrap_verifier.ml:320-379,667-713`. `Split_commitments.combine` over
    `Nat.N45.n + Max_proofs_verified.n` commitments — and unlike the step side it carries a
    `Curve_opt` mux (`keep`, `Point.Maybe_finite`, `Inner_curve.if_`) and closes with
    `Boolean.Assert.is_true non_zero` (`:377`).
  * **W-BULLET** `wrap_verifier.ml:383-437`. `check_bulletproof`: absorb `combined_inner_product`
    (⚑ **ONE field element** — `Other_field.Packed.absorb_shifted` at `:64-66` unwraps the
    `Shifted_value` and absorbs `x`; the step side absorbs field **and** bit because its
    `Other_field.Packed` is a pair), `u = group_map (Sponge.squeeze_field sponge)`, the combined
    polynomial, `bullet_reduce` over `Tick.Rounds.n` rounds, `absorb sponge PC delta`,
    `c = squeeze_scalar`, `lhs = Scalar_challenge.endo q c + delta`,
    `rhs = z_1·(G + b·u) + z_2·H`, `equal_g lhs rhs`.
  * **W-CLOSE** `wrap_main.ml:419-439` + `wrap_verifier.ml:717-731`. `Boolean.Assert.is_true
    bulletproof_success`; `Field.Assert.equal messages_for_next_wrap_proof_digest
    (Wrap_hack.Checked.hash_messages_for_next_wrap_proof …)`; `Field.Assert.equal
    sponge_digest_before_evaluations sponge_digest_before_evaluations_actual`; the per-round
    `Field.Assert.equal x1 x2` over `bulletproof_challenges_actual`; and `assert_eq_plonk` tying
    β/γ/α/ζ to the statement's `plonk` words.

## ⚑ WHAT THIS FILE ASSEMBLES TODAY — four rungs, and the rest named

  * **W1 `transcript`** — §4. The **Fq** Poseidon sponge of `wrap_verifier.ml:516-646` and
    `check_bulletproof`'s continuation, driven by the REAL upstream state machine
    (`PastaPoseidonFq.absorb1`/`squeeze1`, the transcription of `poseidon.rs:107-146`) rather than
    by a one-permutation-per-block model. ⚑ **That is strictly more faithful than the step side's
    R1**: at rate 2, β and γ come out of ONE permutation (γ reads lane 1 with no permutation), and
    a `z_comm` absorbed straight after a squeeze re-enters at lane 0 without permuting. §12a pins
    the whole derivation against `PastaPoseidonFq.fqPhase1` — β, γ, α′, ζ′ and the digest of a REAL
    Vesta-committed kimchi proof that `kimchi::verifier::verify` accepts.
  * **W2 `challenges`** — §5. `to_field_checked` over **Fq** (`scalar_challenge.ml:12-129`), the
    chained `EndoMulScalar` rows with `n₀=0, a₀=2, b₀=2` PINNED, the `lowest_128_bits`
    decomposition, `assert_128_bits hi` as a SECOND chain, and the closing lift
    `Field.(scale a endo + b)` at Pallas's endo scalar.
  * **W3 `branch`** — §9. `One_hot_vector.of_index`, `Pseudo.choose`, `Util.ones_vector`, and
    `Branch_data.Checked.pack` — the wrap-specific selection sub-circuit, `Generic` only.
  * **W4 `bind`** — §10. The closing ties: the wrap statement words this assembly DERIVES become
    public words through `placeChecked`, so a word no gate reads REFUSES.

## ⚑ MEASURED — the emitted ladder, and the shape oracle it is scored against

    rung             smoke rows   wrap rows   pub   what it is at source
    w1_transcript        246          818       0    wrap_verifier.ml:516-646 + :383-437
    w2_challenges        471         1407       0    scalar_challenge.ml:12-136
    w3_branch            489         1430       0    wrap_main.ml:164-199
    w4_bind              492         1441      22    wrap_main.ml:419-439 + :189-199

At the committed shape the transcript feeds **120 sponge items** and takes **23 squeezes**, of which
21 are 128-bit challenges (§2b is the item-by-item census).

`bridge/mina-zkapp/scripts/mina-canonical-circuit-oracle.mjs --circuit wrap-transaction` reports
**15,122 gates at PI 40**, histogram `Generic 3521 · Poseidon 2871 · Zero 2757 · EndoMul 2528 ·
VarBaseMul 2417 · EndoMulScalar 536 · CompleteAdd 492`; the devnet wrap VK's domain is 2^14 = 16,384,
so Mina's own emission has ~1,259 rows of headroom. `wrapmain-region-conformance.mjs` scores this
assembly against it, and the two verdicts that are not "absent" are:

  * **`Poseidon` — 61/61 instances, 100%**, the WHOLE 11-row permutation INCLUDING all fifteen round
    constants per row, matching a `wrap-transaction` class byte for byte. The Fq Poseidon gadget
    this file emits IS the one Snarky emits in Mina's own wrap circuit.
  * **`EndoMulScalar` — the BODY 42/42, the whole instance 0/42**, with the seam exactly three cells
    and both of them this file being STRICTER; §13 names them.

⚑ And the wrap side has a cross-check the step side never had: **`wrap-blockchain` is an
independently compiled `wrap_main`** and its non-Generic gate stream is byte-identical to
`wrap-transaction`'s (11,601 gates, same types, same coefficients), so every non-Generic conformance
fact is checked against both blobs.

⚠ **NOT ASSEMBLED, named by sub-circuit** (§13): W-KEY, W-PREV, W-FINALIZE, W-WRAPHACK,
W-OPENINGS, W-XHAT, W-SPLIT, W-FTCOMM, W-COMBINE, W-BULLET, and W-CLOSE's three curve-side asserts.
Each is a row-emitter this file does not have; none is a value this file fakes and calls derived.

## ⚑ THE SIX DEFECT CLASSES, CHECKED AS EMITTED (§12)

  1. **Free ladder seeds** — no curve ladder is emitted yet, so there is no `acc₀`/`n₀` to leave
     free. The `EndoMulScalar` chains DO have seeds and all three are pinned by `Generic` rows
     (§5, `tfcRowsQ`); §12c bends each and the row refuses.
  2. **Prover-chosen challenge decompositions** — BOTH halves of every `lowest_128_bits` are
     range-checked: the low half IS the `to_field_checked` chain, the high half gets its own
     (`util.ml:98` asserts `hi` unconditionally). §12d exhibits the forged split that a
     one-sided check admits and shows the high chain refusing it.
  3. **Absorbed-but-not-consumed words** — §2c is the CENSUS and it is honest: at this rung the
     transcript's commitment words are absorbed and **not yet consumed**, because W-XHAT/W-COMBINE
     are not assembled. `WRAP_UNCONSUMED` names every one; nothing is padded to make a count look
     closed.
  4. **Constants pinned against their own definitions** — §11b pins `ENDO_Q` against
     `MinaRealBlockTranscript.ENDO_R`, an INDEPENDENT module whose value is validated by
     `derived_zeta`/`derived_alpha` against a real block's challenge expansion. §11a pins the Fq
     Poseidon constants against `PastaPoseidonFq.rcsQ` AND asserts they differ from the Fp ones.
  5. **Fixtures standing for derived values** — §2d lists every fixture by name. The transcript's
     absorbed words are the REAL commitments of `PastaPoseidonFq`'s accepted Vesta proof wherever
     one exists (`PREVCOMM_XY`, `PUBCOMM_XY`, `WCOMM_XY`, `ZCOMM_XY`, `TCOMM_XY`); `index_digest`
     is that proof's own `VKDIGEST`. The `lr`/`delta` blocks have no real source in this tree and
     are named as fixtures rather than dressed up.
  6. **Wrong seed points** — no curve seed is emitted; the one seeded object is the
     `EndoMulScalar` accumulator triple and §12c is its red control.

## Axiom hygiene / build

NO `main` (roots into `PicklesSynthesis`; the emit driver is `EmitWrapMainJson.lean`). `#guard`s
reduce in the interpreter; no `sorry`/`native_decide`, no `decide` over the big grid.
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.MinaRealBlockTranscript
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate

namespace Dregg2.Circuit.Emit.KimchiWrapMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §0 — **Fq**, and the Fq gate constants.

Every value in this file lives mod `qN`. Nothing is shared with `KimchiStepMain`, which is mod `pN`;
a single `% pN` reaching this file would be a silent field confusion, so the arithmetic is defined
here and §11a/§11b pin the two constants that a copy-paste would get wrong. -/

/-- `x + y` over `Fq`. -/
def qAdd (x y : Nat) : Nat := (x + y) % qN
/-- `x − y` over `Fq`. -/
def qSub (x y : Nat) : Nat := (x + qN - y % qN) % qN
/-- `x · y` over `Fq`. -/
def qMul (x y : Nat) : Nat := (x * y) % qN

/-- ⚑ **`Endo.Step_inner_curve.scalar`** (`endo.ml:16`) — `Pasta_bindings.Pallas.endo_scalar ()`,
an element of `Backend.Tock.Field = Fq`, and the constant `to_field_checked` scales `a₈` by INSIDE
THE WRAP CIRCUIT (`wrap_verifier.ml:134,143`). ⚠ It is NOT the step side's
`Endo.Wrap_inner_curve.scalar`, which is an Fp element; §11b pins this against an independent
module rather than against its own definition. -/
def ENDO_Q : Nat :=
  26005156700822196841419187675678338661165322343552424574062261873906994770353

/-- Poseidon row `j`'s fifteen **Fq** round constants (five rounds × three lanes), from
`PastaPoseidonFq.rcsQ` = `mina_poseidon::pasta::fq_kimchi::static_params()`. The step side's
emitter reads `rcsN`; §11a pins that these are different elements. -/
def poseidonRowCoeffsQ (j : Nat) : List Int :=
  (List.range 5).flatMap (fun i => (rcsQ.getD (5 * j + i) []).map (fun n => (n : Int)))

/-- `c(x)` as an `Fq` element (`endomul_scalar.rs:303-309`): `0↦0 1↦0 2↦−1 3↦1`. -/
def cFuncQ (x : Nat) : Nat := if x == 2 then qN - 1 else if x == 3 then 1 else 0
/-- `d(x)` as an `Fq` element (`endomul_scalar.rs:311-317`): `0↦−1 1↦1 2↦0 3↦0`. -/
def dFuncQ (x : Nat) : Nat := if x == 0 then qN - 1 else if x == 1 then 1 else 0

/-! ## §1 — the shape.

Every field is a quantity `wrap_main` fixes. §8 sets them against the census in §2b/§2c. -/

structure WrapShape where
  /-- `Max_proofs_verified.n` — how many previous STEP proofs the wrap statement carries
  (`wrap_main.ml:103-104,180`). The devnet wrap VK says `prev_challenges = 2`. -/
  prevs : Nat
  /-- `Backend.Tick.Rounds.n` — the STEP proof's IPA round count, which is how many `(L,R)` pairs
  `bullet_reduce` absorbs and how many prechallenges it squeezes (`wrap_main.ml:381`,
  `wrap_verifier.ml:159-174`). -/
  ipaRounds : Nat
  /-- `Plonk_types.Columns.n` — the witness commitments absorbed at `wrap_verifier.ml:619`. -/
  wComms : Nat
  /-- `t_comm`'s quotient chunks, absorbed at `:630`. -/
  tComms : Nat
  /-- `EndoMulScalar` rows per `to_field_checked` chain; 8 is upstream's 128-bit width
  (`bits_per_row = 16`). -/
  emsRows : Nat
  /-- the one-hot length — `branches`, the number of STEP rules this wrap instance was compiled for
  (`wrap_main.ml:96,124`). ⚑ THIS is what makes wrap per-zkApp. -/
  branches : Nat
  /-- how many wrap statement words this assembly TIES. ⚠ Upstream's `PRIMARY_LEN` is
  `WRAP_PRIMARY_LEN = 40`; §10 carries the slot-by-slot census of which 40 and which of them this
  rung derives. Setting this to 40 with undERIVED words would be a public vector of fixtures. -/
  pubWords : Nat
  deriving Repr, Inhabited, DecidableEq

/-- ⚑ Mina's own wrap public-input width — `mina-canonical-circuit-oracle.mjs` reports
`public_input_size = 40` for both `wrap-transaction` and `wrap-blockchain`, and the devnet wrap VKs
say `public: 40`. Two independent sources. `MinaWrapPublicInput` carries the slot-by-slot layout. -/
def WRAP_PRIMARY_LEN : Nat := 40

/-! ## §2 — the transcript SCHEDULE, from source.

`wrap_verifier.ml:516-646` then `check_bulletproof` (`:383-437`), in upstream's own order. Each
entry is a SPONGE ITEM (one field element), not a block — §4 runs the real rate-2 state machine, so
where the permutations fall is DERIVED and not assumed. -/

/-- What a squeeze is for. -/
inductive SqKind where
  /-- a 128-bit challenge (`lowest_128_bits`): β, γ, α, ζ, the prechallenges, `c`. -/
  | chal
  /-- a FULL field squeeze that no `to_field_checked` consumes: `u`'s `group_map` input (`:403`). -/
  | full
  /-- ⚑ the FORK. `sponge_before_evaluations = Sponge.copy sponge` (`:645`) is taken BEFORE
  `sponge_digest_before_evaluations = Sponge.squeeze_field sponge` (`:646`), so the digest squeeze
  is a DEAD-END branch: `check_bulletproof` continues from the pre-digest state. Modelling it as
  an in-line squeeze would silently advance the transcript by one permutation. -/
  | fork
  deriving Repr, DecidableEq, Inhabited

/-- One sponge event. -/
inductive Ev where
  /-- absorb one field element, tagged with the item name it carries (§2c's census key). -/
  | abs (tag : Nat) (w : Nat)
  | sq (k : SqKind)
  deriving Repr, Inhabited

/-! ### §2b — **THE ITEM CENSUS**, `wrap_verifier.ml` line by line.

    :537  absorb sponge Field index_digest                        1 item
    :538  Vector.iter (absorb sponge PC) sg_old                    2·prevs
    :617  absorb sponge PC x_hat                                   2
    :619  Vector.iter absorb_g w_comm                              2·wComms
    :620  beta  = sample ()                                        squeeze (chal)
    :621  gamma = sample ()                                        squeeze (chal)
    :623  absorb_g z_comm                                          2
    :624  alpha = sample_scalar ()                                 squeeze (chal)
    :630  absorb_g t_comm                                          2·tComms
    :631  zeta  = sample_scalar ()                                 squeeze (chal)
    :645  sponge_before_evaluations = Sponge.copy sponge           (the FORK point)
    :646  sponge_digest_before_evaluations = squeeze_field sponge  squeeze (fork)
    :395  absorb_shifted sponge advice.combined_inner_product      1 item   ⚑ ONE, not two
    :403  t = Sponge.squeeze_field sponge  (u = group_map t)       squeeze (full)
    :414  bullet_reduce: per round  absorb (PC :: PC) gammas_i     4 items
                                    squeeze_scalar                 squeeze (chal)
    :420  absorb sponge PC delta                                   2
    :421  c = squeeze_scalar sponge                                squeeze (chal)

⚑ **`combined_inner_product` is ONE item here and TWO on the step side.** `wrap_verifier.ml:64-66`
`absorb_shifted sponge (Shifted_value x) = Sponge.absorb sponge x` — `Other_field.Packed.t` is
`Impls.Wrap.Other_field.t`, a single `Field.t`, because an Fp value fits in one Fq element. The step
side's `Other_field.Packed` is `(Field.t, Boolean.var)` and absorbs field THEN bit. Carrying the
step shape across would absorb a word `wrap_main` never feeds. -/

/-- Item TAGS, so §2c's census is by name and not by position. -/
def T_DIGEST : Nat := 0
def T_SGOLD : Nat := 1
def T_XHAT : Nat := 2
def T_WCOMM : Nat := 3
def T_ZCOMM : Nat := 4
def T_TCOMM : Nat := 5
def T_CIP : Nat := 6
def T_LR : Nat := 7
def T_DELTA : Nat := 8

/-- The REAL commitment coordinates of an accepted Vesta-committed kimchi proof, in Fq — the field
this circuit computes in and the field a STEP proof's commitments live in. `PastaPoseidonFq` §6
dumped them from `kimchi/examples/pickles_p6_fq_export.rs` off a `create_recursive` proof that
`kimchi::verifier::verify` ACCEPTS, and re-derives β/γ/α′/ζ′ from them (`fqPhase1`). §12a pins this
assembly's own sponge against that derivation. -/
def RC_SGOLD : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.PREVCOMM_XY
def RC_XHAT : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.PUBCOMM_XY
def RC_WCOMM : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.WCOMM_XY
def RC_ZCOMM : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.ZCOMM_XY
def RC_TCOMM : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.TCOMM_XY
/-- ⚑ …and the real proof's own verifier-index digest, which is `wrap_verifier.ml:537`'s first
absorbed item. Deriving it here would need W-KEY's one-hot fold over the per-branch step VKs
(`wrap_main.ml:215-220`), which §13 names as not assembled — so this is a FIXTURE, said plainly. -/
def RC_DIGEST : Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.VKDIGEST

/-! ### §2d — **THE FIXTURES, NAMED.**

`RC_SGOLD`/`RC_XHAT`/`RC_WCOMM`/`RC_ZCOMM`/`RC_TCOMM` and `RC_DIGEST` are a real accepted proof's
values, but they are FIXTURES in this circuit: no row here derives them, because the sub-circuits
that would (W-KEY for the digest, W-XHAT for `x_hat`) are not assembled. `lr`/`delta` have no real
source in this tree at all and get a deterministic filler, which is named here and nowhere pretends
to be a commitment. -/
def wrapFixture (tag i : Nat) : Nat := (11 + 1000003 * (17 * tag + i)) % qN

/-- Item `i` of tag `t`'s VALUE. -/
def itemVal (t i : Nat) : Nat :=
  match t with
  | 0 => RC_DIGEST
  | 1 => RC_SGOLD.getD i (wrapFixture 1 i)
  | 2 => RC_XHAT.getD i (wrapFixture 2 i)
  | 3 => RC_WCOMM.getD i (wrapFixture 3 i)
  | 4 => RC_ZCOMM.getD i (wrapFixture 4 i)
  | 5 => RC_TCOMM.getD i (wrapFixture 5 i)
  | _ => wrapFixture t i

/-- **THE EVENT LIST**, in `wrap_verifier.ml`'s own order. -/
def schedule (s : WrapShape) : List Ev :=
  [ Ev.abs T_DIGEST RC_DIGEST ]
  ++ (List.range (2 * s.prevs)).map (fun i => Ev.abs T_SGOLD (itemVal T_SGOLD i))
  ++ (List.range 2).map (fun i => Ev.abs T_XHAT (itemVal T_XHAT i))
  ++ (List.range (2 * s.wComms)).map (fun i => Ev.abs T_WCOMM (itemVal T_WCOMM i))
  ++ [ Ev.sq .chal, Ev.sq .chal ]                                   -- beta, gamma
  ++ (List.range 2).map (fun i => Ev.abs T_ZCOMM (itemVal T_ZCOMM i))
  ++ [ Ev.sq .chal ]                                                 -- alpha
  ++ (List.range (2 * s.tComms)).map (fun i => Ev.abs T_TCOMM (itemVal T_TCOMM i))
  ++ [ Ev.sq .chal ]                                                 -- zeta
  ++ [ Ev.sq .fork ]                                                 -- the digest, off-chain
  ++ [ Ev.abs T_CIP (itemVal T_CIP 0) ]                              -- ⚑ ONE item
  ++ [ Ev.sq .full ]                                                 -- u = group_map t
  ++ (List.range s.ipaRounds).flatMap (fun r =>
       (List.range 4).map (fun j => Ev.abs T_LR (itemVal T_LR (4 * r + j)))
       ++ [ Ev.sq .chal ])
  ++ (List.range 2).map (fun i => Ev.abs T_DELTA (itemVal T_DELTA i))
  ++ [ Ev.sq .chal ]                                                 -- c

/-- Absorbed ITEMS. -/
def nItems (s : WrapShape) : Nat := ((schedule s).filter (fun e => match e with | .abs _ _ => true | _ => false)).length
/-- Squeezes, of every kind. -/
def nSqueezes (s : WrapShape) : Nat := (schedule s).length - nItems s
/-- The squeezes a `to_field_checked` chain consumes — `chal` only. -/
def nChals (s : WrapShape) : Nat :=
  ((schedule s).filter (fun e => match e with | .sq .chal => true | _ => false)).length

/-! ### §2c — ⚑ **THE UNCONSUMED CENSUS, and it is NOT zero.**

The step side reached `UNWIRED_ITEMS = ∅` after eight rungs. This file is at rung four, and the
honest statement is that **every commitment word the transcript absorbs is absorbed and NOT YET
CONSUMED**, because the sub-circuits that consume them — W-XHAT (`x_hat`), W-COMBINE (`sg_old`,
`z_comm`, `w_comm`, `t_comm`), W-BULLET (`lr`, `delta`, `combined_inner_product`) — are §13's
named-and-not-assembled list. Padding the count, or wiring a commitment to a gadget that merely
re-reads it, is metric-gaming; the count is reported as it is. -/
def WRAP_UNCONSUMED : List String :=
  [ "index_digest — needs W-KEY (choose_key over the per-branch step VKs)"
  , "sg_old — needs W-COMBINE (~init of combine_split_commitments)"
  , "x_hat — needs W-XHAT (the Cond_add/Add_with_correction MSM)"
  , "w_comm — needs W-COMBINE"
  , "z_comm — needs W-COMBINE"
  , "t_comm — needs W-FTCOMM (Common.ft_comm's 8 scale_fast2s)"
  , "combined_inner_product — needs W-FINALIZE (the xi/r fold)"
  , "lr — needs W-BULLET (bullet_reduce's endo/endo_inv pairs)"
  , "delta — needs W-BULLET (lhs = Scalar_challenge.endo q c + delta)" ]

/-! ## §3 — the row-schedule primitives.

Deliberately this file's OWN copies. They are three lines each, and importing `KimchiStepMain` for
them would couple a wrap build to an Fp module two siblings are editing. -/

/-- One circuit row: gate `kind`, the `K_PERMUTS = 7` permutation-column variables (`none` =
unwired ⇒ `place` self-wires), the `coeffs`, and the ADVICE `(col, value)` placements. -/
structure WRow where
  kind : KGateType
  perm : List (Option PVar)
  coeffs : List Int := []
  advice : List (Nat × Int) := []
  /-- `true` only for the standalone `Zero` σ-only probes. -/
  probe : Bool := false
  deriving Repr, Inhabited

def noPerm : List (Option PVar) := List.replicate K_PERMUTS none

/-- A σ-ONLY PROBE: a standalone `Zero` row. A `Zero` gate reads nothing and no gate reads a probe
row, so a probe cell is constrained by the copy-permutation AND BY NOTHING ELSE. -/
def probeRow (wired : Bool) (a b : PVar) : WRow :=
  { kind := .zero
  , perm := if wired then [some a, some b, none, none, none, none, none] else noPerm
  , probe := true }

/-- The DOUBLE generic gate: half 1 is `c₀w₀+c₁w₁+c₂w₂+c₃w₀w₁+c₄ = 0` over cols 0,1,2; half 2 is
the same with `coeffs[5..9]` over cols 3,4,5 (`generic.rs:283-314`, read-only). -/
def genericRow (v0 v1 v2 v3 v4 v5 : Option PVar) (c : List Int) : WRow :=
  { kind := .generic, perm := [v0, v1, v2, v3, v4, v5, none], coeffs := c }

/-- `w₂ = w₀ + w₁`. -/ def cAdd : List Int := [1, 1, -1, 0, 0]
/-- `w₂ = w₀ · w₁`. -/ def cMul : List Int := [0, 0, -1, 1, 0]
/-- `w₀ = w₁`. -/ def cEq : List Int := [1, -1, 0, 0, 0]
/-- `w₀ = k`. -/ def cConst (k : Int) : List Int := [1, 0, 0, 0, -k]
/-- `w₀ = w₂ + 2^bits·w₁` — the `lowest_128_bits` decomposition. -/
def cSplit (bits : Nat) : List Int := [1, -((2 ^ bits : Nat) : Int), -1, 0, 0]
/-- `w₀·w₀ = w₀` — `Boolean.typ`'s own check, as one half over cols 0,1,2 with `w₁ = w₂ = w₀`. -/
def cBool : List Int := [1, 0, 0, -1, 0]
/-- An unused generic half. -/ def cNil : List Int := [0, 0, 0, 0, 0]

/-- Pack a list of `Generic` HALVES two to a row (Snarky's own double-generic filling). -/
def packHalves (hs : List (List (Option PVar) × List Int)) : List WRow :=
  let nil : List (Option PVar) × List Int := ([none, none, none], cNil)
  (List.range ((hs.length + 1) / 2)).map (fun r =>
    let h1 := hs.getD (2 * r) nil
    let h2 := if 2 * r + 1 < hs.length then hs.getD (2 * r + 1) nil else nil
    ({ kind := .generic, perm := h1.1 ++ h2.1 ++ [none]
     , coeffs := h1.2 ++ h2.2 } : WRow))

/-! ## §4 — W1, the **Fq** TRANSCRIPT SPONGE.

⚑ **THE STATE MACHINE IS UPSTREAM'S, NOT A BLOCK MODEL.** `PastaPoseidonFq.absorb1`/`squeeze1`
(`poseidon.rs:107-146`, transcribed there and proved equal to `PastaPoseidon.Ref` at Fp by
`core_is_Ref_at_Fp`) says:

  * absorbing into `Absorbed n` with `n = rate` PERMUTES first, then writes lane 0;
  * absorbing into `Squeezed _` writes lane 0 with NO permutation;
  * squeezing from `Squeezed n` with `n < rate` reads lane `n` with NO permutation.

So β and γ share one permutation, and `z_comm` re-enters at lane 0 without one. A
one-permutation-per-rate-2-block model gets both wrong, and it gets them wrong in the direction that
makes the transcript LOOK longer than it is.

Each permutation is eleven `Poseidon` rows plus the closing `Zero` row that holds the output state
(`KimchiRenderPoseidon`'s `round_to_cols = [0,2,3,4,1]`, read-only). Each absorb is one `Generic`
HALF `out = in + word`, and adjacent absorbs pack two to a row exactly as Snarky's double-generic
filling does. -/

/-- The 56 states of one Fq permutation, `s(0) = st` through `s(55)`, ONE round per step. -/
def permStatesQ (st : List Nat) : List (List Nat) :=
  (List.range 55).foldl
    (fun acc i =>
      acc ++ [Dregg2.Circuit.Emit.PastaPoseidonFq.Core.round fqParams (rcsQ.getD i []) (acc.getLastD st)])
    [st]

def stLane (ss : List (List Nat)) (k j : Nat) : Int := ((ss.getD k []).getD j 0 : Int)

/-- The eleven `Poseidon` rows + the closing `Zero` row of ONE Fq permutation. -/
def permBlockRowsQ (i0 i1 i2 o0 o1 o2 : PVar) (ss : List (List Nat)) : List WRow :=
  (List.range 11).map (fun r =>
    ({ kind := .poseidon
     , perm := if r == 0 then [some i0, some i1, some i2, none, none, none, none] else noPerm
     , coeffs := poseidonRowCoeffsQ r
     , advice :=
         (if r == 0 then [] else (List.range 3).map (fun j => (j, stLane ss (5 * r) j)))
         ++ (List.range 3).map (fun j => (3 + j, stLane ss (5 * r + 4) j))
         ++ (List.range 3).map (fun j => (6 + j, stLane ss (5 * r + 1) j))
         ++ (List.range 3).map (fun j => (9 + j, stLane ss (5 * r + 2) j))
         ++ (List.range 3).map (fun j => (12 + j, stLane ss (5 * r + 3) j)) } : WRow))
  ++ [ { kind := .zero, perm := [some o0, some o1, some o2, none, none, none, none] } ]

/-- One evaluated sponge event: what the machine did, which variables carry it, and the values. -/
structure SpEvt where
  isAbs : Bool
  kind : SqKind
  /-- the item TAG (absorbs only). -/
  tag : Nat
  /-- the absorbed word's VALUE. -/
  word : Nat
  /-- the absorbed word's own VARIABLE — one σ class per absorbed field element. -/
  wordV : PVar
  /-- did the machine permute before this event. -/
  didPerm : Bool
  /-- the lane written (absorb) or read (squeeze). -/
  lane : Nat
  inV : List PVar
  midV : List PVar
  outV : List PVar
  inN : List Nat
  midN : List Nat
  outN : List Nat
  /-- the 56 round states, when `didPerm`. -/
  ps : List (List Nat)
  /-- the squeezed VALUE and the variable it is read out of. -/
  val : Nat
  srcV : PVar
  deriving Repr, Inhabited

/-- The sponge region's variables are allocated in emission order from `base`. -/
structure SpAcc where
  evs : List SpEvt
  st : List PVar
  stN : List Nat
  /-- the upstream `Mode`, carried verbatim. -/
  mode : Dregg2.Circuit.Emit.PastaPoseidonFq.Mode
  next : Nat

instance : Inhabited SpAcc :=
  ⟨{ evs := [], st := [], stN := [], mode := .absorbed 0, next := 0 }⟩

/-- Fresh sponge variable. -/
private def fresh (base i : Nat) : PVar := .external (base + i)

/-- **THE TRAJECTORY.** One fold, driven by the upstream state machine; `bt`/`bw` override the
`bt`-th absorbed item's value so §12 can re-run the whole transcript on a prover's chosen word
rather than on a second copy of it. -/
def runSpongeQ (base : Nat) (evs : List Ev) (bt bw : Nat) : SpAcc :=
  let z : SpAcc :=
    { evs := [], st := [fresh base 0, fresh base 1, fresh base 2], stN := [0, 0, 0]
    , mode := .absorbed 0, next := 3 }
  (evs.zip (List.range evs.length)).foldl
    (fun a ei =>
      let rate := Dregg2.Circuit.Emit.PastaPoseidon.rate
      let doPerm : Bool :=
        match ei.1, a.mode with
        | .abs _ _, .absorbed n => n == rate
        | .abs _ _, .squeezed _ => false
        | .sq _, .squeezed n => n == rate
        | .sq _, .absorbed _ => true
      let ps := if doPerm then permStatesQ a.stN else []
      let midN := if doPerm then ps.getLastD a.stN else a.stN
      let midV := if doPerm then [fresh base a.next, fresh base (a.next+1), fresh base (a.next+2)]
                  else a.st
      let n1 := if doPerm then a.next + 3 else a.next
      match ei.1 with
      | .abs t w =>
        let ln : Nat := match a.mode with
          | .absorbed n => if n == rate then 0 else n
          | .squeezed _ => 0
        let wv := fresh base n1
        let ov := fresh base (n1 + 1)
        let outV := midV.set ln ov
        let outN := midN.set ln (qAdd (midN.getD ln 0) (if ei.2 == bt then bw else w))
        { evs := a.evs ++ [{ isAbs := true, kind := .chal, tag := t
                           , word := (if ei.2 == bt then bw else w), wordV := wv
                           , didPerm := doPerm, lane := ln
                           , inV := a.st, midV := midV, outV := outV
                           , inN := a.stN, midN := midN, outN := outN
                           , ps := ps, val := 0, srcV := ov }]
        , st := outV, stN := outN, mode := .absorbed (ln + 1), next := n1 + 2 }
      | .sq k =>
        let ln : Nat := match a.mode with
          | .squeezed n => if n == rate then 0 else n
          | .absorbed _ => 0
        let sq := midN.getD ln 0
        -- ⚑ THE FORK: the digest squeeze does NOT advance the transcript
        -- (`wrap_verifier.ml:645-646`), so the state and mode carried forward are the PRE-squeeze
        -- ones. Its permutation still costs its rows; its output feeds only the statement tie.
        let adv := k != SqKind.fork
        { evs := a.evs ++ [{ isAbs := false, kind := k, tag := 0, word := 0
                           , wordV := fresh base n1
                           , didPerm := doPerm, lane := ln
                           , inV := a.st, midV := midV, outV := midV
                           , inN := a.stN, midN := midN, outN := midN
                           , ps := ps, val := sq, srcV := midV.getD ln (fresh base n1) }]
        , st := if adv then midV else a.st
        , stN := if adv then midN else a.stN
        , mode := if adv then .squeezed (ln + 1) else a.mode
        , next := n1 })
    z

/-- **W1's ROWS.** The init pin, then per event: the permutation (when the machine took one) and
the absorb half. Adjacent absorb halves pack two to a `Generic` row. A σ-only probe is dropped after
every squeeze — the transcript's own boundary values. -/
def transcriptRowsQ (base : Nat) (d : SpAcc) (wired : Bool) : List WRow :=
  let init : List WRow :=
    [ genericRow (some (fresh base 0)) none none (some (fresh base 1)) none none
        (cConst 0 ++ cConst 0)
    , genericRow (some (fresh base 2)) none none none none none (cConst 0 ++ cNil) ]
  -- absorb HALVES are collected per contiguous run so `packHalves` fills the double gate.
  let rec go (es : List SpEvt) (pend : List (List (Option PVar) × List Int)) : List WRow :=
    match es with
    | [] => packHalves pend
    | e :: rest =>
      if e.isAbs then
        let half : List (Option PVar) × List Int :=
          ([ some (e.midV.getD e.lane (fresh base 0)), some e.wordV, some e.srcV ], cAdd)
        if e.didPerm then
          packHalves pend
          ++ permBlockRowsQ (e.inV.getD 0 (fresh base 0)) (e.inV.getD 1 (fresh base 1))
               (e.inV.getD 2 (fresh base 2)) (e.midV.getD 0 (fresh base 0))
               (e.midV.getD 1 (fresh base 1)) (e.midV.getD 2 (fresh base 2)) e.ps
          ++ go rest [half]
        else go rest (pend ++ [half])
      else
        packHalves pend
        ++ (if e.didPerm then
              permBlockRowsQ (e.inV.getD 0 (fresh base 0)) (e.inV.getD 1 (fresh base 1))
                (e.inV.getD 2 (fresh base 2)) (e.midV.getD 0 (fresh base 0))
                (e.midV.getD 1 (fresh base 1)) (e.midV.getD 2 (fresh base 2)) e.ps
            else [])
        ++ [ probeRow wired e.srcV (e.midV.getD 0 (fresh base 0)) ]
        ++ go rest []
  init ++ go d.evs []

/-- The sponge region's variable ENVIRONMENT. -/
def spongeEnv (base : Nat) (d : SpAcc) : VarEnv :=
  [ (fresh base 0, (0 : Int)), (fresh base 1, (0 : Int)), (fresh base 2, (0 : Int)) ]
  ++ d.evs.flatMap (fun e =>
      (if e.didPerm then (List.range 3).map (fun j => (e.midV.getD j (fresh base 0), (e.midN.getD j 0 : Int))) else [])
      ++ (if e.isAbs then
            [ (e.wordV, (e.word : Int))
            , (e.srcV, (e.outN.getD e.lane 0 : Int)) ]
          else []))

/-- The `chal` squeezes, in order: `(source variable, squeezed value)`. -/
def chalSqueezes (d : SpAcc) : List (PVar × Nat) :=
  (d.evs.filter (fun e => !e.isAbs && e.kind == SqKind.chal)).map (fun e => (e.srcV, e.val))

/-- ⚑ The FORK squeeze — `sponge_digest_before_evaluations` (`wrap_verifier.ml:646`). -/
def forkSqueeze (d : SpAcc) : Option (PVar × Nat) :=
  ((d.evs.filter (fun e => !e.isAbs && e.kind == SqKind.fork)).map (fun e => (e.srcV, e.val))).head?

/-! ## §5 — W2, CHALLENGE DERIVATION (`to_field_checked` over **Fq**).

`scalar_challenge.ml:12-129`. One `EndoMulScalar` row eats 8 crumbs and folds `n ↦ 4n + xⱼ`,
`a ↦ 2a + c(xⱼ)`, `b ↦ 2b + d(xⱼ)` from `n₀=0, a₀=2, b₀=2` (`endomul_scalar.rs:227-288`), the
column order is `[n0, n8, a0, b0, a8, b8, x₀..x₇, 0]`, cols 0..5 are all permutation columns so the
chain hops row→row through σ, and the chain closes with `Field.(scale a endo + b)` at `ENDO_Q`.

⚑ **DEFECT CLASS 2, CHECKED AS EMITTED.** `Util.lowest_128_bits` asserts the HIGH part
unconditionally and the low part when `~constrain_low_bits:true`; `wrap_verifier.ml:146-157` calls
it both ways (`squeeze_challenge` with `true`, `squeeze_scalar` with `false`). With only ONE part
constrained the decomposition row is one equation in two unknowns and a prover picks the challenge
(§12d). Both parts are emitted here for every challenge: the low part IS the `to_field_checked`
chain, the high part gets its own `assert_128_bits` chain, which `wrap_verifier.ml:136-144` shows is
literally `ignore (SC.to_field_checked … ~num_bits:n)` — the same rows. -/

def CHAL_BITS (s : WrapShape) : Nat := 16 * s.emsRows

/-- The `8·emsRows` base-4 crumbs of `v`, MSB-first. -/
def crumbsOfQ (s : WrapShape) (v : Nat) : List Nat :=
  (List.range (8 * s.emsRows)).map (fun j => v / 4 ^ (8 * s.emsRows - 1 - j) % 4)

/-- The `(n,a,b)` accumulator triples at every ROW boundary. -/
def emsAccsQ (s : WrapShape) (v : Nat) : List (Nat × Nat × Nat) :=
  let all := (crumbsOfQ s v).foldl
    (fun acc x =>
      let cur := acc.getLastD (0, 2, 2)
      acc ++ [((4 * cur.1 + x) % qN, (2 * cur.2.1 + cFuncQ x) % qN,
               (2 * cur.2.2 + dFuncQ x) % qN)])
    [(0, 2, 2)]
  (List.range (s.emsRows + 1)).map (fun k => all.getD (8 * k) (0, 2, 2))

/-- `a₈·endo + b₈` — `to_field_checked`'s closing line at `ENDO_Q`. -/
def liftValQ (s : WrapShape) (v : Nat) : Nat :=
  let a := (emsAccsQ s v).getD s.emsRows (0, 2, 2)
  qAdd (qMul a.2.1 ENDO_Q) a.2.2
def liftTValQ (s : WrapShape) (v : Nat) : Nat :=
  qMul ((emsAccsQ s v).getD s.emsRows (0, 2, 2)).2.1 ENDO_Q

/-- One `to_field_checked` chain's variable block. -/
structure ChainVars where
  n : Nat → PVar
  a : Nat → PVar
  b : Nat → PVar
  hi : PVar
  liftT : PVar
  lift : PVar

/-- Chain `c` of a region based at `base`, stride `chainStride`. -/
def chainStride (s : WrapShape) : Nat := 3 * (s.emsRows + 1) + 3
def chainVars (s : WrapShape) (base c : Nat) : ChainVars :=
  let b0 := base + c * chainStride s
  { n := fun k => .external (b0 + k)
  , a := fun k => .external (b0 + (s.emsRows + 1) + k)
  , b := fun k => .external (b0 + 2 * (s.emsRows + 1) + k)
  , hi := .external (b0 + 3 * (s.emsRows + 1))
  , liftT := .external (b0 + 3 * (s.emsRows + 1) + 1)
  , lift := .external (b0 + 3 * (s.emsRows + 1) + 2) }

/-- The pinned `endo` cell, shared by every chain (`Field.scale a endo`, one constant). -/
def vEndoQ (base : Nat) : PVar := .external base
def endoPinRow (base : Nat) : List WRow :=
  [ genericRow (some (vEndoQ base)) none none none none none (cConst (ENDO_Q : Int) ++ cNil) ]

/-- **`to_field_checked`'s rows.** `split = true` — the source is a full field element (a sponge
squeeze), so the tie is the `lowest_128_bits` decomposition `src = n₈ + 2^bits·hi`. `split = false`
— the source is already a `Challenge.t`, so the tie is `Field.Assert.equal n scalar` (`:124`). -/
def tfcRowsQ (s : WrapShape) (endoBase : Nat) (cv : ChainVars) (src : PVar) (split : Bool)
    (v : Nat) (wired : Bool) : List WRow :=
  let cr := crumbsOfQ s v
  [ genericRow (some (cv.n 0)) none none (some (cv.a 0)) none none (cConst 0 ++ cConst 2)
  , genericRow (some (cv.b 0)) none none none none none (cConst 2 ++ cNil) ]
  ++ (List.range s.emsRows).map (fun k =>
      ({ kind := .endoMulScalar
       , perm := [ some (cv.n k), some (cv.n (k+1)), some (cv.a k), some (cv.b k)
                 , some (cv.a (k+1)), some (cv.b (k+1)), none ]
       , advice := (List.range 8).map (fun j => (6 + j, (cr.getD (8 * k + j) 0 : Int)))
                   ++ [(14, 0)] } : WRow))
  ++ [ (if split then
          genericRow (some src) (some cv.hi) (some (cv.n s.emsRows)) none none none
                     (cSplit (CHAL_BITS s) ++ cNil)
        else
          genericRow (some (cv.n s.emsRows)) (some src) none none none none (cEq ++ cNil))
     , genericRow (some (cv.a s.emsRows)) (some (vEndoQ endoBase)) (some cv.liftT)
                  (some cv.liftT) (some (cv.b s.emsRows)) (some cv.lift) (cMul ++ cAdd)
     , probeRow wired (cv.n s.emsRows) (cv.a s.emsRows)
     , probeRow wired cv.lift (cv.b s.emsRows) ]

/-- A chain's variable environment at value `v`. -/
def chainEnv (s : WrapShape) (cv : ChainVars) (v hi : Nat) : VarEnv :=
  let accs := emsAccsQ s v
  (List.range (s.emsRows + 1)).flatMap (fun k =>
    let a := accs.getD k (0, 2, 2)
    [ (cv.n k, (a.1 : Int)), (cv.a k, (a.2.1 : Int)), (cv.b k, (a.2.2 : Int)) ])
  ++ [ (cv.hi, (hi : Int)), (cv.liftT, (liftTValQ s v : Int)), (cv.lift, (liftValQ s v : Int)) ]

/-! ## §9 — W3, the BRANCH SELECTION (`wrap_main.ml:164-199`).

⚑ This sub-circuit has no analogue on the step side at all, and it is the one that decides which
STEP verification key the whole rest of `wrap_main` runs against. Read at source, it is four things:

  * **`One_hot_vector.of_index which_branch' ~length:branches`** (`one_hot_vector.ml:22-25`):
    `Vector.init length ~f:(fun j => Field.equal (Field.of_int j) i)` then
    `Boolean.Assert.any`. ⚠ **`of_index` asserts ANY, not EXACTLY-ONE** — the `exactly_one` lives in
    `typ` (`:29-38`) and `wrap_main.ml:170-171` does not take that path; uniqueness follows from
    `Field.equal`'s determinism. §13 records that this file emits the STRICTER `Σ bᵢ = 1` and that
    the difference may not be claimed as fidelity.
  * **`Pseudo.choose (which_branch, xs) ~f:Field.of_int`** (`pseudo.ml:22-30`) — `Σ (bᵢ :> t)·xᵢ`,
    emitted twice: once over `step_widths` (the mask's `first_zero`) and once over the domains'
    `Domain.log2_size` (`domain.ml:19`). ⚠ With `~f:Field.of_int` the `xᵢ` are CONSTANTS, so
    `Checked.mul` takes its `Constant` branch (`utils.ml:81-88`) and upstream emits **zero rows**.
    This file emits the fold as rows; §13 records that too.
  * **`Util.ones_vector ~first_zero:k Max_proofs_verified.n |> Vector.rev`** (`util.ml:43-62`):
    `value ← value && not (Field.equal first_zero (Field.of_int i))`, i ascending, then reversed. ⚑
    **`Field.equal` is not free** — `utils.ml:44-48,65-79` allocates `(r, z_inv)` and asserts
    `z_inv·z = 1 − r` and `r·z = 0` with `r` boolean, two R1CS constraints per element. Those are
    emitted here, so the mask bits are DERIVED from `first_zero` rather than witnessed: a prover
    cannot claim a mask that does not follow from the branch he selected.
  * **`Branch_data.Checked.pack`** (`branch_data.ml:95-101`) — `4·domain_log2 + Field.pack (mask)`,
    LSB-first. ⚑ **The mask term is 0/2/3, not 0/1/2**: `Prefix_mask.there` is
    `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]` (`pickles_base/proofs_verified.ml:75-81`), which is
    exactly what `ones_vector ∘ rev` produces. §11c pins the packing against
    `MinaWrapPublicInput.branchDataPacked`, an independent transcription, and §11c exhibits all
    three legal widths.

⚠ **W-KEY is NOT emitted here.** `choose_key` (`wrap_verifier.ml:189-204`) is 28 commitments × 2
coordinates × `branches` multiplications and its output feeds `sponge_after_index`, i.e. the
transcript's FIRST absorbed word. Until it lands, `index_digest` is §2d's fixture and the one-hot
bits reach `branch_data` and nothing else — which is exactly what §2c says. -/

/-- `x^e` over `Fq`, binary exponentiation (the inverse `Field.equal` needs). -/
def qPow (x : Nat) : Nat → Nat
  | 0 => 1
  | (n + 1) =>
    let h := qPow (qMul x x) ((n + 1) / 2)
    if (n + 1) % 2 == 1 then qMul x h else h
decreasing_by simp_wf; omega

/-- `x⁻¹` over `Fq` by Fermat, `0` at zero — which is what Snarky's `Field.equal` witnesses when the
difference vanishes (the `r·z = 0` leg is what makes the value irrelevant there). -/
def qInv (x : Nat) : Nat := if x == 0 then 0 else qPow x (qN - 2)

/-- W3's variable block, based at `base`. -/
structure BranchVars where
  /-- one-hot bit `i`. -/
  bit : Nat → PVar
  /-- `Σ bᵢ` after `i+1` terms; the last is asserted `= 1`. -/
  accS : Nat → PVar
  /-- `Σ i·bᵢ` after `i+1` terms; the last IS `which_branch'`. -/
  accI : Nat → PVar
  /-- `Σ step_widthsᵢ·bᵢ`; the last IS `first_zero`. -/
  accW : Nat → PVar
  /-- `Σ log2_sizeᵢ·bᵢ`; the last IS `domain_log2`. -/
  accD : Nat → PVar
  which : PVar
  firstZero : PVar
  domainLog2 : PVar
  /-- `Field.equal`'s `z = first_zero − j`. -/
  zEq : Nat → PVar
  /-- …its witnessed inverse. -/
  invEq : Nat → PVar
  /-- …and its boolean result `[first_zero = j]`. -/
  rEq : Nat → PVar
  /-- `ones_vector`'s running `value` after element `j`. -/
  vv : Nat → PVar
  /-- `m₀ + 2·m₁` with `m = rev [vv 0, vv 1]`, i.e. `vv 1 + 2·vv 0`. -/
  maskPack : PVar
  /-- the packed `branch_data` word. -/
  packed : PVar

/-- `Max_proofs_verified.n` for the wrap statement — `ones_vector`'s length and the mask's width
(`wrap_main.ml:179-180`, `Nat.N2` at `:195`). -/
def MASK_N : Nat := 2

def branchVars (s : WrapShape) (base : Nat) : BranchVars :=
  let b := s.branches
  { bit := fun i => .external (base + i)
  , accS := fun i => .external (base + b + i)
  , accI := fun i => .external (base + 2 * b + i)
  , accW := fun i => .external (base + 3 * b + i)
  , accD := fun i => .external (base + 4 * b + i)
  , which := .external (base + 5 * b)
  , firstZero := .external (base + 5 * b + 1)
  , domainLog2 := .external (base + 5 * b + 2)
  , zEq := fun j => .external (base + 5 * b + 3 + j)
  , invEq := fun j => .external (base + 5 * b + 3 + MASK_N + j)
  , rEq := fun j => .external (base + 5 * b + 3 + 2 * MASK_N + j)
  , vv := fun j => .external (base + 5 * b + 3 + 3 * MASK_N + j)
  , maskPack := .external (base + 5 * b + 3 + 4 * MASK_N)
  , packed := .external (base + 5 * b + 4 + 4 * MASK_N) }

def nBranchVars (s : WrapShape) : Nat := 5 * s.branches + 5 + 4 * MASK_N

/-- `Util.ones_vector ~first_zero:k n` REVERSED: entry `j` is `1` iff `n − 1 − j < k`. Derived from
the `value ← value && ¬(k = i)` recurrence, and §11c pins the three legal packings it produces. -/
def maskBit (n k j : Nat) : Nat := if n - 1 - j < k then 1 else 0

/-- ⚑ `Branch_data.Checked.pack` (`branch_data.ml:95-101`): `4·domain_log2 + Field.pack mask`,
`Field.pack = project` LSB-first. §11c pins this against a REAL devnet Wrap proof's public word 29
rather than against a sibling transcription — two INDEPENDENT sources, one of them off the wire. -/
def branchDataPacked (pvBits domainLog2 : Nat) : Nat := pvBits + 4 * domainLog2

/-- The evaluated branch selection. -/
structure BranchData where
  idx : Nat
  widths : List Nat
  logs : List Nat
  fz : Nat
  dl : Nat
  m : List Nat
  packedV : Nat
  deriving Repr, Inhabited

def runBranch (_s : WrapShape) (idx : Nat) (widths logs : List Nat) : BranchData :=
  let fz := widths.getD idx 0
  let dl := logs.getD idx 0
  let m := (List.range MASK_N).map (fun j => maskBit MASK_N fz j)
  { idx := idx, widths := widths, logs := logs, fz := fz, dl := dl, m := m
  , packedV := branchDataPacked (m.getD 0 0 + 2 * m.getD 1 0) dl }

/-- `ones_vector`'s running `value` after element `j` — `vv j = ∏_{i≤j} ¬(fz = i)`. -/
def onesVal (fz j : Nat) : Nat :=
  (List.range (j + 1)).foldl (fun acc i => if fz == i then 0 else acc) 1

/-- **W3's rows.** Every one is a `Generic` half; `packHalves` fills the double gate. -/
def branchRows (s : WrapShape) (base : Nat) (d : BranchData) (wired : Bool) : List WRow :=
  let v := branchVars s base
  let b := s.branches
  -- the one-hot bits, each booleanity-constrained (`Vector.typ Boolean.typ`)
  let boolHalves : List (List (Option PVar) × List Int) :=
    (List.range b).map (fun i => ([some (v.bit i), some (v.bit i), some (v.bit i)], cBool))
  -- a weighted one-hot fold: `acc i = acc (i−1) + wᵢ·bᵢ`, `acc 0 = w₀·b₀`.
  let fold (acc : Nat → PVar) (w : Nat → Int) : List (List (Option PVar) × List Int) :=
    (List.range b).map (fun i =>
      if i == 0 then ([some (v.bit 0), none, some (acc 0)], [w 0, 0, -1, 0, 0])
      else ([some (acc (i - 1)), some (v.bit i), some (acc i)], [1, w i, -1, 0, 0]))
  let tie (x y : PVar) : List (Option PVar) × List Int := ([some x, some y, none], cEq)
  let eqHalves : List (List (Option PVar) × List Int) :=
    (List.range MASK_N).flatMap (fun j =>
      -- `z = first_zero − j`
      [ ([some v.firstZero, none, some (v.zEq j)], [1, 0, -1, 0, -(j : Int)])
      -- `r` boolean
      , ([some (v.rEq j), some (v.rEq j), some (v.rEq j)], cBool)
      -- `z_inv·z = 1 − r`  (`utils.ml:44-48`)
      , ([some (v.invEq j), some (v.zEq j), some (v.rEq j)], [0, 0, 1, 1, -1])
      -- `r·z = 0`
      , ([some (v.rEq j), some (v.zEq j), none], [0, 0, 0, 1, 0]) ])
  let onesHalves : List (List (Option PVar) × List Int) :=
    (List.range MASK_N).map (fun j =>
      if j == 0 then
        -- `value₀ = true ∧ ¬r₀ = 1 − r₀`
        ([some (v.rEq 0), none, some (v.vv 0)], [1, 0, 1, 0, -1])
      else
        -- `valueⱼ = value_{j−1}·(1 − rⱼ)`
        ([some (v.vv (j - 1)), some (v.rEq j), some (v.vv j)], [1, 0, -1, -1, 0]))
  packHalves
    (boolHalves
     ++ fold v.accS (fun _ => 1) ++ [ ([some (v.accS (b - 1)), none, none], cConst 1) ]
     ++ fold v.accI (fun i => (i : Int)) ++ [ tie (v.accI (b - 1)) v.which ]
     ++ fold v.accW (fun i => (d.widths.getD i 0 : Int)) ++ [ tie (v.accW (b - 1)) v.firstZero ]
     ++ fold v.accD (fun i => (d.logs.getD i 0 : Int)) ++ [ tie (v.accD (b - 1)) v.domainLog2 ]
     ++ eqHalves ++ onesHalves
     -- ⚑ `Vector.rev`: `proofs_verified_mask ! 0` is `vv (MASK_N−1)`, `! 1` is `vv 0`, so the
     -- LSB-first `Field.pack` is `vv 1 + 2·vv 0` — the 0/2/3 shape, not 0/1/2.
     ++ [ ([some (v.vv (MASK_N - 1)), some (v.vv 0), some v.maskPack], [1, 2, -1, 0, 0])
     -- `Branch_data.Checked.pack = 4·domain_log2 + mask`
        , ([some v.maskPack, some v.domainLog2, some v.packed], [1, 4, -1, 0, 0]) ])
  ++ [ probeRow wired v.packed v.domainLog2
     , probeRow wired (v.vv 0) v.which ]

def branchEnv (s : WrapShape) (base : Nat) (d : BranchData) : VarEnv :=
  let v := branchVars s base
  let b := s.branches
  let hit : Nat → Nat := fun i => if i == d.idx then 1 else 0
  let part : (Nat → Nat) → Nat → Int := fun w i =>
    (((List.range (i + 1)).foldl (fun acc k => acc + w k * hit k) 0 : Nat) : Int)
  (List.range b).flatMap (fun i =>
    [ (v.bit i, (hit i : Int))
    , (v.accS i, part (fun _ => 1) i)
    , (v.accI i, part (fun k => k) i)
    , (v.accW i, part (fun k => d.widths.getD k 0) i)
    , (v.accD i, part (fun k => d.logs.getD k 0) i) ])
  ++ (List.range MASK_N).flatMap (fun j =>
       let z := qSub d.fz j
       [ (v.zEq j, (z : Int)), (v.invEq j, (qInv z : Int))
       , (v.rEq j, (if z == 0 then 1 else 0 : Int))
       , (v.vv j, (onesVal d.fz j : Int)) ])
  ++ [ (v.which, (d.idx : Int)), (v.firstZero, (d.fz : Int)), (v.domainLog2, (d.dl : Int))
     , (v.maskPack, ((onesVal d.fz (MASK_N - 1) + 2 * onesVal d.fz 0 : Nat) : Int))
     , (v.packed, (d.packedV : Int)) ]

/-! ⚑ The derived mask IS `maskBit`, so §11c's packing pin and the emitted rows are about one
object. Checked at every legal `first_zero`. -/
#guard (List.range (MASK_N + 1)).all (fun k =>
  (List.range MASK_N).all (fun j => onesVal k (MASK_N - 1 - j) == maskBit MASK_N k j))

/-! ## §6 — the whole assembly: variable space, rows, environment, placement, witness. -/

/-- ⚑ The lowest `external` id the circuit allocates for itself. Public words are
`external 0 .. pubWords-1` (Snarky's own numbering), so `placeChecked`'s H1 cannot fire and its H2
— an inert public word — is the real gate on the closing rung. -/
def AUXW (s : WrapShape) : Nat := s.pubWords

def baseSp (s : WrapShape) : Nat := AUXW s
/-- the challenge region starts after the sponge; sized by the trace. -/
def baseCh (s : WrapShape) (sp : SpAcc) : Nat := baseSp s + sp.next
/-- chain region: `nChals` transcript chains + `nChals` `assert_128_bits hi` chains. -/
def baseBr (s : WrapShape) (sp : SpAcc) : Nat :=
  baseCh s sp + 1 + 2 * nChals s * chainStride s

/-- Everything the schedule and the environment read, evaluated ONCE. -/
structure WrapData where
  sh : WrapShape
  sp : SpAcc
  br : BranchData

instance : Inhabited WrapData := ⟨{ sh := default, sp := default, br := default }⟩

/-- The committed branch instance: index 1 of `branches`, widths `[0,1,2,…]`, domains all log2 16
(`Common.Max_degree.step_log2`). -/
def mkWrapWith (s : WrapShape) (bt bw : Nat) : WrapData :=
  { sh := s
  , sp := runSpongeQ (baseSp s) (schedule s) bt bw
  , br := runBranch s (min 1 (s.branches - 1))
            ((List.range s.branches).map (fun i => min 2 i))
            ((List.range s.branches).map (fun _ => 16)) }

def mkWrap (s : WrapShape) : WrapData := mkWrapWith s (nItems s + 1) 0

/-- W2's rows: the shared endo pin, then a `to_field_checked` chain per `chal` squeeze and an
`assert_128_bits` chain over each one's HIGH part. -/
def challengeRowsQ (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let cb := baseCh s t.sp
  let sq := chalSqueezes t.sp
  endoPinRow cb
  ++ (List.range (nChals s)).flatMap (fun c =>
      let e := sq.getD c (.external 0, 0)
      let lo := e.2 % 2 ^ CHAL_BITS s
      let hi := e.2 / 2 ^ CHAL_BITS s
      tfcRowsQ s cb (chainVars s (cb + 1) c) e.1 true lo wired
      ++ tfcRowsQ s cb (chainVars s (cb + 1) (nChals s + c)) (chainVars s (cb + 1) c).hi false hi wired)

def challengeEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let cb := baseCh s t.sp
  let sq := chalSqueezes t.sp
  [ (vEndoQ cb, (ENDO_Q : Int)) ]
  ++ (List.range (nChals s)).flatMap (fun c =>
      let e := sq.getD c (.external 0, 0)
      let lo := e.2 % 2 ^ CHAL_BITS s
      let hi := e.2 / 2 ^ CHAL_BITS s
      chainEnv s (chainVars s (cb + 1) c) lo hi
      ++ chainEnv s (chainVars s (cb + 1) (nChals s + c)) hi 0)

/-! ## §10 — W4, the CLOSING TIES, and the 40-word census.

⚑ **THE PUBLIC VECTOR IS THIS ASSEMBLY'S, NOT MINA'S, AND THE DIFFERENCE IS STATED.** Mina's wrap
circuits have `PRIMARY_LEN = WRAP_PRIMARY_LEN = 40`. `MinaWrapPublicInput` carries the slot-by-slot
layout, measured against a devnet block. Of those 40, this rung DERIVES:

    slot   word                                    here
    5–8    plonk.{alpha, beta, gamma, zeta}        ✅ the transcript's own four challenge squeezes,
                                                      which `assert_eq_plonk` (`wrap_verifier.ml:
                                                      717-731`) is exactly the tie for
    10     sponge_digest_before_evaluations        ✅ the FORK squeeze (`:646`), which
                                                      `wrap_main.ml:430-432` asserts equal
    13–28  bulletproof_challenges ×16              ✅ `bullet_reduce`'s own prechallenges, which
                                                      `wrap_main.ml:433-439` asserts equal one by one
    29     branch_data                             ✅ §9's `Branch_data.Checked.pack`
                                                      (`wrap_main.ml:189-199`)
    0–4    cip, b, ζ^srs_len, ζ^dom, perm          ✗ W-FINALIZE
    9      xi                                      ✗ W-FINALIZE
    11     messages_for_next_wrap_proof            ✗ W-WRAPHACK
    12     messages_for_next_step_proof            ✗ W-WRAPHACK / W-PREV
    30–39  padding + the lookup Opt's challenge    ✗ (constant / feature-flag words)

**22 of 40.** Exposing all 40 would mean tying 18 words to variables no row derives — public
fixtures, which is defect class 5 wearing a public vector. So `pubWords` is 22 and this table is
the census; §13 names what each missing word costs. -/

/-- The variables this assembly exposes as public words, in order. ⚑ Slot order here is THIS
circuit's; the census above maps each to Mina's slot. -/
def exposedVars (t : WrapData) : List PVar :=
  let s := t.sh
  let cb := baseCh s t.sp
  -- the four plonk challenges are the FIRST four `chal` squeezes (β, γ, α, ζ) — LIFTED, because
  -- `assert_eq_plonk` compares `Scalar_challenge.t` inners for α/ζ and raw challenges for β/γ, and
  -- the lift is what `map_challenges ~scalar` produces.
  (List.range 4).map (fun c => (chainVars s (cb + 1) c).lift)
  ++ [ (match forkSqueeze t.sp with | some e => e.1 | none => .external 0) ]
  ++ (List.range (min s.ipaRounds (nChals s - 5))).map (fun r =>
       (chainVars s (cb + 1) (4 + r)).lift)
  ++ [ (branchVars s (baseBr s t.sp)).packed ]
  |>.take s.pubWords

/-- One closing `Generic` half per public word: `external i = v`. This is the row that makes the
public word a READ one, so `placeChecked`'s `inertPublicWord` cannot fire silently. -/
def closingRows (t : WrapData) : List WRow :=
  packHalves ((List.range t.sh.pubWords).map (fun i =>
    (([ some (.external i : PVar), some ((exposedVars t).getD i (.external 0)), none
      ] : List (Option PVar)), cEq)))

/-! ## §7 — rows, environment, rungs. -/

inductive Rung where
  | transcript | challenges | branch | bind
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "w1_transcript" | .challenges => "w2_challenges"
  | .branch => "w3_branch" | .bind => "w4_bind"

/-- **THE ROW SCHEDULE**, in the order `wrap_main` runs it. Every sub-circuit's row-set function is
REACHED FROM HERE — a row-set that drops out of this `match` is a red in §12b, not a silence. -/
def rungRows (t : WrapData) (k : Rung) (wired : Bool) : List WRow :=
  let s := t.sh
  let a := transcriptRowsQ (baseSp s) t.sp wired
  let b := challengeRowsQ t wired
  let c := branchRows s (baseBr s t.sp) t.br wired
  let d := closingRows t
  match k with
  | .transcript => a
  | .challenges => a ++ b
  | .branch => a ++ b ++ c
  | .bind => a ++ b ++ c ++ d

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at it. -/
def rungPub (s : WrapShape) : Rung → Nat
  | .bind => s.pubWords
  | _ => 0

def circuitEnv (t : WrapData) : VarEnv :=
  spongeEnv (baseSp t.sh) t.sp ++ challengeEnv t ++ branchEnv t.sh (baseBr t.sh t.sp) t.br

/-- The full environment: the circuit's variables, then the public words, whose values are READ OUT
of the circuit env at the exposed variables — so a public word and the variable its closing row ties
it to hold ONE value by construction, exactly as a copy class does. -/
def wrapEnv (t : WrapData) : VarEnv :=
  let ce := circuitEnv t
  let ix := envIndex ce
  ce ++ (List.range t.sh.pubWords).map (fun i =>
    ((.external i : PVar), envLookupAt ix ((exposedVars t).getD i (.external 0))))

def wrapPublic (t : WrapData) : List Int :=
  let ix := envIndex (circuitEnv t)
  (List.range t.sh.pubWords).map (fun i =>
    envLookupAt ix ((exposedVars t).getD i (.external 0)))

def wrapGates (rows : List WRow) : List PGate :=
  rows.map (fun r => { kind := r.kind, permVars := r.perm, coeffs := r.coeffs })

/-- The composed 15 × `(pubSize + nRows)` witness grid. -/
def wrapWitness (t : WrapData) (pubSize : Nat) (rows : List WRow) : List (List Int) :=
  let ix := envIndex (wrapEnv t)
  let n := rows.length
  compose 15 (pubSize + n)
    (((List.range pubSize).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
     :: (rows.zip (List.range n)).map (fun ri =>
          gateVarWitnessAt ix (pubSize + ri.2)
            { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
          ++ ri.1.advice.map (fun cv => ((⟨pubSize + ri.2, cv.1⟩ : Cell), cv.2))))

/-- **THE FAIL-CLOSED PLACEMENT.** `placeChecked`, never `place`. -/
def placedOf (s : WrapShape) (pubSize : Nat) (gs : List PGate) : List PlacedGate :=
  match placeChecked ⟨pubSize, AUXW s⟩ gs with
  | .ok p => p
  | .error _ => []

def refusalOf (s : WrapShape) (pubSize : Nat) (gs : List PGate) : Option PlaceRefusal :=
  match placeChecked ⟨pubSize, AUXW s⟩ gs with
  | .ok _ => none
  | .error e => some e

/-- Rung `k`'s absolute probe rows, in schedule order. -/
def rungProbeRows (t : WrapData) (k : Rung) : List Nat :=
  let rows := rungRows t k true
  let p := rungPub t.sh k
  ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map (fun ri => p + ri.2)

/-! ### The renderer — the same JSON the pickles harnesses parse. -/

private def qs (s : String) : String := "\"" ++ s ++ "\""
private def renderCell (c : Cell) : String := "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"
private def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"
private def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => qs (toString i))) ++ "]"
private def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
private def renderGate (g : PlacedGate) : String :=
  "{" ++ qs "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ qs "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ qs "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"

def renderWrapCircuit (name : String) (pubSize numRows : Nat) (gs : List PlacedGate)
    (w : List (List Int)) (pub : List Int) (probes : List Nat) : String :=
  "{" ++ qs "name" ++ ":" ++ qs name ++ ","
       ++ qs "public_input_size" ++ ":" ++ toString pubSize ++ ","
       ++ qs "public_input" ++ ":" ++ renderIntList pub ++ ","
       ++ qs "num_rows" ++ ":" ++ toString numRows ++ ","
       ++ qs "probe_rows" ++ ":" ++ renderNatList probes ++ ","
       ++ qs "gates" ++ ":[" ++ String.intercalate "," (gs.map renderGate) ++ "],"
       ++ qs "witness" ++ ":[" ++ String.intercalate "," (w.map renderIntList) ++ "]}"

def rungJson (t : WrapData) (k : Rung) (wired : Bool) (name : String) : String :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderWrapCircuit name p (p + rows.length)
    (placedOf t.sh p (wrapGates rows)) (wrapWitness t p rows)
    (if p == 0 then [] else wrapPublic t) (rungProbeRows t k)

/-! ## §8 — the committed shape.

  * `prevs = 2` — the devnet wrap VK's `prev_challenges: 2`
    (`bridge/mina-zkapp/fixtures/mina-devnet-wrap-transaction-vk.json`).
  * `ipaRounds = 16` — `Backend.Tick.Rounds.n`, the STEP proof's IPA round count
    (`Common.Max_degree.step_log2 = 16`); `wrap_main.ml:381` sizes `openings_proof.lr` by it.
    ⚠ It is NOT 15; 15 is `Tock.Rounds.n`, which is what the STEP circuit's `verify_one` sees.
  * `wComms = 15`, `tComms = 7` — `Plonk_types.Columns.n` and
    `Commitment_lengths.create ~t:(of_int 7)`.
  * `emsRows = 8` — the 128-bit `to_field_checked` (`bits_per_row = 16`).
  * `branches = 5` — a wrap instance compiled for a five-rule step circuit. ⚑ There is no canonical
    value: `wrap_main` is per-zkApp (`wrap_main.ml:96-101`), which is the whole reason Mina's two
    blobs are a shape reference and not a byte target.
  * `pubWords = 22` — §10's census; upstream's `PRIMARY_LEN` is 40 and the 18-word gap is named
    there by sub-circuit. -/
def shapeWrap : WrapShape :=
  { prevs := 2, ipaRounds := 16, wComms := 15, tComms := 7, emsRows := 8
  , branches := 5, pubWords := 22 }

/-- A small shape for the in-CI `#guard`s (the committed one is emitted by the driver). -/
def shapeSmoke : WrapShape :=
  { prevs := 2, ipaRounds := 3, wComms := 3, tComms := 2, emsRows := 8
  , branches := 3, pubWords := 6 }


/-! ## §11 — the CONSTANT PINS, each against an INDEPENDENT source.

⚑ Defect class 4: "a constant pinned against its own definition is decoration; two INDEPENDENT
sources are a gate." Each pin below reads a value this file does not own.

### §11a — the Fq Poseidon constants.

The gate coefficients this file emits are `fq_kimchi`'s (`wrap_main_inputs.ml:12-13`,
`sponge/constants.ml:4011` `params_Pasta_q_kimchi`, 3×3 MDS and 55×3 round constants), NOT
`fp_kimchi`'s. A copy-paste of the step side's `rcsN` reds here, and so does a value that is not
reduced mod `qN`. -/

#guard poseidonRowCoeffsQ 0
       = (List.range 5).flatMap (fun i => (rcsQ.getD i []).map (fun n => (n : Int)))
#guard rcsQ.getD 0 [] != Dregg2.Circuit.Emit.PastaPoseidon.rcsN.getD 0 []
#guard mdsQ.getD 0 [] != Dregg2.Circuit.Emit.PastaPoseidon.mdsN.getD 0 []
#guard (poseidonRowCoeffsQ 0).length == 15
#guard (poseidonRowCoeffsQ 10).length == 15
#guard (poseidonRowCoeffsQ 0).all (fun c => decide (c ≥ 0) && decide (c < (qN : Int)))
#guard rcsQ.length == 55
#guard mdsQ.length == 3

/-! ### §11b — the endomorphism scalar.

`ENDO_Q` is `Endo.Step_inner_curve.scalar = Pasta_bindings.Pallas.endo_scalar ()` (`endo.ml:14-21`),
an element of `Backend.Tock.Field = Fq`, and `wrap_verifier.ml:134,143` is where the wrap circuit
scales `a₈` by it. `MinaRealBlockTranscript.ENDO_R` is the SAME Fq element arrived at independently
— the endo a real Mina Wrap proof's `ScalarChallenge::to_field` uses, validated THERE by
REPRODUCING that block's own α, ζ, v and u (`derived_alpha`, `derived_zeta`, `derived_v`,
`derived_u`). Two sources, one value.

⚠ ⚑ **AND GETTING IT BACKWARDS IS EASY, WHICH IS WHY BOTH DIRECTIONS ARE PINNED.**
`wrap_verifier.ml:121` instantiates the `Scalar_challenge` functor with **`Endo.Wrap_inner_curve`**
(Vesta's pair — `base ∈ Fq`, `scalar ∈ Fp`) for the in-circuit `endo`/`endo_inv` curve gadget, while
`:134` uses **`Endo.Step_inner_curve.scalar`** (Pallas's, in Fq) for `to_field_checked`. Two
different endos in one file, and only one of them is a scalar of this circuit's own field. -/

#guard (ENDO_Q : Nat) == (Dregg2.Circuit.Emit.MinaRealBlockTranscript.ENDO_R).val
-- …and it is NOT the step side's `Endo.Wrap_inner_curve.scalar`, which lives in Fp
-- (`bindings_js_test.ml:588-592`). Conflating the two is the `MinaWrapFtEval0Weld` defect, in the
-- direction nothing had tested.
#guard ENDO_Q != 8503465768106391777493614032514048814691664078728891710322960303815233784505
-- …nor `Endo.Wrap_inner_curve.base`, the Fq element `wrap_verifier.ml:944`/`:121` uses for the
-- CURVE endomorphism (`bindings_js_test.ml:583-587`). Both are Fq; only one is a scalar.
#guard ENDO_Q != 2942865608506852014473558576493638302197734138389222805617480874486368177743
-- It is a nontrivial cube root of unity in `Fq` — the property `endo_scalar` HAS
-- (`poly-commitment/src/srs.rs:44-60`), checked rather than assumed.
#guard qMul (qMul ENDO_Q ENDO_Q) ENDO_Q == 1
#guard ENDO_Q != 1

/-! ### §11c — `Branch_data.Checked.pack`.

`branch_data.ml:95-101`: `pack = 4·domain_log2 + Impl.Field.pack (Vector.to_list
proofs_verified_mask)`, where `Field.pack` is `project`, LSB-first. ⚑ **The mask term is 0/2/3, not
0/1/2**, because `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`
(`pickles_base/proofs_verified.ml:75-81`) and `wrap_main.ml:172-180` builds it as
`ones_vector ~first_zero:w |> Vector.rev = [w>1; w>0]`. §9's `maskBit` is that. -/

-- ⚑ **THE INDEPENDENT SOURCE IS A REAL DEVNET WRAP PROOF'S OWN PUBLIC WORD 29.**
-- `MinaWrapPublicCommGate.PUBLIC_INPUT` is the forty Fq words of a Mina devnet block's Wrap proof,
-- decoded off the wire; slot 29 IS `branch_data`. That block was proved at `proofs_verified = N2`
-- (mask `[tt;tt]`, packing to 3) over a `domain_log2 = 16` step domain, so
-- `Branch_data.Checked.pack` must give `3 + 4·16 = 67` — and it does, which is what makes this a
-- gate rather than a constant agreeing with itself.
#guard Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0 == 67
#guard branchDataPacked 3 16 == Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
-- …and the emitter's own value at that instance agrees.
#guard (runBranch shapeSmoke 2 [0,1,2] [16,16,16]).packedV
       == Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
-- ⚑ THE 0/2/3 SHAPE, exhibited at all three legal widths. A `[1;0]` mask — the packing `0/1/2`
-- would produce — is NOT reachable from `ones_vector ∘ rev`, which is exactly why
-- `Prefix_mask.back` can `invalid_arg` on it out of circuit and no gate refuses it in one.
#guard (List.range 3).map (fun w => maskBit 2 w 0 + 2 * maskBit 2 w 1) == [0, 2, 3]
#guard (runBranch shapeSmoke 0 [0,1,2] [16,16,16]).packedV == 64
#guard (runBranch shapeSmoke 1 [0,1,2] [16,16,16]).packedV == 66

/-! ### §11d — the field itself.

A wrap emission whose values were reduced mod `pN` would be accepted by nothing; this is the
tripwire that says which field the file is in. -/

#guard qN != pN
#guard qAdd (qN - 1) 1 == 0
#guard qMul (qN - 1) (qN - 1) == 1
#guard qSub 0 1 == qN - 1

/-! ## §12 — the in-CI PINS on the smoke instance (`#guard`, interpreter-reduced).

Nullary `def`s so the interpreter evaluates the chains ONCE. -/

def tW : WrapData := mkWrap shapeSmoke
def rowsW : List WRow := rungRows tW .bind true
def rowsUW : List WRow := rungRows tW .bind false
def nRowsW : Nat := rowsW.length
def gatesW : List PGate := wrapGates rowsW
def placedW : List PlacedGate := placedOf shapeSmoke shapeSmoke.pubWords gatesW
def gridW : List (List Int) := wrapWitness tW shapeSmoke.pubWords rowsW

/-! ### §12a — ⚑ **THE REALITY GATE: this file's sponge IS upstream's.**

`PastaPoseidonFq.fqPhase1` re-derives β, γ, α′, ζ′ and the phase-1 digest of a REAL Vesta-committed
kimchi proof that `kimchi::verifier::verify` ACCEPTS, from the verifier-index digest and the
commitments. If `runSpongeQ`'s state machine is upstream's, driving it on THAT tape reproduces THAT
tuple exactly — including where the permutations fall, since a single misplaced one changes every
value below it. This is a cross-source check on the transcript machinery itself, not on a value
this file chose. -/

/-- The real proof's absorb/squeeze schedule (`verifier.rs:159-283`): the tape, β, γ, `z_comm`, α′,
`t_comm`, ζ′, digest. -/
def realTapeSchedule : List Ev :=
  (Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape).map (fun w => Ev.abs T_WCOMM w)
  ++ [ Ev.sq .chal, Ev.sq .chal ]
  ++ (Dregg2.Circuit.Emit.PastaPoseidonFq.ZCOMM_XY).map (fun w => Ev.abs T_ZCOMM w)
  ++ [ Ev.sq .chal ]
  ++ (Dregg2.Circuit.Emit.PastaPoseidonFq.TCOMM_XY).map (fun w => Ev.abs T_TCOMM w)
  ++ [ Ev.sq .chal, Ev.sq .full ]

def realRun : SpAcc := runSpongeQ 0 realTapeSchedule 99999 0
/-- β, γ, α′, ζ′ — the four `chal` squeezes, low 128 bits. -/
def realChals : List Nat := (chalSqueezes realRun).map (fun e => e.2 % 2 ^ 128)
/-- the phase-1 digest — the FULL squeeze. -/
def realDigest : Nat :=
  ((realRun.evs.filter (fun e => !e.isAbs && e.kind == SqKind.full)).map (fun e => e.val)).headD 0

-- ⚑ **The four challenges and the digest of a REAL accepted proof, out of THIS file's emitter.**
#guard realChals.getD 0 0 == Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
#guard realChals.getD 1 0 == Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
#guard realChals.getD 2 0 == Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
#guard realChals.getD 3 0 == Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL
#guard realDigest == Dregg2.Circuit.Emit.PastaPoseidonFq.FQDIGEST

/-- ⚑ RED CONTROL. Bending ONE absorbed word of that tape moves ALL FOUR challenges and the digest
— which is what makes the pins above a measurement of the derivation rather than of five
constants. -/
def realBent : SpAcc :=
  runSpongeQ 0 realTapeSchedule 3 (qAdd (Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape.getD 3 0) 1)
def realBentChals : List Nat := (chalSqueezes realBent).map (fun e => e.2 % 2 ^ 128)
#guard realBentChals.getD 0 0 != Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
#guard realBentChals.getD 1 0 != Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
#guard realBentChals.getD 2 0 != Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
#guard realBentChals.getD 3 0 != Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL

/-! ### §12b — the rungs are a LADDER and every row-set is REACHED.

The step side measured a sub-circuit whose row emitter was absent from `rungRows` while every probe
still passed — the rows the commit subject named were in NO proved circuit. These pin each rung's
length as the sum of its own sub-lists, so a dropped row-set is a red. -/

#guard (rungRows tW .transcript true).length
       == (transcriptRowsQ (baseSp shapeSmoke) tW.sp true).length
#guard (rungRows tW .challenges true).length
       == (rungRows tW .transcript true).length + (challengeRowsQ tW true).length
#guard (rungRows tW .branch true).length
       == (rungRows tW .challenges true).length
          + (branchRows shapeSmoke (baseBr shapeSmoke tW.sp) tW.br true).length
#guard (rungRows tW .bind true).length
       == (rungRows tW .branch true).length + (closingRows tW).length
-- Strictly monotone: every rung really adds rows.
#guard (rungRows tW .transcript true).length < (rungRows tW .challenges true).length
#guard (rungRows tW .challenges true).length < (rungRows tW .branch true).length
#guard (rungRows tW .branch true).length < (rungRows tW .bind true).length

/-! The WIRED and UNWIRED circuits differ ONLY in the probe rows' permutation columns — the control
that turns "rejected" into "rejected BY THE WIRE". -/
#guard rowsW.length == rowsUW.length
#guard (rowsW.zip rowsUW).all (fun p => p.1.kind == p.2.kind && p.1.coeffs == p.2.coeffs)
#guard (rowsW.zip rowsUW).all (fun p => p.1.probe == p.2.probe)
#guard ((rowsW.zip rowsUW).filter (fun p => p.1.perm != p.2.perm)).length
       == (rowsW.filter (fun r => r.probe)).length
#guard (rowsW.filter (fun r => r.probe)).length > 0

/-! The placement is ACCEPTED — no `auxOverlapsPublic`, no `referenceInGap`, no `inertPublicWord`.
⚑ That last one is the real gate: a wrap statement word no gate reads REFUSES here rather than
sitting inert in the public vector. -/
#guard refusalOf shapeSmoke shapeSmoke.pubWords gatesW == none
#guard placedW.length == shapeSmoke.pubWords + nRowsW
#guard inertPublicWords shapeSmoke.pubWords gatesW == []

/-! The witness grid is 15 columns of `pubWords + nRows`. -/
#guard gridW.length == 15
#guard (gridW.getD 0 []).length == shapeSmoke.pubWords + nRowsW

/-! ### §12c — DEFECT CLASS 1/6: the `EndoMulScalar` SEEDS are PINNED.

`scalar_challenge.ml:63-66` seeds `n₀ = 0, a₀ = 2, b₀ = 2`. Leaving any of the three a free witness
lets a prover choose the decoded scalar while the chain still closes — the same shape as the step
side's free `acc₀`/`n₀` (`plonk_curve_ops.ml:157-158`). All three are pinned by `Generic` rows
(`tfcRowsQ`'s first two), and this exhibits what a free seed would buy. -/

/-- The same chain at a bent seed `n₀ = 1` decodes a DIFFERENT scalar. -/
def seedBentN : Nat :=
  let cr := crumbsOfQ shapeSmoke 12345
  cr.foldl (fun acc x => (4 * acc + x) % qN) 1
def seedHonestN : Nat := ((emsAccsQ shapeSmoke 12345).getD shapeSmoke.emsRows (0, 2, 2)).1
#guard seedBentN != seedHonestN
/-- …and the emitted rows DO pin all three: `n₀ = 0` and `a₀ = 2` on one row, `b₀ = 2` on the next. -/
def seedRow0 : List Int :=
  ((tfcRowsQ shapeSmoke 0 (chainVars shapeSmoke 100 0) (.external 1) true 12345 true).getD 0
     default).coeffs
def seedRow1 : List Int :=
  ((tfcRowsQ shapeSmoke 0 (chainVars shapeSmoke 100 0) (.external 1) true 12345 true).getD 1
     default).coeffs
#guard seedRow0 == cConst 0 ++ cConst 2
#guard seedRow1 == cConst 2 ++ cNil

/-! ### §12d — DEFECT CLASS 2: BOTH halves of `lowest_128_bits` are range-checked.

`util.ml:88-101` witnesses `(lo, hi)`, then `assert_128_bits hi` UNCONDITIONALLY (`:98`) and
`assert_128_bits lo` only when `~constrain_low_bits` (`:99`), and closes with
`Field.Assert.equal x Field.(lo + scale hi (pow2 128))`. With only the LOW half constrained that
last line is one equation in two unknowns: for any `lo' < 2¹²⁸` a prover solves
`hi' = (x − lo')·2^{−128}` and the Fiat–Shamir challenge is his. The forged `hi'` is generically
≥ 2¹²⁸, so its OWN `to_field_checked` chain cannot reconstruct it — which is why `:98` is
unconditional, and why this file emits a SECOND chain per challenge. -/

/-- A real squeeze off the smoke transcript, and the honest split. -/
def sqSample : Nat := ((chalSqueezes tW.sp).getD 0 (.external 0, 0)).2
def hiHonest : Nat := sqSample / 2 ^ CHAL_BITS shapeSmoke
def loHonest : Nat := sqSample % 2 ^ CHAL_BITS shapeSmoke
/-- A FORGED low part. `util.ml:100` stays satisfiable because `hi' = (x − lo')·2^{−128}` always
exists in `Fq` — `2^128` is a unit — so the decomposition row alone constrains NOTHING about which
128-bit value `lo` is. -/
def loForged : Nat := (loHonest + 12345) % 2 ^ CHAL_BITS shapeSmoke
/-! The honest split satisfies the decomposition row, stated on this assembly's own squeeze. -/
#guard qAdd loHonest (qMul hiHonest (2 ^ CHAL_BITS shapeSmoke)) == sqSample % qN
#guard loForged != loHonest
/-! ⚑ …and the HIGH chain refuses it: `emsAccsQ` reconstructs only `chalBits` bits, so a chain over
a value ≥ 2^chalBits cannot close its `Field.Assert.equal n scalar` tie. Exhibited on the honest
`hi` (which IS below the bound, so the chain closes) and on a forged one that is not. -/
#guard seedHonestN == 12345 % 2 ^ CHAL_BITS shapeSmoke
#guard ((emsAccsQ shapeSmoke (2 ^ CHAL_BITS shapeSmoke + 7)).getD shapeSmoke.emsRows (0, 2, 2)).1
       != 2 ^ CHAL_BITS shapeSmoke + 7
/-! The high chain IS emitted, one per challenge — `2 · nChals` chains of `emsRows` rows. -/
#guard (rowsW.filter (fun r => r.kind == KGateType.endoMulScalar)).length
       == 2 * nChals shapeSmoke * shapeSmoke.emsRows

/-! ### §12e — DEFECT CLASS 3: the UNCONSUMED census is REPORTED, not padded.

Every absorbed item is a variable and the sponge's own absorb row reads it; NONE is yet read by a
consumer, because W-XHAT / W-COMBINE / W-BULLET are not assembled. This pins the count, so
"closing" an item by wiring it to a gadget that merely re-reads it would not move the number. -/
#guard WRAP_UNCONSUMED.length == 9
#guard (tW.sp.evs.filter (fun e => e.isAbs)).length == nItems shapeSmoke
/-- ⚑ …and the transcript's dependence on them is REAL: bending one absorbed word moves every later
challenge. That is the property an absorbed-but-unconsumed word still has, and it is the only one. -/
def tBent : WrapData := mkWrapWith shapeSmoke 5 (qAdd (itemVal T_WCOMM 0) 7)
#guard ((chalSqueezes tBent.sp).getD 0 (.external 0, 0)).2
       != ((chalSqueezes tW.sp).getD 0 (.external 0, 0)).2
#guard ((chalSqueezes tBent.sp).getD 3 (.external 0, 0)).2
       != ((chalSqueezes tW.sp).getD 3 (.external 0, 0)).2

/-! ### §12f — ⚑ the RATE-2 STATE MACHINE, and what a block model gets wrong.

`poseidon.rs:107-146` (transcribed in `PastaPoseidonFq.absorb1`/`squeeze1`): β and γ come out of ONE
permutation — γ reads lane 1 with no permutation — and the `z_comm` absorbed right after them
re-enters at lane 0 without one. A one-permutation-per-squeeze model, which is what the step side's
R1 runs, would emit two extra permutations here and would make γ a function of a state upstream
never reaches. §12a is the measurement that this file does not. -/

def sqEvts : List SpEvt := tW.sp.evs.filter (fun e => !e.isAbs)
#guard (sqEvts.getD 0 default).didPerm == true
#guard (sqEvts.getD 1 default).didPerm == false
#guard (sqEvts.getD 0 default).lane == 0
#guard (sqEvts.getD 1 default).lane == 1
/-! …and they are read out of the SAME state triple, which is what "one permutation" means. -/
#guard (sqEvts.getD 0 default).midN == (sqEvts.getD 1 default).midN

/-! ⚑ THE FORK. `sponge_before_evaluations = Sponge.copy sponge` (`wrap_verifier.ml:645`) is taken
BEFORE `sponge_digest_before_evaluations = Sponge.squeeze_field sponge` (`:646`), so the digest
squeeze does NOT advance the transcript: the state it carries forward is the one it entered with. -/
def forkEvt : SpEvt := (tW.sp.evs.filter (fun e => !e.isAbs && e.kind == SqKind.fork)).getD 0 default
#guard (tW.sp.evs.filter (fun e => !e.isAbs && e.kind == SqKind.fork)).length == 1
#guard forkEvt.outN == forkEvt.inN
/-! …and it still COSTS its permutation, so the digest is a real squeeze and not a relabelled cell. -/
#guard forkEvt.didPerm == false
#guard forkEvt.val != 0

/-! ### §12g — the gate census.

The `wrap-transaction` blob's own histogram is
`Generic 3521 · Poseidon 2871 · Zero 2757 · EndoMul 2528 · VarBaseMul 2417 · EndoMulScalar 536 ·
CompleteAdd 492` (`mina-canonical-circuit-oracle.mjs --circuit wrap-transaction`), 15,122 gates at
PI 40. This assembly emits FOUR of those seven families; the three it does not are W-XHAT /
W-FTCOMM / W-COMBINE / W-BULLET's curve gadgets, named in §13. Saying so here is the point. -/

def censusW : List (KGateType × Nat) :=
  [KGateType.zero, .generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoMulScalar].map
    (fun k => (k, (rowsW.filter (fun r => r.kind == k)).length))
#guard (rowsW.filter (fun r => r.kind == KGateType.varBaseMul)).length == 0
#guard (rowsW.filter (fun r => r.kind == KGateType.endoMul)).length == 0
#guard (rowsW.filter (fun r => r.kind == KGateType.completeAdd)).length == 0
/-! Poseidon rows come in 11-row permutations — the run-length family the conformance diff
compares — and `EndoMulScalar` in 8-row chains. -/
#guard (rowsW.filter (fun r => r.kind == KGateType.poseidon)).length % 11 == 0
#guard (rowsW.filter (fun r => r.kind == KGateType.endoMulScalar)).length % 8 == 0

/-! ### §12h — the emitted circuit is well-formed for the harness. -/
#guard placedW.all (fun g => g.wires.length == K_PERMUTS)
#guard gridW.all (fun col => col.length == shapeSmoke.pubWords + nRowsW)
/-! Every gate's `typ` ordinal is one of the seven Mina uses. -/
#guard placedW.all (fun g => g.kind.ordinal < 7)

/-! ## §13 — ⚑ WHAT IS LEFT, BY SUB-CIRCUIT.

Named, not estimated; each entry is a row emitter this file does not have, and each carries the
measurement that sizes it. None of them is a value this file fakes and calls derived.

  1. **W-KEY** `wrap_verifier.ml:189-204`, `wrap_main.ml:215-220` — `choose_key`: 28 commitments ×
     2 coordinates × `branches` `Generic` multiplication halves plus the reduce and the `seal`, then
     `sponge_after_index` over the chosen key (28 absorb pairs + a squeeze ≈ 29 permutations) whose
     output IS the transcript's first absorbed word. Until it lands, `index_digest` is §2d's fixture
     and the one-hot bits reach `branch_data` and nothing else — which is what §2c says.
  2. **W-XHAT** `wrap_verifier.ml:539-616` — the public-input MSM, and it is NOT the step side's
     `multiscale_known`. ⚑ **MEASURED: 67 scalars, at widths 15 × 255 · 40 × 128 · 12 × 1.** The
     STEP statement packs to **57** words (`composition_types.ml:1268-1276,1427-1436,1453-1459` at
     `bp_log2 = Backend.Tock.Rounds.n = 15` and `max_proofs_verified = 2`), of which 10 are `` `Field ``
     and 47 `` `Packed_bits ``; `wrap_verifier.ml:542-548` turns each `` `Field `` into TWO entries
     (255-bit value + 1-bit parity), giving 57 + 10 = 67. The 12 one-bit scalars take the
     `` `Cond_add `` path with an explicit `assert_ (Constraint.boolean …)` (`:573-576`); the other
     55 take `Ops.scale_fast2'` at `chunks_needed ~num_bits:(n−1)` five-bit chunks — **51 chunks at
     255 bits, 26 at 128** (`plonk_curve_ops.ml:66-70,251-267`). Plus the `lagrange` /
     `scaled_lagrange` constant partition, the correction sum, `Inner_curve.negate` and
     `x_hat blinding`.
  3. **W-SPLIT** `wrap_main.ml:51-81` — `split_field`: one `Generic` half per statement `Field`
     word plus a `Boolean.typ` check, with the hi range check DEFERRED INTO `scale_fast2`
     (upstream's own comment, `:64-68`; the check is `scale_fast2`'s top-bit loop at
     `plonk_curve_ops.ml:262-265`). Emitting the split without that deferred check would be defect
     class 2 in a new place.
  4. **W-FTCOMM** `wrap_verifier.ml:655-666` — `Common.ft_comm`, eight `scale_fast2`s at
     `Other_field.Packed.Constant.size_in_bits = 255`, i.e. 51 chunks each.
  5. **W-COMBINE** `wrap_verifier.ml:320-379,676-713` — `Split_commitments.combine` over
     **47** commitments (`Nat.N45.n + Max_proofs_verified.n`; the 45 are 9 singletons + `w_comm` 15
     + `coefficients_comm` 15 + `sigma_comm_init` 6, `plonk_types.ml:14-19`), with the `Curve_opt`
     `keep` mux, `Point.Maybe_finite`, `Inner_curve.if_` and `Boolean.Assert.is_true non_zero`.
     ⚑ The step side's fold has no mux; this one does, and `with_degree_bound` is `[]`.
  6. **W-BULLET** `wrap_verifier.ml:383-437` — `check_bulletproof`: `group_map`, the fold,
     `bullet_reduce` over **16** rounds (`Backend.Tick.Rounds.n`, `wrap_main.ml:381`) each costing
     `endo_inv` + `endo` = **two** 32-block `EndoMul` ladders (`endo_inv` IS an `endo` plus two
     equality asserts, `scalar_challenge.ml:343-354`) and an `add_fast`, then 15 reduction adds;
     four `scale_fast` at 255 bits; `lhs`, `rhs`, `equal_g`.
     ⚠ Exactly as on the step side, `G`, `z₁` and `z₂` are FREE WITNESSES in `openings_proof`
     (`wrap_main.ml:357-383`), so assembling `equal_g` would refuse no on-curve substitution of a
     consumed commitment. The refusal is the accumulator check, which is W-FINALIZE's.
  7. **W-FINALIZE** `wrap_verifier.ml:820-1049`, run `prevs` times — the deferred-value finalizer.
     ⚑ **AND `Scalars.Tock` IS NOT `Scalars.Tick` WITH DIFFERENT LITERALS**, whatever
     `plonk_checks/scalars.ml:104` says: `Tock`'s `constant_term` (`:3405-4250`) DISCARDS `beta`,
     `gamma`, `joint_combiner`, `if_feature`, `unnormalized_lagrange_basis` and
     `vanishes_on_last_4_rows` outright (`:3406-3430`, every one bound to `_`) and uses only
     `alpha^1..alpha^20`, where `Tick` (`:105-3403`) uses `alpha^1..20, 24..31` and 68 `if_feature`
     guards. Both `index_terms` are the EMPTY table. Porting the step side's `gateLinConst` across
     unchanged would be wrong in both directions. This is the biggest remaining piece and it is
     what wrap public words 0–4 and 9 need.
  8. **W-WRAPHACK** `wrap_hack.ml:118-141`, `wrap_main.ml:340-355,421-429` — the two
     `hash_messages_for_next_wrap_proof` sponges; wrap public words 11 and 12. ⚑ Absorption order
     is **all old bulletproof challenges first, flattened, THEN the commitment as `[x; y]`**
     (`composition_types.ml:411-418`) — the opposite of the step side's interleaving — and the
     padding is at the FRONT via a PRECOMPUTED sponge-state table indexed by
     `2 − max_proofs_verified` (`wrap_hack.ml:99-109,124-137`), not by absorbing dummies in circuit.
  9. **W-PREV** `wrap_main.ml:201-256` — the witnessed previous proof state, including
     `~assert_16_bits:(assert_n_bits ~n:16)`, a `to_field_checked` at a width this file does not
     emit (only 128), and `old_bp_chals` at `Backend.Tock.Rounds.n = 15` per proof.
 10. **W-CLOSE**'s curve-side assert `wrap_main.ml:419-420` — `Boolean.Assert.is_true
     bulletproof_success`, which is W-BULLET's output.

⚠ ⚑ **TWO PLACES THIS FILE IS STRICTER THAN UPSTREAM, said rather than banked.**

  * **`One_hot_vector`.** `wrap_main.ml:170-171` calls `One_hot_vector.of_index` on a raw `exists`,
    and `of_index` (`one_hot_vector.ml:22-25`) asserts `Boolean.Assert.any`, NOT `exactly_one` —
    uniqueness follows from `Field.equal`'s determinism, and the `exactly_one` in `typ` (`:29-38`)
    is not on this path. §9 emits a `Σ bᵢ = 1` fold, which is the `typ` form. Stricter, and
    therefore not a fidelity claim.
  * **`Pseudo.choose`.** `pseudo.ml:22-30` is `Σ (bᵢ :> t) · xᵢ`, and with `~f:Field.of_int` the
    `xᵢ` are CONSTANTS, so `Checked.mul` takes its `Constant` branch (`utils.ml:81-88`) and the
    whole fold is a free linear combination — **zero rows upstream**. §9 emits it as rows. Again
    stricter, and again not a row-count this file may claim as conformance.
  * ⚑ **AND THE `to_field_checked` SEAM, MEASURED rather than reasoned.**
    `bridge/mina-zkapp/scripts/wrapmain-region-conformance.mjs` reports the `EMS8` gadget BODY
    (rows 1..6, base-free signature) matching a `wrap-transaction` class on **42/42** instances, and
    the WHOLE 8-row instance matching on **0/42**, with exactly three cells differing:
    `+0.w2 IN 0,3→EXT`, `+7.w4 SELF→EXT`, `+7.w5 SELF→EXT`. Both are this file being stricter:
    (a) upstream's `a₀` and `b₀` are ONE cell, because `scalar_challenge.ml:63-66` seeds both at
    `Field.of_int 2` and Snarky gives them one constant `Cvar`, where §5 pins two variables;
    (b) upstream leaves `a₈`/`b₈` SELF — i.e. UNWIRED — because `Field.(scale a endo + b)`
    (`scalar_challenge.ml:136`) is a `Cvar` linear combination that Snarky folds into whatever
    consumes it and emits **no row**, where §5 emits an explicit lift row. Neither is a missing
    constraint, and neither may be reported as row-count conformance.

## ⚑ WHERE FIAT–SHAMIR STANDS, at the resolution it is actually at

  * **GIVEN THE STATE, no challenge in this assembly is prover-chosen.** Both halves of every
    `lowest_128_bits` are range-checked (§12d), the sponge state crosses every permutation as a σ
    class, the `EndoMulScalar` seeds are pinned (§12c), and the rate-2 machine is upstream's own
    (§12a, §12f).
  * **THE INPUT IS NOT YET DERIVED.** `index_digest` is a fixture until W-KEY lands, and the
    commitment words are absorbed and consumed by nothing (§2c). A prover who could choose an
    absorbed word would steer every challenge; the transcript BINDS its input (§12e), but nothing
    here yet forces that input to be the previous proof's actual commitment. W-KEY, W-XHAT and
    W-COMBINE are what would, and they are the first thing to build.
  * **THE OPENING IS NOT HERE AT ALL.** `equal_g`, `verified` and the accumulator check are
    W-BULLET and W-FINALIZE. Everything this file proves is about the transcript and the selection.
-/

end Dregg2.Circuit.Emit.KimchiWrapMain
