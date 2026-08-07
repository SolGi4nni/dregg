/-
# Dregg2.Circuit.Emit.KimchiWrapMainCore — `wrap_main`'s DEFINITIONS: the whole emitter.

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

§0–§8 verbatim: the Fq gate constants, the shape, the transcript schedule and its census, the
row-schedule primitives, all fifteen sub-circuits (W1 transcript · W2 challenges · W3 branch ·
W-KEY · W-XHAT · W-SPLIT · W-FTCOMM · W-PREV · W-WRAPHACK · W-CLOSE · W-FINALIZE · W-FINSPONGE ·
W-COMBINE · W-BULLET), the rung ladder, the renderer and the two committed shapes.

⚑ **THIS IS WHAT THE EMIT DRIVER IMPORTS**, and the point of the split: `EmitWrapMainJson` needs
the emitter, not the pins, so an emission no longer waits on a single sponge trajectory reducing in
the kernel. `EmitStepMainJson` imports `…StepMainCore` for exactly this reason and the step side
measured emitting fall to 13.6 s.

-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.MinaRealBlockTranscript
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate
import Dregg2.Circuit.Emit.MinaWrapDeferredWords
import Dregg2.Circuit.Emit.KimchiWrapMainField
import Dregg2.Circuit.Emit.KimchiStepWrapChainKey
-- ⚑ THE STEP PROOF THE TRANSCRIPT IS ABOUT. `RC_SGOLD`/`RC_WCOMM`/`RC_ZCOMM`/`RC_TCOMM` read it;
-- the module imports only `PastaField`, so this is not a cycle.
import Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)
-- ⚑ The six deferred words `wrap_main` READS and never derives, MEASURED through Mina's own
-- `PreparedStatement::to_public_input(40)`. See `MinaWrapDeferredWords` for provenance and for the
-- width signature that says each is the object its slot names.
open Dregg2.Circuit.Emit.MinaWrapDeferredWords
  (DEF_CIP DEF_B DEF_ZETA_TO_SRS_LENGTH DEF_ZETA_TO_DOMAIN_SIZE DEF_PERM DEF_XI)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ## §0 — **Fq**, and the Fq gate constants.

Every value in this file lives mod `qN`. Nothing is shared with `KimchiStepMain`, which is mod `pN`;
a single `% pN` reaching this file would be a silent field confusion.

⚑ **`qAdd` / `qSub` / `qMul` / `qInv` and the whole Vesta value layer moved to
`KimchiWrapMainField` at `w6_xhat`** — same namespace, so nothing here is renamed. The reason is
NOT tidiness: `wrap_verifier.ml:617` absorbs the x_hat MSM's OUTPUT into the transcript, so §15's
value has to exist before §2's schedule, and Lean is order-sensitive. §11a/§11b still pin the two
constants a copy-paste would get wrong. -/

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
  /-- ⚑⚑ **`Max_proofs_verified.n`, AND NOT `actual_proofs_verified` — RENAMED 2026-08-07 BECAUSE
  ONE NAME SERVING TWO NUMBERS HAS NOW COST THIS FILE FIVE REPAIRS.**

  This sizes every STRUCTURAL `prev_step_accs`-shaped thing the wrap circuit allocates, and every
  one of them is `Max_proofs_verified` at source:

    * `prev_step_accs = exists (Vector.typ Inner_curve.typ Max_proofs_verified.n)`
      (`wrap_main.ml:221-223`; `wrap.rs:2832-2840` hands it `messages_for_next_wrap_proof_padded`),
      so `assert_on_curve` runs on all of them — the PAD included, and `whPadSg` is on `y² = x³ + 5`;
    * `prev_proof_state.typ` at `Vector.init Max_proofs_verified.n` (`wrap_main.ml:265-275`);
    * the `finalize_other_proof` loop, over `prev_proof_state.unfinalized_proofs`, whose own
      upstream comment is *"This is padded to max_proofs_verified for the benefit of wrapping with
      dummy unfinalized proofs"* (`wrap_main.ml:287-289`);
    * `Split_commitments.combine`'s list, `Vector.append sg_old … (snd (Max_proofs_verified.add
      Nat.N45.n))` (`wrap_verifier.ml:687-702`; `wrap.rs:2458-2477`'s `sg_old.chain(rest)` over
      `NUM_COMMITMENTS_WITHOUT_DEGREE_BOUND = 45`) — so `combTerms` is `maxPrevs + 45`.

  ⚠ **`actual_proofs_verified` IS NOT A SHAPE FIELD AND CANNOT BE ONE**, which is the structural
  reason the conflation kept coming back: it is `Pseudo.choose (which_branch, step_widths)`
  (`wrap_main.ml:173-180`) — a value the WITNESS selects — while `Max_proofs_verified` is a functor
  argument of the compiled instance. It lives on `BranchData.fz`, and the one place the transcript
  needs it is `schedule`, which reads `WH_REAL_SLOTS`. -/
  maxPrevs : Nat
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
  /-- ⚑ **WHICH x_hat MSM ENTRIES THIS SHAPE EMITS — the SELECTION, not a count** (§15).

  At the committed wrap shape this is `xhatSel XHAT_TERMS_FULL = List.range 67`, i.e.
  `wrap_verifier.ml:539-548`'s own entry list in its own order; the smoke shape carries a NAMED
  spread that reaches all three widths and both partitions; and the shape that verifies **dregg's own
  step proof** carries `XHAT_OWN_SEL`, twelve entries of a disjoint index space whose bases are the
  step SRS's Lagrange basis at THIS proof's domain.

  ⚠ ⚑ **IT WAS `xhatTerms : Nat` AND THAT COULD NOT SURVIVE A SECOND ENTRY SPACE.** A count names a
  selection only through `xhatSel`, which is Mina's packed statement's; so `xhatTerms := 12` read
  like "this proof's twelve public inputs" and meant "Mina's named spread of twelve", with no diff
  at any call site. That is `mkWrap`'s `nItems + 1` sentinel again — one number, two meanings, which
  at smoke scale lands harmlessly and at wrap scale zeroes a real word. The selection is now the
  field, so a shape says which entries it means. `EmitWrapMainJson` refuses a selection that leaves
  the entry space or names an index twice. -/
  xhatEntries : List Nat
  /-- ⚑ **THE PAIR `wrap_verifier.ml:617` ABSORBS** — §15's MSM output, carried in the SHAPE rather
  than recomputed inside `schedule`.

  ⚠ This is a MEMO WITH A PROOF OBLIGATION, not a fixture, and the difference is enforced in two
  places: `xhat_smoke_shape_absorbs_the_msm_output` closes it by `rfl` IN THE KERNEL for the smoke
  shape, and `EmitWrapMainJson` REFUSES to emit a COMMITTED shape whose `xhatXY` is not
  `xhatOutOf xhatEntries`. A wrong pair cannot reach a proved circuit. ⚑ A `DREGG_WM`-supplied shape is
  a different case and the refusal does NOT cover it: a comma spec of naturals cannot carry two Fq
  coordinates, so `parseShape` DERIVES the pair and it agrees by construction. Saying the refusal
  covers that path too would be describing a branch that cannot go red.

  ⚑ It is here because of a MEASUREMENT. `schedule` feeds the whole transcript, so a dozen §12/§14b
  kernel theorems reduce it; with the MSM inline each of them re-ran 77 five-bit ladder chunks
  (1805 at the wrap shape) in the kernel, and the file went from 150 s and ~1 GB to unfinished at
  9.6 GB. Memoising the pair turns a dozen full MSM reductions into one. -/
  xhatXY : Nat × Nat
  deriving Repr, Inhabited, DecidableEq

/-- ⚑ Mina's own wrap public-input width — `mina-canonical-circuit-oracle.mjs` reports
`public_input_size = 40` for both `wrap-transaction` and `wrap-blockchain`, and the devnet wrap VKs
say `public: 40`. Two independent sources. `MinaWrapPublicInput` carries the slot-by-slot layout. -/
def WRAP_PRIMARY_LEN : Nat := 40

/-- Mina's slot for `messages_for_next_step_proof` — the `Field.Assert.equal` of
`wrap_main.ml:350-351`, which W-PREV emits. §10's census and
`Dregg2.Bridge.MinaWrapPublicInput.publicInputWords` are the two sources. -/
def WRAP_SLOT_MSG_NEXT_STEP : Nat := 12

/-- Mina's slot for `messages_for_next_wrap_proof` — the closing
`hash_messages_for_next_wrap_proof` squeeze (`wrap_main.ml:421-431`), which W-WRAPHACK emits. -/
def WRAP_SLOT_MSG_NEXT_WRAP : Nat := 11

/-- Mina's slot for `branch_data` — `(domain_log2 <<< 2) ||| proofs_verified`
(`branch_data.ml:63`, `prepared_statement.rs:131-139`), which §9's `Branch_data.Checked.pack`
derives. ⚑ It is the ONE derived word with no transcript dependence at all, which is what
`KimchiStepWrapChain.the_bend_moves_every_transcript_derived_public_word` singles it out for. -/
def WRAP_SLOT_BRANCH_DATA : Nat := 29

/-! ⚑ **THE SIX SLOTS `wrap_main` READS AND NEVER CHECKS**, named rather than written as literals at
their tie sites. `prepared_statement.rs:99-117` is the authority for every index here, and
`MinaWrapDeferredWords` carries the values with the width signature that says each is the object its
name claims. ⚠ `perm` is slot **4** and `zeta_to_srs_length` is slot **2** — the emit order of
`ftcSVal`'s three arguments (`0 = perm`, `1 = zeta_to_srs_length`, `2 = zeta_to_domain_size`) is
`ft_comm`'s and is NOT Mina's slot order, which is exactly the transposition a slot map exists to
get right. -/

/-- `advice.combined_inner_product`, `absorb_shifted` at `wrap_verifier.ml:395`. -/
def WRAP_SLOT_CIP : Nat := 0
/-- `advice.b`, `check_bulletproof`'s `b·u` multiplier. -/
def WRAP_SLOT_B : Nat := 1
/-- `plonk.zeta_to_srs_length`, `ft_comm`'s fold multiplier. -/
def WRAP_SLOT_ZETA_TO_SRS : Nat := 2
/-- `plonk.zeta_to_domain_size`, `ft_comm`'s closing scale. -/
def WRAP_SLOT_ZETA_TO_DOM : Nat := 3
/-- `plonk.perm`, `ft_comm`'s `f_comm` scale. -/
def WRAP_SLOT_PERM : Nat := 4
/-- `xi`, the `Split_commitments.combine` endo ladders' shared scalar. -/
def WRAP_SLOT_XI : Nat := 9

/-- ⚑ **THE OUT-OF-RANGE SENTINEL — AND IT STOPPED BEING `.external 0` ON 2026-08-05.**

Five `getD` sites need a total default for a lookup that should never miss (a squeeze index past the
end of the tape, a `forkSqueeze` that found nothing). Every one of them used `.external 0`, which was
harmless for exactly as long as slot 0 was declared unread: a fired default tied a cell to a public
word nothing looked at.

Slot 0 is `combined_inner_product` now, and it is READ. A fired default would silently alias the
consumer's cell to it — `exposedVars`' `forkSqueeze` fallback is the sharp one, since that entry is
tied to slot 10 and would have made slots 10 and 0 one variable. That is the exact shape of defect
this layout exists to refuse: no length moves, no count moves, and every rung still proves.

⚠ `.internal` is the right sentinel because `externalRefs` filters it out by construction, so a
fired default can never make a public word look read. This file allocates NO other internal, so the
id is unambiguous in a dump. -/
def PVAR_NOWHERE : PVar := .internal 0

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

/-! ### ⚑ **THE COMMITMENTS ARE OUR OWN STEP PROOF'S SINCE 2026-08-05 — AND THAT CLOSED A
THREE-PROOF PIPELINE, NOT A ONE-PROOF GAP.**

These four blocks used to be `PastaPoseidonFq`'s: the commitments of a `create_circuit(0,5)` proof
exported from a THIRD-PARTY checkout (`kimchi/examples/pickles_p6_fq_export.rs`). They were real,
and they were *someone else's*. Meanwhile the forty public words `MinaWrapDeferredWords` carries
came from `pickles_kimchi_marshal`'s step proof, and `KimchiStepWrapChainFixture` was written by a
SECOND binary about a THIRD step proof — proved over kimchi's TEST SRS with **`OsRng`**, so not even
reproducible.

⚠ **THREE PROOFS, AND EVERY SHAPE AGREED**: `maxPrevs = 2`, `wComms = 15`, `tComms = 7` on all three,
so no census, no arity check and no `WrapShape` comparison could ever go red. That is the whole
lesson — *same-shape is not same-proof*, and a pipeline whose parts agree on shape will keep its
disagreement about IDENTITY silently forever.

There is now ONE step proof. `tape.rs` writes `KimchiStepWrapChainFixture` from the same
`prove_step` return value that produces the forty, so the words this transcript absorbs and the
words the public vector must derive are facts about one object.

⚠ **WHAT IS STILL NOT THIS PROOF'S, SAID PLAINLY.** Two of the transcript's absorbed items are not
sourced here and are not claimed to be:

  * `RC_DIGEST` is **Mina's `step-transaction` key's** index digest, not ours — §14's `choose_key`
    folds `STEP_VK_XY`, and that is W-KEY's deliberate anchor (`KimchiStepWrapChainKey` carries our
    own step key's 56 coordinates for the chain, which is the module that uses them);
  * `x_hat` is §15's MSM output, which is `w6_xhat`'s achievement and not a fixture at all.

So the emitted transcript's β/γ/α/ζ are NOT this step proof's β/γ/α/ζ, and nothing here says they
are. `KimchiStepWrapChain` is where that equality is a theorem, because it overrides both. -/

/-- ⚑⚑ **`prev_step_accs`, THE WHOLE `Max_proofs_verified`-LONG RECORD — `[pad …; real …]`.**

`wrap_main.ml:221-223` allocates `Vector.typ Inner_curve.typ Max_proofs_verified.n` and
`wrap.rs:2832-2840` fills it from `messages_for_next_wrap_proof_padded`, which
`pad_messages_for_next_wrap_proof` (`wrap.rs:476-491`) has PREPENDED
`InnerCurve::from(dummy_ipa_step_sg())` onto until it is `WH_PADDED` long. So slot 0 is the pad and
the real `RecursionChallenge` commitments (`verifier.rs:165-168`) are LAST.

⚠ **IT CARRIED THE REAL POINTS ALONE UNTIL 2026-08-07 AND THAT IS WHAT PUT AN OFF-CURVE POINT IN
THE SMOKE SHAPE.** When `STEP_PREVCOMM_XY` went from four coordinates to two (dregg's step rule
has one `verify_one`), `shapeSmoke`'s two-slot `prev_step_accs` indexed past the end and took
`wrapFixture 1 2` — a number that is not on `y² = x³ + 5`, so `prev_step_accs_are_on_vesta`,
`bullData`'s `equal_g` legs and `close_witness_is_the_bullet_verdict` all went red on the same
filler. The pad is a REAL Vesta point and the record is now the object upstream allocates.

⚑ The TRANSCRIPT is a different length: `schedule` absorbs the kept SUFFIX only, because the
`OptSponge` mask drops the pad. -/
def RC_SGOLD : List Nat :=
  (List.range (whNPad WH_REAL_SLOTS)).flatMap (fun _ => [whPadSg.1, whPadSg.2])
  ++ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY
/-- ⚠ **NOT ON THE TRANSCRIPT ANY MORE — A RED CONTROL ONLY.** The third-party proof's
public-input commitment, kept because `xhat_derived_is_not_the_old_fixture` exhibits the value the
transcript used to absorb before §15's MSM replaced it. -/
def RC_XHAT : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.PUBCOMM_XY
/-- The step proof's 15 witness commitments (`verifier.rs:173-177`, absorbed at `:619`). -/
def RC_WCOMM : List Nat := Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_WCOMM_XY
/-- The step proof's `z_comm` (`verifier.rs:250`, absorbed at `:623`). -/
def RC_ZCOMM : List Nat := Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_ZCOMM_XY
/-- The step proof's 7 `t_comm` chunks (`verifier.rs:269`, absorbed at `:630`). -/
def RC_TCOMM : List Nat := Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_TCOMM_XY
/-- ⚑ **THE INDEX DIGEST OF §14's `STEP_VK_XY`** — `verifier_index.digest::<BaseSponge>()` as Rust
kimchi computes it for Mina's `step-transaction` key, which `key_digest_is_the_index_digest`
re-derives from the 56 coordinates through THIS FILE's own Fq sponge, and which the extractor re-derives a third time by an independent `absorb_fq`
replay. Two implementations, three computations, one number.

⚠ It is NOT `PastaPoseidonFq.VKDIGEST`, and the split is the point: that constant is the
verifier-index digest of the accepted proof §12a's reality gate replays, and the two coincided only
while `STEP_VK_XY` was that proof's index.

⚠ ⚑ **AND IT IS NOT `RC_DIGEST` EITHER SINCE 2026-08-06.** `wrap_verifier.ml:537` absorbs the digest
of the key `choose_key` SELECTED, and this assembly selects `KEY_CHAIN_BRANCH`. This number is
`KEY_REAL_BRANCH`'s, which is the branch `key_digest_moves_with_the_branch_selection` exhibits as
the one the tape does NOT admit. -/
def STEP_VK_DIGEST : Nat := 4681608191240531986877886841186183594145822800262795016763288444525244254540

/-- ⚑⚑ **THE TRANSCRIPT'S FIRST ABSORBED WORD IS DREGG'S OWN STEP KEY'S DIGEST SINCE 2026-08-06.**
`wrap_verifier.ml:537` absorbs `index_digest` of the key `choose_key` selected, and this assembly
selects `KEY_CHAIN_BRANCH` — dregg's own compiled step rule — so the word here is that rule's
`VerifierIndex::digest::<BaseSponge>()`.

⚑ **IT IS `KimchiStepWrapChainFixture.STEP_VKDIGEST` AND NOT `KimchiStepWrapChainKey
.STEP_OWN_VK_DIGEST`, AND THE DISTINCTION IS THE GATE.** The fixture's copy is read off the PROOF
(`verifier.rs:162-163`, the digest kimchi's own verifier absorbed); the key module's copy is
re-derived in-circuit by `keySponge` over the 56 `index_to_field_elements` coordinates. Two
INDEPENDENT sources for one number, welded by `keyRows`' closing `digestTie` — which is a gate, and
which reading either one twice would have made decoration.

⚠ **WHAT RE-EMITS:** everything above `w4_bind`. `index_digest` is the FIRST absorbed word, so
β/γ/α/ζ, the fork digest, all sixteen IPA prechallenges and every derived public word move.
`STEP_VK_DIGEST` survives as `KEY_REAL_BRANCH`'s digest — the branch this assembly no longer
selects and `key_digest_moves_with_the_branch_selection` still exhibits. -/
def RC_DIGEST : Nat := Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_VKDIGEST

/-! ### §2d — **THE FIXTURES, NAMED — AND THE LIST IS NOW SHORT.**

⚑ **`wrapFixture` NO LONGER REACHES ANY TRANSCRIPT ITEM.** Every one of the 116 Fq words this
transcript absorbs off the step proof — `sg_old` (4), `w_comm` (30), `z_comm` (2), `t_comm` (14),
`lr` (64), `delta` (2) — comes from `KimchiStepWrapChainFixture`, i.e. from an accepted
`ProverProof::create_recursive` over Mina's own 65,536-generator SRS. `lr` and `delta` were the
sharp end: until 2026-08-05 this docblock said they *"have no real source in this tree at all"* and
`KimchiWrapMainField.lrPointQ i = xhatBase (5 + i % 50)` made thirty-two of the thirty-three IPA
points fifty SRS Lagrange bases, cycled. An IPA opening **is** `lr` and `delta`, and the step proof
in this pipeline had carried one the whole time; nobody had read it off.

They are still FIXTURES **in this circuit** in the exact sense that matters and no other: no row
here DERIVES them. That is a statement about which sub-circuits are assembled (W-COMBINE's `~init`,
W-BULLET's consumers — §2c's census), not about where the numbers came from. The two items that are
not this step proof's at all are named in §2's `RC_*` block: `RC_DIGEST` (Mina's `step-transaction`
key) and `x_hat` (§15's MSM output).

⚠ `wrapFixture` survives as the `getD` TOTALITY default on the four commitment blocks — not a value
anything reads, since a fired default would mean the tape asked for a word past the end of a block
and `the_sourced_transcript_census_is_57_points` pins every length against the shape.
`lrPointQ`/`deltaPointQ` default to **`0`** instead, and the difference is deliberate rather than an
oversight: `(0, 0)` is kimchi's own flattening of the point at infinity (`sponge.rs:332-344`), it is
off `y² = x³ + 5`, and `the_transcript_points_are_on_vesta` therefore turns a fired default there
into a red rather than into a plausible-looking coordinate. -/
def wrapFixture (tag i : Nat) : Nat := (11 + 1000003 * (17 * tag + i)) % qN

/-- Item `i` of tag `t`'s VALUE.

⚠ ⚑ **TAG 2 (`x_hat`) IS NO LONGER HERE.** At `w6_xhat` the absorbed `x_hat` pair is
`xhatOutOf s.xhatEntries` — §15's MSM output — and `schedule` reads it directly, because `itemVal`
has no shape to read it with. `RC_XHAT` survives only as `xhat_derived_is_not_the_old_fixture`'s red control: the
value the transcript used to absorb, kept so the change is exhibited rather than merely asserted. -/
def itemVal (t i : Nat) : Nat :=
  match t with
  | 0 => RC_DIGEST
  | 1 => RC_SGOLD.getD i (wrapFixture 1 i)
  | 2 => RC_XHAT.getD i (wrapFixture 2 i)
  | 3 => RC_WCOMM.getD i (wrapFixture 3 i)
  | 4 => RC_ZCOMM.getD i (wrapFixture 4 i)
  | 5 => RC_TCOMM.getD i (wrapFixture 5 i)
  -- ⚑ **`lr` AND `delta` ARE CURVE POINTS SINCE `w11_bullet`, AND THAT IS A FLAG DAY.** They arrive
  -- upstream through `Openings.Bulletproof.typ`'s `Inner_curve.typ` (`wrap_main.ml:357-383`), so
  -- they are on-curve by construction; the `wrapFixture` filler that stood here was not, and
  -- `Scalar_challenge.endo_inv` (`scalar_challenge.ml:343-354`) has NO WITNESS over an off-curve
  -- `l` — its `res = [x⁻¹]·l` needs the group. These are real SRS Lagrange bases, which
  -- `MinaStepSrsLagrangePin` grounds against the devnet SRS and which cost no inversion to reduce. They are still FIXTURES and §2d still says so;
  -- what changed is that they are now fixtures of the right TYPE. What re-emits: every rung's
  -- witness, because the 16 prechallenges and `c` are squeezed AFTER these words. β/γ/α/ζ are
  -- squeezed before them, so §12a's reality gate does not move.
  | 7 => if i % 2 == 0 then (lrPointQ (i / 2)).1 else (lrPointQ (i / 2)).2
  | 8 => if i == 0 then deltaPointQ.1 else deltaPointQ.2
  -- ⚑ **TAG 6 (`combined_inner_product`) IS MEASURED SINCE 2026-08-05.** `wrap_verifier.ml:395` is
  -- `absorb_shifted sponge advice.combined_inner_product`, and `advice.combined_inner_product` IS
  -- Mina slot 0 — so the word this tape absorbs and the word the public vector carries are ONE
  -- object upstream, and were two numbers here while this fell through to `wrapFixture`. It now
  -- carries `expand_deferred`'s own value, in the `Shifted_value.Type1` representation
  -- `absorb_shifted` expects and `prepared_statement.rs:99` pushes.
  -- ⚠ What re-emits: every rung's witness from `w4_bind` up. T_CIP is absorbed at `schedule`'s
  -- `:291`, AFTER the fork squeeze and BEFORE `u = group_map t`, so the 16 IPA prechallenges and `c`
  -- move with it; β/γ/α/ζ and the fork digest are squeezed earlier and do NOT.
  | 6 => DEF_CIP
  | _ => wrapFixture t i

/-- **THE EVENT LIST**, in `wrap_verifier.ml`'s own order.

⚑ **`x_hat` IS DERIVED HERE.** `wrap_verifier.ml:539-616` computes the MSM and `:617` absorbs its
output, and the MSM reads no sponge state — so the schedule can and must carry §15's value. Before
`w6_xhat` this slot held `RC_XHAT`, a real proof's public-input commitment standing in for a value
no row computed. -/
def schedule (s : WrapShape) : List Ev :=
  [ Ev.abs T_DIGEST RC_DIGEST ]
  -- ⚑⚑ **`WH_REAL_SLOTS`, NOT `s.maxPrevs` — THIS IS THE ONE PLACE THE TRANSCRIPT WANTS
  -- `actual_proofs_verified`, AND IT IS SHAPE-INDEPENDENT.**
  --
  -- `wrap_verifier.ml:511-514` masks the `Max_proofs_verified`-long `sg_old` with
  -- `actual_proofs_verified_mask` and `:538` absorbs it through an `Opt` sponge. A `keep = false`
  -- absorb is a NO-OP on the state, and that is upstream's own statement rather than a reading of
  -- ours: `opt_sponge.ml`'s `let%test_unit "correctness"` asserts the opt sponge's squeeze equals a
  -- plain sponge over `List.filter_map ps ~f:(fun (b, x) -> if b then Some x else None)`.
  -- `wrap.rs:2280-2300` is the same shape (`absorb_curve` → `OptSponge::absorb ((b, x))`).
  --
  -- So the RECORD has `WH_PADDED` slots and the TAPE carries `WH_REAL_SLOTS` points — the kept
  -- SUFFIX, because `pad_messages_for_next_wrap_proof` PREPENDS (`wrap.rs:476-491`) and
  -- `ones_vector … |> Vector.rev` puts the zeros at the front. `whNPad` is that offset.
  ++ (List.range (2 * WH_REAL_SLOTS)).map (fun i =>
       Ev.abs T_SGOLD (itemVal T_SGOLD (2 * whNPad WH_REAL_SLOTS + i)))
  ++ [ Ev.abs T_XHAT s.xhatXY.1, Ev.abs T_XHAT s.xhatXY.2 ]
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

The step side reached `UNWIRED_ITEMS = ∅` after eight rungs. This file is at rung five, and the
honest statement is that **every COMMITMENT word the transcript absorbs is absorbed and NOT YET
CONSUMED**, because the sub-circuits that consume them — W-XHAT (`x_hat`), W-COMBINE (`sg_old`,
`z_comm`, `w_comm`, `t_comm`), W-BULLET (`lr`, `delta`, `combined_inner_product`) — are §13's
named-and-not-assembled list. Padding the count, or wiring a commitment to a gadget that merely
re-reads it, is metric-gaming; the count is reported as it is.

⚠ ⚑ **`x_hat` DID NOT LEAVE THIS LIST AT `w6_xhat`, AND THE ENTRY WAS REWRITTEN RATHER THAN
DELETED.** §15 emits the whole MSM and `wrap_verifier.ml:617`'s absorbed pair IS the ladder's output
— `x_hat` is no longer a value the prover hands the sponge. But the 67 SCALARS that MSM consumes are
the packed previous STEP statement, which `wrap_main.ml:201-256` obtains by
`exists ~request:Req.Proof_state`; they are free here and free upstream, and what ties them there is
W-FINALIZE, W-WRAPHACK and `assert_eq_plonk`. An MSM over free scalars spans the group, so the
prover's reach into the transcript is UNCHANGED in size and only changed in shape. Striking the
entry on the strength of "a sub-circuit now computes it" is exactly the metric-gaming this census
exists to refuse. The count stays **8**.

⚑ **`index_digest` LEFT THIS LIST AT `w5_key` AND IT LEFT BY BEING DERIVED.** §14 emits `choose_key`
and the index sponge, and `keyRows`' closing tie puts the squeeze and the transcript's first absorbed
word in ONE σ class; `key_digest_is_the_index_digest` pins the value against a digest Rust kimchi
computed for the same index. ⚠ Below `w5_key` the digest is still a free witness at §2d's value —
the rung, not the file, is what closed it. -/
def WRAP_UNCONSUMED : List String :=
  [ "sg_old — ON-CURVE at w9_prev (§18), HASHED at w11_wraphack (§21) into packed statement \
     words 55/56; still a FREE witness, and its consumer is W-COMBINE's ~init"
  , "x_hat — MSM EMITTED at w6_xhat (§15); its 67 SCALARS are W-PREV's packed statement words, \
           and 64 of them are still free"
  , "w_comm — CONSUMED at w10_combine (§23), one fold step each"
  , "z_comm — CONSUMED at w10_combine (§23)"
  , "t_comm — ft_comm EMITTED at w8_ftcomm (§17); its OUTPUT is W-COMBINE/W-BULLET's"
  , "combined_inner_product — CONSUMED at w11_bullet (§24) as `uc = scale_fast u cip`'s scalar. \
           ⚠ Its VALUE is still W-FINALIZE's, so what closed is the READ, not the derivation"
  , "lr — CONSUMED at w11_bullet (§24): 32 endo ladders, plus `Inner_curve.typ`'s on-curve check"
  , "delta — CONSUMED at w11_bullet (§24): `lhs = Scalar_challenge.endo q c + delta`" ]

/-- ⚑ **THE CENSUS'S KEYS, SEPARATED FROM ITS PROSE — and the separation is a repair, not tidying.**

Three lanes edit `WRAP_UNCONSUMED`'s entry TEXT concurrently, and five theorems pinned whole strings
out of it. Every one of them went red the moment a lane reworded WHY a word is unconsumed, which is
the one part of an entry that is *supposed* to change as sub-circuits land. Worse, the two pins that
tried to be robust by using `String.startsWith` did not go red — they got **STUCK**: `String.startsWith`
is well-founded recursion over a `String.Iterator` and does not kernel-reduce, so `decide` could
neither prove nor refute them and the tactic failed for a reason that looks nothing like the fact
being false.

So the identity of the census lives here, as a list of KEYS that no lane has a reason to reword, and
the pins are `rfl` over `getD` on THIS list. The prose above stays the lanes' to maintain; a pin on
it is a pin against a moving target. ⚠ The two lists are kept in step by `unconsumed_keys_match_the_census`
below — the count only, because relating a key to its own entry needs exactly the string operation
that does not reduce. That is the residual and it is stated rather than papered over. -/
def WRAP_UNCONSUMED_KEYS : List String :=
  [ "sg_old", "x_hat", "w_comm", "z_comm", "t_comm", "combined_inner_product", "lr", "delta" ]

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

/-- ⚑ **THE ABSORBED WORD'S VALUE, READ OFF THE EMITTED TRACE** — the value-layer twin of the
`(sp.evs.filter (·.isAbs && ·.tag == tag)).wordV` that every consuming sub-circuit already uses for
its VARIABLE, and the single source both layers now share.

⚠ **THIS EXISTS BECAUSE THE TWO LAYERS DISAGREED, AND THE DISAGREEMENT WAS INVISIBLE HERE.**
`combPtVal`, `bullCipVal`, `bullLrVal`, `bullDeltaVal`, `prevEnv`'s `assert_on_curve` intermediates
and `whSpongeP`'s tape all answered with `itemVal` — `PastaPoseidonFq`'s borrowed
`create_circuit(0,5)` proof — **whatever tape drove the `WrapData`**. For a `WrapData` whose `sp` is
`runSpongeQ … (schedule s) …` that is invisible, because `schedule` absorbs `itemVal`: value and
variable agree by coincidence of source, not by construction. For `KimchiStepWrapChain.tChain`,
whose `sp` is driven by dregg's own step proof's tape, they DISAGREED — a `.combine` emission would
have folded one proof's commitments over cells holding another's, and its honest witness would fail
`CompleteAdd`. `bullCipVal tChain` was `102000317`, a `wrapFixtureQ` filler, against an absorbed
`combined_inner_product` of 24039349238365581886618386413466944030470576020951420730767724460078234281349.

Reading the trace makes the agreement STRUCTURAL: the value a gadget computes over and the cell it
computes in are one object, for every `WrapData`, including one whose tape is bent. It is
byte-neutral wherever `sp` came from `schedule` — which is every previously emitted rung — so
nothing below re-emits. -/
def absVal (sp : SpAcc) (tag i : Nat) : Nat :=
  ((sp.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).word

/-- …and the pair, at item `2i`/`2i+1`, which is how every commitment family is read. -/
def absPtVal (sp : SpAcc) (tag i : Nat) : Nat × Nat := (absVal sp tag (2 * i), absVal sp tag (2 * i + 1))

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

/-! ⚑ `x⁻¹` over `Fq` is `KimchiWrapMainField.qInv` since `w6_xhat` — one definition, not two.

⚠ The version that used to live here was `if x == 0 then 0 else qPow x (qN - 2)`, and `qPow` above
is WELL-FOUNDED recursion (`decreasing_by simp_wf; omega`). That is fine for the interpreter and
hostile to the kernel: `WellFounded.fix` does not reduce by `rfl` without unfolding its accessibility
proof. Every ladder cell in §15 is three inverses deep, so the Field module's FUEL-BOUNDED
`qPowAux` is what a `decide` can actually reach. `qPow` stays because `Field.equal`'s witness layer
below still calls it and nothing kernel-reduces that. -/

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
(`wrap_main.ml:179-180`, `Nat.N2` at `:195`).

⚑ **IT IS `WH_PADDED` AND NOT A THIRD COPY OF `2`.** `Wrap_hack.Padded_length` and
`Max_proofs_verified.n` are one number upstream (`wrap_main.ml:423` hashes the closing record at
`Max_proofs_verified.n`), and this file held them as two literals until 2026-08-07. -/
def MASK_N : Nat := WH_PADDED

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

/-! ### ⚑ **WHICH ENTRY OF `step_keys` EACH COMPILED STEP RULE HOLDS.**

`wrap_main.ml:98-101` makes `step_keys` a per-branch vector of the compiled STEP rules'
verification keys, and this tree has TWO of them. The two indices live HERE, above `mkWrapWith`,
because the committed `WrapData` selects one of them; §14 is where the keys themselves are. -/

/-- ⚑ Mina's `step-transaction` key's entry. ⚠ **This assembly no longer selects it.**
`key_digest_moves_with_the_branch_selection` is where it is still exercised, and
`chain_step_rule_is_a_second_real_key` is where its coordinates are pinned apart from dregg's. -/
def KEY_REAL_BRANCH : Nat := 1

/-- ⚑⚑ **AND WHICH ENTRY HOLDS DREGG'S OWN STEP RULE** — the circuit `KimchiStepMain` assembles and
`EmitStepMainJson` emits, whose accepted Vesta proof drives this transcript.

⚑ **THIS BRANCH IS WHAT MAKES THE TWO HALVES COMPOSE, AND IT IS `choose_key`'s OWN MECHANISM.**
`keyRows`' closing `digestTie` welds the index sponge's squeeze to the transcript's FIRST absorbed
word, so a wrap circuit can only verify a step proof whose verifier index is the key it committed
to. Before 2026-08-05 there was exactly one real entry — Mina's — while the tape was dregg's, and
that single row is why `KimchiStepWrapChain` stopped at `w4_bind`: not W-COMBINE, not W-BULLET. Two
step rules in one `step_keys` vector is not a workaround for that; it is what `step_keys` IS.

⚑ **AND SINCE 2026-08-06 `mkWrapWith` SELECTS IT** — the chain's setting is the assembly's, which
is what collapsed `shapeChain` into `shapeWrap`. -/
def KEY_CHAIN_BRANCH : Nat := 2

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
`external 0 .. WRAP_PRIMARY_LEN-1` — **MINA'S forty slots**, in Mina's own numbering — so
`placeChecked`'s H1 cannot fire and its H2, an inert public word, is the real gate on the closing
rungs.

⚑ **THIS USED TO BE `pubWords + 2`, AND THE `+ 2` WAS A DEAD GAP.** When the public vector was this
assembly's own dense one, the two slots above it were RESERVED (so the aux ids started above them)
and any gate that touched them was refused as `referenceInGap`; that is how a rung was stopped from
exposing a word it does not derive. With the vector in MINA'S layout there is no gap left to
reserve: every rung declares all forty and the same refusal is now H2's, at the exact Mina slot.
`prev_rung_places_and_the_rung_below_it_does_not` and
`wraphack_rung_places_and_the_rung_below_it_does_not` still exhibit both refusals — at slots 12 and
11 rather than at `pubWords` and `pubWords + 1`, which is the same fact said in Mina's coordinates.

⚠ Every circuit variable id therefore moves by `40 - (pubWords + 2)`. Nothing emitted moves with it:
`place` maps VARIABLES to cells through their equivalence classes, and an id is only an identity. -/
def AUXW (_s : WrapShape) : Nat := WRAP_PRIMARY_LEN

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

/-- The committed branch instance: `KEY_CHAIN_BRANCH` of `branches`, widths `[0,1,2,…]`, and the
per-branch STEP domain `Branch_data.domain_log2` packs.

⚑⚑ **THE SELECTION MOVED OFF `min 1 (branches − 1)` ON 2026-08-06, AND IT IS THE FIRST OF THE TWO
EDITS THAT MADE THIS ASSEMBLY DERIVE MINA'S FORTY.** `keyRows`' closing `digestTie` welds
`choose_key`'s index-sponge squeeze to the transcript's first absorbed word, which is `RC_DIGEST` —
dregg's own step key's digest. A wrap `WrapData` selecting Mina's `step-transaction` entry has no
satisfying witness for that row on this tape, whatever anything downstream does, because the digest
is absorbed BEFORE β.

⚑ Two derived words follow the selection and neither is decoration:

  * ⚑⚑ `fz = widths.getD KEY_CHAIN_BRANCH = WH_REAL_SLOTS = 1`, so
    `Branch_data.proofs_verified` packs as **`N1`** — mask `[0, 1]`, `Field.pack = 2`, and Mina's
    public slot 29 is `4·domain_log2 + 2`.
    ⚠ **IT WAS `2` UNTIL 2026-08-07 AND THAT MADE SLOT 29 AGREE ON A WRONG NUMBER.** `first_zero`
    is `Pseudo.choose (which_branch, step_widths)` (`wrap_main.ml:173-180`) — the SELECTED branch's
    `actual_proofs_verified`, the same quantity `wrap.rs:666` reads off the step record — and
    dregg's step rule assembles ONE `verify_one`. `proofs_verified.ml:70-78` gives
    `Prefix_mask.there N1 = [false; true]` and `prepared_statement.rs:131-139` packs `N1 => 0b10`,
    so the honest word is 58 and not 59. It read 59 on BOTH sides because the referee's own
    `pickles_kimchi_marshal` hardcoded `PicklesBaseProofsVerifiedStableV1::N2` while its
    `gates::STEP_RULE_N_PREVIOUS` docblock already said `Prefix_mask.there N1`. Two wrong sides
    agreeing is not agreement, and this is the one slot in the forty where that was true;
  * `logs.getD KEY_CHAIN_BRANCH = STEP_DOMAIN_LOG2`, the domain `kimchi::verifier` proved that rule
    at. **Every entry used to be `16`** — `Common.Max_degree.step_log2`, Mina's `step-transaction`
    domain and the SRS depth, which is right for `KEY_REAL_BRANCH` and describes a different
    circuit here. `branchDataPacked` is `4·domain_log2 + Field.pack mask`, so this is Mina's public
    slot 29 and nothing else in the vector reads it. -/
def mkWrapWith (s : WrapShape) (bt bw : Nat) : WrapData :=
  { sh := s
  , sp := runSpongeQ (baseSp s) (schedule s) bt bw
  , br := runBranch s (min KEY_CHAIN_BRANCH (s.branches - 1))
            -- ⚑ per-branch `actual_proofs_verified` (`step_widths`, `wrap_main.ml:130-133`).
            -- ⚠ `KEY_CHAIN_BRANCH`'s is dregg's own rule's — `WH_REAL_SLOTS`, ONE — and not
            -- `min 2 i`'s saturation at `Max_proofs_verified`; that saturation is what packed
            -- `branch_data` as `N2` for a one-`verify_one` rule.
            ((List.range s.branches).map (fun i =>
              if i == KEY_CHAIN_BRANCH then WH_REAL_SLOTS else min WH_PADDED i))
            ((List.range s.branches).map (fun i =>
              if i == KEY_CHAIN_BRANCH then
                Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_DOMAIN_LOG2
              else 16)) }

/-- The HONEST instance — `mkWrapWith` at a bend index that cannot name any event.

⚠ ⚑ **THIS SENTINEL WAS COUNTED IN THE WRONG NUMBERING, AND AT `shapeWrap` IT ZEROED A REAL
ABSORBED WORD.** It was `nItems s + 1`. `nItems` counts **absorbs only**; `runSpongeQ` compares `bt`
against `ei.2`, the index in the **full event list**, which interleaves absorbs and squeezes. So the
"out of range" sentinel is only out of range when `nItems s + 1 ≥ (schedule s).length`, which is
false for every shape this file has:

  * `shapeSmoke` — `nItems = 34`, sentinel `35`, events `44`. Index 35 lands on a **squeeze**, and
    the override only reads in the `.abs` branch, so it was harmless. **That is why it was never
    seen**, and it is luck, not design.
  * `shapeWrap` — `nItems = 120`, sentinel `121`, events `143`. Index 121 is an **absorb**:
    `T_LR` item 49, i.e. round 12's `L.y`. Its word was replaced by `bw = 0`, so `bullLrVal t 12 0`
    read `(x, 0)` — a point off `y² = x³ + 5`. `endoInvPtQ`'s `vestaScMul` then hit a degenerate
    Jacobian (`Z = 0`), returned `(0, 0)` through its silent fallback, and the emitted witness was
    unsatisfiable. **The prover reported it as `Prover("rest of division by vanishing polynomial")`
    — three layers from the cause, and pointing at W-BULLET rather than at this line.**

⚑ **MEASURED, not deduced:** of the 116 words the transcript sources, `absVal ≠ itemVal` at
**exactly one index** — `T_LR 49` — and nowhere else, at any tag.

⚠ It is **pre-existing** and independent of whose step proof the transcript carries: the zeroing
happens in the trajectory, whatever value the schedule offers. It was invisible because the WRAP
shape had never been proved — the accepted artifact is the smoke one, where the sentinel misses.

The sentinel is now `(schedule s).length`, which is one past the last valid index **in the numbering
`runSpongeQ` actually uses**, so no event can match it at any shape. -/
def mkWrap (s : WrapShape) : WrapData := mkWrapWith s (schedule s).length 0

/-- W2's rows: the shared endo pin, then a `to_field_checked` chain per `chal` squeeze and an
`assert_128_bits` chain over each one's HIGH part. -/
def challengeRowsQ (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let cb := baseCh s t.sp
  let sq := chalSqueezes t.sp
  endoPinRow cb
  ++ (List.range (nChals s)).flatMap (fun c =>
      let e := sq.getD c (PVAR_NOWHERE, 0)
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
      let e := sq.getD c (PVAR_NOWHERE, 0)
      let lo := e.2 % 2 ^ CHAL_BITS s
      let hi := e.2 / 2 ^ CHAL_BITS s
      chainEnv s (chainVars s (cb + 1) c) lo hi
      ++ chainEnv s (chainVars s (cb + 1) (nChals s + c)) hi 0)

/-! ## §14 — ⚑ **W-KEY**: `choose_key` + the index sponge, and the transcript's INPUT.

`wrap_main.ml:215-220` → `wrap_verifier.ml:189-204`, then `wrap_verifier.ml:521-530`. Read end to
end at source, W-KEY is **two** things and only the first is named `choose_key`:

  * **`choose_key which_branch step_keys`** (`wrap_verifier.ml:189-204`) —
    `Vector.map2 (bs :> (Boolean.var, n) Vector.t) keys ~f:(fun b key -> map key ~f:(fun g ->
    Double.map g ~f:(( * ) (b :> t))))` reduced by `map2 ~f:(Double.map2 ~f:( + ))` and closed by
    `map ~f:(Double.map ~f:(Util.seal (module Impl)))`. ⚑ **The keys are `Inner_curve.constant`**
    (`wrap_main.ml:218-219`), so this is NOT a curve MSM: every `b · g` is a Boolean var times a
    CONSTANT coordinate, i.e. plain `Generic` arithmetic. 28 points × 2 coordinates × `branches`.
  * **the INDEX SPONGE** (`wrap_verifier.ml:521-530`) — a FRESH `Sponge.create sponge_params`
    absorbing `Types.index_to_field_elements ~g:(Inner_curve.to_field_elements) m` one element at a
    time, then ONE `Sponge.squeeze_field`. Its output is `index_digest`, and `:537` absorbs it as
    the wrap transcript's FIRST item. **This is why W-KEY is what unblocks the transcript's input.**

⚑ **THE FLATTENING ORDER IS NOT ALPHABETICAL AND NOT THE STRUCT ORDER OF THE VK JSON.**
`Pickles_base.Side_loaded_verification_key.index_to_field_elements` (`side_loaded_verification_key
.ml:159-183`) is exactly

    Vector.to_list sigma_comm        (`Plonk_types.Permuts_vec` — 7)
    @ Vector.to_list coefficients_comm (`Plonk_types.Columns_vec` — 15)
    @ [ generic_comm; psm_comm; complete_add_comm; mul_comm; emul_comm; endomul_scalar_comm ]

mapped by `~g` and `Array.concat`ed. 28 points, `~g z = [x; y]`, **56 field elements**.

⚠ ⚑ **AND THE FOLD IS ROWS HERE AND ZERO ROWS UPSTREAM.** Because the keys are constants,
`Checked.mul` takes its `Constant` branch (`snarky/src/base/utils.ml:81-88`) and Snarky spends
NOTHING on the 28 × 2 × `branches` multiplications and adds; the only rows `choose_key` costs
upstream are `Util.seal`'s one per coordinate (`util.ml:65-76`). This file emits the fold, so every
partial sum is a constrained variable. That is STRICTER and it is recorded in §13's stricter-than-
upstream list — it is not a conformance claim, and the wrap conformance report shows it as the
`[K 0 -1 0 0] × 56` family.

⚑ **AND THE POINT COUNT IS A KIMCHI CONSTANT, NOT A `WrapShape` FIELD.** `Permuts.n = 7` and
`Columns.n = 15` are fixed by the proof system, so `KEY_COORDS = 56` at BOTH the smoke and the wrap
shape. `shapeSmoke.wComms = 3` shrinks the TRANSCRIPT's witness-commitment block; it is not a claim
that `Columns.n` is 3. Scaling the index down with it would have made the reality gate below
unreachable at the shape the pins actually run on.

### ⚑ THE REALITY GATE, AND THE ONE PLACE IT COULD HAVE BEEN THE WRONG OBJECT

`STEP_VK_XY` below is the 56 coordinates of **MINA'S OWN `step-transaction` VERIFICATION KEY** —
branch 0 of the transaction SNARK, the step rule this wrap circuit exists to verify — dumped in
`index_to_field_elements` order by `fixtures/kimchi-extractors/step_vk_index_export.rs`, whose output
is `metatheory/kimchi_step_key_index.json`. The input is o1-labs' RELEASED gate blob
(`circuit-blobs/berkeley-devnet`, md5 `c33ec5211c07928c87e850a63c6a2079` — the release filename IS
the OCaml constraint-system digest), 17 806 rows at 67 public inputs, which openmina independently
transcribes as `StepTransactionProof {PRIMARY_LEN 67, ROWS 17806}`.

⚑ **AND MINA'S OWN WRAP CIRCUIT BAKES THESE 56 NUMBERS IN, WHICH IS THE PIN.** `choose_key`
(`wrap_verifier.ml:189-204`) holds `step_keys` as `Inner_curve.constant`, so the coordinates appear
as literal gate coefficients of the compiled wrap. Measured by the extractor, which REFUSES on
disagreement: **56/56 of them occur among `wrap-transaction`'s 995 distinct coefficients, and 0/56
among `wrap-blockchain`'s 584** — the second leg is what makes it a check and not a birthday
coincidence, since the blockchain wrap wraps the blockchain step rules. Two independently released
artifacts, one key.

⚠ **Rust kimchi's `VerifierIndex::digest` is NOT `index_to_field_elements` in general.**
`kimchi/src/verifier_index.rs:451-530` absorbs the same eight fields in the same order, and THEN
`range_check0/1`, `foreign_field_add/mul`, `xor`, `rot` and the whole `lookup_index` **when they are
present**. Pickles' `Plonk_verification_key_evals.t` has no such fields, so the two agree only for
an index that carries none of them. The extractor **asserts** that every optional commitment and the
lookup index is `None` before it dumps — otherwise these 56 numbers would be a prefix of the digest
preimage wearing the name of the whole of it, which is this campaign's own recorded defect.

## ⚠ ⚑ THIS KEY REPLACED A DEGENERATE ONE, AND THAT IS A FLAG DAY — READ IT

Until 2026-08-04 `STEP_VK_XY` was kimchi's **own generic-gate test circuit** — `create_circuit(0, 5)`
through `new_index_for_test_with_lookups`, dumped by `wrap_key_index_export.rs`. That circuit has no
Poseidon, CompleteAdd, VarBaseMul, EndoMul or EndoMulScalar row and writes only 8 of the 15
coefficient columns, so **seven of its 28 commitments were the point at infinity** — coefficient
columns 3, 6, 10, 11, 12, 13 and 14. The cause is exact and is at
`kimchi/src/verifier_index.rs:230-238`: `sigma_comm` and `coefficients_comm` are committed with
`commit_evaluations_non_hiding`, **unmasked**, so a zero column lands on the identity; the six
selectors below them go through `mask_fixed` with blinder 1, so a zero selector lands on the SRS
blinding base `h` instead — which is why five of that key's singles were the same point, and that
point was `MinaStepSrsLagrange.URS_H_XY`.

`index_to_field_elements` flattens infinity as the FAKE POINT `(0,0)` (`DefaultFqSponge::absorb_g`,
`poseidon/src/sponge.rs:332-345`), W-COMBINE folds the 28 points with `Ops.add_fast` — the INCOMPLETE
add — and a chord through `(0,0)` is not on `y² = x³ + 5`. So `combined_polynomial` was off-curve,
`p_prime`, `q`, `cq` and `lhs` inherited it, and `wrap_main.ml:419`'s
`Boolean.Assert.is_true bulletproof_success` had **no satisfying witness at all**: the honest
`G := z₁⁻¹(lhs − z₂H) − b·u` solve needs an on-curve `lhs` to land on. It was the FIXTURE, not the
gadget, and §24's header carried that finding for one day before this key closed it.

**WHAT RE-EMITS:** everything. `index_digest` is the wrap transcript's FIRST absorbed word
(`wrap_verifier.ml:537`), so every squeezed challenge, every derived public word and every rung's
witness moves. `STEP_VK_DIGEST` replaces `PastaPoseidonFq.VKDIGEST` as `RC_DIGEST`; the two were
welded only because the old key happened to be the index that fixture's proof was made against.
§12a's reality gate is UNTOUCHED — it drives a separate sponge over that proof's own tape, and
`PastaPoseidonFq.VKDIGEST` is still the head of it, which is the correct object for that gate. -/

/-- `Plonk_types.Permuts.n` — `sigma_comm`'s length. -/
def KEY_SIGMA : Nat := 7
/-- `Plonk_types.Columns.n` — `coefficients_comm`'s length. -/
def KEY_COLS : Nat := 15
/-- `generic_comm`, `psm_comm`, `complete_add_comm`, `mul_comm`, `emul_comm`, `endomul_scalar_comm`. -/
def KEY_SINGLES : Nat := 6
/-- The points `index_to_field_elements` flattens. -/
def KEY_POINTS : Nat := KEY_SIGMA + KEY_COLS + KEY_SINGLES
/-- …and the field elements the index sponge absorbs, at `~g z = [x; y]`. -/
def KEY_COORDS : Nat := 2 * KEY_POINTS

/-- ⚑ **MINA'S `step-transaction` VERIFICATION KEY, FLATTENED.** `metatheory/kimchi_step_key_index
.json`, `index_comm_xy` — 56 Fq coordinates in `index_to_field_elements` order. The extractor
asserts, in Rust: that no optional commitment and no lookup index is present; that **none of the 28
points is the identity**; that the SRS it committed against has `h = MinaStepSrsLagrange.URS_H_XY`,
so this is the STEP URS the x_hat MSM already runs on; that all 56 coordinates occur as
`wrap-transaction` gate coefficients and NONE occurs in `wrap-blockchain`; and that an independent
`absorb_fq` replay over exactly these 56 numbers reproduces `verifier_index.digest::<BaseSponge>()`,
so the list is the digest's preimage rather than a second copy of some coordinates. -/
def STEP_VK_XY : List Nat :=
[
  7838087279879676988487524620018877099697850333536108594890305181134476064109, 6862458903183076358794804158815719092069743952414443701796013163943330780886, 21569770123320958997141546748269312575599811482377528453067296363263509355160, 14831154974989574843865288625259329553643196642542558606202890285470699918383,
  3560450003512249024409829945285052200733803457856555953541880567009457529941, 21300440324491612702438114091755179103724859179797933308254392224248452634198, 27811548696859300672030920370491524663871233726404568842157093983436742351790, 1019005569818862979818515017915427357531367052099945156164116380307024580822,
  26806482625388101877865595690247158683969662175939617638680733272824795520600, 20807048512676894705070190745423807476394776417488119995584790564879906625550, 4264921334837211813523473596106659753780429242059460249028903670194047444859, 15002824747260430568018596693971462363413716130450885434092317522975368885083,
  9973737635982028161229945394735368614595826208720132528626693541866367064730, 16659983257260110859039822567874232195774207251037813693410305820458243284408, 6789171475125240853106418159619911679547993077039670979696986007339761837963, 9954962990733376247478547393614381021734444402551376939777273613821496057163,
  20441985299479206844856618377502721386546485981104536189177508596763081613846, 8437013323026492242835746190639999279940648822570426142081354060059597581354, 7428444655971501060314217372484428511951982333145045518108400976108376363414, 14964834431185989489044468659340852205684700893168630975786671472036071611623,
  11003199762419203965178628795408442038044740124278653514016456446516605881389, 24295953863481597447043611018977063350795404043491089551371918032778736488583, 23209251104262728415991697618120051317993574566580727430451243398730303885509, 27871326997877373287941141073908256466130775246153087971101975248713771958196,
  14733450161582593406877278657140958916205965759158250410954950808860069381600, 4373252547534122630906505992479353093090205058461560044958206946818920929159, 2414776948690910771466703311103896306893508714970431281994316441460480355270, 18059676002121798624789491098740021239957823038165119492651077911753051580827,
  13989863828120645283890262231662545934119019705549233995221856532838452175342, 14357490266021739134916759742795636242761766133521234852967225526090908171625, 4767918159193249017153143429329706708556268933477552723804974643215431065699, 7716082504585394456849865359945150483547335864125586464941318802937186312598,
  24977425038157702399148147775397729352308687538526000284810585132652947534036, 12744816833487249843437985908205002162615373239400952061299483211869107849182, 11059547395811712232277984980108008802362989976094718193158581914943611537369, 22392709934111142868429807112448426168132179721445499650123144170456559762110,
  12308879040194379789595637963739559587788945735249459474541295465767102094943, 16913494992236477182403705531101361400832188323022474017688573878570805298259, 1108939583278668348735941230120457730006347969722607769862817764301566439293, 18867148946624578488604077886301147760211655910964942745930560496217255397061,
  24011126098988602671910387116937753816234144577820719437376506993486031316621, 18560717796954544475185179396456927010146736365913713783711218177005996649611, 25193222744664952841564739090004189114337884494344796110684543247362396029933, 6751793767093906846141277563468135897565712435126409584454802214774747456090,
  25155928172182760879570967334854982065796984066472662203442437861526155449412, 11652429192093861033924657190627873179752162738595026112334026099149954614968, 3257648458652036328358617834555037576116682576201252973846584715201501429220, 7909179644321276961050844815424388529013106586525611413036608508886302802213,
  6112345133339187774424965719472681942223308075989306910616908574075076689837, 27349563440527400850628712495340704438886226561321588757627527101101858081586, 7460570426237314259837285873223905596811295885898345835344619846043062276989, 9878879395752744355402770915411675925276816629622263160718393689597676814917,
  4129260839752076466596086431914048517141014770261954927508289257654980391346, 26308296295204227453552650644860782362357850810154305358229728558512579255099, 24502611438695320232273002947412396906059627211521155699290420437119200351654, 27688738592432713487369312650930096659220848921637869873729171969431898187759
]

/-- Branch `i`'s coordinate `k`. ⚠ `KEY_REAL_BRANCH` and `KEY_CHAIN_BRANCH` are real compiled step
rules; §2d names the rest. -/
def keyConst (i k : Nat) : Nat :=
  if i == KEY_REAL_BRANCH then STEP_VK_XY.getD k 0
  else if i == KEY_CHAIN_BRANCH then
    Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD k 0
  else wrapFixture (64 + i) k

/-- Item tag for an index-sponge coordinate. -/
def T_INDEXPT : Nat := 9

/-- The index sponge's schedule at branch `i`: 56 absorbs of the CHOSEN key, then one full squeeze
(`Sponge.squeeze_field`, `wrap_verifier.ml:530`).

⚠ ⚑ **THIS TOOK NO BRANCH UNTIL 2026-08-05, AND THAT WAS A LATENT DEFECT, NOT ONLY A LIMITATION.**
It absorbed `keyConst KEY_REAL_BRANCH` unconditionally while `keyEnv`'s one-hot fold outputs
`keyConst t.br.idx`, and `keyRows`' `sealHalves` ties the two together — so W-KEY had a satisfying
witness ONLY at `t.br.idx = KEY_REAL_BRANCH`. Every `WrapData` in the tree happened to select
branch 1, so the whole `choose_key` fold was decoration: a one-hot selector over five entries whose
sponge ignored the selection. `key_sponge_absorbs_the_selected_branch` is the pin that it no longer
does, and `key_digest_moves_with_the_branch_selection` is the red control. -/
def keySchedule (i : Nat) : List Ev :=
  (List.range KEY_COORDS).map (fun k => Ev.abs T_INDEXPT (keyConst i k))
  ++ [ Ev.sq .full ]

/-- W-KEY's accumulator variables: `acc k i = Σ_{j ≤ i} bⱼ · C_{j,k}`. -/
structure KeyVars where
  acc : Nat → Nat → PVar

def keyVars (s : WrapShape) (base : Nat) : KeyVars :=
  { acc := fun k i => .external (base + k * s.branches + i) }

def nKeyAccVars (s : WrapShape) : Nat := KEY_COORDS * s.branches

/-- The key region starts after the branch region, so nothing below `w5_key` moves. -/
def baseKey (s : WrapShape) (sp : SpAcc) : Nat := baseBr s sp + nBranchVars s
def baseKeySp (s : WrapShape) (sp : SpAcc) : Nat := baseKey s sp + nKeyAccVars s

/-- The index sponge's trajectory at branch `i`. `bt` is out of range, so no word is bent. -/
def keySponge (s : WrapShape) (sp : SpAcc) (i : Nat) : SpAcc :=
  runSpongeQ (baseKeySp s sp) (keySchedule i) (KEY_COORDS + 1) 0

/-- …and one with coordinate `k` bent by `+d`, for the red control. -/
def keySpongeBent (s : WrapShape) (sp : SpAcc) (i k d : Nat) : SpAcc :=
  runSpongeQ (baseKeySp s sp) (keySchedule i) k (qAdd (keyConst i k) d)

/-- `index_digest`'s VARIABLE — the squeeze's source cell. -/
def keyDigestVar (s : WrapShape) (sp : SpAcc) (i : Nat) : PVar :=
  (((keySponge s sp i).evs.filter (fun e => !e.isAbs)).getD 0 default).srcV
/-- …and its VALUE. -/
def keyDigestVal (s : WrapShape) (sp : SpAcc) (i : Nat) : Nat :=
  (((keySponge s sp i).evs.filter (fun e => !e.isAbs)).getD 0 default).val
def keyDigestValOf (a : SpAcc) : Nat :=
  ((a.evs.filter (fun e => !e.isAbs)).getD 0 default).val

/-- **W-KEY's ROWS.** The index sponge (whose `init` rows PIN the fresh state to zero — defect
class 1 in a new place), then `choose_key`'s one-hot folds, the `Util.seal` that makes each fold
output the sponge's absorbed word, and the tie that makes the squeeze the TRANSCRIPT's first
absorbed word. -/
def keyRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let kv := keyVars s (baseKey s t.sp)
  let bv := branchVars s (baseBr s t.sp)
  let ks := keySponge s t.sp t.br.idx
  let b := s.branches
  -- `Vector.map2 … ~f:(fun b key → g * (b :> t))` then `Vector.reduce_exn ~f:(+)`, per coordinate.
  let foldHalves : List (List (Option PVar) × List Int) :=
    (List.range KEY_COORDS).flatMap (fun k =>
      (List.range b).map (fun i =>
        if i == 0 then
          ([some (bv.bit 0), none, some (kv.acc k 0)], [(keyConst 0 k : Int), 0, -1, 0, 0])
        else
          ([some (kv.acc k (i - 1)), some (bv.bit i), some (kv.acc k i)],
           [1, (keyConst i k : Int), -1, 0, 0])))
  -- ⚑ `Util.seal` FUSED WITH THE ABSORB: the sealed variable IS the index sponge's absorbed word,
  -- so no coordinate reaches the sponge as a free witness.
  let sealHalves : List (List (Option PVar) × List Int) :=
    (List.range KEY_COORDS).map (fun k =>
      ([some (kv.acc k (b - 1)), some ((ks.evs.getD k default).wordV), none], cEq))
  -- ⚑ AND THE TIE THAT CLOSES §2c's FIRST ENTRY: `absorb sponge Field index_digest` (`:537`).
  let digestTie : List (List (Option PVar) × List Int) :=
    [ ([some (keyDigestVar s t.sp t.br.idx), some ((t.sp.evs.getD 0 default).wordV), none], cEq) ]
  transcriptRowsQ (baseKeySp s t.sp) ks wired
  ++ packHalves (foldHalves ++ sealHalves ++ digestTie)

/-- W-KEY's variable environment. `acc k i` is `0` until the selected branch is reached and the
chosen coordinate after it, which is what a one-hot fold over constants computes. -/
def keyEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let kv := keyVars s (baseKey s t.sp)
  spongeEnv (baseKeySp s t.sp) (keySponge s t.sp t.br.idx)
  ++ (List.range KEY_COORDS).flatMap (fun k =>
      (List.range s.branches).map (fun i =>
        (kv.acc k i, ((if t.br.idx ≤ i then keyConst t.br.idx k else 0 : Nat) : Int))))

/-! ## §10 — W4, the CLOSING TIES, and the 40-word census.

⚑ **THE PUBLIC VECTOR IS THIS ASSEMBLY'S, NOT MINA'S, AND THE DIFFERENCE IS STATED.** Mina's wrap
circuits have `PRIMARY_LEN = WRAP_PRIMARY_LEN = 40`. `MinaWrapPublicInput` carries the slot-by-slot
layout, measured against a devnet block. Of those 40, this rung DERIVES:

    slot   word                                    here
    5–8    plonk.{beta, gamma, alpha, zeta}        ✅ the transcript's own four challenge squeezes,
                                                      as RAW 128-bit prechallenges (`spec.ml:384-386`,
                                                      `Packed_bits (x, Challenge.length)`), which is
                                                      exactly what `assert_eq_plonk`
                                                      (`wrap_verifier.ml:492-499,717-731`) compares
    10     sponge_digest_before_evaluations        ✅ the FORK squeeze (`:646`), which
                                                      `wrap_main.ml:430-432` asserts equal
    13–28  bulletproof_challenges ×16              ✅ `bullet_reduce`'s own prechallenges, RAW
                                                      (`spec.ml:391-392` packs `Sc.inner = pre`),
                                                      which `wrap_main.ml:433-439` asserts equal
                                                      one by one
    29     branch_data                             ✅ §9's `Branch_data.Checked.pack`
                                                      (`wrap_main.ml:189-199`)
    0–4    cip, b, ζ^srs_len, ζ^dom, perm          ◑ TIED since 2026-08-05 — READ by W-FTCOMM
                                                      (2,3,4) and W-BULLET (0,1) out of the PUBLIC
                                                      WORD, not out of a free witness; CHECKED by
                                                      the NEXT proof's `finalize_other_proof`,
                                                      never by this one
    9      xi                                      ◑ TIED at W-COMBINE, same story
    12     messages_for_next_step_proof            ✅ at `w9_prev` ONLY (§18) — the
                                                      `Field.Assert.equal` of `wrap_main.ml:350-351`
                                                      against packed statement word 54, which the
                                                      x_hat MSM consumes as entry 64
    11     messages_for_next_wrap_proof            ✅ at `w11_wraphack` ONLY (§21) — the closing
                                                      `hash_messages_for_next_wrap_proof` sponge's
                                                      `squeeze_field` (`wrap_main.ml:421-431`)
    30–37  Spec.T.Constant padding                 ✗ (never constrained upstream either)
    38–39  the lookup Opt                          ✗ (`lookup_verification_enabled` is off)

**22 of 40 through `w7_split`; 25 at `w8_ftcomm`, 26 at `w9_prev`, 27 at `w11_wraphack`, 28 at
`w10_combine` and 30 at `w11_bullet` / `w12_close`** — the 24 this circuit DERIVES plus the six it
READS, each appearing at the rung whose rows read it. ⚠ At the SMOKE shape `pubWords = 6` and
`ipaRounds = 3`, so the derived base is 6, not 22, and `branch_data` is not exposed at all.

⚑ **AND `pubWords = 22` AGAINST `WRAP_PINNED_SLOTS.length = 24` IS THAT LADDER, NOT A SHORTFALL.**
`pubWords` is the width of `exposedVars` — the words the CLOSING rung derives — and the last two
pinned slots are derived by rungs ABOVE it: `exposedVarsAt` appends slot 12 at `.prev` and slot 11 at
`.wraphack`, and `rungPub` widens by exactly one and then two to carry them. So `22 + 1 + 1 = 24`,
and the terminal rung emits all twenty-four. Neither "two pinned slots are not emitted" nor
"`pubWords` counts something else": `pubWords` counts the BASE, the ladder counts the rest.

⚑ **THE ORDER AT 5–8 IS β, γ, α, ζ — AND THE FIRST DRAFT OF THIS TABLE SAID `alpha, beta, gamma`.**
`Wrap.Statement.to_data` (`composition_types.ml:826-880`) lays the `challenge` bucket down before the
`scalar_challenge` one, so β and γ come first and α third;
`Dregg2.Bridge.MinaWrapPublicInput.publicInputWords` carries the same order as a MEASURED correction
against block 539508's own binprot bytes (2026-07-30). This assembly's `exposedVars` is indexed by
the TRANSCRIPT's squeeze order — β (`wrap_verifier.ml:620`), γ (`:621`), α (`:624`), ζ (`:631`) —
which is the SAME order, so `wrapSlots` maps word `i` to slot `5 + i` with no permutation. That the
two agree is a fact to be checked, not a coincidence to be assumed: `the_challenge_slots_are_the_
transcript_order` is where it is checked, and a rotation here is precisely the defect that puts the
wrong object under the right name and moves nothing a width signature can see.

⚠ ⚑ **THE DENOMINATOR IS 30, AND IT WAS 24 UNTIL 2026-08-05 BECAUSE SIX SLOTS WERE MISLABELLED.**
`wrap_main` is HANDED forty words. It CONSTRAINS twenty-four. It READS six more — slots 0–4 and 9,
passed through as `~advice` / `~plonk` / `~xi` (`wrap_main.ml:405-414`) — and CHECKS none of those
six; what checks them is the NEXT proof's `finalize_other_proof`. The remaining ten are
`Spec.T.Constant` padding (30–37) and the lookup `Opt` (38–39) that `G.lookup_verification_enabled`
leaves off (`wrap_verifier.ml:487,715`); a real devnet wrap proof carries **ZERO** in all ten
(`MinaWrapPublicInput.the_tail_is_padding_and_branch_data`, over
`MinaWrapPublicCommGate.PUBLIC_INPUT`), and tying those to variables would be public fixtures —
defect class 5 wearing a public vector.

⚑ **SO THE HONEST READING OF A `PI ours-vs-mina` DELTA IS `30 read + 10 dead`, NOT `24 + 16`.** The
six used to sit in `WRAP_UNPINNED_SLOTS` beside the dead ten, which said "nothing reads these" about
words `ft_comm`, `Split_commitments.combine` and `check_bulletproof` all read. They were unread HERE
only because this assembly wired those three consumers to free witnesses with fixture defaults, and
that was a divergence from `wrap_main` wearing the clothes of a design choice.

⚠ **AND BEING READ IS NOT A COSMETIC CHANGE — IT REMOVES SIX FREE WITNESSES.** A free witness is
chosen by the prover; a public word is handed to the verifier. Before this, a prover could pick any
`perm`, any `ξ`, any `b` it liked and the circuit would prove. `WRAP_PASSTHROUGH_SLOTS` and the ties
in `ftcRows` / `combRows` / `bulletRows` are what closed that, and the harness's polarity (5) sigma
leg is what MEASURES it: those six slots move from "accepts a cell flip" to "refuses one".

⚑ **AND EACH NEW WORD IS EXPOSED AT ONE RUNG, NOT AT ALL OF THEM.** `closingRows` emits `pubWords`
halves at `w4_bind`, `prevRows` emits slot 12 and `whRows` slot 11; every rung declares all forty,
and below their rungs those two slots sit in `wrapInertOk` — so a rung that exposed them early would
tie a public word to a cell nothing in that rung reads, and `placeCheckedWith` refuses it under the
DECLARATION of the rung above. That is the difference between a public word a rung derives and one
it inherits. `prev_rung_places_and_the_rung_below_it_does_not` and
`wraphack_rung_places_and_the_rung_below_it_does_not` exhibit both refusals, now naming slot 12 and
slot 11 rather than `pubWords` and `pubWords + 1`. -/

/-- ⚑ **WHICH OF `WRAP_PRIMARY_LEN`'s FORTY SLOTS `wrap_main` ACTUALLY PINS**, read at source and
listed so a `PI ours-vs-mina` delta cannot be read as a to-do list. -/
def WRAP_PINNED_SLOTS : List Nat :=
  [5, 6, 7, 8]                                    -- assert_eq_plonk β γ α ζ (wrap_verifier.ml:717-731)
  ++ [10]                                         -- sponge_digest_before_evaluations (:430-432)
  ++ [11]                                         -- messages_for_next_wrap_proof (:421-431)
  ++ [12]                                         -- messages_for_next_step_proof (:350-351)
  ++ (List.range 16).map (fun r => 13 + r)        -- bulletproof_challenges (:433-439)
  ++ [29]                                         -- branch_data (:189-199)

def WRAP_PINNED_WORDS : Nat := WRAP_PINNED_SLOTS.length

/-- ⚑ **THE SIX `wrap_main` READS AND NEVER CHECKS** — `~advice` / `~plonk` / `~xi`
(`wrap_main.ml:405-414`). A THIRD category, and the reason it exists is that the other two were
answering different questions and both answered this one wrong.

  * `WRAP_PINNED_SLOTS` are the slots `wrap_main` CONSTRAINS. These are not among them: nothing in
    this circuit checks them, and inventing a check would be a divergence from upstream, not a fix.
  * `WRAP_UNPINNED_SLOTS` are the slots NOTHING reads. These are not among those either: `ft_comm`,
    `Split_commitments.combine` and `check_bulletproof` all read them, and until 2026-08-05 this
    assembly hid that by wiring those three consumers to free witnesses instead.

So they are READ-BUT-NOT-CHECKED, they are tied to the cell that reads them, and their checker is
the NEXT proof's `finalize_other_proof`. ⚠ Being read is what makes a prover unable to choose them:
before this they were six free witnesses, and a public word is not. -/
def WRAP_PASSTHROUGH_SLOTS : List Nat :=
  [ WRAP_SLOT_CIP, WRAP_SLOT_B ]                  -- W-BULLET, check_bulletproof (wrap_verifier.ml:395)
  ++ [ WRAP_SLOT_ZETA_TO_SRS, WRAP_SLOT_ZETA_TO_DOM, WRAP_SLOT_PERM ]   -- W-FTCOMM, ft_comm
  ++ [ WRAP_SLOT_XI ]                             -- W-COMBINE, Split_commitments.combine

/-- ⚑ **THE TEN SLOTS `wrap_main` LEAVES UNREAD, as indices** — written down rather than computed
from the emission, because it is what the emission is CHECKED AGAINST (`wrapInertOk`).
`WRAP_UNPINNED` below is the same ten by reason and by owner.

⚠ **THIS WAS SIXTEEN UNTIL 2026-08-05** and six of those sixteen were a mislabel: they were unread
HERE only because this assembly declined to tie them, not because upstream leaves them unread. They
are now `WRAP_PASSTHROUGH_SLOTS`. What is left is the genuinely dead tail, and nothing upstream
reads any of it. -/
def WRAP_UNPINNED_SLOTS : List Nat :=
  (List.range 8).map (fun j => 30 + j)            -- Spec.T.Constant padding
  ++ [38, 39]                                     -- the dead lookup Opt

/-- …and the ten it does not pin, by REASON and by OWNER. -/
def WRAP_UNPINNED : List String :=
  [ "30–37 Spec.T.Constant padding — ZERO in a real devnet wrap proof, constrained by nothing upstream"
  , "38–39 the lookup Opt — G.lookup_verification_enabled is off (wrap_verifier.ml:487,715)" ]

/-- …and the six pass-throughs, by REASON and by OWNER. -/
def WRAP_PASSTHROUGH : List String :=
  [ "0 combined_inner_product — ~advice (wrap_main.ml:405-414); READ by W-BULLET at \
     wrap_verifier.ml:395's absorb_shifted; CHECKED by the NEXT proof's finalize_other_proof"
  , "1 b — ~advice; READ by W-BULLET as check_bulletproof's b·u multiplier; same checker"
  , "2 zeta_to_srs_length — ~plonk; READ by W-FTCOMM as ft_comm's fold multiplier; same checker"
  , "3 zeta_to_domain_size — ~plonk; READ by W-FTCOMM as ft_comm's closing scale; same checker"
  , "4 perm — ~plonk; READ by W-FTCOMM as f_comm's scale (common.ml:245); same checker"
  , "9 xi — ~xi (wrap_main.ml:409); READ by W-COMBINE, shared by all 46 endo ladders; same checker" ]

/-- The variables this assembly exposes as public words, in order. ⚑ Slot order here is THIS
circuit's; the census above maps each to Mina's slot.

⚠ ⚑ **THE WIDTH DECIDES WHICH VARIABLE, AND THIS WAS WRONG IN THE FIRST DRAFT.** `spec.ml:374-392`
packs `Challenge` / `Scalar Challenge` / `Bulletproof_challenge` at `Challenge.length = 128` — the
RAW prechallenge — where `Digest` packs at `Field.size_in_bits`. Exposing the 255-bit endo lift for
the challenge words would have put a different object in the public vector under the right name. -/
def exposedVars (t : WrapData) : List PVar :=
  let s := t.sh
  let cb := baseCh s t.sp
  -- ⚑ THE RAW PRECHALLENGE, NOT THE LIFT — read at source and corrected before shipping.
  -- `spec.ml:374-392` packs `Challenge` and `Scalar Challenge` at `Challenge.length = 128` and
  -- `Bulletproof_challenge` as `let { Sc.inner = pre } = pack x in `Packed_bits (pre, 128)`, i.e.
  -- the 128-bit value the sponge squeezed — NOT the 255-bit `Field.(scale a endo + b)`. And
  -- `assert_eq_plonk` (`wrap_verifier.ml:492-499`) compares exactly those: `Field.Assert.equal` on
  -- the raw challenge for β/γ and on the `Scalar_challenge.inner` for α/ζ. So the exposed variable
  -- is the chain's reconstructed `n₈`, which the `cSplit` row ties to the sponge squeeze.
  (List.range 4).map (fun c => (chainVars s (cb + 1) c).n s.emsRows)
  -- `sponge_digest_before_evaluations` IS a `Digest` (`Field.size_in_bits`), so THIS one is the
  -- full field squeeze — the fork at `wrap_verifier.ml:646`.
  ++ [ (match forkSqueeze t.sp with | some e => e.1 | none => PVAR_NOWHERE) ]
  ++ (List.range (min s.ipaRounds (nChals s - 5))).map (fun r =>
       (chainVars s (cb + 1) (4 + r)).n s.emsRows)
  ++ [ (branchVars s (baseBr s t.sp)).packed ]
  |>.take s.pubWords

/-- ⚑ **THE SLOT MAP** — MINA'S OWN statement slot for each word `exposedVars` produces, in
`exposedVars`' order and truncated by the SAME `.take s.pubWords`, so the two lists are pointwise a
(variable, slot) pair by construction and cannot drift in length.

⚠ This is the object the whole layout turns on. A slot map is exactly the artefact whose failure
mode is silent: swap two entries and every gate still places, every rung still proves, and the
circuit commits to a different statement. The three instruments that see it are §10's census
(read at source), `the_challenge_slots_are_the_transcript_order` (the β/γ/α order, against the
transcript's own squeeze order) and `MinaWrapPublicInput`'s width signature on a real block. -/
def wrapSlots (s : WrapShape) : List Nat :=
  ([5, 6, 7, 8]                                   -- β γ α ζ, `assert_eq_plonk`
   ++ [10]                                        -- sponge_digest_before_evaluations, the FORK
   ++ (List.range (min s.ipaRounds (nChals s - 5))).map (fun r => 13 + r)
   ++ [29]                                        -- branch_data
  ).take s.pubWords

/-- One closing `Generic` half per public word: `external <mina slot> = v`. This is the row that
makes the public word a READ one, so `placeChecked`'s `inertPublicWord` cannot fire silently.

⚑ **THE SLOT, NOT THE INDEX.** This row used to tie `external i` for `i < pubWords` — a DENSE public
vector of this assembly's own devising, which is why a proof of it needed a public input Mina does
not compute. It now ties MINA'S slot, so the emitted vector sits in the layout
`Pickles.prepared_statement` builds and `kimchi::verifier::verify` reads under a side-loaded wrap
index. -/
def closingRows (t : WrapData) : List WRow :=
  packHalves (((wrapSlots t.sh).zip (exposedVars t)).map (fun sv =>
    (([ some (.external sv.1 : PVar), some sv.2, none ] : List (Option PVar)), cEq)))

/-! ## §15 — ⚑ **W-XHAT**: `wrap_verifier.ml:539-616`, the public-input MSM.

Read end to end at source. `x_hat` is built in five movements and this file emits all five:

  * **THE EXPANSION** (`:542-548`). `wrap_main.ml:404-411` hands `incrementally_verify_proof` the
    packed previous STEP statement with every `` `Field `` already through `split_field`; `:542-548`
    turns each such pair into TWO entries, `(x, Field.size_in_bits)` and `((b :> Field.t), 1)`.
    57 packed words + 10 splits = **67 entries**, at `15 × 255 · 40 × 128 · 12 × 1`
    (`KimchiWrapMainField` §15a, cross-checked against a Rust binary's own census AND against
    Mina's own compiled `VarBaseMul 2417`).
  * **THE PARTITION** (`:550-582`). `` `Field (Constant c, _) `` goes to `constant_part`; everything
    else to `non_constant_part`, where a one-bit entry becomes `` `Cond_add `` with an explicit
    `assert_ (Constraint.boolean b)` and everything else `` `Add_with_correction `` at
    `Ops.scale_fast2'`. ⚑ **`constant_part` IS EMPTY HERE** — the STEP statement's spec has no
    `Spec.T.Constant` and no `Opt` node, so all 67 entries are in-circuit. That is the MIRROR of the
    step side, where nine one-bit WRAP-statement words leave the circuit entirely.
  * **THE CORRECTION** (`:584-596`). The `Add_with_correction` corrections are reduced by
    `Ops.add_fast` and become the fold's `~init` (there is nothing else to fold in, `constant_part`
    being empty). A correction is `negate (pow2pow g actual_shift)`, which cancels `scale_fast2`'s
    `+ 2 ^ actual_bits_used`.
  * **THE FOLD** (`:598-609`). `List.foldi terms ~init` in entry order — `Cond_add` is
    `Inner_curve.if_ b ~then_:(Ops.add_fast g acc) ~else_:acc`, `Add_with_correction` is
    `Ops.add_fast acc (Ops.scale_fast2' … g x ~num_bits:n)`, in that argument order.
  * **THE CLOSE** (`:610-617`). `Inner_curve.negate`, then `x_hat blinding` adds
    `Inner_curve.constant (Lazy.force Generators.h)`, then `:617` ABSORBS the pair.

## ⚑ THE DEFECT CLASSES, INSIDE THIS SUB-CIRCUIT

  1. **Free ladder seeds.** `scale_fast_unpack` opens with `let acc = ref (add_fast base base)` and
     `let n_acc = ref Field.zero` (`plonk_curve_ops.ml:157-158`) — the exact two cells the step side
     found free in R3, where a prover could solve for `acc₀` because doubling is a bijection. Every
     ladder here emits `xhDblRow` (a `CompleteAdd` DEFINING `acc₀`) and an `n₀ = 0` `Generic` half;
     `xhat_every_ladder_seed_is_pinned` reads both off the EMITTED row list, per ladder.
  2. **Prover-chosen decompositions, BOTH halves.** `scale_fast2'` splits `x = 2·s_div_2 + s_odd`
     (`:285-291`) and `scale_fast2` then asserts the TOP bits of `s_div_2` zero
     (`:262-265`) — `bits_lsb[i] = 0` for `i` from `num_bits − 1` to `actual_bits_used − 1`. That is
     **one** bit at width 255 and **three** at width 128, because a 128-bit entry's ladder actually
     runs at 130. ⚑ Those bits are chunk 0's, and in the witness layout they are NEXT-row cells that
     would ordinarily be ADVICE — an advice cell cannot be σ-tied to anything, so the emitter moves
     them into permutation columns and pins them with `Generic` halves. Emitting the split without
     them is the containment §13 refused to ship.
  3. **Absorbed-but-not-consumed.** ⚠ `x_hat` **stays on `WRAP_UNCONSUMED`** and the entry text is
     rewritten rather than deleted. See §15c of `KimchiWrapMainField`: the 67 scalars are the
     witnessed previous STEP statement, free here and free upstream, and what ties them there is
     W-FINALIZE / W-WRAPHACK / `assert_eq_plonk`. Moving `x_hat` off the census on the strength of
     an MSM over free scalars would be metric-gaming.
  4. **Constants pinned against their own definitions.** Every base, correction and `Generators.h`
     comes from `MinaStepSrsLagrange`, and `MinaStepSrsLagrangePin` proves the SRS construction that
     produced them reproduces the DEVNET SRS coordinate for coordinate.
  6. **Wrong seed points.** `add_fast base base` is `2T` and that is what upstream seeds with here
     — unlike `Scalar_challenge.endo`, which seeds at `2(t + φ(t))` and which the step side had
     wrong for a while. The two are different gadgets and the difference is stated, not assumed.

## ⚑ THREE PLACES THIS SUB-CIRCUIT IS STRICTER THAN UPSTREAM

  * **The base pins.** `lagrange_with_correction` short-circuits to a pure constant when every
    branch domain agrees (`wrap_verifier.ml:277-279`), and `lagrange` never does — it always folds
    `Σ bⱼ · gⱼ` over the one-hot vector, which Snarky spends NO row on because the `gⱼ` are
    `Inner_curve.constant` and `Checked.mul` takes its `Constant` branch. This file pins each base as
    a constant. Under §9's emitted `Σ bⱼ = 1` at equal domains the two agree; it is stricter, and it
    is therefore not a row-count conformance claim.
  * **`Inner_curve.negate`.** `snarky_curve.ml:206` is `(x, F.negate y)`, a `Cvar` scale — zero rows.
    This file emits one `Generic` half so the negated ordinate is a constrained cell the blinding
    add reads.
  * **The mux.** `Field.if_` is three halves per coordinate here (`d = t − e`, `m = b·d`,
    `r = m + e`). Snarky's `assert_r1cs b (then_ − else_) (r − else_)` reduces the same two linear
    combinations and lands in the same place, but this file's decomposition is explicit rather than
    whatever `reduce_lincom` chose. -/

/-- The entries this shape emits (`xhatSel`), and the projections the layout indexes by. -/
def xhSel (s : WrapShape) : List Nat := s.xhatEntries
def xhN (s : WrapShape) : Nat := (xhSel s).length
def xhAt (s : WrapShape) (k : Nat) : Nat := (xhSel s).getD k 0
def xhChunks (s : WrapShape) (k : Nat) : Nat := xhatChunksAt (xhAt s k)
def xhChunkPrefix (s : WrapShape) (k : Nat) : Nat :=
  ((List.range k).map (fun m => xhChunks s m)).foldl (· + ·) 0
def xhTotalChunks (s : WrapShape) : Nat := xhChunkPrefix s (xhN s)
/-- Positions of the `Add_with_correction` entries within the selection. -/
def xhLadders (s : WrapShape) : List Nat :=
  (List.range (xhN s)).filter (fun k => xhChunks s k != 0)

/-- Region A's per-entry stride. Slots: 0/1 base, 2/3 correction, 4 scalar, 5 `s_div_2`, 6 `s_odd`,
7/8 the `add_fast h (negate g)` alternative, 9..14 the mux intermediates `(d,m,r)` for x then y,
15/16 the fold output, 17/18 the `Cond_add` sum, 19 `−yT`. -/
def XH_STRIDE : Nat := 20

/-- The index sponge's permutations at rate 2 — the same arithmetic §21 spells for
`hash_messages_for_next_wrap_proof`: one per odd absorb after the opening pair, plus the squeeze's
(the 56th absorb leaves the state at `Absorbed 2`, so the squeeze permutes). -/
def KEY_SP_PERMS : Nat := (KEY_COORDS - 1) / 2 + 1
/-- …and the variables `runSpongeQ` allocates for it: three state cells, three per permutation and
two per absorb. Identical in shape to `WH_VARS`, because it is the same allocator on a longer tape. -/
def KEY_SP_VARS : Nat := 3 + 3 * KEY_SP_PERMS + 2 * KEY_COORDS

/-- ⚑ The key sponge's VARIABLE COUNT. Branch-independent by construction: `keySchedule i` has the
same 56 absorbs and one squeeze at every `i`, and `runSpongeQ` allocates per EVENT and not per
value. `key_sponge_width_is_branch_independent` pins it across all five branches, because every base
above `w5_key` is built on this number and a branch-dependent one would move the whole layout under
a branch selection.

⚠ ⚑ **AND IT IS THE CLOSED FORM SINCE 2026-08-05, WHICH IS A COST FACT AND NOT A LAYOUT ONE.** It
read `(keySponge s sp KEY_REAL_BRANCH).next`. `baseXh` IS this number, and **every** base address
above `w5_key` is built on `baseXh`: `xhBase*`, `basePrev`, `baseFtc`, `baseWh`, `baseFin`,
`baseComb`, `baseBull`, `baseClose`. Each of those recomputes its whole chain on **every cell
reference** — `combSlot`, `bV`, `whBaseP`, `finEvVar`, `xA` — and `baseComb` alone unfolds that chain
into **three** `baseXh` evaluations, because `nFtcVars` is `ftcBaseO − baseFtc` and both sides walk
down to it.

⚑ **MEASURED, at the smoke shape, in the interpreter that actually emits** (`ProbeAddr`, 100 calls
each): `nKeySpVars` **19.3 ms**, `baseKeySp` — everything BELOW the sponge — **0.03 ms**, `baseXh`
**19.1 ms**, `baseComb` **57.3 ms**, `combSlot` **57.7 ms**. **One cell reference cost 57.7 ms**, and
it was three runs of the 28-permutation index sponge: 1 540 Fq Poseidon rounds plus `permStatesQ`'s
quadratic `acc ++ [·]`, for a number that is `199` at every shape and every branch.

That is why `w12_close` took **33 m 52 s** at the smoke shape for 4 326 rows, ~11× what it cost before
it absorbed W-COMBINE and W-BULLET: those two contribute **2 034** of those rows (4 286 circuit rows,
less `.prev`'s 1 613, less W-WRAPHACK's own 637 and W-CLOSE's 2), every one of them carrying about ten
`combSlot`/`bV` references, and `rungRows`/`circuitEnvAt` are evaluated five times over per emission.
This is the file's own measured lesson a fourth time (§7's `let`-above-the-`match`, §19's `finAll`,
`fnEm`'s `modifyGet`): **a value that costs a traversal must be BOUND, not re-derived per use.**

⚠ ⚑ **AND THE GENERAL `rfl` IS NOT AVAILABLE HERE — SAID PLAINLY RATHER THAN ROUNDED AWAY.** The
statement this hoist wants is `nKeySpVars s sp = (keySponge s sp KEY_REAL_BRANCH).next` for EVERY
shape and sponge, in the idiom of `rungRows_is_a_ladder` and `finAll_is_the_recomputation`. It does
not elaborate: `whnf` forces the sponge's lanes through `midN`, and the proof was still running at
**400 000 000 heartbeats and ten minutes**. So the equality is discharged the way this file already
discharges `xhatXY`, which is out of the kernel's reach for the same kind of reason, and on three
legs rather than one:

  * **the kernel, at the smoke shape and at all five branches** —
    `key_sponge_width_is_branch_independent` (§14b) is now a trajectory measured against an
    INDEPENDENT count rather than partly against itself;
  * **the kernel, generally, for the half that IS general** —
    `key_sponge_width_is_the_same_at_every_shape` says this number does not read its arguments, which
    is the claim the paragraph above used to make in prose;
  * ⚑ **`EmitWrapMainJson`, at EVERY emission and at whatever shape is being emitted** — it runs the
    trajectory once (19 ms) and REFUSES when the two disagree. That is the leg that covers `shapeWrap`
    and any `DREGG_WM`-supplied shape, and it is the only one that could ever go red on a shape
    nobody wrote a pin for. -/
def nKeySpVars (_s : WrapShape) (_sp : SpAcc) : Nat := KEY_SP_VARS

/-- The x_hat region starts after the key sponge, so nothing below `w6_xhat` moves. -/
def baseXh (s : WrapShape) (sp : SpAcc) : Nat := baseKeySp s sp + nKeySpVars s sp
def xhBaseB (s : WrapShape) (sp : SpAcc) : Nat := baseXh s sp + XH_STRIDE * xhN s
def xhBaseC (s : WrapShape) (sp : SpAcc) : Nat :=
  xhBaseB s sp + 2 * (xhTotalChunks s + xhN s)
def xhBaseD (s : WrapShape) (sp : SpAcc) : Nat := xhBaseC s sp + xhTotalChunks s
def xhBaseE (s : WrapShape) (sp : SpAcc) : Nat := xhBaseD s sp + 3 * xhN s
def xhBaseF (s : WrapShape) (sp : SpAcc) : Nat := xhBaseE s sp + 2 * (xhLadders s).length

/-- Entry `k`'s slot `o`. -/
def xA (s : WrapShape) (sp : SpAcc) (k o : Nat) : PVar :=
  .external (baseXh s sp + XH_STRIDE * k + o)
/-- Entry `k`'s accumulator point at chunk boundary `j` (`j = 0 .. chunks`). -/
def xAccX (s : WrapShape) (sp : SpAcc) (k j : Nat) : PVar :=
  .external (xhBaseB s sp + 2 * (xhChunkPrefix s k + k + j))
def xAccY (s : WrapShape) (sp : SpAcc) (k j : Nat) : PVar :=
  .external (xhBaseB s sp + 2 * (xhChunkPrefix s k + k + j) + 1)
/-- ⚑ Entry `k`'s scalar counter at chunk boundary `j`. At `j = chunks` it IS `s_div_2`'s own
variable — `plonk_curve_ops.ml:207`'s `Field.Assert.equal !n_acc scalar` as a σ class rather than as
a row, which is what makes the ladder's bits the multiplier `scale_fast2` actually used. -/
def xCnt (s : WrapShape) (sp : SpAcc) (k j : Nat) : PVar :=
  if j == xhChunks s k then xA s sp k 5
  else .external (xhBaseC s sp + xhChunkPrefix s k + j)
/-- Entry `k`'s `t`-th top-bit-zero cell (`plonk_curve_ops.ml:262-265`). -/
def xZb (s : WrapShape) (sp : SpAcc) (k t : Nat) : PVar :=
  .external (xhBaseD s sp + 3 * k + t)
/-- The `a`-th partial sum of the correction reduce. -/
def xCorrSum (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar × PVar :=
  (.external (xhBaseE s sp + 2 * a), .external (xhBaseE s sp + 2 * a + 1))
/-- `Generators.h`'s two cells, and the negated ordinate of the fold's output. -/
def xhHVar (s : WrapShape) (sp : SpAcc) : PVar × PVar :=
  (.external (xhBaseF s sp), .external (xhBaseF s sp + 1))
def xNegY (s : WrapShape) (sp : SpAcc) : PVar := .external (xhBaseF s sp + 2)

def nXhVars (s : WrapShape) (sp : SpAcc) : Nat := xhBaseF s sp + 3 - baseXh s sp

/-! ## §18a — ⚑ **W-PREV's VARIABLE SPACE** (`wrap_main.ml:201-256`), declared HERE because §15 and
§16 both point INTO it.

The 57 packed statement words are the MSM's scalars and the split's `x`. Upstream they are not
copies of those things, they ARE them — `wrap_main.ml:404-411` hands `incrementally_verify_proof`
the array `pack_statement … prev_statement` directly, so entry `i`'s scalar and packed word `i` are
one `Cvar` and the tie costs no row. This layout is what lets that be true here too: `xScal` and
`xSplitW` resolve to `prevW`, so the σ class is the identity of the variable and not a `Field.Assert
.equal` this file invented. Emitting a tie row instead would have been STRICTER than `wrap_main` and
would have had to be declared as such; it is cheaper and more faithful not to. -/

/-- The prev-statement region starts after W-XHAT's — nothing below `w6_xhat` moves. -/
def basePrev (s : WrapShape) (sp : SpAcc) : Nat := xhBaseF s sp + 3
/-- ⚑ Packed statement word `w`'s cell, `w < PREV_WORDS`. -/
def prevW (s : WrapShape) (sp : SpAcc) (w : Nat) : PVar := .external (basePrev s sp + w)
/-- `assert_on_curve`'s two intermediates for `prev_step_accs.(p)`: `x²` at `t = 0`, `x³` at `t = 1`
(`snarky_curve.ml:211-217`). -/
def prevSq (s : WrapShape) (sp : SpAcc) (p t : Nat) : PVar :=
  .external (basePrev s sp + PREV_WORDS + 2 * p + t)
/-- ⚑ **THE PADDED `prev_step_accs` SLOTS' OWN COORDINATE CELLS.** `wrap_main.ml:221-223` allocates
`Max_proofs_verified` points and the `OptSponge` mask (`wrap_verifier.ml:511-514`) keeps `whNPad` of
them off the tape — so those have no absorbed cell to borrow and this rung witnesses them here.
`sgOldVar` is where the two halves are joined. -/
def prevPadSg (s : WrapShape) (sp : SpAcc) (p j : Nat) : PVar :=
  .external (basePrev s sp + PREV_WORDS + 2 * s.maxPrevs + 2 * p + j)
def nPrevVars (s : WrapShape) : Nat :=
  PREV_WORDS + 2 * s.maxPrevs + 2 * whNPad WH_REAL_SLOTS

/-- ⚑ **ENTRY `k`'s SCALAR CELL.** For a `` `Packed_bits `` entry that IS the packed statement word;
for the two halves of a `split_field` pair it is the gadget's own output cell, whose `x` is the word.
Below `w9_prev` nothing else constrains `prevW`, exactly as today — the cell moves, the rung does
not. -/
def xScal (s : WrapShape) (sp : SpAcc) (k : Nat) : PVar :=
  let i := xhAt s k
  if xhatIsSplitHi i || xhatIsSplitLo i then .external (baseXh s sp + XH_STRIDE * k + 4)
  else prevW s sp (xhatWordOf i)

/-- The fold's `~init` — the last correction partial sum, or the single correction when there is
only one `Add_with_correction` entry. -/
def xInitVar (s : WrapShape) (sp : SpAcc) : PVar × PVar :=
  let m := (xhLadders s).length
  if m ≤ 1 then (xA s sp ((xhLadders s).headD 0) 2, xA s sp ((xhLadders s).headD 0) 3)
  else xCorrSum s sp (m - 2)

/-- The accumulator AFTER entry `k`: the mux output on a `Cond_add`, the fold `add_fast`'s output on
an `Add_with_correction`. -/
def xFoldOut (s : WrapShape) (sp : SpAcc) (k : Nat) : PVar × PVar :=
  if xhChunks s k == 0 then (xA s sp k 11, xA s sp k 14) else (xA s sp k 15, xA s sp k 16)
/-- …and the accumulator entry `k` READS. -/
def xFoldIn (s : WrapShape) (sp : SpAcc) (k : Nat) : PVar × PVar :=
  if k == 0 then xInitVar s sp else xFoldOut s sp (k - 1)

/-- One `complete_add` row — `Ops.add_fast l r = o`. Cols 0..5 are the six point coordinates, col 6
is `inf` (self-wired, and zero for every add this sub-circuit makes), cols 7..10 carry `same_x`,
the slope, `inf_z` and `x21_inv`. -/
def caRowQ (l r o : PVar × PVar) (c : List Nat) : WRow :=
  { kind := .completeAdd
  , perm := [some l.1, some l.2, some r.1, some r.2, some o.1, some o.2, none]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- A CONSTANT-point pin: two `Generic` halves, one row. -/
def ptConstRow (vx vy : PVar) (p : Nat × Nat) : WRow :=
  genericRow (some vx) none none (some vy) none none (cConst (p.1 : Int) ++ cConst (p.2 : Int))

/-- The two rows of entry `k`'s chunk `j`.
CURR `w₀=xT w₁=yT w₂=x₀ w₃=y₀ w₄=n w₅=n' w₆=Ø w₇..w₁₄ = x₁y₁..x₄y₄`;
NEXT `w₀=x₅ w₁=y₅ w₂..w₆=b₀..b₄ w₇..w₁₁=s₀..s₄`.
⚑ On chunk 0 the first `topZeros` bit cells move from ADVICE into PERMUTATION columns, because
`scale_fast2`'s `Field.Assert.equal Field.zero bits_lsb.(i)` has to reach them and an advice cell is
in no σ class.

⚠ ⚑ **`td` AND `bits` ARE PARAMETERS, AND THAT IS §17's LESSON APPLIED BACKWARDS TO §15.**
`ftcChunkRows` already carried this note and this signature; `xhChunkRows` did not, and computed
`xhatLadder i` and `xhatBitsOf i` INSIDE — i.e. once per CHUNK. A 255-bit entry has 51 chunks, so
its 255-step chain (three `qInv` a step) ran 51 times, and the wrap shape's 1805 chunks replayed
**1805** ladders where 55 were needed. MEASURED at the smoke shape, which is three ladders: the
`w6_xhat` rung's emission went from 176 s to 4.4 s. The emitted bytes are unchanged — same term,
same order — which is the check that this is a hoist and not an edit. -/
def xhChunkRows (s : WrapShape) (sp : SpAcc) (k : Nat) (td : TermDataQ) (bits : List Nat)
    (topZeros : Nat) (j : Nat) : List WRow :=
  let tz := if j == 0 then topZeros else 0
  let ax : Nat → Int := fun n => ((td.accs.getD n (0, 0)).1 : Int)
  let ay : Nat → Int := fun n => ((td.accs.getD n (0, 0)).2 : Int)
  let sl : Nat → Int := fun n => (td.slopes.getD n 0 : Int)
  let bt : Nat → Int := fun n => (bits.getD n 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some (xA s sp k 0), some (xA s sp k 1)
              , some (xAccX s sp k j), some (xAccY s sp k j)
              , some (xCnt s sp k j), some (xCnt s sp k (j + 1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (xAccX s sp k (j+1)), some (xAccY s sp k (j+1)) ]
              ++ (List.range 5).map (fun t => if t < tz then some (xZb s sp k t) else none)
    , advice := ((List.range 5).filter (fun t => t ≥ tz)).map (fun t => (2 + t, bt (5*j+t)))
                ++ (List.range 5).map (fun t => (7 + t, sl (5*j+t))) } ]

/-- **W-XHAT's ROWS.** -/
def xhatRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let sel := xhSel s
  let n := xhN s
  let lad := xhLadders s
  let m := lad.length
  -- (1) every base and every correction is a PINNED CONSTANT.
  let basePins : List WRow :=
    (List.range n).map (fun k => ptConstRow (xA s sp k 0) (xA s sp k 1) (xhatBase (xhAt s k)))
  let corrPins : List WRow :=
    lad.map (fun k => ptConstRow (xA s sp k 2) (xA s sp k 3) (xhatCorr (xhAt s k)))
  -- (2) the correction reduce (`wrap_verifier.ml:588-596`), left-associated.
  let corrVal : Nat → Nat × Nat := fun a =>
    ((lad.take (a + 2)).drop 1).foldl (fun acc k => addAQ acc (xhatCorr (xhAt s k)))
      (xhatCorr (xhAt s (lad.headD 0)))
  let corrRows : List WRow :=
    (List.range (m - 1)).map (fun a =>
      let l := if a == 0 then (xA s sp (lad.headD 0) 2, xA s sp (lad.headD 0) 3)
               else xCorrSum s sp (a - 1)
      let lv := if a == 0 then xhatCorr (xhAt s (lad.headD 0)) else corrVal (a - 1)
      let rv := xhatCorr (xhAt s (lad.getD (a + 1) 0))
      caRowQ l (xA s sp (lad.getD (a + 1) 0) 2, xA s sp (lad.getD (a + 1) 0) 3)
        (xCorrSum s sp a) (caWitnessQ lv.1 lv.2 rv.1 rv.2))
  -- (3) the fold, entry by entry, in `List.foldi` order. ⚑ `folds` is bound ONCE: `xhatFoldAt`
  -- rebuilds the whole fold per call and every step of it runs a `scale_fast2` ladder.
  let folds := xhatFolds sel
  let entryRows : List WRow :=
    (List.range n).flatMap (fun k =>
      let i := xhAt s k
      let accIn := xFoldIn s sp k
      let accInV := folds.getD k (0, 0)
      if xhChunks s k == 0 then
        -- `` `Cond_add `` (`wrap_verifier.ml:573-577,602-605`).
        let g := xhatBase i
        let sum := addAQ g accInV
        packHalves [ ([some (xScal s sp k), some (xScal s sp k), some (xScal s sp k)], cBool) ]
        ++ [ caRowQ (xA s sp k 0, xA s sp k 1) accIn (xA s sp k 17, xA s sp k 18)
               (caWitnessQ g.1 g.2 accInV.1 accInV.2) ]
        ++ packHalves
             [ ([some (xA s sp k 17), some accIn.1, some (xA s sp k 9)], [1, -1, -1, 0, 0])
             , ([some (xScal s sp k), some (xA s sp k 9), some (xA s sp k 10)], cMul)
             , ([some (xA s sp k 10), some accIn.1, some (xA s sp k 11)], cAdd)
             , ([some (xA s sp k 18), some accIn.2, some (xA s sp k 12)], [1, -1, -1, 0, 0])
             , ([some (xScal s sp k), some (xA s sp k 12), some (xA s sp k 13)], cMul)
             , ([some (xA s sp k 13), some accIn.2, some (xA s sp k 14)], cAdd) ]
      else
        -- `` `Add_with_correction `` — `Ops.scale_fast2'` then `Ops.add_fast acc _`.
        let g := xhatBase i
        let td := xhatLadder i
        let h := td.accs.getLastD (0, 0)
        let alt := addAQ h (negAQ g)
        let scaled := xhatScaled i
        let ch := xhChunks s k
        -- `Boolean.typ` on `s_odd`, `Field.Assert.equal (2·s_div_2 + s_odd) x`, `n₀ = 0`,
        -- `−yT`, and `scale_fast2`'s top-bit zeros.
        packHalves
          ([ ([some (xA s sp k 6), some (xA s sp k 6), some (xA s sp k 6)], cBool)
           , ([some (xScal s sp k), some (xA s sp k 5), some (xA s sp k 6)], cSplit 1)
           , ([some (xCnt s sp k 0), none, none], cConst 0)
           , ([some (xA s sp k 1), some (xA s sp k 19), none], [1, 1, 0, 0, 0]) ]
           ++ (List.range (xhatTopZeros i)).map (fun tt =>
                ([some (xZb s sp k tt), none, none], cConst 0)))
        -- `let acc = ref (add_fast base base)` (`plonk_curve_ops.ml:157`).
        ++ [ caRowQ (xA s sp k 0, xA s sp k 1) (xA s sp k 0, xA s sp k 1) (xAccX s sp k 0, xAccY s sp k 0)
               (caWitnessQ g.1 g.2 g.1 g.2) ]
        ++ (List.range ch).flatMap (xhChunkRows s sp k td (xhatBitsOf i) (xhatTopZeros i))
        ++ [ probeRow wired (xAccX s sp k ch) (xAccY s sp k ch) ]
        -- `add_fast h (G.negate g)`, then the `s_odd` mux, then the fold add.
        ++ [ caRowQ (xAccX s sp k ch, xAccY s sp k ch) (xA s sp k 0, xA s sp k 19)
               (xA s sp k 7, xA s sp k 8) (caWitnessQ h.1 h.2 g.1 (qSub 0 g.2)) ]
        ++ packHalves
             [ ([some (xAccX s sp k ch), some (xA s sp k 7), some (xA s sp k 9)], [1, -1, -1, 0, 0])
             , ([some (xA s sp k 6), some (xA s sp k 9), some (xA s sp k 10)], cMul)
             , ([some (xA s sp k 10), some (xA s sp k 7), some (xA s sp k 11)], cAdd)
             , ([some (xAccY s sp k ch), some (xA s sp k 8), some (xA s sp k 12)], [1, -1, -1, 0, 0])
             , ([some (xA s sp k 6), some (xA s sp k 12), some (xA s sp k 13)], cMul)
             , ([some (xA s sp k 13), some (xA s sp k 8), some (xA s sp k 14)], cAdd) ]
        ++ [ caRowQ accIn (xA s sp k 11, xA s sp k 14) (xA s sp k 15, xA s sp k 16)
               (caWitnessQ accInV.1 accInV.2 scaled.1 scaled.2) ]
        ++ [ probeRow wired (xA s sp k 15) (xA s sp k 16) ])
  -- (4) `Inner_curve.negate`, `Generators.h`, `x_hat blinding`, and the ABSORB tie.
  let last := xFoldOut s sp (n - 1)
  let lastV := folds.getD n (0, 0)
  let neg := negAQ lastV
  let xw : PVar × PVar :=
    (((sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 0 default).wordV,
     ((sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 1 default).wordV)
  basePins ++ corrPins ++ corrRows ++ entryRows
  ++ packHalves [ ([some last.2, some (xNegY s sp), none], [1, 1, 0, 0, 0]) ]
  ++ [ ptConstRow (xhHVar s sp).1 (xhHVar s sp).2 XHAT_H ]
  ++ [ caRowQ (last.1, xNegY s sp) (xhHVar s sp) xw
         (caWitnessQ neg.1 neg.2 XHAT_H.1 XHAT_H.2) ]
  ++ [ probeRow wired xw.1 xw.2 ]

/-- W-XHAT's variable environment. -/
def xhatEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let sel := xhSel s
  let n := xhN s
  let lad := xhLadders s
  let m := lad.length
  let corrVal : Nat → Nat × Nat := fun a =>
    ((lad.take (a + 2)).drop 1).foldl (fun acc k => addAQ acc (xhatCorr (xhAt s k)))
      (xhatCorr (xhAt s (lad.headD 0)))
  let folds := xhatFolds sel
  (List.range n).flatMap (fun k =>
    let i := xhAt s k
    let g := xhatBase i
    let accInV := folds.getD k (0, 0)
    let outV := folds.getD (k + 1) (0, 0)
    [ (xA s sp k 0, (g.1 : Int)), (xA s sp k 1, (g.2 : Int))
    , (xScal s sp k, (xhatScalar i : Int)) ]
    ++ (if xhChunks s k == 0 then
          let sum := addAQ g accInV
          [ (xA s sp k 17, (sum.1 : Int)), (xA s sp k 18, (sum.2 : Int))
          , (xA s sp k 9, (qSub sum.1 accInV.1 : Int))
          , (xA s sp k 10, (qMul (xhatScalar i) (qSub sum.1 accInV.1) : Int))
          , (xA s sp k 11, (outV.1 : Int))
          , (xA s sp k 12, (qSub sum.2 accInV.2 : Int))
          , (xA s sp k 13, (qMul (xhatScalar i) (qSub sum.2 accInV.2) : Int))
          , (xA s sp k 14, (outV.2 : Int)) ]
        else
          let c := xhatCorr i
          let td := xhatLadder i
          let h := td.accs.getLastD (0, 0)
          let alt := addAQ h (negAQ g)
          let sc := xhatScaled i
          [ (xA s sp k 2, (c.1 : Int)), (xA s sp k 3, (c.2 : Int))
          , (xA s sp k 5, (xhatSDiv2 i : Int)), (xA s sp k 6, (xhatSOdd i : Int))
          , (xA s sp k 7, (alt.1 : Int)), (xA s sp k 8, (alt.2 : Int))
          , (xA s sp k 19, (qSub 0 g.2 : Int))
          , (xA s sp k 9, (qSub h.1 alt.1 : Int))
          , (xA s sp k 10, (qMul (xhatSOdd i) (qSub h.1 alt.1) : Int))
          , (xA s sp k 11, (sc.1 : Int))
          , (xA s sp k 12, (qSub h.2 alt.2 : Int))
          , (xA s sp k 13, (qMul (xhatSOdd i) (qSub h.2 alt.2) : Int))
          , (xA s sp k 14, (sc.2 : Int))
          , (xA s sp k 15, (outV.1 : Int)), (xA s sp k 16, (outV.2 : Int)) ]
          ++ (List.range (xhChunks s k + 1)).flatMap (fun j =>
               [ (xAccX s sp k j, ((td.accs.getD (5 * j) (0, 0)).1 : Int))
               , (xAccY s sp k j, ((td.accs.getD (5 * j) (0, 0)).2 : Int)) ])
          ++ (List.range (xhChunks s k)).map (fun j =>
               (xCnt s sp k j, (td.ns.getD (5 * j) 0 : Int)))
          ++ (List.range (xhatTopZeros i)).map (fun tt => (xZb s sp k tt, (0 : Int)))))
  ++ (List.range (m - 1)).flatMap (fun a =>
       [ ((xCorrSum s sp a).1, ((corrVal a).1 : Int))
       , ((xCorrSum s sp a).2, ((corrVal a).2 : Int)) ])
  ++ [ ((xhHVar s sp).1, (XHAT_H.1 : Int)), ((xhHVar s sp).2, (XHAT_H.2 : Int))
     , (xNegY s sp, (qSub 0 (folds.getD n (0, 0)).2 : Int)) ]

/-! ## §16 — ⚑ **W-SPLIT**: `split_field`, and what its "deferred check" actually discharges.

`wrap_main.ml:69-81`, called ONCE, at `wrap_main.ml:409`, on every `` `Field `` word of the packed
previous STEP statement before `incrementally_verify_proof` sees it. The gadget is three lines:

    let split_field (x : Field.t) : Field.t * Boolean.var =
      let ((y, is_odd) as res) = exists Typ.(field * Boolean.typ) ~compute:… in
      Field.(Assert.equal ((of_int 2 * y) + (is_odd :> t)) x) ; res

so it costs, per word, `Boolean.typ`'s own check on `is_odd` and one `Field.Assert.equal` — **two
`Generic` halves, one row**. §15's expansion (`wrap_verifier.ml:542-548`) then turns each result into
the ADJACENT entry pair `(y, Field.size_in_bits)` and `((is_odd :> Field.t), 1)`, so W-SPLIT's whole
content is that those two MSM entries are the two halves of ONE word.

⚑ **THE OUTPUTS ARE NOT NEW VARIABLES — THEY ARE §15's ENTRY SCALARS.** `y` IS `xA k 4` at the
255-bit position and `is_odd` IS `xA k' 4` at its 1-bit successor. Emitting a split whose outputs
were fresh cells would be decoration; the σ classes are the point.

⚠ ⚑ **AND `is_odd` IS BOOLEAN-CONSTRAINED TWICE UPSTREAM, NOT ONCE.** `exists Typ.(field *
Boolean.typ)` runs `Boolean.typ`'s check here, and `wrap_verifier.ml:573-576` runs
`assert_ (Constraint.boolean b)` again on the same variable when the 1-bit entry takes the
`` `Cond_add `` path. §15 already emits the second; this section emits the first. Emitting one would
be *less* strict than upstream, so both are here — and the duplication is upstream's, not ours.
⚠ The twelve one-bit entries are NOT all split parities: the two `should_finalize` words
(`j = 31`) arrive as `` `Packed_bits (x, 1) `` and get only the `Cond_add` boolean. `xhatIsSplitHi`
is what separates them, and it is a predicate on the width table rather than a hand-copied list.

## ⚑ THE CORRECTION THIS SECTION MAKES TO §13, READ AT SOURCE

§13 item 3 recorded — from upstream's own comment at `wrap_main.ml:64-68` — that split_field "does
not check that the high bits actually fit into n − 1 bits, this is deferred to a call to
`scale_fast2`, which performs this check", and concluded that emitting the split before W-XHAT's
ladder would ship defect class 2 in a new place. **The deferral is real; what it discharges is not
a bound on `y`.** Followed to source:

  * `scale_fast2 g (s_div_2, s_odd) ~num_bits:255` sets `s_div_2_bits = 254`,
    `chunks_needed = 51`, `actual_bits_used = 255`, and asserts `bits_lsb.(i) = 0` for
    `i = 254 .. 254` — **one** cell (`plonk_curve_ops.ml:251-267`). So `s_div_2 < 2^254`.
  * `2^254 < q` (`q − 2^254 = 45560315531506369815346746415080538113 ≈ 2^125`), so that ONE bit is
    exactly the canonicity guard on the ladder's OWN decomposition: `scale_fast_unpack` witnesses
    `bits_msb` at `Typ.array … Field.typ` — **255 free cells, not booleans** — and ties them to the
    scalar only through `Field.Assert.equal !n_acc scalar` over `Fq` (`:207`). Without the top-bit
    zero a prover could present `B` and `B + q`; with it, `B < 2^254 < q` is the unique
    representative and the ladder's multiplier IS `s_div_2`. **That is what the deferral buys.**
  * It buys **no bound on `y`**. `y = 2·s_div_2 + s_odd` with `s_div_2 < 2^254` admits every
    `y ∈ Fq`, and for a given `y` BOTH candidate splits — `(y/2, 0)` and `((y−1)/2, 1)` — land below
    `2^254` for all but a `2^-128` fraction of `y`. `Other_field.With_top_bit0.typ` is
    `typ_unchecked` (`wrap_verifier.ml:68-77`, `impls.ml:196-212`), so nothing checks there either.
  * ⚑ **And it does not need to**, because `scale_fast2`'s mux makes the ambiguity immaterial ONE
    level down: `h = (2^255 + 2·s_div_2 + 1)·g` and the `else` branch subtracts `g`, so the result is
    `(2^255 + y)·g` under EITHER split, and `lagrange_with_correction`'s correction cancels the
    `2^255·g`. The contribution is `y·g` whichever way the prover splits.

⚠ **The split ONE level up — this section's own — is a different matter and it is NOT immaterial.**
`y` and `is_odd` are consumed by DIFFERENT Lagrange bases (`lagrange i` and `lagrange (i+1)`), so
`(y, 0)` and `(y − (q+1)/2, 1)` give DIFFERENT `x_hat`. Nothing in `wrap_main` bounds `y` to 254
bits, so upstream the choice is the prover's.

⚑ ⚑ **AND THE PARAGRAPH THAT USED TO END HERE IS NOW HALF WRONG, WHICH IS WHY `w9_prev` EXISTS.**
It said: *"It is not a hole HERE only because `x` is a free witness on both sides; W-SPLIT's
constraint therefore pins nothing today; its content lands when W-PREV ties `x`."* Two of those
three clauses survive and one does not.

  * **`x` IS TIED NOW.** §18a makes `xSplitW` the packed statement word `prevW (xhatWordOf i)`
    itself — the same variable the MSM's other 47 entries read, and the same one word 54's public
    tie lands on. So `Field.Assert.equal ((of_int 2 * y) + is_odd) x` is an equation between three
    cells the circuit uses elsewhere rather than a definition of a cell nothing else reads, and
    `split_field_recomposes_the_statement_word` is the value-side fact that the honest witness
    satisfies it over ℕ.
  * **`x` IS STILL A FREE WITNESS**, here and upstream, because `exists ~request:Req.Proof_state`
    is a free witness upstream. `w9_prev` did not change that and no rung short of W-FINALIZE can.
  * **SO THE AMBIGUITY IS UNCHANGED AND IT IS UPSTREAM'S.** A prover who picks `x` picks the pair
    `(x/2, x mod 2)` or `((x − q − 1)/2, 1 − x mod 2)`, both satisfy this row, and they give
    different `x_hat`. Bounding `y` here would be a divergence from `wrap_main`, not a fix to it —
    the same line §17 holds on `scale_fast`'s two admissible multipliers. What changed is that the
    residual is now a statement about a variable the circuit CONSUMES, which is a smaller and more
    honest thing than "pins nothing". -/

/-- The pairs of POSITIONS in `xhSel` that one `split_field` produced. A shape that selects the
value half without its parity contributes NO pair — the tie needs both entries to exist. -/
def splitPairs (s : WrapShape) : List (Nat × Nat) :=
  let n := xhN s
  (List.range n).filterMap (fun k =>
    if xhatIsSplitHi (xhAt s k) then
      match (List.range n).find? (fun k' => xhAt s k' == xhAt s k + 1) with
      | some k' => some (k, k')
      | none => none
    else none)

/-- ⚑ Pair `a`'s UNSPLIT word — `split_field`'s argument `x`, which IS packed statement word
`xhatWordOf i` (§18a). This used to be a cell of its own in a region between W-XHAT's and
W-FTCOMM's; that region is gone, because a fresh cell here was precisely the decoration §16's header
now names. -/
def xSplitW (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar :=
  prevW s sp (xhatWordOf (xhAt s ((splitPairs s).getD a (0, 0)).1))

/-- **W-SPLIT's ROWS.** Per pair: `Boolean.typ`'s check on the parity, and
`Field.Assert.equal ((of_int 2 * y) + is_odd) x`, whose `y` and `is_odd` ARE §15's entry scalars and
whose `x` IS §18a's statement word. -/
def splitRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let ps := splitPairs s
  packHalves ((ps.zip (List.range ps.length)).flatMap (fun pa =>
      [ ([some (xScal s sp pa.1.2), some (xScal s sp pa.1.2), some (xScal s sp pa.1.2)], cBool)
      , ([some (xSplitW s sp pa.2), some (xScal s sp pa.1.1), some (xScal s sp pa.1.2)],
         cSplit 1) ]))
  ++ (ps.zip (List.range ps.length)).map (fun pa =>
       probeRow wired (xSplitW s sp pa.2) (xScal s sp pa.1.1))

/-- W-SPLIT's variable environment — the statement word each pair recomposes. ⚠ It is `prevWordVal`
and no longer `2y + b`: the arrow reversed at `w9_prev`, and writing the derived form here would put
one value under two definitions the moment they could disagree. -/
def splitEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let ps := splitPairs s
  (ps.zip (List.range ps.length)).map (fun pa =>
    (xSplitW s sp pa.2, (prevWordVal (xhatWordOf (xhAt s pa.1.1)) : Int)))

/-! ## §17 — ⚑ **W-FTCOMM**: `Common.ft_comm`, and the ONE word §13 had wrong at source.

`wrap_verifier.ml:655-666` calls `Common.ft_comm` (`common.ml:238-256`). Read at source, in
upstream's own order:

    let scale_fast = scale_fast ~num_bits:Other_field.Packed.Constant.size_in_bits   (* :658-659 *)
    let _, [ sigma_comm_last ] = Vector.split m.sigma_comm (Permuts_minus_1 + 1)
    let f_comm = List.reduce_exn ~f:( + ) [ plonk.perm * sigma_comm_last ]
    let chunked_t_comm =
      let n = Array.length t_comm in
      let res = ref t_comm.(n - 1) in
      for i = n - 2 downto 0 do res := t_comm.(i) + scale !res plonk.zeta_to_srs_length done ;
      !res
    f_comm + chunked_t_comm + negate (scale chunked_t_comm plonk.zeta_to_domain_size)

⚠ ⚑ **THEY ARE `scale_fast`, NOT `scale_fast2` — §13 ITEM 4 WAS WRONG AT SOURCE.**
`wrap_verifier.ml:658-659` SHADOWS `scale_fast` with `Ops.scale_fast ~num_bits:255` and passes THAT
as `~scale`. The difference is this section's whole shape:

  * `scale_fast` (`plonk_curve_ops.ml:220-222`) is `scale_fast_unpack` and nothing else — no
    `(s_div_2, s_odd)` split, no `Boolean.typ`, no top-bit-zero loop, no `G.if_` mux and no
    correction to cancel, because the scalar is already a `Shifted_value.Type1` and
    `(2^255 + 2s + 1)·g` IS the value `ft_comm` wants.
  * its chunk count is `num_bits / bits_per_chunk` under a `[%test_eq]` that the division is EXACT
    (`plonk_curve_ops.ml:149-151`) — **not** `chunks_needed ~num_bits:(n−1)`. At 255 both land on
    51, so the row census agrees; the derivation does not, and a width that was not a multiple of
    five would diverge rather than round up.
  * so a ladder here is one `CompleteAdd` seed + `51 × (VarBaseMul, Zero)` + one `n₀ = 0` half,
    against §15's ladder which additionally carries four halves, a mux and an alternative add.

⚑ **`List.reduce_exn` ON A SINGLETON APPLIES `f` ZERO TIMES**, so `f_comm` costs one ladder and NO
`add_fast`. The adds are the six in the fold, `f_comm + chunked_t_comm`, and the final `+ negate …`
— eight, left-associated as OCaml's `+` is.

## ⚑ THE CENSUS THIS SECTION CLOSES

`VarBaseMul 2417` in Mina's own compiled `wrap-transaction` is `1805` (W-XHAT) `+ 408` (here)
`+ 204` (W-BULLET's four `scale_fast`), and **408 = 8 × 51**. The eight are `1`
(`perm · sigma_comm_last`) `+ 6` (the fold at `tComms = 7`) `+ 1` (`zeta_to_domain_size`) —
`tComms + 1`, which is why the smoke shape's `tComms = 2` gives three.

## ⚑ WHAT WIRES IN, AND WHAT DOES NOT

  * ⚑ **THE FIRST LADDER'S BASE IS W-KEY'S OUTPUT.** `~verification_key:m` is `step_plonk_index`,
    i.e. `choose_key`'s one-hot fold (`wrap_main.ml:215-220`), so `sigma_comm_last` is the pair of
    SEALED variables §14 emits at coordinates 12 and 13 — `index_to_field_elements` flattens
    `sigma_comm` FIRST (`side_loaded_verification_key.ml:159-183`) and `Permuts.n = 7`, so
    `sigma_comm.(6)` is coordinates 12 and 13. This section READS those variables rather than
    pinning a constant, and that σ tie is the one place `ft_comm` is not free.
  * **`t_comm` is witnessed** (`wrap_main.ml:387-396` → `Plonk_types.Messages.typ`), so the seven
    points are free here exactly as they are upstream, at named fixture values.
  * ⚠ **The three scalars are DEFERRED VALUES and therefore free.** `plonk.perm`,
    `plonk.zeta_to_srs_length` and `plonk.zeta_to_domain_size` are checked by the NEXT proof
    (§13's W-FINALIZE), not here. ⚑ There are **three variables and eight ladders**: all six fold
    ladders share `zeta_to_srs_length`, so six `Field.Assert.equal !n_acc scalar` land on ONE σ
    class. That is upstream's shape, and `ftc_six_fold_ladders_share_one_scalar` pins it.

## ⚑ THE DEFECT CLASSES, INSIDE THIS SUB-CIRCUIT

  1. **Free ladder seeds.** Every ladder opens `acc = ref (add_fast base base)` and
     `n_acc = ref Field.zero` (`plonk_curve_ops.ml:157-158`). Both are emitted — a `CompleteAdd`
     DEFINING `acc₀ = 2·base` and a `Generic` half pinning `n₀ = 0`, per ladder — and
     `ftc_every_ladder_seed_is_pinned` reads both off the emitted row list.
  2. ⚑ **PROVER-CHOSEN DECOMPOSITION, AND HERE IT IS NOT CLOSED — UPSTREAM OR HERE.**
     `scale_fast_unpack` witnesses `bits_msb` at `Typ.array ~length:255 Field.typ` — 255 FREE cells,
     booleanity coming from the `EC_scale` gate — and ties them to the scalar ONLY through
     `Field.Assert.equal !n_acc scalar` over `Fq` (`:207`). `scale_fast2` adds a top-bit-zero that
     forces `B < 2^254 < q`, hence canonical (§16b); **`scale_fast` has no such loop at all.** `B`
     ranges over `[0, 2^255)` and `q < 2^255`, so `B` and `B + q` are BOTH admissible for every
     scalar below `2^255 − q` — all but a `2^-128` fraction. The ladder multiplies by `B`, so the
     two choices differ by `2q·g ≠ O`. Emitted as upstream has it, and named by
     `ftc_scale_fast_admits_two_decompositions`, which EXHIBITS the second representative rather
     than describing it. Emitting a top-bit-zero here would be a DIVERGENCE from `wrap_main`, not a
     fix to it; §13's stricter-than-upstream list is where such a thing would have to be argued.
  3. **Absorbed-but-not-consumed.** ⚠ **`t_comm` STAYS ON `WRAP_UNCONSUMED` and the entry is
     REWRITTEN, not deleted** — exactly as `x_hat` did at `w6_xhat`. This section CONSUMES the seven
     points into `ft_comm`, but `ft_comm` itself is read by `Split_commitments.combine` and
     `check_bulletproof` (`wrap_verifier.ml:680,688`), which are W-COMBINE and W-BULLET and are not
     assembled. A value derived from a free witness and then used by nothing constrains nothing;
     striking the entry on the strength of "a sub-circuit now computes it" is the metric-gaming
     §2c exists to refuse. The count stays **8**.
  4. **Constants pinned against their own definitions.** This section owns NO curve constant: the
     first base is W-KEY's variable, the rest are the fold's own outputs, and the `t_comm` fixtures
     are doublings of `MinaStepSrsLagrange` points, which `MinaStepSrsLagrangePin` grounds.

## ⚑ WHERE THIS SECTION IS STRICTER THAN UPSTREAM

  * **`Inner_curve.negate`** is `(x, F.negate y)` — a `Cvar` scale, zero rows (`snarky_curve.ml:206`).
    This file emits one `Generic` half so the negated ordinate is a constrained cell the closing add
    reads, exactly as §15 does for the fold's output. Recorded, not claimed as conformance. -/

/-- `Other_field.Packed.Constant.size_in_bits` — the width `wrap_verifier.ml:658-659` fixes for
every `ft_comm` ladder. -/
def FTC_BITS : Nat := 255
/-- ⚑ `scale_fast_unpack`'s OWN chunk count: `num_bits / bits_per_chunk` under a `[%test_eq]` that
the remainder is zero (`plonk_curve_ops.ml:149-151`). NOT `chunksNeededQ`. -/
def FTC_CHUNKS : Nat := FTC_BITS / BITS_PER_CHUNK

/-- The ladders `ft_comm` runs: one for `perm`, `tComms − 1` for the `chunked_t_comm` fold, one for
`zeta_to_domain_size`. -/
def ftcLadders (s : WrapShape) : Nat := s.tComms + 1

/-- Which of the THREE deferred scalars ladder `l` uses: `0 = perm`, `1 = zeta_to_srs_length`
(all six fold ladders), `2 = zeta_to_domain_size`. -/
def ftcScalarIdx (s : WrapShape) (l : Nat) : Nat :=
  if l == 0 then 0 else if l < s.tComms then 1 else 2

/-- The three deferred values `ft_comm` scales by — `plonk.perm`, `plonk.zeta_to_srs_length`,
`plonk.zeta_to_domain_size`, at Mina slots **4, 2 and 3**.

⚑ **MEASURED, NOT DRAWN, SINCE 2026-08-05.** These were `wrapFixtureQ 22 j`, a deterministic filler.
They are now `expand_deferred`'s own recomputation over a real step proof's transcript, read out of
`PreparedStatement::to_public_input(40)` — Mina's function — and carried by
`MinaWrapDeferredWords`. They are still not DERIVED here and cannot be: `wrap_main` reads all three
out of its public input and checks none of them, and their checker is the next proof's
`finalize_other_proof`. What changed is that the number a verifier now sees at slot 2 is a real
`ζ^(2^16)` rather than an arithmetic sequence, and `closingRows` ties the cell to the slot. -/
def ftcSVal (j : Nat) : Nat :=
  if j == 0 then DEF_PERM
  else if j == 1 then DEF_ZETA_TO_SRS_LENGTH
  else DEF_ZETA_TO_DOMAIN_SIZE

/-- `messages.t_comm.(j)` — witnessed upstream (`Plonk_types.Messages.typ`), fixtures here, and on
the curve because they are doublings of real SRS Lagrange bases. -/
def ftcTVal (j : Nat) : Nat × Nat := dblAQ (xhatBase (j + 1))

/-- A scalar's 255 bits, MSB-first — what `scale_fast_unpack` unpacks at `Field.typ`
(`plonk_curve_ops.ml:151-156`). -/
def ftcBitsOf (v : Nat) : List Nat :=
  (List.range FTC_BITS).map (fun k => v / 2 ^ (FTC_BITS - 1 - k) % 2)

/-- One `scale_fast` ladder, seeded exactly as upstream: `acc₀ = add_fast base base`, `n₀ = 0`. -/
def ftcLadderOf (T : Nat × Nat) (v : Nat) : TermDataQ := runVbmQ T (addAQ T T) (ftcBitsOf v)

/-- …and the point it leaves: `(2^255 + 2v + 1)·T`. -/
def ftcScaledOf (T : Nat × Nat) (v : Nat) : Nat × Nat := (ftcLadderOf T v).accs.getLastD (0, 0)

/-- `sigma_comm_last` — `choose_key`'s selected coordinates 12 and 13. -/
def ftcSigmaLast (t : WrapData) : Nat × Nat :=
  (keyConst t.br.idx 12, keyConst t.br.idx 13)

/-- `res` after `a` iterations of `common.ml:247-251`, counting DOWN from `t_comm.(n−1)`. -/
def ftcResVal (s : WrapShape) : Nat → Nat × Nat
  | 0 => ftcTVal (s.tComms - 1)
  | a + 1 => addAQ (ftcTVal (s.tComms - 2 - a)) (ftcScaledOf (ftcResVal s a) (ftcSVal 1))

/-- `chunked_t_comm` (`common.ml:246-253`). -/
def ftcChunked (s : WrapShape) : Nat × Nat := ftcResVal s (s.tComms - 1)
/-- `f_comm` (`common.ml:245`) — one ladder, no add. -/
def ftcFComm (t : WrapData) : Nat × Nat := ftcScaledOf (ftcSigmaLast t) (ftcSVal 0)
/-- `f_comm + chunked_t_comm` (`common.ml:255`). -/
def ftcSum1 (t : WrapData) : Nat × Nat := addAQ (ftcFComm t) (ftcChunked t.sh)
/-- `scale chunked_t_comm plonk.zeta_to_domain_size` (`common.ml:256`). -/
def ftcLastScaled (t : WrapData) : Nat × Nat := ftcScaledOf (ftcChunked t.sh) (ftcSVal 2)
/-- ⚑ **`ft_comm`** — `f_comm + chunked_t_comm + negate (…)`. -/
def ftcOut (t : WrapData) : Nat × Nat := addAQ (ftcSum1 t) (negAQ (ftcLastScaled t))

/-- Ladder `l`'s base VALUE: W-KEY's `sigma_comm_last`, then the fold's running `res`. -/
def ftcBaseVal (t : WrapData) (l : Nat) : Nat × Nat :=
  if l == 0 then ftcSigmaLast t else ftcResVal t.sh (l - 1)

/-! ### §17a — the variable layout. -/

/-- The ft_comm region starts after W-PREV's, so nothing below `w8_ftcomm` moves. ⚠ It used to start
after a W-SPLIT region of `(splitPairs s).length` cells; that region is gone (§16), and W-PREV's is
where the split's `x` now lives. -/
def baseFtc (s : WrapShape) (sp : SpAcc) : Nat := basePrev s sp + nPrevVars s
/-- `messages.t_comm.(j)`'s two cells. -/
def ftcTV (s : WrapShape) (sp : SpAcc) (j : Nat) : PVar × PVar :=
  (.external (baseFtc s sp + 2 * j), .external (baseFtc s sp + 2 * j + 1))
/-- The three deferred scalars. -/
def ftcSV (s : WrapShape) (sp : SpAcc) (j : Nat) : PVar :=
  .external (baseFtc s sp + 2 * s.tComms + j)
/-- Per-ladder stride: `chunks + 1` accumulator points and `chunks` interior counters. -/
def FTC_STRIDE : Nat := 3 * FTC_CHUNKS + 2
def ftcBaseL (s : WrapShape) (sp : SpAcc) : Nat := baseFtc s sp + 2 * s.tComms + 3
def ftcAccX (s : WrapShape) (sp : SpAcc) (l j : Nat) : PVar :=
  .external (ftcBaseL s sp + FTC_STRIDE * l + 2 * j)
def ftcAccY (s : WrapShape) (sp : SpAcc) (l j : Nat) : PVar :=
  .external (ftcBaseL s sp + FTC_STRIDE * l + 2 * j + 1)
/-- ⚑ Ladder `l`'s counter at chunk boundary `j`. At `j = FTC_CHUNKS` it IS the scalar's own
variable — `plonk_curve_ops.ml:207`'s `Field.Assert.equal !n_acc scalar` as a σ class rather than as
a row, which is what makes the ladder's bits the multiplier `scale_fast` actually used. -/
def ftcCnt (s : WrapShape) (sp : SpAcc) (l j : Nat) : PVar :=
  if j == FTC_CHUNKS then ftcSV s sp (ftcScalarIdx s l)
  else .external (ftcBaseL s sp + FTC_STRIDE * l + 2 * (FTC_CHUNKS + 1) + j)
def ftcBaseR (s : WrapShape) (sp : SpAcc) : Nat := ftcBaseL s sp + FTC_STRIDE * ftcLadders s
/-- The fold's running `res` after `a` iterations. `a = 0` IS `t_comm.(n−1)`, which is a witnessed
point and not a new cell. -/
def ftcResVar (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar × PVar :=
  if a == 0 then ftcTV s sp (s.tComms - 1)
  else (.external (ftcBaseR s sp + 2 * (a - 1)), .external (ftcBaseR s sp + 2 * (a - 1) + 1))
def ftcBaseO (s : WrapShape) (sp : SpAcc) : Nat := ftcBaseR s sp + 2 * (s.tComms - 1)
def ftcSum1V (s : WrapShape) (sp : SpAcc) : PVar × PVar :=
  (.external (ftcBaseO s sp), .external (ftcBaseO s sp + 1))
def ftcNegY (s : WrapShape) (sp : SpAcc) : PVar := .external (ftcBaseO s sp + 2)
def ftcOutV (s : WrapShape) (sp : SpAcc) : PVar × PVar :=
  (.external (ftcBaseO s sp + 3), .external (ftcBaseO s sp + 4))
def nFtcVars (s : WrapShape) (sp : SpAcc) : Nat := ftcBaseO s sp + 5 - baseFtc s sp

/-! ### §17b — ⚑⚑ **THE THREE BLOCKS ABOVE W-FTCOMM, AND WHY EACH IS A CAP.**

`baseWh` (§21a), `baseFin` (§19e) and `baseComb` (§23a) were **each literally `baseFtc s sp +
nFtcVars s sp`** until 2026-08-05 — three sub-circuits' variable regions at ONE address. That was
sound only while no rung's `rungsUpto` held two of the three, which was an accident of the assembly
order and not a property of the layout: `.wraphack`, `.finalize` and `.combine` were built
concurrently as sibling branches off `.prev`. A rung composing two of them would have aliased two
regions, and it would NOT have failed loudly — `placeChecked` sees one variable where two were meant,
merges two σ classes that were never meant to meet, and the emitted witness makes cells agree that
nothing asserted. That is the class §12 spends its whole length refusing, in a base address.

They are now STACKED, and the space above W-FTCOMM is three disjoint blocks:

    [baseWh  , +WH_REGION_CAP  )    W-WRAPHACK's three sponges, then W-CLOSE's one cell
    [baseFin , +FIN_REGION_CAP )    W-FINALIZE's lifts, columns and programs, then W-FINSPONGE's
    [baseComb, +COMB_REGION_CAP)    W-COMBINE's fold, then W-BULLET's opening check

⚑ **AND EACH BLOCK IS A CAP, NOT A SIZE — for a measured reason.** Stacking a block on the ACTUAL
size of the one below needs that size, and W-FINALIZE's is `finStride fa =
(fa.getD 0 default).fp.prog.size` plus `finSpSize`, both computed by RUNNING the program builder.
Threading them into `baseComb (s : WrapShape) (sp : SpAcc)` would drag a `finBuild` into every one of
`combSlot`'s reductions and take §23/§24's pins with it — and an `Array` in `whnf` is its `List`
model, so a `StateM (Array _)` program is not kernel-reachable at all: `.size` alone fails at
1 000 000 heartbeats. So each block declares a cap that is a **constant in the shape**, every base
reduces without the builder, and `EmitWrapMainJson` **REFUSES** to emit a rung whose gates reference
a cell outside its own block. This is the memo-with-an-obligation shape `WrapShape.xhatXY` and
`FIN_DEFERRED_*` already use twice; the obligation here is `regionEscape` (§7).

⚠ **THE FAIL-CLOSED LEG IS THE DESIGN, NOT A GARNISH.** A cap without it is a number that drifts
from the region it claims to bound, and the drift is silent aliasing. `regionEscape` reads the
EMITTED gates, so it is a second and independent source against the caps' arithmetic rather than a
pin against their own definition — and it checks BOTH ends, because an escape DOWNWARD into the
block below is exactly the aliasing this layout exists to refuse and a max-index check cannot see it.

⚠ Two of the three caps are EXACT — `WH_REGION_CAP` is `nWhVars s + 1` and `COMB_REGION_CAP` is
`nCombVars s + nBullVars s`, because those regions ARE shape arithmetic and a cap with slack there
would be slack nothing needs. Only W-FINALIZE's carries headroom, and inside it only the two
builder-computed summands are capped rather than counted. -/

/-- A half-open block of the external variable space: the `n` cells from `b`. The three blocks above
W-FTCOMM are pairwise disjoint in this predicate for EVERY shape, EVERY sponge and EVERY cell —
`no_rung_holds_two_colliding_regions`, whose red control re-stacks the same three caps at one address
and exhibits the shared cell. -/
def inBlock (b n x : Nat) : Prop := b ≤ x ∧ x < b + n

instance (b n x : Nat) : Decidable (inBlock b n x) :=
  inferInstanceAs (Decidable (b ≤ x ∧ x < b + n))

/-- Ladder `l`'s base VARIABLES: W-KEY's sealed coordinates 12/13, then the fold's `res`. -/
def ftcBaseVar (t : WrapData) (l : Nat) : PVar × PVar :=
  let s := t.sh
  let kv := keyVars s (baseKey s t.sp)
  if l == 0 then (kv.acc 12 (s.branches - 1), kv.acc 13 (s.branches - 1))
  else ftcResVar s t.sp (l - 1)

/-- The two rows of ladder `l`'s chunk `j`, laid out exactly as §15's — `scale_fast` and
`scale_fast2` share `scale_fast_unpack`, so they share the gate. ⚑ The difference is what is NOT
here: no top-bit-zero cells, so all five bit cells of every chunk stay in ADVICE.
⚠ `td` and `bits` are PARAMETERS, computed once per ladder by the caller. Recomputing the ladder
per chunk — which is what a `xhChunkRows`-shaped signature would do — is 51 replays of a 255-step
chain with three `qInv` per step, per ladder. -/
def ftcChunkRows (s : WrapShape) (sp : SpAcc) (bv : PVar × PVar) (l : Nat)
    (td : TermDataQ) (bits : List Nat) (j : Nat) : List WRow :=
  let ax : Nat → Int := fun n => ((td.accs.getD n (0, 0)).1 : Int)
  let ay : Nat → Int := fun n => ((td.accs.getD n (0, 0)).2 : Int)
  let sl : Nat → Int := fun n => (td.slopes.getD n 0 : Int)
  let bt : Nat → Int := fun n => (bits.getD n 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some bv.1, some bv.2
              , some (ftcAccX s sp l j), some (ftcAccY s sp l j)
              , some (ftcCnt s sp l j), some (ftcCnt s sp l (j + 1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (ftcAccX s sp l (j+1)), some (ftcAccY s sp l (j+1))
              , none, none, none, none, none ]
    , advice := (List.range 5).map (fun tt => (2 + tt, bt (5*j+tt)))
                ++ (List.range 5).map (fun tt => (7 + tt, sl (5*j+tt))) } ]

/-- **W-FTCOMM's ROWS.** -/
def ftcRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let L := ftcLadders s
  -- (1) every ladder's `n₀ = 0` (`plonk_curve_ops.ml:158`), batched two halves to a row.
  let seedHalves : List WRow :=
    packHalves ((List.range L).map (fun l => ([some (ftcCnt s sp l 0), none, none], cConst 0)))
  -- (2) every ladder: the `acc₀ = 2·base` seed, 51 chunks, a probe on the output.
  let ladderRows : List WRow :=
    (List.range L).flatMap (fun l =>
      let b := ftcBaseVal t l
      let v := ftcSVal (ftcScalarIdx s l)
      let td := ftcLadderOf b v
      [ caRowQ (ftcBaseVar t l) (ftcBaseVar t l) (ftcAccX s sp l 0, ftcAccY s sp l 0)
          (caWitnessQ b.1 b.2 b.1 b.2) ]
      ++ (List.range FTC_CHUNKS).flatMap (ftcChunkRows s sp (ftcBaseVar t l) l td (ftcBitsOf v))
      ++ [ probeRow wired (ftcAccX s sp l FTC_CHUNKS) (ftcAccY s sp l FTC_CHUNKS) ])
  -- (3) the fold: `res := t_comm.(i) + scale !res zeta_to_srs_length`, `i = n−2 downto 0`.
  let foldRows : List WRow :=
    (List.range (s.tComms - 1)).map (fun a =>
      let lv := ftcTVal (s.tComms - 2 - a)
      let rv := ftcScaledOf (ftcResVal s a) (ftcSVal 1)
      caRowQ (ftcTV s sp (s.tComms - 2 - a))
        (ftcAccX s sp (a + 1) FTC_CHUNKS, ftcAccY s sp (a + 1) FTC_CHUNKS)
        (ftcResVar s sp (a + 1)) (caWitnessQ lv.1 lv.2 rv.1 rv.2))
  -- (4) `f_comm + chunked_t_comm`, `Inner_curve.negate`, and the closing add.
  let lastOut := (ftcAccX s sp (L - 1) FTC_CHUNKS, ftcAccY s sp (L - 1) FTC_CHUNKS)
  seedHalves ++ ladderRows ++ foldRows
  ++ [ caRowQ (ftcAccX s sp 0 FTC_CHUNKS, ftcAccY s sp 0 FTC_CHUNKS)
         (ftcResVar s sp (s.tComms - 1)) (ftcSum1V s sp)
         (caWitnessQ (ftcFComm t).1 (ftcFComm t).2 (ftcChunked s).1 (ftcChunked s).2) ]
  ++ packHalves [ ([some lastOut.2, some (ftcNegY s sp), none], [1, 1, 0, 0, 0]) ]
  ++ [ caRowQ (ftcSum1V s sp) (lastOut.1, ftcNegY s sp) (ftcOutV s sp)
         (caWitnessQ (ftcSum1 t).1 (ftcSum1 t).2 (ftcLastScaled t).1
           (qSub 0 (ftcLastScaled t).2)) ]
  -- (5) ⚑ **THE THREE PUBLIC TIES** — `~plonk`'s `perm`, `zeta_to_srs_length` and
  -- `zeta_to_domain_size` at MINA'S slots 4, 2 and 3. `ft_comm` reads these three out of the wrap
  -- statement (`wrap_main.ml:405-414`); before 2026-08-05 this rung read three free witnesses
  -- instead, which is what made the slots look unread. The cells are unchanged — `ftcCnt` already
  -- lands each one in the last `varBaseMul` row's counter column — so this adds only the half that
  -- says the multiplier IS the public word.
  ++ packHalves
       [ ([some (.external WRAP_SLOT_PERM : PVar), some (ftcSV s sp 0), none], cEq)
       , ([some (.external WRAP_SLOT_ZETA_TO_SRS : PVar), some (ftcSV s sp 1), none], cEq)
       , ([some (.external WRAP_SLOT_ZETA_TO_DOM : PVar), some (ftcSV s sp 2), none], cEq) ]
  ++ [ probeRow wired (ftcOutV s sp).1 (ftcOutV s sp).2 ]

/-- W-FTCOMM's variable environment. -/
def ftcEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let L := ftcLadders s
  (List.range s.tComms).flatMap (fun j =>
    [ ((ftcTV s sp j).1, ((ftcTVal j).1 : Int)), ((ftcTV s sp j).2, ((ftcTVal j).2 : Int)) ])
  ++ (List.range 3).map (fun j => (ftcSV s sp j, (ftcSVal j : Int)))
  ++ (List.range L).flatMap (fun l =>
      let td := ftcLadderOf (ftcBaseVal t l) (ftcSVal (ftcScalarIdx s l))
      (List.range (FTC_CHUNKS + 1)).flatMap (fun j =>
        [ (ftcAccX s sp l j, ((td.accs.getD (5 * j) (0, 0)).1 : Int))
        , (ftcAccY s sp l j, ((td.accs.getD (5 * j) (0, 0)).2 : Int)) ])
      ++ (List.range FTC_CHUNKS).map (fun j =>
           (ftcCnt s sp l j, (td.ns.getD (5 * j) 0 : Int))))
  ++ (List.range (s.tComms - 1)).flatMap (fun a =>
      [ ((ftcResVar s sp (a + 1)).1, ((ftcResVal s (a + 1)).1 : Int))
      , ((ftcResVar s sp (a + 1)).2, ((ftcResVal s (a + 1)).2 : Int)) ])
  ++ [ ((ftcSum1V s sp).1, ((ftcSum1 t).1 : Int)), ((ftcSum1V s sp).2, ((ftcSum1 t).2 : Int))
     , (ftcNegY s sp, (qSub 0 (ftcLastScaled t).2 : Int))
     , ((ftcOutV s sp).1, ((ftcOut t).1 : Int)), ((ftcOutV s sp).2, ((ftcOut t).2 : Int)) ]

/-! ## §18 — ⚑ **W-PREV**: `wrap_main.ml:201-256` + `:340-356`, the WITNESSED PREVIOUS STATEMENT.

Read end to end at source, and it is smaller than §13 item 9 said and lands in a different place.

  * **`prev_proof_state = exists typ ~request:Req.Proof_state`** (`:201-213`). The `typ` is
    `Types.Step.Proof_state.typ (module Impl) tock_zero ~assert_16_bits:(assert_n_bits ~n:16)
    (Vector.init 2 ~f:Features.none) (Shifted_value.Type2.typ Field.typ)`
    (`composition_types.ml:1389-1409`). ⚑ **ITS CHECKS ARE TWO `Boolean.typ`s AND NOTHING ELSE**,
    which `spec.ml:414-429` decides basic by basic:

        Field                 → `Shifted_value.Type2.typ Field.typ`   no check
        Digest                → `Typ.transport Field.typ`  (`digest.ml:79-83`)         no check
        Challenge             → `Typ.field |> Typ.transport` (`limb_vector/make.ml:14-19`)  NO CHECK
        Scalar Challenge      → `Sc.typ Challenge.typ`                                  no check
        Bulletproof_challenge → `Typ.transport (Sc.typ Challenge.typ)`                   no check
        Bool                  → `Boolean.typ`                                    ONE constraint
        Branch_data           → the ONLY arm that reads `~assert_16_bits` — and the STEP per-proof
                                spec has no `Branch_data` node (`composition_types.ml:1268-1276`)

    ⚠ ⚑ **SO `~assert_16_bits` IS PASSED AND NEVER FIRES**, and §13 item 9's "a `to_field_checked` at
    a width this file does not emit (only 128)" was wrong at source: there is no width check on a
    `Challenge` anywhere in this typ. A 128-bit `B Challenge` word is an unconstrained Fq var
    upstream, and the only thing that bounds it is `scale_fast2`'s three top-bit zeros inside the
    MSM — which §15 already emits. That is the correction this section makes, and it is the reason
    W-PREV costs two rows of checks rather than twenty chains.
  * **`prev_step_accs = exists (Vector.typ Inner_curve.typ 2)`** (`:221-225`). `Inner_curve.typ`
    is `Snarky_curve.For_native_base_field(_).typ`, whose `check` IS `assert_on_curve`
    (`snarky_curve.ml:211-228`): `x² = x·x`, `x³ = x²·x`, `assert_square y (x³ + a·x + b)`. Vesta has
    `a = 0`, so `constant Params.a * x` is a `Cvar.scale` by zero and costs nothing, and `b = 5`.
    **Three R1CS constraints per point.** ⚑ And `~sg_old:prev_step_accs` (`:412`) is the SAME vector
    `wrap_verifier.ml:538` absorbs, so this section's rows run on the TRANSCRIPT's own `sg_old`
    cells — `RC_SGOLD`, which `prev_step_accs_are_on_vesta` shows really are Vesta points, so the
    check has an honest witness and the transcript does not move.
  * **`Field.Assert.equal messages_for_next_step_proof prev_proof_state.messages_for_next_step_proof`**
    (`:350-351`). One `Generic` half, and it is what closes §10's slot 12 — the wrap statement's
    word against packed word `PREV_MSG_NEXT_STEP`, which the MSM consumes as entry 64.
  * **`old_bp_chals`** (`:226-256`) is a `Vector.typ (Vector.typ Field.typ Tock.Rounds.n)` — plain
    field vars, no check — and its ONLY consumer is `hash_messages_for_next_wrap_proof` at `:341-348`.
    ⚠ **THIS SECTION DOES NOT EMIT IT**, because cells with no consumer are decoration and saying
    otherwise is the sin this campaign is named after. It is W-WRAPHACK's, together with packed
    words 55 and 56, and §13 item 8 carries it.

## ⚑ WHAT THIS RUNG CHANGES, AND WHAT IT DOES NOT

**Does:** the 67 MSM scalars become the packed image of 57 statement words instead of 67 independent
draws (`prev_word_map_is_the_packed_expansion`); `split_field`'s `x` becomes the word rather than a
cell derived downward from its own outputs; one statement word becomes a PUBLIC word; two become
`Boolean.typ`-checked; two curve points become on-curve-checked in the cells the transcript absorbs.

**Does not:** `x_hat` does not leave `WRAP_UNCONSUMED`. Sixty-six of the 67 scalars are still free
witnesses — free HERE and free UPSTREAM — so the MSM still spans the group and a prover's reach into
the transcript is the same size it was. What ties them upstream is W-FINALIZE, W-WRAPHACK and
`assert_eq_plonk`. Striking the entry because a sub-circuit now names its inputs is metric-gaming. -/

/-- Vesta's `b` (`y² = x³ + 5`) as a `Generic` half: `w₀·w₁ − w₂ − 5 = 0`, i.e.
`assert_square y (x³ + b)` at `w₀ = w₁ = y`, `w₂ = x³`. `a = 0` so no `a·x` term appears — it is a
`Cvar.scale` by zero upstream and costs no cell here either. -/
def cOnCurveQ : List Int := [0, 0, -1, 1, -(5 : Int)]

/-- ⚑ **RECORD SLOT `p`'s COMMITMENT, AS THE CIRCUIT SEES IT.** A REAL slot reads the TRANSCRIPT's
own absorbed cells (`absPtVal`), so §21's tie row joins two cells that already hold one value; the
PAD slot reads `whPadSg` — `Dummy.Ipa.Step.sg` — which the transcript never absorbs because the
`OptSponge` mask drops it.

⚠ **THE INDEX SHIFT IS THE WHOLE POINT.** Record slot `whNPad + j` is transcript slot `j`. Reading
`absPtVal t.sp T_SGOLD p` at the RECORD's index is what made a one-`verify_one` rule hash the real
accumulator into the PAD's word.

⚠ ⚑ **AND IT IS `WH_REAL_SLOTS`, NOT `t.sh.maxPrevs`, AND THE FIRST DRAFT OF THIS REPAIR USED
`t.sh.maxPrevs`.** The record is not a per-shape object: `whRows` ties slot `p`'s squeeze to
`prevWordVal (PREV_MSG_NEXT_STEP + 1 + p)`, which recomposes `STEP_PUBLIC_IN` and is the SAME step
statement whatever wrap shape is being emitted. A shape-keyed `whNPad` would make `shapeSmoke`
(a shape-keyed `whNPad` would be 0 there) hash a real accumulator into the word the step proof
publishes the PAD at —
a tie with no satisfying witness, i.e. `w11_wraphack` back in `STATEMENT_BLOCKED`. The transcript is
per-shape; the record is the pipeline's. -/
def whSlotSgAt (t : WrapData) (p : Nat) : Nat × Nat :=
  if p < whNPad WH_REAL_SLOTS then whPadSg
  else absPtVal t.sp T_SGOLD (p - whNPad WH_REAL_SLOTS)

/-- ⚑⚑ **RECORD SLOT `p`'s COORDINATE `j` — AND THE PAD SLOT HAS A CELL OF ITS OWN.**

A REAL slot is the TRANSCRIPT's own absorbed cell, because `wrap_main.ml:412` hands
`incrementally_verify_proof` the same vector `wrap_verifier.ml:538` absorbs — one `exists`, two
consumers, which is why §18b's `assert_on_curve` and §21's tie join cells that already hold one
value rather than copies.

⚠ **THE PAD SLOT IS THE HALF THAT HAS NO TRANSCRIPT CELL**, and it is not an omission: upstream
allocates all `Max_proofs_verified` points (`wrap_main.ml:221-223`) and the `OptSponge` mask drops
the padded one from the tape (`wrap_verifier.ml:511-514,538`). So it is a witness cell this rung
allocates, `assert_on_curve`d like every other, carrying `whPadSg`. Reading a transcript cell at the
RECORD's index — which is what this def did until 2026-08-07 — is how a one-`verify_one` rule put
the real accumulator where the pad belongs. -/
def sgOldVar (t : WrapData) (p j : Nat) : PVar :=
  if p < whNPad WH_REAL_SLOTS then prevPadSg t.sh t.sp p j
  else ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_SGOLD)).getD
          (2 * (p - whNPad WH_REAL_SLOTS) + j) default).wordV

/-- **W-PREV's ROWS.** Everything `wrap_main.ml:201-256` and `:350-351` cost, and nothing else. -/
def prevRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  -- (1) `Boolean.typ` on each `B Bool` word — the ONLY check the 57-word `typ` emits.
  let boolHalves : List (List (Option PVar) × List Int) :=
    (List.range XHAT_PREVS).map (fun p =>
      let v := prevW s sp (PREV_PER_PROOF_WORDS * p + PREV_SHOULD_FINALIZE)
      ([some v, some v, some v], cBool))
  -- (2) the public tie (`:350-351`) — `w9_prev`'s own public word, at MINA'S slot 12.
  let pubTie : List (List (Option PVar) × List Int) :=
    [ ([some (.external WRAP_SLOT_MSG_NEXT_STEP : PVar), some (prevW s sp PREV_MSG_NEXT_STEP), none]
      , cEq) ]
  -- (3) `assert_on_curve` on each `prev_step_accs` point — all `Max_proofs_verified` of them, over
  -- the transcript's `sg_old` cells at the REAL slots and this rung's own at the padded ones.
  let curveHalves : List (List (Option PVar) × List Int) :=
    (List.range s.maxPrevs).flatMap (fun p =>
      [ ([some (sgOldVar t p 0), some (sgOldVar t p 0), some (prevSq s sp p 0)], cMul)
      , ([some (prevSq s sp p 0), some (sgOldVar t p 0), some (prevSq s sp p 1)], cMul)
      , ([some (sgOldVar t p 1), some (sgOldVar t p 1), some (prevSq s sp p 1)], cOnCurveQ) ])
  packHalves (boolHalves ++ pubTie ++ curveHalves)
  ++ [ probeRow wired (prevW s sp PREV_MSG_NEXT_STEP) (prevW s sp 0) ]

/-- W-PREV's variable environment: the 57 witnessed words, then `assert_on_curve`'s intermediates.
⚠ The word values DUPLICATE what `xhatEnv`/`splitEnv` already carry for the words their rungs read —
`envIndex` is first-wins on an equal value, and the point of listing all 57 here is that the rung
carries the WHOLE statement rather than the part a reduced shape's MSM happens to select. -/
def prevEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  (List.range PREV_WORDS).map (fun w => (prevW s sp w, (prevWordVal w : Int)))
  -- ⚑ the padded slots' own coordinate cells — `Dummy.Ipa.Step.sg`, the value
  -- `pad_messages_for_next_wrap_proof` puts at the front (`wrap.rs:476-491`).
  ++ (List.range (whNPad WH_REAL_SLOTS)).flatMap (fun p =>
      [ (prevPadSg s sp p 0, (whPadSg.1 : Int)), (prevPadSg s sp p 1, (whPadSg.2 : Int)) ])
  -- ⚑ `assert_on_curve`'s intermediates are `sgOldVar`'s OWN square and cube, so the value must come
  -- from the RECORD — `whSlotSgAt`, not `itemVal`. Under `itemVal` these three rows were satisfied
  -- only for a `schedule`-driven tape; on a chained one the cube of the borrowed proof's abscissa
  -- sat in a cell whose `cMul` factors were the chained one's, and `cOnCurveQ` had no witness.
  ++ (List.range s.maxPrevs).flatMap (fun p =>
      let x := (whSlotSgAt t p).1
      [ (prevSq s sp p 0, (qMul x x : Int))
      , (prevSq s sp p 1, (qMul (qMul x x) x : Int)) ])

/-! ## §21 — ⚑ **W-WRAPHACK**: `wrap_hack.ml:110-137` run THREE times
(`wrap_main.ml:341-348` and `:421-431`), and the end of the public-vector gap.

⚑ **THE DENOMINATOR IS 24, NOT 40.** `wrap_main` is handed forty statement words and PINS
twenty-four of them. Words **0–4** (`combined_inner_product`, `b`, `zeta_to_srs_length`,
`zeta_to_domain_size`, `perm`) and **9** (`xi`) are deferred values it passes straight through as
`~advice` and `~plonk` (`wrap_main.ml:411-414`) and never checks — `wrap_verifier.ml:717-731`'s
`assert_eq_plonk` ties α/β/γ/ζ and nothing else. Words **30–37** are `Spec.T.Constant` padding and
**38–39** the lookup `Opt` that `G.lookup_verification_enabled` leaves off. So the census that
matters is the 24, and before this rung 22 of them were derived: 5–8, 10, 13–28, 29 at `w4_bind`,
and 12 at `w9_prev`. ⚠ 12 and 11 are the two `wrap_main.ml:340-355,419-439` owns, and 12 landed
with W-PREV. **This rung is word 11 and nothing else is left.**

## WHAT UPSTREAM ACTUALLY DOES, READ AT SOURCE

`Wrap_hack.Checked.hash_messages_for_next_wrap_proof` (`wrap_hack.ml:110-137`) is ONE Fq sponge:

  * it OPENS at `dummy_messages_for_next_wrap_proof_sponge_states.(2 − max_proofs_verified)` —
    the state a fresh sponge reaches after absorbing `whPadVectors mlmb` DUMMY challenge vectors,
    injected as `Impls.Wrap.Field.constant`. ⚑ That is `wrap_hack.ml:26-28`'s FRONT pad: `pad_vector`
    is `Vector.extend_front_exn`, and padding at the front is exactly what makes the state
    precomputable. §15c″ fixes `WH_MLMB = WH_PADDED`, so all three openings are the FRESH state and
    `transcriptRowsQ`'s init rows PIN it to zero — defect class 1, in the pad specifically.
  * it absorbs `Messages_for_next_wrap_proof.to_field_elements` (`composition_types.ml:411-418`):
    ⚑ **every old bulletproof challenge FIRST, flattened, and the commitment's `[x; y]` LAST.**
    The step side interleaves; this one does not, and getting it backwards would be a sponge over
    the right 32 values in the wrong order — a digest wearing the right name.
  * and it closes with `Sponge.squeeze_field`.

`wrap_main` runs it three times at the committed shape:

  * **`:341-348`, once per previous proof.** `{ challenge_polynomial_commitment = prev_step_accs.(p)
    ; old_bulletproof_challenges = old_bp_chals.(p) }`. Its output is NOT witnessed — `:351-355`
    puts it into `prev_statement.messages_for_next_wrap_proof`, which `pack_statement` lands at
    packed words `PREV_MSG_NEXT_STEP + 1` and `+ 2` (**55 and 56**) and `wrap_verifier.ml:542-548`
    turns into MSM entries 65 and 66. ⚑ **So this is the sub-circuit that consumes `old_bp_chals`**,
    which §18 deliberately did not emit for exactly that reason, **and it runs on the TRANSCRIPT's
    own `sg_old` cells** — `~sg_old:prev_step_accs` at `:412` is the same vector
    `wrap_verifier.ml:538` absorbs and `w9_prev` already checks on-curve.
  * **`:421-431`, once.** `{ challenge_polynomial_commitment =
    openings_proof.challenge_polynomial_commitment; old_bulletproof_challenges =
    new_bulletproof_challenges }` at `Max_proofs_verified.n`, `Field.Assert.equal`'d against
    `messages_for_next_wrap_proof_digest` — **wrap statement word 11**, this assembly's 24th
    public word.

## ⚑ WHAT THIS RUNG CHANGES, AND WHAT IT DOES NOT

**Does:** word 11 becomes a public word this circuit DERIVES, so every one of `wrap_main`'s
twenty-four pinned statement words is derived; packed words 55 and 56 stop being fixtures and become
squeezes (⚠ — see below: since 2026-08-06 they are squeezes the PUBLISHED statement does not carry,
which `wraphack_digest_is_the_emitted_squeeze` states as a refusal); `old_bp_chals` acquires its
only consumer; and `prev_step_accs` acquires a second one.

**Does not:** `sg_old` does NOT leave `WRAP_UNCONSUMED`. Hashing a free witness into a statement word
that an MSM over free scalars consumes, whose output is itself absorbed and unconsumed, does not
force `sg_old` to any value — a prover still chooses it subject only to `assert_on_curve`. The entry
is REWRITTEN, not struck. ⚠ And word 11's two inputs are free HERE and named as such: the 30
`new_bulletproof_challenges` are **W-FINALIZE's** output (§13 item 7) and
`openings_proof.challenge_polynomial_commitment` is **W-OPENINGS's** `exists` — its own
`assert_on_curve` belongs to that sub-circuit, not this one. What this rung establishes is that word
11 is the sponge's squeeze over those cells rather than a fixture the prover hands the verifier.

⚠ ⚑ **AND THE LADDER FORKS HERE, WHICH IS SAID RATHER THAN HIDDEN.** `w11_wraphack`'s `rungsUpto`
contains `w9_prev` and NOT `w10_finalize` or `w10_combine`: the three sub-circuits were assembled
concurrently as siblings off `w9_prev`, and neither reads the other's rows (`wrap_main.ml` runs
`finalize_other_proof` at `:329`, `hash_messages_for_next_wrap_proof` at `:341`, and
`Split_commitments.combine` inside `incrementally_verify_proof` at `:412`). So
`rungRows_is_a_ladder`'s two new conjuncts are the ones that HOLD — `w11_wraphack` is `w9_prev` plus
§21's rows, `w12_close` is `w11_wraphack` plus §22's — and the rung numbering already reserves
`w10_*` for the sibling branches so that whichever lands last re-bases into one chain rather than
renumbering everything. A rung table that implied `w11` contained `w10` would be the more
comfortable lie. -/

/-- Item tag for a `hash_messages_for_next_wrap_proof` absorb. -/
def T_WHACK : Nat := 10

/-- ONE sponge's absorbs: `WH_PADDED · WH_ROUNDS` challenges then the commitment's `[x; y]`. -/
def WH_ABSORBS : Nat := WH_MLMB * WH_ROUNDS + 2
/-- …its permutations at rate 2: one per odd absorb after the opening pair, plus the squeeze's
(the last absorb leaves the state at `Absorbed 2`, so the squeeze permutes). -/
def WH_PERMS : Nat := (WH_ABSORBS - 1) / 2 + 1
/-- …and the variables `runSpongeQ` allocates for it: three state cells, three per permutation and
two per absorb. `wraphack_sponge_allocation` closes this against the emitter. -/
def WH_VARS : Nat := 3 + 3 * WH_PERMS + 2 * WH_ABSORBS

/-- One wrap-hack sponge's SCHEDULE — the tape, then `Sponge.squeeze_field` (`wrap_hack.ml:137`). -/
def whSchedule (tape : List Nat) : List Ev :=
  tape.map (fun w => Ev.abs T_WHACK w) ++ [ Ev.sq .full ]

/-- …and its trajectory. `bt` is out of range, so no word is bent. -/
def whSpongeOf (base : Nat) (tape : List Nat) : SpAcc :=
  runSpongeQ base (whSchedule tape) (tape.length + 1) 0

/-- The wrap-hack region starts after **W-FTCOMM's**, so nothing below `w9_prev` moves.

⚠ ⚑ **THIS READ `basePrev s sp + nPrevVars s` AND THAT WAS AN ALIASING BUG, CAUGHT BY A SIBLING
LANE AND FIXED HERE.** That expression IS `baseFtc` (§17a), and `rungsUpto .wraphack` contains
`.ftcomm` — so W-WRAPHACK's 345 cells and W-FTCOMM's occupied **the same addresses in a circuit that
holds both**. It would not have failed loudly: `placeChecked` sees one variable where two were meant,
merges two σ classes that were never meant to meet, and the emitted witness makes cells agree that
nothing asserted. It is the class this file spends its whole §12 refusing, in a base address.

⚑ **AND THE COMPOSITION HAZARD IS CLOSED, NOT NAMED — 2026-08-05.** `baseFin` (§19e) and `baseComb`
(§23a) were BOTH this same address, sound TODAY only because no rung's `rungsUpto` contained two of
`.finalize`, `.combine`, `.wraphack`. §17b stacks all three on shape-determined CAPS, so this is the
BOTTOM block of three disjoint ones and the `rungsUpto` accident carries no weight any more. -/
def baseWh (s : WrapShape) (sp : SpAcc) : Nat := baseFtc s sp + nFtcVars s sp
def whBaseP (s : WrapShape) (sp : SpAcc) (p : Nat) : Nat := baseWh s sp + WH_VARS * p
/-- ⚑⚑ **`WH_PADDED`, NOT `s.maxPrevs` — THE RECORD'S LENGTH IS `Max_proofs_verified` AND THE
TRANSCRIPT'S IS `actual_proofs_verified`.**

`wrap.rs:2832-2846` hands the wrap circuit `prev_step_accs` and `old_bp_chals` off
`messages_for_next_wrap_proof_padded`, which `pad_messages_for_next_wrap_proof` (`wrap.rs:476-491`)
has made **two** entries long whatever the step proof carried, and `wrap.rs:2919-2932` hashes every
one of them. The `sg_old` the TRANSCRIPT absorbs is the same list masked by
`actual_proofs_verified_mask` (`wrap.rs:2280-2300`) through an `OptSponge`, so the padded slot is
computed and NOT absorbed — two counts, and `shapeWrap.maxPrevs` served both until 2026-08-07.

⚠ At BOTH shapes `maxPrevs = WH_PADDED`, which is the point of the rename: the RECORD's length is a
shape parameter and the TAPE's is not. Every one of the thirty
tracked smoke fixtures is unmoved by this split and why it stayed invisible. -/
def whBaseC (s : WrapShape) (_sp : SpAcc) : Nat := baseWh s _sp + WH_VARS * WH_PADDED
def nWhVars (_s : WrapShape) : Nat := WH_VARS * (WH_PADDED + 1)

/-- ⚑ **W-WRAPHACK'S BLOCK (§17b)** — the three sponges' cells, plus the ONE cell W-CLOSE puts at
the block's last address (`baseClose = baseWh + nWhVars`, §22). EXACT, not capped: both summands are
shape arithmetic, so a cap with slack here would be slack nothing needs.
`close_is_the_last_cell_of_the_wraphack_block` is the `rfl` that says the `+ 1` is W-CLOSE's and that
the block ends where W-CLOSE's cell does. -/
def WH_REGION_CAP (s : WrapShape) : Nat := nWhVars s + 1


/-- Record slot `p`'s sponge (`wrap_main.ml:341-348`, `wrap.rs:2919-2932`).

⚠ **Residual, named:** the 57 packed previous-statement words that `prevWordVal` feeds are a FREE
WITNESS upstream (`wrap_main.ml:226-256` checks `old_bp_chals` with no `typ` of any kind) and are
memoized into `WrapShape.xhatXY`, so routing them through a tape would make the shape depend on the
transcript. That is a design fork, not this repair.

⚠ ⚑ **AND THE PAD SLOT'S THIRTY-TWO ABSORBS ARE FREE WITNESS CELLS HERE EXACTLY AS THEY ARE
UPSTREAM** (`w.exists`, `wrap.rs:2832-2846`). What binds them is the tie `whRows` emits from the
squeeze to packed statement word 55, plus the STEP circuit publishing `messages_for_next_wrap_proof
_padding()` there. Neither side pins the preimage to the constant, and saying so is the point:
`the_pad_slot_derives_minas_own_padding_digest` is a fact about the EMITTED VALUE, not a
constraint the emitted circuit carries. -/
def whSpongeP (t : WrapData) (p : Nat) : SpAcc :=
  whSpongeOf (whBaseP t.sh t.sp p) (whTape (whSlotChals WH_REAL_SLOTS p) (whSlotSgAt t p))

/-- ⚑⚑⚑ **`new_bulletproof_challenges`, DERIVED — and it was a `wrapFixtureQ 42` FIXTURE until
2026-08-06.**

`finalize_other_proof` (`wrap_main.ml:258-338`) returns `compute_challenges ~scalar chals`, i.e.
`Scalar_challenge.to_field_checked` of each of the fifteen `Bulletproof_challenge` prechallenges of
instance `p`'s block — packed words `27·p + 11 … 27·p + 25`. §20's `finSpRows` step (4) ALREADY EMITS
those fifteen chains per instance (`tfcRowsQ … (prevW … (finBlockWord p (FIN_W_CHAL + k)))`), and
`chainEnv` puts `liftValQ s (finBlockVal p (FIN_W_CHAL + k))` in the chain's `lift` cell. So the
value the closing sponge must absorb is a value this assembly already computes; only the module
graph stopped it being written, because `liftValQ` is `…Core`'s and the fixture was `…Field`'s.

⚑ **AND THE FLATTENING IS INSTANCE-MAJOR** — `composition_types.ml:411-418` is
`Vector.to_array old_bulletproof_challenges |> Array.concat_map ~f:Vector.to_array`, so tape position
`WH_ROUNDS · p + k` is instance `p`'s round `k`. `2 · 15 = 30 = WH_MLMB · WH_ROUNDS`, the length the
sponge's schedule already fixed.

⚠ **WHAT THIS DOES AND DOES NOT CLOSE, said here rather than banked.** It closes the DERIVATION gap:
the closing digest is no longer a hash of a fixture, and
`wraphack_closing_sponge_reproduces_minas_slot_eleven` (§21a) measures that the shape is Mina's to
the digit, on Mina's own preimage. It does NOT close the SOUNDNESS
gap: `whRows` ties the sponge's last two absorbs to `sgOldVar` and its squeeze to slot 11, and the
THIRTY challenge absorbs are tied to nothing, so they remain free witness cells. Tying them means
joining them to §20's `finSpChain … k |>.lift` — which makes `.wraphack` contain `.finsponge` and is
a LADDER REBASE, not a row addition. Emitting a second copy of the fifteen chains inside `whRows`
would be two constructions of one object, which is the defect this file spends §12 refusing. -/
def whNewChal (s : WrapShape) (k : Nat) : Nat :=
  liftValQ s (finBlockVal (k / WH_ROUNDS) (FIN_W_CHAL + k % WH_ROUNDS))
def whNewChals (s : WrapShape) : List Nat :=
  (List.range (WH_MLMB * WH_ROUNDS)).map (whNewChal s)

/-- ⚑ **WRAP STATEMENT WORD 11** — `messages_for_next_wrap_proof_digest`, the value
`wrap_main.ml:421-431` `Field.Assert.equal`s. -/
def whCloseDigest (s : WrapShape) : Nat := whDigestOf (whNewChals s) whSg

/-- …and the CLOSING one (`wrap_main.ml:421-431`), whose squeeze is wrap statement word 11. -/
def whSpongeC (t : WrapData) : SpAcc :=
  whSpongeOf (whBaseC t.sh t.sp) (whTape (whNewChals t.sh) whSg)

/-- A wrap-hack sponge's squeeze — the cell it is read out of… -/
def whDigestVar (a : SpAcc) : PVar := ((a.evs.filter (fun e => !e.isAbs)).getD 0 default).srcV
/-- …and its value. -/
def whDigestVal (a : SpAcc) : Nat := ((a.evs.filter (fun e => !e.isAbs)).getD 0 default).val

/-- ⚑ The public slot word 11 lands in — **MINA'S slot 11**, which is where
`hash_messages_for_next_wrap_proof`'s closing squeeze belongs. (This was `pubWords + 1`, the top of
this assembly's own dense vector, until the layout moved to Mina's.) -/
def WH_PUB_SLOT (_s : WrapShape) : Nat := WRAP_SLOT_MSG_NEXT_WRAP

/-- **W-WRAPHACK's ROWS.** Three sponges — whose `init` rows pin each fresh opening state to zero,
i.e. the front pad at `WH_MLMB = 2` — and then the ties that make each sponge's INPUT and OUTPUT
cells the ones the rest of the assembly already has. -/
def whRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let ties : List (List (Option PVar) × List Int) :=
    (List.range WH_PADDED).flatMap (fun p =>
      let a := whSpongeP t p
      -- ⚑ THE LAST TWO ABSORBS ARE `prev_step_accs.(p)` — the TRANSCRIPT's own `sg_old` cells, not
      -- a second copy of them. This is what makes `x; y` last rather than first observable.
      -- ⚠ ⚑ **ONLY FOR A REAL SLOT.** A PADDED slot's commitment is `Dummy.Ipa.Step.sg`, which the
      -- transcript's `OptSponge` never absorbs (`wrap.rs:2280-2300`), so there is no cell to tie to
      -- and emitting one would tie the pad's absorb to a REAL accumulator — the exact aliasing this
      -- repair removes. Its binding is the squeeze tie below and nothing else, as upstream.
      (if p < whNPad WH_REAL_SLOTS then [] else
        (List.range 2).map (fun j =>
          ([some (a.evs.getD (WH_MLMB * WH_ROUNDS + j) default).wordV,
            -- ⚠ ⚑ `sgOldVar` is RECORD-indexed since 2026-08-07 and does the `whNPad` shift
            -- itself; this line subtracted it a SECOND time and the smoke rung stopped proving
            -- (`Prover("rest of division by vanishing polynomial")`) — the pad's cell tied to the
            -- real accumulator's absorb.
            some (sgOldVar t p j), none],
           cEq)))
      -- …and the squeeze IS packed statement word 55 / 56, which the MSM consumes as entry 65 / 66.
      ++ [ ([some (whDigestVar a), some (prevW s sp (PREV_MSG_NEXT_STEP + 1 + p)), none], cEq) ])
    -- ⚑ …and the closing squeeze IS wrap statement word 11 (`wrap_main.ml:421-431`).
    ++ [ ([some (.external (WH_PUB_SLOT s) : PVar), some (whDigestVar (whSpongeC t)), none], cEq) ]
  (List.range WH_PADDED).flatMap (fun p =>
    transcriptRowsQ (whBaseP s sp p) (whSpongeP t p) wired)
  ++ transcriptRowsQ (whBaseC s sp) (whSpongeC t) wired
  ++ packHalves ties

/-- W-WRAPHACK's variable environment — the three sponges'. ⚠ The `sg_old` absorb cells duplicate
values `spongeEnv (baseSp …)` already carries for the transcript's own cells; they are DIFFERENT
variables holding ONE value, which is what the tie rows say and what a σ class means. -/
def whEnv (t : WrapData) : VarEnv :=
  (List.range WH_PADDED).flatMap (fun p => spongeEnv (whBaseP t.sh t.sp p) (whSpongeP t p))
  ++ spongeEnv (whBaseC t.sh t.sp) (whSpongeC t)

/-! ## §22 — ⚑ **W-CLOSE**: `wrap_main.ml:419-420`, and it is one constraint.

§13's last entry. `with_label __LOC__ (fun () -> Boolean.Assert.is_true bulletproof_success)` —
`bulletproof_success` is `check_bulletproof`'s `` `Success `` (`wrap_verifier.ml:383-437`), and
`Boolean.Assert.is_true b` is `assert_equal (b :> Field.t) Field.one`: **ONE R1CS constraint**, one
`Generic` half here.

✅ **AND ITS INPUT IS W-BULLET'S — TIED SINCE 2026-08-05.** The cell this rung pins to 1 used to be a
FREE WITNESS that `closeEnv` simply set to `1`, so the rung asserted a fact about a variable nothing
computed. It is now σ-tied to `bullEqV s sp 12` — `equal_g`'s `Boolean.all` output, W-BULLET's own
verdict — and `closeEnv` **COMPUTES** it as `bullLhs t v == bullRhs t v` off `bullData` rather than
writing `1`. So the two-row rung now says: *the opening equation's verdict is this cell, and this
cell is 1.* If `equal_g` ever landed on 0 the `cConst 1` half would have NO satisfying witness and the
rung would refuse — which is exactly what it could not do while the witness was a constant.

⚠ **WHAT THAT STILL DOES NOT BUY, AND SAYING OTHERWISE WOULD BE THE WHOLE DEFECT.** `equal_g`
refuses no on-curve substitution: `G`, `z₁` and `z₂` reach `check_bulletproof` through
`Openings.Bulletproof.typ` with NO binder anywhere in `wrap_main` (§24's own note), so for any `lhs`
on the curve a prover can solve for a `G` that closes the opening. The equation constrains the TRIPLE
and pins none of its three legs; what binds them is the NEXT proof's `finalize_other_proof`. So this
is "the verdict of a check that refuses little is now required" — not "the opening is checked".

⚑ **THE PRECONDITION THIS RUNG NEEDED, AND IT IS NOW MET.** `rungsUpto .close` holds TWO block
owners — `.wraphack` and `.combine` — because `.bullet` is under `.close`. `rungRegion` used to
return ONE `(base, cap)` per rung, so every gate W-BULLET contributes (all in the `baseComb` block)
would have been a region escape against W-WRAPHACK's block and `EmitWrapMainJson` would have REFUSED
the rung. `rungRegions` returns a LIST and `w12_close` DECLARES both blocks; the escape check still
bites on anything outside both, and §17b already proves the blocks pairwise disjoint for every `x`,
so this is a generalization and not a relaxation. `no_rung_holds_two_colliding_regions`'s `≤ 1`
conjunct is retired with it — it was already marked "kept, no longer load-bearing", and keeping a
count that now refuses a legitimate rung would be worse than deleting it. -/

/-- The closing region: one cell, and it is the LAST cell of W-WRAPHACK's block (§17b). -/
def baseClose (s : WrapShape) (sp : SpAcc) : Nat := baseWh s sp + nWhVars s

/-- ⚑ **W-CLOSE'S CELL IS THE BLOCK'S LAST**, general over every shape and every sponge, by `rfl` —
so `WH_REGION_CAP`'s `+ 1` is this rung's cell and not headroom, and a second closing cell would have
to move `baseFin`. -/
theorem close_is_the_last_cell_of_the_wraphack_block (s : WrapShape) (sp : SpAcc) :
    baseClose s sp + 1 = baseWh s sp + WH_REGION_CAP s := by
  simp [baseClose, WH_REGION_CAP, Nat.add_assoc]

/-- `bulletproof_success` — `check_bulletproof`'s `` `Success `` (`wrap_verifier.ml:436`). -/
def bpSuccessVar (s : WrapShape) (sp : SpAcc) : PVar := .external (baseClose s sp)

/-! ## §19 — ⚑ **W-FINALIZE**: `finalize_other_proof`, and the fact that decides it.

`wrap_verifier.ml:820-1049`, run `Max_proofs_verified.n` times from `wrap_main.ml:329-336`
(`Vector.mapn` over `prev_proof_state.unfinalized_proofs`), so this rung emits **`maxPrevs` instances**
and not one.

⚑⚑ **`Scalars.Tock` IS NOT `Scalars.Tick` WITH DIFFERENT LITERALS, AND THE DIFFERENCE IS MEASURED,
NOT ASSERTED.** `plonk_checks/scalars.ml` carries both; `Tick` is `:105-3403`, `Tock` is
`:3405-4250`. Diffed at source (2026-08-04, hex literals normalised so only STRUCTURE compares):

  * the `let x_0 … let x_48` prefix — 225 lines — is **byte-identical** between the two modules;
  * the tails diverge at exactly one hunk, `@@ -576,1813 +576,4 @@`: the first 575 tail lines agree
    line for line, then `Tick` continues for **1813** lines and `Tock` for **4**.
  * Those 1813 lines are the `if_feature` arms — `RangeCheck0`, `RangeCheck1`, `ForeignFieldAdd`,
    `ForeignFieldMul`, `Xor16`, `Rot64` and the lookup argument — and they are the ONLY consumers of
    `beta`, `gamma`, `joint_combiner`, `unnormalized_lagrange_basis`, `vanishes_on_last_4_rows` and
    `if_feature`. `Tock` binds all six to `_` (`:3423-3430`) because with the arms deleted nothing
    reads them. `Tock`'s four are a trailing `+ field "0x00…0"`.
  * So `Tock.constant_term` is **exactly the six always-on gate bodies**, α-combined behind their
    selectors: `Poseidon` (15, α¹⁻¹⁴), `VarBaseMul` (21, α¹⁻²⁰), `CompleteAdd` (7, α¹⁻⁶), `EndoMul`
    (11, α¹⁻¹⁰), `EndoMulScalar` (11, α¹⁻¹⁰), `Generic` (2, α¹) — measured by scanning the tail's
    six `cell (var (Index …, Curr))` regions. Both `index_terms` are `of_alist_exn []`.

⚠ **AND THE ALPHA POWERS REALLY ARE SHARED ACROSS THE GATES.** `scalars_env`'s `alpha_pow` is one
`Array.create ~len:71` (`plonk_checks.ml:330-338`), so `alpha_pow 1` inside the `Poseidon` block and
`alpha_pow 1` inside the `VarBaseMul` block are the SAME field element. That is what the generated
module does; §19 emits it unaltered, exactly as `scale_fast`'s two admissible decompositions are
emitted unaltered at §15. Bounding either here would be a divergence from `wrap_main`, not a fix.

⚑ **WHAT THIS RUNG IS FOR, AND WHERE IT SITS IN THE FOUR LEGS.** `finalize_other_proof` returns
`Boolean.all [xi_correct; b_correct; combined_inner_product_correct; plonk_checks_passed]`. This
rung emits **`plonk_checks_passed`** — `Plonk_checks.checked` (`plonk_checks.ml:476-500`), whose
`perm` scalar is compared against the previous statement's own deferred `perm` through
`Shifted_value.Type2.to_field` — together with everything `plonk_checks_passed` needs and nothing
else: `scalars_env`, `Scalars.Tock.constant_term` and `ft_eval0`. The other three legs need the
finalize SPONGE (ξ and r are its two squeezes, `:892-894`) and are named in §13 as the remainder.

⚑ **ITS INPUTS ARE `w9_prev`'s CELLS.** `deferred_values` comes from
`prev_proof_state.unfinalized_proofs`, i.e. the packed previous STEP statement §18 already witnesses.
`Per_proof.In_circuit.spec` (`composition_types.ml:1268-1276,1290-1320`) fixes the block order:
word 0 `combined_inner_product`, 1 `b`, 2 `zeta_to_srs_length`, 3 `zeta_to_domain_size`, 4 `perm`
(five `B Field`, `Shifted_value.Type2`), 5 `sponge_digest_before_evaluations`, 6 `beta`, 7 `gamma`
(raw `Challenge`), 8 `alpha`, 9 `zeta`, 10 `xi` (`Scalar Challenge`), 11–25 the fifteen
bulletproof challenges, 26 `should_finalize`. This rung CONSUMES words 4, 6, 7, 8, 9 and 26 of each
block — six statement words that were absorbed-but-not-consumed at `w9_prev`.

⚠ **α AND ζ GO THROUGH `to_field_checked`, β AND γ DO NOT.** `map_plonk_to_field`
(`wrap_verifier.ml:800-802`) maps `Scalar_challenge` fields with `scalar_to_field` and `Challenge`
fields with `Util.seal`. So this rung emits two lift chains per instance and reads the raw words for
β and γ — the same split §5 already pays for on the transcript side, at the same `ENDO_Q` and
through the same shared endo cell.

⚑ **THE EVALUATION COLUMNS ARE FREE WITNESSES HERE BECAUSE THEY ARE FREE WITNESSES UPSTREAM.**
`wrap_main.ml:262-268` obtains `evals` as `exists ty ~request:Req.Evals`. What ties them upstream is
the finalize sponge's absorption (`:844-891`) and `combined_inner_product`; both are the remainder,
so the 86 columns and `p(ζ)` stay in `WRAP_UNCONSUMED` and are named there rather than dressed up. -/

/-- `w₂ = w₀ − w₁`, the one `Generic` half §3 had no use for until the finalize program. -/
def cSubQ : List Int := [1, -1, -1, 0, 0]

/-! ### §19a — the straight-line **Fq** program.

A `Generic`-only intermediate representation: the finalize computation is 800-odd field operations
with no curve and no sponge in it, and writing them as rows by hand is how a transcription slip
becomes a proof. Every slot below `.inp`/`.wit` owns one variable and one `Generic` half, and
`finRowsQ` packs the halves two to a row exactly as `packHalves` does. -/

/-- One straight-line operation. Slot `i` is the `i`-th entry of the program. -/
inductive FOp where
  /-- ALIAS a circuit variable another rung's rows define — no row, no new variable. -/
  | inp (v : PVar)
  /-- A FREE witness cell: no defining row, so only what the program ASSERTS about it constrains it.
  Used for the two witnessed inverses (`ω⁻¹` and the C5 denominator's), each of which is checked by a
  row of the program itself. -/
  | wit (val : Nat)
  /-- A field constant, pinned by the row `w₀ = k`. -/
  | lit (val : Nat)
  | add (i j : Nat)
  | sub (i j : Nat)
  | mul (i j : Nat)
  /-- ASSERT slot `i` = slot `j`; the produced slot is inert. -/
  | aeq (i j : Nat)
  deriving Repr, Inhabited, DecidableEq

abbrev FM := StateM (Array FOp)

/-- ⚑ **`modifyGet`, NOT `get`-then-`set`, AND THE DIFFERENCE IS QUADRATIC.** `let st ← get` retains
a second reference to the array, so `st.push o` cannot reuse it and copies — one 900-op program build
becomes ~810 000 array copies. `modifyGet` threads the state LINEARLY, so `push` is destructive and
the build is O(n). Measured: the smoke shape's `w10_finalize` emission did not finish in 50 minutes
before this line and takes seconds after it. -/
def fnEm (o : FOp) : FM Nat := modifyGet (fun st => (st.size, st.push o))

def fnLit (k : Nat) : FM Nat := fnEm (.lit k)
def fnWit (k : Nat) : FM Nat := fnEm (.wit k)
def fnInp (v : PVar) : FM Nat := fnEm (.inp v)
def fnAdd (a b : Nat) : FM Nat := fnEm (.add a b)
def fnSub (a b : Nat) : FM Nat := fnEm (.sub a b)
def fnMul (a b : Nat) : FM Nat := fnEm (.mul a b)
def fnAeq (a b : Nat) : FM Nat := fnEm (.aeq a b)

/-- Evaluate the program over **Fq**. `lk` resolves `.inp` out of the surrounding circuit. -/
def fnEval (lk : PVar → Int) (prog : Array FOp) : Array Nat :=
  prog.foldl (fun (vs : Array Nat) op =>
    vs.push (match op with
      | .inp v => (lk v).toNat % qN
      | .wit x => x % qN
      | .lit x => x % qN
      | .add i j => qAdd (vs.getD i 0) (vs.getD j 0)
      | .sub i j => qSub (vs.getD i 0) (vs.getD j 0)
      | .mul i j => qMul (vs.getD i 0) (vs.getD j 0)
      | .aeq i _ => vs.getD i 0)) #[]

/-- Slot `i`'s circuit variable. `.inp` aliases; everything else owns `external (base + i)`. -/
def fnVarAt (base : Nat) (prog : Array FOp) (i : Nat) : PVar :=
  match prog.getD i default with
  | .inp v => v
  | _ => .external (base + i)

/-- The slots that need a `Generic` half. -/
def fnHalfSlots (prog : Array FOp) : List Nat :=
  (List.range prog.size).filter (fun i =>
    match prog.getD i default with | .inp _ => false | .wit _ => false | _ => true)

/-- Slot `i`'s half: three permutation columns and five coefficients. -/
def fnHalf (base : Nat) (prog : Array FOp) (i : Nat) : List (Option PVar) × List Int :=
  let V := fnVarAt base prog
  match prog.getD i default with
  | .lit k => ([some (V i), none, none], cConst (k : Int))
  | .add a b => ([some (V a), some (V b), some (V i)], cAdd)
  | .sub a b => ([some (V a), some (V b), some (V i)], cSubQ)
  | .mul a b => ([some (V a), some (V b), some (V i)], cMul)
  | .aeq a b => ([some (V a), some (V b), none], cEq)
  | _ => ([none, none, none], cNil)

/-- The program's rows. -/
def fnRows (base : Nat) (prog : Array FOp) : List WRow :=
  packHalves ((fnHalfSlots prog).map (fun i => fnHalf base prog i))

/-- The program's contribution to the variable environment. -/
def fnEnvOf (base : Nat) (prog : Array FOp) (vals : Array Nat) : VarEnv :=
  (List.range prog.size).filterMap (fun i =>
    match prog.getD i default with
    | .inp _ => none
    | _ => some ((.external (base + i) : PVar), (vals.getD i 0 : Int)))

/-! ### §19b — the SIX gate constraint bodies of `Scalars.Tock`, compiled.

Each is `KimchiVerify`'s own body, which `MinaWrapFtEval0Weld` reproduces byte-exact against a real
devnet block's `PolishToken::evaluate(linearization.constant_term)` on BOTH sides of the cycle. §19f
re-checks the compiled program's `linConst` slot against `gateLinConst` at `ZMod qN` — two
independent evaluations of the same six bodies, not a constant pinned against its own definition. -/

/-- `x⁷` — kimchi's Poseidon S-box. -/
def fnSbox (x : Nat) : FM Nat := do
  let x2 ← fnMul x x
  let x4 ← fnMul x2 x2
  let x6 ← fnMul x4 x2
  fnMul x6 x

/-- `target − (rc + Σ_c mds[j][c]·sbox(source_c))`. -/
def fnLane (mdsRow : List Nat) (rc : Nat) (sb : List Nat) (target : Nat) : FM Nat := do
  let t0 ← fnMul (mdsRow.getD 0 0) (sb.getD 0 0)
  let t1 ← fnMul (mdsRow.getD 1 0) (sb.getD 1 0)
  let t2 ← fnMul (mdsRow.getD 2 0) (sb.getD 2 0)
  let s01 ← fnAdd t0 t1
  let s ← fnAdd s01 t2
  let r ← fnAdd rc s
  fnSub target r

/-- The 15 `Poseidon` constraints, in emission order. -/
def fnPoseidon (mdsS : List (List Nat)) (c w wn : List Nat) : FM (List Nat) := do
  let ww := fun i => w.getD i 0
  let cc := fun i => c.getD i 0
  let wnn := fun i => wn.getD i 0
  let sb ← (List.range 15).foldlM (fun acc i => do let s ← fnSbox (ww i); pure (acc ++ [s])) []
  let g := fun (ix : List Nat) => ix.map (fun i => sb.getD i 0)
  let s0 := g [0, 1, 2]; let s1 := g [6, 7, 8]; let s2 := g [9, 10, 11]
  let s3 := g [12, 13, 14]; let s4 := g [3, 4, 5]
  let m := fun j => mdsS.getD j []
  let spec : List (Nat × Nat × List Nat × Nat) :=
    [ (0, 0, s0, ww 6), (1, 1, s0, ww 7), (2, 2, s0, ww 8)
    , (0, 3, s1, ww 9), (1, 4, s1, ww 10), (2, 5, s1, ww 11)
    , (0, 6, s2, ww 12), (1, 7, s2, ww 13), (2, 8, s2, ww 14)
    , (0, 9, s3, ww 3), (1, 10, s3, ww 4), (2, 11, s3, ww 5)
    , (0, 12, s4, wnn 0), (1, 13, s4, wnn 1), (2, 14, s4, wnn 2) ]
  spec.foldlM (fun acc q => do let k ← fnLane (m q.1) (cc q.2.1) q.2.2.1 q.2.2.2; pure (acc ++ [k]))
    []

/-- The 7 `CompleteAdd` constraints. -/
def fnCompleteAdd (one : Nat) (w : List Nat) : FM (List Nat) := do
  let ww := fun i => w.getD i 0
  let x1 := ww 0; let y1 := ww 1; let x2 := ww 2; let y2 := ww 3
  let x3 := ww 4; let y3 := ww 5; let inf := ww 6; let sameX := ww 7
  let s := ww 8; let infZ := ww 9; let x21Inv := ww 10
  let x21 ← fnSub x2 x1
  let y21 ← fnSub y2 y1
  let x1sq ← fnMul x1 x1
  let nsx ← fnSub one sameX
  let a ← fnMul x21Inv x21
  let k0 ← fnSub a nsx
  let k1 ← fnMul sameX x21
  let ss ← fnAdd s s
  let ssy ← fnMul ss y1
  let q2 ← fnAdd x1sq x1sq
  let t1a ← fnSub ssy q2
  let t1 ← fnSub t1a x1sq
  let p1 ← fnMul sameX t1
  let x21s ← fnMul x21 s
  let t2 ← fnSub x21s y21
  let p2 ← fnMul nsx t2
  let k2 ← fnAdd p1 p2
  let sx ← fnAdd x1 x2
  let sx3 ← fnAdd sx x3
  let s2v ← fnMul s s
  let k3 ← fnSub sx3 s2v
  let d ← fnSub x1 x3
  let sd ← fnMul s d
  let e1 ← fnSub sd y1
  let k4 ← fnSub e1 y3
  let f ← fnSub sameX inf
  let k5 ← fnMul y21 f
  let g ← fnMul y21 infZ
  let k6 ← fnSub g inf
  pure [k0, k1, k2, k3, k4, k5, k6]

/-- The 21 `VarbaseMul` constraints. -/
def fnVarBaseMul (one : Nat) (w wn : List Nat) : FM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xT := ww 0; let yT := ww 1
  let accX := fun i => ([ww 2, ww 7, ww 9, ww 11, ww 13, wnn 0] : List Nat).getD i 0
  let accY := fun i => ([ww 3, ww 8, ww 10, ww 12, ww 14, wnn 1] : List Nat).getD i 0
  let bit := fun i => ([wnn 2, wnn 3, wnn 4, wnn 5, wnn 6] : List Nat).getD i 0
  let sl := fun i => ([wnn 7, wnn 8, wnn 9, wnn 10, wnn 11] : List Nat).getD i 0
  let nPrev := ww 4; let nNext := ww 5
  let acc ← (List.range 5).foldlM (fun a i => do let aa ← fnAdd a a; fnAdd (bit i) aa) nPrev
  let dec ← fnSub nNext acc
  let rest ← (List.range 5).foldlM (fun out i => do
      let b := bit i; let s := sl i
      let ix := accX i; let iy := accY i
      let ox := accX (i + 1); let oy := accY (i + 1)
      let b2 ← fnAdd b b
      let bSign ← fnSub b2 one
      let ssq ← fnMul s s
      let rxa ← fnSub ssq ix
      let rx ← fnSub rxa xT
      let t ← fnSub ix rx
      let iy2 ← fnAdd iy iy
      let ts ← fnMul t s
      let u ← fnSub iy2 ts
      let bb ← fnMul b b
      let k0 ← fnSub bb b
      let ixT ← fnSub ix xT
      let l1 ← fnMul ixT s
      let by' ← fnMul bSign yT
      let r1 ← fnSub iy by'
      let k1 ← fnSub l1 r1
      let uu ← fnMul u u
      let tt ← fnMul t t
      let oxT ← fnSub ox xT
      let q ← fnAdd oxT ssq
      let ttq ← fnMul tt q
      let k2 ← fnSub uu ttq
      let oyiy ← fnAdd oy iy
      let l3 ← fnMul oyiy t
      let ixox ← fnSub ix ox
      let r3 ← fnMul ixox u
      let k3 ← fnSub l3 r3
      pure (out ++ [k0, k1, k2, k3])) []
  pure (dec :: rest)

/-- The 11 DEPLOYED `EndosclMul` constraints (`proof-systems` 0.3.0's `CONSTRAINTS = 11`; the 12th
distinct-point witness is not in the deployed linearization constant term). -/
def fnEndoMul (one endo : Nat) (w wn : List Nat) : FM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xt := ww 0; let yt := ww 1
  let xp := ww 4; let yp := ww 5; let n := ww 6
  let xr := ww 7; let yr := ww 8; let s1 := ww 9; let s3 := ww 10
  let b1 := ww 11; let b2 := ww 12; let b3 := ww 13; let b4 := ww 14
  let xs := wnn 4; let ys := wnn 5; let nNext := wnn 6
  let em1 ← fnSub endo one
  let t1 ← fnMul b1 em1
  let u1 ← fnAdd one t1
  let xq1 ← fnMul u1 xt
  let t3 ← fnMul b3 em1
  let u3 ← fnAdd one t3
  let xq2 ← fnMul u3 xt
  let b22 ← fnAdd b2 b2
  let v2 ← fnSub b22 one
  let yq1 ← fnMul v2 yt
  let b42 ← fnAdd b4 b4
  let v4 ← fnSub b42 one
  let yq2 ← fnMul v4 yt
  let s1sq ← fnMul s1 s1
  let s3sq ← fnMul s3 s3
  let n2 ← fnAdd n n
  let d1 ← fnAdd n2 b1
  let d1a ← fnAdd d1 d1
  let d2 ← fnAdd d1a b2
  let d2a ← fnAdd d2 d2
  let d3 ← fnAdd d2a b3
  let d3a ← fnAdd d3 d3
  let d4 ← fnAdd d3a b4
  let nC ← fnSub d4 nNext
  let xpxr ← fnSub xp xr
  let xrxs ← fnSub xr xs
  let ysyr ← fnAdd ys yr
  let yryp ← fnAdd yr yp
  let k0 ← do let t ← fnMul b1 b1; fnSub t b1
  let k1 ← do let t ← fnMul b2 b2; fnSub t b2
  let k2 ← do let t ← fnMul b3 b3; fnSub t b3
  let k3 ← do let t ← fnMul b4 b4; fnSub t b4
  let k4 ← do let a ← fnSub xq1 xp; let l ← fnMul a s1; let r ← fnSub yq1 yp; fnSub l r
  let k5 ← do
    let xp2 ← fnAdd xp xp
    let a ← fnSub xp2 s1sq
    let a2 ← fnAdd a xq1
    let m1 ← fnMul xpxr s1
    let m2 ← fnAdd m1 yryp
    let l ← fnMul a2 m2
    let yp2 ← fnAdd yp yp
    let r ← fnMul yp2 xpxr
    fnSub l r
  let k6 ← do
    let l ← fnMul yryp yryp
    let p ← fnMul xpxr xpxr
    let a ← fnSub s1sq xq1
    let a2 ← fnAdd a xr
    let r ← fnMul p a2
    fnSub l r
  let k7 ← do let a ← fnSub xq2 xr; let l ← fnMul a s3; let r ← fnSub yq2 yr; fnSub l r
  let k8 ← do
    let xr2 ← fnAdd xr xr
    let a ← fnSub xr2 s3sq
    let a2 ← fnAdd a xq2
    let m1 ← fnMul xrxs s3
    let m2 ← fnAdd m1 ysyr
    let l ← fnMul a2 m2
    let yr2 ← fnAdd yr yr
    let r ← fnMul yr2 xrxs
    fnSub l r
  let k9 ← do
    let l ← fnMul ysyr ysyr
    let p ← fnMul xrxs xrxs
    let a ← fnSub s3sq xq2
    let a2 ← fnAdd a xs
    let r ← fnMul p a2
    fnSub l r
  pure [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, nC]

/-- The 11 `EndomulScalar` constraints. `cA/cB/cC` are the quotients `11/6, −5/2, 2/3`. -/
def fnEmScalar (cA cB cC negOne three six eleven : Nat) (w : List Nat) : FM (List Nat) := do
  let ww := fun i => w.getD i 0
  let n0 := ww 0; let n8 := ww 1; let a0 := ww 2; let b0 := ww 3
  let a8 := ww 4; let b8 := ww 5
  let x := fun i => ww (6 + i)
  let cf : Nat → FM Nat := fun t => do
    let m1 ← fnMul cC t
    let s1 ← fnAdd m1 cB
    let m2 ← fnMul s1 t
    let s2 ← fnAdd m2 cA
    fnMul s2 t
  let cfs ← (List.range 8).foldlM (fun acc i => do let v ← cf (x i); pure (acc ++ [v])) []
  let dfs ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let m1 ← fnMul negOne t
      let s1 ← fnAdd m1 three
      let m2 ← fnMul s1 t
      let s2 ← fnAdd m2 negOne
      let v ← fnAdd (cfs.getD i 0) s2
      pure (acc ++ [v])) []
  let n8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← fnAdd acc acc
      let a4 ← fnAdd a2 a2
      fnAdd a4 (x i)) n0
  let a8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← fnAdd acc acc
      fnAdd a2 (cfs.getD i 0)) a0
  let b8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← fnAdd acc acc
      fnAdd a2 (dfs.getD i 0)) b0
  let c0 ← fnSub n8e n8
  let c1 ← fnSub a8e a8
  let c2 ← fnSub b8e b8
  let cr ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let a ← fnSub t six
      let b ← fnMul a t
      let c ← fnAdd b eleven
      let d ← fnMul c t
      let e ← fnSub d six
      let v ← fnMul e t
      pure (acc ++ [v])) []
  pure ([c0, c1, c2] ++ cr)

/-- `genericGateConstraint` — the double generic gate's own linearization factor, `α`-combined
inside the body exactly as the generated module writes it. -/
def fnGenericGate (genSel alpha : Nat) (c w : List Nat) : FM Nat := do
  let cc := fun i => c.getD i 0
  let ww := fun i => w.getD i 0
  let t0 ← fnMul (cc 0) (ww 0)
  let t1 ← fnMul (cc 1) (ww 1)
  let t2 ← fnMul (cc 2) (ww 2)
  let w01 ← fnMul (ww 0) (ww 1)
  let t3 ← fnMul (cc 3) w01
  let s0 ← fnAdd t0 t1
  let s1 ← fnAdd s0 t2
  let s2 ← fnAdd s1 t3
  let k1 ← fnAdd s2 (cc 4)
  let u0 ← fnMul (cc 5) (ww 3)
  let u1 ← fnMul (cc 6) (ww 4)
  let u2 ← fnMul (cc 7) (ww 5)
  let w34 ← fnMul (ww 3) (ww 4)
  let u3 ← fnMul (cc 8) w34
  let r0 ← fnAdd u0 u1
  let r1 ← fnAdd r0 u2
  let r2 ← fnAdd r1 u3
  let k2 ← fnAdd r2 (cc 9)
  let ak2 ← fnMul alpha k2
  let sum ← fnAdd k1 ak2
  fnMul genSel sum

/-- `Σᵢ αⁱ·csᵢ` over a gate's constraint list, sharing the ONE power chain the whole rung pays for. -/
def fnAlphaCombine (apow : List Nat) (cs : List Nat) : FM Nat := do
  match cs with
  | [] => fnLit 0
  | c0 :: rest =>
      (List.range rest.length).foldlM (fun acc i => do
        let t ← fnMul (apow.getD (i + 1) 0) (rest.getD i 0)
        fnAdd acc t) c0

/-! ### §19c — the wire, the config and the slots. -/

/-- ⚑ `Common.wrap_domains ~proofs_verified:1 |>.h` — the wrap evaluation domain is `2^14`, NOT the
`2^15` `Max_degree.wrap_log2` names. `common.ml:27-31` maps `0 ↦ 13, 1 ↦ 14, 2 ↦ 15`, and the devnet
wrap index that `MinaRealBlockGate.OMEGA` came off is the `14`. -/
def FIN_LOG2N : Nat := 14
/-- The `2^14`-th root of unity of `Fq`, from the real block's verifier index. -/
def FIN_OMEGA : Nat := 13720502009405270468270247285101677286753189198487843249698478072631298866919
/-- ⚑ `env.endo_coefficient` is `Endo.Wrap_inner_curve.base = Vesta.endo_base ()` (`endo.ml:5`), the
BASE endomorphism eigenvalue `5^((q−1)/3)` — **NOT** `ENDO_Q`, which is `Pallas.endo_scalar ()` and
is what `to_field_checked` lifts by. Two different cube roots in two different roles; §19f pins that
they differ. -/
def FIN_ENDO : Nat :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743
/-- The seven **Fq** coset shifts of the wrap domain, from the same real verifier index. -/
def FIN_SHIFTS : List Nat :=
  [ 1
  , 328286983623303317637963920346571898945724874896624808297627776768640590563
  , 220790353665890403705559231885806581221301230221265349993193424985261418438
  , 211720422259245489258933986578227917398506328781182391541883955346082631533
  , 211634429328372259348572816867521795029192573698954618296359582461568682420
  , 317476258975906211462498873025720239242336777696786967497139785505242641540
  , 99141114743446054294525453467100398765600279346526770105380817318185104545 ]
/-- `Shifted_value.Type2.Shift = 2^{field size in bits}` (`shifted_value.ml:180-182`), and
`Field.size_in_bits` for Fq is 255. -/
def FIN_SHIFT2 : Nat := 2 ^ 255 % qN
/-- The three `EndomulScalar` quotients `11/6, −5/2, 2/3` over `Fq`, as the CHECKED witnessed
quotients `6·cA = 11`, `2·cB = −5`, `3·cC = 2` (§19f). -/
def FIN_CA : Nat :=
  4824670384888174809315457708695329493893842746990274563279957124732227158018
def FIN_CB : Nat :=
  14474011154664524427946373126085988481681528240970823689839871374196681474046
def FIN_CC : Nat :=
  9649340769776349618630915417390658987787685493980549126559914249464454316033

/-- The 43 evaluation columns, in `to_absorption_sequence` order: `z`, the six gate selectors, the
15 witness columns, the 15 coefficient columns, the six σ columns. -/
def FIN_NCOLS : Nat := 43
def FIN_IDX_Z : Nat := 0
def FIN_IDX_SEL : Nat := 1
def FIN_IDX_W : Nat := 7
def FIN_IDX_COEFF : Nat := 22
def FIN_IDX_S : Nat := 37
/-- `Plonk_types.Permuts_minus_1.n` — the σ evals `ft_eval0` folds over, and the index of the `w_n`
`ft_eval0` seeds with. -/
def FIN_PERMUTS1 : Nat := 6

/-! #### ⚑⚑ **THE EVALUATIONS ARE MINA'S OWN WRAP PROOF'S, AND THEY NEEDED NO ENCODING.**

Until 2026-08-06 the four families below were `wrapFixtureQ` — `(11 + 1000003·(17·tag + i)) % qN`,
a mixer. The step side's twins (`KimchiStepMainCore.evVal`) are a DIFFERENT mixer, which is why
"two derivations of one quantity" could never agree: neither was about a proof.

⚠ ⚑ **AND THE REASON THAT WAS NOT A ONE-LINE CHANGE WAS RECORDED AS A FIELD BOUNDARY. THERE IS NO
FIELD BOUNDARY.** Four docblocks said these evaluations are **Fp** and "enter only through
`Other_field` (`impls.ml:167-217`)", and that the encoding — "not a fixpoint" — was the distance to
the top of the ladder. This block's OWN CONFIGURATION refutes it, and did before the sentence was
written:

  * `FIN_LOG2N = 14` is `Common.wrap_domains ~proofs_verified:1 |>.h`, the **WRAP** evaluation
    domain — not the step-transaction `2^16`;
  * `FIN_OMEGA` and `FIN_SHIFTS` are that same **Fq** wrap verifier index's root of unity and coset
    shifts, digit for digit `MinaRealBlockGate.OMEGA` and `.SHIFT`;
  * `finBuild` folds `Scalars.Tock` bodies and closes with `Shifted_value.Type2`
    (`FIN_SHIFT2 = 2^255`), the SAME-field shift. `Type1` — the one with a cross-field `c` — is
    what `wrap_main.ml:454` uses on `combined_inner_product`, and that is a different word.

`wrap_main.ml`'s `finalize_other_proof` finalizes the deferred SCALAR work of the proofs the STEP
verified, and those are **wrap** proofs over Pallas, whose scalar field IS this circuit's native Fq.
So the evaluations are native, the crossing is empty, and `the_finalize_evaluations_need_no_encoding`
says so as a theorem rather than as a paragraph.

⚑ **ONE OBJECT, READ ONCE.** `MinaRealBlockTranscript.EVZ_N` / `.EVZW_N` are `ZMod.val` of
`MinaRealBlockGate.EVZ` / `.EVZW` — the 47 `es` columns of Mina devnet block 539508's own Wrap
proof, the proof whose verifier index already supplies `FIN_OMEGA` and `FIN_SHIFTS` and whose
transcript already supplies packed statement words 32–36 (`STEP_PUBLIC_IN`'s digest, β, γ, α′, ζ′
are `MinaRealBlockTranscript.FQ_DIGEST`, `BETA_N`, `GAMMA_N`, `ALPHA_CHAL`, `ZETA_CHAL` to the
digit). Reading them here makes the config, the statement and the evaluations three views of ONE
proof instead of a real index over a mixer.

⚠ **AND THE `p` ARGUMENT IS GONE FROM THE VALUE, WHICH IS THE HONEST SHAPE.** There is ONE real Mina
wrap proof in this tree, so both blocks read it; block 0 is the one whose `should_finalize` is 0 and
whose statement words are the synthetic ramp, so its `Field.equal` gadgets still run at NONZERO
differences and `(1 − finalized)·should_finalize = 0` still has a failing instance. The argument at
`finZW0` and at §20's solve is unchanged: only the LIVE block is solved. -/

/-- The 4-entry prefix `verifier.rs:492-540` puts ahead of the 43 columns: the 2 recursion
b-polynomials, the public polynomial, then `ft`. `MinaRealBlockTranscript.evalsTape` drops exactly
these four, which is the same convention read from the other end. -/
def FIN_EV_PREFIX : Nat := 4
/-- …and where the public polynomial sits inside that prefix — `p(ζ)` / `p(ζω)`. -/
def FIN_EV_PUB : Nat := 2
/-- …and `ft`: at ζ it is `ft_eval0`, at ζω it is `ft_eval1`. -/
def FIN_EV_FT : Nat := 3

/-- The real Wrap proof's evaluation columns at ζ, as `Nat`. -/
def finEvZ : List Nat := Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N
/-- …and at ζω. -/
def finEvW : List Nat := Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N

/-- Column `k`'s value at ζ (`j = 0`) / at ζω (`j = 1`) — Mina devnet block 539508's own Wrap
proof's, in `to_absorption_sequence` order after the 4-entry prefix. -/
def finColVal (_p k j : Nat) : Nat :=
  (if j == 0 then finEvZ else finEvW).getD (FIN_EV_PREFIX + k) 0
/-- `evals.public_input.0` — `p(ζ)`, the same proof's. -/
def finPZetaVal (_p : Nat) : Nat := finEvZ.getD FIN_EV_PUB 0

-- ⚑ `finBlockWord` / `finBlockVal` are in `KimchiWrapMainField`, below `prevWordVal`, since
-- 2026-08-06: §21's closing sponge is defined ABOVE this point and needs to name a packed word.

/-- The cells §19's program reads. Every one is a variable ANOTHER rung's rows define, or a witness
cell this rung's own region owns. -/
structure FinWire where
  /-- Column `k` at ζ. -/
  ez : Nat → PVar
  /-- Column `k` at ζω. -/
  ew : Nat → PVar
  /-- `p(ζ)`. -/
  pZeta : PVar
  /-- ζ, LIFTED by `scalar_to_field`. -/
  zeta : PVar
  /-- α, LIFTED. -/
  alpha : PVar
  /-- β, RAW (`Challenge`, `Util.seal`). -/
  beta : PVar
  /-- γ, RAW. -/
  gamma : PVar
  /-- Packed statement word 4 — the deferred `perm`, a `Shifted_value.Type2`. -/
  permStmt : PVar
  /-- Packed statement word 26 — `should_finalize`. -/
  shouldFin : PVar
  deriving Inhabited

/-- The constants the program bakes in, and the TWO witnessed inverses it CHECKS. -/
structure FinCfg where
  log2n : Nat
  omega : Nat
  /-- `ω⁻¹`, a `.wit` whose defining constraint is the program's own `ω·ω⁻¹ = 1`. -/
  omegaInv : Nat
  shifts : List Nat
  mds9 : List Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  shift2 : Nat
  /-- The C5 denominator's inverse, likewise `.wit` and likewise checked. -/
  denomInv : Nat
  /-- `Field.equal`'s witnessed `(inv, bit)` for the ONE equality this rung emits. -/
  eqInv : Nat
  eqBit : Nat
  deriving Repr, Inhabited

/-- The slots §19's rows, environment and pins refer to by NAME. -/
structure FinSlots where
  zetaN : Nat
  zkp : Nat
  linConst : Nat
  ftEval0 : Nat
  perm : Nat
  permUsed : Nat
  permOk : Nat
  out : Nat
  deriving Repr, Inhabited

/-! ### §19d — **the finalize program**, `plonk_checks.ml` line by line. -/

def finBuild (W : FinWire) (C : FinCfg) : FM FinSlots := do
  let zero ← fnLit 0
  let one ← fnLit 1
  -- ── the wires ─────────────────────────────────────────────────────────────────────────────
  let ez ← (List.range FIN_NCOLS).foldlM (fun acc k => do
      let v ← fnInp (W.ez k); pure (acc ++ [v])) []
  let ew ← (List.range FIN_NCOLS).foldlM (fun acc k => do
      let v ← fnInp (W.ew k); pure (acc ++ [v])) []
  let zeta ← fnInp W.zeta
  let alpha ← fnInp W.alpha
  let beta ← fnInp W.beta
  let gamma ← fnInp W.gamma
  let pZeta ← fnInp W.pZeta
  let col := fun (l : List Nat) (i : Nat) => l.getD i 0
  let w0 := (List.range 15).map (fun i => col ez (FIN_IDX_W + i))
  let wN := (List.range 15).map (fun i => col ew (FIN_IDX_W + i))
  let coeff := (List.range 15).map (fun i => col ez (FIN_IDX_COEFF + i))
  let sEv := (List.range FIN_PERMUTS1).map (fun i => col ez (FIN_IDX_S + i))
  let e0z := col ez FIN_IDX_Z
  let e1z := col ew FIN_IDX_Z
  -- ── `scalars_env`: ω⁻¹, ω⁻², ω⁻³, `zk_polynomial`, `ζⁿ − 1` (`plonk_checks.ml:339-355`) ────
  -- ⚑ `ω⁻¹` is a WITNESS the program CHECKS (`ω·ω⁻¹ = 1`), never an asserted constant: a wrong
  -- witness is a refusal, and `1` is the program's own literal.
  let omega ← fnLit C.omega
  let w1 ← fnWit C.omegaInv
  let ow ← fnMul omega w1
  let _ ← fnAeq ow one
  let w2 ← fnMul w1 w1
  let w3 ← fnMul w2 w1
  let d1 ← fnSub zeta w1
  let d2 ← fnSub zeta w2
  let d3 ← fnSub zeta w3
  let zk01 ← fnMul d1 d2
  let zkp ← fnMul zk01 d3
  let zetaN ← (List.range C.log2n).foldlM (fun acc _ => fnMul acc acc) zeta
  let zeta1m1 ← fnSub zetaN one
  -- ── the α power chain, α⁰ … α²³ — ONE chain, shared by every gate and by `perm_alpha0`. ────
  let apow ← (List.range 23).foldlM (fun acc _ => do
      let t ← fnMul (acc.getLastD one) alpha; pure (acc ++ [t])) [one]
  -- ── `Scalars.Tock.constant_term` — the six always-on bodies, and nothing else. ─────────────
  let mdsS ← (List.range 3).foldlM (fun acc r => do
      let row ← (List.range 3).foldlM (fun rw c => do
          let v ← fnLit (C.mds9.getD (3 * r + c) 0); pure (rw ++ [v])) []
      pure (acc ++ [row])) []
  let endoL ← fnLit C.endo
  let cAL ← fnLit C.cA
  let cBL ← fnLit C.cB
  let cCL ← fnLit C.cC
  let negOne ← fnLit (qN - 1)
  let three ← fnLit 3
  let six ← fnLit 6
  let eleven ← fnLit 11
  let genT ← fnGenericGate (col ez (FIN_IDX_SEL + 0)) (apow.getD 1 0) coeff w0
  let posC ← fnPoseidon mdsS coeff w0 wN
  let posT0 ← fnAlphaCombine apow posC
  let posT ← fnMul (col ez (FIN_IDX_SEL + 1)) posT0
  let caC ← fnCompleteAdd one w0
  let caT0 ← fnAlphaCombine apow caC
  let caT ← fnMul (col ez (FIN_IDX_SEL + 2)) caT0
  let vbC ← fnVarBaseMul one w0 wN
  let vbT0 ← fnAlphaCombine apow vbC
  let vbT ← fnMul (col ez (FIN_IDX_SEL + 3)) vbT0
  let emC ← fnEndoMul one endoL w0 wN
  let emT0 ← fnAlphaCombine apow emC
  let emT ← fnMul (col ez (FIN_IDX_SEL + 4)) emT0
  let esC ← fnEmScalar cAL cBL cCL negOne three six eleven w0
  let esT0 ← fnAlphaCombine apow esC
  let esT ← fnMul (col ez (FIN_IDX_SEL + 5)) esT0
  let l1 ← fnAdd genT posT
  let l2 ← fnAdd l1 caT
  let l3 ← fnAdd l2 vbT
  let l4 ← fnAdd l3 emT
  let linConst ← fnAdd l4 esT
  -- ── `ft_eval0` (`plonk_checks.ml:420-460`) ────────────────────────────────────────────────
  let a0 := apow.getD 21 0
  let a1 := apow.getD 22 0
  let a2 := apow.getD 23 0
  let wn6 := w0.getD FIN_PERMUTS1 0
  let i0 ← fnAdd wn6 gamma
  let i1 ← fnMul i0 e1z
  let i2 ← fnMul i1 a0
  let init ← fnMul i2 zkp
  let num ← (List.range FIN_PERMUTS1).foldlM (fun acc i => do
      let bs ← fnMul beta (sEv.getD i 0)
      let bw ← fnAdd bs (w0.getD i 0)
      let bg ← fnAdd bw gamma
      fnMul bg acc) init
  let ft1 ← fnSub num pZeta
  let dInit0 ← fnMul a0 zkp
  let dInit ← fnMul dInit0 e0z
  let den ← (List.range 7).foldlM (fun acc i => do
      let sh ← fnLit (C.shifts.getD i 0)
      let bz ← fnMul beta zeta
      let bzs ← fnMul bz sh
      let g1 ← fnAdd gamma bzs
      let g2 ← fnAdd g1 (w0.getD i 0)
      fnMul acc g2) dInit
  let ft2 ← fnSub ft1 den
  let n1a ← fnMul zeta1m1 a1
  let n1 ← fnMul n1a d3
  let zm1 ← fnSub zeta one
  let n2a ← fnMul zeta1m1 a2
  let n2 ← fnMul n2a zm1
  let nsum ← fnAdd n1 n2
  let omz ← fnSub one e0z
  let nom ← fnMul nsum omz
  -- ⚑ the C5 denominator's inverse is the SECOND witnessed value, and it is CHECKED the same way.
  let dq ← fnMul d3 zm1
  let dInv ← fnWit C.denomInv
  let dchk ← fnMul dq dInv
  let _ ← fnAeq dchk one
  let quo ← fnMul nom dInv
  let ft3 ← fnAdd ft2 quo
  let ftEval0 ← fnSub ft3 linConst
  -- ── `Plonk_checks.checked`'s `perm` scalar (`plonk_checks.ml:476-500`) ─────────────────────
  let p0 ← fnMul e1z beta
  let p1 ← fnMul p0 a0
  let pInit ← fnMul p1 zkp
  let pf ← (List.range FIN_PERMUTS1).foldlM (fun acc i => do
      let bs ← fnMul beta (sEv.getD i 0)
      let g1 ← fnAdd gamma bs
      let g2 ← fnAdd g1 (w0.getD i 0)
      fnMul acc g2) pInit
  let perm ← fnSub zero pf
  -- ── …against the statement's own deferred value, through `Shifted_value.Type2.to_field`. ──
  let sh2 ← fnLit C.shift2
  let permStmt ← fnInp W.permStmt
  let permUsed ← fnAdd permStmt sh2
  -- `Field.equal`, the real gadget: `d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`.
  let dd ← fnSub perm permUsed
  let iv ← fnWit C.eqInv
  let bb ← fnWit C.eqBit
  let bb2 ← fnMul bb bb
  let _ ← fnAeq bb2 bb
  let pp ← fnMul dd iv
  let qq ← fnSub one bb
  let _ ← fnAeq pp qq
  let sZ ← fnMul dd bb
  let _ ← fnAeq sZ zero
  let permOk := bb
  -- ── `Boolean.Assert.any [finalized; not should_finalize]` (`wrap_main.ml:335`) ─────────────
  -- ⚑ `finalized` upstream is `Boolean.all` of FOUR legs; this rung emits the one it derives and
  -- §13 names the other three. The assert is `(1 − fin)·sf = 0`, upstream's `any` verbatim.
  let sf ← fnInp W.shouldFin
  let sf2 ← fnMul sf sf
  let _ ← fnAeq sf2 sf
  let nfin ← fnSub one permOk
  -- ⚑ `Boolean.Assert.any [finalized; not should_finalize]` is `(1 − finalized)·should_finalize = 0`,
  -- and it is emitted VERBATIM. ⚠ With a FIXTURE previous statement `finalized` is 0, so the row is
  -- satisfiable exactly when that block's `should_finalize` word is 0 — which is upstream's
  -- semantics, not a concession: a previous proof whose deferred `perm` is not the derived one and
  -- which nonetheless claims `should_finalize` IS refused, here and at source.
  let out ← fnMul nfin sf
  let _ ← fnAeq out zero
  pure { zetaN := zetaN, zkp := zkp, linConst := linConst, ftEval0 := ftEval0
       , perm := perm, permUsed := permUsed, permOk := permOk, out := out }

structure FinProg where
  prog : Array FOp
  slots : FinSlots
  deriving Repr, Inhabited

def finProgOf (W : FinWire) (C : FinCfg) : FinProg :=
  let r := (finBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-! ### §19e — the variable space, the wires, and the rows. -/

/-- ⚑ **THE §19 PROGRAM'S CAP.** `finStride` — instance 0's compiled `finBuild` program size — is
**1047** at BOTH committed shapes, measured through the emitter on 2026-08-05. It is not a shape
formula and cannot be made one: it is the `.size` of an `Array FOp` a `StateM` builder produced, and
reading it costs a `finBuild`. So the block declares a cap and `regionEscape` refuses an emission
that outgrows it. -/
def FIN_PROG_CAP : Nat := 1200
/-- ⚑ …and §20's per instance: `finSpSize` is **1732** at both committed shapes, likewise measured
and likewise builder-computed (two sponges, nineteen lift chains, then a second compiled program). -/
def FINSP_BLOCK_CAP : Nat := 2000

/-- ⚑ **W-FINALIZE'S BLOCK (§17b)** — and the only one of the three that carries headroom, because
it is the only one whose size is not shape arithmetic.

The FIRST TWO summands are EXACT and are spelled to match §19e's own layout: `finEvBase`'s two
`to_field_checked` lift chains per instance (`2 · prevs · chainStride`) and `finProgBase`'s
`2 · FIN_NCOLS + 1` evaluation columns per instance. `fin_block_prefix_is_shape_arithmetic` and
`fin_block_ceiling_is_finProgBase_plus_the_two_caps` close both, general over every shape and every
sponge — so the exact part is not taken on trust, and the block's CEILING is `finProgBase` plus
exactly `maxPrevs` copies of the two capped sizes. The last summand is the cap: one compiled §19 program
and one §20 sponge half per instance.

⚠ At both committed shapes this is **6694** against a cone measured at **5852** — 842 cells of
headroom, which is what lets §19/§20 grow without moving W-COMBINE and W-BULLET. It is not slack for
its own sake: a block whose cap is its exact size re-bases everything above it on any change. -/
def FIN_REGION_CAP (s : WrapShape) : Nat :=
  2 * s.maxPrevs * chainStride s + s.maxPrevs * (2 * FIN_NCOLS + 1)
  + s.maxPrevs * (FIN_PROG_CAP + FINSP_BLOCK_CAP)

/-- The finalize block starts above W-WRAPHACK's, at its CAP (§17b). ⚠ It read
`baseFtc s sp + nFtcVars s sp` — W-WRAPHACK's own base and W-COMBINE's — until 2026-08-05. -/
def baseFin (s : WrapShape) (sp : SpAcc) : Nat := baseWh s sp + WH_REGION_CAP s
/-- Two `to_field_checked` chains per instance — α and ζ, the two `Scalar_challenge` fields
`map_plonk_to_field` lifts. -/
def finChainVars (s : WrapShape) (sp : SpAcc) (p j : Nat) : ChainVars :=
  chainVars s (baseFin s sp) (2 * p + j)
def finEvBase (s : WrapShape) (sp : SpAcc) : Nat :=
  baseFin s sp + 2 * s.maxPrevs * chainStride s
/-- Instance `p`'s evaluation column `k` at ζ (`j = 0`) / ζω (`j = 1`); slot `2·NCOLS` is `p(ζ)`. -/
def finEvVar (s : WrapShape) (sp : SpAcc) (p k j : Nat) : PVar :=
  .external (finEvBase s sp + p * (2 * FIN_NCOLS + 1) + j * FIN_NCOLS + k)
def finPZetaVar (s : WrapShape) (sp : SpAcc) (p : Nat) : PVar :=
  .external (finEvBase s sp + p * (2 * FIN_NCOLS + 1) + 2 * FIN_NCOLS)
def finProgBase (s : WrapShape) (sp : SpAcc) : Nat :=
  finEvBase s sp + s.maxPrevs * (2 * FIN_NCOLS + 1)

/-- ⚑ **THE EXACT PART OF `FIN_REGION_CAP` IS EXACT** — everything below `finProgBase` is shape
arithmetic, general over every shape and every sponge. -/
theorem fin_block_prefix_is_shape_arithmetic (s : WrapShape) (sp : SpAcc) :
    finProgBase s sp
      = baseFin s sp + (2 * s.maxPrevs * chainStride s + s.maxPrevs * (2 * FIN_NCOLS + 1)) := by
  simp [finProgBase, finEvBase, Nat.add_assoc]

/-- ⚑⚑ **AND THEREFORE THE BLOCK'S CEILING IS `finProgBase` PLUS `maxPrevs` COPIES OF THE TWO CAPPED
SIZES** — which is what makes the emit refusal's obligation narrow enough to state in one line:
each instance's compiled §19 program must fit in `FIN_PROG_CAP` and its §20 sponge half in
`FINSP_BLOCK_CAP`. Nothing else in this block is taken on trust. General over every shape and every
sponge, so it is not a coincidence of the two committed ones. -/
theorem fin_block_ceiling_is_finProgBase_plus_the_two_caps (s : WrapShape) (sp : SpAcc) :
    baseFin s sp + FIN_REGION_CAP s
      = finProgBase s sp + s.maxPrevs * (FIN_PROG_CAP + FINSP_BLOCK_CAP) := by
  simp [FIN_REGION_CAP, finProgBase, finEvBase, Nat.add_assoc]

/-- Instance `p`'s wire. ⚑ β and γ are the RAW packed words; α and ζ are their lift chains' `lift`
cells; `perm` and `should_finalize` are packed words 4 and 26 of the same block. -/
def finWireOf (s : WrapShape) (sp : SpAcc) (p : Nat) : FinWire :=
  { ez := fun k => finEvVar s sp p k 0
  , ew := fun k => finEvVar s sp p k 1
  , pZeta := finPZetaVar s sp p
  , zeta := (finChainVars s sp p 1).lift
  , alpha := (finChainVars s sp p 0).lift
  , beta := prevW s sp (finBlockWord p 6)
  , gamma := prevW s sp (finBlockWord p 7)
  , permStmt := prevW s sp (finBlockWord p 4)
  , shouldFin := prevW s sp (finBlockWord p 26) }

/-- Instance `p`'s config. The two witnessed inverses are computed HERE and CHECKED by the program's
own rows, so a wrong one is a refusal rather than an accept. -/
def finCfgOf (s : WrapShape) (p : Nat) : FinCfg :=
  let zeta := liftValQ s (finBlockVal p 9)
  let wi := qInv FIN_OMEGA
  let w3 := qMul (qMul wi wi) wi
  let dq := qMul (qSub zeta w3) (qSub zeta 1)
  { log2n := FIN_LOG2N, omega := FIN_OMEGA, omegaInv := wi
  , shifts := FIN_SHIFTS, mds9 := mdsQ.flatten, endo := FIN_ENDO
  , cA := FIN_CA, cB := FIN_CB, cC := FIN_CC, shift2 := FIN_SHIFT2
  , denomInv := qInv dq
  -- ⚑ the HONEST witness: `perm` and the statement's unshifted word agree, so `bit = 1, inv = 0`.
  -- §12/§16's red controls run the same program at a bent statement word, where the honest witness
  -- is `bit = 0` and `d·inv = 1 − bit` has no solution — an `Err`, not an accept.
  , eqInv := 0, eqBit := 1 }

/-- Everything instance `p` reads that is NOT an evaluation column: `p(ζ)`, the two lift cells, and
the four packed statement words. Shared by the probe environment and the real one, so the two differ
in exactly one cell. -/
def finTailEnv (s : WrapShape) (sp : SpAcc) (p : Nat) : VarEnv :=
  [ (finPZetaVar s sp p, (finPZetaVal p : Int))
  , ((finChainVars s sp p 0).lift, (liftValQ s (finBlockVal p 8) : Int))
  , ((finChainVars s sp p 1).lift, (liftValQ s (finBlockVal p 9) : Int))
  , (prevW s sp (finBlockWord p 6), (finBlockVal p 6 : Int))
  , (prevW s sp (finBlockWord p 7), (finBlockVal p 7 : Int))
  , (prevW s sp (finBlockWord p 4), (finBlockVal p 4 : Int))
  , (prevW s sp (finBlockWord p 26), (finBlockVal p 26 : Int)) ]

/-- The environment with the RAW `Req.Evals` fixtures, i.e. before `finZW0` solves one of them. It is
what the probe below evaluates, and the two differ in exactly one cell. -/
def finRawEnv (s : WrapShape) (sp : SpAcc) (p : Nat) : VarEnv :=
  (List.range FIN_NCOLS).flatMap (fun k =>
    [ (finEvVar s sp p k 0, (finColVal p k 0 : Int))
    , (finEvVar s sp p k 1, (finColVal p k 1 : Int)) ])
  ++ finTailEnv s sp p

/-- ✅ ⚑⚑⚑ **THE PREVIOUS PROOF'S `z(ζω)` — AND SINCE 2026-08-07 THERE IS NO SOLVE AT ALL.
`finZW0` IS DELETED, WITH AN EMIT-AND-DIFF RATHER THAN AN ASSERTION.**

⚠ **WHAT THIS DOCBLOCK USED TO ARGUE, AND WHY IT IS KEPT VISIBLE.** It said: *"THE FREE CELL TO MOVE
IS NOT THE STATEMENT WORD. That is MSM scalar material … `z` at ζω is a `Req.Evals` witness this
sub-circuit alone reads, and `derive_plonk`'s `perm` is `−(e1z · β · α²¹ · zkp · Π …)` — LINEAR in
it. So the honest value is `e1z · permUsed / perm₀`: one probe evaluation, one inversion, statement
word untouched."* Its premise expired on 2026-08-06 when §19c started reading Mina devnet block
539508's own `es` columns — bending a fixture is free, bending a real block's evaluation presents
§20's sponge a value that block does not have.

⚑ **THAT PRICE WAS A DESCRIPTION OF THE DEFECT, NOT OF A COST.** `ftcDiv2 0`/`ftcOdd 0` are §6b's
own **Fp** ft-comm scalar — the WRAP statement's word 4. The step statement's word 31 is an **Fq**
`Shifted_value.Type2` deferred value about the WRAP proof, which the step circuit never derived and
never could. It was ALIASED onto those cells, and un-aliasing it (`KimchiStepMainCore` §1f) was
eleven new cells, one emit and one re-prove — no MSM move that mattered, no fixpoint.

⚑ **THE LABEL WAS RETIRED ON `9c03979cb`; THE SOLVE WAS NOT, AND THAT GAP IS THE WHOLE LESSON.**
`permUsed = perm₀` made the ratio 1, so the function returned `finColVal p FIN_IDX_Z 1` on both
blocks — **inert**. An inert solve is worse than none: it is a compensator with no input yet, and a
future word 31 that stopped being the derived `perm` would be silently absorbed by the ratio instead
of refusing at `w10_finalize`'s `Field.equal`. The three theorem conjuncts that named it would have
gone on being green about `finZW0 = finColVal` while the emission drifted.

⚑ **THE EVIDENCE IS AN EMIT-AND-DIFF, NOT AN ASSERTION**, which is what the previous pass said it
owed and did not pay. `w11_finsponge` and `w12_close` were emitted at the smoke shape with the solve
present and with it deleted; all four artifacts (each rung wired + unwired) are **byte-identical**,
`cmp` silent, same length, same digest:

    269f4b37b838cc76…  wrapmain_smoke_w11_finsponge.json          6 545 266 B
    d105ed6fd2253509…  wrapmain_smoke_w11_finsponge_unwired.json  6 545 274 B
    6bc681cc241db839…  wrapmain_smoke_w12_close.json              4 973 000 B
    e24824a4cf153c3f…  wrapmain_smoke_w12_close_unwired.json      4 973 008 B

⚠ ⚑ **AND THE FIRST RUN OF THAT DIFF SAID THE OPPOSITE, WHICH IS THE PART TO INHERIT.** It reported
21 777 differing witness cells, 50 differing gate rows and a MOVED public input — because the
"before" emission had been run against **stale `.olean`s** while the "after" one followed a
`lake build`. Nothing in the delta was this change; it was a sibling's landed work in the dependency
closure showing up as if it were mine. **An emit-and-diff is only evidence if BOTH sides were
built**, and in a shared tree that has to be arranged rather than assumed. The value-layer probe
agrees with the corrected diff: the solve returned the block's own `z(ζω)` at BOTH instances — the
padding block by its `should_finalize` guard, the live block because `perm = permUsed`.

`KimchiWrapFinalizeSpongeGate.the_live_block_publishes_the_derived_perm_so_no_solve_is_needed`
carries the arithmetic half (`perm = permUsed`, and the padding block's word is still NOT its
derivation, so `Field.equal`'s `(d⁻¹, 0)` branch keeps an instance).

⚠ ⚑ **AND THE `should_finalize` GUARD WENT WITH IT, WHICH IS NOT A LOSS.** The guard existed so the
solve applied only to the block that claims `should_finalize` — solving in EVERY block would have
forced `perm = permUsed` for any statement word whatever, `Field.equal` would take `bit = 1`
unconditionally, and the one constraint this rung exists to emit could not go red. With no solve at
all, both blocks read their own `z(ζω)`, the live one agrees because the statement carries the
derivation and the padding one does not — so both branches stay live and the assert stays
falsifiable for the ORIGINAL reason: give block 0 a `should_finalize` of 1 and this rung is
unsatisfiable. -/
structure FinData where
  fp : FinProg
  vals : Array Nat
  deriving Repr, Inhabited

/-- The program run ONCE on the RAW evaluations, so `finZW0` can read its own `perm`/`permUsed`
slots. It is a probe: nothing emits its rows. -/
def finProbeData (s : WrapShape) (sp : SpAcc) (p : Nat) : FinData :=
  let fp := finProgOf (finWireOf s sp p) (finCfgOf s p)
  { fp := fp, vals := fnEval (envLookupAt (envIndex (finRawEnv s sp p))) fp.prog }

/-! ⚑⚑ **`finZW0` IS DELETED (2026-08-07), AND ITS INERTNESS IS WHY.**

It stood here and read: *instance `p`'s `z(ζω)` — the raw `Req.Evals` fixture on a block that does
NOT claim `should_finalize`, and `e1z · permUsed / perm₀` on the one that does.* It was a
CONTAINMENT: it scaled the live block's `z(ζω)` so §19's `Field.equal` leg would hold while packed
word 31 carried something other than the derived `perm`. Word 31 became
`Shifted_value.Type2.of_field perm` (`the_live_block_publishes_the_derived_perm_so_no_solve_is_needed`),
so the ratio went to 1 and the solve became the IDENTITY at both instances — the live one because
`permUsed = perm`, the padding one because the `should_finalize` guard already returned the raw
column. Its LABEL was retired on `9c03979cb`; the solve was not.

⚠ **AN INERT SOLVE IS WORSE THAN NONE.** Left in place it is a compensator waiting for an input: a
future wrong word 31 gets silently ABSORBED by the ratio instead of REFUSING at `w10_finalize`,
which is precisely the check this ladder exists to run. Deleting it means the three consumers below
read `finColVal p k 1` — the block's own evaluation — unconditionally, so §19's `Field.equal` is
answered by the derivation or not at all.

⚑ `finProbeData` STAYS: it is what
`the_live_block_publishes_the_derived_perm_so_no_solve_is_needed` reads `perm`/`permUsed` out of,
and that theorem is the anti-vacuity leg that keeps the padding block's difference NONZERO. The
probe was never the containment; the scaling was. -/

/-- Instance `p`'s `.inp` lookup: the 87 witnessed evaluation cells, the two lifts, and the four
statement words. Every entry is a cell some row of the assembly defines. -/
def finInputEnv (s : WrapShape) (sp : SpAcc) (p : Nat) : VarEnv :=
  (List.range FIN_NCOLS).flatMap (fun k =>
    [ (finEvVar s sp p k 0, (finColVal p k 0 : Int))
    , (finEvVar s sp p k 1, (finColVal p k 1 : Int)) ])
  ++ finTailEnv s sp p

/-- ⚑ **THE `Field.equal` WITNESS IS COMPUTED, NOT ASSUMED — AND ASSUMING IT IS WHY THE FIRST
EMISSION WAS REJECTED.** `finCfgOf` used to hardcode `(inv, bit) = (0, 1)`, the witness for
`perm = permStmt`. The previous statement's deferred `perm` is a NAMED FIXTURE (`prevWordVal` stands
in for `exists ~request:Req.Proof_state`), so it is NOT the derived value, the difference is nonzero,
and `d·bit = 0` had no solution: the prover answered `Prover("rest of division by vanishing
polynomial")` while every σ-class pin and every row-count theorem stayed green. A row schedule and a
witness environment are two places and only the prover reads both.

So the program is run ONCE with a placeholder pair, its own `perm`/`permUsed` slots are read, and the
gadget's honest witness is derived from the actual difference — `(0, 1)` when they agree and
`(d⁻¹, 0)` when they do not, which is `Field.equal`'s own answer either way. -/
def runFin (s : WrapShape) (sp : SpAcc) (p : Nat) : FinData :=
  let lk := envLookupAt (envIndex (finInputEnv s sp p))
  let probe := finProgOf (finWireOf s sp p) (finCfgOf s p)
  let pv := fnEval lk probe.prog
  let d := qSub (pv.getD probe.slots.perm 0) (pv.getD probe.slots.permUsed 0)
  let cfg := { finCfgOf s p with
               eqInv := if d == 0 then 0 else qInv d
               eqBit := if d == 0 then 1 else 0 }
  let fp := finProgOf (finWireOf s sp p) cfg
  { fp := fp, vals := fnEval lk fp.prog }

/-- ⚑ **EVERY INSTANCE'S PROGRAM, BUILT ONCE.** This is the module's own perf lesson applied a third
time — the one that took `rungRows tWrap .key` from 1 014 740 ms to 62 ms, and the one the `xhatBitsOf`
docblock names. `finRows` and `finEnv` each USED to call `runFin` **and** a separate `finProgSize`
(a second full `finProgOf`) per instance, and `emitRung` calls those four times over — ~20 builds and
evaluations of a ~900-op program per emission. Bind the list once at the top of each and index it. -/
def finAll (t : WrapData) : List FinData :=
  (List.range t.sh.maxPrevs).map (fun p => runFin t.sh t.sp p)

/-- The per-instance program stride: instance 0's size. The programs are the same builder at
different wires, so they agree; a shape whose instances disagreed would overlap and `placeChecked`
would refuse rather than emit. -/
def finStride (fa : List FinData) : Nat := (fa.getD 0 default).fp.prog.size
def finProgAt (s : WrapShape) (sp : SpAcc) (fa : List FinData) (p : Nat) : Nat :=
  finProgBase s sp + p * finStride fa

/-- ⚑ **THE HOIST IS THE THING IT HOISTS**, general over every `WrapData`, by `rfl` — the same
statement shape `rungRows_is_a_ladder` uses, and the reason the change is auditable rather than
trusted: the bound list IS the per-instance recomputation, so no emitted cell can have moved. -/
theorem finAll_is_the_recomputation (t : WrapData) :
    finAll t = (List.range t.sh.maxPrevs).map (fun p => runFin t.sh t.sp p) := rfl

/-- …and at both committed shapes (`maxPrevs = 2`) the stride really is instance 0's program size,
which is exactly the value the separate second `finProgOf` used to compute. -/
theorem finStride_is_instance_zeros_program_size (t : WrapData) (h : t.sh.maxPrevs = 2) :
    finStride (finAll t) = (runFin t.sh t.sp 0).fp.prog.size := by
  simp [finStride, finAll, h]

/-- **W-FINALIZE's ROWS.** Per instance: the two `to_field_checked` lifts of α and ζ (through the
SHARED endo cell §5 pins, `split = false` because both sources are already `Challenge.t`), the
compiled program, and the σ-only probes. -/
def finRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let cb := baseCh s sp
  let fa := finAll t
  (List.range s.maxPrevs).flatMap (fun p =>
    let d := fa.getD p default
    let base := finProgAt s sp fa p
    let V := fnVarAt base d.fp.prog
    tfcRowsQ s cb (finChainVars s sp p 0) (prevW s sp (finBlockWord p 8)) false
      (finBlockVal p 8) wired
    ++ tfcRowsQ s cb (finChainVars s sp p 1) (prevW s sp (finBlockWord p 9)) false
      (finBlockVal p 9) wired
    ++ fnRows base d.fp.prog
    -- ⚑ **ONE probe, not three, and the reason is a measured conformance fact.** Mina's
    -- `wrap-transaction` blob has **NO two consecutive `Zero` rows anywhere** — every `Zero` there is
    -- a gadget tail. Three probes in a row would be a divergence this rung introduced, so the rung
    -- emits one, preceded by the program's `Generic` run. (The two `tfcRowsQ` already closes each
    -- lift chain with are §5's, unchanged here.)
    ++ [ probeRow wired (V d.fp.slots.ftEval0) (V d.fp.slots.linConst) ])

/-- W-FINALIZE's variable environment. -/
def finEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let fa := finAll t
  (List.range s.maxPrevs).flatMap (fun p =>
    let d := fa.getD p default
    chainEnv s (finChainVars s sp p 0) (finBlockVal p 8) 0
    ++ chainEnv s (finChainVars s sp p 1) (finBlockVal p 9) 0
    ++ finInputEnv s sp p
    ++ fnEnvOf (finProgAt s sp fa p) d.fp.prog d.vals)

/-! ## §23 — ⚑ **W-COMBINE**: `Split_commitments.combine`, and the ξ-aggregate's 46 endo ladders.

`wrap_verifier.ml:320-379` (the gadget) called at `:687-713` (the 47 commitments). Read end to end,
`Pcs_batch.combine_split_commitments` (`pickles_types/pcs_batch.ml:69-83`) is:

    let flat = List.concat_map (Vector.to_list without_degree_bound) ~f:Array.to_list @ …
    match List.rev flat with
    | init :: comms -> List.fold_left comms ~init:(i init) ~f:(fun acc p -> scale_and_add ~acc ~xi p)

⚑ **`List.rev flat` — THE FOLD RUNS BACKWARDS.** `~init` is the LAST commitment and the fold walks
down to the first, so the two `sg_old` entries are the fold's LAST two steps and not its first two.
Getting that round the wrong way gives the same gate COUNT and a different circuit.

## THE 47, IN `wrap_verifier.ml:687-706`'s OWN ORDER

    0 .. prevs-1     sg_old            the previous proofs' `challenge_polynomial_commitment`s
    prevs            x_hat             ⚑ §15's MSM OUTPUT — the cells `:617` absorbs
    prevs+1          ft_comm           ⚑ §17's OUTPUT
    prevs+2          z_comm            transcript
    prevs+3 .. +8    the six index singletons   ⚑ W-KEY's `choose_key` cells (coords 44..55)
    … + wComms       w_comm            transcript
    … + KEY_COLS     coefficients_comm ⚑ W-KEY (coords 14..43)
    … + 6            sigma_comm_init   ⚑ W-KEY (coords 0..11), i.e. `sigma_comm` minus its last

`Nat.N45.n + Max_proofs_verified.n` = 45 + 2 = **47** at the wrap shape, and `47 − 1 = 46` fold
steps is exactly what closes Mina's own `EndoMul 2528 = 32 × (46 + 33)` against W-BULLET's 33.

## ⚑ WHAT THIS RUNG WIRES, AND IT IS THE WHOLE POINT OF THE SUB-CIRCUIT

Every one of the 47 is a cell some OTHER rung already defines: a transcript absorbed word, W-KEY's
sealed coordinate, W-XHAT's MSM output or W-FTCOMM's `ft_comm`. Nothing here is witnessed except
`xi`. That is what takes `sg_old`, `w_comm`, `z_comm`, `x_hat` and `t_comm` off §2c — not because a
gadget re-reads them, but because bending any one of them moves 46 ladders' worth of gate
polynomials and the fold's output.

⚠ **`xi` IS FREE, HERE AND UPSTREAM.** It is `Deferred_values.xi`, wrap statement slot 9, and
§10's census already says W-FINALIZE is what binds it. All 46 ladders' counters land on ONE cell —
`Field.Assert.equal !n_acc scalar` (`scalar_challenge.ml:305`) as a σ class — which is upstream's
shape and is what `comb_all_ladders_share_one_xi` pins.

## ⚑ THE `keep` MUX, WHICH THE STEP SIDE'S FOLD DOES NOT HAVE

`scale_and_add` is

    point = if_ keep ~then_:(if_ acc.non_zero ~then_:(Point.add p (endo acc.point xi))
                                              ~else_:(Point.underlying p))
                     ~else_:acc.point
    non_zero = keep &&& Point.finite p ||| acc.non_zero

and three of those four booleans are CONSTANT here, which is upstream's own reduction and not a
simplification this file made:

  * `p` is `` `Finite `` for all 47 (`:709` maps every one through `~f:(fun (keep,x) -> (keep, `Finite x))`),
    so `Point.finite p = Boolean.true_` and `Point.add p q = Ops.add_fast p q`;
  * `keep` is `Boolean.true_` for 45 of them (`:706`) and the `actual_proofs_verified_mask` VARIABLE
    for the two `sg_old` (`:511-514`) — §9's `vv`, reversed;
  * so `non_zero` starts constant `true` at `~init` and stays constant, `if_ acc.non_zero` folds to
    its `then_` branch at ZERO rows, and `Boolean.Assert.is_true non_zero` (`:377`) is a check on a
    CONSTANT and emits no row. ⚠ Recorded rather than emitted: writing a row for it would be this
    file inventing a constraint `wrap_main` does not have.

⚑ So the mux is emitted exactly TWICE, at the fold's last two steps. ⚠ **Since 2026-08-06 both
carry `keep = 1`** — `mkWrapWith` witnesses `KEY_CHAIN_BRANCH` with widths `[0,1,2,…]`, so
`first_zero = 2` and `ones_vector` is all ones, which is what `proofs_verified = N2` MEANS for a step
rule with two accumulators. The `~else_` arm is therefore not exercised by the committed emission;
`comb_mux_keep_is_the_branch_selections` says both halves of that plainly and exhibits `[0, 1]` at
`KEY_REAL_BRANCH`'s width, so `keep` is still measured to be a function of the selection.

## ⚑ THE DEFECT CLASSES, INSIDE THIS SUB-CIRCUIT

  1. **Free ladder seeds.** `Scalar_challenge.endo` opens `let p = t + (scale xt Endo.base, yt)` and
     `acc = ref (p + p)`, `n_acc = ref Field.zero` (`scalar_challenge.ml:230-233`). ⚑ **The seed is
     `2(t + φ(t))`, NOT `2t`** — a different gadget from `scale_fast_unpack`'s, and the step side
     shipped the wrong one of the two for a while. All three cells are emitted and pinned: `φ(t)`'s
     abscissa by a `Generic` half at `ENDO_BASE_Q`, `p` and `acc₀` by `CompleteAdd` rows that DEFINE
     them, `n₀` by a `Generic` half at 0. `comb_every_ladder_seed_is_pinned` reads them off the row
     list.
  2. **Prover-chosen decomposition.** The 128 bits are `EndoMul`'s own advice cells and are tied to
     `xi` only through the counter chain `nₑ₊₁ = 16nₑ + 8b₁+4b₂+2b₃+b₄` closing on `xi`. The gate
     polynomial constrains each `bᵢ` to `{0,1}` (`endosclmul.rs`), so at `n₀ = 0` the chain is the
     base-2 expansion of a 128-bit value and is unique — which is why the `n₀` pin above is
     load-bearing and not decoration.
  3. **Absorbed-but-not-consumed.** ⚑ This rung is what takes `sg_old`, `w_comm`, `z_comm` and
     `x_hat` OFF §2c, and `t_comm` with them (its consumer `ft_comm` is now consumed). ⚠ What does
     NOT change: `equal_g` refuses no on-curve substitution, because `G`/`z₁`/`z₂` are free — that
     is §24's own note and it is measured on the step side, not asserted here.
  4. **Constants pinned against their own definitions.** This sub-circuit owns exactly one constant,
     `ENDO_BASE_Q`, and `KimchiWrapMainField.endo_base_q_is_the_curve_endomorphism` pins it three
     ways: as a nontrivial cube root of unity, as the group map's own
     `sqrt_neg_three_u_squared_minus_u_over_2`, and as NOT `ENDO_Q`.

## ⚑ WHERE THE EMITTED SHAPE IS THIS FILE'S AND NOT MINA'S

The σ-only probe rows are ours; `wrap_main` has none. They are placed at the TOP of each fold step
rather than after the ladder tail, so no `Zero` row ever follows another — Mina's wrap blob has no
two consecutive `Zero`s anywhere, and a probe after a ladder's closing `Zero` would have
manufactured 46 of them. -/

/-- ⚑ `Nat.N45.n + Max_proofs_verified.n` — the commitments `Split_commitments.combine` folds.
`KEY_COLS` and `KEY_SIGMA` are `Plonk_types.Columns.n` / `Permuts.n` and are NOT shape knobs: the
coefficient and sigma commitments come out of W-KEY's 56 REAL coordinates at every shape.

⚑⚑ **AND THE `sg_old` PREFIX IS `Max_proofs_verified`, NOT `actual_proofs_verified`.**
`wrap_verifier.ml:687-702` builds the list as `Vector.append sg_old (…) (snd
(Max_proofs_verified.add num_commitments_without_degree_bound))` with `num_commitments_without
_degree_bound = Nat.N45.n`, and `sg_old` is typed `(_, Max_proofs_verified.n) Vector.t` at `:507`.
`wrap.rs:2458-2477` says it the same way: `sg_old.chain(rest)` over
`NUM_COMMITMENTS_WITHOUT_DEGREE_BOUND = 45`. **The `keep` mask selects at the MUX, not at the
LIST** — a masked entry still gets its `Scalar_challenge.endo` ladder, which is exactly why the
census is `32 × (46 + 33) = 2528` and not `32 × (45 + 33) = 2496`. This def read `s.prevs` while
that field held `actual_proofs_verified`, and `comb_and_bullet_close_minas_endomul_census` was RED
against Mina's own compiled `wrap_main` for it. -/
def combTerms (s : WrapShape) : Nat :=
  s.maxPrevs + 3 + KEY_SINGLES + s.wComms + KEY_COLS + (KEY_SIGMA - 1)
/-- Fold steps — one fewer than the commitments, because `~init` consumes the last. -/
def combSteps (s : WrapShape) : Nat := combTerms s - 1

/-- ⚑ **`xi`**, `Deferred_values.xi`'s `Scalar_challenge.inner` — a RAW 128-bit challenge at Mina
slot **9**. It is `< 2^ENDO_BITS` because the ladder's counter reconstructs exactly that many bits;
a wider value would make `Field.Assert.equal !n_acc scalar` unsatisfiable.

⚑ **MEASURED SINCE 2026-08-05**, and the `% 2 ^ ENDO_BITS` that used to reduce the filler is GONE
rather than kept as a belt: the measurement is a real `Scalar_challenge.inner` and is 128 bits by
construction, so a modulus here would have hidden a wrong object instead of catching one.
`MinaWrapDeferredWords.the_six_fit_the_cells_that_will_carry_them` is where the bound is checked,
and it is checked on the value rather than imposed on it. -/
def combXiVal : Nat := DEF_XI

/-- Commitment `k`'s VALUE, in `wrap_verifier.ml:687-706`'s flat order.

⚑ **EVERY TRANSCRIPT SLOT READS `t.sp`, THE SAME PLACE `combPtVar`'s `absW` READS THE VARIABLE.**
Four of the seven cases below are the transcript's own absorbed words, and until 2026-08-05 they
answered with `itemVal` regardless of the tape — see `absVal`. `x_hat` is one of them: `schedule`
absorbs `s.xhatXY`, so `absVal t.sp T_XHAT` IS `s.xhatXY` for a `schedule`-driven `WrapData`, and is
the step proof's own public-input commitment for a chained one. The three that do not read the
transcript are named: `ftcOut` is §17's output and `kc` is W-KEY's sealed coordinates. -/
def combPtVal (t : WrapData) (k : Nat) : Nat × Nat :=
  let s := t.sh
  let sp := t.sp
  let kc : Nat → Nat × Nat := fun c => (keyConst t.br.idx c, keyConst t.br.idx (c + 1))
  if k < s.maxPrevs then whSlotSgAt t k
  else if k == s.maxPrevs then absPtVal sp T_XHAT 0
  else if k == s.maxPrevs + 1 then ftcOut t
  else if k == s.maxPrevs + 2 then absPtVal sp T_ZCOMM 0
  else if k < s.maxPrevs + 3 + KEY_SINGLES then kc (44 + 2 * (k - s.maxPrevs - 3))
  else if k < s.maxPrevs + 3 + KEY_SINGLES + s.wComms then
    absPtVal sp T_WCOMM (k - s.maxPrevs - 3 - KEY_SINGLES)
  else if k < s.maxPrevs + 3 + KEY_SINGLES + s.wComms + KEY_COLS then
    kc (14 + 2 * (k - s.maxPrevs - 3 - KEY_SINGLES - s.wComms))
  else kc (2 * (k - s.maxPrevs - 3 - KEY_SINGLES - s.wComms - KEY_COLS))

/-- …and its VARIABLE. ⚑ Every one is another rung's cell; this sub-circuit allocates none of them. -/
def combPtVar (t : WrapData) (k : Nat) : PVar × PVar :=
  let s := t.sh
  let sp := t.sp
  let kv := keyVars s (baseKey s sp)
  let kc : Nat → PVar × PVar := fun c => (kv.acc c (s.branches - 1), kv.acc (c + 1) (s.branches - 1))
  let absW : Nat → Nat → PVar := fun tag i =>
    ((sp.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).wordV
  if k < s.maxPrevs then (sgOldVar t k 0, sgOldVar t k 1)
  else if k == s.maxPrevs then (absW T_XHAT 0, absW T_XHAT 1)
  else if k == s.maxPrevs + 1 then ftcOutV s sp
  else if k == s.maxPrevs + 2 then (absW T_ZCOMM 0, absW T_ZCOMM 1)
  else if k < s.maxPrevs + 3 + KEY_SINGLES then kc (44 + 2 * (k - s.maxPrevs - 3))
  else if k < s.maxPrevs + 3 + KEY_SINGLES + s.wComms then
    let j := k - s.maxPrevs - 3 - KEY_SINGLES
    (absW T_WCOMM (2 * j), absW T_WCOMM (2 * j + 1))
  else if k < s.maxPrevs + 3 + KEY_SINGLES + s.wComms + KEY_COLS then
    kc (14 + 2 * (k - s.maxPrevs - 3 - KEY_SINGLES - s.wComms))
  else kc (2 * (k - s.maxPrevs - 3 - KEY_SINGLES - s.wComms - KEY_COLS))

/-- ⚑ `actual_proofs_verified_mask ! k` (`wrap_verifier.ml:511-514`). §9 emits `ones_vector` and
`Vector.rev` makes element `k` the running value `vv (MASK_N − 1 − k)` — the SAME cells §11c's
packing reads, so a `keep` and the `branch_data` public word cannot disagree. -/
def combKeepVal (t : WrapData) (k : Nat) : Nat := onesVal t.br.fz (MASK_N - 1 - k)
def combKeepVar (t : WrapData) (k : Nat) : PVar :=
  (branchVars t.sh (baseBr t.sh t.sp)).vv (MASK_N - 1 - k)

/-- ⚑ **THE WHOLE FOLD, EVALUATED ONCE.** `accs` is the accumulator ENTERING step `a` (so `accs !
combSteps` is `combine`'s output), `eds` the per-step `Scalar_challenge.endo` traces, `sums` the
`Ops.add_fast` outputs. Bound as one structure for §15's reason: a per-row recomputation would
replay a 32-block ladder for every one of its rows. -/
structure CombData where
  accs : List (Nat × Nat)
  eds : List EndoDataQ
  sums : List (Nat × Nat)
  deriving Inhabited

def combData (t : WrapData) : CombData :=
  let n := combTerms t.sh
  let st := (List.range (n - 1)).foldl
    (fun (st : CombData) a =>
      let cur := st.accs.getLastD (0, 0)
      let idx := n - 2 - a
      let ed := runEndoQ cur combXiVal
      let sum := addAQ (combPtVal t idx) (ed.accs.getLastD (0, 0))
      let out := if idx < t.sh.maxPrevs && combKeepVal t idx == 0 then cur else sum
      { accs := st.accs ++ [out], eds := st.eds ++ [ed], sums := st.sums ++ [sum] })
    { accs := [combPtVal t (n - 1)], eds := [], sums := [] }
  st

/-- The commitment fold step `a` consumes — the fold runs DOWN the flat list. -/
def combIdx (s : WrapShape) (a : Nat) : Nat := combTerms s - 2 - a
/-- …and whether that step carries a live `keep` mux. -/
def combIsMux (s : WrapShape) (a : Nat) : Bool := combIdx s a < s.maxPrevs

/-! ### §23a — the variable layout.

⚑ **THE REGION SHARED ITS BASE WITH W-FINALIZE'S AND W-WRAPHACK'S UNTIL 2026-08-05**, and was safe
only because `.combine`, `.finalize` and `.wraphack` are sibling branches off `.prev` and no rung's
`rungsUpto` contains two of them — an accident of the assembly order, which a rung that merged them
would have spent. §17b stacks the three blocks on shape-determined caps, so this is the TOP block and
its base is W-FINALIZE's cap. -/

/-- Per-step slots: `p` (2), `endo·xt` (1), the 33 accumulator points (66), the 32 interior
counters, the `Ops.add_fast` output (2), and the mux's `(d, m, r)` for x then y (6). -/
def COMB_STRIDE : Nat := 3 + 2 * (ENDO_BLOCKS + 1) + ENDO_BLOCKS + 2 + 6

def baseComb (s : WrapShape) (sp : SpAcc) : Nat := baseFin s sp + FIN_REGION_CAP s
/-- ⚑ ξ's own cell — ONE for all 46 ladders. -/
def combXiV (s : WrapShape) (sp : SpAcc) : PVar := .external (baseComb s sp)
def combSlot (s : WrapShape) (sp : SpAcc) (a o : Nat) : PVar :=
  .external (baseComb s sp + 1 + COMB_STRIDE * a + o)
def combPV (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar × PVar :=
  (combSlot s sp a 0, combSlot s sp a 1)
def combEndoX (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar := combSlot s sp a 2
def combAccPt (s : WrapShape) (sp : SpAcc) (a e : Nat) : PVar × PVar :=
  (combSlot s sp a (3 + 2 * e), combSlot s sp a (4 + 2 * e))
/-- ⚑ The counter at block boundary `e`. At `e = ENDO_BLOCKS` it IS `xi`'s cell —
`Field.Assert.equal !n_acc scalar` as a σ class rather than as a row. -/
def combN (s : WrapShape) (sp : SpAcc) (a e : Nat) : PVar :=
  if e == ENDO_BLOCKS then combXiV s sp
  else combSlot s sp a (3 + 2 * (ENDO_BLOCKS + 1) + e)
def combSumV (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar × PVar :=
  (combSlot s sp a (3 + 3 * ENDO_BLOCKS + 2), combSlot s sp a (3 + 3 * ENDO_BLOCKS + 3))
/-- The mux's `d`/`m`/`r` for coordinate `c` (0 = x, 1 = y). -/
def combMux (s : WrapShape) (sp : SpAcc) (a c o : Nat) : PVar :=
  combSlot s sp a (3 + 3 * ENDO_BLOCKS + 4 + 3 * c + o)
def nCombVars (s : WrapShape) : Nat := 1 + COMB_STRIDE * combSteps s

/-- Step `a`'s OUTPUT variable: the mux result where there is a mux, the `add_fast` output
otherwise. -/
def combOutVar (t : WrapData) (a : Nat) : PVar × PVar :=
  let s := t.sh
  let sp := t.sp
  if combIsMux s a then (combMux s sp a 0 2, combMux s sp a 1 2) else combSumV s sp a
/-- …and the accumulator step `a` READS, which is the ladder's base. -/
def combAccVar (t : WrapData) (a : Nat) : PVar × PVar :=
  if a == 0 then combPtVar t (combTerms t.sh - 1) else combOutVar t (a - 1)

/-- One `Scalar_challenge.endo` block row. Cols 0/1 are the ladder's BASE (`xt`, `yt` — sealed once
per ladder), 4/5 the accumulator entering the block, 6 the counter; the four bits, the two stored
slopes, the intermediate point and the distinct-point inverse are advice
(`endosclmul.rs:48-56`). -/
def combBlockRows (s : WrapShape) (sp : SpAcc) (bv : PVar × PVar) (a : Nat)
    (bl : List EndoBlockQ) : List WRow :=
  (List.range ENDO_BLOCKS).map (fun e =>
    let b := bl.getD e default
    ({ kind := .endoMul
     , perm := [ some bv.1, some bv.2, none, none
               , some (combAccPt s sp a e).1, some (combAccPt s sp a e).2, some (combN s sp a e) ]
     , advice := [ (2, (b.inv : Int)), (3, 0), (7, (b.xr : Int)), (8, (b.yr : Int))
                 , (9, (b.s1 : Int)), (10, (b.s3 : Int)), (11, (b.b1 : Int)), (12, (b.b2 : Int))
                 , (13, (b.b3 : Int)), (14, (b.b4 : Int)) ] } : WRow))
  ++ [ { kind := .zero
       , perm := [ none, none, none, none
                 , some (combAccPt s sp a ENDO_BLOCKS).1, some (combAccPt s sp a ENDO_BLOCKS).2
                 , some (combN s sp a ENDO_BLOCKS) ] } ]

/-- **W-COMBINE's ROWS.** -/
def combRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let v := combData t
  let ns := combSteps s
  -- (1) every ladder's `n₀ = 0` and its `φ(t)` abscissa pin, batched two halves to a row.
  let seedPins : List WRow :=
    packHalves ((List.range ns).flatMap (fun a =>
      [ ([some (combN s sp a 0), none, none], cConst 0)
      , ([some (combAccVar t a).1, none, some (combEndoX s sp a)],
         [(ENDO_BASE_Q : Int), 0, -1, 0, 0]) ]))
  -- (2) the fold, `wrap_verifier.ml:344-372`, step by step and BACKWARDS down the flat list.
  let stepRows : List WRow :=
    (List.range ns).flatMap (fun a =>
      let bv := combAccVar t a
      let bval := v.accs.getD a (0, 0)
      let ed := v.eds.getD a default
      let q := (qMul ENDO_BASE_Q bval.1, bval.2)
      let p := endoPQ bval
      let out := ed.accs.getLastD (0, 0)
      let pt := combPtVal t (combIdx s a)
      -- the probe leads the step, so no `Zero` row ever follows the ladder's closing `Zero`.
      [ probeRow wired bv.1 bv.2
      , caRowQ bv (combEndoX s sp a, bv.2) (combPV s sp a) (caWitnessQ bval.1 bval.2 q.1 q.2)
      , caRowQ (combPV s sp a) (combPV s sp a) (combAccPt s sp a 0)
          (caWitnessQ p.1 p.2 p.1 p.2) ]
      ++ combBlockRows s sp bv a ed.blks
      ++ [ caRowQ (combPtVar t (combIdx s a)) (combAccPt s sp a ENDO_BLOCKS) (combSumV s sp a)
             (caWitnessQ pt.1 pt.2 out.1 out.2) ]
      ++ (if combIsMux s a then
            packHalves ((List.range 2).flatMap (fun c =>
              let sm := if c == 0 then (combSumV s sp a).1 else (combSumV s sp a).2
              let cu := if c == 0 then bv.1 else bv.2
              [ ([some sm, some cu, some (combMux s sp a c 0)], [1, -1, -1, 0, 0])
              , ([some (combKeepVar t (combIdx s a)), some (combMux s sp a c 0),
                  some (combMux s sp a c 1)], cMul)
              , ([some (combMux s sp a c 1), some cu, some (combMux s sp a c 2)], cAdd) ]))
          else []))
  seedPins ++ stepRows
  -- ⚑ **THE ξ PUBLIC TIE** — `~xi` (`wrap_main.ml:409`) at MINA'S slot 9. ONE half for all 46
  -- ladders, because `combXiV` is one cell: `comb_all_ladders_share_one_xi` is what makes that a
  -- fact about the emission rather than a hope. The value is the RAW 128-bit `Scalar_challenge.
  -- inner`, which is the object `spec.ml:374-392` packs at slot 9 — the endo lift lives in the
  -- ladder, not in the public word.
  ++ packHalves [ ([some (.external WRAP_SLOT_XI : PVar), some (combXiV s sp), none], cEq) ]
  ++ [ probeRow wired (combOutVar t (ns - 1)).1 (combOutVar t (ns - 1)).2 ]

/-- W-COMBINE's variable environment. -/
def combEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let v := combData t
  let ns := combSteps s
  [ (combXiV s sp, (combXiVal : Int)) ]
  ++ (List.range ns).flatMap (fun a =>
      let bval := v.accs.getD a (0, 0)
      let ed := v.eds.getD a default
      let p := endoPQ bval
      let sum := v.sums.getD a (0, 0)
      [ ((combPV s sp a).1, (p.1 : Int)), ((combPV s sp a).2, (p.2 : Int))
      , (combEndoX s sp a, (qMul ENDO_BASE_Q bval.1 : Int))
      , ((combSumV s sp a).1, (sum.1 : Int)), ((combSumV s sp a).2, (sum.2 : Int)) ]
      ++ (List.range (ENDO_BLOCKS + 1)).flatMap (fun e =>
           let pt := ed.accs.getD e (0, 0)
           [ ((combAccPt s sp a e).1, (pt.1 : Int)), ((combAccPt s sp a e).2, (pt.2 : Int)) ])
      ++ (List.range ENDO_BLOCKS).map (fun e => (combN s sp a e, (ed.ns.getD e 0 : Int)))
      ++ (if combIsMux s a then
            let keep := combKeepVal t (combIdx s a)
            (List.range 2).flatMap (fun c =>
              let sm := if c == 0 then sum.1 else sum.2
              let cu := if c == 0 then bval.1 else bval.2
              let d := qSub sm cu
              [ (combMux s sp a c 0, (d : Int))
              , (combMux s sp a c 1, (qMul keep d : Int))
              , (combMux s sp a c 2, (qAdd (qMul keep d) cu : Int)) ])
          else []))

/-! ## §24 — ⚑ **W-BULLET**: `check_bulletproof`, and the 33 endo ladders that close `EndoMul`.

`wrap_verifier.ml:383-437`, read end to end, in upstream's own order:

    Other_field.Packed.absorb_shifted sponge advice.combined_inner_product   (§2b, ONE item)
    let u = group_map (Sponge.squeeze_field sponge)                          (:402-405)
    let combined_polynomial = Split_commitments.combine pcs_batch ~xi …      (§23)
    let scale_fast = scale_fast ~num_bits:Other_field.Packed.Constant.size_in_bits
    let lr_prod, challenges = bullet_reduce sponge lr                        (:158-174)
    let p_prime = let uc = scale_fast u advice.combined_inner_product in combined_polynomial + uc
    let q = p_prime + lr_prod
    absorb sponge PC delta ; let c = squeeze_scalar sponge
    let lhs = let cq = Scalar_challenge.endo q c in cq + delta
    let rhs = let b_u = scale_fast u advice.b in
              let z_1_g_plus_b_u = scale_fast (challenge_polynomial_commitment + b_u) z_1 in
              let z2_h = scale_fast (Inner_curve.constant Generators.h) z_2 in
              z_1_g_plus_b_u + z2_h
    (`Success (equal_g lhs rhs), challenges)

## ⚑ THE CENSUS THIS SECTION CLOSES, AND IT CLOSES TWO FAMILIES

  * **`EndoMul`.** `bullet_reduce` runs `2 × ipaRounds` ladders — an `endo_inv` AND an `endo` per
    round (`:167-168`) — and `lhs` runs one more, so **33** at `ipaRounds = 16`. With W-COMBINE's 46
    that is `79 × 32 = 2528`, which is `wrap-transaction`'s whole `EndoMul` count. Before these two
    rungs this assembly emitted **zero** gates of that type.
  * **`VarBaseMul`.** Four `scale_fast` at `num_bits = 255`, i.e. `4 × 51 = 204` — exactly
    `wrap-transaction`'s `2417` minus W-XHAT's `1805` and W-FTCOMM's `408`.

## ⚑ `bullet_reduce`, AND WHY `endo_inv` IS THE ONLY NEW ARITHMETIC IN THE FILE

`:158-174`. Per round: `absorb (PC :: PC) gammas_i` (four transcript items), `squeeze_scalar`, then

    let term_and_challenge (l, r) pre =
      let left_term = Scalar_challenge.endo_inv l pre in
      let right_term = Scalar_challenge.endo r pre in
      (Ops.add_fast left_term right_term, Bulletproof_challenge.unpack pre)

⚑ `endo_inv` (`scalar_challenge.ml:343-354`) is an `exists G.typ` — so an `assert_on_curve` — plus an
`endo` ladder over that witness plus **two `Field.Assert.equal` tying the ladder's OUTPUT to `l`**.
So the ladder runs FORWARD from a witnessed point and the transcript's `l` is what it must land on;
`KimchiWrapMainField` §19d computes that witness by inverting in Vesta's scalar field, and
`endo_inv_is_the_ladders_inverse` runs the actual ladder on it and gets `l` back. That theorem is the
only thing tying `ENDO_BASE_Q` (Fq, the gate's) to `ENDO_SCALAR_FP` (Fp, the witness generator's),
and it is the pin, not a comment.

⚠ ⚑ **AND IT FORCED A FIXTURE CHANGE, WHICH IS A FLAG DAY: `lr` AND `delta` ARE NOW CURVE POINTS.**
§2d's filler for tags 7 and 8 was `wrapFixture`, i.e. arbitrary field elements. Upstream's arrive
through `Openings.Bulletproof.typ`'s `Inner_curve.typ` and are on-curve by construction, and
`endo_inv` has **no witness at all** over an off-curve `l`. `lrPointQ`/`deltaPointQ` replace them
with doublings of real SRS Lagrange bases — the construction `ftcTVal` already uses for `t_comm`.
**What re-emits:** every rung's witness below `w11_bullet`, because the transcript's absorbed words
moved; the 16 prechallenges and `c` change value, hence public words 13–28. Nothing pinned against
an external source moves — β, γ, α and ζ are squeezed BEFORE `lr` (§2b), so §12a's reality gate and
§14b's `index_digest` are untouched.

## ⚑ `equal_g` IS COMPUTED, AND THE FIXTURE THAT MADE IT COMPUTE **ZERO** IS GONE

`equal_g lhs rhs` (`:177-181`) is `Field.equal` per coordinate then `Boolean.all`, and this section
emits the real gadget: `d = lhs − rhs`, `d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`. Its value is
NOT assumed — `bulletEnv` computes `d` off the assembly and reads `bit` off `d`.

⚠ ⚑ **FOR ONE DAY IT WAS 0, AND THE CAUSE WAS THE KEY.** The step side closes the same gadget by
SOLVING `G := z₁⁻¹·(lhs − z₂·H) − b·u` — one scalar-field inverse and three scalar multiplications —
and that solve needs `lhs` to be **on the curve**. Until 2026-08-04 it was not: `STEP_VK_XY` was
kimchi's own generic-gate TEST index, **seven of whose 28 commitments are the point at infinity**
(`verifier_index.rs:230-238` commits `sigma_comm` and `coefficients_comm` UNMASKED, so a zero column
lands on the identity), `index_to_field_elements` flattens the identity as the fake point `(0, 0)`,
and `Ops.add_fast` is the INCOMPLETE add — a chord through `(0,0)`, which is not on `y² = x³ + 5`. So
W-COMBINE's `combined_polynomial` was an off-curve pair, `p_prime`, `q`, `cq` and `lhs` inherited it,
and no `G` closed the opening: `wrap_main.ml:419-420`'s `Boolean.Assert.is_true bulletproof_success`
was **UNSATISFIABLE at that key**. It was never W-BULLET being incomplete — the gadget was emitted in
full and its witness was honest — it was the FIXTURE.

⚑ **§14 NOW CARRIES MINA'S OWN `step-transaction` KEY, WHOSE 28 COMMITMENTS ARE ALL ON VESTA**
(`key_index_has_no_identity_and_is_on_vesta`), so the fold stays on the curve and the solve is back
in reach. `challenge_polynomial_commitment` accordingly gets its `assert_on_curve` — it is the last
of `bullOCPts` — which is the check upstream's `Openings.Bulletproof.typ` always ran and this rung
could not. `bullet_challenge_commitment_is_on_curve_and_refuses_off_curve` exhibits both poles.

⚠ **WHAT `equal_g` STILL DOES NOT DO, AND SAYING OTHERWISE WOULD BE THE WHOLE DEFECT.** It refuses
nothing by construction even at a good key: `G`, `z₁` and `z₂` have no binder in `verify_one`, so an
honest witness SOLVES for `G` rather than being caught by the equation. That is faithful to upstream
— the binder is the NEXT proof's `finalize_other_proof` — and it is §13's standing residual, not
something this key changed.

## ⚑ THE DEFECT CLASSES, INSIDE THIS SUB-CIRCUIT

  1. **Free ladder seeds.** Every one of the 33 endo ladders pins `φ(t)`'s abscissa, `p`, `acc₀` and
     `n₀`, exactly as §23 does; every one of the four `scale_fast` ladders pins `acc₀ = add_fast base
     base` and `n₀ = 0`, exactly as §17 does. `bullet_every_ladder_seed_is_pinned` reads them off the
     row list.
  2. **Prover-chosen decompositions.** ⚠ The four `scale_fast` carry §17's residual VERBATIM and
     this section does not repair it: `scale_fast` has no top-bit-zero loop, so `B` and `B + q` are
     both admissible 255-bit decompositions of the same scalar. Bounding it here would be a
     divergence from `wrap_main`, not a fix to it.
  3. **Absorbed-but-not-consumed.** ⚑ This rung takes `lr`, `delta` and `combined_inner_product` off
     §2c — the last three entries. `lr` feeds `bullet_reduce`'s 32 ladders and the reduce, `delta`
     feeds `lhs`, and `combined_inner_product` is `uc`'s scalar, tied by
     `Field.Assert.equal !n_acc scalar` as a σ class to the very cell the sponge absorbed.
  4. **Constants pinned against their own definitions.** `Generators.h` is `XHAT_H`, which
     `MinaStepSrsLagrangePin` grounds against the devnet SRS; the Bw19 group-map parameters are
     checked by their DEFINING equations (`bwq_params_are_the_field_construction`) rather than
     transcribed from the step side, and the one that would catch a copy-paste — `Fp`'s
     `sqrt_neg_three_u_squared` is not a square root of `−3` mod `q` — is a conjunct of it.

## ⚠ WHERE THIS EMISSION IS AN UPPER BOUND AND SAYS SO

`group_map` materialises every linear combination that feeds a multiplication as its own `Generic`
half, where Snarky's `assert_r1cs` takes linear combinations as operands directly. So the emitted
half-count is **≥** Snarky's constraint count, never fewer, and the difference is in the cheapest
rows in the file. The ladders — which are 95% of this section — are block-for-block exact. -/

/-- `Ops.scale_fast`'s chunk count here is `ft_comm`'s: same gadget, same width. -/
def SF_CHUNKS : Nat := FTC_CHUNKS
/-- `uc`, `b_u`, `z₁·(G + b_u)`, `z₂·H`. -/
def BULL_SF : Nat := 4
/-- `2 × ipaRounds` from `bullet_reduce` plus `Scalar_challenge.endo q c`. -/
def bullNE (s : WrapShape) : Nat := 2 * s.ipaRounds + 1
/-- The points `Inner_curve.typ` checks here: the `2·ipaRounds` `lr` points, `delta`, the
`ipaRounds` `endo_inv` witnesses, **and `challenge_polynomial_commitment`**, which is the LAST index.

⚑ `G` arrives through `Openings.Bulletproof.typ`'s `Inner_curve.typ` (`wrap_main.ml:357-383`) just
as `lr` and `delta` do, so upstream checks it and so must this. It was omitted for exactly one day:
at the degenerate step key the honest `G := z₁⁻¹(lhs − z₂H) − b·u` solve produced an off-curve
value, because `lhs` itself was off-curve, and emitting the check on a value the honest witness fails
is a rung that cannot be proved. §14's key closed that, so the check is here. -/
def bullOCPts (s : WrapShape) : Nat := 3 * s.ipaRounds + 2

/-! ### §24a — the variable layout. -/

def SF_STRIDE : Nat := 2 * (SF_CHUNKS + 1) + SF_CHUNKS
def EN_STRIDE : Nat := 3 + 2 * (ENDO_BLOCKS + 1) + ENDO_BLOCKS

def BU_GM : Nat := 0
def BU_H : Nat := 43
def BU_G : Nat := 45
def BU_SCAL : Nat := 47
def BU_GB : Nat := 50
def BU_PP : Nat := 52
def BU_Q : Nat := 54
def BU_LHS : Nat := 56
def BU_RHS : Nat := 58
def BU_EQ : Nat := 60
def BU_SF : Nat := 73
def BU_RES : Nat := BU_SF + BULL_SF * SF_STRIDE
def BU_LRT (s : WrapShape) : Nat := BU_RES + 2 * s.ipaRounds
def BU_RED (s : WrapShape) : Nat := BU_LRT s + 2 * s.ipaRounds
def BU_OC (s : WrapShape) : Nat := BU_RED s + 2 * (s.ipaRounds - 1)
def BU_EN (s : WrapShape) : Nat := BU_OC s + 2 * bullOCPts s
def nBullVars (s : WrapShape) : Nat := BU_EN s + bullNE s * EN_STRIDE

def baseBull (s : WrapShape) (sp : SpAcc) : Nat := baseComb s sp + nCombVars s

/-- ⚑ **W-COMBINE'S BLOCK (§17b)** — the fold's cells and W-BULLET's, which stack directly on them.
EXACT, not capped: both are shape arithmetic, and
`bullet_is_the_last_cell_of_the_combine_block` is the `rfl` that the block ends where W-BULLET's
region does. ⚠ It is the TOP block, so an over-run here aliases nothing today — which is exactly why
it still gets `regionEscape`'s refusal: "nothing is above it" is a fact about the ladder as it
stands, and this file has already been wrong once about which of those hold. -/
def COMB_REGION_CAP (s : WrapShape) : Nat := nCombVars s + nBullVars s

theorem bullet_is_the_last_cell_of_the_combine_block (s : WrapShape) (sp : SpAcc) :
    baseBull s sp + nBullVars s = baseComb s sp + COMB_REGION_CAP s := by
  simp [baseBull, COMB_REGION_CAP, Nat.add_assoc]

def bV (s : WrapShape) (sp : SpAcc) (o : Nat) : PVar := .external (baseBull s sp + o)

def bullGm (s : WrapShape) (sp : SpAcc) (i : Nat) : PVar := bV s sp (BU_GM + i)
/-- `u = group_map t` — the dot-products' last cells, and NOT two fresh variables. -/
def bullU (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bullGm s sp 37, bullGm s sp 42)
def bullHV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_H, bV s sp (BU_H + 1))
def bullGV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_G, bV s sp (BU_G + 1))
/-- `0 = advice.b`, `1 = z₁`, `2 = z₂` — all three free, here and upstream. -/
def bullScalV (s : WrapShape) (sp : SpAcc) (j : Nat) : PVar := bV s sp (BU_SCAL + j)
def bullGbV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_GB, bV s sp (BU_GB + 1))
def bullPpV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_PP, bV s sp (BU_PP + 1))
def bullQV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_Q, bV s sp (BU_Q + 1))
def bullLhsV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_LHS, bV s sp (BU_LHS + 1))
def bullRhsV (s : WrapShape) (sp : SpAcc) : PVar × PVar := (bV s sp BU_RHS, bV s sp (BU_RHS + 1))
/-- `equal_g`'s cells: per coordinate `d`, `inv`, `bit`, `bit²`, `d·inv`, `d·bit`; then the `all`. -/
def bullEqV (s : WrapShape) (sp : SpAcc) (i : Nat) : PVar := bV s sp (BU_EQ + i)

def sfAccV (s : WrapShape) (sp : SpAcc) (k j : Nat) : PVar × PVar :=
  (bV s sp (BU_SF + SF_STRIDE * k + 2 * j), bV s sp (BU_SF + SF_STRIDE * k + 2 * j + 1))
def bullResV (s : WrapShape) (sp : SpAcc) (r : Nat) : PVar × PVar :=
  (bV s sp (BU_RES + 2 * r), bV s sp (BU_RES + 2 * r + 1))
def bullLrtV (s : WrapShape) (sp : SpAcc) (r : Nat) : PVar × PVar :=
  (bV s sp (BU_LRT s + 2 * r), bV s sp (BU_LRT s + 2 * r + 1))
def bullRedV (s : WrapShape) (sp : SpAcc) (a : Nat) : PVar × PVar :=
  (bV s sp (BU_RED s + 2 * a), bV s sp (BU_RED s + 2 * a + 1))
def bullOcV (s : WrapShape) (sp : SpAcc) (i c : Nat) : PVar :=
  bV s sp (BU_OC s + 2 * i + c)
def enSlot (s : WrapShape) (sp : SpAcc) (m o : Nat) : PVar :=
  bV s sp (BU_EN s + EN_STRIDE * m + o)
def enPV (s : WrapShape) (sp : SpAcc) (m : Nat) : PVar × PVar :=
  (enSlot s sp m 0, enSlot s sp m 1)
def enEndoX (s : WrapShape) (sp : SpAcc) (m : Nat) : PVar := enSlot s sp m 2
def enAccV (s : WrapShape) (sp : SpAcc) (m e : Nat) : PVar × PVar :=
  (enSlot s sp m (3 + 2 * e), enSlot s sp m (4 + 2 * e))
/-- ⚑ Ladder `m`'s CHALLENGE variable — the cell `Field.Assert.equal !n_acc scalar` lands on.
`m = 2r` and `m = 2r+1` are round `r`'s `endo_inv`/`endo` and share ONE prechallenge (`:161-168`);
`m = 2·ipaRounds` is `c`. Both are the `to_field_checked` chain's reconstructed `n₈`, i.e. the same
cells §10 exposes as public words 13–28 — so a bent prechallenge moves a ladder AND a public word. -/
def bullChalV (t : WrapData) (m : Nat) : PVar :=
  let s := t.sh
  let cb := baseCh s t.sp
  let c := if m == 2 * s.ipaRounds then 4 + s.ipaRounds else 4 + m / 2
  (chainVars s (cb + 1) c).n s.emsRows
def bullChalVal (t : WrapData) (m : Nat) : Nat :=
  let s := t.sh
  let c := if m == 2 * s.ipaRounds then 4 + s.ipaRounds else 4 + m / 2
  ((chalSqueezes t.sp).getD c (PVAR_NOWHERE, 0)).2 % 2 ^ CHAL_BITS s

def enN (t : WrapData) (m e : Nat) : PVar :=
  if e == ENDO_BLOCKS then bullChalV t m
  else enSlot t.sh t.sp m (3 + 2 * (ENDO_BLOCKS + 1) + e)

/-- The transcript's `combined_inner_product` cell — `absorb_shifted` at `:395`, ONE item. -/
def bullCipV (t : WrapData) : PVar :=
  ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_CIP)).getD 0 default).wordV
def bullCipVal (t : WrapData) : Nat := absVal t.sp T_CIP 0
/-- `t`, the FULL field squeeze `group_map` consumes (`:402-403`) — its SOURCE cell, so the sponge
state and the group map's input are one σ class. -/
def bullTV (t : WrapData) : PVar :=
  ((t.sp.evs.filter (fun e => !e.isAbs && e.kind == SqKind.full)).getD 0 default).srcV
def bullTVal (t : WrapData) : Nat :=
  ((t.sp.evs.filter (fun e => !e.isAbs && e.kind == SqKind.full)).getD 0 default).val

/-- `openings_proof.lr.(r)`'s two points, and `delta`, as the TRANSCRIPT's own absorbed cells. -/
def bullLrV (t : WrapData) (r j : Nat) : PVar × PVar :=
  let w : Nat → PVar := fun i =>
    ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_LR)).getD i default).wordV
  (w (4 * r + 2 * j), w (4 * r + 2 * j + 1))
def bullDeltaV (t : WrapData) : PVar × PVar :=
  let w : Nat → PVar := fun i =>
    ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_DELTA)).getD i default).wordV
  (w 0, w 1)
/-- ⚑ **RUNG-DATA-EXPLICIT.** These took no `WrapData` at all until 2026-08-05, which is what made
the borrowed-proof defect structural rather than accidental: a nullary value function CANNOT follow
the tape. They now read `t.sp`, exactly where `bullLrV`/`bullDeltaV` read the variable. -/
def bullLrVal (t : WrapData) (r j : Nat) : Nat × Nat := absPtVal t.sp T_LR (2 * r + j)
def bullDeltaVal (t : WrapData) : Nat × Nat := absPtVal t.sp T_DELTA 0

/-- The three scalars `check_bulletproof` multiplies by. ⚑ **AND THEY ARE NOT ALL THE SAME KIND OF
THING — ONE IS A PUBLIC WORD AND TWO ARE NOT.**

  * `j = 0` is **`advice.b`**, Mina slot **1**: a word `wrap_main` READS out of its public input
    (`wrap_main.ml:405-414`) and never checks. MEASURED since 2026-08-05 through
    `PreparedStatement::to_public_input`, and tied to slot 1 by `bulletRows`.
  * `j = 1, 2` are **`z₁` and `z₂`**, and they stay FIXTURES because they are not statement words at
    all: they are `openings_proof`'s, they have no binder in `wrap_main`, and there is no slot in
    Mina's forty for either. Feeding them a measured number would put a real value in a cell whose
    honesty is that it is free — which is §13's own note and the reason `equal_g` refuses no
    on-curve substitution.

⚠ Do not "finish the job" by measuring 1 and 2. The asymmetry is the faithful shape. -/
def bullScalVal (j : Nat) : Nat :=
  if j == 0 then DEF_B else wrapFixtureQ (40 + j) 0

/-- ⚑ **THE PROVER'S SOLVE FOR `challenge_polynomial_commitment`**, `G := z₁⁻¹·(lhs − z₂·H) − b·u` —
one inverse in VESTA'S SCALAR FIELD and three scalar multiplications, the step side's `bpSolveG`
transposed to the wrap side's curve. Every multiplier carries `Shifted_value.Type1`'s shift, because
`Ops.scale_fast` computes `(2^255 + 2s + 1)·T` and not `[s]·T` (`sfKQ`), so the solve must invert the
SHIFTED `z₁` and subtract the SHIFTED `b·u` or it closes nothing.

⚠ ⚑ **THIS IS WHY `equal_g` REFUSES NOTHING, AND IT IS UPSTREAM'S SHAPE AND NOT OURS.** `G`, `z₁` and
`z₂` reach `check_bulletproof` through `Openings.Bulletproof.typ` with no binder anywhere in
`wrap_main`, so for ANY `lhs` on the curve a prover can produce a `G` that closes the opening — the
equation constrains the TRIPLE and nothing pins two of its three legs. What binds them is the NEXT
proof's `finalize_other_proof`. Emitting the honest witness by SOLVING is therefore faithful, and
saying that the gadget refuses a bad opening would not be.

⚠ It needs `lhs` ON THE CURVE — a scalar multiple of an off-curve pair is meaningless and
`vestaScMul` returns `(0,0)` for a point it cannot ladder. That is exactly what §14's key restored;
before it, this function had nothing to land on and `bullGVal` was a standalone fixture that made
`equal_g` compute 0. -/
def bullSolveG (u H lhs : Nat × Nat) (bv z1 z2 : Nat) : Nat × Nat :=
  let bu := vestaScMul (sfKQ bv) u
  let z2h := vestaScMul (sfKQ z2) H
  let t := addAQ lhs (z2h.1, qSub 0 z2h.2)
  let g := vestaScMul (pInvW (sfKQ z1)) t
  addAQ g (bu.1, qSub 0 bu.2)

/-- One `Ops.scale_fast ~num_bits:255` ladder, seeded exactly as `plonk_curve_ops.ml:157-158`. -/
def sfLadderQ (T : Nat × Nat) (v : Nat) : TermDataQ := runVbmQ T (addAQ T T) (ftcBitsOf v)
def sfOutQ (T : Nat × Nat) (v : Nat) : Nat × Nat := (sfLadderQ T v).accs.getLastD (0, 0)

/-- ⚑ **EVERYTHING W-BULLET EVALUATES, ONCE.** The chain is
`group_map → uc → p_prime → q → cq → lhs` and `b_u → G+b_u → z₁·(…) → rhs`; it is a chain and not a
cycle, which is why one fold suffices. -/
structure BullData where
  gm : List Nat
  /-- the four `scale_fast` traces, in emission order `uc`, `b_u`, `z₁·(G+b_u)`, `z₂·H`. -/
  sfs : List TermDataQ
  /-- `endo_inv`'s witnesses, one per round. -/
  res : List (Nat × Nat)
  /-- the `2·ipaRounds + 1` endo traces. -/
  eds : List EndoDataQ
  /-- `Ops.add_fast left_term right_term`, one per round. -/
  terms : List (Nat × Nat)
  /-- `Array.reduce_exn terms ~f:Ops.add_fast`'s partial sums. -/
  reds : List (Nat × Nat)
  /-- ⚑ **THE DERIVED POINTS, MEMOISED** — `combined_polynomial` (W-COMBINE's output), `lr_prod`,
  `p_prime`, `q`, `cq`, `lhs`, `G + b_u` and `rhs`. They are FIELDS and not `def`s reading `bullData`
  because `bulletRows` names `q` inside a 33-iteration loop, and a `def` that recomputed it would
  replay W-COMBINE's 34 ladders once per iteration — §15's measured lesson, in a new place. -/
  combOut : Nat × Nat
  lrProd : Nat × Nat
  pp : Nat × Nat
  q : Nat × Nat
  lhs : Nat × Nat
  /-- ⚑ `challenge_polynomial_commitment`, SOLVED off `lhs` rather than fixtured. -/
  g : Nat × Nat
  gb : Nat × Nat
  rhs : Nat × Nat
  deriving Inhabited

def bullData (t : WrapData) : BullData :=
  let s := t.sh
  let gm := gmValsQ (bullTVal t)
  let u : Nat × Nat := (gm.getD 37 0, gm.getD 42 0)
  let uc := sfLadderQ u (bullCipVal t)
  let bu := sfLadderQ u (bullScalVal 0)
  -- the rounds: `endo_inv l pre` then `endo r pre`, then their `add_fast`.
  let rd := (List.range s.ipaRounds).foldl
    (fun (st : List (Nat × Nat) × List EndoDataQ × List (Nat × Nat)) r =>
      let pre := bullChalVal t (2 * r)
      let l := bullLrVal t r 0
      let rr := bullLrVal t r 1
      let res := endoInvPtQ l pre
      let e0 := runEndoQ res pre
      let e1 := runEndoQ rr pre
      (st.1 ++ [res], st.2.1 ++ [e0, e1], st.2.2 ++ [addAQ res (e1.accs.getLastD (0, 0))]))
    ([], [], [])
  let terms := rd.2.2
  let reds := (List.range (s.ipaRounds - 1)).foldl
    (fun (acc : List (Nat × Nat)) a =>
      acc ++ [addAQ (if a == 0 then terms.getD 0 (0, 0) else acc.getLastD (0, 0))
                    (terms.getD (a + 1) (0, 0))])
    []
  let lrProd := if s.ipaRounds == 1 then terms.getD 0 (0, 0) else reds.getLastD (0, 0)
  let combined := (combData t).accs.getLastD (0, 0)
  let pp := addAQ combined (uc.accs.getLastD (0, 0))
  let q := addAQ pp lrProd
  let ec := runEndoQ q (bullChalVal t (2 * s.ipaRounds))
  -- ⚑ `lhs` FIRST, then the solve, then `rhs` — a chain and not a cycle, because `G` enters only
  -- through `gb` and nothing on the `lhs` side reads it.
  let lhs := addAQ (ec.accs.getLastD (0, 0)) (bullDeltaVal t)
  let g := bullSolveG u XHAT_H lhs (bullScalVal 0) (bullScalVal 1) (bullScalVal 2)
  let gb := addAQ g (bu.accs.getLastD (0, 0))
  let z1g := sfLadderQ gb (bullScalVal 1)
  let z2h := sfLadderQ XHAT_H (bullScalVal 2)
  { gm := gm, sfs := [uc, bu, z1g, z2h], res := rd.1, eds := rd.2.1 ++ [ec]
  , terms := terms, reds := reds
  , combOut := combined, lrProd := lrProd, pp := pp, q := q
  , lhs := lhs
  , g := g
  , gb := gb
  , rhs := addAQ (z1g.accs.getLastD (0, 0)) (z2h.accs.getLastD (0, 0)) }

/-- The derived points, READ OFF `bullData` rather than recomputed. -/
def bullLrProd (_t : WrapData) (v : BullData) : Nat × Nat := v.lrProd
def bullUc (_t : WrapData) (v : BullData) : Nat × Nat := (v.sfs.getD 0 default).accs.getLastD (0, 0)
def bullBu (_t : WrapData) (v : BullData) : Nat × Nat := (v.sfs.getD 1 default).accs.getLastD (0, 0)
def bullPp (_t : WrapData) (v : BullData) : Nat × Nat := v.pp
def bullQ (_t : WrapData) (v : BullData) : Nat × Nat := v.q
def bullCq (t : WrapData) (v : BullData) : Nat × Nat :=
  (v.eds.getD (2 * t.sh.ipaRounds) default).accs.getLastD (0, 0)
def bullLhs (_t : WrapData) (v : BullData) : Nat × Nat := v.lhs
/-- `challenge_polynomial_commitment`, as `bullData` solved it. -/
def bullG (_t : WrapData) (v : BullData) : Nat × Nat := v.g
def bullGb (_t : WrapData) (v : BullData) : Nat × Nat := v.gb
def bullZ1g (_t : WrapData) (v : BullData) : Nat × Nat := (v.sfs.getD 2 default).accs.getLastD (0, 0)
def bullZ2h (_t : WrapData) (v : BullData) : Nat × Nat := (v.sfs.getD 3 default).accs.getLastD (0, 0)
def bullRhs (_t : WrapData) (v : BullData) : Nat × Nat := v.rhs

/-- Ladder `k`'s base variable / value, and its scalar's. -/
def sfBaseVar (t : WrapData) (k : Nat) : PVar × PVar :=
  if k ≤ 1 then bullU t.sh t.sp else if k == 2 then bullGbV t.sh t.sp else bullHV t.sh t.sp
def sfBaseVal (t : WrapData) (v : BullData) (k : Nat) : Nat × Nat :=
  if k ≤ 1 then (v.gm.getD 37 0, v.gm.getD 42 0) else if k == 2 then bullGb t v else XHAT_H
def sfScalVar (t : WrapData) (k : Nat) : PVar :=
  if k == 0 then bullCipV t else bullScalV t.sh t.sp (k - 1)
def sfScalVal (t : WrapData) (k : Nat) : Nat :=
  if k == 0 then bullCipVal t else bullScalVal (k - 1)
/-- The counter at chunk boundary `j`; at `j = SF_CHUNKS` it IS the scalar's own cell. -/
def sfN (t : WrapData) (k j : Nat) : PVar :=
  if j == SF_CHUNKS then sfScalVar t k
  else bV t.sh t.sp (BU_SF + SF_STRIDE * k + 2 * (SF_CHUNKS + 1) + j)

/-- The `i`-th point `Inner_curve.typ` checks, as a variable and a value: the `2·ipaRounds` `lr`
points, `delta`, the `ipaRounds` `endo_inv` witnesses, then `challenge_polynomial_commitment`. -/
def bullOcVar (t : WrapData) (v : BullData) (i : Nat) : PVar × PVar :=
  let s := t.sh
  if i < 2 * s.ipaRounds then bullLrV t (i / 2) (i % 2)
  else if i == 2 * s.ipaRounds then bullDeltaV t
  else if i == 3 * s.ipaRounds + 1 then bullGV s t.sp
  else bullResV s t.sp (i - 2 * s.ipaRounds - 1)
def bullOcVal (t : WrapData) (v : BullData) (i : Nat) : Nat × Nat :=
  let s := t.sh
  if i < 2 * s.ipaRounds then bullLrVal t (i / 2) (i % 2)
  else if i == 2 * s.ipaRounds then bullDeltaVal t
  else if i == 3 * s.ipaRounds + 1 then v.g
  else v.res.getD (i - 2 * s.ipaRounds - 1) (0, 0)

/-! ### §24b — the rows. -/

/-- **`group_map`'s rows** — `Snarky_group_map.Checked.wrap` (`checked_map.ml:20-55`) at Fq, one
`Generic` half per Snarky operation. ⚑ `y_squared`'s `a·x` term folds away because Vesta's
`Params.a = 0`, so `Field.mul` on a constant-zero operand emits nothing (`wrap_verifier.ml:310-316`). -/
def bullGmRows (s : WrapShape) (sp : SpAcc) (tv : PVar) : List WRow :=
  let V := bullGm s sp
  packHalves
    ( [ ([some tv, some tv, some (V 0)], cMul)
      , ([some (V 0), some (V 1), none], [1, -1, 0, 0, (BWQ_FU : Int)])
      , ([some (V 1), some (V 0), some (V 2)], cMul)
      , ([some (V 3), some (V 2), none], [0, 0, 0, 1, -1])
      , ([some (V 0), some (V 0), some (V 4)], cMul)
      , ([some (V 4), some (V 3), some (V 5)], cMul)
      , ([some (V 5), some (V 6), none], [-(BWQ_SQ3 : Int), -1, 0, 0, (BWQ_SQ3_MU2 : Int)])
      , ([some (V 6), some (V 7), none], [-1, -1, 0, 0, -(BWQ_U : Int)])
      , ([some (V 3), some (V 1), some (V 8)], cMul)
      , ([some (V 1), some (V 1), some (V 9)], cMul)
      , ([some (V 9), some (V 8), some (V 10)], cMul)
      , ([some (V 10), some (V 11), none], [-(BWQ_INV3U2 : Int), -1, 0, 0, (BWQ_U : Int)]) ]
      ++ (List.range 3).flatMap (fun i =>
          let x := V (if i == 0 then 6 else if i == 1 then 7 else 11)
          let o := 12 + 6 * i
          [ ([some x, some x, some (V o)], cMul)
          , ([some (V o), some x, some (V (o+1))], [0, 0, -1, 1, (VESTA_B : Int)])
          , ([some (V (o+2)), some (V (o+2)), none], [-1, 0, 0, 1, 0])
          , ([some (V (o+2)), some (V (o+1)), some (V (o+3))],
             [0, 0, -1, ((qN + 1 - FQ_NONRES : Nat) : Int), 0])
          , ([some (V (o+1)), some (V (o+3)), some (V (o+4))], [(FQ_NONRES : Int), 1, -1, 0, 0])
          , ([some (V (o+5)), some (V (o+5)), some (V (o+4))], cMul) ])
      ++ [ ([some (V 14), some (V 20), some (V 30)], [-1, -1, -1, 1, 1])
         , ([some (V 30), some (V 26), none], [1, 0, 0, -1, 0])
         , ([some (V 20), some (V 14), some (V 31)], [1, 0, -1, -1, 0])
         , ([some (V 30), some (V 26), some (V 32)], cMul) ]
      ++ (List.range 2).flatMap (fun c =>
          let o := 33 + 5 * c
          let xs : Nat → Nat := fun i =>
            if c == 0 then (if i == 0 then 6 else if i == 1 then 7 else 11) else 17 + 6 * i
          [ ([some (V 14), some (V (xs 0)), some (V o)], cMul)
          , ([some (V 31), some (V (xs 1)), some (V (o+1))], cMul)
          , ([some (V 32), some (V (xs 2)), some (V (o+2))], cMul)
          , ([some (V o), some (V (o+1)), some (V (o+3))], cAdd)
          , ([some (V (o+3)), some (V (o+2)), some (V (o+4))], cAdd) ]) )

/-- The two rows of `scale_fast` ladder `k`'s chunk `j` — the same `(VarBaseMul, Zero)` pair
`ftcChunkRows` emits, at this region's slots. ⚑ No top-bit-zero cells: `scale_fast` has no such loop
(§17), so all five bit cells stay in ADVICE. -/
def sfChunkRows (t : WrapData) (k : Nat) (td : TermDataQ) (bits : List Nat) (j : Nat) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let bv := sfBaseVar t k
  let ax : Nat → Int := fun n => ((td.accs.getD n (0, 0)).1 : Int)
  let ay : Nat → Int := fun n => ((td.accs.getD n (0, 0)).2 : Int)
  let sl : Nat → Int := fun n => (td.slopes.getD n 0 : Int)
  let bt : Nat → Int := fun n => (bits.getD n 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some bv.1, some bv.2
              , some (sfAccV s sp k j).1, some (sfAccV s sp k j).2
              , some (sfN t k j), some (sfN t k (j + 1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (sfAccV s sp k (j+1)).1, some (sfAccV s sp k (j+1)).2
              , none, none, none, none, none ]
    , advice := (List.range 5).map (fun tt => (2 + tt, bt (5*j+tt)))
                ++ (List.range 5).map (fun tt => (7 + tt, sl (5*j+tt))) } ]

/-- One `Scalar_challenge.endo` ladder's rows: the `φ(t)` add, the doubling seed, 32 `EndoMul`
blocks and the closing `Zero`. ⚑ The `CompleteAdd` that seeds `acc₀` sits IMMEDIATELY before the 32
blocks, which is `wrap-transaction`'s own run-length signature. -/
def enLadderRows (t : WrapData) (v : BullData) (m : Nat) (bv : PVar × PVar) (bval : Nat × Nat)
    : List WRow :=
  let s := t.sh
  let sp := t.sp
  let ed := v.eds.getD m default
  let q : Nat × Nat := (qMul ENDO_BASE_Q bval.1, bval.2)
  let p := endoPQ bval
  [ caRowQ bv (enEndoX s sp m, bv.2) (enPV s sp m) (caWitnessQ bval.1 bval.2 q.1 q.2)
  , caRowQ (enPV s sp m) (enPV s sp m) (enAccV s sp m 0) (caWitnessQ p.1 p.2 p.1 p.2) ]
  ++ (List.range ENDO_BLOCKS).map (fun e =>
      let b := ed.blks.getD e default
      ({ kind := .endoMul
       , perm := [ some bv.1, some bv.2, none, none
                 , some (enAccV s sp m e).1, some (enAccV s sp m e).2, some (enN t m e) ]
       , advice := [ (2, (b.inv : Int)), (3, 0), (7, (b.xr : Int)), (8, (b.yr : Int))
                   , (9, (b.s1 : Int)), (10, (b.s3 : Int)), (11, (b.b1 : Int)), (12, (b.b2 : Int))
                   , (13, (b.b3 : Int)), (14, (b.b4 : Int)) ] } : WRow))
  ++ [ { kind := .zero
       , perm := [ none, none, none, none
                 , some (enAccV s sp m ENDO_BLOCKS).1, some (enAccV s sp m ENDO_BLOCKS).2
                 , some (enN t m ENDO_BLOCKS) ] } ]

/-- **W-BULLET's ROWS.** -/
def bulletRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let v := bullData t
  let R := s.ipaRounds
  let enBase : Nat → PVar × PVar := fun m =>
    if m == 2 * R then bullQV s sp
    else if m % 2 == 0 then bullResV s sp (m / 2)
    else bullLrV t (m / 2) 1
  let enBaseVal : Nat → Nat × Nat := fun m =>
    if m == 2 * R then bullQ t v
    else if m % 2 == 0 then v.res.getD (m / 2) (0, 0)
    else bullLrVal t (m / 2) 1
  -- (1) the pins: `Generators.h`, every ladder's `n₀ = 0` and `φ(t)`'s abscissa, and the four
  --     `scale_fast` counters' zero seeds.
  let pins : List WRow :=
    [ ptConstRow (bullHV s sp).1 (bullHV s sp).2 XHAT_H ]
    ++ packHalves
        ((List.range (bullNE s)).flatMap (fun m =>
          [ ([some (enN t m 0), none, none], cConst 0)
          , ([some (enBase m).1, none, some (enEndoX s sp m)],
             [(ENDO_BASE_Q : Int), 0, -1, 0, 0]) ])
         ++ (List.range BULL_SF).map (fun k => ([some (sfN t k 0), none, none], cConst 0)))
  -- (2) `Inner_curve.typ`'s `assert_on_curve` on every point this rung witnesses or reads as one.
  let ocRows : List WRow :=
    packHalves ((List.range (bullOCPts s)).flatMap (fun i =>
      let pv := bullOcVar t v i
      [ ([some pv.1, some pv.1, some (bullOcV s sp i 0)], cMul)
      , ([some (bullOcV s sp i 0), some pv.1, some (bullOcV s sp i 1)], cMul)
      , ([some pv.2, some pv.2, some (bullOcV s sp i 1)], cOnCurveQ) ]))
  -- (3) `u = group_map (Sponge.squeeze_field sponge)` (`:402-405`).
  let gmRows : List WRow := bullGmRows s sp (bullTV t) ++ [ probeRow wired (bullU s sp).1 (bullU s sp).2 ]
  -- (4) one `Ops.scale_fast` ladder's rows, at slot `k`.
  let sfRows : Nat → List WRow := fun k =>
    let bvl := sfBaseVal t v k
    let td := v.sfs.getD k default
    [ caRowQ (sfBaseVar t k) (sfBaseVar t k) (sfAccV s sp k 0) (caWitnessQ bvl.1 bvl.2 bvl.1 bvl.2) ]
    ++ (List.range SF_CHUNKS).flatMap (sfChunkRows t k td (ftcBitsOf (sfScalVal t k)))
  -- (5) `bullet_reduce` (`:158-174`): per round the two ladders and their `add_fast`, then the
  --     left-associated `Array.reduce_exn`.
  let roundRows : List WRow :=
    (List.range R).flatMap (fun r =>
      [ probeRow wired (bullResV s sp r).1 (bullResV s sp r).2 ]
      ++ enLadderRows t v (2 * r) (enBase (2 * r)) (enBaseVal (2 * r))
      -- ⚑ `endo_inv`'s two `Field.Assert.equal`: the ladder's OUTPUT is the transcript's `l`.
      ++ packHalves
          [ ([some (enAccV s sp (2 * r) ENDO_BLOCKS).1, some (bullLrV t r 0).1, none], cEq)
          , ([some (enAccV s sp (2 * r) ENDO_BLOCKS).2, some (bullLrV t r 0).2, none], cEq) ]
      ++ enLadderRows t v (2 * r + 1) (enBase (2 * r + 1)) (enBaseVal (2 * r + 1))
      ++ [ caRowQ (bullResV s sp r) (enAccV s sp (2 * r + 1) ENDO_BLOCKS) (bullLrtV s sp r)
             (caWitnessQ (v.res.getD r (0, 0)).1 (v.res.getD r (0, 0)).2
               ((v.eds.getD (2 * r + 1) default).accs.getLastD (0, 0)).1
               ((v.eds.getD (2 * r + 1) default).accs.getLastD (0, 0)).2) ])
  let redRows : List WRow :=
    (List.range (R - 1)).map (fun a =>
      let lv := if a == 0 then v.terms.getD 0 (0, 0) else v.reds.getD (a - 1) (0, 0)
      let rv := v.terms.getD (a + 1) (0, 0)
      caRowQ (if a == 0 then bullLrtV s sp 0 else bullRedV s sp (a - 1)) (bullLrtV s sp (a + 1))
        (bullRedV s sp a) (caWitnessQ lv.1 lv.2 rv.1 rv.2))
  -- (6) `p_prime`, `q`, `cq`, `lhs`.
  let combOut := combOutVar t (combSteps s - 1)
  let combVal := v.combOut
  let lrpV : PVar × PVar := if R == 1 then bullLrtV s sp 0 else bullRedV s sp (R - 2)
  let tailRows : List WRow :=
    [ caRowQ combOut (sfAccV s sp 0 SF_CHUNKS) (bullPpV s sp)
        (caWitnessQ combVal.1 combVal.2 (bullUc t v).1 (bullUc t v).2)
    , caRowQ (bullPpV s sp) lrpV (bullQV s sp)
        (caWitnessQ (bullPp t v).1 (bullPp t v).2 (bullLrProd t v).1 (bullLrProd t v).2)
    , probeRow wired (bullQV s sp).1 (bullQV s sp).2 ]
    ++ enLadderRows t v (2 * R) (enBase (2 * R)) (enBaseVal (2 * R))
    ++ [ caRowQ (enAccV s sp (2 * R) ENDO_BLOCKS) (bullDeltaV t) (bullLhsV s sp)
           (caWitnessQ (bullCq t v).1 (bullCq t v).2 (bullDeltaVal t).1 (bullDeltaVal t).2)
       , probeRow wired (bullLhsV s sp).1 (bullLhsV s sp).2 ]
  -- (7) `rhs = z₁·(G + b_u) + z₂·H`, then `equal_g`.
  let rhsRows : List WRow :=
    [ caRowQ (bullGV s sp) (sfAccV s sp 1 SF_CHUNKS) (bullGbV s sp)
        (caWitnessQ (bullG t v).1 (bullG t v).2 (bullBu t v).1 (bullBu t v).2) ]
    ++ sfRows 2 ++ sfRows 3
    ++ [ caRowQ (sfAccV s sp 2 SF_CHUNKS) (sfAccV s sp 3 SF_CHUNKS) (bullRhsV s sp)
           (caWitnessQ (bullZ1g t v).1 (bullZ1g t v).2 (bullZ2h t v).1 (bullZ2h t v).2)
       , probeRow wired (bullRhsV s sp).1 (bullRhsV s sp).2 ]
  -- ⚑ `equal_g` (`:177-181`): `Field.equal` per coordinate, then `Boolean.all` of the two.
  let eqRows : List WRow :=
    packHalves ((List.range 2).flatMap (fun i =>
      let l := if i == 0 then (bullLhsV s sp).1 else (bullLhsV s sp).2
      let r := if i == 0 then (bullRhsV s sp).1 else (bullRhsV s sp).2
      let o := 6 * i
      [ ([some l, some r, some (bullEqV s sp o)], cSubQ)
      , ([some (bullEqV s sp (o+2)), some (bullEqV s sp (o+2)), some (bullEqV s sp (o+3))], cMul)
      , ([some (bullEqV s sp (o+3)), some (bullEqV s sp (o+2)), none], cEq)
      , ([some (bullEqV s sp o), some (bullEqV s sp (o+1)), some (bullEqV s sp (o+4))], cMul)
      , ([some (bullEqV s sp (o+4)), some (bullEqV s sp (o+2)), none], [1, 1, 0, 0, -1])
      , ([some (bullEqV s sp o), some (bullEqV s sp (o+2)), some (bullEqV s sp (o+5))], cMul)
      , ([some (bullEqV s sp (o+5)), none, none], cConst 0) ])
      ++ [ ([some (bullEqV s sp 2), some (bullEqV s sp 8), some (bullEqV s sp 12)], cMul) ])
  pins ++ ocRows ++ gmRows ++ sfRows 0 ++ sfRows 1
  ++ roundRows ++ redRows ++ tailRows ++ rhsRows ++ eqRows
  -- ⚑ **THE TWO `~advice` PUBLIC TIES** — `combined_inner_product` at MINA'S slot 0 and `b` at slot
  -- 1, both read by `check_bulletproof` (`wrap_verifier.ml:395`) and checked by neither this proof
  -- nor this rung.
  -- ⚠ **SLOT 0's CELL IS THE TRANSCRIPT'S, NOT A FRESH WITNESS.** `bullCipV` is the word the sponge
  -- ABSORBED — upstream absorbs `advice.combined_inner_product` itself, so tying slot 0 here says
  -- the absorbed word and the public word are one object, which upstream they are. Slot 1's cell is
  -- `bullScalV … 0`, the `b·u` multiplier. `z₁`/`z₂` (`bullScalV … 1, 2`) get NO tie: they are
  -- `openings_proof`'s and have no slot in Mina's forty.
  ++ packHalves
       [ ([some (.external WRAP_SLOT_CIP : PVar), some (bullCipV t), none], cEq)
       , ([some (.external WRAP_SLOT_B : PVar), some (bullScalV s sp 0), none], cEq) ]
  ++ [ probeRow wired (bullEqV s sp 12) (bullEqV s sp 2) ]

/-- W-BULLET's variable environment. -/
def bulletEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let v := bullData t
  let R := s.ipaRounds
  let enBaseVal : Nat → Nat × Nat := fun m =>
    if m == 2 * R then bullQ t v
    else if m % 2 == 0 then v.res.getD (m / 2) (0, 0)
    else bullLrVal t (m / 2) 1
  (List.range 43).map (fun i => (bullGm s sp i, (v.gm.getD i 0 : Int)))
  ++ [ ((bullHV s sp).1, (XHAT_H.1 : Int)), ((bullHV s sp).2, (XHAT_H.2 : Int))
     , ((bullGV s sp).1, ((bullG t v).1 : Int)), ((bullGV s sp).2, ((bullG t v).2 : Int))
     , ((bullGbV s sp).1, ((bullGb t v).1 : Int)), ((bullGbV s sp).2, ((bullGb t v).2 : Int))
     , ((bullPpV s sp).1, ((bullPp t v).1 : Int)), ((bullPpV s sp).2, ((bullPp t v).2 : Int))
     , ((bullQV s sp).1, ((bullQ t v).1 : Int)), ((bullQV s sp).2, ((bullQ t v).2 : Int))
     , ((bullLhsV s sp).1, ((bullLhs t v).1 : Int)), ((bullLhsV s sp).2, ((bullLhs t v).2 : Int))
     , ((bullRhsV s sp).1, ((bullRhs t v).1 : Int)), ((bullRhsV s sp).2, ((bullRhs t v).2 : Int)) ]
  ++ (List.range 3).map (fun j => (bullScalV s sp j, (bullScalVal j : Int)))
  ++ (List.range BULL_SF).flatMap (fun k =>
      let td := v.sfs.getD k default
      (List.range (SF_CHUNKS + 1)).flatMap (fun j =>
        let a := td.accs.getD (5 * j) (0, 0)
        [ ((sfAccV s sp k j).1, (a.1 : Int)), ((sfAccV s sp k j).2, (a.2 : Int)) ])
      ++ (List.range SF_CHUNKS).map (fun j => (sfN t k j, (td.ns.getD (5 * j) 0 : Int))))
  ++ (List.range R).flatMap (fun r =>
      [ ((bullResV s sp r).1, ((v.res.getD r (0, 0)).1 : Int))
      , ((bullResV s sp r).2, ((v.res.getD r (0, 0)).2 : Int))
      , ((bullLrtV s sp r).1, ((v.terms.getD r (0, 0)).1 : Int))
      , ((bullLrtV s sp r).2, ((v.terms.getD r (0, 0)).2 : Int)) ])
  ++ (List.range (R - 1)).flatMap (fun a =>
      [ ((bullRedV s sp a).1, ((v.reds.getD a (0, 0)).1 : Int))
      , ((bullRedV s sp a).2, ((v.reds.getD a (0, 0)).2 : Int)) ])
  ++ (List.range (bullOCPts s)).flatMap (fun i =>
      let p := bullOcVal t v i
      [ (bullOcV s sp i 0, (qMul p.1 p.1 : Int))
      , (bullOcV s sp i 1, (qMul (qMul p.1 p.1) p.1 : Int)) ])
  ++ (List.range (bullNE s)).flatMap (fun m =>
      let ed := v.eds.getD m default
      let bval := enBaseVal m
      let p := endoPQ bval
      [ ((enPV s sp m).1, (p.1 : Int)), ((enPV s sp m).2, (p.2 : Int))
      , (enEndoX s sp m, (qMul ENDO_BASE_Q bval.1 : Int)) ]
      ++ (List.range (ENDO_BLOCKS + 1)).flatMap (fun e =>
           let a := ed.accs.getD e (0, 0)
           [ ((enAccV s sp m e).1, (a.1 : Int)), ((enAccV s sp m e).2, (a.2 : Int)) ])
      ++ (List.range ENDO_BLOCKS).map (fun e => (enN t m e, (ed.ns.getD e 0 : Int))))
  -- ⚑ `equal_g`'s witness, COMPUTED off the assembly: `d = lhs − rhs` per coordinate, `bit` READ OFF
  -- `d`. Nothing here asserts which way it lands — §24's header records what it was at the old
  -- degenerate key and `close_bulletproof_success_is_satisfiable` states what it is at Mina's.
  ++ (List.range 2).flatMap (fun i =>
      let l := if i == 0 then (bullLhs t v).1 else (bullLhs t v).2
      let r := if i == 0 then (bullRhs t v).1 else (bullRhs t v).2
      let d : Nat := qSub l r
      let bit : Nat := if d == 0 then 1 else 0
      let iv : Nat := if d == 0 then 0 else qInv d
      let o := 6 * i
      [ (bullEqV s sp o, (d : Int)), (bullEqV s sp (o+1), (iv : Int))
      , (bullEqV s sp (o+2), (bit : Int)), (bullEqV s sp (o+3), (bit : Int))
      , (bullEqV s sp (o+4), (qMul d iv : Int)), (bullEqV s sp (o+5), (qMul d bit : Int)) ])
  ++ [ (bullEqV s sp 12,
        ((if bullLhs t v == bullRhs t v then 1 else 0 : Nat) : Int)) ]

/-! ### §22b — ⚑ **W-CLOSE'S ROWS AND ENVIRONMENT LIVE HERE**, after §24, because they now read
W-BULLET's `bullEqV`/`bullData`. §22's base, cell and cap theorem stay where the block arithmetic is;
only the two definitions that acquired a W-BULLET dependency moved. -/

/-- **W-CLOSE's ROWS.** `Boolean.Assert.is_true bulletproof_success`, and a σ-only probe so the
rung's own cell is testable by the harness rather than merely present. -/
def closeRows (t : WrapData) (wired : Bool) : List WRow :=
  let v := bpSuccessVar t.sh t.sp
  -- ⚑ the σ-TIE: `bulletproof_success` IS `equal_g`'s `Boolean.all` output, one class, then the
  -- assert. Two halves, one `Generic` double gate.
  packHalves [ ([some v, some (bullEqV t.sh t.sp 12), none], cEq)
             , ([some v, none, none], cConst 1) ]
  ++ [ probeRow wired v (whDigestVar (whSpongeC t)) ]

/-- W-CLOSE's variable environment. ⚑ **COMPUTED, NOT ASSERTED**: `bulletproof_success`'s witness is
`equal_g`'s own verdict off `bullData`, the same expression `bulletEnv` gives `bullEqV s sp 12`. It
read `(1 : Int)` until 2026-08-05, which made the rung's `cConst 1` a statement about a constant this
file wrote. -/
def closeEnv (t : WrapData) : VarEnv :=
  let v := bullData t
  [ (bpSuccessVar t.sh t.sp,
     ((if bullLhs t v == bullRhs t v then 1 else 0 : Nat) : Int)) ]


/-! ## §20 — ⚑ **W-FINSPONGE**: `finalize_other_proof`'s SPONGE HALF, and the three legs it closes.

`wrap_verifier.ml:844-1013`. §19 emits `plonk_checks_passed` and named the other three legs of
`Boolean.all [xi_correct; b_correct; combined_inner_product_correct; plonk_checks_passed]` as the
remainder, because **all three need ξ and r, which are the finalize sponge's two squeezes**. Three
lanes in a row declined to emit them as free witnesses — correctly, a witness nothing constrains is
not a leg — so this rung emits **the sponge**, and the legs follow from it.

## WHAT UPSTREAM DOES, READ OFF A REAL DEVNET BLOCK RATHER THAN OFF PROSE

The tape is not inferred here. `metatheory/mina_real_block_proof.json` is devnet block 539508
(`3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`), ground-truthed
`openmina BlockVerifier + accumulator_check=true + kimchi::verifier::verify=Ok`, and its
`wrap_transcript` carries the **whole phase-2 tape and both of its squeezes**:
`phase2_tape_len = 91`, `prev_challenge_digest`, `phase2_evals_tape` (86), `v_chal`, `u_chal`. So:

  * **a NESTED sponge first.** `Sponge.create`, absorb the flattened old bulletproof challenges —
    `WH_MLMB · WH_ROUNDS = 30` of them, the SAME vector §21's `hash_messages_for_next_wrap_proof`
    absorbs — and close with ONE `Sponge.squeeze_field`. That is `prev_challenge_digest`, and
    `finalize_sponge_reproduces_the_accepted_block` derives the block's own out of this file's
    emitter.
  * **then the finalize sponge**, `Sponge.create` again, over **91** elements:
    `sponge_digest_before_evaluations` (packed word 5 of the block), the challenge digest,
    `ft_eval1`, `evals.public_input.0`, `evals.public_input.1`, and then
    `Evals.to_absorption_sequence` — the **43 columns at ζ and ζω INTERLEAVED**, 86 cells, in
    §19c's own `FIN_NCOLS` order.
  * **then TWO squeezes**, ξ′ and r′ (`:892-894`). ⚑ They come out of **ONE** permutation, at lanes
    0 and 1: the rate-2 machine §4 already runs leaves the sponge `Absorbed 1` after 91 absorbs, the
    first squeeze permutes, the second reads lane 1 with no permutation at all. A block model would
    put them two permutations apart and every value below would be wrong.

⚑ **THE 86 CELLS ARE `w10_finalize`'s OWN.** `finEvVar` is where §19 witnesses `Req.Evals`, and this
sponge absorbs those variables — including the SOLVED `z(ζω)` of the block that claims
`should_finalize`. That is the whole point of the rung sitting above §19 rather than beside it:
`plonk_checks_passed` and `combined_inner_product_correct` read ONE set of evaluation columns, and a
prover who moves a column to satisfy one of them moves ξ and breaks the other.

## THE THREE LEGS

  * **`xi_correct`** (`:895-902`) — `xi_actual = lowest_128_bits ~constrain_low_bits:true` of the
    first squeeze, `Field.equal`'d against the block's own packed word 10. Both halves are
    range-checked exactly as §5 does for the transcript's challenges: the low part IS a
    `to_field_checked` chain, the high part gets its own `assert_128_bits` chain.
  * **`b_correct`** (`:1015-1026`) — `b_actual = challenge_polynomial(ζ) + r · challenge_polynomial(ζω)`
    over the FIFTEEN lifted bulletproof challenges of the block (`compute_challenges`, `:1012-1013`),
    against `Shifted_value.Type2.to_field` of packed word 1. `zetaw = ω · ζ` at the wrap domain's own
    generator, which §19c pins.
  * **`combined_inner_product_correct`** (`:951-1009`) — `Pcs_batch.combine_split_evaluations`, a
    Horner fold in ξ over **47** entries per point: the `maxPrevs` old accumulators' challenge
    polynomials at that point, `evals.public_input`, `ft_eval`, then the 43 columns; the ζ fold uses
    **§19's own `ft_eval0` slot** and the ζω fold uses `ft_eval1`; and the two combine as
    `combine ζ + r · combine ζω`. ⚑ **THE FOLD IS CHECKED AGAINST THE SAME REAL BLOCK**, not against
    its own definition: at block 539508's ξ, r, ζ, ζω, evaluations, `ft_eval0`/`ft_eval1`, public
    evals and 2 × 15 recursion challenges, this expression reproduces that proof's
    `combined_inner_product` on the nose. The measurement is what fixed the entry ORDER and the
    Horner DIRECTION, both of which prose gets wrong silently.

## ⚑ THREE PACKED STATEMENT WORDS BECOME DERIVED, AND THAT IS A FLAG DAY

`Boolean.Assert.any [finalized; not should_finalize]` is §19's row and `finalized` is now the AND of
four legs. Block 1's packed word 53 IS `should_finalize = 1` (§19 measured it), so block 1 must
satisfy **all four** — which means its `combined_inner_product`, `b` and `xi` words are no longer
free fixtures. They are `FIN_DEFERRED_*`, a MEMO WITH A PROOF OBLIGATION in the shape of
`WrapShape.xhatXY`: `fin_deferred_words_are_the_derivation` (`…Pins12`) closes them against the very
program and sponge this rung emits, and `EmitWrapMainJson` REFUSES to emit a disagreeing tree.
⚠ That theorem was named HERE and in three other docblocks for a day before anyone wrote it, and
what they promised — `rfl`, in the kernel — was never reachable: the derivation is two sponges and a
**1732**-op `Array FOp` program, and `whnf` models an `Array` as a `List`. It is `native_decide` +
`#assert_compiled`, at the smoke shape; the wrap shape is covered by the emitter's refusal.

**WHAT RE-EMITS:** everything from `w6_xhat` up at the WRAP shape — packed words 27, 28 and 37 are
x_hat entries 32/33, 34/35 and 47, so `xhatOut 67` moves and with it the absorbed `x_hat`, every
challenge and all 24 derived public words. The SMOKE shape does not move: `xhatSel 5` selects none
of those five entries, which is why the committed fixtures below this rung are byte-identical.

⚠ **AND BLOCK 0 KEEPS ITS FIXTURES, WHICH IS WHAT KEEPS THE ASSERT FALSIFIABLE.** Deriving all three
words in EVERY block would force `xc = bc = cc = 1` for any witness the emitter can produce, and
`(1 − finalized)·should_finalize = 0` would have no failing instance left — the exact defect the
`w10_finalize` lane caught in its own solve. Block 0 does not claim `should_finalize`, so it runs
all three `Field.equal` gadgets at NONZERO differences and takes the `(d⁻¹, 0)` branch, while block
1 takes `(0, 1)`. Both branches live, and the assert reds the moment block 0 claims `should_finalize`.

⚠ **`old_bp_chals` IS ONE `exists` UPSTREAM AND THIS LADDER HOLDS TWO COPIES.** `wrap_main.ml:226-256`
witnesses it once; `hash_messages_for_next_wrap_proof` (§21, the `.wraphack` branch) and this rung's
challenge digest both read it. `.finsponge` does not contain `.wraphack`, so the two branches allocate
two regions over one vector at one set of VALUES. That is the §21 composition hazard in a new place
and it closes the same way — when the ladder becomes one chain, the two become one σ class. Said,
not banked. -/

/-- An old bulletproof challenge, absorbed by the challenge-digest sponge. -/
def T_FINOLD : Nat := 11
/-- A word of the finalize sponge's own 91-element tape. -/
def T_FINTAPE : Nat := 12

-- ⚑ `FIN_W_CIP` / `FIN_W_B` / `FIN_W_DIGEST` / `FIN_W_XI` / `FIN_W_CHAL` are in
-- `KimchiWrapMainField` since 2026-08-06, for the same reason `finBlockVal` is: §21 reads
-- `FIN_W_CHAL + k` and §21 is defined two thousand lines above this rung.

/-- `evals.ft_eval1` — the real Wrap proof's, entry `FIN_EV_FT` of the ζω column
(`MinaRealBlockGate.FT1`). A `Req.Evals` witness upstream (`wrap_main.ml:262-268`), and a NAMED
FIXTURE here until 2026-08-06 for the same reason §19's evaluation columns were. -/
def finFtEval1Val (_p : Nat) : Nat := finEvW.getD FIN_EV_FT 0
/-- `evals.public_input.1` — `p(ζω)`, the same proof's. §19 witnessed only `p(ζ)` because `ft_eval0`
is the only consumer it had; the finalize sponge absorbs both. -/
def finPZetaWVal (_p : Nat) : Nat := finEvW.getD FIN_EV_PUB 0

/-- Instance `p`'s challenge-digest sponge: a FRESH Fq sponge over the `WH_MLMB · WH_ROUNDS`
flattened old bulletproof challenges, closed by one `Sponge.squeeze_field`. `bt` is out of range so
no word is bent. -/
def finChalSpongeOf (base : Nat) (cs : List Nat) : SpAcc :=
  runSpongeQ base (cs.map (fun w => Ev.abs T_FINOLD w) ++ [Ev.sq .full]) (cs.length + 1) 0

def finChalSponge (base p : Nat) : SpAcc := finChalSpongeOf base (whOldChals p)

/-- `Evals.to_absorption_sequence` — the 43 columns at ζ and ζω INTERLEAVED. ⚑ `z(ζω)` is the
block's OWN evaluation since `finZW0`'s deletion (see §19 above): the sponge absorbs §19's own cells
because those cells now ARE the block's, not because a solve was applied to make them agree. -/
def finEvalTape (p : Nat) : List Nat :=
  (List.range FIN_NCOLS).flatMap (fun k => [ finColVal p k 0, finColVal p k 1 ])

/-- **THE 91-ELEMENT TAPE** (`wrap_verifier.ml:844-891`), in upstream's own order. -/
def finSpTape (p cd : Nat) : List Nat :=
  [ finBlockVal p FIN_W_DIGEST, cd, finFtEval1Val p, finPZetaVal p, finPZetaWVal p ]
  ++ finEvalTape p

/-- …and the sponge over it, closed by the TWO squeezes ξ′ and r′. -/
def finFrSpongeOf (base : Nat) (tp : List Nat) : SpAcc :=
  runSpongeQ base (tp.map (fun w => Ev.abs T_FINTAPE w) ++ [Ev.sq .chal, Ev.sq .chal])
    (tp.length + 1) 0

def finFrSponge (base p cd : Nat) : SpAcc :=
  finFrSpongeOf base (finSpTape p cd)

/-- Squeeze `k` of a sponge — the cell it is read out of, and its value. -/
def finSpSq (a : SpAcc) (k : Nat) : PVar × Nat := (chalSqueezes a).getD k (PVAR_NOWHERE, 0)

/-- The cells §20's program reads. Every one is a variable some row of the assembly defines. -/
structure FinSpWire where
  /-- ζ, LIFTED — §19's own chain cell. -/
  zeta : PVar
  /-- ξ, LIFTED. -/
  xiF : PVar
  /-- r, LIFTED. -/
  rF : PVar
  /-- ξ′ — the RAW 128-bit challenge, i.e. the low half of the first squeeze. -/
  xiRaw : PVar
  /-- the fifteen LIFTED bulletproof challenges (`compute_challenges`). -/
  u : Nat → PVar
  /-- old accumulator `i`'s challenge `k` — the challenge-digest sponge's OWN absorb cell. -/
  old : Nat → Nat → PVar
  /-- column `k` at ζ / at ζω — §19's `Req.Evals` cells. -/
  ez : Nat → PVar
  ew : Nat → PVar
  pZeta : PVar
  pZetaW : PVar
  ftEval1 : PVar
  /-- ⚑ §19's OWN `ft_eval0` slot, read as an input. -/
  ftEval0 : PVar
  /-- …and §19's `plonk_checks_passed` bit, the fourth leg of `Boolean.all`. -/
  permOk : PVar
  cipStmt : PVar
  bStmt : PVar
  xiStmt : PVar
  shouldFin : PVar
  deriving Inhabited

/-- What the program bakes in, and the three `Field.equal` witnesses its own rows CHECK. -/
structure FinSpCfg where
  omega : Nat
  shift2 : Nat
  /-- `Backend.Tock.Rounds.n` — the finalized WRAP proof's IPA round count. -/
  rounds : Nat
  /-- how many old accumulators the block carries. -/
  vecs : Nat
  eqInv : List Nat
  eqBit : List Nat
  deriving Repr, Inhabited

structure FinSpSlots where
  bAct : Nat
  bUsed : Nat
  cipAct : Nat
  cipUsed : Nat
  dXi : Nat
  dB : Nat
  dCip : Nat
  xc : Nat
  bc : Nat
  cc : Nat
  finalized : Nat
  out : Nat
  deriving Repr, Inhabited

/-- `challenge_polynomial cs x = ∏ₖ (1 + cₖ · x^{2^{n−1−k}})` (`wrap_verifier.ml:14-35`). One
squaring chain, shared by every factor. -/
def fnChalPoly (one : Nat) (cs : List Nat) (x : Nat) : FM Nat := do
  let n := cs.length
  let ps ← (List.range (n - 1)).foldlM (fun acc _ => do
      let y ← fnMul (acc.getLastD x) (acc.getLastD x); pure (acc ++ [y])) [x]
  (List.range n).foldlM (fun acc k => do
      let t ← fnMul (cs.getD k 0) (ps.getD (n - 1 - k) 0)
      let f ← fnAdd one t
      fnMul acc f) one

/-- `Pcs_batch.combine_split_evaluations` (`pickles_types/pcs_batch.ml:69-83`) — a Horner fold in ξ
with the FIRST entry at ξ⁰. ⚑ The direction is MEASURED against block 539508, not read off the
constructor's name. -/
def fnHorner (xi : Nat) (vs : List Nat) : FM Nat :=
  match vs.reverse with
  | [] => fnLit 0
  | v :: rest => rest.foldlM (fun acc x => do let m ← fnMul acc xi; fnAdd x m) v

/-- **The sponge half's straight-line program**, `wrap_verifier.ml:895-1026` line by line. -/
def finSpBuild (W : FinSpWire) (C : FinSpCfg) : FM FinSpSlots := do
  let zero ← fnLit 0
  let one ← fnLit 1
  let sh2 ← fnLit C.shift2
  let om ← fnLit C.omega
  let zeta ← fnInp W.zeta
  -- `zetaw = domain#generator · ζ`, ONE binding, exactly as `:934` binds it once upstream.
  let zetaw ← fnMul om zeta
  let xiF ← fnInp W.xiF
  let rF ← fnInp W.rF
  -- ── `b_correct` (`:1015-1026`) ────────────────────────────────────────────────────────────
  let us ← (List.range C.rounds).foldlM (fun acc k => do
      let v ← fnInp (W.u k); pure (acc ++ [v])) []
  let bZ ← fnChalPoly one us zeta
  let bW ← fnChalPoly one us zetaw
  let rbw ← fnMul rF bW
  let bAct ← fnAdd bZ rbw
  let bStmt ← fnInp W.bStmt
  let bUsed ← fnAdd bStmt sh2
  -- ── the old accumulators' challenge polynomials — the `sg_olds` entries of the fold ────────
  let olds ← (List.range C.vecs).foldlM (fun acc i => do
      let cs ← (List.range C.rounds).foldlM (fun a k => do
          let v ← fnInp (W.old i k); pure (a ++ [v])) []
      pure (acc ++ [cs])) []
  let sgZ ← olds.foldlM (fun acc cs => do let z ← fnChalPoly one cs zeta; pure (acc ++ [z])) []
  let sgW ← olds.foldlM (fun acc cs => do let z ← fnChalPoly one cs zetaw; pure (acc ++ [z])) []
  -- ── `combined_inner_product_correct` (`:951-1009`) ────────────────────────────────────────
  let ez ← (List.range FIN_NCOLS).foldlM (fun acc k => do
      let v ← fnInp (W.ez k); pure (acc ++ [v])) []
  let ew ← (List.range FIN_NCOLS).foldlM (fun acc k => do
      let v ← fnInp (W.ew k); pure (acc ++ [v])) []
  let pz ← fnInp W.pZeta
  let pzw ← fnInp W.pZetaW
  let ft0 ← fnInp W.ftEval0
  let ft1 ← fnInp W.ftEval1
  let hZ ← fnHorner xiF (sgZ ++ [pz, ft0] ++ ez)
  let hW ← fnHorner xiF (sgW ++ [pzw, ft1] ++ ew)
  let rh ← fnMul rF hW
  let cipAct ← fnAdd hZ rh
  let cipStmt ← fnInp W.cipStmt
  let cipUsed ← fnAdd cipStmt sh2
  -- ── `Field.equal`, the real gadget, three times ───────────────────────────────────────────
  let mkEq : Nat → Nat → Nat → FM (Nat × Nat) := fun i x y => do
    let d ← fnSub x y
    let iv ← fnWit (C.eqInv.getD i 0)
    let bb ← fnWit (C.eqBit.getD i 0)
    let bb2 ← fnMul bb bb
    let _ ← fnAeq bb2 bb
    let pm ← fnMul d iv
    let qq ← fnSub one bb
    let _ ← fnAeq pm qq
    let sZ ← fnMul d bb
    let _ ← fnAeq sZ zero
    pure (d, bb)
  let xiRaw ← fnInp W.xiRaw
  let xiStmt ← fnInp W.xiStmt
  let e0 ← mkEq 0 xiRaw xiStmt
  let e1 ← mkEq 1 bUsed bAct
  let e2 ← mkEq 2 cipUsed cipAct
  -- ── `Boolean.all [xi_correct; b_correct; cip_correct; plonk_checks_passed]` (`:1141-1147`) ─
  let pk ← fnInp W.permOk
  let f1 ← fnMul e0.2 e1.2
  let f2 ← fnMul f1 e2.2
  let fin ← fnMul f2 pk
  -- ⚑ …and `Boolean.Assert.any [finalized; not should_finalize]` over the FOUR-leg `finalized`.
  -- §19's own row asserts the same thing over `plonk_checks_passed` alone; it is implied by this
  -- one and is kept because a rung IS the rung below it plus its own rows.
  let sf ← fnInp W.shouldFin
  let nfin ← fnSub one fin
  let out ← fnMul nfin sf
  let _ ← fnAeq out zero
  pure { bAct := bAct, bUsed := bUsed, cipAct := cipAct, cipUsed := cipUsed
       , dXi := e0.1, dB := e1.1, dCip := e2.1
       , xc := e0.2, bc := e1.2, cc := e2.2, finalized := fin, out := out }

structure FinSpProg where
  prog : Array FOp
  slots : FinSpSlots
  deriving Repr, Inhabited

def finSpProgOf (W : FinSpWire) (C : FinSpCfg) : FinSpProg :=
  let r := (finSpBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-! ### §20a — the variable space. -/

/-- Fifteen `compute_challenges` lifts, then ξ, ξ's high part, r, r's high part. -/
def FINSP_CHAINS : Nat := WH_ROUNDS + 4
def FINSP_XI : Nat := WH_ROUNDS
def FINSP_XIHI : Nat := WH_ROUNDS + 1
def FINSP_R : Nat := WH_ROUNDS + 2
def FINSP_RHI : Nat := WH_ROUNDS + 3

/-- Everything one instance of the sponge half evaluates, ONCE. -/
structure FinSpData where
  base : Nat
  cs : SpAcc
  fs : SpAcc
  fp : FinSpProg
  vals : Array Nat
  deriving Inhabited

def finSpFsBase (d : FinSpData) : Nat := d.base + d.cs.next
def finSpChBase (d : FinSpData) : Nat := finSpFsBase d + d.fs.next
def finSpWireBase (s : WrapShape) (d : FinSpData) : Nat :=
  finSpChBase d + FINSP_CHAINS * chainStride s
def finSpProgBase (s : WrapShape) (d : FinSpData) : Nat := finSpWireBase s d + 2
def finSpSize (s : WrapShape) (d : FinSpData) : Nat :=
  finSpProgBase s d + d.fp.prog.size - d.base
def finSpChain (s : WrapShape) (d : FinSpData) (c : Nat) : ChainVars :=
  chainVars s (finSpChBase d) c
/-- `ft_eval1`'s cell and `p(ζω)`'s — the two `Req.Evals` witnesses §19 had no consumer for. -/
def finSpFt1V (s : WrapShape) (d : FinSpData) : PVar := .external (finSpWireBase s d)
def finSpPzwV (s : WrapShape) (d : FinSpData) : PVar := .external (finSpWireBase s d + 1)
/-- Old accumulator `i`'s challenge `k`, as the challenge-digest sponge's own absorb cell. -/
def finSpOldV (d : FinSpData) (i k : Nat) : PVar :=
  ((d.cs.evs.getD (WH_ROUNDS * i + k) default).wordV)

/-- The region above §19's programs. ⚠ It is `WrapData`-dependent and not shape-dependent, because
`finStride` is instance 0's compiled program size and nothing but the emitter knows it. -/
def baseFinSp (t : WrapData) (fa : List FinData) : Nat :=
  finProgBase t.sh t.sp + t.sh.maxPrevs * finStride fa

/-- §19's `ft_eval0` slot, as a VARIABLE and as a VALUE. -/
def finFtEval0V (t : WrapData) (fa : List FinData) (p : Nat) : PVar :=
  let d := fa.getD p default
  fnVarAt (finProgAt t.sh t.sp fa p) d.fp.prog d.fp.slots.ftEval0
def finFtEval0N (fa : List FinData) (p : Nat) : Nat :=
  let d := fa.getD p default
  d.vals.getD d.fp.slots.ftEval0 0
/-- …and its `plonk_checks_passed` bit. -/
def finPermOkV (t : WrapData) (fa : List FinData) (p : Nat) : PVar :=
  let d := fa.getD p default
  fnVarAt (finProgAt t.sh t.sp fa p) d.fp.prog d.fp.slots.permOk
def finPermOkN (fa : List FinData) (p : Nat) : Nat :=
  let d := fa.getD p default
  d.vals.getD d.fp.slots.permOk 0

/-- Instance `p`'s wire. -/
def finSpWireOf (t : WrapData) (fa : List FinData) (d : FinSpData) (p : Nat) : FinSpWire :=
  let s := t.sh
  let sp := t.sp
  { zeta := (finChainVars s sp p 1).lift
  , xiF := (finSpChain s d FINSP_XI).lift
  , rF := (finSpChain s d FINSP_R).lift
  , xiRaw := (finSpChain s d FINSP_XI).n s.emsRows
  , u := fun k => (finSpChain s d k).lift
  , old := fun i k => finSpOldV d i k
  , ez := fun k => finEvVar s sp p k 0
  , ew := fun k => finEvVar s sp p k 1
  , pZeta := finPZetaVar s sp p
  , pZetaW := finSpPzwV s d
  , ftEval1 := finSpFt1V s d
  , ftEval0 := finFtEval0V t fa p
  , permOk := finPermOkV t fa p
  , cipStmt := prevW s sp (finBlockWord p FIN_W_CIP)
  , bStmt := prevW s sp (finBlockWord p FIN_W_B)
  , xiStmt := prevW s sp (finBlockWord p FIN_W_XI)
  , shouldFin := prevW s sp (finBlockWord p PREV_SHOULD_FINALIZE) }

/-- Instance `p`'s `.inp` lookup — every cell the program aliases, at its value. -/
def finSpInputEnv (t : WrapData) (fa : List FinData) (d : FinSpData) (p : Nat) : VarEnv :=
  let s := t.sh
  let sp := t.sp
  let sq0 := finSpSq d.fs 0
  let sq1 := finSpSq d.fs 1
  let xiLo := sq0.2 % 2 ^ CHAL_BITS s
  let rLo := sq1.2 % 2 ^ CHAL_BITS s
  [ ((finChainVars s sp p 1).lift, (liftValQ s (finBlockVal p 9) : Int))
  , ((finSpChain s d FINSP_XI).lift, (liftValQ s xiLo : Int))
  , ((finSpChain s d FINSP_R).lift, (liftValQ s rLo : Int))
  , ((finSpChain s d FINSP_XI).n s.emsRows, (xiLo : Int))
  , (finPZetaVar s sp p, (finPZetaVal p : Int))
  , (finSpPzwV s d, (finPZetaWVal p : Int))
  , (finSpFt1V s d, (finFtEval1Val p : Int))
  , (finFtEval0V t fa p, (finFtEval0N fa p : Int))
  , (finPermOkV t fa p, (finPermOkN fa p : Int))
  , (prevW s sp (finBlockWord p FIN_W_CIP), (finBlockVal p FIN_W_CIP : Int))
  , (prevW s sp (finBlockWord p FIN_W_B), (finBlockVal p FIN_W_B : Int))
  , (prevW s sp (finBlockWord p FIN_W_XI), (finBlockVal p FIN_W_XI : Int))
  , (prevW s sp (finBlockWord p PREV_SHOULD_FINALIZE),
     (finBlockVal p PREV_SHOULD_FINALIZE : Int)) ]
  ++ (List.range WH_ROUNDS).map (fun k =>
      ((finSpChain s d k).lift, (liftValQ s (finBlockVal p (FIN_W_CHAL + k)) : Int)))
  ++ (List.range WH_MLMB).flatMap (fun i =>
      (List.range WH_ROUNDS).map (fun k =>
        (finSpOldV d i k, (whOldChal p (WH_ROUNDS * i + k) : Int))))
  ++ (List.range FIN_NCOLS).flatMap (fun k =>
      [ (finEvVar s sp p k 0, (finColVal p k 0 : Int))
      , (finEvVar s sp p k 1, (finColVal p k 1 : Int)) ])

/-- The config, at a PLACEHOLDER `Field.equal` witness. -/
def finSpCfg0 : FinSpCfg :=
  { omega := FIN_OMEGA, shift2 := FIN_SHIFT2, rounds := WH_ROUNDS, vecs := WH_MLMB
  , eqInv := [0, 0, 0], eqBit := [1, 1, 1] }

/-- ⚑ **THE THREE `Field.equal` WITNESSES ARE COMPUTED FROM THE GADGET'S OWN INPUTS**, exactly as
§19's `runFin` computes its one: the program is built once at a placeholder pair, its `d` slots are
read, and the honest `(inv, bit)` follows from the ACTUAL difference — `(0, 1)` where they agree and
`(d⁻¹, 0)` where they do not. Asserting the answer instead is what made the first `w10_finalize`
emission unprovable while every σ-pin stayed green. -/
def runFinSp (t : WrapData) (fa : List FinData) (base p : Nat) : FinSpData :=
  let cs := finChalSponge base p
  let fs := finFrSponge (base + cs.next) p (whDigestVal cs)
  let d0 : FinSpData := { base := base, cs := cs, fs := fs, fp := default, vals := #[] }
  let W := finSpWireOf t fa d0 p
  let lk := envLookupAt (envIndex (finSpInputEnv t fa d0 p))
  let probe := finSpProgOf W finSpCfg0
  let pv := fnEval lk probe.prog
  let ds := [ pv.getD probe.slots.dXi 0, pv.getD probe.slots.dB 0, pv.getD probe.slots.dCip 0 ]
  let cfg : FinSpCfg :=
    { finSpCfg0 with
      eqInv := ds.map (fun x => if x == 0 then 0 else qInv x)
      eqBit := ds.map (fun x => if x == 0 then 1 else 0) }
  let fp := finSpProgOf W cfg
  { base := base, cs := cs, fs := fs, fp := fp, vals := fnEval lk fp.prog }

/-- Every instance's sponge half, built ONCE and stacked — the regions are data-sized, so the fold
threads the base rather than a shape stride. -/
def finSpAll (t : WrapData) (fa : List FinData) : List FinSpData :=
  (List.range t.sh.maxPrevs).foldl
    (fun acc p =>
      let b := match acc.getLast? with
               | none => baseFinSp t fa
               | some d => d.base + finSpSize t.sh d
      acc ++ [runFinSp t fa b p])
    []

/-! ### §20b — the rows. -/

/-- **W-FINSPONGE's ROWS.** Per instance: the two sponges, the ties that make their absorb cells the
assembly's own, the nineteen `to_field_checked` chains, the program, and one σ-only probe. -/
def finSpRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let cb := baseCh s sp
  let fa := finAll t
  let da := finSpAll t fa
  (List.range s.maxPrevs).flatMap (fun p =>
    let d := da.getD p default
    let sq0 := finSpSq d.fs 0
    let sq1 := finSpSq d.fs 1
    let xiLo := sq0.2 % 2 ^ CHAL_BITS s
    let xiHi := sq0.2 / 2 ^ CHAL_BITS s
    let rLo := sq1.2 % 2 ^ CHAL_BITS s
    let rHi := sq1.2 / 2 ^ CHAL_BITS s
    let pB := finSpProgBase s d
    let V := fnVarAt pB d.fp.prog
    -- ⚑ the absorbed word of tape position `j`, as the sponge's OWN cell.
    let tv : Nat → PVar := fun j => (d.fs.evs.getD j default).wordV
    -- (1) the nested challenge-digest sponge and (2) the finalize sponge.
    transcriptRowsQ d.base d.cs wired
    ++ transcriptRowsQ (finSpFsBase d) d.fs wired
    -- (3) the ties: every tape position that has a cell elsewhere in the assembly IS that cell.
    ++ packHalves
        ([ ([some (tv 0), some (prevW s sp (finBlockWord p FIN_W_DIGEST)), none], cEq)
         , ([some (tv 1), some (whDigestVar d.cs), none], cEq)
         , ([some (tv 2), some (finSpFt1V s d), none], cEq)
         , ([some (tv 3), some (finPZetaVar s sp p), none], cEq)
         , ([some (tv 4), some (finSpPzwV s d), none], cEq) ]
         ++ (List.range FIN_NCOLS).flatMap (fun k =>
              [ ([some (tv (5 + 2 * k)), some (finEvVar s sp p k 0), none], cEq)
              , ([some (tv (6 + 2 * k)), some (finEvVar s sp p k 1), none], cEq) ]))
    -- (4) `compute_challenges` — fifteen 128-bit lifts of the block's own words.
    ++ (List.range WH_ROUNDS).flatMap (fun k =>
        tfcRowsQ s cb (finSpChain s d k) (prevW s sp (finBlockWord p (FIN_W_CHAL + k))) false
          (finBlockVal p (FIN_W_CHAL + k)) wired)
    -- (5) ξ and r: `lowest_128_bits` with BOTH halves range-checked, then the lift.
    ++ tfcRowsQ s cb (finSpChain s d FINSP_XI) sq0.1 true xiLo wired
    ++ tfcRowsQ s cb (finSpChain s d FINSP_XIHI) (finSpChain s d FINSP_XI).hi false xiHi wired
    ++ tfcRowsQ s cb (finSpChain s d FINSP_R) sq1.1 true rLo wired
    ++ tfcRowsQ s cb (finSpChain s d FINSP_RHI) (finSpChain s d FINSP_R).hi false rHi wired
    -- (6) the three legs and `Boolean.all`.
    ++ fnRows pB d.fp.prog
    ++ [ probeRow wired (V d.fp.slots.cipAct) (V d.fp.slots.bAct) ])

/-- W-FINSPONGE's variable environment. -/
def finSpEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let fa := finAll t
  let da := finSpAll t fa
  (List.range s.maxPrevs).flatMap (fun p =>
    let d := da.getD p default
    let sq0 := finSpSq d.fs 0
    let sq1 := finSpSq d.fs 1
    spongeEnv d.base d.cs
    ++ spongeEnv (finSpFsBase d) d.fs
    ++ (List.range WH_ROUNDS).flatMap (fun k =>
        chainEnv s (finSpChain s d k) (finBlockVal p (FIN_W_CHAL + k)) 0)
    ++ chainEnv s (finSpChain s d FINSP_XI) (sq0.2 % 2 ^ CHAL_BITS s) (sq0.2 / 2 ^ CHAL_BITS s)
    ++ chainEnv s (finSpChain s d FINSP_XIHI) (sq0.2 / 2 ^ CHAL_BITS s) 0
    ++ chainEnv s (finSpChain s d FINSP_R) (sq1.2 % 2 ^ CHAL_BITS s) (sq1.2 / 2 ^ CHAL_BITS s)
    ++ chainEnv s (finSpChain s d FINSP_RHI) (sq1.2 / 2 ^ CHAL_BITS s) 0
    ++ [ (finSpFt1V s d, (finFtEval1Val p : Int))
       , (finSpPzwV s d, (finPZetaWVal p : Int)) ]
    ++ fnEnvOf (finSpProgBase s d) d.fp.prog d.vals)

/-- ⚑ **THE THREE DEFERRED WORDS, DERIVED** — `combined_inner_product`, `b` and `xi` of the block
that claims `should_finalize`, as this rung's own program computes them. `EmitWrapMainJson` and
`fin_deferred_words_are_the_derivation` both read THIS function, so the memo in
`KimchiWrapMainField` cannot drift away from the emission. -/
def finSpDerivedWords (t : WrapData) : Nat × Nat × Nat :=
  let fa := finAll t
  let da := finSpAll t fa
  let d := da.getD FIN_LIVE_BLOCK default
  ( qSub (d.vals.getD d.fp.slots.cipAct 0) FIN_SHIFT2
  , qSub (d.vals.getD d.fp.slots.bAct 0) FIN_SHIFT2
  , (finSpSq d.fs 0).2 % 2 ^ CHAL_BITS t.sh )

/-! ## §7 — rows, environment, rungs. -/

inductive Rung where
  | transcript | challenges | branch | bind | key | xhat | split | ftcomm | prev | finalize
  | finsponge | wraphack | close | combine | bullet
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "w1_transcript" | .challenges => "w2_challenges"
  | .branch => "w3_branch" | .bind => "w4_bind" | .key => "w5_key"
  | .xhat => "w6_xhat" | .split => "w7_split" | .ftcomm => "w8_ftcomm"
  | .prev => "w9_prev" | .finalize => "w10_finalize"
  | .finsponge => "w11_finsponge"
  | .wraphack => "w11_wraphack" | .close => "w12_close"
  | .combine => "w10_combine" | .bullet => "w11_bullet"

/-- **THE ROW SCHEDULE**, rung by rung, in the order `wrap_main` runs it. Every sub-circuit's row-set
function is REACHED FROM HERE — a row-set that drops out of this `match` is a red in §12b, not a
silence.

⚑⚑ **THIS `match` USED TO BIND ALL EIGHT FAMILIES WITH A `let` ABOVE IT, AND LEAN IS STRICT.**
MEASURED 2026-08-03, cold `lean --run` at `shapeWrap` (`KimchiWrapProverChoice`'s header carries the
instrument): `rungRows tWrap .key true` cost **1 014 740 ms** — 16 min 55 s — for **1 977 rows** whose
five families cost **115 ms** between them (`transcriptRowsQ` 19 + `challengeRowsQ` 9 + `branchRows` 0
+ `closingRows` 8 + `keyRows` 79). The other 99.99% was `xhatRows` and `splitRows` — §15's x_hat MSM
ladders and the split rows — **computed and discarded**, because the compiler does not sink a `let`
into the branch that uses it. `.transcript` paid it too. -/
def rungOwn (t : WrapData) (wired : Bool) : Rung → List WRow
  | .transcript => transcriptRowsQ (baseSp t.sh) t.sp wired
  | .challenges => challengeRowsQ t wired
  | .branch => branchRows t.sh (baseBr t.sh t.sp) t.br wired
  | .bind => closingRows t
  | .key => keyRows t wired
  | .xhat => xhatRows t wired
  | .split => splitRows t wired
  | .ftcomm => ftcRows t wired
  | .prev => prevRows t wired
  | .wraphack => whRows t wired
  | .close => closeRows t wired
  | .finalize => finRows t wired
  | .finsponge => finSpRows t wired
  | .combine => combRows t wired
  | .bullet => bulletRows t wired

/-- The rungs at or below `k`, in schedule order. ⚑ "Every rung is a superset of the one below" is
now the SHAPE of the definition rather than a fact about eight hand-written branches. -/
def rungsUpto : Rung → List Rung
  | .transcript => [.transcript]
  | .challenges => [.transcript, .challenges]
  | .branch     => [.transcript, .challenges, .branch]
  | .bind       => [.transcript, .challenges, .branch, .bind]
  | .key        => [.transcript, .challenges, .branch, .bind, .key]
  | .xhat       => [.transcript, .challenges, .branch, .bind, .key, .xhat]
  | .split      => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split]
  | .ftcomm     => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm]
  | .prev       => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev]
  | .wraphack   => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .wraphack]
  -- ⚑⚑ `.combine` and `.bullet` JOINED 2026-08-05. `w12_close` asserts `bulletproof_success`, and
  -- `bulletproof_success` IS `equal_g`'s output — a rung that asserts a verdict without the rows
  -- that compute it asserts a free witness. This is the FIRST rung to hold two block owners
  -- (`.wraphack` and `.combine`); `rungRegions .close` declares both, which is the precondition
  -- §22 measured and §17b now meets.
  | .close      => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .combine, .bullet, .wraphack, .close]
  | .finalize   => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .finalize]
  | .finsponge  => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .finalize, .finsponge]
  | .combine    => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .combine]
  | .bullet     => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .combine, .bullet]

/-- Every rung, so the pins below can quantify over the LADDER rather than over the two or three
instances someone happened to write down. `rungs_enumerates_the_type` is the pin that this list is
the whole type — a constructor added to `Rung` and forgotten here would otherwise make every bounded
∀ below quietly weaker. -/
def ALL_RUNGS : List Rung :=
  [ .transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev
  , .finalize, .finsponge, .wraphack, .close, .combine, .bullet ]

/-- ⚑ **THE THREE SUB-CIRCUITS THAT ONCE STARTED AT THE SAME ADDRESS.** `baseWh` (§21a), `baseFin`
(§19e) and `baseComb` (§23a) were EACH literally `baseFtc s sp + nFtcVars s sp` until 2026-08-05,
sound only while no rung's `rungsUpto` contained two of them. §17b stacks them on caps, so this list
is no longer what makes the layout sound — it names the three block OWNERS, one per block, and
`no_rung_holds_two_colliding_regions` still measures the ladder against it. -/
def COLLIDING_REGION_OWNERS : List Rung := [ .wraphack, .finalize, .combine ]

/-- ⚑ **THE BLOCKS RUNG `k` MAY ALLOCATE IN** — each as a base and a CAP (§17b). A rung at or below
`w9_prev` owns none of the three and everything it touches is below `baseWh`, which is what the empty
list says: for those rungs the whole three-block space is out of bounds.

⚑⚑ **THIS RETURNS A LIST SINCE 2026-08-05, AND THAT IS WHAT LETS A RUNG OWN TWO BLOCKS.** It returned
ONE `(base, cap)`, which was sound only while no `rungsUpto` held two block owners — and that was in
turn the reason `w12_close` could not contain `.bullet`, so `bpSuccessVar` stayed a fresh cell
`closeEnv` sets to 1 instead of W-BULLET's own verdict. The generalization is NOT a relaxation: what
made a single block safe was `regionEscapeIn`'s membership test, and what makes a list of blocks safe
is the same test against each of them, over blocks §17b already proves PAIRWISE DISJOINT for every
`x` (`no_rung_holds_two_colliding_regions`). A rung that reaches into a block it does NOT declare is
still a refusal, which is the aliasing this layout exists to catch. -/
def rungRegions (s : WrapShape) (sp : SpAcc) : Rung → List (Nat × Nat)
  | .wraphack              => [(baseWh s sp, WH_REGION_CAP s)]
  | .finalize | .finsponge => [(baseFin s sp, FIN_REGION_CAP s)]
  | .combine               => [(baseComb s sp, COMB_REGION_CAP s)]
  -- ⚑ `w12_close` holds W-WRAPHACK's block (its own cell is that block's last, §22) AND — since the
  -- `bpSuccessVar` tie — W-COMBINE's, because `.bullet` is under `.close` and W-BULLET allocates in
  -- the `baseComb` block. Two DECLARED blocks, disjoint by §17b, and the escape check still bites on
  -- anything outside both.
  | .close                 => [(baseWh s sp, WH_REGION_CAP s), (baseComb s sp, COMB_REGION_CAP s)]
  | .bullet                => [(baseComb s sp, COMB_REGION_CAP s)]
  | _                      => []

/-- ⚑⚑ **THE CAPS' FAIL-CLOSED LEG — THE WHOLE REASON A CAP IS HONEST RATHER THAN A GUESS.** The
first external id rung `k`'s gates reference that is neither below the three blocks nor inside `k`'s
OWN block; `none` is the healthy case and `EmitWrapMainJson` STOPS on a `some`.

⚠ **IT READS THE EMITTED GATES**, so it is a second and INDEPENDENT source against §17b's shape
arithmetic rather than a pin against the caps' own definition. A block that outgrew its cap and a
rung that reached into a sibling's block are both a `some i` here, and the second is the point: an
escape DOWNWARD is the aliasing this layout exists to refuse, and a max-index check would not see it.

⚠ `k`'s gates are the gates of the WHOLE rung — every rung at or below it — which is what makes the
lower bound `baseWh s sp` rather than `k`'s own base. A rung whose `rungsUpto` holds two block owners
must DECLARE both in `rungRegions`; one it does not declare is still a `some i`, which is the correct
answer and the reason the list form is not a weakening.

⚑ It is stated over an ARBITRARY `(wall, bs)` and instantiated, so the red control is expressible:
`region_escape_bites_on_the_emitted_gates` runs the SAME function over the SAME emitted gates at a
zero-width block and at a sibling's block, and gets a `some` both times. A refusal nothing has ever
been shown to fire is not a gate. -/
def regionEscapeIn (wall b n : Nat) (gs : List PGate) : Option Nat :=
  (externalRefs gs).find? (fun i => !(i < wall || (b ≤ i && i < b + n)))

/-- …and the list form: an id is legal iff it is below the wall or inside ONE OF the declared blocks.
⚑ At a single-block rung this is `regionEscapeIn` exactly (`region_escape_list_is_the_single_block_one`),
so nothing below `w12_close` changed meaning. -/
def regionEscapeInAny (wall : Nat) (bs : List (Nat × Nat)) (gs : List PGate) : Option Nat :=
  (externalRefs gs).find? (fun i =>
    !(i < wall || bs.any (fun bn => bn.1 ≤ i && i < bn.1 + bn.2)))

def regionEscape (s : WrapShape) (sp : SpAcc) (k : Rung) (gs : List PGate) : Option Nat :=
  regionEscapeInAny (baseWh s sp) (rungRegions s sp k) gs


/-- Rung `k`'s rows: the own-rows of every rung at or below it, concatenated in schedule order.

⚑ **THE EMITTED LIST IS THE SAME TERM IT ALWAYS WAS.** `foldl (· ++ ·) []` over a literal list is
left-nested exactly as `a ++ b ++ c` is, and `[] ++ a` reduces to `a` definitionally — so
`rungRows t .key wired` is `(((a ++ b) ++ c) ++ d) ++ e` on the nose, and `rungRows_is_a_ladder`
below is `rfl`. What changed is that the `foldl` walks only the rungs `k` names, so a rung evaluates
only the families it returns. -/
def rungRows (t : WrapData) (k : Rung) (wired : Bool) : List WRow :=
  (rungsUpto k).foldl (fun acc j => acc ++ rungOwn t wired j) []

/-- ⚑ **THE HOIST IS THE THING IT HOISTS.** Each rung is the rung below it plus its own row-set —
general over every `WrapData` and every `wired`, by `rfl`, no shape instance and no evaluated guard.
§12b's four length pins are instances of this plus `List.length_append`. -/
theorem rungRows_is_a_ladder (t : WrapData) (wired : Bool) :
    rungRows t .challenges wired = rungRows t .transcript wired ++ rungOwn t wired .challenges
    ∧ rungRows t .branch wired = rungRows t .challenges wired ++ rungOwn t wired .branch
    ∧ rungRows t .bind wired = rungRows t .branch wired ++ rungOwn t wired .bind
    ∧ rungRows t .key wired = rungRows t .bind wired ++ rungOwn t wired .key
    ∧ rungRows t .xhat wired = rungRows t .key wired ++ rungOwn t wired .xhat
    ∧ rungRows t .split wired = rungRows t .xhat wired ++ rungOwn t wired .split
    ∧ rungRows t .ftcomm wired = rungRows t .split wired ++ rungOwn t wired .ftcomm
    ∧ rungRows t .prev wired = rungRows t .ftcomm wired ++ rungOwn t wired .prev
    ∧ rungRows t .wraphack wired = rungRows t .prev wired ++ rungOwn t wired .wraphack :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **`w12_close` HANGS OFF `w11_bullet`, NOT OFF `w11_wraphack`, SINCE 2026-08-05** — which is
what "`.bullet` is under `.close`" means as a fact about the emitted row list rather than as a
sentence. It is `.bullet`'s rows, then W-WRAPHACK's own, then W-CLOSE's own, in `wrap_main`'s order:
`incrementally_verify_proof` (`:412`), `hash_messages_for_next_wrap_proof` (`:421-431`), then
`Boolean.Assert.is_true bulletproof_success`. Still `rfl`, still general over every `WrapData` and
every polarity — a rung that quietly dropped W-COMBINE's or W-BULLET's rows would red here and not
in a shape instance. -/
theorem rungRows_close_is_a_ladder (t : WrapData) (wired : Bool) :
    rungRows t .close wired
      = rungRows t .bullet wired ++ rungOwn t wired .wraphack ++ rungOwn t wired .close := rfl

/-- …and `w10_finalize` is `w9_prev` plus W-FINALIZE's own row-set, by the same `rfl`. ⚑ Stated
separately rather than as an eleventh conjunct above because `.finalize` and `.wraphack` both hang
off `.prev` — `wrap_main.ml` runs `finalize_other_proof` (`:329`) before
`hash_messages_for_next_wrap_proof` (`:340`), and neither reads the other's rows. -/
theorem rungRows_finalize_is_a_ladder (t : WrapData) (wired : Bool) :
    rungRows t .finalize wired = rungRows t .prev wired ++ rungOwn t wired .finalize := rfl

/-- …and its length, likewise. -/
theorem rungRows_finalize_length (t : WrapData) (wired : Bool) :
    (rungRows t .finalize wired).length
      = (rungRows t .prev wired).length + (rungOwn t wired .finalize).length := by
  simp [rungRows_finalize_is_a_ladder t wired]

/-- …and the length of each rung is the length of the one below plus its own — general, so §12b's
guards are instances rather than the statement. -/
theorem rungRows_lengths_are_the_sum_of_their_parts (t : WrapData) (wired : Bool) :
    (rungRows t .challenges wired).length
      = (rungRows t .transcript wired).length + (rungOwn t wired .challenges).length
    ∧ (rungRows t .branch wired).length
      = (rungRows t .challenges wired).length + (rungOwn t wired .branch).length
    ∧ (rungRows t .bind wired).length
      = (rungRows t .branch wired).length + (rungOwn t wired .bind).length
    ∧ (rungRows t .key wired).length
      = (rungRows t .bind wired).length + (rungOwn t wired .key).length
    ∧ (rungRows t .xhat wired).length
      = (rungRows t .key wired).length + (rungOwn t wired .xhat).length
    ∧ (rungRows t .split wired).length
      = (rungRows t .xhat wired).length + (rungOwn t wired .split).length
    ∧ (rungRows t .ftcomm wired).length
      = (rungRows t .split wired).length + (rungOwn t wired .ftcomm).length
    ∧ (rungRows t .prev wired).length
      = (rungRows t .ftcomm wired).length + (rungOwn t wired .prev).length
    ∧ (rungRows t .wraphack wired).length
      = (rungRows t .prev wired).length + (rungOwn t wired .wraphack).length
    ∧ (rungRows t .close wired).length
      = (rungRows t .bullet wired).length + (rungOwn t wired .wraphack).length
        + (rungOwn t wired .close).length := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := rungRows_is_a_ladder t wired
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h4]
  · simp [h5]
  · simp [h6]
  · simp [h7]
  · simp [h8]
  · simp [h9]
  · rw [rungRows_close_is_a_ladder t wired]
    simp [List.length_append, Nat.add_assoc]

/-- ⚑ **Rung `k`'s public-input size is MINA'S, or ZERO.** A rung below the closing one has no
public vector at all; every rung from `w4_bind` up declares `WRAP_PRIMARY_LEN = 40` — the width
`Impls.Wrap.input ()` allocates and the width `make_zkapp_verifier_index` hands
`kimchi::verifier::verify` for a side-loaded wrap key.

⚠ **THIS IS NOT PADDING, AND THE DIFFERENCE IS MECHANICAL.** What changes with the rung is not the
WIDTH but which of Mina's slots carry a value this rung DERIVES: `wrapSlotsAt` says which, and
`wrapInertOk` declares the rest to `placeCheckedWith`, which refuses any slot left unread that the
declaration did not name. Widening to 40 with a vector of our own choosing would be exactly the
"6 words + 34 zeros" probe — it establishes plumbing and nothing else. -/
def rungPub (_s : WrapShape) : Rung → Nat
  | .transcript | .challenges | .branch => 0
  | _ => WRAP_PRIMARY_LEN

/-- The variables rung `k` exposes as public words. ⚑ `w9_prev` appends ONE — packed statement word
`PREV_MSG_NEXT_STEP`, the MSM's entry 64 — and no rung below it may, because below `w6_xhat` no row
reads that cell and a public word on an unread cell is a public fixture. -/
def exposedVarsAt (t : WrapData) (k : Rung) : List PVar :=
  let s := t.sh
  let sp := t.sp
  -- ⚑ The three `ft_comm` scales, in `ftcSVal`'s own argument order (`0 = perm`, `1 = ζ^srs_len`,
  -- `2 = ζ^dom`). `wrapSlotsAt` maps them to Mina's 4, 2, 3 — NOT to 2, 3, 4.
  let ftc := [ftcSV s sp 0, ftcSV s sp 1, ftcSV s sp 2]
  let xi := [combXiV s sp]
  let bul := [bullCipV t, bullScalV s sp 0]
  let nextStep := [prevW s sp PREV_MSG_NEXT_STEP]
  let nextWrap := [whDigestVar (whSpongeC t)]
  exposedVars t ++ (match k with
    | .ftcomm => ftc
    | .prev => nextStep ++ ftc
    | .finalize | .finsponge => nextStep ++ ftc
    | .combine => nextStep ++ ftc ++ xi
    | .bullet => nextStep ++ ftc ++ xi ++ bul
    -- ⚑ …and `w11_wraphack` appends slot 11, the closing `hash_messages_for_next_wrap_proof`
    -- squeeze (`wrap_main.ml:421-431`). It does NOT sit above W-COMBINE or W-BULLET, so it carries
    -- the ft_comm trio and neither ξ nor the bulletproof pair.
    | .wraphack => nextStep ++ nextWrap ++ ftc
    | .close => nextStep ++ nextWrap ++ ftc ++ xi ++ bul
    | _ => [])

/-- **`wrapSlotsAt`** — Mina's slot for each of `exposedVarsAt t k`'s words, in that list's order.
The base is `wrapSlots`; the ladder appends slot 12 where W-PREV's own row ties it and slot 11 where
W-WRAPHACK's does. Pointwise with `exposedVarsAt` by construction. -/
def wrapSlotsAt (s : WrapShape) (k : Rung) : List Nat :=
  -- ⚠ POINTWISE WITH `exposedVarsAt`, and the two are matched by hand because `wrapInertOk` is
  -- shape-only while the variables need a `WrapData`. The emitter refuses on a length, range or
  -- collision disagreement (`⚑ SLOT MAP …` in `EmitWrapMainJson`), so a drift here is a REFUSAL to
  -- emit rather than a wrong circuit.
  let ftc := [WRAP_SLOT_PERM, WRAP_SLOT_ZETA_TO_SRS, WRAP_SLOT_ZETA_TO_DOM]
  let xi := [WRAP_SLOT_XI]
  let bul := [WRAP_SLOT_CIP, WRAP_SLOT_B]
  wrapSlots s ++ (match k with
    | .ftcomm => ftc
    | .prev | .finalize | .finsponge => [WRAP_SLOT_MSG_NEXT_STEP] ++ ftc
    | .combine => [WRAP_SLOT_MSG_NEXT_STEP] ++ ftc ++ xi
    | .bullet => [WRAP_SLOT_MSG_NEXT_STEP] ++ ftc ++ xi ++ bul
    | .wraphack => [WRAP_SLOT_MSG_NEXT_STEP, WRAP_SLOT_MSG_NEXT_WRAP] ++ ftc
    | .close => [WRAP_SLOT_MSG_NEXT_STEP, WRAP_SLOT_MSG_NEXT_WRAP] ++ ftc ++ xi ++ bul
    | _ => [])

/-- ⚑ **THE DECLARED UNREAD SET — what this rung says it does NOT derive, and the thing
`placeCheckedWith` checks the emission against.**

Two parts, both DECLARATIONS and neither read off the emitted gates:

  * `WRAP_UNPINNED_SLOTS` — the TEN nothing reads, upstream or here: `Spec.T.Constant` padding and
    the dead lookup `Opt`, which `Spec.packed_typ` ALLOCATES and hands the body a `Cvar.Constant`
    for (`composition_types/spec.ml:312-330`). Tying those to variables would be a public fixture.
  * the slots this rung has not REACHED — whether `WRAP_PINNED_SLOTS` (12 below `w9_prev`, 11 below
    `w11_wraphack`) or `WRAP_PASSTHROUGH_SLOTS` (4/2/3 below `w8_ftcomm`, 9 below `w10_combine`,
    0/1 below `w11_bullet`). That is the reservation the old `AUXW` dead gap used to carry, said at
    Mina's slot.

⚑ **THE FORK THAT USED TO BE STATED HERE IS CLOSED, AND IT WAS NOT A FORK.** This docblock read
"a DESIGN FORK, LEFT OPEN DELIBERATELY, AND IT IS THE OPERATOR'S": a DERIVATION standard on which
the six stay unread until a next proof's W-FINALIZE exists, against UPSTREAM'S on which they are
free pass-throughs one closing `Generic` half away. The operator settled it on 2026-08-05, and the
reason it was never really two answers is that **Pickles recomputes all six and substitutes them**
(`expand_deferred`, consumed at `verification.rs:886`) — so the derivation horn describes a proof
nobody intends to hand to Pickles. The readers now consume the public words. They still DERIVE
nothing, and they still check nothing: that is upstream's shape, not a shortfall in this one.

⚠ **AND THE CHECK IS AN EQUALITY, NOT A SUBSET, WHERE IT IS PINNED.** `wrapInertOk` alone would
only stop the emission from leaving MORE unread than declared; the per-rung theorems state
`inertPublicWords 40 gates = wrapInertOk`, so a rung that quietly stopped deriving a slot it
declares, or started deriving one it does not, is red either way. -/
def wrapInertOk (s : WrapShape) (k : Rung) : List Nat :=
  (List.range WRAP_PRIMARY_LEN).filter (fun i =>
    WRAP_UNPINNED_SLOTS.contains i
    || ((WRAP_PINNED_SLOTS.contains i || WRAP_PASSTHROUGH_SLOTS.contains i)
        && !((wrapSlotsAt s k).contains i)))

/-- ⚑ **THE SLOT → VARIABLE TABLE, BUILT ONCE.** `wrapSlotsAt` beside `exposedVarsAt`, pointwise.

⚠ **THIS IS A `let`-HOISTING SITE AND IT IS LOAD-BEARING, MEASURED.** Its consumers map over
`WRAP_PRIMARY_LEN = 40` slots, and `exposedVarsAt _ .close` runs `whSpongeC` — three full
`hash_messages_for_next_wrap_proof` sponges. Evaluated inside the map it is FORTY sponge runs per
consumer and `wrapEnvAt`/`wrapPublicAt` are two consumers, where the dense vector cost eight.
Measured 2026-08-05: `w12_close` emitted in ~3 min before the layout change and had not finished in
**44** with the table rebuilt per slot. Callers bind this ONCE above their map. -/
def slotVarTable (t : WrapData) (k : Rung) : List (Nat × PVar) :=
  (wrapSlotsAt t.sh k).zip (exposedVarsAt t k)

/-- Slot `i`'s variable at rung `k`, or `none` where this rung derives nothing for it. ⚠ Rebuilds
the table; use `slotVarTable` directly when asking about more than one slot. -/
def slotVarAt (t : WrapData) (k : Rung) (i : Nat) : Option PVar :=
  (slotVarTable t k).lookup i

/-- ⚑ **THE ENVIRONMENT IS THE RUNG'S, NOT THE FILE'S.** `xhatEnv` carries every accumulator point
and every slope of §15's ladders, and each of those is three `qInv`s deep. Folding it into one
shape-wide `circuitEnv` made EVERY pin below `w6_xhat` — §12's witness-grid guards, §14b's placement
theorems — reduce the whole MSM: measured, that took the module from 150 s and ~1 GB to a hard
~10 GB ceiling inside `#assert_namespace_axioms`. A rung's environment is now exactly the variables
its own rows define, which is also the more faithful statement. -/
def circuitEnvAt (t : WrapData) (k : Rung) : VarEnv :=
  spongeEnv (baseSp t.sh) t.sp ++ challengeEnv t ++ branchEnv t.sh (baseBr t.sh t.sp) t.br
  ++ keyEnv t
  ++ (match k with
      | .xhat => xhatEnv t
      | .split => xhatEnv t ++ splitEnv t
      | .ftcomm => xhatEnv t ++ splitEnv t ++ ftcEnv t
      | .prev => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t
      | .finalize => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ finEnv t
      | .finsponge => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ finEnv t ++ finSpEnv t
      | .wraphack => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ whEnv t
      | .close => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ combEnv t ++ bulletEnv t
                  ++ whEnv t ++ closeEnv t
      | .combine => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ combEnv t
      | .bullet => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ combEnv t ++ bulletEnv t
      | _ => [])

/-- The closing rung's environment — what `w8_ftcomm` sees, i.e. everything. -/
def circuitEnv (t : WrapData) : VarEnv := circuitEnvAt t .prev

/-- The full environment: the circuit's variables, then the forty public words, whose values are
READ OUT of the circuit env at the exposed variables — so a public word and the variable its closing
row ties it to hold ONE value by construction, exactly as a copy class does.

⚠ ⚑ **WHAT SITS AT THE TEN THIS RUNG DOES NOT DERIVE, AND WHAT THAT IS AND IS NOT.** A ZERO. For
the `Spec.T.Constant` / dead-lookup slots that IS the value a real devnet wrap proof carries
(`MinaWrapPublicInput.the_tail_is_padding_and_branch_data`, over `MinaWrapPublicCommGate.
PUBLIC_INPUT`), so those ten are right rather than merely accepted. The circuit reads none of them,
so a verifier accepts any value there, and saying so is the point.

⚑ **THE SIX DEFERRED SLOTS ARE NO LONGER AMONG THEM, AND THE ZERO THAT USED TO SIT THERE WAS THE
WHOLE PROBLEM.** Slots 0–4 and 9 carried a PLACEHOLDER zero while W-FTCOMM / W-COMBINE / W-BULLET
read fixture-defaulted free witnesses beside them — two objects where upstream has one. They now
carry the value of the cell that reads them, which is `MinaWrapDeferredWords`' measurement of
`expand_deferred`'s own output for a real step proof, and `slotVarTable` resolves them like any
other tied slot. They are still DERIVED by nothing and CHECKED by nothing here; what changed is that
a prover no longer chooses them.

⚠ **AND A ZERO AT ONE OF THE SIX IS NOW A RED, NOT A RESIDUE.** If `tbl.lookup` ever misses at 0–4
or 9 the slot silently reverts to the old placeholder, which is exactly the state this commit left.
The instrument that sees it is the per-rung inertness EQUALITY, not this function. -/
def wrapEnvAt (t : WrapData) (k : Rung) : VarEnv :=
  let ce := circuitEnvAt t k
  let ix := envIndex ce
  -- ⚑ HOISTED. See `slotVarTable`: inside the map this is forty `whSpongeC` runs.
  let tbl := slotVarTable t k
  ce ++ (List.range (rungPub t.sh k)).map (fun i =>
    ((.external i : PVar), match tbl.lookup i with
                           | some v => envLookupAt ix v
                           | none => (0 : Int)))

def wrapEnv (t : WrapData) : VarEnv := wrapEnvAt t .prev

def wrapPublicAt (t : WrapData) (k : Rung) : List Int :=
  let ix := envIndex (circuitEnvAt t k)
  let tbl := slotVarTable t k
  (List.range (rungPub t.sh k)).map (fun i =>
    match tbl.lookup i with
    | some v => envLookupAt ix v
    | none => (0 : Int))

/-- **`wrapPublicAt_length`** — a rung's public vector is exactly that rung's declared width, for
EVERY `WrapData` and EVERY `Rung`. General and kernel-clean, in the idiom of `rungRows_is_a_ladder`:
a shape instance of this is an INSTANCE, never a separately evaluated literal that a rung change can
silently falsify. (`wrapPublic`, the rung-blind alias that used to sit here, is deleted — see the
note above `rungJson`.) -/
theorem wrapPublicAt_length (t : WrapData) (k : Rung) :
    (wrapPublicAt t k).length = rungPub t.sh k := by
  simp only [wrapPublicAt, List.length_map, List.length_range]

def wrapGates (rows : List WRow) : List PGate :=
  rows.map (fun r => { kind := r.kind, permVars := r.perm, coeffs := r.coeffs })

/-- The composed 15 × `(pubSize + nRows)` witness grid. -/
def wrapWitnessAt (t : WrapData) (k : Rung) (pubSize : Nat) (rows : List WRow) : List (List Int) :=
  let ix := envIndex (wrapEnvAt t k)
  let n := rows.length
  compose 15 (pubSize + n)
    (((List.range pubSize).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
     :: (rows.zip (List.range n)).map (fun ri =>
          gateVarWitnessAt ix (pubSize + ri.2)
            { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
          ++ ri.1.advice.map (fun cv => ((⟨pubSize + ri.2, cv.1⟩ : Cell), cv.2))))

/-- **THE FAIL-CLOSED PLACEMENT.** `placeCheckedWith`, never `place`.

⚑ The rung is an argument now, and it is the DECLARATION side of H2: `wrapInertOk s k` names the
slots this rung says it leaves unread, and the placement refuses any OTHER inert slot. Passing the
rung is what keeps the refusal rung-shaped — `w8_ftcomm` under `w9_prev`'s declaration is still
refused, at slot 12. -/
def placedOf (s : WrapShape) (k : Rung) (pubSize : Nat) (gs : List PGate) : List PlacedGate :=
  match placeCheckedWith ⟨pubSize, AUXW s⟩ (wrapInertOk s k) gs with
  | .ok p => p
  | .error _ => []

def refusalOf (s : WrapShape) (k : Rung) (pubSize : Nat) (gs : List PGate) : Option PlaceRefusal :=
  match placeCheckedWith ⟨pubSize, AUXW s⟩ (wrapInertOk s k) gs with
  | .ok _ => none
  | .error e => some e

/-- ⚑ **THE UNREAD SET, MEASURED.** What the emitted gates of rung `k` actually leave unread among
Mina's forty. The per-rung pins state this EQUALS `wrapInertOk s k`; it is a separate definition
because one side must be read off the EMISSION and the other must be a declaration, and collapsing
them is how this check would stop being able to go red. -/
def inertSlotsAt (s : WrapShape) (k : Rung) (gs : List PGate) : List Nat :=
  inertPublicWords (rungPub s k) gs

/-- Rung `k`'s absolute probe rows, in schedule order. -/
def rungProbeRows (t : WrapData) (k : Rung) : List Nat :=
  let rows := rungRows t k true
  let p := rungPub t.sh k
  ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map (fun ri => p + ri.2)

/-! ### The renderer — the same JSON the pickles harnesses parse. -/

/-! ⚑ **ONE RENDERER.** `renderWrapCircuit` and its six private helpers are DELETED. The three
field groups this side needs — `public_input`, the slot census and `probe_rows` — are `Option`
fields of the `KimchiCircuit` VALUE, and `renderCircuit_wrap_is_the_open_coded_shape` pins over
EVERY argument that `KimchiCircuitJson.renderCircuit` emits the chain `renderWrapCircuit` emitted.

⚑ **THE SLOT CENSUS TRAVELS WITH THE CIRCUIT.** Which of Mina's forty this emission DERIVES, and
which it declares unread. A Rust gate that had to guess the split would be testing its own guess;
these two lists are what makes the harness's public-input polarity a measurement of the 24-vs-40
shape instead of an assertion about it. They are ONE field (`slots := some (derived, unread)`)
because a circuit declaring half a census is worse than one declaring none.

⚠ `wrapCircuit` below passes `some []` — `some`, not `none` — for a `pubSize = 0` rung's public
vector and slot census. Those rungs emit `"public_input":[]`, `"derived_slots":[]`,
`"unread_slots":[]`, keys and all, and have since this file's first emission. -/

/-- Rung `k`'s circuit, as a VALUE. -/
def wrapCircuit (t : WrapData) (k : Rung) (wired : Bool) (name : String)
    : KimchiCircuitJson.KimchiCircuit :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  { name := name, pubSize := p, numRows := p + rows.length
  , gates := placedOf t.sh k p (wrapGates rows), witness := wrapWitnessAt t k p rows
  , publicInput := some (if p == 0 then [] else wrapPublicAt t k)
  , slots := some (if p == 0 then [] else wrapSlotsAt t.sh k,
                   if p == 0 then [] else wrapInertOk t.sh k)
  , probeRows := some (rungProbeRows t k) }

/-! ⚠ ⚑ **`wrapWitness` AND `wrapPublic` ARE DELETED, and the deletion is the point.** They were
rung-blind aliases — "the closing rung's …, kept for callers that do not carry a `Rung`" — and "the
closing rung" is not a constant. Measured 2026-08-04: `wrapPublic` was REDEFINED FOUR TIMES in 23
hours as this ladder grew — `wrapPublicAt _ .xhat` (`d89815028`, 08-03 10:23), `.split`
(`a06587ab3`, 17:20), `.ftcomm` (`de39288d2`, 18:11), `.prev` (`5269fa248`, 08-04 00:45) — each time
changing every caller's meaning with NO diff in the caller.

Three of the four were harmless by luck, not by design: `WitnessBuilder.envIndex` folds the REVERSED
env so a variable's FIRST binding wins, and each rung APPENDS its environment, so a widened env
cannot move a word already bound. The fourth was not: `rungPub _ .prev = pubWords + 1`, which turned
`KimchiStepWrapChain`'s `(wrapPublic tChain).length = shapeChain.pubWords` into `23 = 22` and took a
whole conjunction — including that file's tamper-detection claim — down with it, in a module nothing
was compiling.

Every caller now carries its rung: `wrapPublicAt t k` / `wrapWitnessAt t k`. See
`KimchiStepWrapChain` §9a. Do not reintroduce a rung-blind alias for these. -/

def rungJson (t : WrapData) (k : Rung) (wired : Bool) (name : String) : String :=
  renderCircuit (wrapCircuit t k wired name)

/-! ## §8 — the committed shape.

  * ⚑⚑ `maxPrevs = 2` — **`Max_proofs_verified`, and the field was RENAMED on 2026-08-07 because
    the two numbers had swapped places rather than separated.** It sizes `prev_step_accs`
    (`wrap_main.ml:221-223`), the `prev_proof_state` typ (`:265-275`), the `finalize_other_proof`
    loop over `unfinalized_proofs` (`:287-289`, whose upstream comment is *"This is padded to
    max_proofs_verified"*) and `Split_commitments.combine`'s list (`wrap_verifier.ml:687-702`) —
    every one of them `Max`, and it is the devnet wrap VK's `prev_challenges: 2`
    (`bridge/mina-zkapp/fixtures/mina-devnet-wrap-transaction-vk.json`).
    ⚠ **AND `actual_proofs_verified` LIVES ON THE BRANCH, NOT ON THE SHAPE.** It is
    `Pseudo.choose (which_branch, step_widths)` (`wrap_main.ml:173-180`) — a witness-selected
    value — so it reaches this file as `BranchData.fz` and as `WH_REAL_SLOTS`, which is 1 because
    dregg's step rule assembles ONE `verify_one` (`gates::STEP_RULE_N_PREVIOUS`,
    `marshal::STEP_RECURSION_SLOTS`, `wrap.rs:666` reading the record's own length).
    ⚠ **THE 2026-08-07 MORNING EDIT SET THIS FIELD TO `1` AND THAT WAS THE FIFTH TURN OF THE SAME
    DEFECT.** It cost `combTerms` (46 against Mina's 47), one of the two `finalize_other_proof`
    instances (61 Poseidon blocks against 122), and — through `RC_SGOLD` shrinking with it — an
    OFF-CURVE `sg_old` at the smoke shape. The transcript's absorb count really did have to move,
    and it moved: it is `schedule`'s `WH_REAL_SLOTS`, where it belongs.
  * `ipaRounds = 16` — `Backend.Tick.Rounds.n`, the STEP proof's IPA round count
    (`Common.Max_degree.step_log2 = 16`); `wrap_main.ml:381` sizes `openings_proof.lr` by it.
    ⚠ It is NOT 15; 15 is `Tock.Rounds.n`, which is what the STEP circuit's `verify_one` sees.
  * `wComms = 15`, `tComms = 7` — `Plonk_types.Columns.n` and
    `Commitment_lengths.create ~t:(of_int 7)`.
  * `emsRows = 8` — the 128-bit `to_field_checked` (`bits_per_row = 16`).
  * `branches = 5` — a wrap instance compiled for a five-rule step circuit. ⚑ There is no canonical
    value: `wrap_main` is per-zkApp (`wrap_main.ml:96-101`), which is the whole reason Mina's two
    blobs are a shape reference and not a byte target.
  * `pubWords = 22` — §10's census: the words the CLOSING rung derives. The emitted vector is
    `WRAP_PRIMARY_LEN = 40` wide at every rung from `w4_bind` up, in Mina's slot order; `w9_prev`
    adds slot 12 and `w11_wraphack` slot 11, which is the 22 → 24 ladder, and the remaining sixteen
    are `WRAP_UNPINNED_SLOTS`. -/
def shapeWrap : WrapShape :=
  { maxPrevs := 2, ipaRounds := 16, wComms := 15, tComms := 7, emsRows := 8
  , branches := 5, pubWords := 22, xhatEntries := xhatSel XHAT_TERMS_FULL
  -- ⚑ `xhatOut XHAT_TERMS_FULL`, and `EmitWrapMainJson` re-derives it and REFUSES on disagreement
  -- at every emission. Not closed in the kernel: 1805 five-bit chunks is 3.6 s compiled and far
  -- more reduced. ⚠ The file's ONE `native_decide` is §24's
  -- `bullet_solves_g_on_curve_and_equal_g_is_one`, pinned by `#assert_compiled`; this is not it.
  -- ⚠ ⚑ **AND IT MOVED AGAIN AT §20 (2026-08-05), FOR THE SAME REASON, FOUND THE SAME WAY.**
  -- `d6683dd54` landed W-FINSPONGE with `FIN_DEFERRED_CIP/_B/_XI` as three literal ZEROS, so every
  -- emission REFUSED; repairing the memo (`44efc9a18`) made packed statement words 27, 28 and 37 the
  -- DERIVED `combined_inner_product`, `b` and `xi` instead of `a^9` fixtures. Those are x_hat MSM
  -- entries 32/33, 34/35 and 47, so `xhatOut 67` is again a different point. §20's own docblock
  -- predicted exactly this in writing and the pair was not re-derived with it; `EmitWrapMainJson`'s
  -- refusal and `KimchiStepWrapChain.chain_xhat_is_the_step_proofs_not_the_msm_output` are what
  -- caught it. **WHAT RE-EMITS:** every `wrapmain_wrap_*.json` from `w6_xhat` up. ⚑ The SMOKE shape
  -- is again unmoved — `xhatSel 5` selects none of entries 32/33/34/35/47 — which is why all 30
  -- smoke rungs are byte-identical across the split.
  -- ⚠ ⚑ **THIS PAIR MOVED AT `w11_wraphack`, AND THE REFUSAL IS WHAT FOUND IT.** §21 makes packed
  -- statement words 55 and 56 the two prev-proof `hash_messages_for_next_wrap_proof` squeezes
  -- instead of fixtures, so MSM entries 65 and 66 carry different scalars and `xhatOut 67` is a
  -- different point. The first wrap-scale emission after §21 landed threw
  -- `⚑ xhatXY IS NOT THE MSM'S OUTPUT` and printed the new pair; this is that pair.
  -- **WHAT RE-EMITS:** every `wrapmain_wrap_*.json` — the absorbed `x_hat` at
  -- `wrap_verifier.ml:617` moves, so every wrap-scale challenge, the fork digest and all 22 derived
  -- public words below it move with it. The SMOKE shape is unmoved: `xhatSel 5` does not select
  -- entries 65/66, which is also why the smoke fixtures below `w11_wraphack` are byte-identical.
  -- ⚠ ⚑ **AND IT MOVED AGAIN ON 2026-08-05, WHEN THE TRANSCRIPT BECAME THIS PIPELINE'S OWN STEP
  -- PROOF'S.** `RC_SGOLD` and `KimchiWrapMainField.whSgOld` now both resolve to
  -- `KimchiStepWrapChainFixture.STEP_PREVCOMM_XY`, so §21's two prev-proof
  -- `hash_messages_for_next_wrap_proof` squeezes hash a different `sg_old`; those squeezes ARE
  -- packed statement words 55/56, which are x_hat MSM entries 65/66. `whSg` moved with them
  -- (`openings_proof.challenge_polynomial_commitment` is the step proof's `sg`), which is packed
  -- word 11's input rather than an MSM entry, so it costs word 11 and not this pair.
  -- ⚠ **THE REFUSAL DID NOT FIRE ON THE FIRST TRY, AND THAT WAS THE FINDING.** With only `RC_SGOLD`
  -- moved, `xhatOut 67` was UNCHANGED — because `whSgOld` was a SECOND copy of `sg_old` still
  -- reading `PastaPoseidonFq.PREVCOMM_XY`, so the emitted §21 rows (which read the transcript's
  -- cells) and the packed words the MSM consumes had come apart. A green refusal check was
  -- evidence of the defect, not of its absence.
  -- ⚑⚑ **AND ON 2026-08-06 IT STOPPED BEING A LITERAL PAIR AT ALL.** The MSM's scalars are the step
  -- proof's own published `Types.Step.Statement` (`STEP_PUBLIC_IN`) against its own domain's
  -- Lagrange basis, so the fold's output IS the public-input commitment `kimchi::verifier` computed
  -- for that proof — `KimchiWrapMainField.the_xhat_msm_is_this_proofs_public_input_commitment`.
  -- Written as the fixture's own words rather than as two numerals so the memo and the value it
  -- must equal have ONE source and a re-export moves both; `EmitWrapMainJson` still re-derives
  -- `xhatOutOf` and REFUSES on disagreement. **WHAT RE-EMITS:** every `wrapmain_wrap_*.json` AND
  -- every `wrapmain_smoke_*.json` — the smoke pair moved too this time, because the base table and
  -- every scalar moved and `xhatSel 5` selects from the same 67.
  , xhatXY :=
      (Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBCOMM_XY.getD 0 0,
       Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBCOMM_XY.getD 1 0) }

/-- A small shape for the in-CI `#guard`s (the committed one is emitted by the driver). -/
def shapeSmoke : WrapShape :=
  { maxPrevs := 2, ipaRounds := 3, wComms := 3, tComms := 2, emsRows := 8
  , branches := 3, pubWords := 6
  -- ⚑ FIVE ENTRIES, and `xhatSel` makes them `[0, 1, 11, 64, 31]` — a 255-bit `B Field` value, its
  -- 1-bit parity, a 128-bit challenge, the `messages_for_next_step_proof` DIGEST and
  -- `should_finalize`. That reaches BOTH partitions, all three widths, both top-zero counts (1 and
  -- 3) and both `Cond_add` branches (§15's `xhat_smoke_selection…`). A PREFIX of five would have
  -- been five 255-bit-or-parity entries and no 128-bit ladder at all. ⚑ Entry 64 is here because
  -- `w9_prev` exposes its packed word as a PUBLIC one, and a public word whose cell the MSM never
  -- reads is a public fixture.
  , xhatEntries := xhatSel 5
  -- ⚑ `xhatOutOf (xhatSel 5)`, closed by `rfl` IN THE KERNEL by
  -- `xhat_smoke_shape_absorbs_the_msm_output`. ⚠ It MOVED on 2026-08-06: the bases are the step
  -- proof's own domain's now and every scalar is a published statement word, so a five-entry subset
  -- of the same 67 is a different point. Unlike the four previous moves, this one is NOT confined to
  -- the wrap shape — all thirty smoke rungs re-emit.
  -- ⚑⚑ **AND IT MOVED AGAIN ON 2026-08-07, WHEN THE WRAP RECORD ACQUIRED ITS PAD.** Packed statement
  -- words 55/56 became `[messages_for_next_wrap_proof_padding(), the real digest]`, so
  -- `stepmain_step_r8_finalize` re-emitted (exactly two of sixty-seven entries) and the step proof
  -- re-proved — which moves EVERY commitment in `KimchiStepWrapChainFixture` and therefore every
  -- MSM scalar and every Lagrange base this fold reads.
  -- ⚠ `shapeWrap.xhatXY` did NOT need a hand-edit for the same event, and the asymmetry is the
  -- lesson: it names `STEP_PUBCOMM_XY` (the fixture's own words) and moved with the re-export, while
  -- this one is a literal pair and went stale silently. `EmitWrapMainJson`'s refusal is what caught
  -- it — a memo written as a numeral is a memo that can rot.
  , xhatXY :=
      (28165423449084717082481151485798317168113882370163881582671000826766251401262,
       4549862343199917614386982613737362184182002331567877581633298615345383329301) }

end Dregg2.Circuit.Emit.KimchiWrapMain
