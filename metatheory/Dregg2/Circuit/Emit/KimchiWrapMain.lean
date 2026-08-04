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

## ⚑ WHAT THIS FILE ASSEMBLES TODAY — nine rungs, and the rest named

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
  * **W5 `key`** — §14. ⚑ **`choose_key` AND THE INDEX SPONGE**, i.e. the sub-circuit that makes the
    transcript's INPUT derived. `wrap_verifier.ml:189-204` folds the per-branch step keys against the
    SAME one-hot vector §9 already emits — and because `wrap_main.ml:218-219` passes them through
    `Inner_curve.constant`, that fold is `Generic` arithmetic and not a curve MSM. Its 28 chosen
    commitments then feed a FRESH Fq sponge (`:521-530`) in `index_to_field_elements` order, 56
    coordinates and one squeeze. §14b pins that squeeze against the digest Rust kimchi computes for
    the same `VerifierIndex` — so `index_digest` is DERIVED here, not fixtured.
  * **W6 `xhat`** — §15. ⚑ **THE PUBLIC-INPUT MSM** (`wrap_verifier.ml:539-616`), and the first
    curve gadget in this file: 67 entries at `15 × 255 · 40 × 128 · 12 × 1`, `scale_fast2`'s split
    and its top-bit zero asserts, `add_fast base base` and `n_acc = 0` both CONSTRAINED, the
    correction reduce, the `Cond_add` mux, `Inner_curve.negate` and `x_hat blinding`. Its output is
    the pair `:617` absorbs, so the transcript's `x_hat` stops being a fixture VALUE. ⚠ Its scalars
    are W-PREV's free witnesses and `x_hat` therefore STAYS on `WRAP_UNCONSUMED` — §2c says why at
    length, and §15's own header says it again where the rows are.
  * **W7 `split`** — §16. `split_field` (`wrap_main.ml:69-81`, called once at `:409`), one
    `Boolean.typ` check and one `Field.Assert.equal ((of_int 2 * y) + is_odd) x` per `` `Field ``
    statement word, whose outputs ARE W6's 255-bit and 1-bit entry scalars.
  * **W8 `ftcomm`** — §17. `Common.ft_comm` (`common.ml:238-256`), `tComms + 1` ladders at
    `Ops.scale_fast ~num_bits:255` — **NOT** `scale_fast2`; `wrap_verifier.ml:658-659` shadows it.
  * **W9 `prev`** — §18. ⚑ **THE WITNESSED PREVIOUS STEP STATEMENT** (`wrap_main.ml:201-256`,
    `:340-356`), and the rung that gives W6 and W7 their content. Its own rows are few ON PURPOSE:
    read at source, `exists ~request:Req.Proof_state`'s `typ` emits **two `Boolean.typ` checks over
    57 words and nothing else** — `Limb_vector.Challenge.typ` is `Typ.field` with a transport and no
    range check at all, and the `~assert_16_bits` `wrap_main.ml:208` passes is consumed only by
    `Branch_data`, which the STEP per-proof spec does not contain. Plus `Inner_curve.typ`'s
    `assert_on_curve` on the two `prev_step_accs` — three rows each, over the very cells
    `wrap_verifier.ml:538` absorbs as `sg_old` — and one `Field.Assert.equal` that makes
    `messages_for_next_step_proof` this assembly's **23rd public word** (§10 slot 12).
    ⚑ **What it really buys is the WIRING**: `xScal` makes every `` `Packed_bits `` entry's MSM
    scalar cell BE its packed statement word, and `xSplitW` makes `split_field`'s `x` the word too,
    so the 67 scalars are the image of 57 words instead of 67 independent draws.
    ⚠ **`x_hat` STILL does not leave `WRAP_UNCONSUMED`**: 64 of the 67 scalars are free witnesses
    here and free upstream, and what ties them is W-FINALIZE / W-WRAPHACK / `assert_eq_plonk`.

## ⚑ MEASURED — the emitted ladder, and the shape oracle it is scored against

    rung             smoke rows   wrap rows   pub   what it is at source
    w1_transcript        246          818       0    wrap_verifier.ml:516-646 + :383-437
    w2_challenges        471         1407       0    scalar_challenge.ml:12-136
    w3_branch            489         1430       0    wrap_main.ml:164-199
    w4_bind              492         1441      22    wrap_main.ml:419-439 + :189-199
    w5_key               972         1977      22    wrap_verifier.ml:189-204 + :521-530
    w6_xhat             1286         6472      22    wrap_verifier.ml:539-616
    w7_split            1288        6492*      22    wrap_main.ml:69-81 + :409
    w8_ftcomm           1607        7338*      22    common.ml:238-256 + wrap_verifier.ml:655-666
    w9_prev             1613        7344*      23    wrap_main.ml:201-256 + :350-351

⚠ ⚑ **THE SMOKE COLUMN MOVED AT `w9_prev` FOR THE THREE RUNGS BELOW IT, AND NOT BECAUSE THEY
CHANGED.** `shapeSmoke.xhatTerms` went 4 → 5 so that the smoke MSM reaches entry 64 — the packed
word `w9_prev` exposes publicly — which adds one 51-chunk ladder: `w6_xhat` 1170 → 1286, and
`w7_split`/`w8_ftcomm` carry it. The WRAP column is unmoved below `w9_prev`, because at the
committed shape `xhatSel` was already the identity over all 67 entries.

⚑ **PROVED, MEASURED 2026-08-03** on the smoke emission, release, all five polarities per rung:

    rung            rows  domain   honest prove+verify   σ-desync   control   pub tamper
    w1_transcript    246     256          1035 ms        REJECTED   ACCEPTED     n/a
    w2_challenges    471     512          1898 ms        REJECTED   ACCEPTED     n/a
    w3_branch        489     512          1248 ms        REJECTED   ACCEPTED     n/a
    w4_bind          498     512          1641 ms        REJECTED   ACCEPTED   REJECTED
    w5_key           978    1024          1042 ms        REJECTED   ACCEPTED   REJECTED
    w6_xhat         1292    2048          1251 ms        REJECTED   ACCEPTED   REJECTED
    w7_split        1294    2048          1127 ms        REJECTED   ACCEPTED   REJECTED
    w8_ftcomm       1613    2048          1085 ms        REJECTED   ACCEPTED   REJECTED
    w9_prev         1620    2048          7877 ms        REJECTED   ACCEPTED   REJECTED

(the `rows` column here is `pubWords + rows`, which is what the harness prints; the table above is
the emitter's row count.) ⚑ At `w9_prev` the public-input leg runs at **i = 0 and i = 6** — the new
word is the last one, so the σ leg "flip cell (i,0) AND tell the verifier the new value" is tested
on it specifically, and it is REJECTED by the copy-permutation alone.
⚠ These are INNER Pallas/Fq kimchi proofs of a `wrap_main`-SHAPED circuit. Not Mina-valid, not
machine-checked Pickles; the opening (`equal_g`, `verified`, the accumulator check) is not in this
circuit at all.

⚠ `*` — the SMOKE column is MEASURED for every rung, from emissions those rungs produced
(`w7_split: 1172 rows, pub 6, 51 probes`; `w8_ftcomm: 1491 rows, pub 6, 55 probes`). The two starred
WRAP figures are DERIVED, because the wrap-scale emission is hours under `lean --run`'s interpreter
and had not finished when this line was written:

  * `w7_split` = `6472 + 20` — ten `split_field` words, ten `Generic` rows and ten σ-probes;
  * `w8_ftcomm` = `6492 + 846` — `4` rows of `n₀ = 0` halves, `8 × (1 seed + 51×2 chunk rows + 1
    probe) = 832`, the fold's `tComms − 1 = 6` `add_fast` rows, and `4` closing rows;
  * `w9_prev` = `7338 + 6` — nine `Generic` halves (2 `Boolean.typ`, 1 public tie, 3 × `prevs = 2`
    `assert_on_curve`) packed two to a row, plus one σ-probe. `prevs` is 2 at BOTH shapes, so this
    is the same six rows at either — which is why the smoke measurement `1613 − 1607 = 6` is a real
    check on the wrap figure and not merely a consistency one.

The `w7`/`w8` derivations are CHECKED at the smoke shape against the emission: `1286 + 2 = 1288` and
`1288 + 319 = 1607`, and the emission agreed on both to the row. A derivation that reproduces the
measured shape is still not a measurement, and the star says which is which.

⚑ `w6_xhat`'s wrap-scale row count is the one number in this table that is checked against something
outside this tree. Its gate stream carries **VarBaseMul = 1805** and **CompleteAdd = 232**, read off
the emitted JSON — and 1805 is exactly the W-XHAT share of `wrap-transaction`'s own `VarBaseMul 2417`
(`+ 408` W-FTCOMM `+ 204` W-BULLET), while 232 is `xhat_gate_census`'s formula at 67 entries and 55
ladders. A wrong entry width, a wrong entry count, or reading `bp_log2` as Tick's 16 instead of
Tock's 15 all miss both.

At the committed shape the transcript feeds **120 sponge items** and takes **23 squeezes**, of which
21 are 128-bit challenges (§2b is the item-by-item census).

`bridge/mina-zkapp/scripts/mina-canonical-circuit-oracle.mjs --circuit wrap-transaction` reports
**15,122 gates at PI 40**, histogram `Generic 3521 · Poseidon 2871 · Zero 2757 · EndoMul 2528 ·
VarBaseMul 2417 · EndoMulScalar 536 · CompleteAdd 492`; the devnet wrap VK's domain is 2^14 = 16,384,
so Mina's own emission has ~1,259 rows of headroom. `wrapmain-region-conformance.mjs` scores this
assembly against it. RE-GRADED at `w6_xhat` (exit 0), the verdicts that are not "absent" are:

  * **`Poseidon` — 89/89 instances, 100%**, the WHOLE 11-row permutation INCLUDING all fifteen round
    constants per row, matching a `wrap-transaction` class byte for byte. The Fq Poseidon gadget
    this file emits IS the one Snarky emits in Mina's own wrap circuit. (It was 61/61 before W-KEY's
    index sponge added 28 permutations; the count moves with the assembly, the 100% does not.)
  * **`EndoMulScalar` — the BODY 42/42, the whole instance 0/42**, with the seam exactly three cells
    and both of them this file being STRICTER; §13 names them.
  * **`VarBaseMul` — 1805 of Mina's 2417**, and **`CompleteAdd` — 232 of 492**, both from `w6_xhat`.
    The remainders are W-FTCOMM's eight ladders (408) and W-BULLET's four (204), and W-COMBINE /
    W-BULLET's `add_fast` rows. Before this rung both read `lean 0 — ⚠ ABSENT`.

✅ **THE STANDING GATE WAS RE-POINTED, AND THE FAIL-OPEN IT HAD WAS STRUCTURAL.**
`wrapmain-region-conformance.mjs`'s `LEAN_DEFAULT` read `…_w5_key.json` — the rung BELOW W-XHAT — so
an unattended run reported `VarBaseMul mina 2417 / lean 0 ⚠ ABSENT`, matched that against a LEDGER
entry which still said `lean 0`, and **exited 0**: a green that measured the wrong object. Three
changes, none of them a warning: a single `TOP_RUNG` constant now derives the default path, the
fixture name and the sidecar name together; the emission's own `name` field is CHECKED against it
and a lower rung REFUSES (exit 3) instead of grading; and `EMITTED_FAMILIES` makes a zero count for
any family the top rung emits a hard exit-1 BEFORE the vector diff, so an ABSENT verdict for a
family we actually emit can no longer be laundered through the ledger.
⚠ **And the committed fixture that comment promised did not exist.** `git log --all --
'fixtures/wrapmain*'` was EMPTY: the `.gz` and its sidecar were described in the script's own header
as "added 2026-08-03", and neither was ever committed — so `haveFix` was permanently false and the
`fixture/in-sync-with-live-emission` leg could never fire. A documented fixture is not a committed
one.

⚠ ⚑ **AND THE SENTENCE THAT STOOD HERE — "It is committed now, under the top rung's name" — WAS
ITSELF FALSE, re-checked 2026-08-03.** `git log --all -- 'bridge/mina-zkapp/fixtures/wrapmain-*'` is
still empty and `bridge/mina-zkapp/fixtures/` holds only the step fixture and the two devnet wrap
VKs. So the correction inherited the defect it was correcting: a second documented fixture, one
sentence below the paragraph explaining why that is not a real one.

**The fixture is PENDING, and the reason is the emission, not an oversight.**
`wrapmain-region-conformance.mjs` names `wrapmain-wrap-w8-ftcomm-gates.json.gz`, and producing it
needs `DREGG_WM=wrap lake env lean --run …/EmitWrapMainJson.lean` at the TOP rung — a wrap-scale
emission under `lean --run`'s interpreter, which is what the `*` in the rung table above is about:
it is hours, and it had not finished when either sentence was written. Until it lands, `haveFix` is
false, `requireFreshFixture` is unreachable, and the `fixture/in-sync-with-live-emission` leg
reports `absent`. ⚠ That leg is a `conform(…, 'absent', 'absent')` equality, so it is GREEN while
absent — the gate is live only for the run that has a live emission anyway. Read "conformance
green" at that resolution until the `.gz` is on disk.

⚑ And the wrap side has a cross-check the step side never had: **`wrap-blockchain` is an
independently compiled `wrap_main`** and its non-Generic gate stream is byte-identical to
`wrap-transaction`'s (11,601 gates, same types, same coefficients), so every non-Generic conformance
fact is checked against both blobs.

⚠ **NOT ASSEMBLED, named by sub-circuit** (§13): W-FINALIZE, W-WRAPHACK,
W-OPENINGS, W-COMBINE, W-BULLET, and W-CLOSE's three curve-side asserts.
Each is a row-emitter this file does not have; none is a value this file fakes and calls derived.

## ⚑ THE SIX DEFECT CLASSES, CHECKED AS EMITTED (§12)

  1. **Free ladder seeds** — no curve ladder is emitted yet, so there is no `acc₀`/`n₀` to leave
     free. The `EndoMulScalar` chains DO have seeds and all three are pinned by `Generic` rows
     (§5, `tfcRowsQ`); §12c bends each and the row refuses. ⚑ **And W-KEY introduced a second seeded
     object** — the index sponge's fresh zero state (`Sponge.create`, `wrap_verifier.ml:522`), which
     a prover left free could choose `index_digest` with outright. `key_sponge_seed_is_pinned` reads
     the two pinning rows off the EMITTED row list.
  2. **Prover-chosen challenge decompositions** — BOTH halves of every `lowest_128_bits` are
     range-checked: the low half IS the `to_field_checked` chain, the high half gets its own
     (`util.ml:98` asserts `hi` unconditionally). §12d exhibits the forged split that a
     one-sided check admits and shows the high chain refusing it.
  3. **Absorbed-but-not-consumed words** — §2c is the CENSUS and it is honest: at `w5_key` the
     transcript's COMMITMENT words are absorbed and **not yet consumed**, because W-XHAT/W-COMBINE
     are not assembled. `WRAP_UNCONSUMED` names every one; nothing is padded to make a count look
     closed. ⚑ It went 9 → **8** because `index_digest` is now DERIVED by a sub-circuit, not because
     an entry was deleted: `key_digest_is_the_index_digest` is the value pin and `keyRows`' closing
     tie is the σ class.
  4. **Constants pinned against their own definitions** — §11b pins `ENDO_Q` against
     `MinaRealBlockTranscript.ENDO_R`, an INDEPENDENT module whose value is validated by
     `derived_zeta`/`derived_alpha` against a real block's challenge expansion. §11a pins the Fq
     Poseidon constants against `PastaPoseidonFq.rcsQ` AND asserts they differ from the Fp ones.
  5. **Fixtures standing for derived values** — §2d lists every fixture by name. The transcript's
     absorbed words are the REAL commitments of `PastaPoseidonFq`'s accepted Vesta proof wherever
     one exists (`PREVCOMM_XY`, `PUBCOMM_XY`, `WCOMM_XY`, `ZCOMM_XY`, `TCOMM_XY`). ⚑ **`index_digest`
     LEFT THIS LIST at `w5_key`**: §14 emits `choose_key` and the index sponge over the 56 real
     coordinates of the very `VerifierIndex` that digest belongs to, and reproduces it. The
     `lr`/`delta` blocks have no real source in this tree and are named as fixtures rather than
     dressed up.
  6. **Wrong seed points** — no curve seed is emitted; the two seeded objects are the
     `EndoMulScalar` accumulator triple (§12c is its red control) and the index sponge's zero state
     (`key_sponge_seed_is_pinned`).

⚑ **AND THE SEVENTH, WHICH THIS RUNG IS THE PLACE TO GET WRONG: A PUBLIC WORD — OR AN ABSORBED ONE —
HOLDING THE WRONG OBJECT UNDER THE RIGHT NAME.** Rust kimchi's `VerifierIndex::digest`
(`verifier_index.rs:451-530`) absorbs Pickles' eight index fields AND THEN the optional gate
commitments and the whole lookup index when they exist; Pickles' `Plonk_verification_key_evals.t`
has no such fields. The two agree only for an index carrying none of them, so
`fixtures/kimchi-extractors/wrap_key_index_export.rs` **asserts** they are all `None` before it
dumps. Without that assertion the 56 numbers would be a PREFIX of the digest's preimage wearing the
name of the whole of it — and, exactly as in the 20-words case, nothing downstream would notice.

## Axiom hygiene / build

NO `main` (roots into `PicklesSynthesis`; the emit driver is `EmitWrapMainJson.lean`). No `sorry`,
**no `native_decide`**, no `decide` over the big grid. §14b's facts are NAMED THEOREMS closed by
`rfl`/`decide` IN THE KERNEL — strictly stronger than the `#guard`s they would have been
(`metatheory/docs/GUARD-DISCIPLINE.md`) — and `#assert_namespace_axioms` at the foot of the file
accounts for every one of them. The remaining `#guard`s reduce in the interpreter and are the
conversion backlog, not the model.
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.MinaRealBlockTranscript
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate
import Dregg2.Circuit.Emit.KimchiWrapMainField

namespace Dregg2.Circuit.Emit.KimchiWrapMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

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
  /-- ⚑ How many of `wrap_verifier.ml:539-548`'s **67** public-input entries the x_hat MSM emits
  (§15). At the committed wrap shape this IS `XHAT_TERMS_FULL` and `xhatSel` is the identity; the
  smoke shape emits a NAMED spread that reaches all three widths and both partitions. It is NOT a
  claim that the statement has fewer words — `xhatBits` is over all 67 either way. -/
  xhatTerms : Nat
  /-- ⚑ **THE PAIR `wrap_verifier.ml:617` ABSORBS** — §15's MSM output, carried in the SHAPE rather
  than recomputed inside `schedule`.

  ⚠ This is a MEMO WITH A PROOF OBLIGATION, not a fixture, and the difference is enforced in two
  places: `xhat_smoke_shape_absorbs_the_msm_output` closes it by `rfl` IN THE KERNEL for the smoke
  shape, and `EmitWrapMainJson` REFUSES to emit a COMMITTED shape whose `xhatXY` is not
  `xhatOut xhatTerms`. A wrong pair cannot reach a proved circuit. ⚑ A `DREGG_WM`-supplied shape is
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
absorbed item. ⚑ **AT `w5_key` THIS IS NO LONGER A FIXTURE**: §14 emits `choose_key`
(`wrap_main.ml:215-220`) and the index sponge (`wrap_verifier.ml:521-530`) over the 56 real
coordinates of that same index, and `key_digest_is_the_index_digest` pins the derivation's output to
this value. Below `w5_key` it is still a witnessed constant, which is what §2c now says. -/
def RC_DIGEST : Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.VKDIGEST

/-! ### §2d — **THE FIXTURES, NAMED.**

`RC_SGOLD`/`RC_XHAT`/`RC_WCOMM`/`RC_ZCOMM`/`RC_TCOMM` and `RC_DIGEST` are a real accepted proof's
values, but they are FIXTURES in this circuit: no row here derives them, because the sub-circuits
that would (W-KEY for the digest, W-XHAT for `x_hat`) are not assembled. `lr`/`delta` have no real
source in this tree at all and get a deterministic filler, which is named here and nowhere pretends
to be a commitment. -/
def wrapFixture (tag i : Nat) : Nat := (11 + 1000003 * (17 * tag + i)) % qN

/-- Item `i` of tag `t`'s VALUE.

⚠ ⚑ **TAG 2 (`x_hat`) IS NO LONGER HERE.** At `w6_xhat` the absorbed `x_hat` pair is `xhatOut
s.xhatTerms` — §15's MSM output — and `schedule` reads it directly, because `itemVal` has no shape
to read it with. `RC_XHAT` survives only as `xhat_derived_is_not_the_old_fixture`'s red control: the
value the transcript used to absorb, kept so the change is exhibited rather than merely asserted. -/
def itemVal (t i : Nat) : Nat :=
  match t with
  | 0 => RC_DIGEST
  | 1 => RC_SGOLD.getD i (wrapFixture 1 i)
  | 2 => RC_XHAT.getD i (wrapFixture 2 i)
  | 3 => RC_WCOMM.getD i (wrapFixture 3 i)
  | 4 => RC_ZCOMM.getD i (wrapFixture 4 i)
  | 5 => RC_TCOMM.getD i (wrapFixture 5 i)
  | _ => wrapFixture t i

/-- **THE EVENT LIST**, in `wrap_verifier.ml`'s own order.

⚑ **`x_hat` IS DERIVED HERE.** `wrap_verifier.ml:539-616` computes the MSM and `:617` absorbs its
output, and the MSM reads no sponge state — so the schedule can and must carry §15's value. Before
`w6_xhat` this slot held `RC_XHAT`, a real proof's public-input commitment standing in for a value
no row computed. -/
def schedule (s : WrapShape) : List Ev :=
  [ Ev.abs T_DIGEST RC_DIGEST ]
  ++ (List.range (2 * s.prevs)).map (fun i => Ev.abs T_SGOLD (itemVal T_SGOLD i))
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
  [ "sg_old — ON-CURVE at w9_prev (§18); its consumer is W-COMBINE's ~init"
  , "x_hat — MSM EMITTED at w6_xhat (§15); its 67 SCALARS are W-PREV's packed statement words, \
           and 64 of them are still free"
  , "w_comm — needs W-COMBINE"
  , "z_comm — needs W-COMBINE"
  , "t_comm — ft_comm EMITTED at w8_ftcomm (§17); its OUTPUT is W-COMBINE/W-BULLET's"
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
— an inert public word — is the real gate on the closing rung.

⚑ **THE `+ 1` IS `w9_prev`'s PUBLIC WORD, RESERVED AT EVERY RUNG AND EXPOSED AT ONE.**
`wrap_main.ml:350-351` ties `messages_for_next_step_proof` to the witnessed previous statement, and
W-PREV is the rung that emits it — so `rungPub` is `pubWords` up to `w8_ftcomm` and `pubWords + 1` at
`w9_prev`, and slot `pubWords` sits in `placeChecked`'s DEAD GAP below it. That is deliberate and it
is the fail-closed choice: exposing the word earlier would put a public word on a variable no row of
that rung derives — defect class 5 wearing a public vector — and `placeChecked` refuses any gate
that touches the gap, so the reservation cannot be used by accident. -/
def AUXW (s : WrapShape) : Nat := s.pubWords + 1

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

`STEP_VK_XY` below is the 56 coordinates of a REAL `VerifierIndex` — the very index the
`PastaPoseidonFq` fixture's accepted Vesta proof was proved against — dumped in
`index_to_field_elements` order by `fixtures/kimchi-extractors/wrap_key_index_export.rs`, whose
output is `metatheory/kimchi_wrap_key_index.json`.

⚠ **Rust kimchi's `VerifierIndex::digest` is NOT `index_to_field_elements` in general.**
`kimchi/src/verifier_index.rs:451-530` absorbs the same eight fields in the same order, and THEN
`range_check0/1`, `foreign_field_add/mul`, `xor`, `rot` and the whole `lookup_index` **when they are
present**. Pickles' `Plonk_verification_key_evals.t` has no such fields, so the two agree only for
an index that carries none of them. The extractor **asserts** that every optional commitment and the
lookup index is `None` before it dumps — otherwise these 56 numbers would be a prefix of the digest
preimage wearing the name of the whole of it, which is this campaign's own recorded defect.

⚠ **Seven of the 28 points are the identity** — unused coefficient columns of a small generic-only
test circuit — and `DefaultFqSponge::absorb_g` (`poseidon/src/sponge.rs:332-345`) absorbs the FAKE
POINT `(0,0)` for infinity, so they contribute 14 zero coordinates rather than being skipped. That
is recorded because a model that SKIPPED them would produce a different digest, silently. -/

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

/-- ⚑ **THE REAL STEP VERIFICATION KEY, FLATTENED.** `metatheory/kimchi_wrap_key_index.json`,
`index_comm_xy` — 56 Fq coordinates in `index_to_field_elements` order. The extractor asserts, in
Rust, that `verifier_index.digest::<BaseSponge>()` on this index is `PastaPoseidonFq.VKDIGEST` AND
that an independent `absorb_fq` replay over exactly these 56 numbers reproduces it, so the list is
the digest's preimage rather than a second copy of some coordinates. -/
def STEP_VK_XY : List Nat :=
[
  17543387709741642679739098213698819913488961292403631225445715364238599519526, 11573119529266093432396705461675492768038945834599255508296049241297856734468, 24282664799507863726157063054906103836202492223618401057783687704719820518705, 20450769838057368128713704557782545311454600786604851373719488932980829136843,
  13113153697847829803920060773119622631328674576725490904704100107786648013785, 18268880086648877151518696776539000602490214710016166711666240084965263566097, 17263379750694784169780313942094169078426558408734693614265244171650715328121, 9516830587755563624520140836045964417674452343254966588144055563065053437379,
  5571680532746181882816762299697441868911258251718183279851151166607476540269, 26089732342446321127783040719047971682230909306947938294879670120879789365816, 11084502016271805275156586017751893052296064720808704716139366911383136640483, 13575924989125377237478499118365277423417352119937721717049105910199671479436,
  8524547102381891393261912421754872664239363432604302927612170249743630855664, 24154532797574905872704672317362362731042105066852021571757264474697449209648, 20098847360559689704156237343437698136685061298335774373054279593854954294157, 16016631076239966449375000253103811755798626487622941417714689406337320150621,
  19173029641940667037213690524237473254239936644985289298821252322304963417134, 13649680322427311111003087732784799183031566494751591093631401121426475486568, 22968308972962693007021994118989831571840507329322261781320027130804109359533, 4699393604549216660493350767071496631231541711590188006949964301836284822067,
  0, 0, 15946577074244468859156586973572112925677512585555558705349790263010734874107, 19830108337409191689946544792769765859766881769361046975673792357296329864584,
  12806597378361232525042966560513890323423999808517697669343319205651472509020, 24214522613166948753927263944427591729742024623019401563814603303410302167085, 0, 0,
  22968308972962693007021994118989831571840507329322261781320027130804109359533, 4699393604549216660493350767071496631231541711590188006949964301836284822067, 5855324959043032206080591060552754589277265355003809508810922677413304314288, 27932104530385305061856817511502119186290266679145697503580270326100011568248,
  7036480107581638277610712629716610245645415109171603721188368913225225471884, 3567323232828783680610059751565196267442548472793536898599635367442107934142, 0, 0,
  0, 0, 0, 0,
  0, 0, 0, 0,
  8208862071468831568051590605385178994882582145299441122791530348420333425160, 15207365439891095423786130753506646110027367253224152562652125356368357079146, 4128018831155263258921677689761735101256426860488784731125497417640507220481, 22304269070532896717707344537995120070212833580943367087267197592645043797542,
  4128018831155263258921677689761735101256426860488784731125497417640507220481, 22304269070532896717707344537995120070212833580943367087267197592645043797542, 4128018831155263258921677689761735101256426860488784731125497417640507220481, 22304269070532896717707344537995120070212833580943367087267197592645043797542,
  4128018831155263258921677689761735101256426860488784731125497417640507220481, 22304269070532896717707344537995120070212833580943367087267197592645043797542, 4128018831155263258921677689761735101256426860488784731125497417640507220481, 22304269070532896717707344537995120070212833580943367087267197592645043797542
]

/-- ⚑ Which entry of `step_keys` holds the REAL key. `wrap_main.ml:98-101` makes `step_keys` a
per-branch vector of the compiled STEP rules' verification keys; only one of them exists in this
tree, so the others are named fixtures. `mkWrapWith` witnesses branch `min 1 (branches − 1)`, and
`key_digest_is_the_index_digest` below is what would RED if the selection ever moved off it. -/
def KEY_REAL_BRANCH : Nat := 1

/-- Branch `i`'s coordinate `k`. ⚠ Only `KEY_REAL_BRANCH` is real; §2d names the rest. -/
def keyConst (i k : Nat) : Nat :=
  if i == KEY_REAL_BRANCH then STEP_VK_XY.getD k 0 else wrapFixture (64 + i) k

/-- Item tag for an index-sponge coordinate. -/
def T_INDEXPT : Nat := 9

/-- The index sponge's schedule: 56 absorbs of the CHOSEN key, then one full squeeze
(`Sponge.squeeze_field`, `wrap_verifier.ml:530`). -/
def keySchedule : List Ev :=
  (List.range KEY_COORDS).map (fun k => Ev.abs T_INDEXPT (keyConst KEY_REAL_BRANCH k))
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

/-- The index sponge's trajectory. `bt` is out of range, so no word is bent. -/
def keySponge (s : WrapShape) (sp : SpAcc) : SpAcc :=
  runSpongeQ (baseKeySp s sp) keySchedule (KEY_COORDS + 1) 0

/-- …and one with coordinate `k` bent by `+d`, for the red control. -/
def keySpongeBent (s : WrapShape) (sp : SpAcc) (k d : Nat) : SpAcc :=
  runSpongeQ (baseKeySp s sp) keySchedule k (qAdd (keyConst KEY_REAL_BRANCH k) d)

/-- `index_digest`'s VARIABLE — the squeeze's source cell. -/
def keyDigestVar (s : WrapShape) (sp : SpAcc) : PVar :=
  (((keySponge s sp).evs.filter (fun e => !e.isAbs)).getD 0 default).srcV
/-- …and its VALUE. -/
def keyDigestVal (s : WrapShape) (sp : SpAcc) : Nat :=
  (((keySponge s sp).evs.filter (fun e => !e.isAbs)).getD 0 default).val
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
  let ks := keySponge s t.sp
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
    [ ([some (keyDigestVar s t.sp), some ((t.sp.evs.getD 0 default).wordV), none], cEq) ]
  transcriptRowsQ (baseKeySp s t.sp) ks wired
  ++ packHalves (foldHalves ++ sealHalves ++ digestTie)

/-- W-KEY's variable environment. `acc k i` is `0` until the selected branch is reached and the
chosen coordinate after it, which is what a one-hot fold over constants computes. -/
def keyEnv (t : WrapData) : VarEnv :=
  let s := t.sh
  let kv := keyVars s (baseKey s t.sp)
  spongeEnv (baseKeySp s t.sp) (keySponge s t.sp)
  ++ (List.range KEY_COORDS).flatMap (fun k =>
      (List.range s.branches).map (fun i =>
        (kv.acc k i, ((if t.br.idx ≤ i then keyConst t.br.idx k else 0 : Nat) : Int))))

/-! ## §10 — W4, the CLOSING TIES, and the 40-word census.

⚑ **THE PUBLIC VECTOR IS THIS ASSEMBLY'S, NOT MINA'S, AND THE DIFFERENCE IS STATED.** Mina's wrap
circuits have `PRIMARY_LEN = WRAP_PRIMARY_LEN = 40`. `MinaWrapPublicInput` carries the slot-by-slot
layout, measured against a devnet block. Of those 40, this rung DERIVES:

    slot   word                                    here
    5–8    plonk.{alpha, beta, gamma, zeta}        ✅ the transcript's own four challenge squeezes,
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
    0–4    cip, b, ζ^srs_len, ζ^dom, perm          ✗ W-FINALIZE
    9      xi                                      ✗ W-FINALIZE
    12     messages_for_next_step_proof            ✅ at `w9_prev` ONLY (§18) — the
                                                      `Field.Assert.equal` of `wrap_main.ml:350-351`
                                                      against packed statement word 54, which the
                                                      x_hat MSM consumes as entry 64
    11     messages_for_next_wrap_proof            ✗ W-WRAPHACK (it hashes
                                                      `openings_proof.sg` with
                                                      `new_bulletproof_challenges`, and the latter is
                                                      W-FINALIZE's output — so word 11 needs BOTH)
    30–39  padding + the lookup Opt's challenge    ✗ (constant / feature-flag words)

**22 of 40 through `w8_ftcomm`, 23 at `w9_prev`.** Exposing all 40 would mean tying 17 words to
variables no row derives — public fixtures, which is defect class 5 wearing a public vector. So
`pubWords` is 22, `rungPub .prev` is 23, and this table is the census; §13 names what each missing
word costs.

⚑ **AND `w9_prev`'s WORD IS EXPOSED AT ONE RUNG, NOT AT ALL OF THEM.** `closingRows` emits
`pubWords` halves at `w4_bind` and `prevRows` emits the 23rd; `AUXW` reserves the slot at every rung
so that below `w9_prev` it sits in `placeChecked`'s DEAD GAP. That is the difference between a
public word a rung derives and a public word a rung inherits: exposing word 12 at `w4_bind` would
tie it to a cell nothing in `w4_bind` reads. `prev_rung_places_and_the_rung_below_it_does_not`
exhibits the refusal. -/

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
  ++ [ (match forkSqueeze t.sp with | some e => e.1 | none => .external 0) ]
  ++ (List.range (min s.ipaRounds (nChals s - 5))).map (fun r =>
       (chainVars s (cb + 1) (4 + r)).n s.emsRows)
  ++ [ (branchVars s (baseBr s t.sp)).packed ]
  |>.take s.pubWords

/-- One closing `Generic` half per public word: `external i = v`. This is the row that makes the
public word a READ one, so `placeChecked`'s `inertPublicWord` cannot fire silently. -/
def closingRows (t : WrapData) : List WRow :=
  packHalves ((List.range t.sh.pubWords).map (fun i =>
    (([ some (.external i : PVar), some ((exposedVars t).getD i (.external 0)), none
      ] : List (Option PVar)), cEq)))

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
def xhSel (s : WrapShape) : List Nat := xhatSel s.xhatTerms
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

/-- The x_hat region starts after the key sponge, so nothing below `w6_xhat` moves. -/
def baseXh (s : WrapShape) (sp : SpAcc) : Nat := baseKeySp s sp + (keySponge s sp).next
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
def nPrevVars (s : WrapShape) : Nat := PREV_WORDS + 2 * s.prevs

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

/-- The three deferred values, as FIXTURES — `plonk.perm`, `plonk.zeta_to_srs_length`,
`plonk.zeta_to_domain_size` are free witnesses here and checked by W-FINALIZE in the next proof. -/
def ftcSVal (j : Nat) : Nat := wrapFixtureQ 22 j

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

/-- `prev_step_accs.(p)`'s coordinate `j` — the TRANSCRIPT's own absorbed cell, because
`wrap_main.ml:412` hands `incrementally_verify_proof` the same vector `wrap_verifier.ml:538`
absorbs. -/
def sgOldVar (t : WrapData) (p j : Nat) : PVar :=
  ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_SGOLD)).getD (2 * p + j) default).wordV

/-- **W-PREV's ROWS.** Everything `wrap_main.ml:201-256` and `:350-351` cost, and nothing else. -/
def prevRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  -- (1) `Boolean.typ` on each `B Bool` word — the ONLY check the 57-word `typ` emits.
  let boolHalves : List (List (Option PVar) × List Int) :=
    (List.range XHAT_PREVS).map (fun p =>
      let v := prevW s sp (PREV_PER_PROOF_WORDS * p + PREV_SHOULD_FINALIZE)
      ([some v, some v, some v], cBool))
  -- (2) the public tie (`:350-351`) — `w9_prev`'s own public word, at slot `pubWords`.
  let pubTie : List (List (Option PVar) × List Int) :=
    [ ([some (.external s.pubWords : PVar), some (prevW s sp PREV_MSG_NEXT_STEP), none], cEq) ]
  -- (3) `assert_on_curve` on each `prev_step_accs` point, over the transcript's `sg_old` cells.
  let curveHalves : List (List (Option PVar) × List Int) :=
    (List.range s.prevs).flatMap (fun p =>
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
  ++ (List.range s.prevs).flatMap (fun p =>
      let x := itemVal T_SGOLD (2 * p)
      [ (prevSq s sp p 0, (qMul x x : Int))
      , (prevSq s sp p 1, (qMul (qMul x x) x : Int)) ])

/-! ## §7 — rows, environment, rungs. -/

inductive Rung where
  | transcript | challenges | branch | bind | key | xhat | split | ftcomm | prev
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "w1_transcript" | .challenges => "w2_challenges"
  | .branch => "w3_branch" | .bind => "w4_bind" | .key => "w5_key"
  | .xhat => "w6_xhat" | .split => "w7_split" | .ftcomm => "w8_ftcomm"
  | .prev => "w9_prev"

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
    ∧ rungRows t .prev wired = rungRows t .ftcomm wired ++ rungOwn t wired .prev :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
      = (rungRows t .ftcomm wired).length + (rungOwn t wired .prev).length := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rungRows_is_a_ladder t wired
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h4]
  · simp [h5]
  · simp [h6]
  · simp [h7]
  · simp [h8]

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at it — and `pubWords + 1` at
`w9_prev`, whose own row ties `messages_for_next_step_proof` (`wrap_main.ml:350-351`). ⚑ The extra
slot is RESERVED in `AUXW` at every rung, so below `w9_prev` it sits in `placeChecked`'s dead gap and
any gate that touched it would be refused rather than silently absorbed. -/
def rungPub (s : WrapShape) : Rung → Nat
  | .bind => s.pubWords
  | .key => s.pubWords
  | .xhat => s.pubWords
  | .split => s.pubWords
  | .ftcomm => s.pubWords
  | .prev => s.pubWords + 1
  | _ => 0

/-- The variables rung `k` exposes as public words. ⚑ `w9_prev` appends ONE — packed statement word
`PREV_MSG_NEXT_STEP`, the MSM's entry 64 — and no rung below it may, because below `w6_xhat` no row
reads that cell and a public word on an unread cell is a public fixture. -/
def exposedVarsAt (t : WrapData) (k : Rung) : List PVar :=
  exposedVars t ++ (match k with
    | .prev => [prevW t.sh t.sp PREV_MSG_NEXT_STEP]
    | _ => [])

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
      | _ => [])

/-- The closing rung's environment — what `w8_ftcomm` sees, i.e. everything. -/
def circuitEnv (t : WrapData) : VarEnv := circuitEnvAt t .prev

/-- The full environment: the circuit's variables, then the public words, whose values are READ OUT
of the circuit env at the exposed variables — so a public word and the variable its closing row ties
it to hold ONE value by construction, exactly as a copy class does. -/
def wrapEnvAt (t : WrapData) (k : Rung) : VarEnv :=
  let ce := circuitEnvAt t k
  let ix := envIndex ce
  ce ++ (List.range (rungPub t.sh k)).map (fun i =>
    ((.external i : PVar), envLookupAt ix ((exposedVarsAt t k).getD i (.external 0))))

def wrapEnv (t : WrapData) : VarEnv := wrapEnvAt t .prev

def wrapPublicAt (t : WrapData) (k : Rung) : List Int :=
  let ix := envIndex (circuitEnvAt t k)
  (List.range (rungPub t.sh k)).map (fun i =>
    envLookupAt ix ((exposedVarsAt t k).getD i (.external 0)))

def wrapPublic (t : WrapData) : List Int := wrapPublicAt t .prev

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

/-- The closing rung's witness — kept for callers that do not carry a `Rung`. -/
def wrapWitness (t : WrapData) (pubSize : Nat) (rows : List WRow) : List (List Int) :=
  wrapWitnessAt t .prev pubSize rows

def rungJson (t : WrapData) (k : Rung) (wired : Bool) (name : String) : String :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderWrapCircuit name p (p + rows.length)
    (placedOf t.sh p (wrapGates rows)) (wrapWitnessAt t k p rows)
    (if p == 0 then [] else wrapPublicAt t k) (rungProbeRows t k)

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
  , branches := 5, pubWords := 22, xhatTerms := XHAT_TERMS_FULL
  -- ⚑ `xhatOut XHAT_TERMS_FULL`, and `EmitWrapMainJson` re-derives it and REFUSES on disagreement
  -- at every emission. Not closed in the kernel: 1805 five-bit chunks is 3.6 s compiled and far
  -- more reduced, and this file has no `native_decide`.
  , xhatXY :=
      (24946197319037634231440770924058307246402971142903096884297069648301688224485,
       16382596241194855030609766549760651138786638147061512510866706509908262255965) }

/-- A small shape for the in-CI `#guard`s (the committed one is emitted by the driver). -/
def shapeSmoke : WrapShape :=
  { prevs := 2, ipaRounds := 3, wComms := 3, tComms := 2, emsRows := 8
  , branches := 3, pubWords := 6
  -- ⚑ FIVE ENTRIES, and `xhatSel` makes them `[0, 1, 11, 64, 31]` — a 255-bit `B Field` value, its
  -- 1-bit parity, a 128-bit challenge, the `messages_for_next_step_proof` DIGEST and
  -- `should_finalize`. That reaches BOTH partitions, all three widths, both top-zero counts (1 and
  -- 3) and both `Cond_add` branches (§15's `xhat_smoke_selection…`). A PREFIX of five would have
  -- been five 255-bit-or-parity entries and no 128-bit ladder at all. ⚑ Entry 64 is here because
  -- `w9_prev` exposes its packed word as a PUBLIC one, and a public word whose cell the MSM never
  -- reads is a public fixture.
  , xhatTerms := 5
  -- ⚑ `xhatOut 5`, closed by `rfl` IN THE KERNEL by `xhat_smoke_shape_absorbs_the_msm_output`.
  , xhatXY :=
      (16939429680523055563406117440808118430703004205774435970856079172456077167531,
       12956915833716130635753754766705188581923939059745973521002626957608324504831) }


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

/-- ⚑ `ENDO_Q` against an INDEPENDENT source, both directions, and its defining algebraic property.

  * it IS `MinaRealBlockTranscript.ENDO_R`, arrived at by reproducing a real Mina Wrap proof's own
    α, ζ, v and u;
  * it is NOT the step side's `Endo.Wrap_inner_curve.scalar`, which lives in Fp
    (`bindings_js_test.ml:588-592`) — conflating the two is the `MinaWrapFtEval0Weld` defect, in the
    direction nothing had tested;
  * nor `Endo.Wrap_inner_curve.base`, the Fq element `wrap_verifier.ml:944`/`:121` uses for the CURVE
    endomorphism (`bindings_js_test.ml:583-587`). Both are Fq; only one is a scalar;
  * and it is a NONTRIVIAL cube root of unity in Fq — the property `endo_scalar` HAS
    (`poly-commitment/src/srs.rs:44-60`), checked rather than assumed. -/
theorem endo_q_is_pallas_endo_scalar :
    (ENDO_Q : Nat) = (Dregg2.Circuit.Emit.MinaRealBlockTranscript.ENDO_R).val
    ∧ ENDO_Q ≠ 8503465768106391777493614032514048814691664078728891710322960303815233784505
    ∧ ENDO_Q ≠ 2942865608506852014473558576493638302197734138389222805617480874486368177743
    ∧ qMul (qMul ENDO_Q ENDO_Q) ENDO_Q = 1
    ∧ ENDO_Q ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

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
/-- ⚑ `Branch_data.Checked.pack` against a REAL devnet Wrap proof's own public word 29, and the
0/2/3 mask shape at all three legal widths. A `[1;0]` mask — the packing `0/1/2` would produce — is
NOT reachable from `ones_vector ∘ rev`, which is exactly why `Prefix_mask.back` can `invalid_arg` on
it out of circuit and no gate refuses it in one. -/
theorem branch_data_packing_matches_a_real_wrap_proof :
    Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0 = 67
    ∧ branchDataPacked 3 16 = Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
    ∧ (runBranch shapeSmoke 2 [0,1,2] [16,16,16]).packedV
        = Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
    ∧ (List.range 3).map (fun w => maskBit 2 w 0 + 2 * maskBit 2 w 1) = [0, 2, 3]
    ∧ (runBranch shapeSmoke 0 [0,1,2] [16,16,16]).packedV = 64
    ∧ (runBranch shapeSmoke 1 [0,1,2] [16,16,16]).packedV = 66 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### §11d — the field itself.

A wrap emission whose values were reduced mod `pN` would be accepted by nothing; this is the
tripwire that says which field the file is in.

⚑ **CONVERTED FROM FOUR `#guard`s.** They were four closed instances evaluated by
`unsafe evalExpr Bool`, leaving no term and invisible to the `#assert_namespace_axioms` sweep at the
foot of this file — a `native_decide` with the name, the term and the axiom record deleted. The
facts are pure `Fq` arithmetic on 254-bit literals and `decide` closes every one in the kernel, so
being guards bought nothing and cost the axiom accounting. -/

/-- **THE FIELD IS `Fq`, AND `Fq` IS A FIELD.** `qN ≠ pN` is the tripwire that says which of the two
Pasta primes this file reduces by — a wrap emission reduced mod `pN` is the one mistake that would
be accepted by nothing and visible in nothing. The other three are the ring identities the emitter
relies on every time it writes a negative coefficient as `qSub 0 k`. -/
theorem the_field_is_fq_and_wraps :
    qN ≠ pN
    ∧ qAdd (qN - 1) 1 = 0
    ∧ qMul (qN - 1) (qN - 1) = 1
    ∧ qSub 0 1 = qN - 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §12 — the in-CI PINS on the smoke instance (`#guard`, interpreter-reduced).

Nullary `def`s so the interpreter evaluates the chains ONCE. -/

def tW : WrapData := mkWrap shapeSmoke
def rowsW : List WRow := rungRows tW .bind true
def rowsUW : List WRow := rungRows tW .bind false
def nRowsW : Nat := rowsW.length
def gatesW : List PGate := wrapGates rowsW
def placedW : List PlacedGate := placedOf shapeSmoke shapeSmoke.pubWords gatesW
/-- ⚑ At `.bind`, not at the closing rung: `rowsW` IS the `w4_bind` row list, and asking for the
`w6_xhat` environment here would make every §12 guard reduce §15's ladders for cells no `w4_bind`
row has. That is the measurement that cost this module its build. -/
def gridW : List (List Int) := wrapWitnessAt tW .bind shapeSmoke.pubWords rowsW

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

/-- ⚑ **The four challenges and the digest of a REAL accepted proof, out of THIS file's emitter.**
Closed in the KERNEL, so this is strictly stronger than the `#guard`s it replaces
(`metatheory/docs/GUARD-DISCIPLINE.md`) and it is a term later work can cite. -/
theorem real_transcript_reproduces_the_accepted_proof :
    realChals.getD 0 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
    ∧ realChals.getD 1 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
    ∧ realChals.getD 2 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
    ∧ realChals.getD 3 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL
    ∧ realDigest = Dregg2.Circuit.Emit.PastaPoseidonFq.FQDIGEST := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ RED CONTROL. Bending ONE absorbed word of that tape moves ALL FOUR challenges and the digest
— which is what makes the pins above a measurement of the derivation rather than of five
constants. -/
def realBent : SpAcc :=
  runSpongeQ 0 realTapeSchedule 3 (qAdd (Dregg2.Circuit.Emit.PastaPoseidonFq.fqTape.getD 3 0) 1)
def realBentChals : List Nat := (chalSqueezes realBent).map (fun e => e.2 % 2 ^ 128)
theorem real_transcript_bends_on_one_absorbed_word :
    realBentChals.getD 0 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
    ∧ realBentChals.getD 1 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
    ∧ realBentChals.getD 2 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
    ∧ realBentChals.getD 3 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

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
#guard WRAP_UNCONSUMED.length == 8
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
/-- ⚑ **THE `w4_bind` RUNG EMITS NO CURVE GATE, AND ITS TWO STRUCTURED FAMILIES RUN IN WHOLE
BLOCKS.** Poseidon rows come in 11-row permutations — the run-length family the conformance diff
compares — and `EndoMulScalar` in 8-row chains; a partial block would mean a permutation or a
`to_field_checked` chain was emitted half-open. ⚠ The curve families are zero HERE and non-zero from
`w6_xhat` up (`xhat_gate_census`, `ftc_gate_census`); this is the closing rung's census, not the
file's. -/
theorem bind_rung_gate_census :
    (rowsW.filter (fun r => r.kind == KGateType.varBaseMul)).length = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.endoMul)).length = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.completeAdd)).length = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.poseidon)).length % 11 = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.endoMulScalar)).length % 8 = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### §12h — the emitted circuit is well-formed for the harness. -/

/-- ⚑ Every placed gate carries exactly `K_PERMUTS` wires, every witness column is as long as the
public words plus the rows, and every gate's `typ` ordinal is one of the seven kimchi kinds the
harness can deserialise. A violation of any of these is a JSON the Rust prover would reject at parse
time rather than a circuit it would refuse — which is why it is checked here and not there. -/
theorem bind_rung_is_well_formed_for_the_harness :
    placedW.all (fun g => g.wires.length == K_PERMUTS) = true
    ∧ gridW.all (fun col => col.length == shapeSmoke.pubWords + nRowsW) = true
    ∧ placedW.all (fun g => g.kind.ordinal < 7) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ### §14b — ⚑ **W-KEY'S PINS, AS NAMED THEOREMS.**

`metatheory/docs/GUARD-DISCIPLINE.md`: a fact worth asserting is worth naming, and where the KERNEL
can reach it, `rfl`/`decide` is strictly stronger than the `#guard` would have been. Every fact below
is kernel-clean — `#assert_namespace_axioms` at the foot of the file accounts for all of them, and
none of them is a `native_decide` oracle. -/

/-- The smoke instance, materialised once so the interpreter and the kernel share one term. -/
def tKey : WrapData := mkWrap shapeSmoke

/-- The flattening's SHAPE — `Permuts.n = 7`, `Columns.n = 15`, six singletons, 28 points, and a
fixture list that is exactly `~g`'s output length and not a truncation of it. -/
theorem key_index_shape :
    KEY_SIGMA = 7 ∧ KEY_COLS = 15 ∧ KEY_SINGLES = 6
    ∧ KEY_POINTS = 28 ∧ KEY_COORDS = 56 ∧ STEP_VK_XY.length = KEY_COORDS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- ⚠ Seven of the 28 commitments are the identity, so 14 of the 56 coordinates are `0` — a
property of the small generic-only index the fixture came from, recorded because a model that
SKIPPED infinity instead of absorbing `(0,0)` would produce a different digest silently
(`poseidon/src/sponge.rs:332-345`). -/
theorem key_index_carries_the_identity_points :
    (STEP_VK_XY.filter (fun x => x == 0)).length = 14 := by decide

/-- The index sponge is 56 absorbs and ONE squeeze — `wrap_verifier.ml:524-530`'s `Array.iter … ~f:
Sponge.absorb` then `Sponge.squeeze_field`, at rate 2, which is 28 permutations. -/
theorem key_sponge_schedule :
    ((keySponge shapeSmoke tKey.sp).evs.filter (fun e => e.isAbs)).length = KEY_COORDS
    ∧ ((keySponge shapeSmoke tKey.sp).evs.filter (fun e => !e.isAbs)).length = 1
    ∧ ((keySponge shapeSmoke tKey.sp).evs.filter (fun e => e.didPerm)).length = 28 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- ⚑⚑ **THE REALITY GATE, AND THE POINT OF THE WHOLE RUNG.** Driving THIS FILE'S OWN Fq sponge
over the 56 coordinates of a REAL `VerifierIndex`, in `index_to_field_elements` order, reproduces the
digest that RUST KIMCHI computed for that index (`verifier_index.rs:407-533`) — recorded in
`PastaPoseidonFq.VKDIGEST` before this sub-circuit existed, and re-derived a third time by the
extractor's independent `absorb_fq` replay. Two implementations, three computations, one number.

⚑ **So the wrap transcript's first absorbed item is DERIVED here, not fixtured.** -/
theorem key_digest_is_the_index_digest :
    keyDigestVal shapeSmoke tKey.sp = Dregg2.Circuit.Emit.PastaPoseidonFq.VKDIGEST := by rfl

/-- …and it is the value the TRANSCRIPT absorbs first (`wrap_verifier.ml:537`), so `RC_DIGEST` is no
longer standing in for anything: the tie row in `keyRows` puts the two in one σ class and this puts
them at one value. -/
theorem key_digest_is_the_transcript_input :
    itemVal T_DIGEST 0 = keyDigestVal shapeSmoke tKey.sp := by rfl

/-- ⚑ **RED CONTROL — the digest is a function of EVERY coordinate.** Bending any one of the 56
inputs by `+1` moves it, including one of the 14 that are `0` (an identity commitment's fake point:
absorbing it is not a no-op) and the last one. Without this the theorem above is a number agreeing
with a number. -/
theorem key_digest_bends_at_every_probed_coordinate :
    [0, 20, 41, 55].all (fun k =>
      keyDigestValOf (keySpongeBent shapeSmoke tKey.sp k 1)
        != Dregg2.Circuit.Emit.PastaPoseidonFq.VKDIGEST) = true := by rfl

/-- ⚑ **AND THE ONE-HOT SELECTION MATTERS.** `choose_key` at a DIFFERENT branch produces a different
key and therefore a different `index_digest`; the real key is at `KEY_REAL_BRANCH` and
`mkWrapWith` witnesses exactly that branch. If the witnessed branch ever moved off it, the reality
gate above would red rather than quietly digest a fixture. -/
theorem key_selection_is_the_branch_selection :
    tKey.br.idx = KEY_REAL_BRANCH
    ∧ (mkWrap shapeWrap).br.idx = KEY_REAL_BRANCH
    ∧ (List.range KEY_COORDS).all (fun k => keyConst KEY_REAL_BRANCH k == STEP_VK_XY.getD k 0) = true
    ∧ ((List.range KEY_COORDS).filter (fun k => keyConst 0 k != STEP_VK_XY.getD k 0)).length = 56 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

/-- ⚑ **DEFECT CLASS 1 IN A NEW PLACE: the index sponge's INITIAL STATE IS PINNED.**
`Sponge.create sponge_params` (`wrap_verifier.ml:522`) starts at the zero state. Leaving those three
lanes free witnesses would let a prover choose `index_digest` outright — the same shape as the step
side's free `acc₀`/`n₀` (`plonk_curve_ops.ml:157-158`). `transcriptRowsQ`'s two `init` rows pin all
three by `Generic` constant halves, and this reads them off the EMITTED rows. -/
theorem key_sponge_seed_is_pinned :
    ((keyRows tKey true).getD 0 default).coeffs = cConst 0 ++ cConst 0
    ∧ ((keyRows tKey true).getD 1 default).coeffs = cConst 0 ++ cNil
    ∧ ((keyRows tKey true).getD 0 default).kind = KGateType.generic
    ∧ ((keyRows tKey true).getD 1 default).kind = KGateType.generic := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **DEFECT CLASS 3, MOVED BY ONE.** `index_digest` leaves `WRAP_UNCONSUMED`, and it leaves because
a row reads it — not because the entry was deleted. The other eight stay, unpadded. -/
theorem key_closes_one_unconsumed_entry :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED.contains
        "index_digest — needs W-KEY (choose_key over the per-branch step VKs)" = false
    ∧ WRAP_UNCONSUMED.head?
        = some "sg_old — ON-CURVE at w9_prev (§18); its consumer is W-COMBINE's ~init" := by
  refine ⟨rfl, ?_, rfl⟩
  decide

/-- The `w5_key` rung is a strict superset of `w4_bind` and its length is the sum of its parts — the
§12b shape, so a dropped `keyRows` is a red and not a silence. -/
theorem key_rung_is_a_ladder_step :
    (rungRows tKey .key true).length
      = (rungRows tKey .bind true).length + (keyRows tKey true).length
    ∧ (rungRows tKey .bind true).length < (rungRows tKey .key true).length
    ∧ rungPub shapeSmoke .key = shapeSmoke.pubWords := by
  refine ⟨rfl, ?_, rfl⟩
  decide

/-- The WIRED and UNWIRED `w5_key` circuits differ ONLY in the probe rows' permutation columns —
the control that makes "rejected" mean "rejected BY THE WIRE" at this rung too. -/
theorem key_rung_control_differs_only_in_probes :
    (rungRows tKey .key true).length = (rungRows tKey .key false).length
    ∧ ((rungRows tKey .key true).zip (rungRows tKey .key false)).all
        (fun p => p.1.kind == p.2.kind && p.1.coeffs == p.2.coeffs && p.1.probe == p.2.probe) = true
    ∧ (((rungRows tKey .key true).zip (rungRows tKey .key false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tKey .key true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, rfl, rfl⟩

/-- `placeChecked` ACCEPTS the `w5_key` rung and no public word is inert — the fail-closed placement
still holds with W-KEY's 56 folds and its second sponge in the grid. -/
theorem key_rung_places :
    refusalOf shapeSmoke shapeSmoke.pubWords (wrapGates (rungRows tKey .key true)) = none
    ∧ inertPublicWords shapeSmoke.pubWords (wrapGates (rungRows tKey .key true)) = []
    ∧ (placedOf shapeSmoke shapeSmoke.pubWords (wrapGates (rungRows tKey .key true))).length
        = shapeSmoke.pubWords + (rungRows tKey .key true).length := by
  refine ⟨rfl, rfl, rfl⟩

/-- W-KEY's Poseidon rows come in 11-row permutations, and it adds NO curve gate — `choose_key` over
`Inner_curve.constant` keys is `Generic` arithmetic, which is the substantive reading of
`wrap_main.ml:218-219` and the reason this sub-circuit is cheap. -/
theorem key_rows_are_generic_and_poseidon_only :
    ((keyRows tKey true).filter (fun r => r.kind == KGateType.poseidon)).length = 28 * 11
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.varBaseMul)).length = 0
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.endoMul)).length = 0
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.completeAdd)).length = 0
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.endoMulScalar)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### §15f — ⚑ **W-XHAT'S PINS, AS NAMED THEOREMS.**

Read off the EMITTED row list wherever the claim is about a row. Every one is kernel-clean and
accounted for by `#assert_namespace_axioms` below; there are no new `#guard`s in this section.

⚠ These reduce the smoke instance's x_hat rows, which is 77 five-bit chunks of Vesta ladder in the
kernel. That is the reason there are NINE of them and not thirty: each one is a real reduction of
the same object, and the marginal fact is not worth the marginal minute. MEASURED — the nine cost
+0.55 GiB of peak elaboration RSS (8.64 → 9.19 GiB) and no wall time at all. -/

/-- The smoke instance's W-XHAT rows, materialised once so the pins share one term. -/
def xhRows : List WRow := xhatRows tKey true

/-- Does the emitted row list contain the `Generic` constant pin `vx = p.1`, `vy = p.2`?

⚑ Deliberately compares `kind` / `perm` / `coeffs` and NOT the whole row. `WRow` carries the
`advice` cells, and a structural equality on a `CompleteAdd` row forces `caWitnessQ` — three `qInv`
apiece — for every row against every candidate. Written as `List.contains` this one theorem took the
file from 150 s and ~1 GB to 9.7 GB and unfinished. The pin is about the CONSTRAINT, and the
constraint is the gate kind, the wires and the coefficients. -/
def xhHasConstRow (vx vy : PVar) (p : Nat × Nat) : Bool :=
  let r := ptConstRow vx vy p
  xhRows.any (fun w => w.kind == r.kind && w.perm == r.perm && w.coeffs == r.coeffs)

/-- ⚑ **THE MEMO'S OBLIGATION, IN THE KERNEL.** `shapeSmoke.xhatXY` — the pair `schedule` hands the
transcript at `wrap_verifier.ml:617` — IS §15's MSM output. Without this the field would be a
fixture with a good docstring. (The wrap shape's copy is discharged by `EmitWrapMainJson`'s refusal
at every emission; 1805 chunks is out of the kernel's reach and this file has no `native_decide`.) -/
theorem xhat_smoke_shape_absorbs_the_msm_output :
    shapeSmoke.xhatXY = xhatOut shapeSmoke.xhatTerms := by rfl

/-- ⚑ **AND IT IS A DIFFERENT OBJECT FROM THE ONE THIS FILE USED TO ABSORB.** `RC_XHAT` is a real
accepted proof's public-input commitment, which stood in for `x_hat` through five rungs. The derived
pair is not it — so `w6_xhat` changed the transcript rather than confirming it, and every challenge
below the absorb moved. Saying that out loud is the point: a rung that "derives" a value it already
had would be deriving nothing. -/
theorem xhat_derived_is_not_the_old_fixture :
    shapeSmoke.xhatXY.1 ≠ RC_XHAT.getD 0 0 ∧ shapeSmoke.xhatXY.2 ≠ RC_XHAT.getD 1 0
    ∧ shapeWrap.xhatXY.1 ≠ RC_XHAT.getD 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **DEFECT CLASS 1, IN A NEW PLACE AND IN THE PLACE THE STEP SIDE FOUND IT.**
`scale_fast_unpack` opens `let acc = ref (add_fast base base)` / `let n_acc = ref Field.zero`
(`plonk_curve_ops.ml:157-158`). Doubling is a bijection on the group, so a FREE `acc₀` lets a prover
steer the ladder's output to any point at all, and a free `n₀` lets him choose which bit vector the
ladder actually multiplied by. Per ladder this reads BOTH off the emitted rows: a `CompleteAdd` whose
two input point-pairs are the base's own cells and whose output is `acc₀`, and a `Generic` half
pinning `n₀` to zero. -/
theorem xhat_every_ladder_seed_is_pinned :
    (xhLadders shapeSmoke).all (fun k =>
      xhRows.any (fun w => w.kind == KGateType.completeAdd
        && w.perm == [ some (xA shapeSmoke tKey.sp k 0), some (xA shapeSmoke tKey.sp k 1)
                     , some (xA shapeSmoke tKey.sp k 0), some (xA shapeSmoke tKey.sp k 1)
                     , some (xAccX shapeSmoke tKey.sp k 0), some (xAccY shapeSmoke tKey.sp k 0)
                     , none ])
      && xhRows.any (fun w => w.kind == KGateType.generic
           && w.perm.contains (some (xCnt shapeSmoke tKey.sp k 0))
           && w.coeffs.contains 0)) = true := by decide

/-- ⚑ **DEFECT CLASS 2, BOTH HALVES, INSIDE THE LADDER.** `scale_fast2` asserts the top bits of
`s_div_2` zero (`plonk_curve_ops.ml:262-265`) — ONE bit at width 255 and THREE at width 128, because
a 128-bit entry's ladder actually runs at 130. Those cells live in chunk 0's NEXT row, which in the
`VarBaseMul` witness layout is ADVICE; an advice cell is in no σ class and cannot be asserted. This
says the emitter moved every one of them into a PERMUTATION column AND that a `Generic` half pins it
to zero. Emitting the split without them is the containment §13 refused to ship. -/
theorem xhat_top_bits_are_range_checked :
    (xhLadders shapeSmoke).all (fun k =>
      (List.range (xhatTopZeros (xhAt shapeSmoke k))).all (fun tt =>
        xhRows.any (fun w => w.kind == KGateType.zero
          && w.perm.contains (some (xZb shapeSmoke tKey.sp k tt)))
        && xhRows.any (fun w => w.kind == KGateType.generic
             && w.perm.contains (some (xZb shapeSmoke tKey.sp k tt))))) = true
  ∧ ((xhLadders shapeSmoke).map (fun k => xhatTopZeros (xhAt shapeSmoke k))) = [1, 3, 1] := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **DEFECT CLASS 4: NO BASE IS A FREE WITNESS.** Every entry's base — and every correction, and
`Generators.h` — is pinned by a `Generic` constant row to the value `MinaStepSrsLagrange` holds.
Before this rung the wrap side emitted no curve base at all; the step side's R3 spent a night with
all forty free.

⚠ SAY THE PIN'S REACH EXACTLY. `MinaStepSrsLagrangePin` closes `SRS::<Pallas>::create(16).g` against
the devnet blockchain Wrap SRS's **first sixteen generators, thirty-two coordinates**, by `decide`.
It does NOT observe the Vesta basis these bases actually come from (depth 65536); what it
establishes is that `SRS::create` — the one deterministic generic function both halves go through —
reproduces Mina's generators where an independent devnet dump exists to check it against. The step
from there to `LAGRANGE_XY` is an argument about that function, not a checked equality, and the pin
module says so in its own header. -/
theorem xhat_every_base_and_correction_is_pinned :
    (List.range (xhN shapeSmoke)).all (fun k =>
      xhHasConstRow (xA shapeSmoke tKey.sp k 0) (xA shapeSmoke tKey.sp k 1)
        (xhatBase (xhAt shapeSmoke k))) = true
  ∧ (xhLadders shapeSmoke).all (fun k =>
      xhHasConstRow (xA shapeSmoke tKey.sp k 2) (xA shapeSmoke tKey.sp k 3)
        (xhatCorr (xhAt shapeSmoke k))) = true
  ∧ xhHasConstRow (xhHVar shapeSmoke tKey.sp).1 (xhHVar shapeSmoke tKey.sp).2 XHAT_H = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE CLOSING TIE.** `x_hat blinding`'s `CompleteAdd` writes its output into the very cells the
transcript absorbs at `wrap_verifier.ml:617` — not a σ class BETWEEN two variables but the same two
variables, which is the strongest form the tie can take. So the sponge cannot be fed an `x_hat` the
MSM did not produce. -/
theorem xhat_output_is_the_absorbed_word :
    ((xhRows.filter (fun w => w.kind == KGateType.completeAdd)).getLast?.map (fun w =>
        (w.perm.getD 4 none, w.perm.getD 5 none)))
      = some
          (some ((tKey.sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 0 default).wordV,
           some ((tKey.sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 1 default).wordV)
    := by decide

/-- ⚑ **DEFECT CLASS 3: THE CENSUS DID NOT MOVE, AND THE ENTRY SAYS WHY.** `x_hat` is still on
`WRAP_UNCONSUMED` because W-XHAT's 67 scalars are `exists ~request:Req.Proof_state`'s free witnesses
(§2c, §15c). Eight entries before this rung, eight after. -/
theorem xhat_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED.getD 1 ""
        = "x_hat — MSM EMITTED at w6_xhat (§15); its 67 SCALARS are W-PREV's packed statement \
           words, and 64 of them are still free" := by
  refine ⟨rfl, ?_⟩
  decide

/-- The `w6_xhat` rung is a strict superset of `w5_key` and its length is the sum of its parts, the
WIRED and UNWIRED circuits differ ONLY in the probe rows' permutation columns, and `placeChecked`
accepts it with no inert public word. §12b's shape, at the rung that first emits curve gates. -/
theorem xhat_rung_is_a_ladder_step_and_places :
    (rungRows tKey .xhat true).length
      = (rungRows tKey .key true).length + xhRows.length
    ∧ (rungRows tKey .key true).length < (rungRows tKey .xhat true).length
    ∧ (((rungRows tKey .xhat true).zip (rungRows tKey .xhat false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tKey .xhat true).filter (fun r => r.probe)).length
    ∧ refusalOf shapeSmoke shapeSmoke.pubWords (wrapGates (rungRows tKey .xhat true)) = none
    ∧ inertPublicWords shapeSmoke.pubWords (wrapGates (rungRows tKey .xhat true)) = [] := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  decide

/-- ⚑ **THE GATE CENSUS OF THE SUB-CIRCUIT.** Two rows per five-bit chunk (`VarBaseMul` + its `Zero`
tail, `varbasemul.rs:135-140`), and a `CompleteAdd` for every `add_fast` upstream makes: one seed and
one `G.negate` adjust and one fold add per ladder, one per `Cond_add`, `m − 1` for the correction
reduce, and one for `x_hat blinding`. A row-set that quietly stopped emitting one of them reds
here rather than in a conformance report six weeks out. -/
theorem xhat_gate_census :
    (xhRows.filter (fun r => r.kind == KGateType.varBaseMul)).length
      = xhTotalChunks shapeSmoke
    ∧ (xhRows.filter (fun r => r.kind == KGateType.completeAdd)).length
      = 3 * (xhLadders shapeSmoke).length
        + (xhN shapeSmoke - (xhLadders shapeSmoke).length)
        + ((xhLadders shapeSmoke).length - 1) + 1
    ∧ (xhRows.filter (fun r => r.kind == KGateType.poseidon)).length = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### §16b — ⚑ **W-SPLIT'S PINS, AS NAMED THEOREMS.**

Every claim §16 makes about a ROW is read off the emitted row list, and the two claims it makes
about upstream's ARITHMETIC are closed in the kernel rather than asserted in prose. No new `#guard`s. -/

/-- The smoke instance's W-SPLIT rows, materialised once so the pins share one term. -/
def spRows : List WRow := splitRows tKey true

/-- W-PREV's own row-set at the smoke shape. ⚑ Same `WrapData` as §14b/§15f/§16b's — the rungs share
one shape and one sponge trajectory; a second `mkWrap` here would re-run the whole transcript. -/
def tPrev : WrapData := tKey
def prRows : List WRow := prevRows tPrev true

/-- ⚑ Does `rows` carry the `Generic` HALF `(vs, c)` — in EITHER slot of the double gate?
`packHalves` fills cols 0,1,2 with the first half and 3,4,5 with the second, so a pin written
against `perm.take 3` alone would silently miss every half that landed in the second slot. It is the
HALF that is the constraint, and both slots are the same constraint. -/
def hasHalf (rows : List WRow) (vs : List (Option PVar)) (c : List Int) : Bool :=
  rows.any (fun w => w.kind == KGateType.generic
    && ((w.perm.take 3 == vs && w.coeffs.take 5 == c)
        || ((w.perm.drop 3).take 3 == vs && (w.coeffs.drop 5).take 5 == c)))

/-- ⚑ **THE SELECTION FINDS EXACTLY THE `` `Field `` WORDS.** The wrap shape's ten `split_field`
calls are `wrap_main.ml:409` applied to the five `B Field` words of each of the two `per_proof`
blocks; the smoke shape's four-entry spread carries exactly one of those pairs, at positions
`(0, 1)`. A shape that selected a value half without its parity would contribute NO pair, which is
what makes this a pin on the WIDTH TABLE rather than on a hand-copied index list. -/
theorem split_pairs_are_the_field_words :
    splitPairs shapeSmoke = [(0, 1)]
    ∧ (splitPairs shapeWrap).length = 10
    ∧ (splitPairs shapeWrap).map (fun p => xhAt shapeWrap p.1)
        = [0, 2, 4, 6, 8, 32, 34, 36, 38, 40] := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE TIE IS TO §15's ENTRY SCALARS, NOT TO FRESH CELLS.** For every pair, the emitted row
list carries the half whose three permutation variables are `(x, y, is_odd)` with `y` and `is_odd`
the MSM entry scalars `xA k 4` and `xA k' 4` at `cSplit 1` — i.e.
`Field.Assert.equal ((of_int 2 * y) + is_odd) x`. This is the whole of W-SPLIT's content and it is
read off the ROWS. -/
theorem split_ties_the_msm_entry_scalars :
    ((splitPairs shapeSmoke).zip (List.range (splitPairs shapeSmoke).length)).all (fun pa =>
      hasHalf spRows [some (xSplitW shapeSmoke tKey.sp pa.2),
                      some (xA shapeSmoke tKey.sp pa.1.1 4),
                      some (xA shapeSmoke tKey.sp pa.1.2 4)] (cSplit 1)) = true := by
  rfl

/-- ⚑ **THE PARITY IS BOOLEAN-CONSTRAINED TWICE, AND BOTH ARE UPSTREAM'S.** `exists Typ.(field *
Boolean.typ)` in `split_field` is this section's; `assert_ (Constraint.boolean b)` at
`wrap_verifier.ml:573-576` is §15's `` `Cond_add `` arm. Emitting one would be LESS strict than
`wrap_main`, so the pin is that BOTH row lists carry the half — not that one does. -/
theorem split_parity_is_boolean_in_both_sections :
    hasHalf spRows [some (xA shapeSmoke tKey.sp 1 4), some (xA shapeSmoke tKey.sp 1 4),
                    some (xA shapeSmoke tKey.sp 1 4)] cBool = true
    ∧ hasHalf xhRows [some (xA shapeSmoke tKey.sp 1 4), some (xA shapeSmoke tKey.sp 1 4),
                      some (xA shapeSmoke tKey.sp 1 4)] cBool = true := by
  refine ⟨rfl, rfl⟩

/-- W-SPLIT spends `Generic` halves and σ-probes and NOTHING else — `split_field` has no curve op,
no sponge and no lookup. A row family appearing here would mean the gadget was read wrong. -/
theorem split_rows_are_generic_and_probe_only :
    ((splitRows tKey true).filter (fun r => r.kind == KGateType.generic)).length = 1
    ∧ ((splitRows tKey true).filter (fun r => r.probe)).length = 1
    ∧ ((splitRows tKey true).filter (fun r => r.kind == KGateType.varBaseMul)).length = 0
    ∧ ((splitRows tKey true).filter (fun r => r.kind == KGateType.completeAdd)).length = 0
    ∧ ((splitRows tKey true).filter (fun r => r.kind == KGateType.poseidon)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The `w7_split` rung is a strict superset of `w6_xhat`, its length is the sum of its parts, and
the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns — the property
that makes the harness's control byte-identical everywhere else. -/
theorem split_rung_extends_xhat :
    (rungRows tKey .split true).length
      = (rungRows tKey .xhat true).length + (splitRows tKey true).length
    ∧ (rungRows tKey .xhat true).length < (rungRows tKey .split true).length
    ∧ (((rungRows tKey .split true).zip (rungRows tKey .split false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tKey .split true).filter (fun r => r.probe)).length
    ∧ rungPub shapeSmoke .split = rungPub shapeSmoke .xhat := by
  refine ⟨rfl, by decide, rfl, rfl⟩

/-- `placeChecked` ACCEPTS the `w7_split` rung and no public word is inert — the fail-closed
placement, at the new top rung rather than at the one below it. -/
theorem split_rung_places_and_exposes_every_public_word :
    refusalOf shapeSmoke shapeSmoke.pubWords (wrapGates (rungRows tKey .split true)) = none
    ∧ inertPublicWords shapeSmoke.pubWords (wrapGates (rungRows tKey .split true)) = [] := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **WHAT `scale_fast2`'s TOP-BIT ZERO ACTUALLY BUYS — IN THE KERNEL, NOT IN PROSE.**
`plonk_curve_ops.ml:262-265` asserts ONE bit zero at width 255, giving `s_div_2 < 2^254`.

  * `2^254 < q`, so that bit CANONICALISES the ladder's own 255-cell decomposition: `B < 2^254 < q`
    is the unique representative of `s_div_2` mod `q`, and the multiplier the `EC_scale` gate uses
    IS the scalar `Field.Assert.equal !n_acc scalar` names.
  * `2·2^254 > q`, so it bounds `y = 2·s_div_2 + s_odd` by NOTHING: every `y ∈ Fq` has a split with
    `s_div_2 < 2^254`. Upstream's comment at `wrap_main.ml:64-68` calls this the deferred check on
    the high bits; it is a canonicity guard one level down, and §16 says so.

Both halves are needed: the first alone would read as "the deferral works", the second alone as "the
deferral is empty". Neither is true on its own. -/
theorem split_deferred_check_canonicalises_but_does_not_bound :
    2 ^ 254 < qN ∧ qN < 2 * 2 ^ 254 ∧ xhatTopZeros 0 = 1 ∧ xhatTopZeros 11 = 3 := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide

/-! ### §17b — ⚑ **W-FTCOMM'S PINS, AS NAMED THEOREMS.**

⚠ These are deliberately written so the KERNEL never reduces a ladder. A `scale_fast` ladder is 255
`stepVbmQ`s and each is three `qInv`s; the smoke shape runs five of them once `ftcResVal`'s recursion
is counted. `List.length` and a `kind`/`perm` filter reduce the list SPINE only — the accumulator and
slope values live in `advice` and stay unforced — so the row pins are cheap, and every pin that
needs a VALUE is stated over the scalars, which are plain `Nat`. No new `#guard`s. -/

/-- Recompose an MSB-first bit list, exactly as the `EC_scale` gate's `n_acc` chain does
(`plonk_curve_ops.ml:174-177`: `n' = 2n + b`, five bits per row). -/
def ftcRecompose (bs : List Nat) : Nat := bs.foldl (fun a b => 2 * a + b) 0

/-- ⚑ **`scale_fast`'s CHUNK COUNT IS A DIVISION, NOT A ROUNDING — AND THE TWO AGREE ONLY HERE.**
`scale_fast_unpack` takes `num_bits / bits_per_chunk` under a `[%test_eq]` that the remainder is
zero (`plonk_curve_ops.ml:149-151`); `scale_fast2` takes `chunks_needed ~num_bits:(n−1)`, which
rounds UP (`:66-70,254-256`). At 255 both are 51, which is why the `408 = 8 × 51` census is
insensitive to the confusion §13 item 4 shipped. At 128 they are 25 and 26 — the pin names a width
where the two disagree, so it cannot be satisfied by a definition that quietly used the other one. -/
theorem ftc_chunks_is_exact_division_and_that_matters :
    FTC_CHUNKS = 51
    ∧ FTC_BITS % BITS_PER_CHUNK = 0
    ∧ FTC_CHUNKS = chunksNeededQ (FTC_BITS - 1)
    ∧ 128 / BITS_PER_CHUNK ≠ chunksNeededQ (128 - 1) := by
  refine ⟨rfl, rfl, rfl, by decide⟩

/-- ⚑ **THE LADDER CENSUS, AND THE `408` IT CLOSES.** `tComms + 1` ladders, `51` chunks each, two
rows per chunk. At the committed wrap shape that is `8 × 51 = 408` `VarBaseMul` rows — exactly
`wrap-transaction`'s `VarBaseMul 2417` minus W-XHAT's `1805` and W-BULLET's `204`. -/
theorem ftc_ladder_census :
    ftcLadders shapeWrap = 8
    ∧ ftcLadders shapeSmoke = 3
    ∧ ftcLadders shapeWrap * FTC_CHUNKS = 408
    ∧ 1805 + ftcLadders shapeWrap * FTC_CHUNKS + 204 = 2417 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **THREE SCALAR VARIABLES, EIGHT LADDERS.** `common.ml:247-251` scales by
`plonk.zeta_to_srs_length` on EVERY fold iteration, so `tComms − 1` ladders assert `n_acc` against
ONE variable. A layout that gave each ladder its own scalar cell would be a different circuit — six
independent witnesses where upstream has one. -/
theorem ftc_six_fold_ladders_share_one_scalar :
    ((List.range (ftcLadders shapeWrap)).map (ftcScalarIdx shapeWrap))
      = [0, 1, 1, 1, 1, 1, 1, 2]
    ∧ ((List.range (ftcLadders shapeSmoke)).map (ftcScalarIdx shapeSmoke)) = [0, 1, 2] := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **DEFECT CLASS 2, EXHIBITED RATHER THAN DESCRIBED.** `scale_fast` ties its 255 free bit cells
to the scalar by `Field.Assert.equal !n_acc scalar` over `Fq` and by NOTHING else — there is no
top-bit-zero loop, because `scale_fast2`'s lives in `scale_fast2` (`plonk_curve_ops.ml:262-265`).
This exhibits the second admissible bit string for one of the three actual scalars: `v` and `v + q`
are DIFFERENT 255-bit strings, both recompose faithfully, both satisfy the only constraint the
circuit imposes, and the ladder multiplies by whichever the prover supplies. It is upstream's, it is
emitted unaltered, and adding a bound here would be a divergence from `wrap_main` rather than a fix
to it. -/
theorem ftc_scale_fast_admits_two_decompositions :
    ftcRecompose (ftcBitsOf (ftcSVal 1)) = ftcSVal 1
    ∧ ftcRecompose (ftcBitsOf (ftcSVal 1 + qN)) = ftcSVal 1 + qN
    ∧ ftcSVal 1 + qN < 2 ^ FTC_BITS
    ∧ (ftcSVal 1 + qN) % qN = ftcSVal 1
    ∧ ftcBitsOf (ftcSVal 1) ≠ ftcBitsOf (ftcSVal 1 + qN) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **EVERY LADDER SEED IS PINNED — BOTH OF THEM, PER LADDER.** `acc₀ = add_fast base base` is a
`CompleteAdd` row DEFINING the accumulator, and `n₀ = 0` is a `Generic` half; `plonk_curve_ops.ml:
157-158`. Read off the emitted row list: one `n₀` half per ladder, and the seed `CompleteAdd` count
is one per ladder plus the fold's `tComms − 1` adds plus the two closing adds. -/
theorem ftc_every_ladder_seed_is_pinned :
    ((List.range (ftcLadders shapeSmoke)).all (fun l =>
      hasHalf (ftcRows tKey true) [some (ftcCnt shapeSmoke tKey.sp l 0), none, none] (cConst 0)))
      = true
    ∧ ((ftcRows tKey true).filter (fun r => r.kind == KGateType.completeAdd)).length
        = ftcLadders shapeSmoke + (shapeSmoke.tComms - 1) + 2 := by
  refine ⟨rfl, rfl⟩

/-- The gate census of the sub-circuit: two rows per five-bit chunk, no sponge, no `EndoMul`. -/
theorem ftc_gate_census :
    ((ftcRows tKey true).filter (fun r => r.kind == KGateType.varBaseMul)).length
      = ftcLadders shapeSmoke * FTC_CHUNKS
    ∧ ((ftcRows tKey true).filter (fun r => r.kind == KGateType.poseidon)).length = 0
    ∧ ((ftcRows tKey true).filter (fun r => r.kind == KGateType.endoMul)).length = 0
    ∧ ((ftcRows tKey true).filter (fun r => r.probe)).length = ftcLadders shapeSmoke + 1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE FIRST LADDER'S BASE IS W-KEY'S SEALED OUTPUT, NOT A CONSTANT.** `sigma_comm.(6)` is
index-sponge coordinates 12 and 13, so `ft_comm` reads the variables §14's one-hot fold produced.
This is the σ tie that makes W-FTCOMM depend on the branch selection rather than on a literal. -/
theorem ftc_first_base_is_the_chosen_keys_sigma_comm_last :
    ftcBaseVar tKey 0
      = ((keyVars shapeSmoke (baseKey shapeSmoke tKey.sp)).acc 12 (shapeSmoke.branches - 1),
         (keyVars shapeSmoke (baseKey shapeSmoke tKey.sp)).acc 13 (shapeSmoke.branches - 1))
    ∧ ftcSigmaLast tKey = (STEP_VK_XY.getD 12 0, STEP_VK_XY.getD 13 0) := by
  refine ⟨rfl, rfl⟩

/-- The `w8_ftcomm` rung is a strict superset of `w7_split`, and `placeChecked` accepts it with no
inert public word. -/
theorem ftcomm_rung_extends_split_and_places :
    (rungRows tKey .ftcomm true).length
      = (rungRows tKey .split true).length + (ftcRows tKey true).length
    ∧ (rungRows tKey .split true).length < (rungRows tKey .ftcomm true).length
    ∧ refusalOf shapeSmoke shapeSmoke.pubWords (wrapGates (rungRows tKey .ftcomm true)) = none
    ∧ inertPublicWords shapeSmoke.pubWords (wrapGates (rungRows tKey .ftcomm true)) = [] := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  decide

/-- ⚑ **`t_comm` DOES NOT LEAVE THE UNCONSUMED CENSUS.** The MSM is emitted and the seven points are
consumed into `ft_comm` — and `ft_comm` is read by W-COMBINE and W-BULLET, which are not assembled,
so nothing downstream refuses a substituted `t_comm`. The entry is REWRITTEN, exactly as `x_hat`'s
was at `w6_xhat`; the count stays 8. -/
theorem ftcomm_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED.getD 4 ""
        = "t_comm — ft_comm EMITTED at w8_ftcomm (§17); its OUTPUT is W-COMBINE/W-BULLET's" := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### §18b — ⚑ **W-PREV'S PINS, AS NAMED THEOREMS.**

⚠ Same discipline as §17b: nothing here reduces a ladder. The rows are `Generic` halves and one
probe, and every value pin is over `Nat`s.

⚑ **AND THE HARDEST ONE TO WRITE HONESTLY IS THE LAST.** A rung whose own row count is nine is easy
to oversell; what these say is exactly what §18's header says — the checks upstream emits, the σ
identities that make the MSM read the statement, and the census entry that did NOT move. -/

/-- ⚑ **`prev_step_accs` ARE REAL VESTA POINTS.** `Inner_curve.typ`'s check is `assert_on_curve`, so
the rung is only satisfiable if the values the transcript already absorbs as `sg_old` lie on
`y² = x³ + 5` over Fq. They do — `PastaPoseidonFq.PREVCOMM_XY` are the two `RecursionChallenge`
commitments of a proof `kimchi::verifier::verify` ACCEPTED — so `w9_prev` adds a real check WITHOUT
moving the transcript. Had they not been on the curve, this rung would have had to re-fixture
`sg_old` and every challenge below the absorb would have moved. -/
theorem prev_step_accs_are_on_vesta :
    (List.range shapeSmoke.prevs).all (fun p =>
      onCurveQ (itemVal T_SGOLD (2 * p), itemVal T_SGOLD (2 * p + 1))) = true
    ∧ (List.range shapeWrap.prevs).all (fun p =>
      onCurveQ (itemVal T_SGOLD (2 * p), itemVal T_SGOLD (2 * p + 1))) = true := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **AND THE ON-CURVE CHECK RUNS ON THE ABSORBED CELLS, NOT ON COPIES.** `wrap_main.ml:412` hands
`incrementally_verify_proof` the same `prev_step_accs` that `wrap_verifier.ml:538` absorbs, so both
`assert_on_curve` chains here name the transcript's own `wordV` for `sg_old`. A version that
allocated fresh coordinate cells would have checked a curve point the sponge never saw. -/
theorem prev_on_curve_runs_on_the_absorbed_cells :
    (List.range shapeSmoke.prevs).all (fun p =>
      hasHalf prRows [some (sgOldVar tPrev p 0), some (sgOldVar tPrev p 0),
                      some (prevSq shapeSmoke tPrev.sp p 0)] cMul
      && hasHalf prRows [some (prevSq shapeSmoke tPrev.sp p 0), some (sgOldVar tPrev p 0),
                         some (prevSq shapeSmoke tPrev.sp p 1)] cMul
      && hasHalf prRows [some (sgOldVar tPrev p 1), some (sgOldVar tPrev p 1),
                         some (prevSq shapeSmoke tPrev.sp p 1)] cOnCurveQ) = true
    ∧ (List.range shapeSmoke.prevs).all (fun p =>
        (sgOldVar tPrev p 0) == ((tPrev.sp.evs.getD (1 + 2 * p) default).wordV)) = true := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **THE ONE CHECK THE 57-WORD `typ` EMITS, AND IT IS EMITTED TWICE BECAUSE THERE ARE TWO
`B Bool`s.** Everything else in `Types.Step.Proof_state.typ` is check-free at source (§18), so a
third `Boolean` half here would mean this file invented a constraint `wrap_main` does not have. -/
theorem prev_should_finalize_is_boolean_constrained :
    (List.range XHAT_PREVS).all (fun p =>
      let v := prevW shapeSmoke tPrev.sp (PREV_PER_PROOF_WORDS * p + PREV_SHOULD_FINALIZE)
      hasHalf prRows [some v, some v, some v] cBool) = true
    ∧ ((prevRows tPrev true).filter (fun r => r.kind == KGateType.generic)).length = 5
    ∧ ((prevRows tPrev true).filter (fun r => r.probe)).length = 1
    ∧ ((prevRows tPrev true).filter (fun r =>
         r.kind == KGateType.poseidon || r.kind == KGateType.varBaseMul
         || r.kind == KGateType.completeAdd)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **§10 SLOT 12 CLOSES HERE.** `Field.Assert.equal messages_for_next_step_proof
prev_proof_state.messages_for_next_step_proof` (`wrap_main.ml:350-351`) as the tie between the rung's
own public word and packed statement word `PREV_MSG_NEXT_STEP` — and the rung's public size is one
more than every rung below it. -/
theorem prev_ties_messages_for_next_step_proof_to_a_public_word :
    hasHalf prRows [some (.external shapeSmoke.pubWords : PVar),
                    some (prevW shapeSmoke tPrev.sp PREV_MSG_NEXT_STEP), none] cEq = true
    ∧ rungPub shapeSmoke .prev = shapeSmoke.pubWords + 1
    ∧ rungPub shapeSmoke .ftcomm = shapeSmoke.pubWords
    ∧ (exposedVarsAt tPrev .prev).getD shapeSmoke.pubWords (.external 0)
        = prevW shapeSmoke tPrev.sp PREV_MSG_NEXT_STEP := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **…AND THAT PUBLIC WORD IS NOT A PUBLIC FIXTURE.** The cell it ties is packed word 54, which
the MSM reads as entry 64 — at the committed wrap shape by construction, and at the SMOKE shape
because `xhatSel` selects it. A shape that exposed the word without selecting the entry would tie a
public word to a cell no other row constrains, which is the defect class this rung would otherwise
have introduced. -/
theorem prev_public_word_is_read_by_the_msm :
    (xhSel shapeSmoke).contains (XHAT_PER_PROOF * XHAT_PREVS) = true
    ∧ (xhSel shapeWrap).contains (XHAT_PER_PROOF * XHAT_PREVS) = true
    ∧ (List.range (xhN shapeSmoke)).any (fun k =>
        xhAt shapeSmoke k == XHAT_PER_PROOF * XHAT_PREVS
        && xScal shapeSmoke tPrev.sp k == prevW shapeSmoke tPrev.sp PREV_MSG_NEXT_STEP) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE MSM READS THE STATEMENT, AND THE TIE IS A σ IDENTITY RATHER THAN A ROW.**
`wrap_main.ml:404-411` passes `pack_statement … prev_statement` straight into
`incrementally_verify_proof`, so entry `i`'s scalar and its packed word are ONE `Cvar` and cost no
constraint. `xScal` is that: every non-split entry's scalar cell IS `prevW (xhatWordOf i)`, and only
the two `split_field` halves keep cells of their own. Emitting `Field.Assert.equal` rows instead
would have been stricter than `wrap_main` and would have had to be declared in §13's list. -/
theorem prev_msm_scalars_are_the_statement_words :
    (List.range (xhN shapeSmoke)).all (fun k =>
      let i := xhAt shapeSmoke k
      if xhatIsSplitHi i || xhatIsSplitLo i then
        xScal shapeSmoke tPrev.sp k
          == (PVar.external (baseXh shapeSmoke tPrev.sp + XH_STRIDE * k + 4))
      else xScal shapeSmoke tPrev.sp k == prevW shapeSmoke tPrev.sp (xhatWordOf i)) = true
    ∧ ((List.range (xhN shapeSmoke)).filter (fun k =>
        xScal shapeSmoke tPrev.sp k
          == prevW shapeSmoke tPrev.sp (xhatWordOf (xhAt shapeSmoke k)))).length = 3 := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **AND `w7_split`'s `x` IS THAT SAME WORD** — the sentence §16's header had been carrying as a
promise since `w7_split` landed. The `cSplit 1` half now names three cells the circuit uses
elsewhere: the statement word, and the two MSM entry scalars its halves feed. -/
theorem split_x_is_the_statement_word :
    (List.range (splitPairs shapeSmoke).length).all (fun a =>
      xSplitW shapeSmoke tPrev.sp a
        == prevW shapeSmoke tPrev.sp
             (xhatWordOf (xhAt shapeSmoke ((splitPairs shapeSmoke).getD a (0, 0)).1))) = true
    ∧ (splitPairs shapeSmoke).length = 1
    ∧ hasHalf (splitRows tPrev true)
        [some (xSplitW shapeSmoke tPrev.sp 0),
         some (xScal shapeSmoke tPrev.sp ((splitPairs shapeSmoke).getD 0 (0, 0)).1),
         some (xScal shapeSmoke tPrev.sp ((splitPairs shapeSmoke).getD 0 (0, 0)).2)]
        (cSplit 1) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- The `w9_prev` rung is a strict superset of `w8_ftcomm`, its length is the sum of its parts, and
the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns. -/
theorem prev_rung_extends_ftcomm :
    (rungRows tPrev .prev true).length
      = (rungRows tPrev .ftcomm true).length + (prevRows tPrev true).length
    ∧ (rungRows tPrev .ftcomm true).length < (rungRows tPrev .prev true).length
    ∧ (((rungRows tPrev .prev true).zip (rungRows tPrev .prev false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tPrev .prev true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, by decide, rfl⟩

/-- `placeChecked` ACCEPTS the `w9_prev` rung at its LARGER public size and no public word is inert
— including the new one. ⚑ And the rung below it is refused at that size: `w8_ftcomm`'s gates read
no cell for slot `pubWords`, so `inertPublicWord` fires. That is the leg that makes the reservation
a gate rather than a comment. -/
theorem prev_rung_places_and_the_rung_below_it_does_not :
    refusalOf shapeSmoke (rungPub shapeSmoke .prev) (wrapGates (rungRows tPrev .prev true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .prev)
        (wrapGates (rungRows tPrev .prev true)) = []
    ∧ inertPublicWords (rungPub shapeSmoke .prev)
        (wrapGates (rungRows tPrev .ftcomm true)) = [shapeSmoke.pubWords] := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚠ ⚑ **THE CENSUS DID NOT MOVE, AND THE ENTRY IS REWRITTEN RATHER THAN DELETED.** W-PREV names
the MSM's scalars and constrains three of the 67 — one to a public word, two to bits. The other 64
are free witnesses, HERE and UPSTREAM, so an MSM over them still spans the group and the prover's
reach into the transcript is unchanged in size. `sg_old` likewise: it is on-curve now and still
consumed by nothing, because its consumer is `Split_commitments.combine`'s `~init` (W-COMBINE).
Striking either entry on the strength of "a sub-circuit now reads it" is the metric-gaming this
census exists to refuse. The count stays **8**. -/
theorem prev_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED.getD 1 ""
        = "x_hat — MSM EMITTED at w6_xhat (§15); its 67 SCALARS are W-PREV's packed statement words, \
           and 64 of them are still free"
    ∧ WRAP_UNCONSUMED.getD 0 ""
        = "sg_old — ON-CURVE at w9_prev (§18); its consumer is W-COMBINE's ~init" := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-! ## §13 — ⚑ WHAT IS LEFT, BY SUB-CIRCUIT.

Named, not estimated; each entry is a row emitter this file does not have, and each carries the
measurement that sizes it. None of them is a value this file fakes and calls derived.

  1. ✅ **W-KEY — LANDED at `w5_key`** (§14). `choose_key` is 56 coordinate folds of `branches`
     `Generic` halves each against §9's one-hot bits, and the index sponge is 56 absorbs + one
     squeeze = **28 Fq permutations**. MEASURED: **536 wrap rows, 480 smoke rows**, no curve gate.
     The sizing note this list carried was right about the permutation count (28, not 29 — the last
     absorb leaves the state at `Absorbed 2`, so the squeeze's permutation is the 28th) and right
     that the output IS the transcript's first absorbed word. What it did not say is that the fold
     runs over `Inner_curve.constant` keys and is therefore not a curve MSM at all.
  2. ✅ **W-XHAT — LANDED at `w6_xhat`** (§15). MEASURED, from an emission this rung produced:
     **6472 wrap rows, 1170 smoke rows**, and the wrap-scale gate stream is `VarBaseMul 1805 ·
     CompleteAdd 232 · Zero 2115 · Generic 1027 · Poseidon 979 · EndoMulScalar 336`. The smoke rung
     PROVES on Pallas at 1176 rows / domain 2048 in ~1.1 s with all five polarities and 50/50
     sigma-only probes rejecting. The census the sizing note below predicted is
     confirmed three ways: read at source, printed independently by `xhat_lagrange_export.rs`, and
     — the strongest of the three — closed against Mina's own compiled wrap circuit, whose
     `VarBaseMul 2417` is EXACTLY `1805` (W-XHAT) `+ 408` (W-FTCOMM) `+ 204` (W-BULLET's four
     `scale_fast`). ⚠ What the note did NOT say: `lagrange` is a one-hot fold and not a bare
     constant (`wrap_verifier.ml:207-224`), the constant partition is EMPTY on this side (the STEP
     statement's spec has no `Constant` and no `Opt` node), `bp_log2` is `Tock`'s 15 and not
     `Tick`'s 16, and `lagrange_with_correction` computes its shift at `chunks_needed ~num_bits:n`
     rather than `n − 1` — upstream's own TODO, harmless at 255 and 128 and checked as such.
     The ORIGINAL sizing note, kept because it was right:
     ⚑ **MEASURED: 67 scalars, at widths 15 × 255 · 40 × 128 · 12 × 1.** The
     STEP statement packs to **57** words (`composition_types.ml:1268-1276,1427-1436,1453-1459` at
     `bp_log2 = Backend.Tock.Rounds.n = 15` and `max_proofs_verified = 2`), of which 10 are `` `Field ``
     and 47 `` `Packed_bits ``; `wrap_verifier.ml:542-548` turns each `` `Field `` into TWO entries
     (255-bit value + 1-bit parity), giving 57 + 10 = 67. The 12 one-bit scalars take the
     `` `Cond_add `` path with an explicit `assert_ (Constraint.boolean …)` (`:573-576`); the other
     55 take `Ops.scale_fast2'` at `chunks_needed ~num_bits:(n−1)` five-bit chunks — **51 chunks at
     255 bits, 26 at 128** (`plonk_curve_ops.ml:66-70,251-267`). Plus the `lagrange` /
     `scaled_lagrange` constant partition, the correction sum, `Inner_curve.negate` and
     `x_hat blinding`.
  3. ✅ **W-SPLIT — LANDED at `w7_split`** (§16). `wrap_main.ml:69-81`, called once at `:409`: one
     `Boolean.typ` check and one `Field.Assert.equal ((of_int 2 * y) + is_odd) x` per statement
     `Field` word — **two `Generic` halves, one row**, ten words at the wrap shape and one at the
     smoke shape. The outputs ARE §15's entry scalars, so the tie is a σ class and not a new cell.
     ⚠ **THE SIZING NOTE THIS LIST CARRIED WAS RIGHT ABOUT THE ROWS AND WRONG ABOUT THE DEFERRAL.**
     It said the hi range check is "DEFERRED INTO `scale_fast2`" and that emitting the split without
     it would be defect class 2 in a new place. Followed to source (§16b proves both halves in the
     kernel): `scale_fast2` at width 255 asserts ONE bit zero, giving `s_div_2 < 2^254`, and
     `2^254 < q` — so what the deferral buys is **canonicity of the ladder's own 255-cell
     decomposition**, not a bound on `y`. `q < 2·2^254`, so every `y ∈ Fq` has an admissible split
     and the "check" bounds `y` by nothing. It does not need to: `scale_fast2`'s mux makes the
     contribution `y·g` under EITHER split. ⚠ **The split ONE level up is a different matter** —
     `y` and `is_odd` are consumed by DIFFERENT Lagrange bases, so the two solutions give different
     `x_hat`, and nothing bounds `y`. It is not a hole HERE only because `x` is a free witness on
     both sides: **W-SPLIT's constraint pins nothing until W-PREV ties `x`**, which is item 9 and is
     now the first thing this list wants.
  4. ✅ **W-FTCOMM — LANDED at `w8_ftcomm`** (§17). MEASURED, from an emission this rung produced:
     **1491 smoke rows**, gate stream `VarBaseMul 230 · CompleteAdd 16 · Zero 331 · Generic 286 ·
     Poseidon 506 · EndoMulScalar 128`, and the `230 − 77 = 153 = 3 × 51` delta is the smoke shape's
     three ladders exactly. It PROVES on Pallas at 1497 rows / domain 2048 in 1162 ms with all five
     polarities. `Common.ft_comm` (`common.ml:238-256`), **eight
     `scale_fast`** at `Other_field.Packed.Constant.size_in_bits = 255`, i.e. 51 chunks each.
     ⚠ **NOT `scale_fast2`, which is what this entry used to say and is wrong at source**:
     `wrap_verifier.ml:658-659` SHADOWS `scale_fast` with `Ops.scale_fast ~num_bits:255` and passes
     THAT as `~scale`. The difference is the whole shape — no `(s_div_2, s_odd)` split, no
     `Boolean.typ`, **no top-bit-zero loop**, no `G.if_` mux and no correction, because the scalar
     is already a `Shifted_value.Type1`; and the chunk count is `num_bits / bits_per_chunk` under a
     `[%test_eq]` for exact division (`plonk_curve_ops.ml:149-151`), not `chunks_needed ~num_bits:
     (n−1)`. Both land on 51 at width 255, so the row census is unaffected and the derivation is
     not. ⚑ The eight are `1` (`perm · sigma_comm_last`) `+ 6` (the `chunked_t_comm` fold at
     `tComms = 7`) `+ 1` (`zeta_to_domain_size`); `List.reduce_exn` on a singleton applies `+` zero
     times, so `f_comm` costs a ladder and no add. ⚑ The first ladder's base is **W-KEY's output** —
     `sigma_comm.(6)` is index-sponge coordinates 12 and 13 — so this sub-circuit wires into §14.
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
     `hash_messages_for_next_wrap_proof` sponges. ⚠ **Public word 12 is NO LONGER ITS**: `w9_prev`
     closed it (§10, §18), and what is left here is word 11 plus packed statement words 55 and 56 —
     the PREVIOUS statement's own `messages_for_next_wrap_proof` digests, which is what consumes
     `old_bp_chals`. ⚑ Word 11 needs W-FINALIZE too: `wrap_main.ml:421-429` hashes
     `openings_proof.challenge_polynomial_commitment` with `new_bulletproof_challenges`, and the
     latter is `finalize_other_proof`'s output. ⚑ Absorption order
     is **all old bulletproof challenges first, flattened, THEN the commitment as `[x; y]`**
     (`composition_types.ml:411-418`) — the opposite of the step side's interleaving — and the
     padding is at the FRONT via a PRECOMPUTED sponge-state table indexed by
     `2 − max_proofs_verified` (`wrap_hack.ml:99-109,124-137`), not by absorbing dummies in circuit.
  9. ✅ **W-PREV — LANDED at `w9_prev`** (§18). ⚠ **AND THE SIZING NOTE THIS ENTRY CARRIED WAS
     WRONG AT SOURCE, IN THE DIRECTION THAT MADE THE WORK LOOK BIGGER THAN IT IS.** It said the typ
     carried "`~assert_16_bits:(assert_n_bits ~n:16)`, a `to_field_checked` at a width this file
     does not emit (only 128)". Read at source: `spec.ml:414-429` consumes `~assert_16_bits` in
     exactly ONE arm — `Branch_data` — and `Per_proof.In_circuit.spec`
     (`composition_types.ml:1268-1276`) has no such node, so the argument is passed and NEVER FIRES.
     `Limb_vector.Challenge.typ` is `Typ.field` with a transport (`limb_vector/make.ml:14-19`) and
     emits **no range check at all**, which `Scalar_challenge.typ` and `Bulletproof_challenge.typ`
     inherit; `Digest.typ` is likewise a bare transport. The whole 57-word `exists` costs **two
     `Boolean.typ` checks** — the two `should_finalize` words — and that is the entire typ.
     What it DOES cost is `Inner_curve.typ`'s `assert_on_curve` on the two `prev_step_accs`
     (`snarky_curve.ml:211-228`, three R1CS rows each at Vesta's `a = 0`, `b = 5`), and one
     `Field.Assert.equal` at `:350-351`. MEASURED: **5 `Generic` rows + 1 probe** at the smoke shape.
     ⚑ The rung's value is not its rows — it is that `xScal`/`xSplitW` make the 67 MSM scalars the
     packed image of 57 statement words, so `w7_split`'s `x` is a cell the circuit consumes rather
     than a cell derived downward from its own outputs.
     ⚠ **`old_bp_chals` is DELIBERATELY NOT EMITTED**: its only consumer is
     `hash_messages_for_next_wrap_proof` (`wrap_main.ml:341-348`), which is item 8, and 30 cells with
     no consumer are decoration. It stays with W-WRAPHACK.
 10. **W-CLOSE**'s curve-side assert `wrap_main.ml:419-420` — `Boolean.Assert.is_true
     bulletproof_success`, which is W-BULLET's output.

⚠ ⚑ **THREE PLACES THIS FILE IS STRICTER THAN UPSTREAM, said rather than banked.**

  * ⚑ **`choose_key`'s FOLD — the biggest of them, and it arrived with W-KEY.** `wrap_main.ml:218-219`
    passes the step keys through `Inner_curve.constant`, so in `wrap_verifier.ml:196-204` every
    `Double.map g ~f:(( * ) (b :> t))` is a var times a CONSTANT — `Checked.mul`'s `Constant` branch
    is `Cvar.scale` (`snarky/src/base/utils.ml:81-88`, read at source) — and every `Double.map2 ~f:(+)`
    is Cvar addition. **Upstream emits ZERO rows for the whole 28 × 2 × `branches` fold** and pays
    only `Util.seal`'s one `exists` + `Field.Assert.equal` per coordinate (`util.ml:65-76`), i.e.
    **56 rows**. §14 emits `KEY_COORDS × branches` fold halves — 280 halves = 140 rows at the wrap
    shape — so every partial sum is a constrained variable rather than a linear form the prover
    could re-associate. Stricter, therefore **not** a row-count conformance claim; the wrap
    conformance report surfaces it as the `[K 0 -1 0 0] × 56` shape family Snarky never emits.
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
  * **THE INPUT IS DERIVED IN ITS FIRST WORD AND NOWHERE ELSE.** ⚑ At `w5_key`, `index_digest` is
    no longer a fixture: it is the squeeze of a sponge over the 28 commitments a one-hot fold
    selected out of the step keys, and `key_digest_is_the_index_digest` pins that squeeze against a
    digest Rust kimchi computed for the same index. So the FIRST absorbed word is forced by the
    circuit. ⚠ **The other nine are not.** `x_hat`, `sg_old`, `w_comm`, `z_comm`, `t_comm`,
    `combined_inner_product`, `lr` and `delta` are absorbed and consumed by nothing (§2c), so a
    prover who could choose one would steer every challenge below it. W-XHAT and W-COMBINE are what
    would force them, and they are now the first thing to build.
  * **THE OPENING IS NOT HERE AT ALL.** `equal_g`, `verified` and the accumulator check are
    W-BULLET and W-FINALIZE. Everything this file proves is about the transcript and the selection.
-/

#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapMain

end Dregg2.Circuit.Emit.KimchiWrapMain
