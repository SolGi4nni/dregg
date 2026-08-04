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

⚠ **NOT ASSEMBLED, named by sub-circuit** (§13): W-FINALIZE, W-OPENINGS, W-COMBINE and W-BULLET.
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
that touches the gap, so the reservation cannot be used by accident.

⚑ **AND THE `+ 2` IS `w11_wraphack`'s**, reserved the same way and for the same reason: wrap
statement word 11 is the closing `hash_messages_for_next_wrap_proof` squeeze (`wrap_main.ml:421-431`,
§19), and below that rung no row reads the cell it would be tied to. `wraphack_rung_places_and_the_
rung_below_it_does_not` exhibits the refusal at slot `pubWords + 1`. -/
def AUXW (s : WrapShape) : Nat := s.pubWords + 2

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
    11     messages_for_next_wrap_proof            ✅ at `w11_wraphack` ONLY (§21) — the closing
                                                      `hash_messages_for_next_wrap_proof` sponge's
                                                      `squeeze_field` (`wrap_main.ml:421-431`)
    30–37  Spec.T.Constant padding                 ✗ (never constrained upstream either)
    38–39  the lookup Opt                          ✗ (`lookup_verification_enabled` is off)

**22 of 40 through `w8_ftcomm`, 23 at `w9_prev`, 24 at `w11_wraphack`.**

⚠ ⚑ **AND 40 IS NOT THE DENOMINATOR — 24 IS, AND THE OTHER SIXTEEN ARE NOT THIS FILE'S WORK.**
`wrap_main` is HANDED forty words and CONSTRAINS twenty-four of them. Slots 0–4 and 9 are deferred
values it passes straight through as `~advice` / `~plonk` / `~xi` (`wrap_main.ml:405-414`) and never
checks — what consumes them is **W-FINALIZE**, §13 item 7, and until it lands they are not "missing
from our public vector", they are unconstrained in `wrap_main` as written. Slots 30–37 are
`Spec.T.Constant` padding and 38–39 the lookup `Opt` that `G.lookup_verification_enabled` leaves off
(`wrap_verifier.ml:487,715`); a real devnet wrap proof carries **ZERO** in all ten
(`MinaWrapPublicInput.the_tail_is_padding_and_branch_data`, over
`MinaWrapPublicCommGate.PUBLIC_INPUT`). Tying those to variables would be public fixtures — defect
class 5 wearing a public vector. So the honest reading of a `PI 24 vs 40` delta is
**6 W-FINALIZE + 10 constant-or-dead**, and this rung is the last of the 24.

⚑ **AND EACH NEW WORD IS EXPOSED AT ONE RUNG, NOT AT ALL OF THEM.** `closingRows` emits `pubWords`
halves at `w4_bind`, `prevRows` emits the 23rd and `whRows` the 24th; `AUXW` reserves BOTH extra
slots at every rung so that below their rungs they sit in `placeChecked`'s DEAD GAP. That is the
difference between a public word a rung derives and one it inherits: exposing word 12 at `w4_bind`,
or word 11 at `w9_prev`, would tie it to a cell nothing in that rung reads.
`prev_rung_places_and_the_rung_below_it_does_not` and
`wraphack_rung_places_and_the_rung_below_it_does_not` exhibit both refusals. -/

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

/-- …and the sixteen it does not pin, by REASON and by OWNER. -/
def WRAP_UNPINNED : List String :=
  [ "0–4 cip · b · zeta_to_srs_length · zeta_to_domain_size · perm — PASSED THROUGH as ~advice/~plonk \
     (wrap_main.ml:405-414); W-FINALIZE is what consumes them"
  , "9 xi — PASSED THROUGH as ~xi (wrap_main.ml:409); W-FINALIZE"
  , "30–37 Spec.T.Constant padding — ZERO in a real devnet wrap proof, constrained by nothing upstream"
  , "38–39 the lookup Opt — G.lookup_verification_enabled is off (wrap_verifier.ml:487,715)" ]

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
squeezes (§15c″ is the value side of that, and `wraphack_digest_is_the_statement_word` is the pin
that the two agree); `old_bp_chals` acquires its only consumer; and `prev_step_accs` acquires a
second one.

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

⚠ **AND THE COMPOSITION HAZARD IS NOT CLOSED, IT IS NAMED.** `baseFin` (§19) and `baseComb` (§23)
are BOTH `baseFtc s sp + nFtcVars s sp` — the same address this now uses. That is sound TODAY only
because no rung's `rungsUpto` contains two of `.finalize`, `.combine`, `.wraphack`: the three
sub-circuits were assembled concurrently as siblings off `w9_prev`. **When the ladder closes into one
chain, the three regions must be STACKED, and whichever lane does that owns all three base
definitions at once.** `wraphack_region_is_above_ftcomms` refutes the bug that was here; it does not
and cannot cover a rung that does not exist yet. -/
def baseWh (s : WrapShape) (sp : SpAcc) : Nat := baseFtc s sp + nFtcVars s sp
def whBaseP (s : WrapShape) (sp : SpAcc) (p : Nat) : Nat := baseWh s sp + WH_VARS * p
def whBaseC (s : WrapShape) (sp : SpAcc) : Nat := baseWh s sp + WH_VARS * s.prevs
def nWhVars (s : WrapShape) : Nat := WH_VARS * (s.prevs + 1)

/-- Previous proof `p`'s sponge (`wrap_main.ml:341-348`). -/
def whSpongeP (t : WrapData) (p : Nat) : SpAcc :=
  whSpongeOf (whBaseP t.sh t.sp p) (whTape (whOldChals p) (whSgOld p))
/-- …and the CLOSING one (`wrap_main.ml:421-431`), whose squeeze is wrap statement word 11. -/
def whSpongeC (t : WrapData) : SpAcc :=
  whSpongeOf (whBaseC t.sh t.sp) (whTape whNewChals whSg)

/-- A wrap-hack sponge's squeeze — the cell it is read out of… -/
def whDigestVar (a : SpAcc) : PVar := ((a.evs.filter (fun e => !e.isAbs)).getD 0 default).srcV
/-- …and its value. -/
def whDigestVal (a : SpAcc) : Nat := ((a.evs.filter (fun e => !e.isAbs)).getD 0 default).val

/-- ⚑ The public slot word 11 lands in: this assembly's 24th, one above `w9_prev`'s. -/
def WH_PUB_SLOT (s : WrapShape) : Nat := s.pubWords + 1

/-- **W-WRAPHACK's ROWS.** Three sponges — whose `init` rows pin each fresh opening state to zero,
i.e. the front pad at `WH_MLMB = 2` — and then the ties that make each sponge's INPUT and OUTPUT
cells the ones the rest of the assembly already has. -/
def whRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let ties : List (List (Option PVar) × List Int) :=
    (List.range s.prevs).flatMap (fun p =>
      let a := whSpongeP t p
      -- ⚑ THE LAST TWO ABSORBS ARE `prev_step_accs.(p)` — the TRANSCRIPT's own `sg_old` cells, not
      -- a second copy of them. This is what makes `x; y` last rather than first observable.
      ((List.range 2).map (fun j =>
        ([some (a.evs.getD (WH_MLMB * WH_ROUNDS + j) default).wordV, some (sgOldVar t p j), none],
         cEq)))
      -- …and the squeeze IS packed statement word 55 / 56, which the MSM consumes as entry 65 / 66.
      ++ [ ([some (whDigestVar a), some (prevW s sp (PREV_MSG_NEXT_STEP + 1 + p)), none], cEq) ])
    -- ⚑ …and the closing squeeze IS wrap statement word 11 (`wrap_main.ml:421-431`).
    ++ [ ([some (.external (WH_PUB_SLOT s) : PVar), some (whDigestVar (whSpongeC t)), none], cEq) ]
  (List.range s.prevs).flatMap (fun p =>
    transcriptRowsQ (whBaseP s sp p) (whSpongeP t p) wired)
  ++ transcriptRowsQ (whBaseC s sp) (whSpongeC t) wired
  ++ packHalves ties

/-- W-WRAPHACK's variable environment — the three sponges'. ⚠ The `sg_old` absorb cells duplicate
values `spongeEnv (baseSp …)` already carries for the transcript's own cells; they are DIFFERENT
variables holding ONE value, which is what the tie rows say and what a σ class means. -/
def whEnv (t : WrapData) : VarEnv :=
  (List.range t.sh.prevs).flatMap (fun p => spongeEnv (whBaseP t.sh t.sp p) (whSpongeP t p))
  ++ spongeEnv (whBaseC t.sh t.sp) (whSpongeC t)

/-! ## §22 — ⚑ **W-CLOSE**: `wrap_main.ml:419-420`, and it is one constraint.

§13's last entry. `with_label __LOC__ (fun () -> Boolean.Assert.is_true bulletproof_success)` —
`bulletproof_success` is `check_bulletproof`'s `` `Success `` (`wrap_verifier.ml:383-437`), and
`Boolean.Assert.is_true b` is `assert_equal (b :> Field.t) Field.one`: **ONE R1CS constraint**, one
`Generic` half here.

⚠ **AND ITS INPUT IS W-BULLET'S, WHICH THIS FILE DOES NOT ASSEMBLE.** So the cell this rung pins to
1 is a free witness until §13 item 6 lands, and the honest statement of what the rung buys is
narrow: the wrap circuit REFUSES a witness in which `bulletproof_success` is anything but 1, which
is the difference between an opening check whose verdict is ignored and one whose verdict is
required. It is not a claim that the opening is checked — `equal_g` is not in this circuit at all.
Emitting it anyway is right for the same reason `wrap_main` writes it: the assert is the closing
tie, and a `check_bulletproof` whose result nothing asserts is a check that does not refuse. -/

/-- The closing region: one cell. -/
def baseClose (s : WrapShape) (sp : SpAcc) : Nat := baseWh s sp + nWhVars s
/-- `bulletproof_success` — `check_bulletproof`'s `` `Success `` (`wrap_verifier.ml:436`). -/
def bpSuccessVar (s : WrapShape) (sp : SpAcc) : PVar := .external (baseClose s sp)

/-- **W-CLOSE's ROWS.** `Boolean.Assert.is_true bulletproof_success`, and a σ-only probe so the
rung's own cell is testable by the harness rather than merely present. -/
def closeRows (t : WrapData) (wired : Bool) : List WRow :=
  let v := bpSuccessVar t.sh t.sp
  packHalves [ ([some v, none, none], cConst 1) ]
  ++ [ probeRow wired v (whDigestVar (whSpongeC t)) ]

/-- W-CLOSE's variable environment: the honest witness satisfies the assert. -/
def closeEnv (t : WrapData) : VarEnv := [ (bpSuccessVar t.sh t.sp, (1 : Int)) ]

/-! ## §19 — ⚑ **W-FINALIZE**: `finalize_other_proof`, and the fact that decides it.

`wrap_verifier.ml:820-1049`, run `Max_proofs_verified.n` times from `wrap_main.ml:329-336`
(`Vector.mapn` over `prev_proof_state.unfinalized_proofs`), so this rung emits **`prevs` instances**
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

def fnEm (o : FOp) : FM Nat := do
  let st ← get
  set (st.push o)
  pure st.size

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

/-- Column `k`'s value at ζ (`j = 0`) / at ζω (`j = 1`) for instance `p` — a NAMED FIXTURE, because
`exists ~request:Req.Evals` is a free witness upstream and a fixture is the faithful stand-in. -/
def finColVal (p k j : Nat) : Nat := wrapFixtureQ (40 + 2 * p + j) k
/-- `evals.public_input.0` — `p(ζ)`, likewise witnessed. -/
def finPZetaVal (p : Nat) : Nat := wrapFixtureQ (44 + p) 0

/-- Instance `p`'s packed statement word `w` of its own 27-word block. -/
def finBlockWord (p w : Nat) : Nat := PREV_PER_PROOF_WORDS * p + w
/-- …and its VALUE. -/
def finBlockVal (p w : Nat) : Nat := prevWordVal (finBlockWord p w)

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

/-- The finalize region starts after W-FTCOMM's, so nothing below `w10_finalize` moves. -/
def baseFin (s : WrapShape) (sp : SpAcc) : Nat := baseFtc s sp + nFtcVars s sp
/-- Two `to_field_checked` chains per instance — α and ζ, the two `Scalar_challenge` fields
`map_plonk_to_field` lifts. -/
def finChainVars (s : WrapShape) (sp : SpAcc) (p j : Nat) : ChainVars :=
  chainVars s (baseFin s sp) (2 * p + j)
def finEvBase (s : WrapShape) (sp : SpAcc) : Nat :=
  baseFin s sp + 2 * s.prevs * chainStride s
/-- Instance `p`'s evaluation column `k` at ζ (`j = 0`) / ζω (`j = 1`); slot `2·NCOLS` is `p(ζ)`. -/
def finEvVar (s : WrapShape) (sp : SpAcc) (p k j : Nat) : PVar :=
  .external (finEvBase s sp + p * (2 * FIN_NCOLS + 1) + j * FIN_NCOLS + k)
def finPZetaVar (s : WrapShape) (sp : SpAcc) (p : Nat) : PVar :=
  .external (finEvBase s sp + p * (2 * FIN_NCOLS + 1) + 2 * FIN_NCOLS)
def finProgBase (s : WrapShape) (sp : SpAcc) : Nat :=
  finEvBase s sp + s.prevs * (2 * FIN_NCOLS + 1)

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

/-- Instance `p`'s `.inp` lookup: the 87 witnessed evaluation cells, the two lifts, and the four
statement words. Every entry is a cell some row of the assembly defines. -/
def finInputEnv (s : WrapShape) (sp : SpAcc) (p : Nat) : VarEnv :=
  (List.range FIN_NCOLS).flatMap (fun k =>
    [ (finEvVar s sp p k 0, (finColVal p k 0 : Int))
    , (finEvVar s sp p k 1, (finColVal p k 1 : Int)) ])
  ++ [ (finPZetaVar s sp p, (finPZetaVal p : Int))
     , ((finChainVars s sp p 0).lift, (liftValQ s (finBlockVal p 8) : Int))
     , ((finChainVars s sp p 1).lift, (liftValQ s (finBlockVal p 9) : Int))
     , (prevW s sp (finBlockWord p 6), (finBlockVal p 6 : Int))
     , (prevW s sp (finBlockWord p 7), (finBlockVal p 7 : Int))
     , (prevW s sp (finBlockWord p 4), (finBlockVal p 4 : Int))
     , (prevW s sp (finBlockWord p 26), (finBlockVal p 26 : Int)) ]

/-- Instance `p`'s program, compiled and evaluated ONCE. -/
structure FinData where
  fp : FinProg
  vals : Array Nat
  deriving Repr, Inhabited

def runFin (s : WrapShape) (sp : SpAcc) (p : Nat) : FinData :=
  let fp := finProgOf (finWireOf s sp p) (finCfgOf s p)
  let lk := envLookupAt (envIndex (finInputEnv s sp p))
  { fp := fp, vals := fnEval lk fp.prog }

/-- Instance `p`'s program base. The programs are the same builder at different wires, so the stride
is instance 0's size; a shape whose instances disagreed in size would overlap and `placeChecked`
would refuse rather than emit. -/
def finProgSize (s : WrapShape) (sp : SpAcc) : Nat :=
  (finProgOf (finWireOf s sp 0) (finCfgOf s 0)).prog.size
def finProgAt (s : WrapShape) (sp : SpAcc) (p : Nat) : Nat :=
  finProgBase s sp + p * finProgSize s sp

/-- **W-FINALIZE's ROWS.** Per instance: the two `to_field_checked` lifts of α and ζ (through the
SHARED endo cell §5 pins, `split = false` because both sources are already `Challenge.t`), the
compiled program, and the σ-only probes. -/
def finRows (t : WrapData) (wired : Bool) : List WRow :=
  let s := t.sh
  let sp := t.sp
  let cb := baseCh s sp
  (List.range s.prevs).flatMap (fun p =>
    let d := runFin s sp p
    let base := finProgAt s sp p
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
  (List.range s.prevs).flatMap (fun p =>
    let d := runFin s sp p
    chainEnv s (finChainVars s sp p 0) (finBlockVal p 8) 0
    ++ chainEnv s (finChainVars s sp p 1) (finBlockVal p 9) 0
    ++ finInputEnv s sp p
    ++ fnEnvOf (finProgAt s sp p) d.fp.prog d.vals)

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

⚑ So the mux is emitted exactly TWICE, at the fold's last two steps, and — because
`mkWrapWith` witnesses branch 1 with widths `[0,1,2,…]`, so `first_zero = 1` — the two carry
`keep = 0` and `keep = 1`. **Both arms of `Inner_curve.if_` are live in the honest witness**, which
`comb_mux_takes_both_branches` pins.

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
coefficient and sigma commitments come out of W-KEY's 56 REAL coordinates at every shape. -/
def combTerms (s : WrapShape) : Nat :=
  s.prevs + 3 + KEY_SINGLES + s.wComms + KEY_COLS + (KEY_SIGMA - 1)
/-- Fold steps — one fewer than the commitments, because `~init` consumes the last. -/
def combSteps (s : WrapShape) : Nat := combTerms s - 1

/-- ⚑ **`xi`**, `Deferred_values.xi`'s `Scalar_challenge.inner` — a RAW 128-bit challenge, free here
and bound by W-FINALIZE. It is `< 2^ENDO_BITS` because the ladder's counter reconstructs exactly
that many bits; a wider value would make `Field.Assert.equal !n_acc scalar` unsatisfiable. -/
def combXiVal : Nat := wrapFixtureQ 30 0 % 2 ^ ENDO_BITS

/-- Commitment `k`'s VALUE, in `wrap_verifier.ml:687-706`'s flat order. -/
def combPtVal (t : WrapData) (k : Nat) : Nat × Nat :=
  let s := t.sh
  let kc : Nat → Nat × Nat := fun c => (keyConst t.br.idx c, keyConst t.br.idx (c + 1))
  if k < s.prevs then (itemVal T_SGOLD (2 * k), itemVal T_SGOLD (2 * k + 1))
  else if k == s.prevs then s.xhatXY
  else if k == s.prevs + 1 then ftcOut t
  else if k == s.prevs + 2 then (itemVal T_ZCOMM 0, itemVal T_ZCOMM 1)
  else if k < s.prevs + 3 + KEY_SINGLES then kc (44 + 2 * (k - s.prevs - 3))
  else if k < s.prevs + 3 + KEY_SINGLES + s.wComms then
    let j := k - s.prevs - 3 - KEY_SINGLES
    (itemVal T_WCOMM (2 * j), itemVal T_WCOMM (2 * j + 1))
  else if k < s.prevs + 3 + KEY_SINGLES + s.wComms + KEY_COLS then
    kc (14 + 2 * (k - s.prevs - 3 - KEY_SINGLES - s.wComms))
  else kc (2 * (k - s.prevs - 3 - KEY_SINGLES - s.wComms - KEY_COLS))

/-- …and its VARIABLE. ⚑ Every one is another rung's cell; this sub-circuit allocates none of them. -/
def combPtVar (t : WrapData) (k : Nat) : PVar × PVar :=
  let s := t.sh
  let sp := t.sp
  let kv := keyVars s (baseKey s sp)
  let kc : Nat → PVar × PVar := fun c => (kv.acc c (s.branches - 1), kv.acc (c + 1) (s.branches - 1))
  let absW : Nat → Nat → PVar := fun tag i =>
    ((sp.evs.filter (fun e => e.isAbs && e.tag == tag)).getD i default).wordV
  if k < s.prevs then (absW T_SGOLD (2 * k), absW T_SGOLD (2 * k + 1))
  else if k == s.prevs then (absW T_XHAT 0, absW T_XHAT 1)
  else if k == s.prevs + 1 then ftcOutV s sp
  else if k == s.prevs + 2 then (absW T_ZCOMM 0, absW T_ZCOMM 1)
  else if k < s.prevs + 3 + KEY_SINGLES then kc (44 + 2 * (k - s.prevs - 3))
  else if k < s.prevs + 3 + KEY_SINGLES + s.wComms then
    let j := k - s.prevs - 3 - KEY_SINGLES
    (absW T_WCOMM (2 * j), absW T_WCOMM (2 * j + 1))
  else if k < s.prevs + 3 + KEY_SINGLES + s.wComms + KEY_COLS then
    kc (14 + 2 * (k - s.prevs - 3 - KEY_SINGLES - s.wComms))
  else kc (2 * (k - s.prevs - 3 - KEY_SINGLES - s.wComms - KEY_COLS))

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
      let out := if idx < t.sh.prevs && combKeepVal t idx == 0 then cur else sum
      { accs := st.accs ++ [out], eds := st.eds ++ [ed], sums := st.sums ++ [sum] })
    { accs := [combPtVal t (n - 1)], eds := [], sums := [] }
  st

/-- The commitment fold step `a` consumes — the fold runs DOWN the flat list. -/
def combIdx (s : WrapShape) (a : Nat) : Nat := combTerms s - 2 - a
/-- …and whether that step carries a live `keep` mux. -/
def combIsMux (s : WrapShape) (a : Nat) : Bool := combIdx s a < s.prevs

/-! ### §23a — the variable layout.

⚠ **THE REGION SHARES ITS BASE WITH W-FINALIZE's, AND THAT IS SAFE BECAUSE OF `rungsUpto`.**
`.combine` and `.finalize` are sibling branches off `.prev`; no rung's `rungsUpto` contains both, so
no emitted circuit ever holds cells from both regions. A rung that merged them would have to re-base
one, and that is the one thing to check before merging. -/

/-- Per-step slots: `p` (2), `endo·xt` (1), the 33 accumulator points (66), the 32 interior
counters, the `Ops.add_fast` output (2), and the mux's `(d, m, r)` for x then y (6). -/
def COMB_STRIDE : Nat := 3 + 2 * (ENDO_BLOCKS + 1) + ENDO_BLOCKS + 2 + 6

def baseComb (s : WrapShape) (sp : SpAcc) : Nat := baseFtc s sp + nFtcVars s sp
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

## ⚑ `equal_g` IS COMPUTED, AND AT THIS TREE'S FIXTURES IT COMPUTES **ZERO**

`equal_g lhs rhs` (`:177-181`) is `Field.equal` per coordinate then `Boolean.all`, and this section
emits the real gadget: `d = lhs − rhs`, `d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`. Its value is
NOT assumed.

⚠ ⚑ **AND IT IS 0, FOR A REASON THAT IS A FINDING AND NOT A SHRUG.** The step side closed the same
gadget by SOLVING `G := z₁⁻¹·(lhs − z₂·H) − b·u` — one scalar-field inverse and three scalar
multiplications — and that solve needs `lhs` to be **on the curve**. Here it is not, and the cause is
upstream's own arithmetic on this tree's step verification key: **seven of that key's 28 commitments
are the identity**, `index_to_field_elements` flattens the identity as the fake point `(0, 0)`
(§14's own note), and `Ops.add_fast` is the INCOMPLETE add — a chord through `(0,0)`, which is not on
`y² = x³ + 5`. So W-COMBINE's `combined_polynomial` is an off-curve pair, `p_prime`, `q`, `cq` and
`lhs` inherit it, and no `G` closes the opening.

⚑ **THE CONSEQUENCE FOR W-CLOSE, SAID OUT LOUD:** `wrap_main.ml:419-420`'s
`Boolean.Assert.is_true bulletproof_success` is **UNSATISFIABLE at this key**. That is not W-BULLET
being incomplete — the gadget is emitted in full and its witness is honest — it is the FIXTURE. A
step key with no identity commitment would put `lhs` back on the curve and the solve back in reach.
Recorded here rather than worked around, because a witness that made `bit = 1` would have to fake a
cell this section computes.

⚠ For the same reason `challenge_polynomial_commitment` gets **no `assert_on_curve`** while `lr`,
`delta` and every `endo_inv` witness DO: an on-curve `G` is exactly what this fixture cannot supply,
and emitting the check on a value the honest witness fails is a rung that cannot be proved. Named,
not banked.

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
/-- The points `Inner_curve.typ` checks here: the `2·ipaRounds` `lr` points, `delta`, and the
`ipaRounds` `endo_inv` witnesses. ⚠ NOT `challenge_polynomial_commitment` — see the header. -/
def bullOCPts (s : WrapShape) : Nat := 3 * s.ipaRounds + 1

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
  ((chalSqueezes t.sp).getD c (.external 0, 0)).2 % 2 ^ CHAL_BITS s

def enN (t : WrapData) (m e : Nat) : PVar :=
  if e == ENDO_BLOCKS then bullChalV t m
  else enSlot t.sh t.sp m (3 + 2 * (ENDO_BLOCKS + 1) + e)

/-- The transcript's `combined_inner_product` cell — `absorb_shifted` at `:395`, ONE item. -/
def bullCipV (t : WrapData) : PVar :=
  ((t.sp.evs.filter (fun e => e.isAbs && e.tag == T_CIP)).getD 0 default).wordV
def bullCipVal (t : WrapData) : Nat := itemVal T_CIP 0
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
def bullLrVal (r j : Nat) : Nat × Nat := (itemVal T_LR (4 * r + 2 * j), itemVal T_LR (4 * r + 2 * j + 1))
def bullDeltaVal : Nat × Nat := (itemVal T_DELTA 0, itemVal T_DELTA 1)

/-- The three free scalars and the free commitment. ⚠ FIXTURES, and named as such: `advice.b` is
wrap statement slot 1 (W-FINALIZE's), `z₁`/`z₂` and `challenge_polynomial_commitment` are
`openings_proof`'s and have no binder in `wrap_main` at all — which is §13's own note and the reason
`equal_g` refuses no on-curve substitution. -/
def bullScalVal (j : Nat) : Nat := wrapFixtureQ (40 + j) 0
def bullGVal : Nat × Nat := dblAQ (dblAQ (dblAQ (xhatBase 62)))

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
      let l := bullLrVal r 0
      let rr := bullLrVal r 1
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
  let gb := addAQ bullGVal (bu.accs.getLastD (0, 0))
  let z1g := sfLadderQ gb (bullScalVal 1)
  let z2h := sfLadderQ XHAT_H (bullScalVal 2)
  { gm := gm, sfs := [uc, bu, z1g, z2h], res := rd.1, eds := rd.2.1 ++ [ec]
  , terms := terms, reds := reds
  , combOut := combined, lrProd := lrProd, pp := pp, q := q
  , lhs := addAQ (ec.accs.getLastD (0, 0)) bullDeltaVal
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
points, `delta`, then the `ipaRounds` `endo_inv` witnesses. -/
def bullOcVar (t : WrapData) (v : BullData) (i : Nat) : PVar × PVar :=
  let s := t.sh
  if i < 2 * s.ipaRounds then bullLrV t (i / 2) (i % 2)
  else if i == 2 * s.ipaRounds then bullDeltaV t
  else bullResV s t.sp (i - 2 * s.ipaRounds - 1)
def bullOcVal (t : WrapData) (v : BullData) (i : Nat) : Nat × Nat :=
  let s := t.sh
  if i < 2 * s.ipaRounds then bullLrVal (i / 2) (i % 2)
  else if i == 2 * s.ipaRounds then bullDeltaVal
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
    else bullLrVal (m / 2) 1
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
           (caWitnessQ (bullCq t v).1 (bullCq t v).2 bullDeltaVal.1 bullDeltaVal.2)
       , probeRow wired (bullLhsV s sp).1 (bullLhsV s sp).2 ]
  -- (7) `rhs = z₁·(G + b_u) + z₂·H`, then `equal_g`.
  let rhsRows : List WRow :=
    [ caRowQ (bullGV s sp) (sfAccV s sp 1 SF_CHUNKS) (bullGbV s sp)
        (caWitnessQ bullGVal.1 bullGVal.2 (bullBu t v).1 (bullBu t v).2) ]
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
    else bullLrVal (m / 2) 1
  (List.range 43).map (fun i => (bullGm s sp i, (v.gm.getD i 0 : Int)))
  ++ [ ((bullHV s sp).1, (XHAT_H.1 : Int)), ((bullHV s sp).2, (XHAT_H.2 : Int))
     , ((bullGV s sp).1, (bullGVal.1 : Int)), ((bullGV s sp).2, (bullGVal.2 : Int))
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
  -- ⚑ `equal_g`'s witness, COMPUTED off the assembly: `d = lhs − rhs` per coordinate. It is nonzero
  -- at this tree's step key (the header says why), so `bit = 0` and `bulletproof_success = 0`.
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

/-! ## §7 — rows, environment, rungs. -/

inductive Rung where
  | transcript | challenges | branch | bind | key | xhat | split | ftcomm | prev | finalize
  | wraphack | close | combine | bullet
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "w1_transcript" | .challenges => "w2_challenges"
  | .branch => "w3_branch" | .bind => "w4_bind" | .key => "w5_key"
  | .xhat => "w6_xhat" | .split => "w7_split" | .ftcomm => "w8_ftcomm"
  | .prev => "w9_prev" | .finalize => "w10_finalize"
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
  | .close      => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .wraphack, .close]
  | .finalize   => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .finalize]
  | .combine    => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .combine]
  | .bullet     => [.transcript, .challenges, .branch, .bind, .key, .xhat, .split, .ftcomm, .prev,
                    .combine, .bullet]


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
    ∧ rungRows t .wraphack wired = rungRows t .prev wired ++ rungOwn t wired .wraphack
    ∧ rungRows t .close wired = rungRows t .wraphack wired ++ rungOwn t wired .close :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
      = (rungRows t .wraphack wired).length + (rungOwn t wired .close).length := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := rungRows_is_a_ladder t wired
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
  · simp [h10]

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at it — and `pubWords + 1` at
`w9_prev`, whose own row ties `messages_for_next_step_proof` (`wrap_main.ml:350-351`). ⚑ The extra
slot is RESERVED in `AUXW` at every rung, so below `w9_prev` it sits in `placeChecked`'s dead gap and
any gate that touched it would be refused rather than silently absorbed. -/
def rungPub (s : WrapShape) : Rung → Nat
  | .finalize => s.pubWords + 1
  | .bind => s.pubWords
  | .key => s.pubWords
  | .xhat => s.pubWords
  | .split => s.pubWords
  | .ftcomm => s.pubWords
  | .prev => s.pubWords + 1
  -- ⚑ `w11_wraphack` adds the LAST pinned statement word — slot 11 — and `w12_close` inherits it.
  | .wraphack => s.pubWords + 2
  | .close => s.pubWords + 2
  -- ⚑ W-COMBINE derives no NEW statement word — `xi` (slot 9) is W-FINALIZE's, per §10's census —
  -- so it inherits `w9_prev`'s 23 and adds none. A public word on `xi` here would be a fixture.
  | .combine => s.pubWords + 1
  | .bullet => s.pubWords + 1
  | _ => 0

/-- The variables rung `k` exposes as public words. ⚑ `w9_prev` appends ONE — packed statement word
`PREV_MSG_NEXT_STEP`, the MSM's entry 64 — and no rung below it may, because below `w6_xhat` no row
reads that cell and a public word on an unread cell is a public fixture. -/
def exposedVarsAt (t : WrapData) (k : Rung) : List PVar :=
  exposedVars t ++ (match k with
    | .prev => [prevW t.sh t.sp PREV_MSG_NEXT_STEP]
    | .finalize => [prevW t.sh t.sp PREV_MSG_NEXT_STEP]
    | .combine | .bullet => [prevW t.sh t.sp PREV_MSG_NEXT_STEP]
    -- ⚑ …and `w11_wraphack` appends slot 11, the closing `hash_messages_for_next_wrap_proof`
    -- squeeze (`wrap_main.ml:421-431`). `w12_close` inherits it and adds none.
    | .wraphack | .close =>
        [prevW t.sh t.sp PREV_MSG_NEXT_STEP, whDigestVar (whSpongeC t)]
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
      | .finalize => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ finEnv t
      | .wraphack => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ whEnv t
      | .close => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ whEnv t ++ closeEnv t
      | .combine => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ combEnv t
      | .bullet => xhatEnv t ++ splitEnv t ++ ftcEnv t ++ prevEnv t ++ combEnv t ++ bulletEnv t
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
        = "sg_old — ON-CURVE at w9_prev (§18), HASHED at w11_wraphack (§21) into packed statement \
           words 55/56; still a FREE witness, and its consumer is W-COMBINE's ~init" := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-! ### §21a — ⚑ THE PINS ON W-WRAPHACK, and the one that is the point. -/

def tWh : WrapData := tPrev

/-- ⚑ **THE SAME 32 VALUES WITH THE COMMITMENT ABSORBED FIRST** — the order the STEP side uses and
this one does not. It exists only as the red control below; nothing emits it. -/
def whDigestCommitmentFirst (chals : List Nat) (g : Nat × Nat) : Nat :=
  (Dregg2.Circuit.Emit.PastaPoseidonFq.squeeze1 Dregg2.Circuit.Emit.PastaPoseidonFq.fqParams
      (Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany Dregg2.Circuit.Emit.PastaPoseidonFq.fqParams
        Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge ([g.1, g.2] ++ chals))).2

/-- ⚑ **THE TAPE IS `to_field_elements`'s, AND THE ORDER IS THE FACT.**
`composition_types.ml:411-418` flattens the old bulletproof challenges FIRST and appends the
commitment's `[x; y]` LAST. The last conjunct is the red control: the same 32 values in the step
side's order give a DIFFERENT digest, so "absorbed the right values" and "absorbed them in the right
order" are two facts and this file checks both. -/
theorem wraphack_tape_is_the_challenges_then_the_commitment :
    WH_ROUNDS = 15 ∧ WH_PADDED = 2 ∧ WH_ABSORBS = 32
    ∧ (whTape (whOldChals 0) (whSgOld 0)).length = WH_ABSORBS
    ∧ (whTape (whOldChals 0) (whSgOld 0)).getD (WH_ABSORBS - 2) 0 = (whSgOld 0).1
    ∧ (whTape (whOldChals 0) (whSgOld 0)).getD (WH_ABSORBS - 1) 0 = (whSgOld 0).2
    ∧ ((List.range (WH_MLMB * WH_ROUNDS)).all (fun k =>
        (whTape (whOldChals 0) (whSgOld 0)).getD k 0 == whOldChal 0 k)) = true
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
        == whDigestCommitmentFirst (whOldChals 0) (whSgOld 0)) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE FRONT PAD IS THE FRESH STATE, AND TWO EMITTED ROWS PIN IT.** `whPadVectors` is
`2 − max_proofs_verified` in general and `0` at the committed shape, so the opening state is
`Sponge.create`'s zeros — defect class 1 in the place `wrap_hack.ml:26-28` put it. The two `cConst 0`
rows are read off the EMITTED row list, exactly as `key_sponge_seed_is_pinned` does. -/
theorem wraphack_front_pad_is_the_fresh_state_and_the_rows_pin_it :
    whPadVectors WH_MLMB = 0 ∧ whPadVectors 1 = 1 ∧ whPadVectors 0 = 2
    ∧ ((whRows tWh true).getD 0 default).coeffs = cConst 0 ++ cConst 0
    ∧ ((whRows tWh true).getD 1 default).coeffs = cConst 0 ++ cNil
    ∧ ((whRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((whRows tWh true).getD 1 default).kind = KGateType.generic := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The emitter's allocation FORMULA is what `runSpongeQ` actually allocates, for all three sponges
— so the three regions cannot silently overlap. -/
theorem wraphack_sponge_allocation :
    WH_PERMS = 16 ∧ WH_VARS = 115
    ∧ (whSpongeP tWh 0).next = WH_VARS
    ∧ (whSpongeP tWh 1).next = WH_VARS
    ∧ (whSpongeC tWh).next = WH_VARS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE GATE: THE EMITTED SQUEEZE IS THE STATEMENT WORD.** §15c″ computes the three digests as
VALUES and `runSpongeQ` computes them again as a TRAJECTORY of emitted rows; this says the two agree.
A disagreement would make `whRows`' tie rows unsatisfiable and every rung at or above
`w11_wraphack` fail to prove — a red the harness finds, but a red here is cheaper and says which of
the two moved. -/
theorem wraphack_digest_is_the_statement_word :
    whDigestVal (whSpongeP tWh 0) = prevWordVal (PREV_MSG_NEXT_STEP + 1)
    ∧ whDigestVal (whSpongeP tWh 1) = prevWordVal (PREV_MSG_NEXT_STEP + 2)
    ∧ whDigestVal (whSpongeC tWh) = whCloseDigest := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ …and the sponge runs on the TRANSCRIPT's own `sg_old` values, not a second copy of them
(`~sg_old:prev_step_accs`, `wrap_main.ml:412` against `wrap_verifier.ml:538`). -/
theorem wraphack_absorbs_the_transcripts_own_sg_old :
    ((List.range shapeSmoke.prevs).all (fun p =>
      (whSgOld p).1 == itemVal T_SGOLD (2 * p) && (whSgOld p).2 == itemVal T_SGOLD (2 * p + 1)))
      = true
    ∧ ((whSpongeP tWh 0).evs.getD (WH_MLMB * WH_ROUNDS) default).word = itemVal T_SGOLD 0
    ∧ ((whSpongeP tWh 0).evs.getD (WH_MLMB * WH_ROUNDS + 1) default).word = itemVal T_SGOLD 1 := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **RED CONTROL — the digest is a function of every input it absorbs.** Bending the first old
bulletproof challenge, the last one, or either coordinate of `sg_old` moves it. Without this the
theorem above is a number agreeing with a number. -/
theorem wraphack_digest_bends_at_every_probed_input :
    (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf ((whOldChals 0).set 0 0) (whSgOld 0)) = false
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf ((whOldChals 0).set (WH_MLMB * WH_ROUNDS - 1) 0) (whSgOld 0)) = false
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf (whOldChals 0) (qAdd (whSgOld 0).1 1, (whSgOld 0).2)) = false
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf (whOldChals 0) ((whSgOld 0).1, qAdd (whSgOld 0).2 1)) = false
    ∧ (whPrevDigest 0 == whPrevDigest 1) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **WORD 11's OBJECT, CHECKED AGAINST A REAL DEVNET WRAP PROOF — not its slot.**

This module has already shipped the other mistake once: twenty exposed words carried the 255-bit
endo lift where `spec.ml:374-392` packs the raw 128-bit prechallenge, and **the only word with a
different width was the only correct one, which is why nothing caught it.** So the object is checked
here and the instrument is INDEPENDENT: `MinaWrapPublicCommGate.PUBLIC_INPUT` is a Mina devnet
block's own forty Fq wrap words, decoded off the wire. In it, slots 5–8 (`β γ α ζ`, `Challenge` and
`Scalar Challenge`) all fit in `Challenge.length = 128` bits, and slots 10 and 11 — the two
`B Digest`s, `sponge_digest_before_evaluations` and `messages_for_next_wrap_proof` — do NOT. That is
the width tell, measured on a real proof rather than derived from our own layout; and the value this
rung exposes at slot 11 is likewise a full `squeeze_field`, not a truncation of one. -/
theorem wraphack_word_11_is_a_digest_not_a_challenge :
    ((List.range 4).all (fun j =>
      decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD (5 + j) 0
                < 2 ^ WQ_CHAL))) = true
    ∧ decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 10 0 < 2 ^ WQ_CHAL)
        = false
    ∧ decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 11 0 < 2 ^ WQ_CHAL)
        = false
    ∧ decide (whCloseDigest < 2 ^ WQ_CHAL) = false
    ∧ decide (whCloseDigest < qN) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The rung's own public word: slot 11, tied to the closing sponge's squeeze. -/
theorem wraphack_public_word_11_is_the_closing_squeeze :
    rungPub shapeSmoke .wraphack = shapeSmoke.pubWords + 2
    ∧ (exposedVarsAt tWh .wraphack).getD (WH_PUB_SLOT shapeSmoke) default
        = whDigestVar (whSpongeC tWh)
    ∧ (wrapPublicAt tWh .wraphack).getD (WH_PUB_SLOT shapeSmoke) 0 = (whCloseDigest : Int) := by
  refine ⟨rfl, rfl, rfl⟩

/-- The `w11_wraphack` rung is a strict superset of `w9_prev`, its length is the sum of its parts,
and the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns. -/
theorem wraphack_rung_extends_prev :
    (rungRows tWh .wraphack true).length
      = (rungRows tWh .prev true).length + (whRows tWh true).length
    ∧ (rungRows tWh .prev true).length < (rungRows tWh .wraphack true).length
    ∧ (((rungRows tWh .wraphack true).zip (rungRows tWh .wraphack false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tWh .wraphack true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, by decide, rfl⟩

/-- `placeChecked` ACCEPTS the `w11_wraphack` rung at its larger public size and no public word is
inert — and `w9_prev` is REFUSED at that size, because no `w9_prev` gate reads slot `pubWords + 1`.
That is what makes `AUXW`'s second reserved slot a gate rather than a comment. -/
theorem wraphack_rung_places_and_the_rung_below_it_does_not :
    refusalOf shapeSmoke (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .wraphack true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .wraphack true)) = []
    ∧ inertPublicWords (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .prev true)) = [WH_PUB_SLOT shapeSmoke] := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE TWENTY-FOUR ARE DERIVED, AND TWENTY-FOUR IS NOT FORTY.** `WRAP_PINNED_SLOTS` is what
`wrap_main` actually constrains; `WRAP_UNPINNED` is the rest, by REASON and by owner. A run that
reads "public inputs: ours 24, mina 40" and calls the remaining sixteen a gap in this assembly would
be reading a deferred value and a zero pad as work. -/
theorem wraphack_closes_every_pinned_statement_word :
    WRAP_PINNED_WORDS = 24
    ∧ WRAP_PINNED_SLOTS.length = 24
    ∧ WRAP_PRIMARY_LEN - WRAP_PINNED_WORDS = 16
    ∧ WRAP_UNPINNED.length = 4
    ∧ rungPub shapeSmoke .wraphack = shapeSmoke.pubWords + 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚠ ⚑ **THE CENSUS DID NOT MOVE, AND `sg_old`'s ENTRY IS REWRITTEN RATHER THAN STRUCK.**
W-WRAPHACK gives `sg_old` a real consumer — it is hashed into packed statement words 55/56, which the
x_hat MSM consumes as entries 65/66. It is still a FREE witness: the digest is a function of it, but
nothing forces the digest to any particular value, because what the MSM's output feeds is `x_hat`,
which is itself absorbed and unconsumed. A prover still chooses `sg_old` subject only to
`assert_on_curve`. Striking the entry here would be the metric-gaming this census exists to refuse.
The count stays **8**. -/
theorem wraphack_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED.getD 0 ""
        = "sg_old — ON-CURVE at w9_prev (§18), HASHED at w11_wraphack (§21) into packed statement \
           words 55/56; still a FREE witness, and its consumer is W-COMBINE's ~init" := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### §22a — ⚑ THE PINS ON W-CLOSE. -/

/-- One `Generic` half's residue at a witness: `c₀w₀ + c₁w₁ + c₂w₂ + c₃w₀w₁ + c₄`
(`generic.rs:283-314`). Two lines, here, so §22's refusal is an ARITHMETIC statement about the
emitted coefficients rather than a restatement of `cConst`'s definition. -/
def genericHalfAt (c : List Int) (w0 w1 w2 : Int) : Int :=
  c.getD 0 0 * w0 + c.getD 1 0 * w1 + c.getD 2 0 * w2 + c.getD 3 0 * w0 * w1 + c.getD 4 0

/-- **W-CLOSE emits `Boolean.Assert.is_true bulletproof_success` and one σ-only probe.** -/
theorem close_asserts_bulletproof_success :
    (closeRows tWh true).length = 2
    ∧ ((closeRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((closeRows tWh true).getD 0 default).coeffs = cConst 1 ++ cNil
    ∧ ((closeRows tWh true).getD 0 default).perm.getD 0 none
        = some (bpSuccessVar shapeSmoke tWh.sp)
    ∧ ((closeRows tWh true).getD 1 default).probe = true
    ∧ ((closeRows tWh true).getD 1 default).kind = KGateType.zero := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ …and the emitted coefficients REFUSE a failed opening: the half is satisfied at
`bulletproof_success = 1` and violated at `0`, which is the whole content of
`Boolean.Assert.is_true`. The honest witness this file emits is the `1`. -/
theorem close_refuses_a_failed_opening :
    genericHalfAt (cConst 1) 1 0 0 = 0
    ∧ genericHalfAt (cConst 1) 0 0 0 ≠ 0
    ∧ (closeEnv tWh).getD 0 ((.external 0 : PVar), (0 : Int))
        = (bpSuccessVar shapeSmoke tWh.sp, (1 : Int)) := by
  refine ⟨rfl, by decide, rfl⟩

/-- The `w12_close` rung is the ladder's top: two more rows, no new public word, and it places. -/
theorem close_rung_extends_wraphack :
    (rungRows tWh .close true).length = (rungRows tWh .wraphack true).length + 2
    ∧ rungPub shapeSmoke .close = rungPub shapeSmoke .wraphack
    ∧ refusalOf shapeSmoke (rungPub shapeSmoke .close)
        (wrapGates (rungRows tWh .close true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .close)
        (wrapGates (rungRows tWh .close true)) = [] := by
  refine ⟨rfl, rfl, rfl, rfl⟩



/-! ### §23b/§24c — ⚑ **W-COMBINE'S AND W-BULLET'S PINS, AS NAMED THEOREMS.**

⚠ **AND WHAT IS *NOT* HERE, SAID FIRST.** The other sub-circuits' pin blocks read facts off the
EMITTED ROW LIST (`xhat_every_ladder_seed_is_pinned`, `ftc_every_ladder_seed_is_pinned`). These two
rungs cannot: `combRows`/`bulletRows` evaluate 34 and 7 thirty-two-block `EndoMul` ladders at the
smoke shape — five `qInv` a block, each a 254-bit modular exponentiation — and reducing that in the
KERNEL is the shape that took this module from 150 s to a 9.6 GB ceiling once before (§7's note on
`circuitEnvAt`). What IS closed in the kernel is the CENSUS and the LAYOUT, which is where the
mistakes that survive a green prove actually live; the row-level facts are established by the
harness's five polarities per rung, and that is a weaker instrument, stated rather than blurred. -/

/-- ⚑ **THE CENSUS THAT CLOSES `wrap-transaction`'s `EndoMul`.** Mina's own compiled `wrap_main`
carries **2528** `EndoMul` gates and this assembly carried **zero** before these two rungs. They are
`32 × (46 + 33)`: W-COMBINE's one ladder per fold step over `Nat.N45.n + Max_proofs_verified.n`
commitments, and W-BULLET's `endo_inv`+`endo` per IPA round plus `Scalar_challenge.endo q c`.
⚑ The last two conjuncts are what makes this a GATE rather than an arithmetic identity: a fold that
started at the FIRST commitment instead of `~init`, or `Tock`'s 15 rounds instead of `Tick`'s 16,
both miss — by one ladder and by two ladders respectively. -/
theorem comb_and_bullet_close_minas_endomul_census :
    combTerms shapeWrap = 47
    ∧ combSteps shapeWrap = 46
    ∧ bullNE shapeWrap = 33
    ∧ ENDO_BLOCKS * (combSteps shapeWrap + bullNE shapeWrap) = 2528
    ∧ ENDO_BLOCKS * (combTerms shapeWrap + bullNE shapeWrap) ≠ 2528
    ∧ ENDO_BLOCKS * (combSteps shapeWrap + (2 * 15 + 1)) ≠ 2528 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ …and the `VarBaseMul` census, which is now a THREE-WAY closure over three sub-circuits.
`wrap-transaction` carries 2417: W-XHAT's 1805, W-FTCOMM's `(tComms + 1) × 51 = 408`, and
W-BULLET's four `scale_fast` at 255 bits. If this rung lands 204 and the total is not 2417, something
else moved — which is exactly what the identity is for. -/
theorem bullet_closes_minas_var_base_mul_census :
    BULL_SF * SF_CHUNKS = 204
    ∧ 1805 + (shapeWrap.tComms + 1) * FTC_CHUNKS + BULL_SF * SF_CHUNKS = 2417
    ∧ SF_CHUNKS = FTC_BITS / BITS_PER_CHUNK
    ∧ 1805 + (shapeWrap.tComms + 1) * FTC_CHUNKS ≠ 2417 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE 47 ARE `wrap_verifier.ml:687-706`'s OWN LIST**, position by position — and the fold
runs BACKWARDS down it, so `combIdx` is a decreasing enumeration whose last two entries are the
`sg_old` pair. A fold that ran forwards would have identical gate counts and would put the mux at
the wrong end. -/
theorem comb_fold_runs_backwards_and_ends_on_sg_old :
    combIdx shapeWrap 0 = 45
    ∧ combIdx shapeWrap (combSteps shapeWrap - 1) = 0
    ∧ (List.range (combSteps shapeWrap)).filter (combIsMux shapeWrap)
        = [combSteps shapeWrap - 2, combSteps shapeWrap - 1]
    ∧ ((List.range (combSteps shapeWrap)).map (combIdx shapeWrap)).length = 46 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **BOTH ARMS OF `Inner_curve.if_` ARE LIVE IN THE HONEST WITNESS.** `mkWrapWith` witnesses
branch 1 at widths `[0,1,2,…]`, so `first_zero = 1` and `Vector.rev (ones_vector ~first_zero:1 2)`
is `[0, 1]` — one `sg_old` kept and one dropped. A `keep` that were constant would make the mux
dead weight and the rung's own distinguishing feature untested. -/
theorem comb_mux_takes_both_branches :
    (List.range MASK_N).map (combKeepVal (mkWrap shapeSmoke)) = [0, 1]
    ∧ (List.range MASK_N).map (combKeepVal (mkWrap shapeWrap)) = [0, 1] := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **ALL 46 LADDERS' COUNTERS LAND ON ONE CELL.** `Field.Assert.equal !n_acc scalar`
(`scalar_challenge.ml:305`) is emitted as a σ class rather than as a row, which is upstream's shape
and is what makes `xi` a single deferred value rather than 46 independent draws. The second
conjunct is the non-vacuity: the INTERIOR counters are all distinct from it and from each other. -/
theorem comb_all_ladders_share_one_xi :
    ((List.range (combSteps shapeSmoke)).map (fun a =>
        combN shapeSmoke (mkWrap shapeSmoke).sp a ENDO_BLOCKS)).all
      (· == combXiV shapeSmoke (mkWrap shapeSmoke).sp) = true
    ∧ ((List.range (combSteps shapeSmoke)).map (fun a =>
        combN shapeSmoke (mkWrap shapeSmoke).sp a 0)).all
      (· != combXiV shapeSmoke (mkWrap shapeSmoke).sp) = true
    ∧ combXiVal < 2 ^ ENDO_BITS := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE REGIONS DO NOT OVERLAP.** W-COMBINE's cells start above W-FTCOMM's last and W-BULLET's
above W-COMBINE's last, at both shapes. ⚠ W-COMBINE's base is `baseFin`'s — see §23a: `.combine` and
`.finalize` are sibling branches off `.prev` and no `rungsUpto` contains both, so no emitted circuit
holds cells from both regions. This is the pin that would go red if that stopped being true and one
rung started emitting both. -/
theorem comb_and_bullet_regions_are_disjoint :
    baseComb shapeSmoke (mkWrap shapeSmoke).sp
      = baseFtc shapeSmoke (mkWrap shapeSmoke).sp + nFtcVars shapeSmoke (mkWrap shapeSmoke).sp
    ∧ baseBull shapeSmoke (mkWrap shapeSmoke).sp
      = baseComb shapeSmoke (mkWrap shapeSmoke).sp + nCombVars shapeSmoke
    ∧ (rungsUpto .combine).contains .finalize = false
    ∧ (rungsUpto .bullet).contains .finalize = false
    ∧ (rungsUpto .bullet).contains .combine = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE COMMITMENTS THE FOLD READS ARE THE TRANSCRIPT'S OWN CELLS**, position by position —
`sg_old`, `x_hat`, `ft_comm`, `z_comm` and `w_comm` at `wrap_verifier.ml:687-706`'s offsets. This is
what "W-COMBINE consumes them" MEANS, and it is why §2c's entries can be rewritten: bend any one of
those words and 46 ladders' gate polynomials move.

⚠ ⚑ **AND IT IS PINNED ON THE VARIABLES, NOT ON THE PROSE.** The first draft of this theorem was a
`decide` over `String.startsWith` on `WRAP_UNCONSUMED`'s sentences. It did not go FALSE when another
lane reworded an entry — it went STUCK, because `String.startsWith` does not kernel-reduce, and
"stuck" reads like a build error rather than a broken claim. A census entry is prose three lanes
edit; a variable identity is not. ⚠ Three of those entries still read "needs W-COMBINE" for exactly
that reason — five pins in the W-WRAPHACK and W-FINALIZE blocks quote them verbatim, so rewording
them is a coordinated edit and not this rung's to make alone. -/
theorem comb_reads_the_transcripts_own_commitment_cells :
    (combPtVar (mkWrap shapeSmoke) 0).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_SGOLD)).getD 0
          default).wordV
    ∧ (combPtVar (mkWrap shapeSmoke) shapeSmoke.prevs).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 0
          default).wordV
    ∧ combPtVar (mkWrap shapeSmoke) (shapeSmoke.prevs + 1)
      = ftcOutV shapeSmoke (mkWrap shapeSmoke).sp
    ∧ (combPtVar (mkWrap shapeSmoke) (shapeSmoke.prevs + 2)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_ZCOMM)).getD 0
          default).wordV
    ∧ (combPtVar (mkWrap shapeSmoke) (shapeSmoke.prevs + 3 + KEY_SINGLES)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_WCOMM)).getD 0
          default).wordV := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **`lr` AND `delta` ARE ON THE CURVE NOW, AND THE OLD FILLER WAS NOT.** This is the flag day
§2d's `itemVal` carries, exhibited rather than described: the `wrapFixture` values that stood there
are not points, so `Scalar_challenge.endo_inv` had no witness over them at all. -/
theorem wrap_lr_and_delta_are_curve_points :
    onCurveQ (itemVal T_LR 0, itemVal T_LR 1) = true
    ∧ onCurveQ (itemVal T_LR 2, itemVal T_LR 3) = true
    ∧ onCurveQ (itemVal T_DELTA 0, itemVal T_DELTA 1) = true
    ∧ onCurveQ (wrapFixture T_LR 0, wrapFixture T_LR 1) = false
    ∧ onCurveQ (wrapFixture T_DELTA 0, wrapFixture T_DELTA 1) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **W-BULLET's LAYOUT IS ITS SOURCE'S SHAPE.** Four `scale_fast` (`uc`, `b_u`, `z₁·(G+b_u)`,
`z₂·H`), `2·ipaRounds + 1` endo ladders, and `3·ipaRounds + 1` points through `Inner_curve.typ`
(the `2·ipaRounds` `lr`, `delta`, and the `ipaRounds` `endo_inv` witnesses). ⚠ NOT
`challenge_polynomial_commitment` — §24's header says why, and the count is what makes the omission
visible instead of silent. -/
theorem bullet_layout_is_check_bulletproofs_shape :
    BULL_SF = 4
    ∧ bullNE shapeWrap = 2 * shapeWrap.ipaRounds + 1
    ∧ bullOCPts shapeWrap = 3 * shapeWrap.ipaRounds + 1
    ∧ shapeWrap.ipaRounds = 16
    ∧ EN_STRIDE = 3 + 2 * (ENDO_BLOCKS + 1) + ENDO_BLOCKS
    ∧ SF_STRIDE = 2 * (SF_CHUNKS + 1) + SF_CHUNKS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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
  7. ⚡ **W-FINALIZE — ITS SCALAR HALF LANDS at `w10_finalize`** (§19), and the half that does not
     is named here rather than left to a reader to notice.
     ⛑ **`Scalars.Tock` IS NOT `Scalars.Tick` WITH DIFFERENT LITERALS**, whatever
     `plonk_checks/scalars.ml:104` says — and the shape of the difference is now MEASURED, not
     inferred from the `_`-bindings. Diffed at source with hex literals normalised: the
     `let x_0 … let x_48` prefix (225 lines) is **identical**, and the tails diverge at exactly ONE
     hunk (`@@ -576,1813 +576,4 @@`) — `Tick` continues for 1813 lines of `if_feature` arms
     (`RangeCheck0/1`, `ForeignFieldAdd/Mul`, `Xor16`, `Rot64`, lookup), `Tock` for 4 (a trailing
     `+ field 0x0`). Those arms are the ONLY consumers of `beta`, `gamma`, `joint_combiner`,
     `unnormalized_lagrange_basis`, `vanishes_on_last_4_rows` and `if_feature`, which is WHY `Tock`
     binds all six to `_`. So `Tock.constant_term` is exactly the six always-on gate bodies —
     Poseidon 15 (α¹⁻¹⁴), VarBaseMul 21 (α¹⁻²⁰), CompleteAdd 7, EndoMul 11, EndoMulScalar 11,
     Generic 2 — and §19b emits those and nothing else. ⚠ The alpha powers really ARE shared across
     the gates (`alpha_pows` is ONE `Array.create ~len:71`, `plonk_checks.ml:330-338`); §19 emits
     that unaltered, as §15 emits `scale_fast`'s two admissible decompositions unaltered.
     ✅ **WHAT `w10_finalize` EMITS**, per instance and `prevs` instances: `scalars_env`'s
     ω⁻¹/ω⁻²/ω⁻³ (the first a WITNESS the program checks by `ω·ω⁻¹ = 1`), `zk_polynomial`,
     `ζⁿ − 1` by 14 squarings at the wrap domain `2^14`, the α⁰..α²³ chain, `Scalars.Tock`'s constant
     term, `ft_eval0` (`plonk_checks.ml:420-460`, C5 denominator by a second CHECKED witnessed
     inverse), `Plonk_checks.checked`'s `perm` scalar compared through `Shifted_value.Type2.to_field`
     against packed statement word 4, and `Boolean.Assert.any [finalized; not should_finalize]`.
     Its α and ζ arrive through two `to_field_checked` chains at `ENDO_Q`, through §5's SHARED endo
     cell; β and γ are the RAW packed words, which is `map_plonk_to_field`'s own split.
     ❌ **WHAT IT DOES NOT EMIT, AND WHAT THAT COSTS.** Three of `Boolean.all`'s four legs —
     `xi_correct`, `b_correct`, `combined_inner_product_correct` — all need the finalize SPONGE
     (`:844-894`: absorb `sponge_digest_before_evaluations`, a nested challenge-digest sponge over
     the padded old bulletproof challenges, `ft_eval1`, both `public_input` evals and the 86-cell
     absorption sequence, then squeeze ξ and r). Emitting ξ or r as free witnesses to get the legs
     would be a witness nothing constrains, so they are NOT emitted. ⛑ That sponge is also where
     wrap's largest remaining GATE gap lives: a calibrated census against Mina's real
     `wrap-transaction` blob puts us **979 Poseidon against 2871**, and ≈122 of the 172 missing
     `(Poseidon × 11, Zero)` blocks are these two sponges at `prevs = 2`.
     ⚠ **AND THE `EndoMulScalar` DIVERGENCE IS THIS RUNG'S SHAPE, NOT ITS COUNT.** Mina's blob has
     `EndoMulScalar × 120` twice — `compute_challenges` (`:1012-1013`) lifting all fifteen
     bulletproof challenges in ONE unbroken run, once per instance — plus `×24` twice and `×16` six
     times. We cannot reach a ×120 run: §5's `tfcRowsQ` brackets every chain with its own seed pins
     and lift row, because upstream's `a₀`/`b₀` are one constant `Cvar` and its `a₈`/`b₈` closing is a
     `Cvar` linear combination that emits NO row (the three cells the region-conformance report
     already names). Fifteen chains therefore come out as fifteen `×8` blocks, not one `×120`. That
     is this file being STRICTER, so it is a shape divergence to state and not a row count to claim
     — and it is why `w10_finalize` emits the two lifts `map_plonk_to_field` needs and leaves
     `compute_challenges` with the sponge, where its consumer (`b_correct`) is.
     ⚠ Wrap public words 0–4 and 9 are still NOT derived: they are the WRAP statement's own deferred
     values, CONSUMED by W-FTCOMM/W-COMBINE/W-BULLET, and this rung consumes the PREVIOUS
     statement's — packed words 4, 6, 7, 8, 9 and 26 of each block, six per instance that were
     absorbed-but-not-consumed at `w9_prev`.
  8. ✅ **W-WRAPHACK — LANDED at `w11_wraphack`** (§24). All THREE
     `hash_messages_for_next_wrap_proof` sponges (`wrap_hack.ml:110-137` at `wrap_main.ml:341-348`
     and `:421-431`): 32 absorbs and one `squeeze_field` each, **16 Fq permutations per sponge, 48
     for the rung**. ⚑ **It closes the public vector.** Wrap statement word 11 is the closing
     sponge's squeeze, and with it **every one of the twenty-four statement words `wrap_main` pins
     is derived** (`WRAP_PINNED_SLOTS`; the other sixteen of forty are W-FINALIZE's six deferred
     values and ten constant-or-dead slots, `WRAP_UNPINNED`). Packed statement words 55 and 56 stop
     being fixtures and become the two prev-proof squeezes, which is what gives `old_bp_chals` its
     only consumer and `prev_step_accs` a second one.
     The sizing notes this entry carried were RIGHT and are kept: absorption order is **all old
     bulletproof challenges first, flattened, THEN the commitment as `[x; y]`**
     (`composition_types.ml:411-418`) — the opposite of the step side's interleaving, and
     `wraphack_tape_is_the_challenges_then_the_commitment` exhibits the other order giving a
     different digest — and the padding is at the FRONT via a PRECOMPUTED sponge-state table indexed
     by `2 − max_proofs_verified` (`wrap_hack.ml:99-109,124-137`), not by absorbing dummies in
     circuit. ⚠ **What the note got wrong is that word 11 "needs W-FINALIZE too".** It does not need
     it to be DERIVED — the sponge is over `new_bulletproof_challenges` and
     `openings_proof.challenge_polynomial_commitment` whatever they are, and word 11 is its squeeze
     either way. What W-FINALIZE and W-OPENINGS would add is that those 32 cells stop being free
     witnesses, and §21 says that in its own header rather than banking it here.
     ⚠ **AND THE `mlmb < 2` PAD IS NOT EMITTED**: `WH_MLMB = WH_PADDED = 2` fixes every opening
     state at `Sponge.create`'s zeros. The other case needs `Dummy.Ipa.Wrap.challenges_computed`
     (`dummy.ml:30-35`), an OCaml random-oracle draw with no independent source in this tree, and
     emitting a fixture constant for it would be defect class 5 inside the pad. `whPadVectors` is in
     the file so the general statement is, and the instance is a SHAPE choice that is said.
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
 10. ✅ **W-CLOSE — LANDED at `w12_close`** (§22). `wrap_main.ml:419-420`,
     `Boolean.Assert.is_true bulletproof_success`: **ONE `Generic` half and one σ-probe**, and the
     sizing note that said so was right. ⚠ Its input is W-BULLET's `` `Success ``, free here, so what
     the rung buys is narrow and stated as such in §22: a witness whose opening FAILED is refused.
     It is not a claim that the opening is checked — `equal_g` is not in this circuit at all.
 11. **W-OPENINGS** `wrap_main.ml:357-383` — `exists (Openings.Bulletproof.typ … Inner_curve.typ
     ~length:Tick.Rounds.n)`. It was named in the header's map and never carried an entry here; it
     is the `assert_on_curve` on `openings_proof.challenge_polynomial_commitment` (and the `lr`
     pairs), i.e. three `Generic` rows per point, plus the `Shifted_value.Type1` transports which
     emit nothing. §21 absorbs that commitment and does NOT check it; that check is this entry's.

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
