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

## ⚑ WHAT THIS FILE ASSEMBLES TODAY — eleven rungs on this branch, and the rest named

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
    w11_wraphack        2250        7981*      24    wrap_hack.ml:110-137 at :341-348 and :421-431
    w12_close           2252        7983*      24    wrap_main.ml:419-420

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
    w11_wraphack    2258    4096           995 ms        REJECTED   ACCEPTED   REJECTED
    w12_close       2260    4096           941 ms        REJECTED   ACCEPTED   REJECTED

(the `rows` column here is `pubWords + rows`, which is what the harness prints; the table above is
the emitter's row count.) ⚑ At `w9_prev` the public-input leg runs at **i = 0 and i = 6** — the new
word is the last one, so the σ leg "flip cell (i,0) AND tell the verifier the new value" is tested
on it specifically, and it is REJECTED by the copy-permutation alone. ⚑ **At `w11_wraphack` and
`w12_close` it runs at i = 0 and i = 7**, and 7 is wrap statement word 11 — the closing
`hash_messages_for_next_wrap_proof` squeeze. The rung's whole point is that word, and the leg that
tests it is the one that would go green on a public fixture.
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
  * `w11_wraphack` = `7344 + 637` and `w12_close` = `7981 + 2`, and these two are the SAFEST
    derivations in the table: `whRows` and `closeRows` depend on the shape only through `s.prevs`,
    which is **2 at both shapes**, so the wrap delta IS the smoke delta — `2250 − 1613 = 637` and
    `2252 − 2250 = 2`, both measured. 637 = three sponges × 211 rows + 4 tie rows, where a sponge is
    2 init rows + 15 × (1 absorb-pair row + 12 permutation rows) + (1 + 12 + 1) for the closing
    absorb pair, the squeeze's permutation and its σ-probe;
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

  * **`Poseidon` — every instance this assembly emits matches a `wrap-transaction` class byte for
    byte**, the WHOLE 11-row permutation INCLUDING all fifteen round constants per row. The Fq
    Poseidon gadget this file emits IS the one Snarky emits in Mina's own wrap circuit. It was 61
    blocks before W-KEY's index sponge, 89 after, and **137 after W-WRAPHACK's three
    `hash_messages_for_next_wrap_proof` sponges added 48** (16 permutations each: 15 for the 32
    absorbs at rate 2, plus the squeeze's). The per-instance 100% does not move with the count.
    ⚠ ⚑ **AND THE COUNT IS NOT THE CIRCUIT.** Mina's `wrap-transaction` carries **261**
    `Poseidon × 11` blocks. Quoting "89/89, 100%" as though it were a coverage figure — this
    header did — reads a per-instance fidelity result as a whole-circuit one; it was 89 of 261,
    i.e. 34%, and it is 137 of 261 now. The remainder is W-FINALIZE's two `finalize_other_proof`
    sponges at `prevs = 2` (≈122 blocks) and is named in §13 item 7, not implied by a percentage.
    ⚑ **AND THE 48 W-WRAPHACK ADDED INTRODUCE NO NEW SIGNATURE**, measured on the emitted smoke JSON
    rather than argued: `w9_prev` carries 46 `Poseidon` runs, `w11_wraphack` 94, **every one of them
    eleven rows long and every one of them the SAME single coefficient signature** — the class
    already graded byte-for-byte against `wrap-transaction`. So this rung cannot have moved the
    per-instance Poseidon verdict in either direction; it emitted 48 more of exactly the block that
    was already conformant. That is the cheap half of the conformance question, and it is the half
    that does not need a wrap-scale emission.
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
`fixtures/kimchi-extractors/step_vk_index_export.rs` **asserts** they are all `None` before it
dumps. Without that assertion the 56 numbers would be a PREFIX of the digest's preimage wearing the
name of the whole of it — and, exactly as in the 20-words case, nothing downstream would notice.

## Axiom hygiene / build

NO `main` (roots into `PicklesSynthesis`; the emit driver is `EmitWrapMainJson.lean`). No `sorry`,
no `decide` over the big grid, and **exactly ONE `native_decide`** — §24's
`bullet_solves_g_on_curve_and_equal_g_is_one`, whose subject is `bullData` (34 + 33 ladders) and does
not whnf inside the heartbeat budget. It is pinned by `#assert_compiled` at its site and NAMED in the
`except` clause at the foot of the file, so the compiler-trust is accounted rather than hidden. Every
other fact is a NAMED THEOREM closed by `rfl`/`decide` IN THE KERNEL — strictly stronger than the
`#guard`s they would have been (`metatheory/docs/GUARD-DISCIPLINE.md`) — and
`#assert_namespace_axioms` accounts for every one of them. The remaining `#guard`s reduce in the interpreter and are the
conversion backlog, not the model.

## ⚑ THIS FILE IS AN UMBRELLA. THE CONTENT IS IN THE MODULES BELOW.

`KimchiWrapMain.lean` reached **7,092 lines** and stopped being elaborable in one piece: a lane
building §20 was memory-killed (`Lean exited with code 137`, twice, 2026-08-04) and one edit to a
single constant in `KimchiWrapMainField` cost **287 s** to see green again. It is now split the way
`KimchiStepMain` was, and for the same measured reason.

**THE NAMESPACE IS UNCHANGED.** Every module below opens `Dregg2.Circuit.Emit.KimchiWrapMain`, so no
declaration is renamed and every consumer that imports this file sees exactly what it saw before.

  * `KimchiWrapMainField`       — the Fq value layer and the statement-word fixtures
  * `KimchiWrapMainCore`        — ALL of §0–§8: the emitter. This is what emits.
  * `KimchiWrapMainFixture`     — the pinned instances §11–§24 measure
  * `KimchiWrapMainPins01`      — the CONSTANT PINS (§11, §11b endo scalar, §11c Branch_data.pack, §11d the field)
  * `KimchiWrapMainPins02`      — ⚑ the REALITY GATE (§12a): the transcript sponge of a REAL accepted proof, in the kernel
  * `KimchiWrapMainPins03`      — the smoke-instance pins (§12b ladder · §12c–§12e defect classes · §12f rate-2 · §12g/h census)
  * `KimchiWrapMainPins04`      — §14b — W-KEY
  * `KimchiWrapMainPins05`      — §15f — W-XHAT (the public-input MSM reductions)
  * `KimchiWrapMainPins06`      — §16b — W-SPLIT
  * `KimchiWrapMainPins07`      — §17b — W-FTCOMM
  * `KimchiWrapMainPins08`      — §18b — W-PREV
  * `KimchiWrapMainPins09`      — §21a — W-WRAPHACK
  * `KimchiWrapMainPins10`      — §22a — W-CLOSE
  * `KimchiWrapMainPins11`      — §23b/§24c — W-COMBINE and W-BULLET (carries the one `native_decide`)

⚑ **THE IN-FILE RULE THAT KEEPS THIS STABLE — it is the step side's and it is not negotiable:**
**a `def` goes in `…Core` (or `…Fixture` if only the pins read it); a pin goes in its section's
`…PinsNN`.** A `def` added to a `…PinsNN` re-couples that section to every other one and the split
starts silently undoing itself.

⚠ **AND EVERY MODULE CARRIES THE `set_option` PREAMBLE VERBATIM.** `set_option` does not cross an
import. `KimchiWrapFinalizeSpongeGate` was split off without it and shipped FOUR proofs as `sorryAx`
— each still in the environment, each with the right statement, no `sorry` token anywhere in the
file. The only thing that caught it was the namespace-wide axiom pin at the foot of this file, which
is why that pin lives here (where it sees every imported module) and why it must never be dropped.

## ⚑ WHAT THE SPLIT DID NOT CHANGE

The emitted circuit. All 28 `wrapmain_smoke_*` rungs were emitted before and after and compared
byte for byte; see the commit that landed the split.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainCore
import Dregg2.Circuit.Emit.KimchiWrapMainFixture
import Dregg2.Circuit.Emit.KimchiWrapMainPins01
import Dregg2.Circuit.Emit.KimchiWrapMainPins02
import Dregg2.Circuit.Emit.KimchiWrapMainPins03
import Dregg2.Circuit.Emit.KimchiWrapMainPins04
import Dregg2.Circuit.Emit.KimchiWrapMainPins05
import Dregg2.Circuit.Emit.KimchiWrapMainPins06
import Dregg2.Circuit.Emit.KimchiWrapMainPins07
import Dregg2.Circuit.Emit.KimchiWrapMainPins08
import Dregg2.Circuit.Emit.KimchiWrapMainPins09
import Dregg2.Circuit.Emit.KimchiWrapMainPins10
import Dregg2.Circuit.Emit.KimchiWrapMainPins11

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

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
  8. ✅ **W-WRAPHACK — LANDED at `w11_wraphack`** (§21). All THREE
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

-- ⚠ ⚑ THE ONE EXCEPTION, AND IT IS NAMED RATHER THAN WAIVED.
-- `bullet_solves_g_on_curve_and_equal_g_is_one` rests on `native_decide` oracle axioms because
-- `bullData` does not whnf inside the heartbeat budget; it is pinned by `#assert_compiled` at its
-- own site, which is a RED path in both directions (a `sorry` still fails, and a kernel-clean fact
-- pinned there ALSO fails). Nothing else in this namespace is compiler-trusted.
#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapMain
  except bullet_solves_g_on_curve_and_equal_g_is_one

end Dregg2.Circuit.Emit.KimchiWrapMain
