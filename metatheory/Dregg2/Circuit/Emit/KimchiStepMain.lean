/-
# Dregg2.Circuit.Emit.KimchiStepMain — `step_verifier.verify_one`, assembled in Lean

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiComposeStepFragment` proved the MSM *shape* at scale (132 rows, four gate types, 13 σ-only
probes rejected, a 4058-row ladder). **This file assembles the recursive verifier itself**, in the
five named sub-circuits `verify_one` runs, each provable on its own and each composing into the next.

## ⚑ THE TARGET, CORRECTED (read this before quoting a fraction)

`StepTransactionProof` is `{PRIMARY_LEN 67, ROWS 17806}` — and it is instantiated with
**`N_PREVIOUS = 0`** (`~/dev/mina-rust/crates/ledger/src/proofs/transaction.rs:4286`
`step::step::<StepTransactionProof, 0>`). **Those 17806 rows contain ZERO `verify_one` calls**; they
are the transaction-application `rule.main` plus `hash_messages_for_next_step_proof`. The row
identity is `ROWS = gate_rows + PRIMARY_LEN` (`transaction.rs:3830`), so 17739 gate rows + 67.

The recursive verifier is exercised by the branches that HAVE previous proofs:
`StepMergeProof` (2 prevs, ROWS 29010, `merge.rs:212,276`), `StepBlockProof` (2 prevs, 34797),
`StepZkappProvedProof` (1 prev, 20023). Costed from Snarky's own emitters
(`plonk_constraint_system.ml`; `Ops.add_fast` = 1 `CompleteAdd`; `scale_fast2 ~num_bits:128` =
26 chunks × 2 + 2 = **54 rows**; `~num_bits:255` = 51 × 2 + 2 = **104**; `Scalar_challenge.endo
~num_bits:128` = 32 `EndoMul` + 1 `Zero` + 2 `CompleteAdd` = **35**; `to_field_checked ~num_bits:128`
= **8 `EndoMulScalar`**; one Poseidon permutation = 11 + 1 = **12**), ONE `verify_one` is
**≈ 6.7k rows**:

  * x_hat MSM (`multiscale_known`)             ≈ 1972 `var_base_mul`-family rows + ~30 adds
  * the 47-commitment fold (`combine_split_commitments`) 46 × (endo 35 + add 1) = **1656**
  * `bullet_reduce`, 15 rounds                  15 × (2 endo + add) + 14 add = **1079**
  * `ft_comm`                                   8 × 104 + 8 = **840** — ASSEMBLED (§6b), and it
    MEASURES 901 rows here: `104` is `Ops.add_fast = 1 CompleteAdd` costing only, and the emitted
    ladder also carries `Shifted_value.Type2`'s split, `scale_fast2`'s top-bit assert, the `G.if_`
    mux and the σ-only probes
  * `check_bulletproof` tail                    ≈ **460**
  * `finalize_other_proof`                      ~20 × 8 endo-scalar = 160, + ≈ 560 poseidon

**That ≈ 6.7k-row `verify_one` is this file's target**, and the committed shape is sized against its
line items, not against a round number.

## THE EIGHT SUB-CIRCUITS

  * **R1 `transcript`** — the Fp Poseidon SPONGE: an init pin, then `absorbs` absorb blocks (a
    `Generic` absorb row + an 11-row `Poseidon` permutation + its output `Zero` row) and `chals`
    squeeze permutations **INTERLEAVED IN `incrementally_verify_proof`'s OWN ORDER** (§2b, the
    schedule, `step_verifier.ml:534-574` then `:247-340`). The sponge STATE crosses every block
    boundary as a σ class — the thing no prior rung had: `KimchiRenderPoseidon` proved ONE
    permutation with an IDENTITY permutation (`sevenNones`, self-wired), so a `Poseidon` gate had
    never been copy-wired to anything.
    ⚑ …and since 2026-08-02 the interleaving is upstream's. R1 used to run **all** `absorbs` absorb
    blocks and **then** all `chals` squeezes, with its absorb order the `ipaAbsorbs` FILTER order
    (`z_comm` ahead of `w_comm`, the gammas ahead of `t_comm`). Both were wrong of an order-sensitive
    object, and the all-absorbs-first shape is what made `combined_inner_product` unwireable: an
    absorption at any position would have made β/γ/α/ζ depend on a value the transcript determines.
    Upstream absorbs it at `:256`, AFTER ζ at `:568`, so it has no cycle — and neither does this now.
  * **R2 `challenges`** — `to_field_checked` (`scalar_challenge.ml:12-128`, `bits_per_row = 16`)
    TWICE per squeezed challenge, because `lowest_128_bits ~constrain_low_bits:true` range-checks
    BOTH parts (`util.ml:98-99`) and `assert_n_bits ~n:128` IS a `to_field_checked`
    (`step_verifier.ml:88-97`; #1 below): `emsRows = 8` chained `EndoMulScalar` rows, the `(n,a,b)`
    accumulators
    hopping row→row through σ (row `k`'s `n₈`/`a₈`/`b₈` at cols 1/4/5 IS row `k+1`'s `n₀`/`a₀`/`b₀`
    at cols 0/2/3), `n₀=0, a₀=2, b₀=2` PINNED by `Generic` rows, and a `Generic` decomposition row
    tying the chain's reconstructed `n₈` back to the SPONGE OUTPUT variable. `EndoMulScalar` had
    never been chained and had never been wired to another gate type.
  * **R3 `msm`** — TWO MSMs. `multiscale_known`, the x_hat MSM: `var_base_mul` scalar
    multiplications
    of `msmChunksAt i` 5-bit chunks — PER STATEMENT WORD since §20 (`bits_per_chunk = 5`,
    `plonk_curve_ops.ml:64-68`) — summed by a `complete_add` chain over
    **`multiscale_known`'s NON-CONSTANT PARTITION** (§21): the nine one-bit statement words are
    `Spec.T.Constant` / `Field.zero` and fold OUT of circuit (`step_verifier.ml:133-152`), so the
    region is **31 ladders, 31 seeds, 31 base pins and 30 adds** and not 40/40/40/39.
    ⚑⚑ …and since §21 each term's scalar counter chain CLOSES ON ITS **WRAP STATEMENT WORD**, not on
    a round-robin transcript challenge: term `i`'s final `n'` cell (col 5) IS `stmtVar i` — for word
    0 that is `vCipShift`, for word 12 segment C's squeeze, for word 13+k the k-th bulletproof
    prechallenge R8's `b_correct` folds. `StepShape.msmChal` is DELETED. Bending statement word `i`
    now MOVES `x_hat`, and bending a transcript challenge no word carries (`c`, ξ, r) moves nothing;
    both directions are `…Pins16`.
    ⚑ …and since 2026-08-02 the ladder STARTS where upstream starts it: `add_fast base base` as a
    `CompleteAdd` row per term and `n_acc = Field.zero` as a `Generic` pin
    (`plonk_curve_ops.ml:157-158`). Both were free witnesses; §12f exhibits what that bought a
    prover.
    ⚑ …and since 2026-08-02 **`Common.ft_comm`** (§6b, `common.ml:238-256`): eight `scale_fast2`s at
    `~num_bits:255` — 51 chunks each, `step_verifier.ml:240-242,587-591` — over `sigma_comm_last` and
    `t_comm`'s seven quotient chunks, folded by `common.ml`'s own `Ops.add_fast` chain, with
    `Shifted_value.Type2`'s split emitted as a row against R6's derived `perm` / `ζ^n` cells. Its
    OUTPUT is R4 round 2's base. **This is what makes `t_comm`'s absorption mean something:** its 14
    transcript words are the MSM's operands, not fixtures the sponge eats.
  * **R4 `ipa`** — `combine_split_commitments` + `bullet_reduce`: `ipaRounds` `Scalar_challenge.endo`
    scalar multiplications of `ipaBlocks` 4-bit blocks each (the row-OVERLAP chaining pattern, no σ
    hop), each closing on its own challenge, folded by a second `complete_add` chain. ⚑ …and since
    2026-08-02 each round STARTS at `Scalar_challenge.endo`'s own seed — `acc = p + p` with
    `p = t + (Endo.base·xt, yt)`, `n_acc = Field.zero` (`scalar_challenge.ml:230-235`) — a `Generic`
    scale and two `Ops.add_fast`s. It was `dblA T` with both cells free: the wrong point AND a
    prover-chosen one (§12g). ⚑ Its bases
    are the PREVIOUS PROOF's — `combine_commitments`' own 47 commitments and `bullet_reduce`'s 30
    `(L,R)` — and the 48 of them upstream absorbs are wired so that their coordinate variables ARE
    the transcript's absorbed words (§3b, #3). ⚑ Each of those 48 also carries `Inner_curve.typ`'s
    own `check`, `assert_on_curve` (§7b, `snarky_curve.ml:212-229`): a curve gate constrains the
    ADDITION and not membership, so a supplied point needs the Typ's check or it needs nothing.
    ⚑ …and since 2026-08-02 the fold chain STARTS WHERE `combine_split_commitments` starts it:
    `~init` at commitment 0 (`step_verifier.ml:606`), i.e. **`sg_old[0]`**, whose two coordinates are
    transcript block `oSgOld0`'s absorbed words. `ipaRounds` adds, not `ipaRounds − 1`.
    ⚑ …and R4 now carries **`check_bulletproof`'s TAIL** (`:321-327`): `absorb sponge PC delta`, the
    LAST squeeze `c`, and `lhs = Scalar_challenge.endo q c + delta` — one more 32-block `EndoMul`
    ladder over the fold output plus one `Ops.add_fast`. That is what makes `delta` and `c` words
    something READS. ⚠ `equal_g lhs rhs` (`:340`) is NOT here: `rhs` is the IPA opening, i.e.
    `verified` (#11), still a witnessed boolean.
    ⚠ ⚑ …and since 2026-08-02 **§17 MEASURES what assembling it would and would not buy**, because
    the answer inverts the reason it was next: `G = challenge_polynomial_commitment`, `z_1` and `z_2`
    are FREE WITNESSES, so `equal_g` is satisfiable for every `lhs` and **refuses no on-curve
    substitution of a consumed commitment.** The exhibit is honest-CLOSES / substituted-with-same-`G`
    REFUSED / substituted-with-re-solved-`G` ACCEPTED, on this assembly's own values, with
    `Generators.h` and the Bw19 `group_map` parameters measured off the Rust side.
    ⚠ ⚑ …and `G`'s binder — `step_main.ml:525-566`, one rung above `verify_one` — **IS NOW
    ASSEMBLED (segment D, §8e′), AND THE SUBSTITUTION IS STILL ACCEPTED.** `G` went from ZERO
    occurrences to an `assert_on_curve` and an absorption whose squeeze is public word 7, so a
    re-solved `G` now MOVES a public word (§17(d)) — but `bpCloses` on the re-solved witness is
    still `true` (§17(e)), because `rhs`/`equal_g` are still not emitted and **no row here relates
    `G` to the opening.** Segment D binds `G` to the STATEMENT.
    ⚠ ⚑ …and since 2026-08-02 **THE INTER-STEP TIE ITSELF IS ASSEMBLED AS A CHAIN AND MEASURED
    (§18), AND IT DOES NOT REFUSE THE SUBSTITUTION EITHER — IT PROPAGATES IT.** The previous
    sentence here read "the refusal is a consumer's, one recursion step later, through segment C's
    reconstruction and the wrap-proof tie (`step_main.ml:83-86,108`)"; §18 builds exactly that
    consumer and the substituted chain CLOSES. What the tie buys is that `sg_old` at step `N+1` is
    FORCED to be the `G` used at step `N` — the fake commitment cannot be laundered away between
    steps — and that direction IS a refusal (§18(d)). The refusal of the substitution itself is one
    link further still: the accumulator check `per_proof_witness.ml:12-32` states, whose two legs
    are `E_c = f_c(ζ)` over `prev_challenges` (simplification #4's residue, measurably ABSENT here,
    §18(f)) and `sg_old` OPENING to `E_c` — which is `verified` (#11), an ASSUMPTION at every step
    of the chain. And with `G` fixed the `z₁`/`z₂` residue is a two-dimensional discrete log, an
    ASSUMPTION and not a gate.
  * **R5 `deferred` + `xi` + `cip` + `closing`** — two of `finalize_other_proof`'s deferred words:
    `b(ζ) = ∏(1 + uᵢ·ζ^{2^{k−1−i}})` (`Wrap.challenge_polynomial`, `wrap.ml:15-17`; the product
    `KimchiVerify.bEvalSq` folds) and `combined_inner_product = Σ_k ξ^k·(evₖ(ζ) + r·evₖ(ζω))`
    (`Common.combined_evaluation`, the `2 × cipEvals` `mul_and_add`s; pinned against
    `KimchiVerify.combinedInnerProduct`, transcribed READ-ONLY from `verifier.rs`, **over the slots
    `combine` KEEPS**) — both as `Generic` chains over the CHALLENGE variables. ⚑ Its ξ is §8g's
    chain 0: a full `to_field_checked` of the STATEMENT's ξ word (`let xi = scalar xi`,
    `step_verifier.ml:1012`), the word R8's `xi_correct` ties to the fr-sponge. ⚑ It also unpacks
    §8h's `branch_data` — the two `proofs_verified_mask` bits R7's opt-sponge muxes with — and, since
    2026-08-02, **CONSUMES them in the fold itself**: `combine`'s two `Opt.Maybe` prefix entries run
    `Field.if_ keepⱼ` (`common.ml:270-271`), so a dropped slot takes no ξ power and
    `combined_inner_product` is the fold over the KEPT sub-list (§12l). Then the closing tie of every one of the
    `pubWords` public words to a computed circuit variable. This rung turns the public input on:
    `placeChecked` (not `place`) with `Contract ⟨pubWords, AUX⟩`, so a public word no gate reads
    REFUSES rather than sitting inert, and the circuit's own ids cannot be silently absorbed into
    the public input.
  * **R6 `ft_eval0`** — `scalars_env` + the linearization CONSTANT TERM + `ft_eval0` +
    `Plonk_checks.checked`'s `perm` scalar (`step_verifier.ml:1019-1071,1131-1136`,
    `plonk_checks.ml:254-548`), compiled by §8b onto double-`Generic` rows and pinned value-for-value
    against `KimchiVerify.gateLinConst` / `ftEval0R` / the 67 constraint bodies list-by-list (§13),
    each with a red control. Its `ft_eval0` output IS the `ft` column R5's `combined_inner_product`
    folds — upstream's own `combine ~ft:ft_eval0`.
  * **R7 `absorption`** — the fr-sponge (`step_verifier.ml:950-1013`, `step_main.ml:525-567`): an
    OPT-SPONGE over the carried bulletproof challenges muxed by §8h's DERIVED
    `branch_data.proofs_verified_mask` bits (the `Field.if_` state mux, `:998-1003`), the
    **43 evaluation columns absorbed at ζ and ζω** in
    `to_absorption_sequence` order, the ξ′/r′ squeezes, `hash_messages_for_next_step_proof` — whose
    `Not_opt` prefix IS ⚑ §3c's `sponge_after_index`, the wrap verifier key's 28 commitments as 56
    absorbed words, 27 of them THE FOLD'S OWN base variables, with `index_digest` squeezed off that
    state and absorbed as R1's first word — and
    ⚑ …and since 2026-08-02 R7 carries **BOTH** hashes, because there are two and they hash
    different things (`step_main.ml:59-81` and `:525-566`). **Segment C, the INNER `…_opt` call**,
    had its two commitment slots wired to R3's x_hat sum and R4's fold output `q`; upstream's are
    `prev_challenge_polynomial_commitments` — `sg_old`, which this assembly already held as the
    fold's `~init` and its round-0 base — and the two vectors are INTERLEAVED PER PROOF
    (`composition_types.ml:595-607`), not concatenated. Both were wrong; §12k exhibits the
    correction in both directions on the emitted digest. **Segment D, the OUTER call**, is new: its OWN
    `sponge_after_index` over **the instance's own wrap verification key** (`step.rs:2718`), then
    the app state, `G` (`acc.wrap_proof.opening.challenge_polynomial_commitment`, `:534`) and
    `finalize_other_proof`'s RETURNED `bulletproof_challenges` (`:563-565` — a different vector from
    segment C's `prev_challenges`), unmasked, its squeeze the step statement's public
    `messages_for_next_step_proof` (`:572-575`). ⚠ See R4 for what that does and does not buy — and
    ⚑ §8g's chain 1 — `to_field_checked` of the SECOND squeeze, which IS the `r` the C8 fold and
    `b_correct` multiply by (`let r = scalar (Scalar_challenge.create r_actual)`, `:1013`).
  * **R8 `finalize`** — ⚑ `finalize_other_proof`'s TAIL, the rung at which the deferred values stop
    being computed and start BINDING (`step_verifier.ml:1076-1147`, `step_main.ml:121,522`): the
    second challenge polynomial at `ζω = domain#generator·ζ` so `b_actual = challenge_poly ζ +
    r·challenge_poly ζω`; the **three `Shifted_value.Type1.to_field` unshifts** of the statement's
    `combined_inner_product`, `b` and `plonk.perm` (Type1 over **`Fp`** — the value's own field, see
    §8f); `xi_correct` against the fr-sponge's own squeeze; and `Boolean.all [xi_correct; b_correct;
    combined_inner_product_correct; plonk_checks_passed]` behind the `should_verify` mux, ASSERTED.
    The four statement words are the **first four public words**, so a prover who claims a different
    deferred value is refused rather than believed. ⚑ And `should_verify` is the FIFTH: it is a
    STATEMENT bool upstream (`step_main.ml:36-37` asserts it equal to `unfinalized.should_finalize`,
    which is in the Per_proof statement's `bool` list, `composition_types.ml:1219,1310`), and while
    this file made it a witness a prover set it to 0 and the whole assert passed with all four legs
    false (§16g).

## ⚑ THE SHAPE ORACLE — MEASURED against Mina's own compiled step circuit

o1-labs publishes Mina's compiled circuits as `*_gates.json` release blobs (kimchi's
`Circuit { public_input_size, gates }` serde form; `bridge/mina-zkapp/scripts/
mina-canonical-circuit-oracle.mjs`, whose digest reproduces the md5 in o1-labs' own asset filename).
**`step-zkapp-proved` is branch 4 — the step branch that RUNS `verify_one` on a side-loaded proof**:
PI 67, 20,023 gates, 13,778 non-Generic. Measured against this file's `shapeStep` **2026-08-03, off
a STAMPED emission the conformance gate produced itself** (`--emit`):

    gate         Mina step-zkapp-proved  r5_full  r6_ft_eval0  r7_absorb  r8_finalize  r9_opening
    total gates         20023              8281      8750       10585       10677      11159
    non-Generic         13778              7445      7447        8977        9000       9429
    Poseidon             6292 (31.4%)       902       902        2277        2277       2277  11×572 / 11×207 ✓
    Generic              6245 (31.2%)       836      1303        1608        1677       1730  —
    EndoMul              2465 (12.3%)      2464      2464        2464        2464       2464  32×77+1×1 / 32×77 ✓
    Zero                 2246 (11.2%)      1996      1998        2137        2144       2359  —
    VarBaseMul           1596  (8.0%)      1390      1390        1390        1390       1594  1×1596 / 1×1594 ✓
    EndoMulScalar         776  (3.9%)       376       376         392         408        408  8×28 / 8×51 ✓
                    upstream also runs 2×42 4×25 16×3 1×2 12×2 32×2 9×1 19×1 22×1 24×1 28×1 128×1
    CompleteAdd           403  (2.0%)       317       317         317         317        327  1×159 2×65 3×23
                    15×1 30×1 / 1×327

⚠ ⚑ **THIS TABLE IS §22's AND §23 MOVED EVERY COLUMN — DO NOT CITE IT FOR `shapeStep` UNTIL IT IS
RE-MEASURED OFF A STAMPED §23 EMISSION.** The lazy sponge removes 22 transcript permutations, five
segment squeeze-blocks and §3c's whole digest block, so `Poseidon` goes `11×207 → 11×179` and every
rung's total drops. The SMOKE shape is measured and green: r1 **151** (was 237), r5 **1581**,
r6 **2050**, r7 **3323**, r8 **3391**, r9 **3873** (was 4037) — `−164` rows, all five polarities in
RELEASE. The `step` column is being re-emitted; the number this file must not carry is a stale one,
so it says so rather than showing one.

⚠ **THE PREVIOUS TABLE WAS STALE AND SAID SO NOWHERE.** It read `r8_finalize 10826` with
`VarBaseMul 1448` — and `1448 = 1040 + 408` is the count at the UNIFORM `msmChunks = 26` that §20
DELETED in the very commit this table sat in. The rows column therefore spanned TWO rungs' movement,
not one, and the `r9_opening` column §19 added had never been carried at all. Re-measured in full
rather than patched. **Never grade a rung off a table you did not just produce, either.**

⚑⚑ MOVEMENT IN THIS COMMIT (§23, `…Pins18`): **OUR SPONGE WAS EAGER WHERE MINA'S IS LAZY, AND
FIXING IT MOVED EVERY SEGMENT AND THE TRANSCRIPT.** §22 read the divergence and named it as its own
rung; this is that rung.

`snarky/sponge/sponge.ml:280-326` at `rate = m − capacity = 2`: **the permutation is triggered by an
ARRIVING element, never on the way out.** A `squeeze` from `Absorbed _` SUPPLIES the pending block's
permutation; a SECOND consecutive squeeze is free (`Squeezed 1`, `n ≠ rate`, `state.(1)`) and only a
THIRD permutes again; an `absorb` from `Squeezed _` lands in lane 0 without permuting, so the rate
counter restarts at every squeeze and the item stream RE-PAIRS. This file did all three the other
way: one permutation per absorb block PLUS one per squeeze, and a per-SOURCE pairing that padded
`index_digest` to two lanes.

  * ⚑ **THE COUNT, EXHIBITED ON THE EMITTED OBJECT.** At upstream's own 21 squeezes the transcript
    now performs `⌈117/2⌉ = 59` permutations — exactly `absorbBlocksNeeded`, which has named that
    number since 2026-08-02 without the emission agreeing with it. At this file's 23 (ξ and r are
    still allocated off the transcript, §2b) it is **60**, the extra one being `r`'s: it is the third
    consecutive squeeze and `Squeezed 2 = rate` permutes. **The pre-fix model was `absorbs + chals`
    = 82 / 80** — a difference of **22 / 21** permutations, and that IS the red control.
  * ⚑ **β AND γ ARE NOW TWO LANES OF ONE PERMUTATION** (`step_verifier.ml:563-564`), and so are the
    fr-sponge's ξ′ and r′ (`:1007-1009`, `squeeze_challenge = lowest_128_bits (Sponge.squeeze …)` at
    `:186-187`). They were two permutations apart. **Every segment permutes `⌈|ws|/2⌉` times**, one
    squeeze or two.
  * ⚑ **`index_digest` COSTS NO PERMUTATION OF ITS OWN.** `sponge_after_index` absorbs 56 — EVEN —
    field elements, so `Sponge.squeeze_field (Sponge.copy …)` (`:531-532`) performs the 28th and
    reads `state.(0)`. This file performed a 29th. **The reality gate is `PastaPoseidon.Ref.hash`,
    whose nine o1js golds include both EVEN-length vectors** — precisely the case an eager sponge
    gets wrong, and precisely the bug `Ref.absorbFrom`'s own header records being fixed in the
    reference on 2026-07-27 and never carried up to `verify_one`. `index_digest = Ref.hash …` is now
    a named theorem and the pre-fix value is exhibited as a REFUTATION.
  * ⚑⚑ **AND THE LAST FREE TRANSCRIPT WORD IS GONE — not by a new wire but by the re-model.** The
    per-source pairing made block 0's second lane carry a `msgVal` FIXTURE, a word `verify_one` never
    feeds. Under the item stream `index_digest` shares block 0 with `sg_old[0]`'s x, the single lane
    an odd item count leaves without an arrival lands at the END of the pre-β run, and it is PINNED
    TO ZERO (`tPadCell`, one `Generic` row) — which is `absorb`'s own "no arrival", since it ADDS.
    `vMsg` and `msgVal` are DELETED. **Of `N_ABSORB_ITEMS = 117` items, ZERO are free witnesses.**

⚑ §23 ALSO CLOSES THE WORD-39 QUESTION, AT SOURCE, AND THE ANSWER IS "FAITHFUL AS IT STANDS".
Word 39 is `lookup.joint_combiner.inner`, the `Opt`'s `Struct [Scalar Challenge]`
(`composition_types.ml:655-665`), and the arm the `proved` rule compiles is **`Maybe`** — its only
predecessor is the side-loaded tag, whose eight feature flags are all `Opt.Flag.Maybe`
(`transaction_snark.ml:609-620,2111-2112`), so `use = lookup_tables_used` is `Maybe`
(`step_main.ml:88-92`) and the value is a witness rather than `Cvar.Constant`. It is a **REQUESTED
WITNESS of the whole step circuit** (`prevs = exists … ~request:Req.Proof_with_datas`,
`step_main.ml:353-355`), and the only place a `joint_combiner` could be derived is dead:
`lookup_verification_enabled = false` (`step_verifier.ml:12`) makes it
`if … then failwith "TODO" else None` (`:631-633`), after which `assert_eq_deferred_values` gets
`None` on both sides and asserts β, γ, α, ζ only (`:634-648`, `:342-363`). **Prover-chosen here and
prover-chosen upstream — exactly word 11's verdict. Nothing to land.**

⚠ **AND TWO CORRECTIONS TO §21/§22's READING OF THE SAME CENSUS.** `2×1 26×22 51×8` is
**chunks × count** — ONE 2-chunk ladder (`branch_data`), not two 1-chunk ones; and ⚑ **the nine
one-bit words are NOT dropped constants.** §1b gives `multiscale_known`'s constant partition as the
reason they emit no ladder; at the all-`Maybe` tag `maybe_constant` yields `Spec.T.B Bool`
(`composition_types.ml:794-802`) and the `Opt` header packs `p.pack Bool b`, so `constant_part` is
**EMPTY**. The nine are live **ZERO-CHUNK** ladders — `chunks_needed ~num_bits:0 = 0`, no scale
chunks but two `add_fast`es, an `EC_scale` with an empty round array and the `2·s_div_2 + s_odd = s`
tie (`plonk_curve_ops.ml:202-208,291`). **Mina emits 40 ladders where this assembly emits 31.** The
chunk census is unchanged; the residue is real and its stated mechanism was wrong.

⚑⚑ MOVEMENT IN THE PREVIOUS COMMIT (§22, `…Pins17`): **the fr-sponge got its SEED, and Wrap statement word
10 stopped being prover-chosen — +14 rows in R7.** `step_main.ml:41-46` hands
`finalize_other_proof` a sponge that has already absorbed
`proof_state.sponge_digest_before_evaluations`; segment B started at `challenge_digest` and now
starts at that word, 91 absorbed field elements over 46 rate-2 blocks with a pinned pad lane.

And the word is a cell R1 already computes. Mina's sponge is LAZY at rate 2
(`snarky/sponge/sponge.ml:294,314-325`): ζ's `Sponge.squeeze` at `step_verifier.ml:568` permutes and
returns `state.(0)`, and the `squeeze_field` at `:574` finds `Squeezed 1`, does NOT permute, and
returns `state.(1)`. So `sponge_digest_before_evaluations` is lane 1 of the state ζ is lane 0 of —
already emitted, already probed. `stmtVar 10` is that cell (`digestBeforeEvalsVar`); `vStmtDigest` is
DELETED and `N_STMT` is 22.

  * ⚑ **BOTH DIRECTIONS, and the retired wiring is the middle leg** (`…Pins17`): bending word 10
    moves both fr-sponge squeezes, §8g's lifted ξ and r, the committed shape's scalar vector **at
    index 10 alone**, and R8's `out` slot from 1 to **0**; under the retired SEEDLESS segment B the
    same bend moves NOTHING, and the two wirings disagree in the first place. Bending the last
    `t_comm` chunk (absorbed before ζ) MOVES the word; bending `combined_inner_product` (absorbed
    after ζ) does not — which is what "the state ζ's permutation left" means.
  * ⚑ **NOT ONE RUN-LENGTH FAMILY MOVED**: `EndoMul 32×77` (exactly Mina's), `EndoMulScalar 8×51`,
    `VarBaseMul 1×1594`, `CompleteAdd 1×327`; `Poseidon 11×206 → 11×207`, which is the new block and
    is the subset closing toward Mina's 572. x_hat is still 31 ladders `2×1 26×22 51×8` = 982 chunks
    on BOTH sides. Conformance re-graded **31/31 byte-exact**.
  * ⚑ The smoke shape moves too — 4,023 → **4,037** rows — because the fr-sponge is in R7 and R7 is
    in the smoke rungs. All nine rungs re-prove in RELEASE with all five polarities.
  * ⚠ **AND IT CHANGES NO VERDICT.** `substituted_assembly_still_closes_equal_g : tSwapAbs.bp.ver
    = 1` — **ACCEPTED**, before and after, as at §19/§20/§21. Word 10 feeds the fr-sponge, hence ξ
    and r, hence what an HONEST prover must claim; it relates nothing to `sg_old`'s opening, which is
    the accumulator check's second leg (`per_proof_witness.ml:12-32`).
  * ⚠ **THE RESIDUE IS TWO WORDS, AND ONE OF THEM IS UPSTREAM'S TOO.** Word 11 is
    `exists … ~request:Req.Messages_for_next_wrap_proof` at `step_main.ml:364-366` — a witness of the
    whole step circuit, derived nowhere upstream either. Word 39 needs the lookup sub-circuit; a
    source reading that would have made it a CONSTANT was refuted by Mina's own compiled ladder
    census. See `…Pins17`.
  * ⚠ **AND §22 READ A SPONGE-MODEL DIVERGENCE IT DID NOT FIX** — one extra permutation per squeeze
    and ξ′/r′ two permutations apart. **CLOSED by §23, above.**

⚑⚑ MOVEMENT IN THE PREVIOUS COMMIT (§21, `…Pins16`): **the x_hat MSM's scalars became the Wrap STATEMENT's
words, and `multiscale_known`'s CONSTANT PARTITION left the circuit — −45 rows in R3.** Exactly
9 `Generic` (the constant words' base pins), 18 `CompleteAdd` (9 seeds + 9 fold adds) and 18 `Zero`
(their probes): `msmRows shapeStep` goes 2178 → 2133 with `VarBaseMul` UNCHANGED at 982, because the
nine emitted no ladder row to begin with. The fold chain is now **30 adds over 31 terms**, which is
Mina's own single run of thirty consecutive `CompleteAdd` rows.

  * ⚑ **NOT ONE RUN-LENGTH FAMILY MOVED**, re-measured off the stamped emission: `EndoMul 32×77`
    (exactly Mina's), `Poseidon 11×206`, `EndoMulScalar 8×51`, `VarBaseMul 1×1594`,
    `CompleteAdd 1×327`.
  * ⚑ **THE SMOKE SHAPE IS UNTOUCHED at 4,023 rows** — its three terms are words 0–2, all `Field`,
    so it has no constant partition at all. The committed harness fixtures move only in their WITNESS
    values, and all nine rungs re-prove in RELEASE with all five polarities.
  * ⚠ **AND IT CHANGES NO VERDICT.** §17(e) and §18(b) re-run unchanged — the
    substituted-with-re-solved-`G` witness is ACCEPTED before and ACCEPTED after. `x_hat` is a public
    word and a segment-C absorption; making its scalars the statement's words moves what an HONEST
    prover must claim. It relates nothing to `sg_old`'s opening, which is `verified` (#11).

⚑⚑ MOVEMENT IN THE COMMIT BEFORE (§20, the per-word MSM widths, 1040 → 982 chunks): see
simplification #2. Its own table update never happened — that is the staleness named above.

⚑⚑ MOVEMENT BEFORE THAT (10822 → 10826 rows, +4): **`combine`'s `Opt.Maybe` MUX —
`branch_data.proofs_verified_mask`'s LAST ignoring consumer, closed — AND IT MOVES PUBLIC WORD 9 AT
THE DEPLOYED MASK, which is the opposite of what the residue predicted.**

`verify_one`'s own file has EXACTLY three consumers of the mask: `step_verifier.ml:944` (`sg_evals`,
which feeds `combine`), `:954` (the opt-sponge, §8e) and `:1182-1186` (the inner hash, segment C).
The first was the one still ignored — `cipRows` folded all 47 prefix entries unconditionally. It now
runs `Field.if_ keepⱼ` off §8h's DERIVED bits. (`wrap_verifier.ml:513` / `wrap_main.ml:173-195` are
the WRAP circuit, a different object and out of scope by construction.)

**READ AT SOURCE, quoted with line numbers, verified in the tree — not relayed:**

  * `common.ml:263-272`, the `Maybe` arm at `:270-271`:
    `| Maybe (b, fx) -> Field.if_ b ~then_:(fx + (xi * acc)) ~else_:acc`
  * `pickles_types/pcs_batch.ml:85-94` — `combine_split_evaluations` flattens the arrays, **REVERSES**,
    seeds `init` with the LAST element and folds the rest, so the list is Horner'd **from its tail**.
  * `step_verifier.ml:916` — `actual_width_mask = branch_data.proofs_verified_mask`; `:940-948`
    `sg_evals pt = Vector.map2 mask sg_olds`; `:1080-1095` those become `[| Opt.Maybe (keep, eval) |]`
    PREPENDED to `[x_hat] :: [ft] :: a`, i.e. prefix entries 0 and 1.
  * `pickles_base/proofs_verified.ml:75-81` — `there`: `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`.
    A set bit is a SUFFIX; the deployed `N1` instance DROPS SLOT 0.
  * `wrap_hack.ml:26-28` — `pad_vector` is `Vector.extend_front_exn`, so slot 0 IS the dummy.

⚠ ⚑ **THE FINDING INVERTS THE EXPECTATION THE RESIDUE CARRIED.** "Slot 0 is the `Wrap_hack` dummy,
so at the deployed mask dropping it is a no-op on the value" is **FALSE**. `mul_and_add`'s `else_`
branch is bare `acc` — it does **not** multiply by ξ — and the fold runs from the list's tail, so
slot 0 is the LAST step. Dropping it removes `c₀` AND takes one ξ power off every one of the other
46 terms. The dummy's VALUE is what the mask makes irrelevant; the ξ-power shift is what it does
not. §12l measures it: the three legal masks give THREE DIFFERENT field elements, and the emitted
`combined_inner_product` is `cipR` over the **kept sub-list**, not `cipR` over 47 with entry 0
zeroed — a third, different value again.

  * ⚑ **+3 `Generic` rows and +1 `Zero`.** The two `Maybe` steps become five halves each where they
    were two (`then_`, the `Field.if_` difference, the mask product, the add), `packHalves`-packed so
    the 45 `Some` steps keep their exact row pairing; plus the mux's own σ probe. NOT ONE run-length
    family moved: `EndoMul 32×77` is exactly Mina's, `Poseidon 11×206`, `VarBaseMul 1×1448`,
    `EndoMulScalar 8×51`, `CompleteAdd 1×334` — re-measured after this rung.
  * ⚑ **THE ROWS DO NOT DEPEND ON THE MASK'S VALUE, and that is the point.** `keepⱼ` is `vMask j`, a
    circuit VARIABLE §8h booleanity-checks and `Checked.pack` ties to the `branch_data` statement
    word, so all three legal masks emit the SAME gate list and differ only in the witness. The mask
    bit's σ class grew by exactly ONE cell — `combine`'s — which §14a pins as `5 + 3·maskReaders + 1`.
  * ⚑ **RED CONTROLS THAT BITE, in both directions** (§12l). At `[1,1]` — where slot 0 is a live
    previous proof and not the dummy — dropping vs folding it gives a DIFFERENT `combined_inner_
    product`; at the deployed `[0,1]` it is different too, and it is different from the zero-the-entry
    reading. Bending slot 0's carried challenges moves `E_c` and LEAVES `cip` at `[0,1]` and MOVES it
    at `[1,1]`; bending slot 1's moves it at both.
  * ⚠ ⚑ **AND IT CHANGES NO VERDICT. §17(e) AND §18(b) ARE RE-RUN AND ARE UNCHANGED — the
    substituted-with-re-solved-`G` witness is ACCEPTED before and ACCEPTED after.** `combined_inner_
    product` is a value R8 ties to a statement word; moving it moves what an HONEST prover must
    claim. It relates nothing to `sg_old`'s opening, which is `verified` (#11), a witnessed boolean
    and not a rung.

⚑ MOVEMENT IN THE COMMIT BEFORE (10746 → 10822 rows, +76): **the ACCUMULATOR CHECK's FIRST
LEG. `E_c = f_c(ζ)` over `prev_challenges` is COMPUTED, where it was four free `evVal` witnesses —
and the substitution §17(e)/§18(b) exhibits is still ACCEPTED, which is said here and not at the
bottom.**

`per_proof_witness.ml:12-32` states the accumulator check in prose and it is TWO legs:
`challenge_polynomial_commitment` must **open** at ζ to `E_c`, AND `E_c = f_c(ζ)` over
`prev_challenges`. §8i is the second of those, read at source from `step_verifier.ml:934-948`
(`zetaw`, `sg_olds = Vector.map prev_challenges ~f:challenge_polynomial`, `sg_evals pt` at ζ and
ζω) feeding `combine`'s own prefix at `:1076-1102`, with `challenge_polynomial` itself at
`wrap_verifier.ml:16-35`.

  * ⚑ **+77 `Generic`/`Zero` rows in R5, −1 in R8.** One half pins `domain#generator`; one gives the
    SINGLE `zetaw` cell (`:934`) that `sg_evals` and `b_correct` share — R8 stopped recomputing
    `ω·ζ`, which is where its row went; then ζω's 15 squaring halves and FOUR 16-factor product
    ladders whose outputs ARE `vEz 0/1` and `vEw 0/1`.
  * ⚑ **`prev_challenges` REACH A PUBLIC WORD for the first time.** §18(f): a carried challenge had
    ZERO cells at `r5_full` (its only consumers were segments A and C, both R7); it now has exactly
    two, and through `combine` it reaches `combined_inner_product` — public word 9, and the
    statement word R8's `combined_inner_product_correct` binds. Bending one moves `E_c` at both
    points of its slot and moves `cip` with it; the OTHER slot does not move.
  * ⚑ **THE VACUOUS CLOSURE IS PINNED SHUT.** `f_c` over `prev_challenges` is NOT `f_c` over this
    proof's own returned bulletproof challenges — `step_verifier.ml:918` says so in one line ("You
    use the NEW bulletproof challenges to check b. Not the old ones."). §18(f) pins the value
    inequality, pins the emitted `E_c` against `KimchiVerify.bEvalSq` at the carried vector, and
    pins the ROW-LEVEL read-set disjointness both ways: §8i's rows touch no `vLift (uChal k)`,
    `deferredRows`' touch no `vPrevChal`.
  * ⚠ ⚑ **AND IT DOES NOT REFUSE THE SUBSTITUTION. §18(b) IS RE-RUN AND IS UNCHANGED.** `E_c` is a
    function of `prev_challenges` and ζ; `sg_old` does not occur in it. The prover who substitutes an
    absorbed commitment and re-solves `G` carries the SAME `prev_challenges`, so all four computed
    entries land where they would have. **ACCEPTED before, ACCEPTED after.** What this leg removes is
    a DIFFERENT forgery surface — four values the prover used to choose freely — not this one. The
    thing still standing between a substituted commitment and acceptance is leg TWO, the opening,
    which is `verified` (#11), a witnessed boolean, and NOT a rung.

⚑ MOVEMENT IN THE COMMIT BEFORE (ZERO ROWS, 10,746 unchanged) — the inter-step tie, assembled and
MEASURED in §18. Segment C at step `N+1`, fed step `N`'s app state, `G` and returned bulletproof
challenges, reproduces step `N`'s public word 7 EXACTLY (§18(a)) — and the SUBSTITUTED chain
reproduces the MOVED word just as exactly (§18(b)). The tie is not a refusal of the substitution; it
is a FORCING of `sg_old`. Its three source corrections stand: the tie has **no `Field.Assert.equal`
in it** (the reconstructed digest is SUBSTITUTED into the wrap statement at `step_main.ml:83-84` and
its only in-circuit wire is x_hat MSM term 12's SCALAR, simplification #2's residue); the two hashes
are ONE chain; and the leg that would refuse it is the accumulator check — which is what §8i above
half-closes.

⚑ MOVEMENT TWO COMMITS BACK (10601 → 10746 rows, +145) — **and the headline was a
CORRECTION, not the rows: segment C hashed two quantities upstream does not put in that hash, and
did not hash the two it does.** Those rows are the OTHER hash, and they do NOT buy the refusal the
rung was queued for; see R4, §17 and §18.

  * ⚑⚑ **SEGMENT C's COMMITMENT SLOTS CORRECTED: zero rows.** `hash_messages_for_next_step_proof_opt`
    absorbs `challenge_polynomial_commitments = prev_challenge_polynomial_commitments`
    (`step_main.ml:78-79`) — `sg_old`. The slots held R3's x_hat MSM output and R4's fold output `q`,
    both computed INSIDE this `verify_one` and both already public words of their own. Both `sg_old`
    slots were already variables here (`qInit` and fold round 0's base), so the swap cost nothing;
    the word ORDER changed too, because `to_field_elements_without_index`
    (`composition_types.ml:595-607`) INTERLEAVES each commitment with its own challenge run. §12k
    exhibits both directions on the emitted digest — and names the third fact, that with
    `Prefix_mask.there N1` slot 0 is the `Wrap_hack` dummy and is masked out, so only slot 1 bites.
  * ⚑⚑ **SEGMENT D, the OUTER `hash_messages_for_next_step_proof`, and `assert_on_curve` on `G`.**
    `step_main.ml:525-566` — its OWN `sponge_after_index` over the instance's own wrap verification
    key (`step.rs:2718`, 56 coordinates), then the app state, `G` and `finalize_other_proof`'s
    returned `bulletproof_challenges`, its squeeze the step statement's public
    `messages_for_next_step_proof`.
    ⚠ **THE ROW LEDGER HERE WAS `+121 Poseidon, +11 Generic, +13 Zero (144 rows)` AND IS STALE:**
    that was the cost of a segment D with NO index prefix. Absorbing its own 56 words takes the
    whole assembly 10 349 → 10 715 rows (+366) at `shapeStep`. `KimchiStepMainPins14`'s
    `the_schedule_wires_variables` is the measured figure; do not cite this bullet's numbers. ⚠ **It does NOT refuse the substitution §17 exhibits.** `G` went
    from zero occurrences to a public digest, so a re-solved `G` now moves a public word — but
    `equal_g` still closes and `rhs` is still not emitted. §17(d)–(g) measure exactly that.
  * ⚑ **`sg_old[0]` CLOSED: +1 `CompleteAdd`, +2 `Zero`, +2 on-curve halves** (previous commit).
    `combine_split_commitments`' `~init` (`step_verifier.ml:606`) — the fold chain starts at
    commitment 0, so `ipaRounds` adds instead of `ipaRounds − 1`.
  * ⚑ **`combined_inner_product` CLOSED: +1 `Generic`, +1 `Zero`.** One `Boolean.typ` check for the
    bit; the FIELD half is `vCipShift`, which R8 already binds. The absorption itself costs no block
    — block `oCip` was one of the three that carried a `msgVal` fixture.
  * ⚑ **`delta` CLOSED: +32 `EndoMul`, +3 `CompleteAdd`, +1 `Generic`, +8 `Zero`.**
    `check_bulletproof`'s `lhs = Scalar_challenge.endo q c + delta` (`:325-327`) — one 32-block endo
    ladder over the fold output at the LAST squeeze, seeded like every other, plus the closing add.

⚑ **AND THE 77th ENDO BLOCK IS UPSTREAM'S OWN, AND THIS COMMIT DID NOT TOUCH IT.** `EndoMul` is
**2464 against Mina's 2465** and the run-length family is `32×77`, exactly Mina's `32×77 1×1` — the
same as before this rung, re-measured by `stepmain-shape-diff.mjs` after it. `Poseidon` `11×206`,
`VarBaseMul` `1×1448`, `EndoMulScalar` `8×51` and `CompleteAdd` `1×334` are unchanged to the row:
**§8i is `Generic`/`Zero` only, so NOT ONE run-length family moved.** (The commit before this moved
none either; the one before that took 10601 → 10746 on segments C/D; before that 10554 → 10601 on
the R1 interleaving and the three closures; the two before that 10342 → 10554 on the three ladder
seeds and the absorb-shape correction; before that 9431 → 10342 on §6b's `ft_comm` MSM; before that
9417 → 9431 on §3c's `sponge_after_index`; before that 9317 → 9417 on #1's third `lowest_128_bits`
and §7b's `assert_on_curve`.)

The RUN LENGTHS are the fidelity signal, and all FIVE families the shape-diff compares are INTACT
(⚠ the prior header said "six"; `stepmain-shape-diff.mjs` prints run lengths for `Poseidon`,
`EndoMul`, `EndoMulScalar`, `VarBaseMul`, `CompleteAdd` and no others): a `Poseidon` permutation is
11 rows (206 of them, upstream 572), a 128-bit `Scalar_challenge.endo` is 32 `EndoMul` rows, a
`var_base_mul` chunk is a lone `VarBaseMul` row followed by its `Zero` — **`1×1448` after §6b, still
`1×`**, because a 255-bit `scale_fast2` chunk has the same two-row shape as a 128-bit one — and a
128-bit `to_field_checked` is 8 `EndoMulScalar` rows, **51 such chains** (23 transcript challenges +
their 23 `assert_128_bits hi`, §8g's deferred ξ and r, r's high part, and R8's own `lowest_128_bits`
on BOTH parts), against upstream's 28 8-row runs. `CompleteAdd` is `1×334` — 330 plus the fold's
`~init` add and `check_bulletproof`'s three — because every add is followed by a row of another kind
(its σ-only probe, or its ladder's first curve row). The `EndoMul` COUNT is **2464 against upstream's
2465** and `VarBaseMul` 1448 against 1596, i.e. the fold, `bullet_reduce`, `check_bulletproof`'s tail
and BOTH commitment MSMs are here at full size.
Only SEVEN gate types appear in any Mina step or wrap circuit — no lookup, no foreign-field, no
range-check — and all seven are emitted here.

⚑ MEASURED PROVE (2026-08-02, `cargo run --release … -- /tmp/pickles-stepmain step`): every rung
`verify()==true`, and every rung keeps all five polarities — honest ACCEPT · σ-only desync REJECTED
· byte-identical UNWIRED control ACCEPTED · unread advice ACCEPTED · (r5–r8) public-vector tamper
REJECTED and the σ leg REJECTED at `i=0` and `i=66`.

    rung             rows   domain   honest prove+verify   σ-only probes emitted
    r1_transcript    1069     2048             744 ms              24
    r2_challenges    1714     2048             845 ms             116
    r3_msm           4917     8192            1021 ms             221
    r4_ipa           8111     8192            1003 ms             452
    r5_full          8444    16384           10554 ms             464
    r6_ft_eval0      8913    16384            1264 ms             466
    r7_absorption   10734    16384            1252 ms             480
    r8_finalize     10826    16384            1441 ms             487

(⚠ **`r8`'s 17.1 s in the previous rung's table was a loaded box and NOT the assembly.** Measured
again here at 10,601 rows — 47 MORE than the 10,554 that produced the 17 s — it is **1.24 s**, in
line with r5–r7. The prior note said as much; this is the re-measurement that settles it. ⚠ the
numbers are from this workstation, not hbox — the shape is the measurement, the wall-clock is not.)

(the harness tampers 8 probes per rung, evenly spread through the schedule; the ratchet floor for
`pickles-stepmain-harness` is 9 `#[test]` functions and it declares 9.)

⚑ **THE `Generic` SHORTFALL WAS MIS-ATTRIBUTED, and this is the correction.** The prior header wrote
that the `ft_eval0` / `Plonk_checks.checked` sub-circuit was "≈5,900 `Generic` rows — the single
largest remaining sub-circuit". MEASURED (2026-08-02): the constant term is **467 `Generic` rows
here** (934 operations, two per double-generic row), and upstream's own generated
`Scalars.Tick.constant_term` (`plonk_checks/scalars.ml`, 3,295 lines) carries **~2,000 arithmetic
operators** — so even Snarky's unshared emission of it is ~1,000–1,500 rows, not 5,900. The
difference between 467 and that is real and named: `gateLinConst` is the STRUCTURED six-body form,
which shares the 15 Poseidon S-boxes and one α power chain across all 67 constraints, where
`Scalars.Tick` is a fully expanded `PolishToken` tree. Same value — pinned in §13 — fewer operations.

The remaining `Generic` gap (1613 vs 6245) is therefore NOT one missing sub-circuit. It is: the zkApp
branch's own `rule.main` application logic (which is not `verify_one` at all), `equal_g`,
`group_map`, `x_hat blinding` and the domain selection — the `sg_evals` prefix of the two `combine`s
(#4) LEFT this list on 2026-08-02, both its `E_c` ladders (§8i) and its `Opt.Maybe` mux (§12l) —
`ft_comm`'s own MSM LEFT this list on 2026-08-02 (§6b). #2–#11 below name the rest. ⚑ R8 spends 70 `Generic` rows on `finalize_other_proof`'s
tail. That is the trade this file is supposed to be making: every commit here should be buying a
named simplification, not scale.

⚑ Likewise `Poseidon` (2266 vs 6292): R7's added permutations ARE segment D, the OUTER
`hash_messages_for_next_step_proof`. ⚠ **THIS PARAGRAPH SAID "ELEVEN … because it is a `Sponge.copy`
of `sponge_after_index` and re-absorbs none of the 28 index commitments", AND THE "BECAUSE" WAS THE
LOAD-BEARING FALSEHOOD.** Segment D runs its own `sponge_after_index` over the instance's own wrap
key (`step.rs:2718`), so it absorbs 56 words ahead of the app state and costs 28 more permutations,
not eleven — the whole assembly moves 10 349 → 10 715 rows. `verify_one`'s own sponge work plus BOTH
of `step_main`'s hashes are assembled; every absolute count in this paragraph is stale and
`KimchiStepMainPins14`/`Pins18`'s censuses are the measured ones.

⚑ **WHERE FIAT-SHAMIR STANDS, stated at the resolution it is actually at, and BOTH HALVES.**

  * **GIVEN THE STATE, no challenge is prover-chosen.** All three `lowest_128_bits` range-check both
    parts (#1), and `should_verify` is a public statement word (§16g) so the rung that binds the
    deferred values cannot be switched off invisibly.
  * **THE INPUT IS NOW DERIVED WHERE `sponge_after_index` REACHES IT, AND NOT ELSEWHERE.** Segment
    C's `Not_opt` prefix went from **58 `hmVal` fixtures to 2**: 56 of those words are the wrap
    verifier key's 28 commitments in `index_to_field_elements` order, 27 of them the fold's own
    `.const` bases and the 28th pinned by an `Inner_curve.constant` row; the two that remain are the
    inductive rule's `app_state`, which no `verify_one` sub-circuit derives. And `index_digest` —
    the squeeze of that sponge — is now R1's FIRST absorbed word, so the transcript is a function of
    the verifier key. §12d exhibits the grind that was open until this landed: one plonk-index word,
    chosen by addition in under 48 tries, drives `index_digest` to a value the prover picked and
    MOVES EVERY transcript challenge (it is R1's FIRST absorbed word, so nothing precedes it) — and
    the pin row's own generic-gate body refuses it now.
  * **AND FOR `t_comm`, BECAUSE `ft_comm` NOW CONSUMES IT.** §6b assembles `Common.ft_comm`'s eight
    `scale_fast2`s; the seven quotient commitments are the MSM's operands, carry `Inner_curve.typ`'s
    `assert_on_curve`, and R4 round 2's base is the MSM's output rather than a supplied point.
    §12e exhibits the grind — one `t_comm` coordinate, chosen by addition in under 64 tries, moves
    ζ AND EVERY LATER CHALLENGE (β, γ and α are squeezed BEFORE `receive without t_comm`, `:563-567`,
    so upstream does not let a quotient chunk move them either) — and shows the on-curve row
    refusing it, and shows that substituting
    a VALID on-curve quotient chunk moves `ft_comm` and the fold, which is the difference between
    consuming a commitment and merely absorbing one.
    ⚠ What that does NOT do: an ON-CURVE substitution is refused by no rung here. The check that
    would refuse it is the IPA opening — `verified`, #11, still a witnessed boolean. The same is
    true of the 48 fold commitments since #3; what changed for `t_comm` is that it stopped being a
    word nothing reads.
  * ⚑ **AND THE LADDER'S SEED IS NO LONGER THE PROVER'S** (2026-08-02, §12f). `scale_fast_unpack`
    opens with `let acc = ref (add_fast base base)` and `let n_acc = ref Field.zero`
    (`plonk_curve_ops.ml:157-158`) and R3 emitted NEITHER, so `pAcc i 0` and `vSN i 0` were
    witnesses no row read. Doubling is a bijection on the group, so a chosen `acc₀` reaches EVERY
    output — `multiscale_known`'s result is `x_hat`, a public word and a segment-C absorption — and
    a chosen `n₀` lets the prover pick the BITS while the counter chain still closes on the
    challenge cell. §12f exhibits both witnesses, shows `varBaseMulConstraints` (proof-systems' own
    21, read-only) ACCEPTING the forged ladder row for row, and shows the two new rows refusing
    them. ⚑ The `n_acc` pin covers §6b's eight `ft_comm` ladders too: they carried `:157` and not
    `:158`.
  * ⚑⚑ **AND R1 IS INTERLEAVED TO UPSTREAM'S ABSORB/SQUEEZE ORDER, WHICH IS WHAT CLOSED THE LAST
    THREE ABSORPTIONS** (2026-08-02, §2b + §12i). R1 ran all `absorbs` absorb blocks and then all
    `chals` squeezes, in the `ipaAbsorbs` filter's order rather than `verify_one`'s. Read at source
    (`step_verifier.ml:534-574`, `:247-340`) the order is: `index_digest` · `sg_old ×2` · `x_hat` ·
    `w_comm ×15` · **β** · **γ** · `z_comm` · **α** · `t_comm ×7` · **ζ** · `combined_inner_product`
    · **u** · fifteen × (`(L,R)` then a **prechallenge**) · `delta` · **c**. The schedule is now
    that, and `absorbs` is DERIVED from it (§12b pins `absorbs == absorbBlocksOf`, at both shapes).
    Three closures follow, each with its CONSUMER:
      – **`sg_old[0]`** is `combine_split_commitments`' `~init` accumulator (`:606`): R4's
        `complete_add` chain starts at it, `ipaRounds` adds instead of `ipaRounds − 1`.
      – **`combined_inner_product`** (field + bit, `:79-81,256`) is absorbed AFTER ζ, so it is not a
        cycle; §12i pins that β/γ/α/ζ and `ft_eval0` are IDENTICAL with the word set to zero, and
        that every later squeeze MOVES. The absorbed field word IS `vCipShift` — the statement word
        R8's `combined_inner_product_correct` ties to R5's Horner output — so it is CONSUMED, not
        merely absorbed. The bit carries `Boolean.typ`'s own `b² = b`.
      – **`delta`** (`:321`) is consumed by `lhs = Scalar_challenge.endo q c + delta` (`:325-327`):
        one more 32-block `EndoMul` ladder over the fold output at the LAST squeeze, plus one
        `Ops.add_fast`. ⚠ `equal_g lhs rhs` is not here — that is `verified` (#11).
    **So `UNWIRED_ITEMS` is EMPTY and 1 of the 118 absorbed words is free**: block `oDigest`'s second
    lane. 117 is odd, this file models one commitment per rate-2 block, and one lane therefore
    carries nothing upstream feeds. **That is STRUCTURAL — there is no absorption behind it.**
  * ⚠ ⚑ **AND THE PRICE, STATED RATHER THAN QUIET.** Closing `cip` needed one more thing than the
    interleaving: `optSpec` (segment A, the opt-sponge) absorbed **R1's own transcript challenges**
    for its `2·bRounds` words, and so did `hmSpec`'s tail. Upstream both absorb `prev_challenges`
    (`step_verifier.ml:953-959`, `step_main.ml:80`) — the PREVIOUS proofs' carried challenges, a
    `Per_proof_witness` field with no relationship to this transcript. That false wire made
    `cip` a function of every transcript challenge, so absorbing it at ANY position was a cycle; the
    interleaving alone would not have fixed it. `prev_challenges` is now its own witness vector, read
    by BOTH segments (one σ class across two sponges, so segment C's public digest moves when one is
    bent). What that COSTS: `2·bRounds` words that were derived cells are now prover-supplied,
    bound by `verified` (#11) exactly as upstream binds them, and by nothing in `verify_one`.

  * ⚑⚑ **AND `step_main`'s TWO HASHES ARE NOW BOTH ASSEMBLED, AND ONE OF THEM WAS HASHING THE
    WRONG THING** (2026-08-02, §8e′ + §12k). The INNER `…_opt` call (`step_main.ml:59-81`) — segment
    C, whose digest is the WRAP statement's `messages_for_next_step_proof` — had its two commitment
    slots wired to R3's x_hat output and R4's fold output `q`. Upstream's are
    `prev_challenge_polynomial_commitments`, i.e. `sg_old`, which this assembly already held as the
    fold's `~init` and its round-0 base; and the commitments are INTERLEAVED with their own challenge
    runs (`composition_types.ml:595-607`), which the segment also did not do. A public word was a
    function of two quantities upstream does not put in it. §12k bends both directions on the emitted
    digest. The OUTER call (`:525-566`) — segment D, the STEP statement's own
    `messages_for_next_step_proof` — is now assembled too, and it is what absorbs `G`.
  * ⚠ ⚑ **AND `G` IS BOUND TO THE STATEMENT AND NOT TO THE OPENING. SAY BOTH.** Before this rung
    `G = challenge_polynomial_commitment` had ZERO occurrences in the assembly; it now has
    `assert_on_curve` and segment D's absorb, so a substituted `G` moves a public word. It is still
    **not refused**: `rhs`/`equal_g` are not emitted, so no row relates `G` to the IPA opening, and
    §17(e) re-runs the substitution exhibit and it is ACCEPTED exactly as before.
  * ⚠ ⚑⚑ **AND THE NEXT STEP'S CONSUMER IS NOW BUILT AND MEASURED, AND IT ACCEPTS IT TOO**
    (2026-08-02, §18). The bullet above used to end "the refusal belongs to whoever COMPARES
    `messages_for_next_step_proof` — the next step's `verify_one`, one recursion step later." §18
    builds that chain: segment C at step `N+1`, fed step `N`'s app state, `G` and returned
    bulletproof challenges, reconstructs step `N`'s public word 7 EXACTLY (§18(a)) — and the
    SUBSTITUTED chain reconstructs the MOVED word just as exactly (§18(b)). **The tie propagates the
    substitution; it does not refuse it.** What it does refuse is the mismatch: a prover cannot move
    word 7 at `N` and then carry the honest `G` at `N+1` (§18(d)). Read at source the tie is not even
    an equality — the digest is SUBSTITUTED into the wrap statement (`step_main.ml:83-84`) and
    consumed as x_hat MSM term 12's scalar (`step_verifier.ml:1237-1245,543-545`,
    `composition_types.ml:854-882`). The refusal is one link further: the accumulator check
    (`per_proof_witness.ml:12-32`), whose `E_c = f_c(ζ)` leg is simplification #4's residue and is
    measurably ABSENT (§18(f)) and whose OPENING leg is `verified` (#11). With `G` fixed, `z₁`/`z₂`
    leave a two-dimensional discrete log: an ASSUMPTION.

So: the sponge input is derived for the verifier key and for the quotient commitment, both MSM
ladders and every endo ladder start where upstream starts them, the blocks are fed in upstream's
order, every item `verify_one` absorbs is a word some row here READS, both of `step_main`'s
`messages_for_next_step_proof` hashes are over the objects upstream hashes, and the two of them are
pinned as the two ends of ONE inter-step chain. What is left of the transcript residue is one
structural pad lane — and `verified` (#11), which is still a witnessed boolean and is still what
would have to hold `G` to its opening, **at every step of that chain and not only at this one.**

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** a Mina-valid proof; the
kimchi proof the harness produces is an **INNER** proof of a `verify_one`-shaped circuit, and wrap
is a later rung. What is reportable is INNER-KIMCHI FIDELITY of the assembled recursive verifier:
the Lean-authored eight-rung assembly is accepted by a pure-Rust kimchi prover, and every
sub-circuit boundary BINDS.

## ⚑ THE σ-ONLY PROBES

Every load-bearing shared cell is also gate-read, so flipping one cannot ISOLATE σ. Each sub-circuit
boundary value is therefore ALSO materialized in a standalone `Zero` **probe row** placed into the
same class. A `Zero` gate reads nothing and no gate reads a probe row, so a probe cell is
constrained by σ and by NOTHING ELSE. The `…Unwired` variant is identical EXCEPT the probe rows are
in no class — the control that turns "rejected" into "rejected BY THE WIRE".

## NAMED SIMPLIFICATIONS (undone work, not theorems)

  1. ⚑ **RETIRED 2026-08-02, and the ORIGINAL COSTING WAS WRONG.** This read "upstream's
     `lowest_128_bits ~constrain_low_bits:true` spends 16 rows + 1 generic… **16 rows per challenge
     not assembled**". READ AT SOURCE, `assert_n_bits ~n:128` is not a bespoke gadget — it is
     `ignore (SC.to_field_checked (Scalar_challenge.create a) ~num_bits:n)`
     (`step_verifier.ml:88-97`): the `EndoMulScalar` chain runs and emits every row, and ONLY the
     returned field element is dropped. So the retirement is `tfcRows` again, once per SPLIT source
     — `chals` for R2 and one for §8g's `r` (§8g's ξ has none: its source is already a
     `Challenge.t`, so upstream splits nothing there either).
     ⚑ IT WAS A SOUNDNESS HOLE, NOT A ROW COUNT. With only `lo` constrained the decomposition row is
     ONE equation in TWO unknowns: for any `lo' < 2¹²⁸` a prover solves
     `hi' = (squeeze − lo')·2^{−128}` and the Fiat-Shamir challenge is his. §12c exhibits that exact
     witness, shows it satisfies the decomposition row, shows the LOW chain accepts it, and shows the
     new HIGH chain refuses it (`hi' ≥ 2¹²⁸`, so its own `EndoMulScalar` fold cannot reconstruct it).
     ⚑ **AND THE THIRD SITE IS NOW CLOSED TOO (2026-08-02).** The residue this entry carried read:
     "the THIRD `lowest_128_bits` — the split of the fr-sponge's FIRST squeeze inside R8's compiled
     finalize program, for `xi_correct` — still has no high chain." It was the WORST of the three,
     because §8g's chain 0 lifts the very statement word `xi_correct` compares against INTO THE FOLD:
     a prover who chose ξ chose `combined_inner_product`'s own multiplier. R8's `hi` was an `AOp.wit`
     — a cell no row defines — so `xi_actual = squeeze − 2¹²⁸·hi` could be made ANY 128-bit value.
     Both chains are now emitted (`util.ml:98` asserts `hi` unconditionally, `:99` asserts `lo`
     because `Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true`,
     `step_verifier.ml:821-822`), wired to the compiled program's OWN cells. §12c′ exhibits the
     forged ξ, shows R8's program ACCEPTS it (`out = 1`, `xi_correct = 1`, `xi_actual` = the chosen
     ξ) and that the fold's multiplier and `combined_inner_product` both MOVE under it, and shows the
     new high chain REFUSES it. All three `lowest_128_bits` in the assembly are now range-checked on
     both parts, so **no Fiat–Shamir value in this circuit is prover-chosen.**
  2. ⚑ **RETIRED (WIDTHS) 2026-08-03 — §20, `…Pins15`. The provenance half is still open.**
     This entry has been wrong twice. It first read "the 255-bit width is expressible with
     `msmChunks = 51`; taking it costs ~1000 `VarBaseMul` rows", which would have been a uniform
     WIDENING and less faithful, not more. It was then corrected to a per-word census that got
     `Backend.Tick.Rounds.n` and the ninth one-bit word right and said so — and the campaign brief
     that carried it forward "corrected" both of those to 15 and 8, which is wrong; see below.

     `multiscale_known`'s scalars are the previous proof's **packed Wrap STATEMENT** —
     `multiscale_known (Array.mapi public_input ~f:(fun i x -> (x, lagrange_commitment ~domain srs
     i)))` (`step_verifier.ml:543-544`) over `Spec.pack … (Types.Wrap.Statement.In_circuit.spec …)`
     (`:1236-1251`) — and `Spec.pack` carries a width PER BASIC (`spec.ml:305-395`). `Field` and
     `Digest` at `Field.size_in_bits = 255`, `Challenge` / `Scalar Challenge` /
     `Bulletproof_challenge` at `Challenge.length = 64·2 = 128` (`limb_vector/challenge.ml:5`,
     `constant.ml:70`), `Branch_data` at `length_in_bits = 10` (`branch_data.ml:61`), `Bool` at 1;
     scaled at `chunks_needed ~num_bits:(n−1)` 5-bit chunks (`plonk_curve_ops.ml:64-68,250-256`).
     The census (`composition_types.ml:785-823`, `to_data` at `:825-880`) is

         i      word(s)                                            basic                 bits chunks
         0–4    combined_inner_product, b, ζ^srs_len, ζ^dom, perm  Field                  255     51
         5–6    beta, gamma                                        Challenge              128     26
         7–9    alpha, zeta, xi                                    Scalar Challenge       128     26
         10–12  sponge_digest_before_evals, msgs_next_wrap/step    Digest                 255     51
         13–28  bulletproof_challenges ×16                         Bulletproof_challenge  128     26
         29     branch_data                                        Branch_data             10      2
         30–37  the eight feature flags                            Bool                     1      0
         38     the lookup Opt's OWN flag bit                      Bool                     1      0
         39     the lookup Opt's inner scalar challenge            Scalar Challenge       128     26

     ⚠ **TWO "CORRECTIONS" THAT WERE THEMSELVES WRONG, both refuted at source AND in Mina's compiled
     circuit.** (a) The bulletproof run is **16, not 15**: the vector is `Vector (B
     Bulletproof_challenge, Backend.Tick.Rounds.n)`, `Backend.Tick = Vesta_based_plonk`
     (`pickles/backend/backend.ml:1-4`), `Vesta_based_plonk.Rounds = Rounds.Step = Nat.N16`
     (`vesta_based_plonk.ml:51`, `kimchi_pasta_basic.ml:17`). `Rounds.Wrap = Nat.N15` is real and is
     the WRAP proof's own IPA round count on Pallas, not this vector's length. (b) `Features` does
     carry **8** and not 9 (`composition_types.ml:786-812`) — and the ninth one-bit word was never a
     feature flag: it is the lookup `Opt`'s own flag, which `Spec.pack` emits ahead of the inner spec
     in all three polarities (`spec.ml:123-140`). The count was right for the reason stated.
     ⚑ (c) There is no `Scalar_challenge` BASIC. `Scalar chal` is a `T.t` constructor whose `pack` is
     `p.pack chal` (`spec.ml:94-99`), so it packs at the `Challenge` width. That one the brief had
     right, and it moves nothing.

     ⚑ **THE REALITY GATE.** Measured off `step-zkapp-proved`, the o1-labs circuit blob — Mina's own
     compiled step circuit — the `x_hat` `var_base_mul` cluster is **31 ladders**, chunk widths in
     row order `51,51,51,51,51, 26,26,26,26,26, 51,51,51, 26×16, 2, 26`, **982 chunks**. That is the
     census above with the nine one-bit words dropped, element for element: `multiscale_known`
     PARTITIONS on `` `Packed_bits (Constant c, _) `` (`step_verifier.ml:133-140`) and folds the
     constant scalars outside the circuit, and `chunks_needed ~num_bits:0 = 0` lands on exactly that
     without a special case. `…Pins15.x_hat_widths_are_minas_own_compiled_ladders` states the
     equality.

     **WHAT LANDED.** `StepShape.msmChunks` is DELETED; `msmBits` / `msmChunksAt` / `msmChunkPrefix`
     (Core §1b) give statement word `i` its own width; `pT` / `pAcc` / `pSum` / `nMsmPts` / `vSN` /
     `baseIpa` are cumulative prefix sums instead of a constant stride; `bitsOf` takes the term index;
     `msmRows` and `circuitEnv` range over `msmChunksAt i`; and `msmNZeroRows` SKIPS the zero-chunk
     terms, because on those `vSN i 0` IS the term's challenge variable and a `w₀ = 0` half over it
     would pin a shared challenge. The emitted total goes 1040 → **982**: the fix is not a widening.

     ⚑⚑ **AND THE PROVENANCE HALF LANDED TOO — §21, `…Pins16`, 2026-08-03. #2 IS FULLY RETIRED.**
     This paragraph read "term `i`'s scalar is still `vN (msmChal i) emsRows` — a shared transcript
     challenge — and NOT Wrap statement word `i`… a 255-bit width over a value that is structurally
     `< 2¹²⁸` is shape-faithful and semantically empty", and it predicted the two remaining items;
     both are done. `StepShape.msmChal` is DELETED, `vSN i (msmChunksAt i)` is `stmtVar i`, and
     `msmRows` runs `multiscale_known`'s NON-CONSTANT partition. See §21 below.
     ⚠ `ft_comm`'s eight `scale_fast2`s ARE uniformly 255 (`step_verifier.ml:240-242`) and stay at
     `FTC_CHUNKS = 51`: two `VarBaseMul` regions, two genuinely different scalar widths.

     **§21 — THE SCALARS, word by word** (`composition_types.ml:823-880` for the order,
     `spec.ml:358-395` for `pack_basic`, both read at source):

         i      word                                    wired to                    provenance
         0,1,4  cip, b, perm (all `Shifted_value.Type1`) `vCipShift`/`vBShift`/`vPermShift`  R8 binds
         2,3    ζ^srs_len, ζ^dom                        R6's `ζ^n` cell             DERIVED
         5–8    β, γ, α, ζ                              `vN c emsRows`              R2 decodes
         9      ξ                                       `vXiStmt`                   R8's `xi_correct`
         10     sponge_digest_before_evaluations        `digestBeforeEvalsVar`  ⚑ §22 DERIVED —
                                                        R1's ζ-squeeze lane 1, and segment B's SEED
         11     messages_for_next_wrap_proof            `vStmtWrapMsgs`    ⚠ NO IN-CIRCUIT SOURCE
                                                        (nor upstream: `step_main.ml:364-366`)
         12     messages_for_next_step_proof            segment C's squeeze         §8e′ computes it
         13–28  bulletproof_challenges ×16              `vN (uChal k) emsRows`      R8's `b_correct`
         29     branch_data                             `vBranch`                   §8h unpacks it
         30–38  8 feature flags + the Opt's flag        no cell reaches a row       CONSTANT partition
         39     the lookup Opt's Scalar Challenge       `vStmtLookup`      ⚠ NO IN-CIRCUIT SOURCE

     ⚑ **FOUR SOURCE CORRECTIONS THIS RUNG MADE, each one refuting something written here.**
     (a) `pack_basic`'s `Field` arm is `` [| `Field x |] ``, **not** `` `Packed_bits (x, 255) ``
     (`spec.ml:373-374`); `multiscale_known` scales that case at `~num_bits:Field.size_in_bits`
     (`:159-165`). §1b's docblock said `Packed_bits` and was wrong — the WIDTH is unaffected.
     (b) `Plonk_checks.checked` compares the list **`[ perm ]` and nothing else**
     (`plonk_checks.ml:537-544`): `zeta_to_srs_length`/`zeta_to_domain_size` are never checked
     in-circuit upstream at all, so wiring words 2/3 to R6's DERIVED `ζ^n` is strictly MORE
     constrained than upstream. ⚠ It also merges two upstream statement variables into ONE cell
     here, which is a σ divergence and is pinned as one.
     (c) The scalars are `Bulletproof_challenge.pack`'s PRECHALLENGE (`Sc.inner`, `spec.ml:390-393`),
     so words 5–9/13–28/39 are `vN c emsRows` and **not** `vLift c`. Taking the lift would put a
     `> 2¹²⁸` value under a 130-bit ladder and the counter chain could not close.
     (d) Words 13–28 are the STEP proof's sixteen IPA challenges carried in the WRAP statement
     (`per_proof_witness.ml:66-72`, `Types.Step_bp_vec`) — the SAME sixteen `finalize_other_proof`
     folds for `b_correct` (`:1113-1128`). They are not `prev_challenges`, and they are not a fresh
     witness vector.

     ⚑ **THE RED CONTROL PAIR, which is what makes the width mean something** (`…Pins16`): bending
     statement word `i` MOVES `x_hat`; bending transcript challenge `c` / ξ / r — which no statement
     word carries — moves NOTHING, while the SAME bend under the retired round-robin moves it. Under
     `msmChal i = i % 23` all twenty-three challenges moved all forty terms and no statement word
     moved any.

     ⚑ **AND THE CONSTANT PARTITION, decided by MINA'S OWN COMPILED CIRCUIT.** `List.reduce_exn` over
     `non_constant_part` (`:180-182`) is one contiguous run of `|non_constant| − 1` `CompleteAdd`
     rows, and `step-zkapp-proved` has exactly one run of **THIRTY**. Forty terms would give
     thirty-nine. So the nine one-bit words get no base pin, no `add_fast base base` seed, no probe
     and no fold add: **−45 rows at the committed shape** (9 base + 9 seed + 9 add + 18 probes), and
     the ladder census is untouched because they emitted no `VarBaseMul` row to begin with.
     ⚠ A one-bit VARIABLE word would still cost a seed upstream (`plonk_curve_ops.ml:157` runs before
     the chunk loop); the nine are dropped because of the PARTITION, not because of the width.

     ⚠ **THE RESIDUE §21 LEAVES: three of the forty scalars are prover-chosen here** — words 10, 11
     and 39, each at its own named cell rather than aliased to something convenient. Word 10's
     absence is a MEASURABLE gap one rung out: upstream seeds the fr-sponge with
     `sponge_digest_before_evaluations` (`step_main.ml:41-46`) and **segment B here starts at
     `challenge_digest`** — the seed absorb is not emitted, which is why the word has no derived
     cell. Word 11 is substituted into the statement by `step_main.ml:84` from outside `verify_one`;
     word 39 needs a lookup this assembly does not model.
  3. ⚑ **RETIRED 2026-08-02, and reading at source split it in two.** This read "the MSM base points
     are `basePts` (distinct on-curve Pallas points), not the previous proof's actual commitments".
     Upstream's bases have TWO provenances and NEITHER is a free witness (§3b): `multiscale_known`'s
     are `Inner_curve.constant (lagrange_commitment ~domain srs i)` (`:150,165-172,543-544`), as are
     the verifier-key `m.*_comm` the fold consumes; the previous proof's OWN commitments — `sg_old`,
     `x_hat`, `z_comm`, `w_comm` and `bullet_reduce`'s fifteen `(L,R)` — are ABSORBED INTO THE
     TRANSCRIPT before the challenge that weights them is squeezed (`:537,559,561,564`; `:193`).
     This file had NEITHER: every base was a free witness holding a fixture, and R1 absorbed
     `2·absorbs` unrelated words.
     ⚑ **The bases are now Mina devnet block 539508's own Wrap-proof commitments** —
     `Dregg2/Bridge/MinaStepPrevCommitments.lean`, which owns NO literals and reads them out of the
     `MinaWrap*` gates that already hold them: the 40 SRS Lagrange commitments,
     `combine_commitments`' own 47 and `bullet_reduce`'s 30, Pallas points in this assembly's own
     field, off a proof openmina's `BlockVerifier` accepted with `accumulator_check = true`. Each
     one is either PINNED by a `Generic` `Inner_curve.constant` row or ABSORBED, its two coordinate
     variables BEING transcript block `b`'s absorbed words — one σ class spanning `Poseidon` and
     `EndoMul`. 18 fold commitments + 30 gammas absorbed, 28 verifier-key/computed constants, all 40
     of R3's constant.
     Red control (§12b): swap ONE absorbed commitment for another real point and EVERY challenge
     moves, the fold output moves, the x_hat MSM moves (its scalars are those challenges),
     `combined_inner_product` and `b(ζ)` move. Swap a CONSTANT one and NO challenge moves — and the
     pin row's own generic-gate body (`KimchiVerify.genericGateConstraint`, read-only) goes nonzero,
     i.e. it is REFUSED. With `basePts` neither could happen in either direction.
     ⚑ **AND THE `is_on_curve` RESIDUE IS CLOSED (2026-08-02).** This entry read "there is no
     in-circuit `is_on_curve` check on a supplied point (`Inner_curve.typ`'s own)". §7b is that
     check, on all 48 absorbed bases: `assert_on_curve` (`snarky_curve.ml:212-229`) is
     `x2 = x²; x3 = x2·x; assert_square y (x3 + a·x + b)`, and Pallas' `a = 0` folds the middle term
     away, so it is three `Generic` halves per point. Red control (§12b′): bend ONE absorbed base's
     `y` by one and the point leaves the curve, yet `endoMulConstraints` and `completeAddConstraints`
     — proof-systems' own polynomials, read-only — are ZERO on every curve row of the bent
     assembly's composed grid. That is the hole, on the emitted object. The new row's `Generic` body
     is nonzero there and zero on the honest grid, and the `x²`/`x³` halves stay zero (the bend was
     in `y`), so the control is about the check and not about the re-run.
     ⚑ **AND THE RESIDUE THIS ENTRY CARRIED IS CLOSED (§21, 2026-08-03).** It read
     "`multiscale_known`'s SCALARS are upstream's PUBLIC INPUT words; here they are still the
     circuit's own derived challenges." They are the statement's words now; #2 carries the detail,
     because reading `Spec.pack` at source made it the SAME item as the widths.
  4. ⚑ **RETIRED 2026-08-02, and the ORIGINAL CLAIM WAS WRONG.** This entry read "`combined_inner_
     product` is HALF of upstream's — R5 assembles ONE ξ-Horner fold (at ζ)". READ AT SOURCE, R5's
     `cipRows` folds `cₖ = evₖ(ζ) + r·evₖ(ζω)` and then Horners over ξ, i.e.
     `Σₖ ξᵏ(ez_k + r·ew_k)` — which IS `combine(ζ) + r·combine(ζω)` term-for-term, and IS
     `KimchiVerify.cipR`'s own body. The r-weighted second fold was never absent; it was folded per
     COLUMN instead of per POINT. What WAS absent is now R8: `b_correct`'s `+ r·challenge_poly ζω`
     leg and the `Shifted_value.Type1.to_field` unshifts.
     ⚑⚑ **AND THE `sg_evals` RESIDUE IS CLOSED TOO (2026-08-02, §8i) — `E_c = f_c(ζ)` IS COMPUTED.**
     This entry read "**Still open:** the `sg_evals` prefix entries (`vEz 0/1`, `vEw 0/1`) are
     `evVal` fixtures where upstream puts the b-polynomial of the CARRIED old bulletproof
     challenges". They are now four `f_c` ladders over `vPrevChal` — `challenge_polynomial`
     (`wrap_verifier.ml:16-35`) at `plonk.zeta` and at `zetaw`, per slot, wired into `combine`'s own
     prefix (`step_verifier.ml:935-948` feeding `:1076-1102`). §18(f) pins each of the four against
     `KimchiVerify.bEvalSq`, the read-only transcription, and pins that a bent carried challenge
     moves `E_c` and `combined_inner_product` (a PUBLIC WORD) with it. `prev_challenges` reach a
     public word for the first time.
     ⚑ **THE TRAP, PINNED SO A FUTURE CONFLATION REDS.** `f_c` over `prev_challenges` is NOT `f_c`
     over this proof's own returned bulletproof challenges — upstream says it in one line at
     `step_verifier.ml:918` ("You use the NEW bulletproof challenges to check b. Not the old ones.")
     — and using the latter would close the leg VACUOUSLY. §18(f) pins the value inequality AND the
     row-level read-set disjointness in both directions: §8i's rows touch no `vLift (uChal k)`,
     `deferredRows`' touch no `vPrevChal`.
     ⚠ **WHAT IT DOES NOT BUY, said where the claim is made.** Read at source
     (`per_proof_witness.ml:12-32`) these four entries ARE `E_c` and the accumulator check is TWO
     legs — "`challenge_polynomial_commitment` **opens** to `E_c` at zeta" AND "`E_c = f_c(zeta)`".
     This is the SECOND of those and not the first. `E_c` is a function of `prev_challenges` and ζ;
     `sg_old` does not occur in it, so nothing here relates the commitment to the value it must open
     to. §18(b) is re-run with the leg computed and the substituted chain is **ACCEPTED exactly as
     before**. What is removed is a different, independent forgery surface: four free witnesses the
     prover chose are now derived cells.
     ⚑⚑ **AND `combine`'s `Opt.Maybe` MUX IS NOW EMITTED TOO (2026-08-02, §12l) — the mask's LAST
     ignoring consumer, +3 `Generic` rows.** This entry read "STILL NOT EMITTED; `cipRows` folds all
     `cipEvals` entries unconditionally". The two `Maybe` steps now run `Field.if_ keepⱼ`
     (`common.ml:270-271`) off §8h's DERIVED `branch_data` bits — the same two variables the
     opt-sponge and segment C mux with — so every consumer of `proofs_verified_mask` upstream has is
     assembled here.
     ⚠ ⚑ **AND THE RESIDUE'S OWN PREMISE WAS WRONG AT SOURCE, which is the measurable part.** It was
     expected to be value-identical at the deployed mask, slot 0 being the `Wrap_hack` dummy
     (`wrap_hack.ml:26-28` prepends dummies). It is NOT: `mul_and_add`'s `else_` branch is bare `acc`
     with NO ξ multiplication, and `Pcs_batch.combine_split_evaluations` folds the flattened list in
     REVERSE (`pcs_batch.ml:88-94`), so slot 0 is the LAST fold step and dropping it takes one ξ
     power off all 46 surviving terms. **`combined_inner_product` — public word 9 — MOVES at the
     deployed mask**, and the three legal masks (`proofs_verified.ml:75-91` admits exactly three)
     give three different field elements. §12l pins each against `cipR` over ITS OWN kept sub-list,
     pins that the unconditional fold and the zero-the-entry fold are two OTHER values, and runs the
     both-direction bend: slot 0's carried challenges move `E_c` and leave `cip` at `[0,1]` and move
     it at `[1,1]`; slot 1's move it at both.
     ⚠ **IT CHANGES NO VERDICT.** `cip` is a value R8 ties to a statement word — moving it moves what
     an honest prover must claim. §17(e)/§18(b) are re-run and are ACCEPTED exactly as before.
  5. **Named and NOT assembled**, each a real sub-circuit: `group_map` (`step_verifier.ml:214-237`);
     `equal_g` and the `check_bulletproof` tail's `scale_fast` of `sg`;
     `x_hat blinding`; `lagrange_commitment` / `public_input_commitment_dynamic`'s domain selection;
     `actual_evaluation`'s per-column chunk Horner (`combined_evals`; our columns are single-chunk,
     though `ζ^n = pow2_pow ζ 16` IS assembled in R6); `Evals.validate_feature_flags`; and the
     app-logic `rule.main`. (`xi_correct`, the `Boolean.all` finalisation and its assert, and the
     `should_verify` mux left this list on 2026-08-02 — they are R8. ⚑ **`sponge_after_index` LEFT
     IT on 2026-08-02 too** — it is §3c, and the entry it used to carry read "the plonk index is
     hashed here from `N_HM_FIX = 58` FIXTURE words, not from the actual commitments".)

     ⚑ **`ft_comm`'s own 8-term MSM LEFT THIS LIST on 2026-08-02 — it is §6b.** The entry named
     three undone things: "a second `VarBaseMul` region at `msmChunks = 51`, its scalars wired to
     R6's `zeta_to_srs_length` / `zeta_to_domain_size` and R6's `perm` rather than to fresh
     witnesses, and R4 round 2's base (`COMBINE_XY[3]`) becoming that MSM's OUTPUT instead of an
     `Inner_curve.constant`." All three landed. `Common.ft_comm` (`common.ml:238-256`) is
     `perm·sigma_comm_last + chunked_t_comm − zeta_to_domain_size·chunked_t_comm`, `chunked_t_comm`
     a 7-chunk Horner in `zeta_to_srs_length` — eight `scale_fast2`s and eight `Ops.add_fast`s, every
     scale at `~num_bits:Field.size_in_bits = 255` (`step_verifier.ml:240-242`), i.e.
     `chunks_needed ~num_bits:254 = 51` five-bit chunks.
     ⚑ **AND IT WAS ASSEMBLED THE WAY THE PREVIOUS ENTRY SAID IT HAD TO BE.** That entry warned:
     "absorbing the 7 `t_comm` commitments into R1 WITHOUT the MSM would move 14 words off the free
     list while changing nothing a prover can do — an absorbed commitment that no sub-circuit
     consumes is still ground freely." §12e is the measurement that it IS consumed: substitute ONE
     quotient chunk — chunk 0, which is only a Horner ADDEND and no scale's base — and `ft_comm`
     moves, so R4 round 2's base moves and the fold moves with it; and the grind that steers every
     transcript challenge off ONE `t_comm` coordinate is REFUSED by `assert_on_curve`, which covers
     `t_comm` now because it arrives through `Inner_curve.typ` like every other supplied commitment.
     ⚠ **THE RESIDUE, and it is a REPRESENTATION one.** Upstream's `ft_comm` scalars are
     `unfinalized.deferred_values.plonk` through `Plonk.In_circuit.to_wrap`
     (`step_verifier.ml:1264-1267`) — `Other_field.t Shifted_value.Type2.t` STATEMENT words over the
     OTHER field (`impls.ml:50-57`), which the step circuit does not constrain at all; the `Fp` Type1
     twins R6/R8 check are different objects and the tie between them is the next wrap proof's job.
     Here the ladder reads R6's OWN cells, which is strictly MORE constrained inside this circuit —
     and the price is that `Shifted_value.Type2`'s `2^255` shift cancels in `Fq`, a fact this circuit
     cannot see. §6b states it at the point of use rather than in a footnote.
  6. Every challenge is derived at ONE width (128 bits, 8 `EndoMulScalar` rows). Upstream also uses
     16/32/64/192/256-bit `to_field_checked` (the 1/2/4/12/16-row runs in the table). ⚑ Since #1 the
     assembly emits `2·chals + 5` chains where it emitted `chals + 2`, so the 8-row family is now
     over-represented rather than under-; the missing WIDTHS are still missing.
  7. ⚑ **RETIRED 2026-08-02.** `to_field_checked` is the `EndoMulScalar` chain, then
     `Field.Assert.equal n scalar`, then **`Field.(scale a endo + b)`** (`scalar_challenge.ml:125-129`)
     — R2 emitted the first two and stopped. It now emits the third: ONE `Generic` row per challenge
     turning the chain's own `a₈`/`b₈` cells into `vLift c`, pinned in §16 against
     `KimchiVerify.endoMap ENDO_R` with the `FT_ENDO`-for-`endo_r` cube-root conflation as its red
     control. `plonk.zeta`/`plonk.alpha` (R6), the deferred ξ/r (R5's `combined_inner_product`) and
     every bulletproof challenge (R5's and R8's `challenge_polynomial`) now read the LIFTED value;
     β/γ stay raw, which is upstream's own split (`map_challenges ~f:Fn.id ~scalar`).
  8. ⚑ **RETIRED 2026-08-02.** R6's seven coset shifts were `FT_SHIFTS`, distinct nonzero fixtures.
     `FT_SHIFTS` is now **`TickShifts.tickShiftsFp 16`** — the `Shifts::new` Blake2b→field
     construction (`permutation.rs:149-197`), `#guard`-pinned in `Dregg2/Bridge/TickShifts.lean`
     byte-exact against o1-labs' own `Shifts::new(Radix2EvaluationDomain::<Fp>::new(2^16))` output.
     §13 re-states the identity at the point of use, checks the structure the derivation guarantees
     (`shifts[0] = 1`, six distinct QNRs outside the domain), and carries the RED CONTROL that makes
     it a retirement rather than a rename: `FT_SHIFTS_WERE_FIXTURES` gives a DIFFERENT `ft_eval0` at
     the same wire, as does a one-unit bend in any derived shift.
  9. ⚑ **RETIRED 2026-08-02.** This read "R7's opt-sponge mask is a fixed `keep` pattern (the first
     half of the blocks kept)… what is not here is deriving it from `branch_data`." §8h derives it.
     `branch_data` is ONE field element packing `4·domain_log2 + (m₀ + 2·m₁)`
     (`branch_data.ml:95-101`), and it is now the assembly's **fifth statement word**: the two
     `proofs_verified_mask` bits are Boolean circuit variables, booleanity-constrained by a row, tied
     to that word by `Checked.pack` emitted as a row, and the opt-sponge's mux reads THEM. Reading at
     source also corrected the pattern: `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] ·
     N2 ↦ [tt;tt]` (`pickles_base/proofs_verified.ml:75-81`), so a set bit is a SUFFIX and the
     one-previous-proof instance keeps the SECOND slot — the opposite of what the fixed pattern did.
     Red control (§14a): the other two legal prefix masks each give a DIFFERENT opt-sponge digest,
     and that digest is segment B's first absorbed word, so `branch_data` reaches the fr-sponge, both
     squeezes, §8g's ξ and r, and `combined_inner_product`.
     ⚑ **AND THE SECOND CONSUMER LANDED, 2026-08-02.** This note read: "`hash_messages_for_next_
     step_proof` (segment C) masks the SAME carried challenges upstream and here absorbs them
     unmasked… one `Vector.map2` away". Done. Segment C now masks BOTH the two
     `challenge_polynomial_commitments` AND the carried challenges with the same two `branch_data`
     bits (`step_verifier.ml:1180-1186` — two `Vector.map2`s, one mask), from block `N_HM_FIX/2` on:
     `Opt_sponge.of_sponge` converts at the FIRST `Opt` element (`:1198-1211`), so the `Not_opt`
     prefix stays unconditional and `SegSpec.maskFrom` is that boundary.
     ⚑ AND ITS DIGEST IS NOW A PUBLIC WORD. Upstream's `messages_for_next_step_proof` hash is one,
     and until this landed segment C's squeeze reached NOTHING — the mask would have been derived
     and then discarded. Red control (§14a): the three legal prefix masks give three DIFFERENT
     digests, `[1;1]` IS the unmasked absorption (so the pin says exactly "the old segment C computed
     a different hash"), and both mask legs are exercised.
     ⚠ The `Not_opt` prefix went 57 → 58 words for one structural reason, stated rather than hidden:
     this segment's `Field.if_` mux is per rate-2 BLOCK where upstream's `Opt_sponge` is per FIELD
     ELEMENT, so the `Opt` region must begin on a block boundary. A per-element opt-sponge is undone
     work, not a theorem.
     ⚑⚑ **AND THE THIRD AND LAST CONSUMER LANDED, 2026-08-02 (§12l).** `verify_one`'s file has
     EXACTLY three consumers of the mask — `step_verifier.ml:944` (`sg_evals`, feeding `combine`),
     `:954` (the opt-sponge) and `:1182-1186` (the inner hash) — and `:944` was the one still
     ignored: `cipRows` folded all 47 prefix entries unconditionally. It now runs `combine`'s own
     `Opt.Maybe` mux. (`wrap_verifier.ml:513` and `wrap_main.ml:173-195` are the WRAP circuit, a
     different object, and are out of this assembly's scope by construction.) So
     `branch_data.proofs_verified_mask` now reaches R5's fold, R7's opt-sponge and R7's segment C,
     which is every place upstream puts it in this circuit.
 10. ⚑ **RETIRED 2026-08-02 — the fr-sponge now FEEDS the fold, not merely gets checked against it.**
     This entry read: "the ξ/r the C8 fold multiplies by are R1's transcript challenges, not
     `endoMap` of R7's squeeze… R8's `xi_correct` binds the STATEMENT's ξ to the fr-sponge squeeze
     but does not yet make that word the fold's own multiplier." §8g is that multiplier. READ AT
     SOURCE (`step_verifier.ml:1006-1013`), upstream is a TWO-STEP, and the two multipliers have
     DIFFERENT provenance: `xi = scalar xi` lifts the STATEMENT's ξ word (the one `xi_correct` ties
     to the first squeeze), while `r = scalar (Scalar_challenge.create r_actual)` lifts the SECOND
     squeeze directly and has no statement word at all. Both are now real `to_field_checked` chains
     — 8 `EndoMulScalar` rows, the tie to their source, the endo lift — and `cipRows`/`b_correct`
     multiply by their outputs. The red control BITES: bending either squeeze by one moves
     `combined_inner_product` and `b_actual`, which it could not do before (§12a, §16b).
     ⚠ THE HONEST RESIDUE, pinned in §15: ξ's source is a statement word so its chain rides with R5
     and binds from `r5_full` up; `r`'s source is an R7 variable, so at r5/r6 — sub-circuits strictly
     below the fr-sponge — the fold's `r` is a free witness, and it binds at r7/r8. That is the
     ladder position `vEz 3` (R6's `ft_eval0`) and the four statement words already occupy.
 11. R8's `verified` bit (the kimchi `verify` result the mux ANDs with `finalized`) is a witnessed
     boolean, booleanity-constrained and nothing else. ⚑ **`should_verify` LEFT THIS ENTRY on
     2026-08-02** — it was never a missing sub-circuit, it was a STATEMENT WORD this file had made a
     witness, and a witnessed `should_verify` let a prover switch the whole `Boolean.all` assert off
     (§16g). `verified` is different, and the rest of this entry is why.
     ⚑ **NOT RETIRABLE WITHOUT A SUB-CIRCUIT THAT
     DOES NOT EXIST.** `verified` is `Step_verifier.verify` (`step_main.ml:88-107`) — the whole wrap
     kimchi verifier: `check_bulletproof` (`equal_g`, the `scale_fast` of `sg`, the IPA fold) and
     `group_map`. Those are #3 and #5's named-and-not-assembled list — TWO items shorter on
     2026-08-02, because `sponge_after_index` over the actual plonk index is now §3c and the
     `x_hat` / `ft_comm` commitment MSMs over REAL commitments are R3 and §6b. Deriving the bit from anything
     less would be a value that LOOKS derived; the honest state is the witness plus this sentence.
     ⚑ **AND SINCE §17 THE PRICE OF DERIVING IT IS MEASURED, not estimated — and it is NOT a refusal.**
     `equal_g lhs rhs` (`:340`) compares `lhs = c·q + δ` with `rhs = z₁·(G + b·u) + z₂·H`. Of those,
     `q`/`c`/`δ` are bound (R1/R4/§7b), `b` is R8's statement word, `u = group_map (squeeze)` is
     DERIVABLE (§17 derives it, against `groupmap`'s own Rust output) and `H = Generators.h` is
     PINNABLE (§17 measures it off `SRS::<Pallas>::create`) — but `G`, `z₁` and `z₂` are FREE
     WITNESSES with no other occurrence in `step_verifier.ml`. §17 exhibits the consequence on this
     assembly's numbers: the honest opening closes, the on-curve-substituted assembly with the same
     `G` is REFUSED, and the same substitution with `G` re-solved (one `Fq` inverse, three scalar
     multiplications — no discrete log) is ACCEPTED. So assembling `equal_g` would make `verified` a
     function of the transcript instead of a free bit, and would refuse NO commitment substitution.
     ⚠ ⚑ **AND `G`'s BINDER IS NOW ASSEMBLED — AND IT DID NOT REFUSE IT EITHER (2026-08-02, §8e′,
     §17(d)–(g)).** The OUTER `hash_messages_for_next_step_proof` (`step_main.ml:525-566`) over
     `acc.wrap_proof.opening.challenge_polynomial_commitment` is segment D, and its squeeze IS the
     step statement's public `messages_for_next_step_proof` (`:572-575`). Measured on the emitted
     object: a re-solved `G` MOVES that public word (§17(d)) — and the substituted witness is still
     ACCEPTED (§17(e)), because nothing here relates `G` to `lhs`. The prior wording, "with that
     assembled … the public-vector tie refuses it", was WRONG: the tie exposes the digest, it does
     not compare it against an independently known one. That comparison is the NEXT step's
     `verify_one` — segment C's reconstruction plus the wrap-proof tie (`step_main.ml:83-86,108`) —
     which is outside this circuit by construction. So `G` is bound to the STATEMENT and not to the
     OPENING, and `verified` is still a witness. ⚠ And even with `G` fixed, `z₁`/`z₂` leave a
     two-dimensional discrete log in `⟨G + b·u, H⟩` — the IPA opening's own hardness, an ASSUMPTION
     and not a gate, and it must be described as one.
     ⚠ ⚑⚑ **AND THAT CONSUMER IS NOW BUILT, AND IT ACCEPTS IT TOO (2026-08-02, §18).** The sentence
     above — "that comparison is the NEXT step's `verify_one` … outside this circuit by
     construction" — was a description of where the refusal LIVES, and it was wrong about what lives
     there. §18 assembles the chain: step `N+1`'s segment C reconstruction reproduces step `N`'s
     public word 7 on the honest chain (§18(a)) AND on the substituted one (§18(b)). The tie FORCES
     `sg_old` at `N+1` to be the `G` used at `N` — the fake commitment must be carried, which §18(d)
     measures as a refusal in that direction — and then the substituted chain proceeds. **The actual
     refusal is the accumulator check** (`per_proof_witness.ml:12-32`): `sg_old` must OPEN at ζ to
     `f_c(ζ)` over `prev_challenges`. ⚑ Its `E_c = f_c(ζ)` leg is #4's residue and is COMPUTED since
     2026-08-02 (§8i, §18(f)) — and `combine`'s mask mux is emitted too (§12l), so BOTH of `combine`'s
     `sg_evals` residues are closed; its OPENING leg is THIS entry and is untouched by either. So the honest one-line state of `verified` is: it is
     the last thing standing between a substituted commitment and acceptance, **at every step of the
     recursion and not only at this one**, and it is an ASSUMPTION until a sub-circuit that does not
     exist is built.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate list, the coefficients, the cross-gate placement and
the composed witness grid are authored in Lean. `proof-systems` (tag 0.3.0) is the Rust PROVER that
RUNS the artifact and authors no constraint. House Law #1. No OCaml, no Node, no o1js in this path.
The `Poseidon`/`VarBaseMul`/`EndoMul`/`EndoMulScalar`/`CompleteAdd`/`Generic` constraint polynomials
are proof-systems' fixed gate semantics, transcribed read-only in `KimchiVerify`; the `#guard`s below
evaluate them against the ASSEMBLED GRID, not against intermediate Lean lists.

## Axiom hygiene / build

NO `main` (roots cleanly into `PicklesSynthesis`; the emit driver is `EmitStepMainJson.lean`).
`#guard`s reduce in the interpreter; no `sorry`/`native_decide`, no `decide` over the big grid.

## ⚑ THE SPLIT (2026-08-02) — and the measurement that forced its shape

This module is an UMBRELLA. `import Dregg2.Circuit.Emit.KimchiStepMain` still brings in every name,
unchanged; the map is below the docstring.

**Why it was split.** One `lake env lean` over the 8,900-line monolith ran 15-20 min and every lane
touching the assembly serialised on it. MEASURED here, on this file:

  * §1-§11 — all 686 declarations, zero guards — elaborate in **11 s**. The definitions were never
    the cost.
  * the **838 `#guard`s** are ~100% of the rest: the profiler attributes the whole of it to
    `interpretation`, at **~1.4 s per pin** (§12 alone: 77 pins, 106 s of user CPU).
  * ⚠ **and a nullary `def` is NOT cached across `#guard` COMMANDS** — which is what §12's banner
    used to claim. Ten separate `#guard`s over one imported nullary constant cost ten evaluations
    (3.2 s vs 0.37 s for one); ten conjuncts of the SAME constant inside ONE `#guard` cost one
    (0.38 s). Sharing is per-command, so `tS`/`placedS`/`witS` are rebuilt once per pin and no
    amount of hoisting into constants removes that work.

So the work is irreducible without batching pins into shared commands — which would cost each pin its
own failure site — and the lever taken instead is PARALLELISM: thirteen pin modules that depend on
`…Fixture` and on nothing else, so `lake build` runs them concurrently.

## ⚑ CARRY-FORWARD FOR WHOEVER ADDS ROWS NEXT — corrections, not tasks

Relayed from the lane that priced item 1 on 2026-08-02 and did not land it. Only the last of these
was re-checked here at source; the rest are recorded so the next lane does not re-derive them, and
each should be confirmed before it is built on.

  * `Evals.validate_feature_flags` and `actual_evaluation`'s chunk Horner emit **ZERO rows** —
    retired, do not carry them forward.
  * `to_field_checked` widths in the STEP path are only **128 and 16** (not 16/32/64/192/256); the
    single missing one is 16, on `branch_data`.
  * `Rounds.Wrap = Nat.N15`, so the bulletproof-challenge run is **15, not 16**, and `Features`
    carries **8 bools, not 9** — two compensating errors that both had to be wrong for the census to
    sum to 40.
  * Item 1 is **four ladders, not three** — ⚑ **LANDED 2026-08-03 as §19, and it MEASURES 482 rows**
    (`r8_finalize` 3391 → `r9_opening` 3873 at the smoke shape, plus 2 rows in R4 for the
    `q = p_prime + lr_prod` add). Our `q` HAD no `uc` term; it has one now, so
    `combined_inner_product` reaches the IPA side and hence `lhs`.
    ⚑ **WHAT IT BOUGHT, AND IT IS ONE THING**: R8's `verified` (#11) was `AOp.wit 1` — a cell no row
    defined, which `Boolean.all` then forced to 1. It is now `equal_g`'s output cell, and R8's
    `.wit` census drops **10 → 9** (§16 pins it).
    ⚠ **WHAT IT DID NOT BUY**: `equal_g` refuses no on-curve substitution. The honest witness this
    file emits SOLVES `G` off `lhs`; §19's `substituted_assembly_still_closes_equal_g` re-runs
    §17(e)/§18(b) on the EMITTED circuit and the verdict is **ACCEPTED**, unchanged.
  * `group_map` is **~30 rows, not ~13** (an indicator dot-product, not a `Field.if_` chain). ⚑ As
    EMITTED it is **23 rows** — 44 `Generic` halves packed two to a row, plus a probe. §19 states
    where that is an UPPER bound on Snarky's count: this emission materialises every linear
    combination that feeds a multiplication, where `assert_r1cs` takes lincoms as operands.
  * ⚠ **`step-zkapp-proved` is the WRONG conformance branch**: its prev is `side_loaded 0`, hence
    `public_input_commitment_dynamic`. This assembly is the `Known` shape (`merge`/`base`).
  * ⚠ **§17's exhibit was wrong at source — CORRECTED 2026-08-03**: `bpUOf` was
    `gmapFp (chalOf …)`, and `chalOf` is `state % 2 ^ chalBits` — the LOW 128 bits (`hiOf` holds the
    rest). `step_verifier.ml:264` squeezes the FULL field element into `group_map`. `bpUOf` now
    reads `uSqueezeVal`, §19 emits `group_map` over `uSqueezeVar`, and
    `u_squeeze_is_the_full_element_not_the_low_128` pins that the two arguments and the two `u`
    points differ.

-/

-- ⚑ SPLIT 2026-08-02 — this file is now an UMBRELLA. `import Dregg2.Circuit.Emit.KimchiStepMain`
-- still brings in every name, unchanged. Where things went:
--   …Field    — the Fp/Pallas value layer (Tonelli–Shanks, `group_map`, `Generators.h`, `bpK`)
--   …Core     — §1–§11, the emission proper (defs only)
--   …Fixture  — every value §12–§18's pins are stated about (defs only)
--   …Pins01   — §12   (77 guards)
--   …Pins02   — §12a §12b §12i   (74 guards)
--   …Pins03   — §12j §12b′   (76 guards)
--   …Pins04   — §12c §12c′ §12d   (71 guards)
--   …Pins05   — §12e   (62 guards)
--   …Pins06   — §12e′ §12f §12g   (74 guards)
--   …Pins07   — §13 §14   (57 guards)
--   …Pins08   — §14a   (72 guards)
--   …Pins09   — §12k §12l   (42 guards)
--   …Pins10   — §15   (73 guards)
--   …Pins11   — §16   (50 guards)
--   …Pins12   — §17   (46 guards)
--   …Pins13   — §18   (63 guards)
--   …Pins14   — §19   (NAMED THEOREMS, zero guards — GUARD-DISCIPLINE.md)
-- Add a def to …Fixture (or …Core), add a `#guard` to the …PinsNN of its section.

import Dregg2.Circuit.Emit.KimchiStepMainField
import Dregg2.Circuit.Emit.KimchiStepMainCore
import Dregg2.Circuit.Emit.KimchiStepMainFixture
import Dregg2.Circuit.Emit.KimchiStepMainPins01
import Dregg2.Circuit.Emit.KimchiStepMainPins02
import Dregg2.Circuit.Emit.KimchiStepMainPins03
import Dregg2.Circuit.Emit.KimchiStepMainPins04
import Dregg2.Circuit.Emit.KimchiStepMainPins05
import Dregg2.Circuit.Emit.KimchiStepMainPins06
import Dregg2.Circuit.Emit.KimchiStepMainPins07
import Dregg2.Circuit.Emit.KimchiStepMainPins08
import Dregg2.Circuit.Emit.KimchiStepMainPins09
import Dregg2.Circuit.Emit.KimchiStepMainPins10
import Dregg2.Circuit.Emit.KimchiStepMainPins11
import Dregg2.Circuit.Emit.KimchiStepMainPins12
import Dregg2.Circuit.Emit.KimchiStepMainPins13
import Dregg2.Circuit.Emit.KimchiStepMainPins14
import Dregg2.Circuit.Emit.KimchiStepMainPins15
import Dregg2.Circuit.Emit.KimchiStepMainPins16
import Dregg2.Circuit.Emit.KimchiStepMainPins17
import Dregg2.Circuit.Emit.KimchiStepMainPins18
-- ⚑ §19b — the block's own IPA opening is ON DISK and does not close this assembly's transcript.
-- Imported here rather than left orphaned: a pin module nobody reaches asserts nothing.
import Dregg2.Circuit.Emit.KimchiStepMainPins19
import Dregg2.Circuit.Emit.KimchiStepStatementPins
