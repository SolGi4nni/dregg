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
  * **R3 `msm`** — TWO MSMs. `multiscale_known`, the x_hat MSM: `msmTerms` `var_base_mul` scalar
    multiplications
    of `msmChunks` 5-bit chunks (`bits_per_chunk = 5`, `plonk_curve_ops.ml:66`), summed by a
    `complete_add` chain. ⚑ Each term's scalar counter chain CLOSES ON ITS CHALLENGE: term `i`'s
    final `n'` cell (col 5) and its challenge's final `n₈` cell (col 1) are the SAME VARIABLE, so
    the value `EndoMulScalar` decoded is the value `VarBaseMul` multiplies by — one σ class spanning
    three gate types and three sub-circuits.
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
  * **R5 `deferred` + `xi` + `cip` + `closing`** — two of `finalize_other_proof`'s deferred words:
    `b(ζ) = ∏(1 + uᵢ·ζ^{2^{k−1−i}})` (`Wrap.challenge_polynomial`, `wrap.ml:15-17`; the product
    `KimchiVerify.bEvalSq` folds) and `combined_inner_product = Σ_k ξ^k·(evₖ(ζ) + r·evₖ(ζω))`
    (`Common.combined_evaluation`, the `2 × cipEvals` `mul_and_add`s; pinned against
    `KimchiVerify.combinedInnerProduct`, transcribed READ-ONLY from `verifier.rs`) — both as
    `Generic` chains over the CHALLENGE variables. ⚑ Its ξ is §8g's chain 0: a full
    `to_field_checked` of the STATEMENT's ξ word (`let xi = scalar xi`, `step_verifier.ml:1012`),
    the word R8's `xi_correct` ties to the fr-sponge. ⚑ It also unpacks §8h's `branch_data` — the
    two `proofs_verified_mask` bits R7's opt-sponge muxes with. Then the closing tie of every one of the
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
PI 67, 20,023 gates, 13,778 non-Generic. Measured against this file's `shapeStep` (2026-08-02):

    gate         Mina step-zkapp-proved  r5_full  r6_ft_eval0  r7_absorb  r8_finalize  run-lengths
    total gates         20023              8362      8831       10508       10601
    non-Generic         13778              7595      7597        8981        8999
    Poseidon             6292 (31.4%)       902       902        2145        2145   11×572 / 11×195 ✓
    Generic              6245 (31.2%)       767      1234        1527        1602   —
    EndoMul              2465 (12.3%)      2464      2464        2464        2464   32×77+1×1 / 32×77 ✓
    Zero                 2246 (11.2%)      2062      2064        2189        2200   —
    VarBaseMul           1596  (8.0%)      1448      1448        1448        1448   1×1596 / 1×1448   ✓
    EndoMulScalar         776  (3.9%)       376       376         392         408   8×28 / 8×51 ✓
                    upstream also runs 2×42 4×25 16×3 1×2 12×2 32×2 9×1 19×1 22×1 24×1 28×1 128×1
    CompleteAdd           403  (2.0%)       334       334         334         334   1×159 2×65 3×23
                    15×1 30×1 / 1×334

⚑ MOVEMENT SINCE THE PREVIOUS COMMIT (10554 → 10601 rows, +47) — **and the headline is that R1 now
FEEDS THE SPONGE IN `verify_one`'S OWN ORDER, which is what closed the last three absorptions.**
The +47 is small and it is the whole point: what landed is not scale, it is the schedule.

  * ⚑ **R1 INTERLEAVED (§2b).** Absorb blocks and squeezes now sit where
    `incrementally_verify_proof` puts them, and the absorb ORDER is upstream's rather than the
    `ipaAbsorbs` filter's (which had `z_comm` ahead of `w_comm` and the gammas ahead of `t_comm`).
    **Zero rows** — `absorbs` is still 59 and `chals` still 23; only the order moved. Every
    challenge VALUE moved with it, and with them every ladder the challenges drive.
  * ⚑ **`sg_old[0]` CLOSED: +1 `CompleteAdd`, +2 `Zero`, +2 on-curve halves.**
    `combine_split_commitments`' `~init` (`step_verifier.ml:606`) — the fold chain starts at
    commitment 0, so `ipaRounds` adds instead of `ipaRounds − 1`.
  * ⚑ **`combined_inner_product` CLOSED: +1 `Generic`, +1 `Zero`.** One `Boolean.typ` check for the
    bit; the FIELD half is `vCipShift`, which R8 already binds. The absorption itself costs no block
    — block `oCip` was one of the three that carried a `msgVal` fixture.
  * ⚑ **`delta` CLOSED: +32 `EndoMul`, +3 `CompleteAdd`, +1 `Generic`, +8 `Zero`.**
    `check_bulletproof`'s `lhs = Scalar_challenge.endo q c + delta` (`:325-327`) — one 32-block endo
    ladder over the fold output at the LAST squeeze, seeded like every other, plus the closing add.

⚑ **AND THE 77th ENDO BLOCK IS UPSTREAM'S OWN.** `EndoMul` 2432 → **2464 against Mina's 2465**, and
the run-length family goes `32×76` → **`32×77`**, which is exactly Mina's `32×77 1×1`. The region
conformance script's `ipa` anchor had already measured the split as `combine_split_commitments 46 |
bullet_reduce 30 | check_bulletproof 1` and was comparing only the first two against our 76; the
block we were missing was the one `delta` needed. `VarBaseMul` 1448, `EndoMulScalar` 408 and
`Poseidon` 2145 are unchanged to the row — no other sub-circuit moved.
(The two commits before these took 10342 → 10554 on the three ladder seeds and the absorb-shape
correction; before that 9431 → 10342 on §6b's `ft_comm` MSM; before that 9417 → 9431 on §3c's
`sponge_after_index`; before that 9317 → 9417 on #1's third `lowest_128_bits` and §7b's
`assert_on_curve`.)

The RUN LENGTHS are the fidelity signal, and all FIVE families the shape-diff compares are INTACT
(⚠ the prior header said "six"; `stepmain-shape-diff.mjs` prints run lengths for `Poseidon`,
`EndoMul`, `EndoMulScalar`, `VarBaseMul`, `CompleteAdd` and no others): a `Poseidon` permutation is
11 rows (195 of them, upstream 572), a 128-bit `Scalar_challenge.endo` is 32 `EndoMul` rows, a
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
    r1_transcript    1069     2048             752 ms              24
    r2_challenges    1714     2048             734 ms             116
    r3_msm           4917     8192            1027 ms             221
    r4_ipa           8110     8192             979 ms             452
    r5_full          8362    16384            1180 ms             459
    r6_ft_eval0      8831    16384            1224 ms             461
    r7_absorption   10508    16384            1247 ms             473
    r8_finalize     10601    16384            1242 ms             480

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

The remaining `Generic` gap (1602 vs 6245) is therefore NOT one missing sub-circuit. It is: the zkApp
branch's own `rule.main` application logic (which is not `verify_one` at all), the `sg_evals` prefix
of the two `combine`s (#4), `equal_g`, `group_map`, `x_hat blinding` and the domain selection —
`ft_comm`'s own MSM LEFT this list on 2026-08-02 (§6b). #2–#11 below name the rest. ⚑ R8 spends 70 `Generic` rows on `finalize_other_proof`'s
tail. That is the trade this file is supposed to be making: every commit here should be buying a
named simplification, not scale.

⚑ Likewise `Poseidon` (2145 vs 6292): R7 brings the count to 195 permutations, the last of which is
`sponge_after_index`'s squeeze — TWELVE fewer than the previous rung, and the twelve are the absorb
blocks the shape correction deleted. `verify_one`'s own sponge work is now assembled; the remaining
377 permutations are the app logic and `group_map` (#5).

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

So: the sponge input is derived for the verifier key and for the quotient commitment, both MSM
ladders and every endo ladder start where upstream starts them, the blocks are fed in upstream's
order, and every item `verify_one` absorbs is a word some row here READS. What is left of the
transcript residue is one structural pad lane.

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
  2. ⚑ **CORRECTED AT SOURCE 2026-08-02, AND THE NAMED FIX WAS WRONG.** This entry read: "All MSM
     scalars are assembled at the 128-bit width… **the 255-bit width is expressible with
     `msmChunks = 51`**; taking it costs ~1000 `VarBaseMul` rows." Widening R3 uniformly to 51
     would be LESS faithful, not more, and reading `multiscale_known`'s argument at source is what
     says so — the same shape as #3, whose bases turned out to have two provenances.

     `multiscale_known`'s scalars are not challenges and are not one width. They are the previous
     proof's **packed Wrap STATEMENT** — `multiscale_known (Array.mapi public_input ~f:(fun i x ->
     (x, lagrange_commitment ~domain srs i)))` (`step_verifier.ml:543-544`), where `public_input` is
     `Spec.pack … (Types.Wrap.Statement.In_circuit.spec …) (… to_data statement)`
     (`:1236-1251`). `Spec.pack` carries a width PER BASIC (`spec.ml:376-392`): `Field` and `Digest`
     pack as `Field.size_in_bits = 255`, `Challenge` and `Bulletproof_challenge` as
     `Challenge.length = 64·2 = 128` (`limb_vector/challenge.ml:5`, `constant.ml:71`), `Branch_data`
     as `length_in_bits = 10` (`branch_data.ml:61`), `Bool` as 1 — and `multiscale_known` scales
     each by `~num_bits:n` (`:164-172`), at `chunks_needed ~num_bits:(n−1)` 5-bit chunks
     (`plonk_curve_ops.ml:66-68,250-252`). MEASURED off the spec and `to_data`
     (`composition_types.ml:812-825,855-882`), the 40 words are:

         i      word(s)                                            basic                 bits chunks
         0–4    combined_inner_product, b, ζ^srs_len, ζ^dom, perm  Field                  255     51
         5–6    beta, gamma                                        Challenge              128     26
         7–9    alpha, zeta, xi                                    Scalar Challenge       128     26
         10–12  sponge_digest_before_evals, msgs_next_wrap/step    Digest                 255     51
         13–28  bulletproof_challenges ×16                         Bulletproof_challenge  128     26
         29     branch_data                                        Branch_data             10      2
         30–38  8 feature flags + the lookup Opt flag              Bool                     1      0
         39     the lookup Opt's own challenge                     Scalar Challenge       128     26

     — which is **40**, i.e. the devnet Wrap VK's `public = 40` is this list, word for word, and
     `msmTerms = 40` was right for a reason nobody had checked. Only **8 of the 40 are 255-bit**;
     22 are 128 and one is 10. A uniform 51 would emit 25 chunks of LEADING ZEROS on every
     challenge-shaped word. Total in-circuit chunks are `8·51 + 22·26 + 2 = 982` against the 1040
     assembled here, so the honest move is not even a widening.
     ⚑ **AND IT IS THE SAME ITEM AS #3's SCALAR RESIDUE.** A 255-bit width over a value that is
     structurally `< 2¹²⁸` is shape-faithful and semantically empty, so the width can only be taken
     together with the provenance: term `i`'s scalar must BE Wrap statement word `i`. The assembly
     already holds every one of them (`vCipShift`/`vBShift`/`vPermShift`, R6's `ζ^n`, R1's sponge
     digest, `hmDigestVar`, the transcript prechallenges, `vXiStmt`, `vBranch`) — what is undone is
     R3's uniform `msmChunks` becoming a per-word vector (cumulative point offsets in §2, per-term
     bit lists in §6) and `vSN i (chunks i)` being wired to the statement word instead of to
     `vN (msmChal i) emsRows`. That is the retirement; nothing less is one.
     ⚠ `ft_comm`'s 8 `scale_fast2`s ARE uniformly 255 (`step_verifier.ml:240-242`), and since
     2026-08-02 they are ASSEMBLED at that width — §6b, `FTC_CHUNKS = 51`. That is a SECOND
     `VarBaseMul` region with its own chunk count, which is why `msmChunks` stays 26: the two MSMs
     have genuinely different scalar widths and collapsing them would be wrong in both directions.
     R3's own per-word width vector remains this entry's residue.
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
     ⚠ THE RESIDUE THAT REMAINS: `multiscale_known`'s SCALARS are upstream's PUBLIC INPUT words;
     here they are still the circuit's own derived challenges. #2 now carries that, because reading
     `Spec.pack` at source made it the SAME item as the widths.
  4. ⚑ **RETIRED 2026-08-02, and the ORIGINAL CLAIM WAS WRONG.** This entry read "`combined_inner_
     product` is HALF of upstream's — R5 assembles ONE ξ-Horner fold (at ζ)". READ AT SOURCE, R5's
     `cipRows` folds `cₖ = evₖ(ζ) + r·evₖ(ζω)` and then Horners over ξ, i.e.
     `Σₖ ξᵏ(ez_k + r·ew_k)` — which IS `combine(ζ) + r·combine(ζω)` term-for-term, and IS
     `KimchiVerify.cipR`'s own body. The r-weighted second fold was never absent; it was folded per
     COLUMN instead of per POINT. What WAS absent is now R8: `b_correct`'s `+ r·challenge_poly ζω`
     leg and the `Shifted_value.Type1.to_field` unshifts. **Still open:** the `sg_evals` prefix
     entries (`vEz 0/1`, `vEw 0/1`) are `evVal` fixtures where upstream puts the b-polynomial of the
     CARRIED old bulletproof challenges, masked by `Vector.trim_front actual_width_mask` — so the
     two `combine`s' first two v-entries are not yet computed from the carried challenges. ⚑ The
     mask half of that is no longer missing (§8h, #9 below); what remains is the b-polynomial of the
     carried challenges at ζ and ζω, which is R5's `deferredRows` ladder run on a SECOND challenge
     vector.
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
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.KimchiRenderPoseidon
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderPublicInput
import Dregg2.Circuit.Emit.KimchiComposeStepFragment
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Bridge.MinaWrapFtEval0
import Dregg2.Bridge.TickShifts
import Dregg2.Bridge.MinaStepPrevCommitments

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (cFuncFp dFuncFp)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment
  (TermData EndoBlock runVbm endoStep dblA addA onCurveA jOf jDbl jAdd jNeg)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints endomulScalarConstraints)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)
open Dregg2.Bridge.MinaWrapFtEval0 (IDX_Z IDX_SEL IDX_W IDX_COEFF IDX_S)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — the shape. -/

/-- The assembly's size. Every field is a quantity upstream fixes; the committed instance in §10
sets them against the `verify_one` line items in the header. -/
structure StepShape where
  /-- transcript absorb blocks; each swallows TWO field elements (`rate = 2`). -/
  absorbs : Nat
  /-- squeezed scalar challenges (one permutation each). -/
  chals : Nat
  /-- `EndoMulScalar` rows per challenge; each eats 8 crumbs = 16 bits (`bits_per_row = 16`). -/
  emsRows : Nat
  /-- `var_base_mul` terms in the commitment MSM. -/
  msmTerms : Nat
  /-- 5-bit chunks per MSM term (`bits_per_chunk = 5`); `26` is upstream's 128-bit `scale_fast2`. -/
  msmChunks : Nat
  /-- `Scalar_challenge.endo` scalar multiplications in the IPA/commitment fold. -/
  ipaRounds : Nat
  /-- 4-bit `endo_mul` blocks per round (`32` is upstream's 128-bit `endo`). -/
  ipaBlocks : Nat
  /-- rounds of the deferred `b(ζ)` product (`Step_bp_vec = N16`). -/
  bRounds : Nat
  /-- evaluation columns folded by `combined_inner_product`
  (`NUM_COMMITMENTS_WITHOUT_DEGREE_BOUND = N45`, + `sg_old` padding = 47). -/
  cipEvals : Nat
  /-- ⚑ `t_comm`'s quotient chunks this shape absorbs (`N_TCOMM = 7` upstream). A FIELD since the
  R1 interleaving: `absorbs` is now DERIVED from the schedule, so sizing `t_comm` off `absorbs`
  would be circular. -/
  tComms : Nat
  /-- the public-input width (`PRIMARY_LEN`). -/
  pubWords : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Sponge blocks = absorb blocks then squeeze blocks. -/
def StepShape.blocks (s : StepShape) : Nat := s.absorbs + s.chals
/-- Bits a challenge carries (`emsRows` rows × 8 crumbs × 2 bits). -/
def StepShape.chalBits (s : StepShape) : Nat := 16 * s.emsRows
/-- Which challenge MSM term `i` consumes (upstream re-uses ξ across the fold, so sharing is the
faithful shape and it merges the two chains' final counter cells into ONE σ class). -/
def StepShape.msmChal (s : StepShape) (i : Nat) : Nat := i % s.chals
/-- Which challenge IPA round `r` consumes. -/
def StepShape.ipaChal (s : StepShape) (r : Nat) : Nat := (s.msmTerms + r) % s.chals

/-! ## §2 — the variable space.

Public words are `external 0 .. pubWords-1` (Snarky's own numbering, which `place` reproduces). The
circuit's OWN variables start at `AUX`, so `placeChecked`'s H1 (silent public/aux absorption) cannot
fire and its H2 (an inert public word) is the real gate on the closing rung. Ids are laid out in
disjoint REGIONS whose bases are functions of the shape; §9 pins the distinct-variable count, so a
collision (which MERGES two σ classes and shrinks the count) goes red. -/

/-- The lowest `external` id the circuit allocates for itself; equals `PRIMARY_LEN` for the committed
shape, so `placeChecked`'s dead gap `pubWords ≤ i < AUX` is empty. -/
def AUX : Nat := 67

/-- Circuit variable `k`. -/
def xv (k : Nat) : PVar := .external (AUX + k)

/-- Sponge state lane `j` entering block `b` (`b = 0..blocks`). -/
def vSt (_s : StepShape) (b j : Nat) : PVar := xv (3 * b + j)
def nSt (s : StepShape) : Nat := 3 * (s.blocks + 1)

/-- Post-absorb lane `j ∈ {0,1}` of absorb block `b`. -/
def vPost (s : StepShape) (b j : Nat) : PVar := xv (nSt s + 2 * b + j)
/-- The transcript word absorbed at lane `j` of block `b`. -/
def vMsg (s : StepShape) (b j : Nat) : PVar := xv (nSt s + 2 * s.absorbs + 2 * b + j)

def baseN (s : StepShape) : Nat := nSt s + 4 * s.absorbs
/-- Challenge `c`'s `n` accumulator after `k` `EndoMulScalar` rows. `vN c emsRows` is THE CHALLENGE
VALUE — the variable three gate types share. -/
def vN (s : StepShape) (c k : Nat) : PVar := xv (baseN s + c * (s.emsRows + 1) + k)
def nN (s : StepShape) : Nat := s.chals * (s.emsRows + 1)
def baseA (s : StepShape) : Nat := baseN s + nN s
def vA (s : StepShape) (c k : Nat) : PVar := xv (baseA s + c * (s.emsRows + 1) + k)
def baseB (s : StepShape) : Nat := baseA s + nN s
def vB (s : StepShape) (c k : Nat) : PVar := xv (baseB s + c * (s.emsRows + 1) + k)
def baseHi (s : StepShape) : Nat := baseB s + nN s
/-- The high part of challenge `c`'s squeeze decomposition. -/
def vHi (s : StepShape) (c : Nat) : PVar := xv (baseHi s + c)

/-! ### The `to_field_checked` OUTPUT (`scalar_challenge.ml:125-129`).

`to_field_checked` is the `EndoMulScalar` chain, then `Field.Assert.equal n scalar`, then
**`Field.(scale a endo + b)`** — the endomorphism LIFT of the prechallenge. R2 emitted the first two
and stopped; these are the variables of the third, so `vLift c` IS `ScalarChallenge::to_field`
(`KimchiVerify.endoMap ENDO_R`) of the squeeze and the chain's `a₈`/`b₈` cells become load-bearing
rather than merely constrained. -/
def baseLift (s : StepShape) : Nat := baseHi s + s.chals
/-- `a₈ · endo_r` — the lift's product half. -/
def vLiftT (s : StepShape) (c : Nat) : PVar := xv (baseLift s + c)
/-- ⚑ **The LIFTED challenge** `a₈·endo_r + b₈`. This is what `plonk.zeta`/`plonk.alpha`, the
deferred `ξ`/`r` and every bulletproof challenge ARE upstream; the raw `vN c emsRows` is the
prechallenge the curve gadgets consume. -/
def vLift (s : StepShape) (c : Nat) : PVar := xv (baseLift s + s.chals + c)
/-- `Endo.Wrap_inner_curve.scalar`, pinned by one `Generic` row and shared by every lift. -/
def vEndoR (s : StepShape) : PVar := xv (baseLift s + 2 * s.chals)

def baseMsm (s : StepShape) : Nat := baseLift s + 2 * s.chals + 1
def mpx (s : StepShape) (p : Nat) : PVar := xv (baseMsm s + 2 * p)
def mpy (s : StepShape) (p : Nat) : PVar := xv (baseMsm s + 2 * p + 1)
/-- MSM term `i`'s base point. -/
def pT (s : StepShape) (i : Nat) : Nat := i * (s.msmChunks + 2)
/-- MSM term `i`'s accumulator at chunk boundary `j` (`j = 0..msmChunks`). -/
def pAcc (s : StepShape) (i j : Nat) : Nat := i * (s.msmChunks + 2) + 1 + j
/-- The running MSM sum after add `a`. -/
def pSum (s : StepShape) (a : Nat) : Nat := s.msmTerms * (s.msmChunks + 2) + a
def nMsmPts (s : StepShape) : Nat := s.msmTerms * (s.msmChunks + 2) + s.msmTerms

def baseSN (s : StepShape) : Nat := baseMsm s + 2 * nMsmPts s
/-- MSM term `i`'s scalar counter at chunk boundary `j`. At `j = msmChunks` it IS the term's
challenge variable — the cross-sub-circuit wire. -/
def vSN (s : StepShape) (i j : Nat) : PVar :=
  if j == s.msmChunks then vN s (s.msmChal i) s.emsRows else xv (baseSN s + i * s.msmChunks + j)

/-- `Nat.N45` + `Wrap_hack`'s two `sg_old` slots — `combine_split_commitments`' commitment count. -/
def N_WDB : Nat := 47
/-- `bullet_reduce`'s fifteen `absorb (PC :: PC) gammas_i` (`step_verifier.ml:199`) — every fold
round past `combine_split_commitments`'. TWO transcript blocks each, then one `squeeze_scalar`. -/
def gamRounds (s : StepShape) : List Nat :=
  (List.range s.ipaRounds).filter (fun r => N_WDB ≤ r + 1)
/-- ⚑ The transcript squeezes upstream takes at SCHEDULED positions (§2b): β, γ, α, ζ, `u`, one per
`bullet_reduce` round, and `c`. **21** at the committed shape; `chals − 21` is what this file still
takes off the transcript that upstream takes off the fr-sponge (ξ and r, §8g). -/
def sqScheduled (s : StepShape) : Nat := 6 + (gamRounds s).length / 2
-- ⚑ THE SCHEDULE'S OWN ORDER since the R1 interleaving (`step_verifier.ml:563-568`): β then γ then
-- α then ζ, squeezes 0..3. They were `ζ,α,β,γ = 0,1,2,3` when R1 had no schedule and the numbering
-- was arbitrary. ⚑ These four are ALL squeezed BEFORE `combined_inner_product` is absorbed (`:256`),
-- which is the whole reason `cip` can be a transcript word at all — §12i pins it.
def StepShape.betaChal (_s : StepShape) : Nat := 0
def StepShape.gammaChal (_s : StepShape) : Nat := 1
def StepShape.alphaChal (_s : StepShape) : Nat := 2
def StepShape.zetaChal (_s : StepShape) : Nat := 3
/-- ⚑ `c = squeeze_scalar sponge` (`:322`) — the LAST scheduled transcript squeeze, and the scalar
`lhs = Scalar_challenge.endo q c + delta` multiplies the fold output by. -/
def StepShape.cChal (s : StepShape) : Nat := sqScheduled s - 1
/-- ⚑ The `bRounds` challenges `b(ζ) = ∏(1 + uₖ·ζ^{2^{…}})` folds over. Upstream these are the
previous proof's `bulletproof_challenges` (`step_verifier.ml:937-938,1124-1128`); this file still
takes them off the transcript (the round-robin sharing #4 names), and takes them from the squeezes
AFTER ζ — which at the committed shape ARE `u` and `bullet_reduce`'s fifteen. It was `k + 1` when ζ
was challenge 0; at ζ = 3 that would have made ζ one of its own `uₖ`. -/
def StepShape.uChal (s : StepShape) (k : Nat) : Nat := s.zetaChal + 1 + k

def baseIpa (s : StepShape) : Nat := baseSN s + s.msmTerms * s.msmChunks
def ipx (s : StepShape) (p : Nat) : PVar := xv (baseIpa s + 2 * p)
def ipy (s : StepShape) (p : Nat) : PVar := xv (baseIpa s + 2 * p + 1)
/-- IPA round `r`'s `endo_mul` base point. ⚑ The per-round stride is `ipaBlocks + 3` and not `+ 2`
since 2026-08-02: the third slot is `Scalar_challenge.endo`'s own seed intermediate. -/
def qT (s : StepShape) (r : Nat) : Nat := r * (s.ipaBlocks + 3)
/-- IPA round `r`'s accumulator after `e` blocks (`e = 0..ipaBlocks`). -/
def qAcc (s : StepShape) (r e : Nat) : Nat := r * (s.ipaBlocks + 3) + 1 + e
/-- ⚑ `Scalar_challenge.endo`'s SEED intermediate `p = t + φ(t)` (`scalar_challenge.ml:230-233`:
`let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in ref G.(p + p)`). `qAcc r 0` is `p + p`,
so BOTH are rows and neither is a witness. -/
def qP (s : StepShape) (r : Nat) : Nat := r * (s.ipaBlocks + 3) + s.ipaBlocks + 2
/-- The running IPA fold sum after add `a`. ⚑ `a = 0 .. ipaRounds−1` since the `~init` wiring: the
chain STARTS at commitment 0 (`sg_old[0]`, `qInit`) and folds in every round's output, so there is
one add per round and `qSum (ipaRounds−1)` is `combined_polynomial`. It was `ipaRounds − 1` adds
starting at round 0's output, i.e. `combine_split_commitments` with its `~init` dropped. -/
def qSum (s : StepShape) (a : Nat) : Nat := s.ipaRounds * (s.ipaBlocks + 3) + a
/-- ⚑ **`sg_old[0]`** — `combine_split_commitments`' `~init` accumulator (`step_verifier.ml:606`,
`~init:(function `Finite x -> `Finite x | …)`), whose two coordinates ARE transcript block
`oSgOld0`'s absorbed words. It gets no fold ROUND; it is the point the chain starts at. -/
def qInit (s : StepShape) : Nat := s.ipaRounds * (s.ipaBlocks + 3) + s.ipaRounds
/-- ⚑ `check_bulletproof`'s TAIL (`:325-327`): `lhs = Scalar_challenge.endo q c + delta`, one more
`Scalar_challenge.endo` over the fold output `q` and one `Ops.add_fast` with `delta`. `qLhsP` is the
seed intermediate `p = t + φ(t)`. -/
def qLhsP (s : StepShape) : Nat := qInit s + 1
def qLhsAcc (s : StepShape) (e : Nat) : Nat := qInit s + 2 + e
/-- ⚑ **`delta`** — `absorb sponge PC delta` (`:321`); its two coordinates are transcript block
`oDelta`'s absorbed words and the second operand of the closing `add_fast`. -/
def qDel (s : StepShape) : Nat := qInit s + s.ipaBlocks + 3
/-- `lhs` itself. -/
def qLhsOut (s : StepShape) : Nat := qInit s + s.ipaBlocks + 4
def nIpaPts (s : StepShape) : Nat := s.ipaRounds * (s.ipaBlocks + 3) + s.ipaRounds + s.ipaBlocks + 5

def baseQN (s : StepShape) : Nat := baseIpa s + 2 * nIpaPts s
/-- IPA round `r`'s endo scalar counter after `e` blocks; at `e = ipaBlocks` it IS the round's
challenge variable. -/
def vQN (s : StepShape) (r e : Nat) : PVar :=
  if e == s.ipaBlocks then vN s (s.ipaChal r) s.emsRows
  else xv (baseQN s + r * s.ipaBlocks + e)
/-- ⚑ `Field.scale xt Endo.base` — the endomorphism image's x, the SECOND operand of
`scalar_challenge.ml:232`'s `add_fast`. One `Generic` half per round pins it to `endo·xt`, so the
seed's provenance is the base and a constant rather than a witness. -/
def vQEndo (s : StepShape) (r : Nat) : PVar := xv (baseQN s + s.ipaRounds * s.ipaBlocks + r)
/-- The `c`-endo tail's own counter chain; at `e = ipaBlocks` it IS `c`'s challenge variable, so the
value the ladder multiplies by is the one `to_field_checked` decoded from the LAST squeeze. -/
def vLhsN (s : StepShape) (e : Nat) : PVar :=
  if e == s.ipaBlocks then vN s (sqScheduled s - 1) s.emsRows
  else xv (baseQN s + s.ipaRounds * s.ipaBlocks + s.ipaRounds + e)
/-- …and its seed's `endo·x_q`. -/
def vLhsEndo (s : StepShape) : PVar :=
  xv (baseQN s + s.ipaRounds * s.ipaBlocks + s.ipaRounds + s.ipaBlocks)

/-- ⚑ Upstream's provenance census for `combine_split_commitments`' 47 `without_degree_bound`
commitments, in ITS OWN ORDER (`step_verifier.ml:601-616`); `true` = absorbed into the transcript.

    0,1    sg_old, padded          ABSORBED (`Vector.iter ~f:(absorb sponge PC) sg_old`, :537)
    2      x_hat                   ABSORBED (`absorb sponge PC x_hat`, :559)
    3      ft_comm                 computed from `t_comm` + the VK — NOT assembled (#5), so const
    4      z_comm                  ABSORBED (`receive without z_comm`, :564)
    5..10  generic/psm/complete_add/mul/emul/endomul_scalar     VK CONSTANT
    11..25 w_comm ×15              ABSORBED (`Vector.iter ~f:absorb_g w_comm`, :561)
    26..40 coefficients_comm ×15   VK CONSTANT
    41..46 sigma_comm_init ×6      VK CONSTANT -/
def wdbAbsorbed (i : Nat) : Bool := i ≤ 2 || i == 4 || (11 ≤ i && i < 26)

/-- ⚑ IPA round `r`'s base provenance before block assignment. Rounds `0 .. N_WDB−2` are
`combine_split_commitments`' own — round `r` folds in commitment `r+1`, the accumulator starting at
commitment `0` — and every round past them is a `bullet_reduce` `(L,R)`, all of which are absorbed
(`step_verifier.ml:193`). -/
def ipaAbsorbs (r : Nat) : Bool := if r + 1 < N_WDB then wdbAbsorbed (r + 1) else true

/-- ⚑ The fold rounds the transcript absorbs BEFORE β, in `incrementally_verify_proof`'s own order:
`sg_old[1]` and `x_hat` (`step_verifier.ml:538,560`) and `w_comm ×15` (`:562`) — census commitments
1, 2 and 11..25, i.e. rounds 0, 1 and 10..24. ⚠ Commitment 0 (`sg_old[0]`) is NOT a round at all:
it is where `combine_split_commitments` STARTS its accumulator (`~init`, `:606`). -/
def preRounds (s : StepShape) : List Nat :=
  (List.range s.ipaRounds).filter (fun r => ipaAbsorbs r && r + 1 < N_WDB && r + 1 != 4)
/-- `receive without z_comm` (`:565`) — census commitment 4, round 3, absorbed BETWEEN γ and α. -/
def zRounds (s : StepShape) : List Nat :=
  (List.range s.ipaRounds).filter (fun r => ipaAbsorbs r && r + 1 == 4)

/-- The rounds whose bases the transcript absorbs, IN UPSTREAM'S ABSORPTION ORDER. ⚑ Since the R1
interleaving this is `preRounds ++ zRounds ++ gamRounds` and not the raw `ipaAbsorbs` filter: the
filter puts `z_comm` (round 3) ahead of `w_comm` (rounds 10..24) and the gammas ahead of `t_comm`,
which is NOT the order `verify_one` feeds the sponge, and a sponge is order-sensitive. §12b pins
that the two are the same SET and a different LIST. -/
def absRoundList (s : StepShape) : List Nat :=
  preRounds s ++ zRounds s ++ gamRounds s

/-! ### ⚑ `verify_one`'s SPONGE-ITEM CENSUS — what `absorbs` is supposed to be a count OF.

Read at source and counted item by item, because the number `absorbs` carried until 2026-08-02 was
not a count of anything: it was 71, i.e. `2·71 = 142` field elements, against the **117** sponge
items `verify_one` actually feeds its transcript. Twenty-five words the sponge swallowed corresponded
to nothing upstream absorbs — a SHAPE overshoot that the previous rung's residue note had mistaken
for twenty-five unwired absorptions.

`Sponge.absorb` takes ONE field element per call; `absorb sponge PC p` is
`g1_to_field_elements p` = **two**, and `absorb sponge Scalar (x, b)` is `Field x` then `Bits [b]` =
**two** (`step_verifier.ml:75-84`). At rate 2 the block count is `⌈items/2⌉`. -/

/-- The census, in `incrementally_verify_proof`'s own absorption order. -/
def ABSORB_ITEMS : List (String × Nat) :=
  [ -- `absorb sponge Field index_digest` (`step_verifier.ml:534`) — ONE field element.
    ("index_digest", 1)
    -- `Vector.iter ~f:(absorb sponge PC) sg_old` (`:538`) over `Wrap_hack.Checked.pad_commitments`,
    -- `Padded_length = Nat.N2` (`wrap_hack.ml:24,28`): TWO points.
  , ("sg_old, padded ×2", 4)
    -- `absorb sponge PC x_hat` (`:560`).
  , ("x_hat", 2)
    -- `Vector.iter ~f:absorb_g w_comm` (`:562`), `Plonk_types.Columns = 15`.
  , ("w_comm ×15", 30)
    -- `receive without z_comm` (`:565`).
  , ("z_comm", 2)
    -- `receive without t_comm` (`:567`), `Commitment_lengths.create ~t:(of_int 7)`
    -- (`commitment_lengths.ml:6-11`).
  , ("t_comm ×7", 14)
    -- `absorb sponge Scalar advice.combined_inner_product` (`:256-259`) — `Other_field.t` is
    -- `(Field.t, Boolean.var)`, so `absorb_scalar` emits field THEN bit (`:79-81`).
  , ("combined_inner_product, field+bit", 2)
    -- `bullet_reduce`'s `absorb (PC :: PC) gammas_i` (`:199`) over 15 `(L,R)` pairs.
  , ("bullet_reduce (L,R) ×15", 60)
    -- `absorb sponge PC delta` (`:321`).
  , ("delta", 2) ]
/-- **117.** -/
def N_ABSORB_ITEMS : Nat := (ABSORB_ITEMS.map (·.2)).foldl (· + ·) 0

/-- ⚑ The absorptions `verify_one` performs that this file does NOT yet wire to a variable a
sub-circuit reads. Named individually so the residue is a LIST and not an adjective. -/
def UNWIRED_ITEMS : List (String × Nat) := []
/-- **0** since 2026-08-02. The three that were here are closed WITH their consumers:

  * `sg_old[0]` — absorbed at block `oSgOld0` and consumed as `combine_split_commitments`' `~init`
    accumulator (`:606`), the point R4's `complete_add` chain starts at.
  * `combined_inner_product` as field+bit — absorbed at `oCip`, which is where `:256` puts it: AFTER
    ζ (`:568`), so it is not a cycle. The field half IS `vCipShift`, the statement word R8's
    `combined_inner_product_correct` ties to R5's Horner output.
  * `delta` — absorbed at `oDelta` and consumed by `lhs = Scalar_challenge.endo q c + delta`
    (`:325-327`), one endo ladder over the fold output at the LAST transcript squeeze plus one
    `Ops.add_fast`.

⚠ What remains is the ONE PAD LANE, which is not an item: 117 is odd. -/
def N_UNWIRED_ITEMS : Nat := (UNWIRED_ITEMS.map (·.2)).foldl (· + ·) 0

/-- The absorb-block count a shape needs to feed `N_ABSORB_ITEMS` items at rate 2 — `⌈117/2⌉ = 59`.
⚑ 117 is ODD, so one lane of one block has nothing upstream to carry: `index_digest` is a single
`Field` and every later item comes in pairs, so the spare lane is block 0's second, exactly where the
one non-commitment free word already sat (`msgVar`). That single PAD LANE is the difference between
`2·absorbs` and 117, and it is a consequence of modelling ONE commitment per rate-2 block. -/
def absorbBlocksNeeded : Nat := (N_ABSORB_ITEMS + 1) / 2

/-! ### `Common.ft_comm`'s own quantities (§6b).

`common.ml:238-256` and `step_verifier.ml:240-242,587-591`. Everything the ft_comm MSM is sized by,
stated where the transcript census can already see it: `t_comm`'s chunk count decides how many
transcript blocks stop being free, and the on-curve region below is sized by it. -/

/-- `Commitment_lengths.create ~t:(of_int 7)` (`commitment_lengths.ml:6-11`) — the quotient
polynomial's chunk count, hence `Array.length t_comm` in `common.ml:248`. -/
def N_TCOMM : Nat := 7
/-- …as many as THIS shape carries, capped at 7. The smoke shape carries three, the same way it
carries five fold rounds instead of 76; §12b″ pins that the cap does not bind at the committed shape,
so no `t_comm` chunk silently stays a free witness. ⚑ Read off `s.tComms` and no longer off
`absorbs − 1 − |absRoundList|`: since the R1 interleaving `absorbs` is DERIVED from the schedule and
the schedule contains the `t_comm` blocks, so the old form was circular. -/
def tCommN (s : StepShape) : Nat := min N_TCOMM s.tComms
/-- `ft_comm`'s `scale_fast2` count: `plonk.perm · sigma_comm_last`, the `n−1` Horner steps in
`plonk.zeta_to_srs_length`, and the closing `plonk.zeta_to_domain_size` scale. **Eight** at
`tCommN = 7`, which is `common.ml:246,251,256` counted. -/
def ftcTerms (s : StepShape) : Nat := tCommN s + 1
/-- `Ops.chunks_needed ~num_bits:(Field.size_in_bits − 1) = ⌈254/5⌉` — the chunk count EVERY
`ft_comm` scale runs at (`plonk_curve_ops.ml:66-70,254-257`; `scale_fast2 ~num_bits:255` via
`step_verifier.ml:240-242`). ⚠ NOT `msmChunks`: `multiscale_known`'s scalars carry a width PER BASIC
(#2) and `ft_comm`'s are uniformly 255-bit. -/
def FTC_CHUNKS : Nat := 51
/-- ⚑ The fold round whose base `Common.ft_comm` COMPUTES. `combine_split_commitments`' commitment
`3` is `ft_comm` (`step_verifier.ml:606`), and round `r` folds commitment `r+1`, so it is round 2. -/
def FTC_ROUND : Nat := 2

/-! ### ⚑⚑ §2b — **THE TRANSCRIPT SCHEDULE**: `incrementally_verify_proof`'s OWN absorb/squeeze
INTERLEAVING, read at source.

Until 2026-08-02 R1 ran **all** `absorbs` absorb blocks and **then** all `chals` squeeze blocks, and
its absorb order was the `ipaAbsorbs` FILTER order (z_comm ahead of w_comm, the gammas ahead of
`t_comm`). Neither is `verify_one`'s. A sponge is order-sensitive, so both were fidelity defects; and
the all-absorbs-first shape is what made `combined_inner_product` unwireable — absorbing it would
have made β/γ/α/ζ depend on a value the transcript itself determines. Upstream has no such cycle
because it absorbs it AFTER ζ.

`step_verifier.ml:529-574` then `:247-340`, in order, with the sponge item counts:

    :534   absorb Field index_digest                    1   (+1 PAD lane — 117 is odd)
    :538   Vector.iter (absorb PC) sg_old ×2            4   ⚑ sg_old[0] is the fold's `~init`
    :560   absorb PC x_hat                              2
    :562   Vector.iter absorb_g w_comm ×15             30
    :563   let beta  = sample ()                          SQUEEZE
    :564   let gamma = sample ()                          SQUEEZE
    :565   let z_comm = receive without z_comm          2
    :566   let alpha = sample_scalar ()                   SQUEEZE
    :567   let t_comm = receive without t_comm         14
    :568   let zeta  = sample_scalar ()                   SQUEEZE
    :573   sponge_before_evaluations = Sponge.copy sponge     ⚑ THE FORK
    :574   sponge_digest_before_evaluations = squeeze_field   (off the COPY's twin — see below)
    :256   absorb Scalar advice.combined_inner_product  2   ⚑ AFTER ζ. This is why there is no cycle.
    :264   let u = group_map (squeeze_field sponge)        SQUEEZE
    :199   ×15  absorb (PC :: PC) gammas_i              60   (two blocks per round)
    :200   ×15  squeeze_scalar                            SQUEEZE
    :321   absorb PC delta                              2
    :322   let c = squeeze_scalar sponge                  SQUEEZE

**117 items, 59 rate-2 blocks, 21 transcript squeezes.** ⚠ THE FORK, stated rather than elided: the
copy at `:573` is taken BEFORE the `:574` squeeze, so `check_bulletproof` continues from the state ζ
left and the digest permutation is a SIDE branch — the same `Sponge.copy` shape §3c already models
for `index_digest`. This file's linear chain IS the copy's; `sponge_digest_before_evaluations` is not
modelled as a block (nothing here consumes it — it is `verify_one`'s return value, absorbed by
`step_main.ml:45` into the sponge `finalize_other_proof` runs, which is segment A/B's business).

⚠ `chals = 23` against upstream's 21: the two extra are ξ and r, which upstream squeezes from the
**fr-sponge** (`:1008-1009`, §8g) and which this file still also allocates as transcript squeezes for
the round-robin `msmChal`/`ipaChal` sharing. They are scheduled at the END, after `c`, and named. -/

/-- Absorb-block ORDINALS, in upstream's order. Block indices are `absBlock` of these. -/
def oDigest : Nat := 0
/-- ⚑ `sg_old[0]` — `combine_split_commitments`' `~init` accumulator (`:606`), absorbed at `:538`
and consumed by R4's `complete_add` chain rather than by a fold round. -/
def oSgOld0 : Nat := 1
def oPre : Nat := 2
def oZ (s : StepShape) : Nat := oPre + (preRounds s).length
def oTc (s : StepShape) : Nat := oZ s + (zRounds s).length
/-- ⚑ `absorb sponge Scalar advice.combined_inner_product` (`:256`) — field then bit (`:79-81`). -/
def oCip (s : StepShape) : Nat := oTc s + tCommN s
def oGam (s : StepShape) : Nat := oCip s + 1
/-- ⚑ `absorb sponge PC delta` (`:321`), consumed by `lhs = Scalar_challenge.endo q c + delta`. -/
def oDelta (s : StepShape) : Nat := oGam s + (gamRounds s).length
/-- **`absorbs`, DERIVED from the schedule.** §12b pins `s.absorbs == absorbBlocksOf s` at both
shapes, so a shape cannot swallow a block the source does not feed. -/
def absorbBlocksOf (s : StepShape) : Nat := oDelta s + 1

/-- ⚑ How many SQUEEZE blocks follow absorb block `a`. Additive rather than a chain of `else if`, so
a shape whose `zRounds` or `t_comm` list is empty still gets both of the squeezes that bracket it. -/
def sqAfter (s : StepShape) (a : Nat) : Nat :=
  (if a + 1 == oZ s then 2 else 0)                              -- β (:563), γ (:564)
  + (if a + 1 == oTc s then 1 else 0)                           -- α (:566)
  + (if a + 1 == oCip s then 1 else 0)                          -- ζ (:568)
  + (if a == oCip s then 1 else 0)                              -- u = group_map … (:264)
  + (if oGam s ≤ a && a < oDelta s && (a - oGam s) % 2 == 1 then 1 else 0)   -- prechallenge (:200)
  -- `c` (:322), then the `chals − 21` this file still takes off the transcript rather than off the
  -- fr-sponge (ξ and r, §8g).
  + (if a == oDelta s then 1 + (s.chals - sqScheduled s) else 0)

/-- **R1's BLOCK SCHEDULE.** `some a` = absorb block `a`; `none` = a squeeze block. -/
def tSched (s : StepShape) : List (Option Nat) :=
  (List.range (absorbBlocksOf s)).flatMap (fun a =>
    some a :: List.replicate (sqAfter s a) none)

/-- Block `i`'s absorb ordinal, if it is an absorb block. -/
def blockAbs (s : StepShape) (i : Nat) : Option Nat := (tSched s).getD i none

/-- Absorb block `a`'s BLOCK index. -/
def absBlock (s : StepShape) (a : Nat) : Nat :=
  a + ((List.range a).map (sqAfter s)).foldl (· + ·) 0

/-- The block index of each squeeze, in order. -/
def sqBlocks (s : StepShape) : List Nat :=
  let l := tSched s
  (((l.zip (List.range l.length)).filter (fun p => p.1 == none)).map (·.2))
/-- ⚑ Squeeze `c`'s block — the state R2 reads challenge `c` out of is `vSt s (sqBlock s c + 1) 0`. -/
def sqBlock (s : StepShape) (c : Nat) : Nat := (sqBlocks s).getD c 0

/-! ### `Inner_curve.typ`'s own CHECK (§7b) — `assert_on_curve`.

`snarky_curve.ml:212-217`: `let x2 = square x in let x3 = x2 * x in let ax = Params.a * x in
assert_square y (x3 + ax + Params.b)`. Pallas has `a = 0, b = 5` (`Inner_curve.C =
Kimchi_pasta.Pasta.Pallas`, `step_main_inputs.ml:115`), so `ax` folds to the zero cvar and the
assert is ONE `Generic` half. Two variables per checked point — `x²` and `x³`; `y²` needs no slot
because the double-generic's own `w₀w₁` term is it.

⚑ The checked set is every SUPPLIED commitment the transcript absorbs: the `absRoundList` fold
bases, since §6b `t_comm`'s `tCommN` chunks, and since the R1 interleaving `sg_old[0]` and `delta`.
A CONSTANT base is pinned coordinate-for-coordinate and needs no membership check; the one COMPUTED
base (`ft_comm`, fold round `FTC_ROUND`) is on the curve because the `complete_add` chain that
produced it is. -/
def nOnC (s : StepShape) : Nat := (absRoundList s).length + tCommN s + 2
def baseOnC (s : StepShape) : Nat :=
  baseQN s + s.ipaRounds * s.ipaBlocks + s.ipaRounds + s.ipaBlocks + 1
def vOcX2 (s : StepShape) (k : Nat) : PVar := xv (baseOnC s + 2 * k)
def vOcX3 (s : StepShape) (k : Nat) : PVar := xv (baseOnC s + 2 * k + 1)

def baseDef (s : StepShape) : Nat := baseOnC s + 2 * nOnC s
/-- `ζ^{2^k}` in the deferred product (`k = 0..bRounds`). -/
def vZ (s : StepShape) (k : Nat) : PVar := xv (baseDef s + k)
/-- The factor `1 + u_k · ζ^{2^{bRounds−1−k}}`. -/
def vFac (s : StepShape) (k : Nat) : PVar := xv (baseDef s + s.bRounds + 1 + k)
/-- The running product after `k` factors; `vAcc bRounds` is `b(ζ)`. -/
def vAcc (s : StepShape) (k : Nat) : PVar := xv (baseDef s + 2 * s.bRounds + 1 + k)

def baseCip (s : StepShape) : Nat := baseDef s + 3 * s.bRounds + 2
/-- The claimed evaluation of column `k` at `ζ`. -/
def vEz (s : StepShape) (k : Nat) : PVar := xv (baseCip s + k)
/-- The claimed evaluation of column `k` at `ζω`. -/
def vEw (s : StepShape) (k : Nat) : PVar := xv (baseCip s + s.cipEvals + k)
/-- `r · evₖ(ζω)`. -/
def vDk (s : StepShape) (k : Nat) : PVar := xv (baseCip s + 2 * s.cipEvals + k)
/-- `cₖ = evₖ(ζ) + r · evₖ(ζω)` — the k-th coefficient of the ξ-weighted sum. -/
def vCk (s : StepShape) (k : Nat) : PVar := xv (baseCip s + 3 * s.cipEvals + k)
/-- The Horner intermediate `accᵢ · ξ`. -/
def vTk (s : StepShape) (i : Nat) : PVar := xv (baseCip s + 4 * s.cipEvals + i)
/-- The Horner accumulator after `i` steps; `vCa cipEvals` IS `combined_inner_product`. -/
def vCa (s : StepShape) (i : Nat) : PVar := xv (baseCip s + 5 * s.cipEvals + i)

/-! ### R6/R7 regions (§8d, §8e).

The absorption segments come FIRST and the ft program's slots LAST, because only the ft region's
size depends on a compiled program: every other base is a closed function of the shape. -/

def baseHm (s : StepShape) : Nat := baseCip s + 6 * s.cipEvals + 1
/-- One of `hash_messages_for_next_step_proof`'s `Not_opt` prefix words — the 28 plonk-index
commitments as 56 coordinates that `sponge_after_index` swallowed, plus two app-state words. ⚑ The
count is EVEN because the `Opt` region must begin on a rate-2 block boundary: upstream's
`Opt_sponge` masks per FIELD ELEMENT, this segment's `Field.if_` mux is per BLOCK, and an odd
prefix would put a `Not_opt` word and an `Opt` word under one `keep` bit. -/
def vHm (s : StepShape) (i : Nat) : PVar := xv (baseHm s + i)
/-- `Plonk_verification_key_evals`' commitment count: `sigma_comm` 7 + `coefficients_comm` 15 + six
selectors (`plonk_verification_key_evals.ml:8-19`). -/
def N_IDX_COMMS : Nat := 28
/-- …as field elements, `Inner_curve.to_field_elements` flattened — `sponge_after_index`'s WHOLE
input (`step_verifier.ml:1149-1157`). -/
def N_IDX_WORDS : Nat := 2 * N_IDX_COMMS
/-- ⚑ The APP-STATE words, and since 2026-08-02 the only fixtures left in the `Not_opt` prefix.
`to_field_elements_without_index` puts `state_to_field_elements app_state` first; the app state is
the INDUCTIVE RULE's own statement and no `verify_one` sub-circuit derives it, so it is a witness
here and is named as one rather than counted as derived. -/
def N_HM_APP : Nat := 2
def N_HM_FIX : Nat := N_IDX_WORDS + N_HM_APP

/-! ### The PLONK-INDEX region (§3c) — `sponge_after_index`'s own variables.

Only the index commitments the FOLD does not already carry need variables of their own; the other
27 ARE `combine_split_commitments`' `.const` bases and segment C absorbs THOSE variables. The
region is allocated in full at every shape so no id moves when a round becomes available. -/
def baseIdx (s : StepShape) : Nat := baseHm s + N_HM_APP
def vIdxX (s : StepShape) (k : Nat) : PVar := xv (baseIdx s + 2 * k)
def vIdxY (s : StepShape) (k : Nat) : PVar := xv (baseIdx s + 2 * k + 1)
/-- ⚑ **`index_digest`** — lane `j` of `Sponge.squeeze_field (Sponge.copy sponge_after_index)`
(`step_verifier.ml:529-534`). Lane 0 is the word R1's transcript absorbs FIRST. -/
def vIdxD (s : StepShape) (j : Nat) : PVar := xv (baseIdx s + N_IDX_WORDS + j)
def N_IDX_VARS : Nat := N_IDX_WORDS + 3

/-- Variables one sponge segment consumes: `3(nb+sq+1)` state lanes, `2·nb` post lanes, and for a
MASKED segment the `after`/`d`/`p`/`keep` mux cells. -/
def segVarCount (nb sq : Nat) : Nat := 3 * (nb + sq + 1) + 2 * nb + 9 * nb + nb

def baseSegA (s : StepShape) : Nat := baseIdx s + N_IDX_VARS
/-- Segment A (the opt-sponge): `2·bRounds` masked words, one squeeze. -/
def nbA (s : StepShape) : Nat := (2 * s.bRounds + 1) / 2
def baseSegB (s : StepShape) : Nat := baseSegA s + segVarCount (nbA s) 1
/-- Segment B (the fr-sponge): the digest, `ft_eval1`, `p(ζ)`, `p(ζω)` and the 43 columns at both
points, two squeezes (ξ′ and r′). -/
def nbB (s : StepShape) : Nat := (4 + 2 * (s.cipEvals - 4) + 1) / 2
def baseSegC (s : StepShape) : Nat := baseSegB s + segVarCount (nbB s) 2
/-- Segment C (`hash_messages_for_next_step_proof`), one squeeze. -/
def nbC (s : StepShape) : Nat := (N_HM_FIX + 4 + 2 * s.bRounds + 1) / 2

/-! ### The STATEMENT words R8 binds (§8f).

Upstream these are the Wrap proof-state's `Deferred_values` — `combined_inner_product`, `b` and
`plonk.perm` in `Shifted_value.Type1` form, and the `Scalar_challenge` `xi` — carried in the step
circuit's statement and CHECKED against what the circuit recomputes. They are exposed as the first
four public words, so a prover who supplies a different deferred value is refused by R8's
`Boolean.all` assert rather than believed. ⚠ In rungs r5–r7 (below the rung that checks them) they
are statement inputs and nothing else; r8 is the rung that binds them. -/
def baseStmt (s : StepShape) : Nat := baseSegC s + segVarCount (nbC s) 1
/-- `combined_inner_product`, `Shifted_value.Type1`. -/
def vCipShift (s : StepShape) : PVar := xv (baseStmt s)
/-- `b`, `Shifted_value.Type1`. -/
def vBShift (s : StepShape) : PVar := xv (baseStmt s + 1)
/-- `plonk.perm`, `Shifted_value.Type1` (`Plonk_checks.checked` compares the SHIFTED words). -/
def vPermShift (s : StepShape) : PVar := xv (baseStmt s + 2)
/-- `xi`'s RAW prechallenge — `xi_correct` compares it against the fr-sponge's own squeeze, and
§8g's chain `0` LIFTS it into the multiplier the C8 fold uses. -/
def vXiStmt (s : StepShape) : PVar := xv (baseStmt s + 3)

/-! ⚑ **`branch_data`, the fifth statement word** (`step_main.ml:53,70-72`;
`composition_types/branch_data.ml:88-101`). It is ONE field element that PACKS the two
`Proofs_verified.Prefix_mask` bits and `domain_log2`:

    Checked.pack {proofs_verified_mask; domain_log2} = 4·domain_log2 + pack(mask)

and `Vector.trim_front branch_data.proofs_verified_mask` is what gates the opt-sponge's absorptions.
§8h emits `pack` as rows, so the mask bits are Boolean circuit VARIABLES tied to a statement word
rather than a constant pattern — the retirement of the module header's simplification #9. -/
def vBranch (s : StepShape) : PVar := xv (baseStmt s + 4)
/-- `domain_log2`, the packed word's high part. -/
def vDomLog2 (s : StepShape) : PVar := xv (baseStmt s + 5)
/-- `proofs_verified_mask ! i` — a Boolean variable. `Prefix_mask.there` is
`N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]` (`pickles_base/proofs_verified.ml:75-81`), so the SET
bits are a SUFFIX: with one previous proof it is slot 1 that is kept, not slot 0. -/
def vMask (s : StepShape) (i : Nat) : PVar := xv (baseStmt s + 6 + i)
/-- The mask's own packing `m₀ + 2·m₁`, `Checked.pack`'s inner `pack`. -/
def vMaskPack (s : StepShape) : PVar := xv (baseStmt s + 8)
/-- ⚑ **`should_verify`, and it is a STATEMENT BOOL and not a witness.**
`step_main.ml:36-37` opens `verify_one` with `Boolean.Assert.( = )
unfinalized.should_finalize should_verify`, and `should_finalize` is a field of
`Types.Step.Proof_state.Per_proof.In_circuit` whose `spec` puts it in the `bool` list
(`composition_types.ml:1219,1310`) — i.e. it is part of the STEP STATEMENT, hence public.
Until 2026-08-02 this file made it an `AOp.wit`: the prover could set it to 0 and R8's
`verified && finalized ||| not should_verify` assert passed with ALL FOUR deferred bindings
false. §16g exhibits that. It is now a statement word, tied by a closing row like the other
four, so the mux branch is a PUBLIC CLAIM a consumer reads rather than a prover's private
choice — which is exactly upstream's semantics for a dummy previous proof. -/
def vShouldVerify (s : StepShape) : PVar := xv (baseStmt s + 9)
/-- ⚑ **`advice.combined_inner_product`'s BIT.** `Other_field.Packed` is `(Field.t, Boolean.var)` and
`absorb_scalar (x, b)` feeds `Field x` then `Bits [b]` (`step_verifier.ml:79-81`), so
`absorb sponge Scalar advice.combined_inner_product` (`:256`) is TWO sponge items and the second is
this. It carries `Boolean.typ`'s own `b² = b` check; the FIELD half is `vCipShift`, the statement
word R8's `combined_inner_product_correct` already ties to R5's Horner output — which is what makes
this a CONSUMED absorption rather than one more word the sponge eats. -/
def vCipBit (s : StepShape) : PVar := xv (baseStmt s + 10)
/-- …and its VALUE. ⚠ THE SIMPLIFICATION, named where it is made: `Other_field.Packed` splits an
`Fq` scalar into a 254-bit `Field.t` and a top BIT because `Fq > Fp`; this file absorbs the statement
word itself and a Boolean-constrained companion bit rather than emitting the split, so the bit is a
constrained witness at 0 in the honest instance. What that does NOT weaken: the FIELD half is
`vCipShift`, and R8 binds it. -/
def CIP_BIT : Nat := 0
def N_STMT : Nat := 11

/-! ### ⚑ `prev_challenges` — the PREVIOUS proofs' carried bulletproof challenges.

`step_verifier.ml:953-959` (`Opt_sponge.absorb opt_sponge (keep, chal)` over `prev_challenges`) and
`step_main.ml:80` (`old_bulletproof_challenges = prev_challenges`): segments A and C absorb THE SAME
vector, and it is a field of `Per_proof_witness` — the previous proof's own statement, checked by
`verified` (#11) and by nothing in `verify_one`.

⚠ ⚑ **THIS RETIRES A FALSE WIRE, AND THE TRADE IS STATED RATHER THAN QUIET.** Until 2026-08-02
`optSpec` and `hmSpec` absorbed `vN s (i % chals) emsRows` — R1's OWN transcript challenges — for
these `2·bRounds` words. Upstream those two vectors have no relationship: `prev_challenges` come from
the previous proof's statement, not from this transcript. That false wire cost more than fidelity: it
made segment A, hence the fr-sponge, hence ξ and r, hence `combined_inner_product` a function of
EVERY transcript challenge — so absorbing `cip` into the transcript at ANY position was a cycle, and
the interleaving alone would not have fixed it. What is LOST is that these words were derived cells
and are now witnesses; what is GAINED is that they are the ones upstream has, and that `cip` can be
absorbed. Both segments read the SAME variables, so they are still one σ class across two sponges and
segment C's public digest moves when one is bent. -/
def basePrevC (s : StepShape) : Nat := baseStmt s + N_STMT
/-- Carried challenge `i` — proof `i / bRounds`, round `i % bRounds`. -/
def vPrevChal (s : StepShape) (i : Nat) : PVar := xv (basePrevC s + i)
/-- A deterministic fixture standing for one carried challenge. -/
def prevChalVal (i : Nat) : Nat := (19 + 4000037 * i + 7 * i * i) % pN

/-! ### The DEFERRED challenges ξ and r (§8g) — the fold's own multipliers.

`step_verifier.ml:1006-1013`, verbatim:

    let squeeze () = squeeze_challenge sponge in
    let xi_actual = squeeze () in
    let r_actual  = squeeze () in
    let xi_correct = Field.equal xi_actual (match xi with { inner = xi } -> xi) in
    let xi = scalar xi in
    let r  = scalar (Import.Scalar_challenge.create r_actual) in

so the ξ the C8 fold multiplies by is `to_field_checked` of **the statement's ξ word** — the word
`xi_correct` ties to the fr-sponge's FIRST squeeze — and the `r` it (and `b_correct`) multiplies by
is `to_field_checked` of the fr-sponge's **SECOND squeeze**, with no statement word at all. Each
gets its own `to_field_checked` chain; chain `0` is ξ and chain `1` is r. ⚑ This is the retirement
of the module header's simplification #10: before it, both were R1 transcript challenges and the
fr-sponge squeeze fed NOTHING but `xi_correct`. -/
def N_DEFC : Nat := 2
/-- One deferred chain's variable block: `n/a/b` at every `EndoMulScalar` row boundary, the
`lowest_128_bits` high part, and the lift's two cells. -/
def defcStride (s : StepShape) : Nat := 3 * (s.emsRows + 1) + 3
def baseDefC (s : StepShape) : Nat := basePrevC s + 2 * s.bRounds
def vDN (s : StepShape) (c k : Nat) : PVar := xv (baseDefC s + c * defcStride s + k)
def vDA (s : StepShape) (c k : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + (s.emsRows + 1) + k)
def vDB (s : StepShape) (c k : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 2 * (s.emsRows + 1) + k)
/-- The discarded high part. Chain `0` has none — its source is already a `Challenge.t`. -/
def vDHi (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1))
def vDLiftT (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1) + 1)
/-- ⚑ **THE FOLD'S OWN MULTIPLIER.** `vDLift 0` is ξ and `vDLift 1` is r: the variables `cipRows`
Horners over and scales its `evₖ(ζω)` leg by, and the one `b_correct` weights `challenge_poly ζω`
with. Nothing else in the assembly plays those two roles. -/
def vDLift (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1) + 2)

/-! ### The `assert_128_bits hi` CHAINS (§5b) — simplification #1.

`lowest_128_bits ~constrain_low_bits x` (`util.ml:78-101`) witnesses `(lo, hi)`, asserts
`x = lo + 2¹²⁸·hi`, and RANGE-CHECKS BOTH PARTS — and `assert_n_bits ~n:128`
(`step_verifier.ml:88-97`) is not a bespoke gadget, it is
`ignore (SC.to_field_checked … ~num_bits:128)`: the `EndoMulScalar` chain runs and emits every one
of its rows, only the returned field element is dropped. So the range check IS a second
`to_field_checked`, and `tfcRows` emits it unchanged.

⚑ WHY IT IS A SOUNDNESS HOLE AND NOT A ROW COUNT. Without the `hi` chain, the decomposition row is
ONE equation in TWO unknowns with only `lo` constrained: for ANY `lo' < 2¹²⁸` the prover can solve
`hi' = (x − lo')·2^{−128}` and hand `lo'` to the rest of the circuit. The Fiat-Shamir challenge
becomes prover-chosen outright. §12c exhibits exactly that witness and shows this chain refuses it.

One block per SPLIT source: R2's `chals` transcript squeezes and §8g's chain `1` (`r`, the
fr-sponge's second squeeze). §8g's chain `0` has no block — its source is already a `Challenge.t`,
so upstream splits nothing there either. -/
def rngStride (s : StepShape) : Nat := 3 * (s.emsRows + 1) + 3
def baseRng (s : StepShape) : Nat := baseDefC s + N_DEFC * defcStride s
/-- Range chain `c`: `c < chals` is transcript challenge `c`'s high part, `chals + d` is deferred
chain `d`'s. -/
def vRN (s : StepShape) (c k : Nat) : PVar := xv (baseRng s + c * rngStride s + k)
def vRA (s : StepShape) (c k : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + (s.emsRows + 1) + k)
def vRB (s : StepShape) (c k : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 2 * (s.emsRows + 1) + k)
def vRHi (s : StepShape) (c : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 3 * (s.emsRows + 1))
def vRLiftT (s : StepShape) (c : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 3 * (s.emsRows + 1) + 1)
def vRLift (s : StepShape) (c : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 3 * (s.emsRows + 1) + 2)
/-- **R8's `lowest_128_bits`, high part.** `xi_actual = lowest_128_bits (squeeze fr_sponge)`
(`step_verifier.ml:820-822,1102`) is decomposed INSIDE the compiled finalize program (§8f), where
its high part is an `AOp.wit` — a cell with no defining row. `Util.lowest_128_bits` asserts
`assert_128_bits hi` UNCONDITIONALLY (`util.ml:98`), and this is that chain. -/
def RNG_FIN_HI (s : StepShape) : Nat := s.chals + N_DEFC
/-- **…and its LOW part.** `Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true`
(`step_verifier.ml:821-822`), so `util.ml:99` asserts the low part too. -/
def RNG_FIN_LO (s : StepShape) : Nat := s.chals + N_DEFC + 1
/-- One block per split source; the ξ chain's block is allocated and unused, so no id moves when a
future rung splits it. The last two are R8's, over the fr-sponge's FIRST squeeze. -/
def nRng (s : StepShape) : Nat := s.chals + N_DEFC + 2

/-! ### `Common.ft_comm`'s MSM region (§6b) — the `scale_fast2` variables.

One block per `scale_fast2` term (`ftcStride`), then the shared globals. ⚑ The region owns NO base
variables except `t_comm`'s: term 0's base is `sigma_comm_last`, which is §3c's own pinned
`vIdxX/vIdxY 6`; term 1's is `t_comm[n−1]`, whose two variables ARE transcript block `l+1`'s absorbed
words; and every later term's base is the PREVIOUS `Ops.add_fast`'s output. -/
def baseFtc (s : StepShape) : Nat := baseRng s + nRng s * rngStride s

/-- One `scale_fast2` term's variables: `FTC_CHUNKS+1` accumulator points, `FTC_CHUNKS` counter
boundaries (the last is the scalar's own `s_div_2`, shared), the top bit `scale_fast2` asserts zero,
the base's negated `y`, the `s_odd = 0` branch point, and `G.if_`'s three cells per coordinate. -/
def ftcStride : Nat := 2 * (FTC_CHUNKS + 1) + FTC_CHUNKS + 1 + 1 + 2 + 2 + 2 + 2

/-- ⚑ `Shifted_value.Type2`'s DISTINCT scalars: `0` is `plonk.perm`, `1` is
`plonk.zeta_to_srs_length` — which at `log2n = srs_length_log2 = 16` IS `plonk.zeta_to_domain_size`
(`plonk_checks.ml:496-497`), so the Horner steps and the closing scale share ONE pair. Upstream
shares it too: `scale_fast2` takes the already-split pair, so `common.ml` splits nothing per scale. -/
def N_FTC_SCAL : Nat := 2
/-- Term `k`'s scalar block. -/
def ftcScalOf (k : Nat) : Nat := if k == 0 then 0 else 1

def ftcAccX (s : StepShape) (k j : Nat) : PVar := xv (baseFtc s + k * ftcStride + 2 * j)
def ftcAccY (s : StepShape) (k j : Nat) : PVar := xv (baseFtc s + k * ftcStride + 2 * j + 1)
/-- Term `k`'s block base offset for the non-accumulator cells. -/
def ftcOff (s : StepShape) (k : Nat) : Nat := baseFtc s + k * ftcStride + 2 * (FTC_CHUNKS + 1)
/-- `scale_fast2`'s TOP BIT — `bits_lsb.(254)`, which `plonk_curve_ops.ml:262-265` asserts zero. It
is chunk 0's MSB, so it is a wired permutation cell of that chunk's `Zero` row and a `Generic` row
pins it. Without it the counter equation has TWO solutions mod `p` and the prover picks. -/
def ftcTop (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS)
/-- `Inner_curve.negate g`'s `y` — the odd-branch `add_fast h (G.negate g)` (`:267`). -/
def ftcNegY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 1)
def ftcHmX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 2)
def ftcHmY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 3)
/-- `G.if_`'s `then_ − else_` (`h − (h−g)`), per coordinate. -/
def ftcDX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 4)
def ftcDY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 5)
/-- …and `s_odd · (then_ − else_)`. -/
def ftcMX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 6)
def ftcMY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 7)
/-- Term `k`'s `scale_fast2` OUTPUT. -/
def ftcResX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 8)
def ftcResY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 9)

def baseFtcG (s : StepShape) : Nat := baseFtc s + ftcTerms s * ftcStride
/-- ⚑ **`t_comm` chunk `i`'s coordinates — and they are TRANSCRIPT WORDS.** `receive without t_comm`
(`step_verifier.ml:567`) absorbs them; `Common.ft_comm`'s Horner consumes them. One σ class spanning
the `Poseidon` sponge, `assert_on_curve` and this MSM's `VarBaseMul` chain. -/
def vTcX (s : StepShape) (i : Nat) : PVar := xv (baseFtcG s + 2 * i)
def vTcY (s : StepShape) (i : Nat) : PVar := xv (baseFtcG s + 2 * i + 1)
/-- `Ops.add_fast` output `a` (`a = 0 .. tCommN−1`): the `n−1` Horner partials `resₙ₋₂₋ₐ`, then
`f_comm + chunked_t_comm`. The LAST add's output is not here — it is the fold's own round-`FTC_ROUND`
base variable. -/
def ftcAddX (s : StepShape) (a : Nat) : PVar := xv (baseFtcG s + 2 * tCommN s + 2 * a)
def ftcAddY (s : StepShape) (a : Nat) : PVar := xv (baseFtcG s + 2 * tCommN s + 2 * a + 1)
/-- `negate (scale chunked_t_comm zeta_to_domain_size)`'s `y` (`common.ml:256`). -/
def ftcNegQ (s : StepShape) : PVar := xv (baseFtcG s + 4 * tCommN s)
/-- `Shifted_value.Type2`'s `s_div_2` — and the cell the ladder's FINAL counter IS. -/
def ftcDiv2 (s : StepShape) (c : Nat) : PVar := xv (baseFtcG s + 4 * tCommN s + 1 + 2 * c)
/-- …and its `s_odd`, a `Boolean.var`. -/
def ftcOdd (s : StepShape) (c : Nat) : PVar := xv (baseFtcG s + 4 * tCommN s + 2 + 2 * c)
/-- Term `k`'s counter at chunk boundary `j`. At `j = FTC_CHUNKS` it IS the scalar's `s_div_2`
variable — `Field.Assert.equal !n_acc scalar` (`plonk_curve_ops.ml:208`), the wire that makes the
ladder multiply by the value R6 derived and not by one the prover picked. -/
def ftcN (s : StepShape) (k j : Nat) : PVar :=
  if j == FTC_CHUNKS then ftcDiv2 s (ftcScalOf k) else xv (ftcOff s k + j)
def nFtcVars (s : StepShape) : Nat :=
  ftcTerms s * ftcStride + 4 * tCommN s + 1 + 2 * N_FTC_SCAL

def baseFtS (s : StepShape) : Nat := baseFtc s + nFtcVars s

/-! ## §3 — the row-schedule primitives. -/

/-- One circuit row: gate `kind`, the `K_PERMUTS = 7` permutation-column variables (`none` = unwired
⇒ `place` self-wires), the `coeffs`, and the ADVICE `(col, value)` placements for every column no
variable owns (including permutation columns deliberately left unwired). -/
structure SRow where
  kind : KGateType
  perm : List (Option PVar)
  coeffs : List Int := []
  advice : List (Nat × Int) := []
  /-- `true` only for the standalone `Zero` σ-only probes. -/
  probe : Bool := false
  deriving Repr, Inhabited

def noPerm : List (Option PVar) := List.replicate K_PERMUTS none

/-- A σ-ONLY PROBE. -/
def probeRow (wired : Bool) (a b : PVar) : SRow :=
  { kind := .zero
  , perm := if wired then [some a, some b, none, none, none, none, none] else noPerm
  , probe := true }

/-- The DOUBLE generic gate: half 1 is `c₀w₀+c₁w₁+c₂w₂+c₃w₀w₁+c₄ = 0` over cols 0,1,2; half 2 is the
same with `coeffs[5..9]` over cols 3,4,5 (`generic.rs:283-314`, read-only — `check_single(0,0)` then
`check_single(GENERIC_COEFFS, GENERIC_REGISTERS)`; the public term applies to half 1 only). -/
def genericRow (v0 v1 v2 v3 v4 v5 : Option PVar) (c : List Int) : SRow :=
  { kind := .generic, perm := [v0, v1, v2, v3, v4, v5, none], coeffs := c }

/-- `w₂ = w₀ + w₁`. -/ def cAdd : List Int := [1, 1, -1, 0, 0]
/-- `w₂ = w₀ · w₁`. -/ def cMul : List Int := [0, 0, -1, 1, 0]
/-- `w₂ = 1 + w₀·w₁`. -/ def cMulPlus1 : List Int := [0, 0, -1, 1, 1]
/-- `w₀ = w₁`. -/ def cEq : List Int := [1, -1, 0, 0, 0]
/-- `w₀ = k`. -/ def cConst (k : Int) : List Int := [1, 0, 0, 0, -k]
/-- `w₀ = w₂ + 2^bits·w₁` — the challenge decomposition. -/
def cSplit (bits : Nat) : List Int := [1, -((2 ^ bits : Nat) : Int), -1, 0, 0]
/-- An unused generic half. -/ def cNil : List Int := [0, 0, 0, 0, 0]

/-- A `complete_add` row: `o = l + r`, with `Ops.add_fast`'s four stored cells as advice. -/
def caRow (l r o : PVar × PVar) (c : List Nat) : SRow :=
  { kind := .completeAdd
  , perm := [ some l.1, some l.2, some r.1, some r.2, some o.1, some o.2, none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- Pack a list of `Generic` HALVES two to a row (Snarky's own double-generic filling). -/
def packHalves (hs : List (List (Option PVar) × List Int)) : List SRow :=
  let nil : List (Option PVar) × List Int := ([none, none, none], cNil)
  (List.range ((hs.length + 1) / 2)).map (fun r =>
    let h1 := hs.getD (2 * r) nil
    let h2 := if 2 * r + 1 < hs.length then hs.getD (2 * r + 1) nil else nil
    ({ kind := .generic, perm := h1.1 ++ h2.1 ++ [none]
     , coeffs := h1.2 ++ h2.2 } : SRow))

/-! ## §3b — the SUPPLIED COMMITMENTS, and where each curve base COMES FROM.

⚑ This is simplification #3, and reading `step_verifier.ml` at source splits it in two, because
upstream's curve bases have TWO provenances and NEITHER of them is "a free witness":

  * **CONSTANTS.** `multiscale_known`'s bases are `Inner_curve.constant (lagrange_commitment
    ~domain srs i)` (`:150,165-172,543-544`) — SRS points the verifier key fixes. So are the
    verifier-key commitments `m.generic_comm … m.sigma_comm` the fold consumes (`:606-616`), which
    reach the transcript only through `sponge_after_index`. A prover cannot choose any of them.
  * **THE PREVIOUS PROOF'S OWN COMMITMENTS.** `sg_old`, `x_hat`, `z_comm`, `w_comm`, and
    `bullet_reduce`'s fifteen `(L,R)` pairs. Every one is ABSORBED INTO THE TRANSCRIPT SPONGE before
    the challenge that weights it is squeezed (`:537,559,561,564`; `:193`) — which is the entire
    reason a Fiat-Shamir challenge binds the commitment it multiplies.

Until 2026-08-02 this file had NEITHER. Every base was a free witness variable carrying a `basePts`
fixture, and R1 absorbed `2·absorbs` UNRELATED `msgVal` words, so bending a base moved nothing and a
prover could pick the bases outright. Now a `.const` base is pinned by a `Generic` row
(`Inner_curve.constant`), and an `.absorbed` base's two coordinate variables **ARE** the two words
transcript block `b` absorbs — one σ class spanning the `Poseidon` sponge and the `EndoMul` chain.

⚠ THE RESIDUE, named rather than absorbed. The VALUES are a real proof's — `MinaStepPrevCommitments`
reads them out of the `MinaWrap*` gates for devnet block 539508 — and since §7b every absorbed one
also carries `Inner_curve.typ`'s `assert_on_curve`. What is still undone and is not a theorem:
`multiscale_known`'s SCALARS are upstream's PUBLIC INPUT words (the packed Wrap statement; #2 has
the word-for-word census) and here are still the circuit's own derived challenges. ⚑ The second
residue this note used to carry — "segment C's `sponge_after_index` prefix is still 58 fixture words
rather than the real plonk index" — is §3c, retired 2026-08-02. -/

/-- Where a curve base comes from. -/
inductive BaseSrc where
  /-- an SRS / verifier-key CONSTANT (`Inner_curve.constant`), pinned by a `Generic` row. -/
  | const
  /-- the previous proof's commitment, absorbed at transcript block `b` — the SAME two variables. -/
  | absorbed (b : Nat)
  /-- ⚑ COMPUTED IN-CIRCUIT: `Common.ft_comm`, whose two coordinate variables are the OUTPUT of
  §6b's own `complete_add` chain. Neither pinned nor absorbed — derived. -/
  | computed
  deriving Repr, DecidableEq, Inhabited

-- (⚑ the provenance CENSUS — `wdbAbsorbed` / `ipaAbsorbs` / `absRoundList` — is stated in §2,
-- because §2's `assert_on_curve` region is sized by it.)

/-- Position `k` of `absRoundList` as an ABSORB ORDINAL: the `preRounds ++ zRounds` prefix sits at
`oPre …`, the `gamRounds` tail at `oGam …` (§2b). -/
def absOrdOfIdx (s : StepShape) (k : Nat) : Nat :=
  let np := (preRounds s).length + (zRounds s).length
  if k < np then oPre + k else oGam s + (k - np)

/-- IPA round `r`'s base source. ⚑ Round `FTC_ROUND` is `ft_comm` and is COMPUTED since §6b — it was
an `Inner_curve.constant` carrying the real block's `COMBINE_XY[3]` until 2026-08-02. -/

def ipaSrc (s : StepShape) (r : Nat) : BaseSrc :=
  if r == FTC_ROUND then .computed
  else match (absRoundList s).findIdx? (fun x => x == r) with
  | some k => .absorbed (absOrdOfIdx s k)
  | none => .const

/-- Absorb block `a`'s commitment, as an IPA round — the inverse of `ipaSrc`. ⚑ Blocks `oDigest`,
`oSgOld0`, the `t_comm` run, `oCip` and `oDelta` carry no ROUND: `index_digest` is a bare `Field`,
`sg_old[0]` is the fold's `~init`, and the other three are consumed elsewhere. -/
def blockRound (s : StepShape) (a : Nat) : Option Nat :=
  if oPre ≤ a && a < oTc s then (absRoundList s)[a - oPre]?
  else if oGam s ≤ a && a < oDelta s then
    (absRoundList s)[(a - oGam s) + (preRounds s).length + (zRounds s).length]?
  else none

/-- ⚑ Absorb block `a`'s `t_comm` CHUNK, if it carries one. `receive without t_comm`
(`step_verifier.ml:567`) absorbs the seven quotient commitments after `z_comm` (hence after α) and
before ζ, which is exactly the `oTc … oCip` run of the schedule. -/
def tCommBlock (s : StepShape) (a : Nat) : Option Nat :=
  if oTc s ≤ a && a < oCip s then some (a - oTc s) else none

/-- ⚑ R3 is `multiscale_known` — the x_hat MSM — and every one of ITS bases is an SRS Lagrange
commitment inside `Inner_curve.constant`. There is no absorbed base in R3, upstream or here. -/
def msmSrc (_i : Nat) : BaseSrc := BaseSrc.const

/-- R4's bases in round order: `combine_split_commitments`' 46 (round `r` folds in commitment
`r+1`; commitment 0 is where the accumulator starts), then `bullet_reduce`'s 30 interleaved
`(L, R)`. -/
def REAL_IPA_XY : List (Nat × Nat) :=
  Dregg2.Bridge.MinaStepPrevCommitments.COMBINE_XY.tail
  ++ Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY

/-- ⚑ THE SUPPLIED COMMITMENTS, indexed as the assembly consumes them: the `msmTerms` SRS Lagrange
constants, then the `ipaRounds` fold / `bullet_reduce` bases. **These are Mina devnet block
539508's own Wrap-proof commitments**, Pallas points in this assembly's own field — not `basePts`,
which is what `[3]G, [4]G, …` this file ran until 2026-08-02. -/
def stepBases (s : StepShape) : List (Nat × Nat) :=
  (List.range s.msmTerms).map (fun i =>
     Dregg2.Bridge.MinaStepPrevCommitments.LAGRANGE_XY.getD i (0, 0))
  ++ (List.range s.ipaRounds).map (fun r => REAL_IPA_XY.getD r (0, 0))
def msmBaseOf (bs : List (Nat × Nat)) (i : Nat) : Nat × Nat := bs.getD i (0, 0)
def ipaBaseOf (s : StepShape) (bs : List (Nat × Nat)) (r : Nat) : Nat × Nat :=
  bs.getD (s.msmTerms + r) (0, 0)

/-- `Inner_curve.constant`: ONE `Generic` row pinning BOTH coordinates of a base the verifier fixes.
Half 1 is `w₀ − x = 0` over col 0, half 2 is `w₃ − y = 0` over col 3. -/
def baseConstRow (vx vy : PVar) (p : Nat × Nat) : SRow :=
  genericRow (some vx) none none (some vy) none none (cConst (p.1 : Int) ++ cConst (p.2 : Int))

/-! ## §3c — `sponge_after_index`, DERIVED (the other half of Fiat–Shamir).

`step_verifier.ml:1149-1157`, verbatim:

    let sponge_after_index index =
      let sponge = Sponge.create sponge_params in
      Array.iter (Types.index_to_field_elements ~g:Inner_curve.to_field_elements index)
        ~f:(fun x -> Sponge.absorb sponge (`Field x)) ; sponge

with `index = d.wrap_key` (`step_main.ml:61`) — the SAME `Plonk_verification_key_evals.t` the fold
consumes as `~verification_key:m`. Two things read it, and both are here:

  * **`index_digest`** (`:529-535`) — `Sponge.squeeze_field (Sponge.copy sponge_after_index)`, and
    `absorb sponge Field index_digest` is the FIRST thing the transcript swallows, ahead of
    `sg_old`. That is the wire that makes every transcript challenge a function of the verifier key.
  * **`hash_messages_for_next_step_proof`** (`:1158-1168`) — `Sponge.copy after_index`, then the
    app state / commitments / challenges. Segment C's `Not_opt` prefix IS that copy: absorbing the
    56 index words into a fresh sponge and continuing gives the same state a copy does, and 56 is
    even so the continuation starts on a rate-2 block boundary.

⚑ **27 OF THE 28 COMMITMENTS ARE ALREADY VARIABLES IN THIS ASSEMBLY.** `combine_split_commitments`
carries `sigma_comm[0..5]`, `coefficients_comm[0..14]` and the six selector commitments
(`step_verifier.ml:583-617`) as `.const` fold bases, each already pinned by an `Inner_curve.constant`
row. Segment C absorbs THOSE VERY VARIABLES, so the plonk index the sponge hashes and the plonk
index the fold multiplies by are ONE object rather than two agreeing copies. The 28th,
`sigma_comm[6]`, is `Common.ft_comm`'s `sigma_comm_last` (`common.ml:243-246`) and the fold does not
carry it, so it gets a pinned variable of its own here.

⚠ WHAT THIS DOES NOT DO: the 56 words are the verifier key, which a PROVER cannot choose either way
— the substance is that they are no longer FREE, i.e. the sponge state is a function of the key
rather than of a witness. -/

/-- VK commitment `k`, in `index_to_field_elements` order, as an IPA fold round — `none` for
`sigma_comm[6]`, which `combine_split_commitments` does not carry. Round `r`'s base is
`COMBINE_XY[r+1]`, so the census indices 41..46 / 26..40 / 5..10 become rounds 40..45 / 25..39 /
4..9. -/
def idxRoundOf (k : Nat) : Option Nat :=
  if k < 6 then some (40 + k)
  else if k == 6 then none
  else if k < 22 then some (25 + (k - 7))
  else some (4 + (k - 22))

/-- …and whether THIS shape has that round as a constant fold base. A shape too small to reach the
round falls back to a pinned variable of its own, so the derivation holds at every shape. -/
def idxSrc (s : StepShape) (k : Nat) : Option Nat :=
  match idxRoundOf k with
  | some r => if r < s.ipaRounds && ipaSrc s r == BaseSrc.const then some r else none
  | none => none

/-- The VARIABLE `sponge_after_index` absorbs at coordinate `j` of index commitment `k`. -/
def idxVar (s : StepShape) (k j : Nat) : PVar :=
  match idxSrc s k with
  | some r => if j == 0 then ipx s (qT s r) else ipy s (qT s r)
  | none => if j == 0 then vIdxX s k else vIdxY s k

/-- …and its VALUE, out of `MinaStepPrevCommitments.INDEX_XY`. -/
def idxVal (k j : Nat) : Nat :=
  let p := Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0)
  if j == 0 then p.1 else p.2

/-- The index commitments this shape must pin itself — everything the fold does not already hold. -/
def idxOwn (s : StepShape) : List Nat :=
  (List.range N_IDX_COMMS).filter (fun k => idxSrc s k == none)

/-- `Inner_curve.constant` rows for those. -/
def idxConstRows (s : StepShape) : List SRow :=
  (idxOwn s).map (fun k =>
    baseConstRow (vIdxX s k) (vIdxY s k)
      (Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0)))

/-- `sponge_after_index`'s trajectory over a WORD FUNCTION — `idxStatesWith ws ! b` is the state
entering absorb block `b`. Parametrised so §12d can re-run it on a prover's chosen input. -/
def idxStatesWith (ws : Nat → Nat) : List (List Nat) :=
  (List.range N_IDX_COMMS).foldl
    (fun acc b =>
      let st := acc.getLastD [0, 0, 0]
      acc ++ [ Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
                 [ (st.getD 0 0 + ws (2 * b)) % pN, (st.getD 1 0 + ws (2 * b + 1)) % pN
                 , st.getD 2 0 ] ])
    [[0, 0, 0]]

/-- The honest word at flat position `i` of the index absorption. -/
def idxWordAt (i : Nat) : Nat := idxVal (i / 2) (i % 2)

/-- ⚑ `sponge_after_index`'s STATE after all 28 absorptions — a closed function of the verifier key,
shape-independent by construction (the prefix is the same 56 words at every shape). -/
def idxAfterState : List Nat := (idxStatesWith idxWordAt).getLastD [0, 0, 0]

/-- …one more permutation, and lane 0 of it IS `index_digest`. -/
def idxDigestState : List Nat :=
  Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm idxAfterState
def indexDigest : Nat := idxDigestState.getD 0 0

/-- A transcript word no row pins and no sub-circuit derives.

⚠ ⚑ **AND THIS IS THE LAST PLACE FIAT-SHAMIR IS STILL THE PROVER'S, so say it plainly.** At
`shapeStep` it is now **ONE of the 118 absorbed words**: block `oDigest`'s SECOND LANE. `verify_one`
feeds `1 + 4 + 2 + 30 + 2 + 14 + 2 + 60 + 2 = 117` sponge items, 117 is ODD, and this file models one
commitment per rate-2 block, so exactly one lane of the `⌈117/2⌉` blocks carries nothing upstream
absorbs. **That is STRUCTURAL, not a hole**: there is no absorption missing behind it, and "closing"
it would mean inventing a word `verify_one` does not feed. It is a consequence of the per-block (not
per-element) rate model — the same simplification the opt-sponge prefix carries, named once.

⚑ The count was **7 until 2026-08-02** (and 31 before that, of which 25 were phantom blocks). The six
that left are the three real unwired absorptions, closed with their consumers by the R1 interleaving:
`sg_old[0]` (the fold's `~init` accumulator, `:606`), `combined_inner_product` as field+bit (`:256`,
tied by R8's `combined_inner_product_correct` to R5's Horner output) and `delta` (`:321`, consumed by
`lhs = Scalar_challenge.endo q c + delta`, `:326-327`). -/
def msgVal (b j : Nat) : Nat := (7 + 1000003 * (2 * b + j)) % pN

/-- ⚑ The VARIABLE absorbed at lane `j` of ABSORB BLOCK `a` (an absorb ORDINAL since the R1
interleaving, not a block index — `absBlock s a` is where it sits in the schedule). Every one of them
is a variable some sub-circuit reads except block `oDigest`'s second lane, the pad. -/
def msgVar (s : StepShape) (a j : Nat) : PVar :=
  match blockRound s a with
  | some r => if j == 0 then ipx s (qT s r) else ipy s (qT s r)
  | none =>
    match tCommBlock s a with
    | some i => if j == 0 then vTcX s i else vTcY s i
    | none =>
      if a == oDigest then (if j == 0 then vIdxD s 0 else vMsg s a j)
      -- ⚑ `sg_old[0]`: the fold's `~init` accumulator point, R4's own `complete_add` chain head.
      else if a == oSgOld0 then (if j == 0 then ipx s (qInit s) else ipy s (qInit s))
      -- ⚑ `advice.combined_inner_product`: the STATEMENT word R8 binds, then its `Boolean.var`.
      else if a == oCip s then (if j == 0 then vCipShift s else vCipBit s)
      -- ⚑ `delta`: the second operand of `check_bulletproof`'s closing `add_fast`.
      else if a == oDelta s then (if j == 0 then ipx s (qDel s) else ipy s (qDel s))
      else vMsg s a j

/-- …and its VALUE. `cipW` is `(field, bit)` of `advice.combined_inner_product`, threaded in because
it is computed from ξ, r and `ft_eval0` — all of which the transcript fixes BEFORE this block
(`:568` precedes `:256`), which is exactly why absorbing it is not a cycle. -/
def msgValOf (s : StepShape) (bs : List (Nat × Nat)) (cipW : Nat × Nat) (a j : Nat) : Nat :=
  match blockRound s a with
  | some r => let p := ipaBaseOf s bs r; if j == 0 then p.1 else p.2
  | none =>
    match tCommBlock s a with
    | some i =>
      let p := Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.getD i (0, 0)
      if j == 0 then p.1 else p.2
    | none =>
      if a == oDigest then (if j == 0 then indexDigest else msgVal a j)
      else if a == oSgOld0 then
        (let p := Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
         if j == 0 then p.1 else p.2)
      else if a == oCip s then (if j == 0 then cipW.1 else cipW.2)
      else if a == oDelta s then
        (let p := Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
         if j == 0 then p.1 else p.2)
      else msgVal a j

/-! ## §4 — R1, the TRANSCRIPT SPONGE.

Rate 2 into lanes 0,1, capacity lane 2 (`PastaPoseidon.Ref.absorbFrom`: `n = rate` triggers `perm`
then `absorbAt _ 0`). One absorb block:

    Generic  w₀=stᵦ[0] w₁=msg₀ w₂=postᵦ[0]  |  w₃=stᵦ[1] w₄=msg₁ w₅=postᵦ[1]
    Poseidon ×11, row j coeffs `poseidonRowCoeffs j`; row 0's cols 0,1,2 WIRED to
             (postᵦ[0], postᵦ[1], stᵦ[2]) — the capacity lane passes through untouched
    Zero     cols 0,1,2 WIRED to stᵦ₊₁[0..2] = the permutation output

A squeeze block is the same without the absorb row. The `Poseidon` gate at row `j` reads the NEXT
row's cols 0,1,2 as its output state, which is why the closing `Zero` row exists and why the state
chains across the eleven rows through the gate reference rather than through σ.

⚑ **THE BLOCKS ARE INTERLEAVED AS §2b's SCHEDULE SAYS**, not "all absorbs, then all squeezes". The
row COUNT is unchanged by that — `absorbs` absorb rows, `blocks` permutations, one probe per squeeze
plus one at the last absorb — but every squeeze's POSITION moves, so every challenge value moves and
with it every ladder the challenges drive. -/

/-- The 56 states of one permutation, `s(0) = st` through `s(55)`, ONE round per step. -/
def permStates (st : List Nat) : List (List Nat) :=
  (List.range 55).foldl
    (fun acc i =>
      acc ++ [Dregg2.Circuit.Emit.PastaPoseidon.Ref.round (rcsN.getD i []) (acc.getLastD st)])
    [st]

/-- Lane `j` of round state `k`. -/
def stLane (ss : List (List Nat)) (k j : Nat) : Int := ((ss.getD k []).getD j 0 : Int)

/-- The eleven `Poseidon` rows + the closing `Zero` row of ONE permutation. `round_to_cols` is
`STATE_ORDER = [0,2,3,4,1]` (`KimchiRenderPoseidon`, read-only): `s(5r)` at 0,1,2 · `s(5r+4)` at
3,4,5 · `s(5r+1)` at 6,7,8 · `s(5r+2)` at 9,10,11 · `s(5r+3)` at 12,13,14. -/
def permBlockRows (i0 i1 i2 o0 o1 o2 : PVar) (ss : List (List Nat)) : List SRow :=
  (List.range 11).map (fun r =>
    ({ kind := .poseidon
     , perm := if r == 0 then [some i0, some i1, some i2, none, none, none, none] else noPerm
     , coeffs := poseidonRowCoeffs r
     , advice :=
         (if r == 0 then [] else (List.range 3).map (fun j => (j, stLane ss (5 * r) j)))
         ++ (List.range 3).map (fun j => (3 + j, stLane ss (5 * r + 4) j))
         ++ (List.range 3).map (fun j => (6 + j, stLane ss (5 * r + 1) j))
         ++ (List.range 3).map (fun j => (9 + j, stLane ss (5 * r + 2) j))
         ++ (List.range 3).map (fun j => (12 + j, stLane ss (5 * r + 3) j)) } : SRow))
  ++ [ { kind := .zero, perm := [some o0, some o1, some o2, none, none, none, none] } ]

/-- The sponge's evaluated trajectory: `states ! b` is the state ENTERING block `b`, `perms ! b` is
block `b`'s 56 round states. -/
structure SpongeData where
  states : List (List Nat)
  perms : List (List (List Nat))
  /-- ⚑ the two words each absorb block SWALLOWED. For a block carrying one of the previous proof's
  commitments these are its coordinates, so the sponge trajectory is a function OF THE COMMITMENTS
  and every challenge below moves when one is bent. -/
  msgs : List (List Nat)
  deriving Repr, Inhabited

/-- R1's trajectory, PARAMETRISED on the value of `index_digest` (§3c), on the absorbed
`combined_inner_product` pair, AND on ONE absorbed word, absorb block `bt` lane `jt` — the grinds
§12d, §12b″ and §12i run. One implementation, so every control re-runs the assembly's own sponge
rather than a second copy of it; `bt ≥ absorbs` overrides nothing.

⚑ `msgs` is indexed by BLOCK (empty at a squeeze block), `vPost`/`vMsg`/`msgVar` by absorb ORDINAL. -/
def runSpongeAt (s : StepShape) (bs : List (Nat × Nat)) (dig : Nat) (cipW : Nat × Nat)
    (bt jt w : Nat) : SpongeData :=
  (List.range s.blocks).foldl
    (fun d b =>
      let pre := d.states.getLastD [0, 0, 0]
      let ms := match blockAbs s b with
        | none => []
        | some a =>
          [ (if a == bt && jt == 0 then w
             else if a == oDigest then dig else msgValOf s bs cipW a 0)
          , (if a == bt && jt == 1 then w else msgValOf s bs cipW a 1) ]
      let post :=
        if ms.isEmpty then pre
        else [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
      let ss := permStates post
      { states := d.states ++ [ss.getLastD post], perms := d.perms ++ [ss]
      , msgs := d.msgs ++ [ms] })
    { states := [[0, 0, 0]], perms := [], msgs := [] }

/-- …with no word overridden. -/
def runSpongeWith (s : StepShape) (bs : List (Nat × Nat)) (dig : Nat) (cipW : Nat × Nat)
    : SpongeData := runSpongeAt s bs dig cipW s.absorbs 0 0

/-- …at the DERIVED digest, which is the only instance the assembly emits. -/
def runSponge (s : StepShape) (bs : List (Nat × Nat)) (cipW : Nat × Nat) : SpongeData :=
  runSpongeWith s bs indexDigest cipW

/-- **R1's rows.** -/
def transcriptRows (s : StepShape) (d : SpongeData) (wired : Bool) : List SRow :=
  [ genericRow (some (vSt s 0 0)) none none (some (vSt s 0 1)) none none (cConst 0 ++ cConst 0)
  , genericRow (some (vSt s 0 2)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range s.blocks).flatMap (fun b =>
      match blockAbs s b with
      | some a =>
        -- ⚑ `msgVar` — for the blocks that carry a commitment this is the FOLD'S OWN BASE-POINT
        -- variable, so the sponge row and the `EndoMul` chain share one σ class.
        [ genericRow (some (vSt s b 0)) (some (msgVar s a 0)) (some (vPost s a 0))
                     (some (vSt s b 1)) (some (msgVar s a 1)) (some (vPost s a 1))
                     (cAdd ++ cAdd) ]
        ++ permBlockRows (vPost s a 0) (vPost s a 1) (vSt s b 2)
                         (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2) (d.perms.getD b [])
        ++ (if a + 1 == s.absorbs then
              [probeRow wired (vSt s (b+1) 0) (vSt s (b+1) 1)] else [])
      | none =>
        permBlockRows (vSt s b 0) (vSt s b 1) (vSt s b 2)
                      (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2) (d.perms.getD b [])
        ++ [probeRow wired (vSt s (b+1) 0) (vSt s (b+1) 1)])

/-! ## §5 — R2, CHALLENGE DERIVATION (`to_field_checked`).

Squeeze `c` is state lane 0 after block `absorbs + c`. Its low `chalBits` bits are the scalar
challenge. One `EndoMulScalar` row eats 8 crumbs and folds `n ↦ 4n + xⱼ`, `a ↦ 2a + c(xⱼ)`,
`b ↦ 2b + d(xⱼ)` from `n₀=0, a₀=2, b₀=2` (`endomul_scalar.rs:227-288`, read-only via
`KimchiRenderEndoMulScalar`). Column order `[n0, n8, a0, b0, a8, b8, x₀..x₇, 0]`, so cols 0..5 are
all permutation columns and the chain hops row→row through σ; col 6 holds crumb `x₀`, unwired. -/

def chalOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  ((d.states.getD (sqBlock s c + 1) []).getD 0 0) % 2 ^ s.chalBits
def hiOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  ((d.states.getD (sqBlock s c + 1) []).getD 0 0) / 2 ^ s.chalBits

/-- ⚑ `Endo.Wrap_inner_curve.scalar` (`endo.ml:7`) — the SCALAR-challenge endomorphism of `Fp`, the
constant `to_field_checked` scales `a₈` by. NOT `FT_ENDO`, which is the BASE endomorphism
`5^((p−1)/3)` the linearization reads; conflating the two cube roots is the defect
`MinaWrapFtEval0Weld` closed, and §16's red control shows it here. -/
def ENDO_R : Nat :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

/-- The `8·emsRows` base-4 crumbs of a challenge, MSB-first. -/
def crumbsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (8 * s.emsRows)).map (fun j => v / 4 ^ (8 * s.emsRows - 1 - j) % 4)

/-- The `(n,a,b)` accumulator triples at every ROW boundary (every 8 crumbs), `k = 0..emsRows`. -/
def emsAccs (s : StepShape) (v : Nat) : List (Nat × Nat × Nat) :=
  let all := (crumbsOf s v).foldl
    (fun acc x =>
      let cur := acc.getLastD (0, 2, 2)
      acc ++ [((4 * cur.1 + x) % pN, (2 * cur.2.1 + cFuncFp x) % pN,
               (2 * cur.2.2 + dFuncFp x) % pN)])
    [(0, 2, 2)]
  (List.range (s.emsRows + 1)).map (fun k => all.getD (8 * k) (0, 2, 2))

/-- The `(a₈, b₈)` accumulators and the LIFT `a₈·endo_r + b₈` of a 128-bit prechallenge. -/
def liftVal (s : StepShape) (v : Nat) : Nat :=
  let a := (emsAccs s v).getD s.emsRows (0, 2, 2)
  fAdd (fMul a.2.1 ENDO_R) a.2.2
def liftTVal (s : StepShape) (v : Nat) : Nat :=
  fMul ((emsAccs s v).getD s.emsRows (0, 2, 2)).2.1 ENDO_R
/-- …of transcript challenge `c`. -/
def liftOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat := liftVal s (chalOf s d c)
def liftTOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat := liftTVal s (chalOf s d c)

/-- The one row that pins `endo_r`, emitted once ahead of the challenge chains. Every
`to_field_checked` chain in the assembly — R2's `chals` and §8g's two deferred ones — shares it. -/
def endoConstRow (s : StepShape) : List SRow :=
  [ genericRow (some (vEndoR s)) none none none none none (cConst (ENDO_R : Int) ++ cNil) ]

/-- One `to_field_checked` chain's variable block, so the SAME row emitter serves R2's transcript
challenges and §8g's deferred ξ/r. -/
structure ChalVars where
  n : Nat → PVar
  a : Nat → PVar
  b : Nat → PVar
  hi : PVar
  liftT : PVar
  lift : PVar

def r2Vars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vN s c, a := vA s c, b := vB s c, hi := vHi s c
  , liftT := vLiftT s c, lift := vLift s c }
def defcVars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vDN s c, a := vDA s c, b := vDB s c, hi := vDHi s c
  , liftT := vDLiftT s c, lift := vDLift s c }

/-- **`to_field_checked`'s rows** over a 128-bit prechallenge `v` (`scalar_challenge.ml:12-129`):
`n₀=0, a₀=2, b₀=2` pinned by `Generic` rows, `emsRows` chained `EndoMulScalar` rows, the tie of the
chain's reconstructed `n₈` back to its SOURCE, and the closing lift `Field.(scale a endo + b)`.

`split = true` — the source is a FULL field element (a sponge squeeze), so the tie is the
`lowest_128_bits` decomposition `src = n₈ + 2^chalBits·hi`. `split = false` — the source is already
a `Challenge.t` (§8g's statement ξ word), so the tie is `Field.Assert.equal n scalar` (`:124`) and
the chain's `hi` cell is not allocated by any row. -/
def tfcRows (s : StepShape) (cv : ChalVars) (src : PVar) (split : Bool) (v : Nat)
    (wired : Bool) : List SRow :=
  let cr := crumbsOf s v
  [ genericRow (some (cv.n 0)) none none (some (cv.a 0)) none none (cConst 0 ++ cConst 2)
  , genericRow (some (cv.b 0)) none none none none none (cConst 2 ++ cNil) ]
  ++ (List.range s.emsRows).map (fun k =>
      ({ kind := .endoMulScalar
       , perm := [ some (cv.n k), some (cv.n (k+1)), some (cv.a k), some (cv.b k)
                 , some (cv.a (k+1)), some (cv.b (k+1)), none ]
       , advice := (List.range 8).map (fun j => (6 + j, (cr.getD (8 * k + j) 0 : Int)))
                   ++ [(14, 0)] } : SRow))
  ++ [ (if split then
          genericRow (some src) (some cv.hi) (some (cv.n s.emsRows)) none none none
                     (cSplit s.chalBits ++ cNil)
        else
          genericRow (some (cv.n s.emsRows)) (some src) none none none none (cEq ++ cNil))
     -- ⚑ `to_field_checked`'s CLOSING LINE: `Field.(scale a endo + b)`. Two halves of one row, and
     -- the `a₈`/`b₈` cells the `EndoMulScalar` chain produced now carry a value the rest of the
     -- assembly reads.
     , genericRow (some (cv.a s.emsRows)) (some (vEndoR s)) (some cv.liftT)
                  (some cv.liftT) (some (cv.b s.emsRows)) (some cv.lift) (cMul ++ cAdd)
     , probeRow wired (cv.n s.emsRows) (cv.a s.emsRows)
     , probeRow wired cv.lift (cv.b s.emsRows) ]

def rngVars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vRN s c, a := vRA s c, b := vRB s c, hi := vRHi s c
  , liftT := vRLiftT s c, lift := vRLift s c }

/-- Range chain `c`'s accumulator trace at value `v`. -/
def rngEnv (s : StepShape) (c v : Nat) : VarEnv :=
  let accs := emsAccs s v
  (List.range (s.emsRows + 1)).flatMap (fun k =>
    let a := accs.getD k (0, 2, 2)
    [ (vRN s c k, (a.1 : Int)), (vRA s c k, (a.2.1 : Int)), (vRB s c k, (a.2.2 : Int)) ])
  ++ [ (vRLiftT s c, (liftTVal s v : Int)), (vRLift s c, (liftVal s v : Int)) ]

/-- **`assert_128_bits x`** — `ignore (to_field_checked … ~num_bits:128)`, so the SAME chain over
the same source, tied by `Field.Assert.equal n scalar` and with the lift emitted (Snarky emits it;
only the value is dropped). Range chain `c` over source `src` holding value `v`. -/
def rangeRows (s : StepShape) (c : Nat) (src : PVar) (v : Nat) (wired : Bool) : List SRow :=
  tfcRows s (rngVars s c) src false v wired

/-- **R2's rows** for challenge `c` — `tfcRows` at the transcript sponge's own squeeze, then
`lowest_128_bits`' OTHER range check, over the high part (`~constrain_low_bits:true` asserts both;
`step_verifier.ml:186-187`). -/
def challengeRows (s : StepShape) (d : SpongeData) (wired : Bool) (c : Nat) : List SRow :=
  tfcRows s (r2Vars s c) (vSt s (sqBlock s c + 1) 0) true (chalOf s d c) wired
  ++ rangeRows s c (vHi s c) (hiOf s d c) wired

/-! ## §6 — R3, the COMMITMENT MSM (`multiscale_known` / `ft_comm`).

`runVbm` (read-only) runs `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, `nₖ₊₁ = 2nₖ+bₖ`, so with `n₀ = 0` the
final counter IS the scalar — and that cell is wired to the CHALLENGE variable, not a fresh one. -/

/-- The `5·msmChunks` bits of `v`, MSB-first. -/
def bitsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (5 * s.msmChunks)).map (fun k => v / 2 ^ (5 * s.msmChunks - 1 - k) % 2)
/-- The `4·ipaBlocks` bits of `v`, MSB-first. -/
def endoBitsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (4 * s.ipaBlocks)).map (fun k => v / 2 ^ (4 * s.ipaBlocks - 1 - k) % 2)

structure MsmData where
  terms : List TermData
  bits : List (List Nat)
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  deriving Repr, Inhabited

def runMsm (s : StepShape) (bases : List (Nat × Nat)) (d : SpongeData) : MsmData :=
  let bs := (List.range s.msmTerms).map (fun i => bitsOf s (chalOf s d (s.msmChal i)))
  let tds := (List.range s.msmTerms).map (fun i =>
    let T := msmBaseOf bases i
    runVbm T (dblA T) (bs.getD i []))
  let pts := (List.range s.msmTerms).map (fun i => (tds.getD i default).accs.getLastD (0, 0))
  let st := (List.range (s.msmTerms - 1)).foldl
    (fun (acc : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then pts.getD 0 (0, 0) else acc.1.getLastD (0, 0)
      let r := pts.getD (a + 1) (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (acc.1 ++ [(cells.getD 4 0, cells.getD 5 0)], acc.2 ++ [cells]))
    ([], [])
  { terms := tds, bits := bs, sums := st.1, addCells := st.2 }

/-- The two rows of MSM term `i`'s chunk `j`.
CURR `w₀=xT w₁=yT w₂=x₀ w₃=y₀ w₄=n w₅=n' w₆=Ø w₇..w₁₄ = x₁y₁..x₄y₄`;
NEXT `w₀=x₅ w₁=y₅ w₂..w₆=b₀..b₄ w₇..w₁₁=s₀..s₄`. -/
def msmChunkRows (s : StepShape) (m : MsmData) (i j : Nat) : List SRow :=
  let td := m.terms.getD i default
  let bits := m.bits.getD i []
  let ax : Nat → Int := fun k => ((td.accs.getD k (0, 0)).1 : Int)
  let ay : Nat → Int := fun k => ((td.accs.getD k (0, 0)).2 : Int)
  let bt : Nat → Int := fun k => (td.slopes.getD k 0 : Int)
  let bi : Nat → Int := fun k => (bits.getD k 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some (mpx s (pT s i)), some (mpy s (pT s i))
              , some (mpx s (pAcc s i j)), some (mpy s (pAcc s i j))
              , some (vSN s i j), some (vSN s i (j+1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (mpx s (pAcc s i (j+1))), some (mpy s (pAcc s i (j+1)))
              , none, none, none, none, none ]
    , advice := [ (2, bi (5*j)), (3, bi (5*j+1)), (4, bi (5*j+2)), (5, bi (5*j+3)), (6, bi (5*j+4))
                , (7, bt (5*j)), (8, bt (5*j+1)), (9, bt (5*j+2)), (10, bt (5*j+3))
                , (11, bt (5*j+4)) ] } ]

/-- The `a`-th `complete_add` of the MSM chain: `Rₐ = Lₐ + Pₐ₊₁`, `L₀ = P₀`, `Lₐ = Rₐ₋₁`. -/
def msmAddRow (s : StepShape) (m : MsmData) (a : Nat) : SRow :=
  let lp := if a == 0 then pAcc s 0 s.msmChunks else pSum s (a - 1)
  let rp := pAcc s (a + 1) s.msmChunks
  let c := m.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (mpx s lp), some (mpy s lp), some (mpx s rp), some (mpy s rp)
            , some (mpx s (pSum s a)), some (mpy s (pSum s a)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **R3's base pins** — `multiscale_known`'s bases are `Inner_curve.constant (lagrange_commitment
~domain srs i)` (`step_verifier.ml:150,165-172,543-544`), so ALL `msmTerms` of them are pinned.
Before 2026-08-02 every one was a free witness the prover chose. -/
def msmBaseRows (s : StepShape) (m : MsmData) : List SRow :=
  (List.range s.msmTerms).map (fun i =>
    baseConstRow (mpx s (pT s i)) (mpy s (pT s i)) (m.terms.getD i default).T)

/-- **`scale_fast_unpack`'s OWN SEED**, `Ops.add_fast base base` (`plonk_curve_ops.ml:157`) — one
`CompleteAdd` row per MSM term, DEFINING `pAcc i 0` instead of leaving it a witness.

⚑ THE HOLE THIS CLOSES. The ladder is `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, so
`acc_N = 2^{5·msmChunks}·acc₀ + Σₖ (2bₖ−1)·2^{5·msmChunks−1−k}·T`. Doubling is a BIJECTION on the
group, so for ANY target point the prover solves for `acc₀` — and nothing else in R3 objects: the
base is pinned (`msmBaseRows`), the bits are the chunk rows' own advice, and the counter chain closes
on the challenge variable, none of which say a word about the seed. `multiscale_known`'s output —
`x_hat`, a PUBLIC word here and a segment-C absorption — was the prover's outright. §12f exhibits the
witness. §6b's `ft_comm` ladders carried this row from the start (`ftcTermRows`'s `caRow g g`); R3's
did not. -/
def msmDblRow (s : StepShape) (m : MsmData) (i : Nat) : SRow :=
  let T := (m.terms.getD i default).T
  let c := completeAddWitness T.1 T.2 T.1 T.2
  { kind := .completeAdd
  , perm := [ some (mpx s (pT s i)), some (mpy s (pT s i))
            , some (mpx s (pT s i)), some (mpy s (pT s i))
            , some (mpx s (pAcc s i 0)), some (mpy s (pAcc s i 0)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **`let n_acc = ref Field.zero`** (`plonk_curve_ops.ml:158`) — the SECOND free witness of the same
two lines, one `Generic` half per MSM term.

⚑ `Field.zero` is a CONSTANT upstream; here `vSN i 0` was a variable no row read. The chunk rows
constrain `n' = 32·n + Σ_t 2^{4−t}·b_t`, so the chain closes on
`n_final = 32^{msmChunks}·n₀ + (the bits as an integer)` — and `n_final` IS the challenge variable
(`vSN i msmChunks = vN (msmChal i) emsRows`). With `n₀` free a prover picks ANY bit vector and solves
`n₀ = (n_final − bits)·32^{−msmChunks}`; the bits he picks are the multiplier the ladder actually
uses. That is the acc₀ hole through the other cell, and §12f exhibits it too. -/
def msmNZeroRows (s : StepShape) : List SRow :=
  packHalves ((List.range s.msmTerms).map (fun i =>
    ([some (vSN s i 0), none, none], cConst 0)))

/-- **R3's rows.** -/
def msmRows (s : StepShape) (m : MsmData) (wired : Bool) : List SRow :=
  msmBaseRows s m
  ++ msmNZeroRows s
  ++ [msmDblRow s m 0]
  ++ ((List.range s.msmChunks).flatMap (msmChunkRows s m 0))
  ++ [probeRow wired (mpx s (pAcc s 0 s.msmChunks)) (mpy s (pAcc s 0 s.msmChunks))]
  ++ (List.range (s.msmTerms - 1)).flatMap (fun a =>
       let i := a + 1
       [msmDblRow s m i]
       ++ ((List.range s.msmChunks).flatMap (msmChunkRows s m i))
       ++ [probeRow wired (mpx s (pAcc s i s.msmChunks)) (mpy s (pAcc s i s.msmChunks))]
       ++ [msmAddRow s m a]
       ++ [probeRow wired (mpx s (pSum s a)) (mpy s (pSum s a))])

/-! ## §7 — R4, the IPA / commitment FOLD (`Scalar_challenge.endo`).

`endo_mul` chains by ROW OVERLAP, not by σ: row `r+1` is simultaneously block `r`'s `Next`
(`w'₄=xs w'₅=ys w'₆=n'`) and block `r+1`'s `Curr` (`w₄=xp w₅=yp w₆=n`) — the SAME three cells. The
base point at cols 0,1 IS a σ class of `ipaBlocks` cells, and the FINAL scalar counter (on the tail
`Zero` row, col 6) is the round's CHALLENGE variable. -/

/-- ⚑ **`Scalar_challenge.endo`'s OWN SEED** (`scalar_challenge.ml:230-234`), verbatim:

    let acc =
      with_label __LOC__ (fun () ->
          let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in
          ref G.(p + p) )
    in
    let n_acc = ref Field.zero in

`φ(t) = (endo·xt, yt)` is the endomorphism image — `Endo.base` is the base field's primitive cube
root, `KimchiRenderEndoMul.endo = PastaCurve.zetaP` — so the seed is `2·(t + φ(t))`, THREE rows: a
`Generic` half for `endo·xt` and two `Ops.add_fast`s. ⚠ Until 2026-08-02 `runIpa` seeded at `dblA T`
with `qAcc r 0` and `vQN r 0` read by NO row, which was both a free-witness hole of R3's exact class
(§12f) and the wrong point: `2t` is not `2(t + φ(t))`, so the fold's arithmetic was self-consistent
but was not `Scalar_challenge.endo`. -/
def endoQ (T : Nat × Nat) : Nat × Nat :=
  (fMul Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo T.1, T.2)
/-- `p = add_fast t φ(t)`. -/
def endoP (T : Nat × Nat) : Nat × Nat := addA T (endoQ T)
/-- `acc₀ = add_fast p p`. -/
def endoSeed (T : Nat × Nat) : Nat × Nat := dblA (endoP T)

structure IpaData where
  accs : List (List (Nat × Nat))
  blks : List (List EndoBlock)
  ns : List (List Nat)
  bases : List (Nat × Nat)
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  /-- ⚑ `check_bulletproof`'s tail (`:325-327`): `Scalar_challenge.endo q c`'s accumulator trace,
  its blocks, its counter chain, and the closing `add_fast` with `delta`. -/
  lhsAccs : List (Nat × Nat) := []
  lhsBlks : List EndoBlock := []
  lhsNs : List Nat := []
  lhsAdd : List Nat := []
  deriving Repr, Inhabited

/-- One `Scalar_challenge.endo` ladder over base `T` at prechallenge `v`, seeded at
`scalar_challenge.ml:230-235`. Shared by the fold's rounds and by `check_bulletproof`'s tail. -/
def runEndo (s : StepShape) (T : Nat × Nat) (v : Nat)
    : List (Nat × Nat) × List EndoBlock × List Nat :=
  let bits := endoBitsOf s v
  (List.range s.ipaBlocks).foldl
    (fun (st : List (Nat × Nat) × List EndoBlock × List Nat) e =>
      let cur := st.1.getLastD (0, 0)
      let b := endoStep T.1 T.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      (st.1 ++ [(b.xs, b.ys)], st.2.1 ++ [b],
       st.2.2 ++ [16 * st.2.2.getLastD 0 + 8*b.b1 + 4*b.b2 + 2*b.b3 + b.b4]))
    ([endoSeed T], [], [0])

/-- ⚑ `ftcOut` is `Common.ft_comm`'s ASSEMBLED value — round `FTC_ROUND`'s base since §6b. The
supplied list still carries `COMBINE_XY[3]` (the real block's own `ft_comm`) and the assembly
IGNORES it: that round's base is computed, so a supplied one would be a second copy.

⚑ THE FOLD CHAIN NOW STARTS AT COMMITMENT 0. `combine_split_commitments` is called with
`~init:(function `Finite x -> `Finite x | …)` (`step_verifier.ml:606`), i.e. the accumulator IS
`sg_old[0]`; every round's output is folded into it, so there are `ipaRounds` adds and not
`ipaRounds − 1`. Until 2026-08-02 the chain started at round 0's output and `sg_old[0]` was one of
the three transcript words nothing read. -/
def runIpa (s : StepShape) (allB : List (Nat × Nat)) (d : SpongeData) (ftcOut : Nat × Nat)
    : IpaData :=
  let bases := (List.range s.ipaRounds).map (fun r =>
    if ipaSrc s r == BaseSrc.computed then ftcOut else ipaBaseOf s allB r)
  let rounds := (List.range s.ipaRounds).map (fun r =>
    runEndo s (bases.getD r (0, 0)) (chalOf s d (s.ipaChal r)))
  let pts := rounds.map (fun r => r.1.getLastD (0, 0))
  let st := (List.range s.ipaRounds).foldl
    (fun (acc : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
               else acc.1.getLastD (0, 0)
      let r := pts.getD a (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (acc.1 ++ [(cells.getD 4 0, cells.getD 5 0)], acc.2 ++ [cells]))
    ([], [])
  -- ⚑ `check_bulletproof`'s tail: `cq = Scalar_challenge.endo q c`, `lhs = cq + delta`.
  let q := st.1.getLastD (0, 0)
  let lhs := runEndo s q (chalOf s d s.cChal)
  let cq := lhs.1.getLastD (0, 0)
  let dl := Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
  { accs := rounds.map (·.1), blks := rounds.map (·.2.1), ns := rounds.map (·.2.2)
  , bases := bases, sums := st.1, addCells := st.2
  , lhsAccs := lhs.1, lhsBlks := lhs.2.1, lhsNs := lhs.2.2
  , lhsAdd := completeAddWitness cq.1 cq.2 dl.1 dl.2 }

/-- One endo ladder's variable slots — the fold's rounds and `check_bulletproof`'s tail differ only
in where their points and counters live. -/
structure EndoSlots where
  /-- the base point's index. -/
  base : Nat
  /-- the seed intermediate `p = t + φ(t)`. -/
  p : Nat
  /-- accumulator point after `e` blocks. -/
  acc : Nat → Nat
  /-- counter after `e` blocks; at `e = ipaBlocks` it is the challenge variable. -/
  n : Nat → PVar
  /-- `endo · x_t`. -/
  endoX : PVar

def roundSlots (s : StepShape) (r : Nat) : EndoSlots :=
  { base := qT s r, p := qP s r, acc := qAcc s r, n := vQN s r, endoX := vQEndo s r }
/-- ⚑ The tail's base is the FOLD OUTPUT `q = combined_polynomial + …` — a computed point, not a
supplied one, so it needs no pin and no `assert_on_curve`. -/
def lhsSlots (s : StepShape) : EndoSlots :=
  { base := qSum s (s.ipaRounds - 1), p := qLhsP s, acc := qLhsAcc s
  , n := vLhsN s, endoX := vLhsEndo s }

def endoRoundRows (s : StepShape) (sl : EndoSlots) (bl : List EndoBlock) : List SRow :=
  (List.range s.ipaBlocks).map (fun e =>
    let b := bl.getD e default
    ({ kind := .endoMul
     , perm := [ some (ipx s sl.base), some (ipy s sl.base), none, none
               , some (ipx s (sl.acc e)), some (ipy s (sl.acc e)), some (sl.n e) ]
     , advice := [ (2, (b.inv : Int)), (3, 0), (7, (b.xr : Int)), (8, (b.yr : Int))
                 , (9, (b.s1 : Int)), (10, (b.s3 : Int)), (11, (b.b1 : Int)), (12, (b.b2 : Int))
                 , (13, (b.b3 : Int)), (14, (b.b4 : Int)) ] } : SRow))
  ++ [ { kind := .zero
       , perm := [ none, none, none, none, some (ipx s (sl.acc s.ipaBlocks))
                 , some (ipy s (sl.acc s.ipaBlocks)), some (sl.n s.ipaBlocks) ] } ]

def ipaRoundRows (s : StepShape) (v : IpaData) (r : Nat) : List SRow :=
  endoRoundRows s (roundSlots s r) (v.blks.getD r [])

/-- ⚑ The `a`-th fold add. `a = 0`'s LEFT operand is `qInit` — `sg_old[0]`, the `~init` accumulator
(`step_verifier.ml:606`) whose two coordinates ARE transcript block `oSgOld0`'s absorbed words. -/
def ipaAddRow (s : StepShape) (v : IpaData) (a : Nat) : SRow :=
  let lp := if a == 0 then qInit s else qSum s (a - 1)
  let rp := qAcc s a s.ipaBlocks
  let c := v.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (ipx s lp), some (ipy s lp), some (ipx s rp), some (ipy s rp)
            , some (ipx s (qSum s a)), some (ipy s (qSum s a)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **R4's base pins** — ONLY the verifier-key CONSTANTS (`ipaSrc r = .const`). The absorbed ones are
pinned by nothing here on purpose: they are the previous proof's, and what binds them is that their
two variables ARE transcript block `b`'s absorbed words. ⚑ Round `FTC_ROUND` is in neither set since
§6b: its base is `.computed`, so a pin row there would be pinning a derived value to a literal. -/
def ipaBaseRows (s : StepShape) (v : IpaData) : List SRow :=
  ((List.range s.ipaRounds).filter (fun r => ipaSrc s r == BaseSrc.const)).map (fun r =>
    baseConstRow (ipx s (qT s r)) (ipy s (qT s r)) (v.bases.getD r (0, 0)))

/-! ### §7b — `Inner_curve.typ`'s CHECK on every SUPPLIED point.

⚑ THE HOLE THIS CLOSES. `EndoMul`, `VarBaseMul` and `CompleteAdd` constrain the ADDITION ARITHMETIC
and nothing else: every one of their polynomials is satisfied by any `(x, y)` in the field, on or
off the curve. Upstream never has to think about it because a supplied point arrives through
`Inner_curve.typ`, whose `check` IS `assert_on_curve` (`snarky_curve.ml:219-229`) — Snarky runs it
on every `exists` of that type. This file read the previous proof's commitments in as bare
coordinate variables, so an off-curve "commitment" satisfied every gate. §12b′ exhibits one.

The CONSTANT bases need no check and get none, which is upstream's shape too: an
`Inner_curve.constant` is a literal, and here it is pinned coordinate-for-coordinate by a `Generic`
row — strictly stronger than membership. So the checked set is exactly the ABSORBED bases. -/

/-- `Pallas.Params.b`. `Params.a = 0`, so the `a·x` term of `assert_on_curve` folds away; a curve
with `a ≠ 0` would need one more half and one more variable, and this is where that would go. -/
def PALLAS_B : Nat := 5

/-- `assert_on_curve (x, y)` as three `Generic` halves: `x2 = x·x`, `x3 = x2·x`, and
`y·y − x3 − b = 0` — the `assert_square` with the linear combination folded into the coefficients,
which is what Snarky's `Basic.Square` emits. -/
def onCurveHalves (s : StepShape) (k : Nat) (vx vy : PVar) :
    List (List (Option PVar) × List Int) :=
  [ ([some vx, some vx, some (vOcX2 s k)], cMul)
  , ([some (vOcX2 s k), some vx, some (vOcX3 s k)], cMul)
  , ([some vy, some vy, some (vOcX3 s k)], [0, 0, -1, 1, -(PALLAS_B : Int)]) ]

/-- The `k`-th CHECKED point's coordinate VARIABLES: the `absRoundList` fold bases, `t_comm`'s
`tCommN` chunks, and — since the R1 interleaving — `sg_old[0]` and `delta`. Every SUPPLIED commitment
the transcript swallows, and no other. -/
def onCVar (s : StepShape) (k : Nat) : PVar × PVar :=
  let l := (absRoundList s).length
  let t := l + tCommN s
  if k < l then let r := (absRoundList s).getD k 0; (ipx s (qT s r), ipy s (qT s r))
  else if k < t then (vTcX s (k - l), vTcY s (k - l))
  else if k == t then (ipx s (qInit s), ipy s (qInit s))
  else (ipx s (qDel s), ipy s (qDel s))

/-- **R4's on-curve rows** — one `assert_on_curve` per ABSORBED commitment, over the very coordinate
variables the transcript absorbed and the `EndoMul` (or, for `t_comm`, the `VarBaseMul`) chain
multiplies. -/
def onCurveRows (s : StepShape) : List SRow :=
  packHalves ((List.range (nOnC s)).flatMap (fun k =>
    let v := onCVar s k
    onCurveHalves s k v.1 v.2))

/-- **`Scalar_challenge.endo`'s SEED PINS**, two `Generic` halves per round
(`scalar_challenge.ml:232,235`): `endo·xt − xq = 0` and `n_acc = Field.zero`. ⚑ Both cells were free
witnesses until 2026-08-02 — `vQN r 0` in exactly R3's way (the counter closes on the challenge from
`16^{ipaBlocks}·n₀ + bits`, so a free `n₀` buys any bit vector), and `vQEndo r` is new because the
seed's second operand did not exist as a variable at all. -/
def seedPinHalves (s : StepShape) (sl : EndoSlots) : List (List (Option PVar) × List Int) :=
  [ ([some (ipx s sl.base), none, some sl.endoX],
     [ (Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo : Int), 0, -1, 0, 0 ])
  , ([some (sl.n 0), none, none], cConst 0) ]

def ipaSeedPinRows (s : StepShape) : List SRow :=
  packHalves ((List.range s.ipaRounds).flatMap (fun r => seedPinHalves s (roundSlots s r))
              ++ seedPinHalves s (lhsSlots s))

/-- **Round `r`'s two `Ops.add_fast`s**: `p = t + φ(t)` and `acc₀ = p + p`. The probe between them
keeps every `CompleteAdd` run at length 1 and materialises `p` as a σ-only boundary value. ⚑ `φ(t)`'s
`y` IS `t`'s — `(seal (Field.scale xt Endo.base), yt)` — so the row reads `ipy (qT r)` at cols 1
AND 3, which is upstream's own shape and not a wiring accident. -/
def endoSeedRows (s : StepShape) (sl : EndoSlots) (T : Nat × Nat) (wired : Bool) : List SRow :=
  let q := endoQ T
  let p := endoP T
  [ caRow (ipx s sl.base, ipy s sl.base) (sl.endoX, ipy s sl.base)
          (ipx s sl.p, ipy s sl.p) (completeAddWitness T.1 T.2 q.1 q.2)
  , probeRow wired (ipx s sl.p) (ipy s sl.p)
  , caRow (ipx s sl.p, ipy s sl.p) (ipx s sl.p, ipy s sl.p)
          (ipx s (sl.acc 0), ipy s (sl.acc 0)) (completeAddWitness p.1 p.2 p.1 p.2) ]

def ipaSeedRows (s : StepShape) (v : IpaData) (wired : Bool) (r : Nat) : List SRow :=
  endoSeedRows s (roundSlots s r) (v.bases.getD r (0, 0)) wired

/-- ⚑ **`check_bulletproof`'s TAIL** (`step_verifier.ml:321-327`), the consumer that makes `delta` an
absorbed word something READS:

    absorb sponge PC delta ;
    let c = squeeze_scalar sponge in
    let lhs = let cq = Scalar_challenge.endo q c in cq + delta in

One `Scalar_challenge.endo` over the fold output `q = qSum (ipaRounds−1)` at the LAST transcript
squeeze, seeded at `scalar_challenge.ml:230-235` like every other round, then one `Ops.add_fast` with
`delta` — whose two coordinate variables ARE transcript block `oDelta`'s absorbed words.

⚠ WHAT THIS DOES NOT DO, at the point of use: `lhs` is not compared with `rhs`. `equal_g lhs rhs`
(`:340`) is the IPA opening's own equality and `rhs` needs `scale_fast2 u advice.b`,
`challenge_polynomial_commitment`, `z_1`, `z_2` and `Generators.h` — that is `verified` (#11), still a
witnessed boolean here. What IS closed is that `delta` and `c` are no longer words the sponge eats
and nothing reads: bend either and this ladder's own gate polynomials move. -/
def lhsRows (s : StepShape) (v : IpaData) (wired : Bool) : List SRow :=
  let sl := lhsSlots s
  endoSeedRows s sl (v.sums.getLastD (0, 0)) wired
  ++ endoRoundRows s sl v.lhsBlks
  ++ [ probeRow wired (ipx s (sl.acc s.ipaBlocks)) (ipy s (sl.acc s.ipaBlocks))
     , caRow (ipx s (sl.acc s.ipaBlocks), ipy s (sl.acc s.ipaBlocks))
             (ipx s (qDel s), ipy s (qDel s))
             (ipx s (qLhsOut s), ipy s (qLhsOut s)) v.lhsAdd
     , probeRow wired (ipx s (qLhsOut s)) (ipy s (qLhsOut s)) ]

/-- **R4's rows.** -/
def ipaRows (s : StepShape) (v : IpaData) (wired : Bool) : List SRow :=
  ipaBaseRows s v
  ++ ipaSeedPinRows s
  ++ onCurveRows s
  ++ (List.range s.ipaRounds).flatMap (fun r =>
       ipaSeedRows s v wired r
       ++ ipaRoundRows s v r
       ++ [probeRow wired (ipx s (qAcc s r s.ipaBlocks)) (ipy s (qAcc s r s.ipaBlocks))]
       ++ [ipaAddRow s v r]
       ++ [probeRow wired (ipx s (qSum s r)) (ipy s (qSum s r))])
  ++ lhsRows s v wired

/-! ## §6b — `Common.ft_comm`'s MSM: the sub-circuit that makes `t_comm` MEAN something.

`common.ml:238-256`, verbatim:

    let ft_comm ~add:( + ) ~scale ~endoscale ~negate ~verification_key:m ~alpha ~plonk ~t_comm =
      let ( * ) x g = scale g x in
      let _, [ sigma_comm_last ] = Vector.split m.sigma_comm (…) in
      let f_comm = List.reduce_exn ~f:( + ) [ plonk.perm * sigma_comm_last ] in
      let chunked_t_comm =
        let n = Array.length t_comm in
        let res = ref t_comm.(n - 1) in
        for i = n - 2 downto 0 do res := t_comm.(i) + scale !res plonk.zeta_to_srs_length done ;
        !res
      in
      f_comm + chunked_t_comm + negate (scale chunked_t_comm plonk.zeta_to_domain_size)

instantiated at `step_verifier.ml:587-591` with `~add:Ops.add_fast ~scale:scale_fast2
~negate:Inner_curve.negate ~verification_key:m ~plonk ~t_comm`, and `scale_fast2 p s = Ops.scale_fast2
p s ~num_bits:Field.size_in_bits` (`:240-242`) — **255 bits, uniformly, all eight of them.** So
`chunks_needed ~num_bits:254 = 51` five-bit chunks per scale (`plonk_curve_ops.ml:66-70,254-257`).

⚑ **WHY THIS IS THE RUNG AND NOT A ROW COUNT.** Until 2026-08-02 `t_comm`'s seven commitments were
seven `msgVal` fixtures: free variables the transcript ate and nothing read. The previous lane
refused to absorb them on their own and was right to — an absorbed commitment no sub-circuit CONSUMES
is still ground freely, and the only thing absorbing it buys is a smaller number in a census. §12b″
exhibits the grind that was open, and shows what refuses it now.

## THE EIGHT SCALES AND WHERE EACH BASE COMES FROM

    k       base                                  scalar                     provenance of the base
    0       sigma_comm_last = sigma_comm[6]       plonk.perm                 §3c's own pinned var
    1       t_comm[n−1]                           zeta_to_srs_length         TRANSCRIPT-ABSORBED
    2..n−1  resₙ₋ₖ (add k−2's output)             zeta_to_srs_length         COMPUTED
    n       chunked_t_comm = res₀                 zeta_to_domain_size        COMPUTED

and `tCommN + 1` `Ops.add_fast`s: the `n−1` Horner adds `resₙ₋₂₋ₐ = t_comm[n−2−a] + scale(a+1)`,
then `f_comm + chunked_t_comm`, then `+ negate (…)`. The last one's OUTPUT is R4 round `FTC_ROUND`'s
base — `combine_split_commitments`' commitment 3 (`step_verifier.ml:606`), which was an
`Inner_curve.constant` carrying the real block's `COMBINE_XY[3]` and is now derived.

## ⚑ THE SCALARS, AND THE ONE DIVERGENCE FROM UPSTREAM — NAMED, AND IT IS A STRENGTHENING

Upstream's `plonk` here is `unfinalized.deferred_values.plonk` mapped through
`Plonk.In_circuit.to_wrap` (`step_verifier.ml:1264-1267`), whose `'fp` is
`Other_field.t Shifted_value.Type2.t` — i.e. **`(Field.t * Boolean.var)` statement words over the
OTHER field** (`impls.ml:50-57`). Nothing in the step circuit constrains them: `Plonk_checks.checked`
(R6/R8) compares the **`Fp` Type1** twins of the same deferred values, and the `Fq` Type2 twins are
checked by the NEXT wrap proof. So upstream's `ft_comm` multiplies by three values a step-circuit
prover chooses.

Here they are R6's OWN derived cells — `Plonk_checks.checked`'s `perm` and the `ζ^n` slot — split
into `(s_div_2, s_odd)` by a row that reads that cell. That is strictly MORE constrained than
upstream inside this circuit, and it is why `ft_comm`'s output is a function of the transcript rather
than of a witness.
⚠ **THE RESIDUE, stated rather than absorbed.** `Shifted_value.Type2`'s shift lives in the OTHER
field (`shifted_value.ml:178-188`: `to_field t = t + 2^{size_in_bits}`), so what this ladder computes
is `[s + 2^255]·g` for the wired `s` — upstream's own emitted arithmetic, with the shift's
cancellation an `Fq`-side fact this circuit cannot see. And ⚑ at `log2n = srs_length_log2 = 16`
(`FT_LOG2N`; `plonk_checks.ml:496-497`) `zeta_to_srs_length` and `zeta_to_domain_size` are the SAME
field element, so the Horner steps and the closing scale share one scalar here; at a shape where the
wrap domain and the step SRS length differ they would not, and that is a shape fact, not a wiring
one. -/

/-- The `5·FTC_CHUNKS = 255` bits of `v`, MSB-first — `scale_fast_unpack`'s `bits_msb`
(`plonk_curve_ops.ml:151-156`), at `actual_bits_used = chunks_needed · 5`. -/
def ftcBitsOf (v : Nat) : List Nat :=
  (List.range (5 * FTC_CHUNKS)).map (fun k => v / 2 ^ (5 * FTC_CHUNKS - 1 - k) % 2)

/-- The two scalar cells `ft_comm` reads, as VARIABLE + VALUE. Passed in rather than reached for, so
§6b has no forward dependency on §8d's compiled program. -/
structure FtcWire where
  /-- `plonk.perm` — R6's `Plonk_checks.checked` slot. -/
  permV : PVar
  permVal : Nat
  /-- `plonk.zeta_to_srs_length` = `plonk.zeta_to_domain_size` — R6's `ζ^n` slot. -/
  zetaV : PVar
  zetaVal : Nat
  deriving Repr, Inhabited

/-- Scalar block `c`'s variable and value. -/
def ftcScalV (W : FtcWire) (c : Nat) : PVar := if c == 0 then W.permV else W.zetaV
def ftcScalVal (W : FtcWire) (c : Nat) : Nat := if c == 0 then W.permVal else W.zetaVal

/-- One evaluated `scale_fast2` (`plonk_curve_ops.ml:251-267`). -/
structure FtcTerm where
  /-- the `scale_fast_unpack` ladder: base, 256 accumulator points, 255 slopes, 256 counters. -/
  td : TermData
  bits : List Nat
  /-- `Ops.add_fast g g` — `scale_fast_unpack`'s own `acc := ref (add_fast base base)` (`:157`).
  Without this row `acc₀` is a free witness and the ladder's OUTPUT is the prover's. -/
  dblCells : List Nat
  /-- `add_fast h (G.negate g)` — the `s_odd = 0` branch (`:267`). -/
  hMg : Nat × Nat
  hMgCells : List Nat
  /-- `G.if_ s_odd ~then_:h ~else_:(h − g)`. -/
  res : Nat × Nat
  deriving Repr, Inhabited

/-- `Common.ft_comm`, evaluated. -/
structure FtcData where
  terms : List FtcTerm
  /-- the `tCommN` `Ops.add_fast` outputs that get variables: the `n−1` Horner partials, then
  `f_comm + chunked_t_comm`. -/
  adds : List (Nat × Nat)
  /-- …and all `tCommN + 1` of their cell vectors, the last being the closing subtraction. -/
  addCells : List (List Nat)
  /-- ⚑ **`Common.ft_comm`.** R4 round `FTC_ROUND`'s base. -/
  out : Nat × Nat
  deriving Repr, Inhabited

/-- `sigma_comm_last` — `Vector.split m.sigma_comm` hands `common.ml:243-245` the SEVENTH permutation
commitment, which is `INDEX_XY[6]` and the one plonk-index commitment the fold does not carry. -/
def ftcSigma : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD 6 (0, 0)
def ftcTc (i : Nat) : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.getD i (0, 0)

/-- ONE `scale_fast2` over base `g` and scalar `sv`. -/
def ftcScaleTerm (g : Nat × Nat) (sv : Nat) : FtcTerm :=
  let bits := ftcBitsOf (sv / 2)
  let td := runVbm g (dblA g) bits
  let h := td.accs.getLastD (0, 0)
  let ng : Nat × Nat := (g.1, Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub 0 g.2)
  let hc := completeAddWitness h.1 h.2 ng.1 ng.2
  let hmg : Nat × Nat := (hc.getD 4 0, hc.getD 5 0)
  { td := td, bits := bits
  , dblCells := completeAddWitness g.1 g.2 g.1 g.2
  , hMg := hmg, hMgCells := hc
  , res := if sv % 2 == 1 then h else hmg }

/-- **`Common.ft_comm`, run** over a `t_comm` ACCESSOR. The Horner is evaluated in `common.ml`'s own
`downto` order, so term `k ≥ 2`'s base is add `k−2`'s output and the two loops are ONE fold.
Parametrised so §12b″ can re-run it on a prover's substituted quotient commitment. -/
def runFtcWith (s : StepShape) (W : FtcWire) (ftcTc : Nat → Nat × Nat) : FtcData :=
  let n := tCommN s
  let t0 := ftcScaleTerm ftcSigma W.permVal
  let st := (List.range n).foldl
    (fun (acc : List FtcTerm × List (Nat × Nat) × List (List Nat)) j =>
      let k := j + 1
      let g := if k == 1 then ftcTc (n - 1) else acc.2.1.getD (k - 2) (0, 0)
      let tk := ftcScaleTerm g W.zetaVal
      if k + 1 ≤ n then
        let l := ftcTc (n - 1 - k)
        let c := completeAddWitness l.1 l.2 tk.res.1 tk.res.2
        (acc.1 ++ [tk], acc.2.1 ++ [(c.getD 4 0, c.getD 5 0)], acc.2.2 ++ [c])
      else (acc.1 ++ [tk], acc.2.1, acc.2.2))
    ([], [], [])
  let terms := t0 :: st.1
  let chunked := st.2.1.getD (n - 2) (0, 0)
  let cF := completeAddWitness t0.res.1 t0.res.2 chunked.1 chunked.2
  let fc : Nat × Nat := (cF.getD 4 0, cF.getD 5 0)
  let qn := (terms.getD n default).res
  let cO := completeAddWitness fc.1 fc.2 qn.1
              (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub 0 qn.2)
  { terms := terms, adds := st.2.1 ++ [fc], addCells := st.2.2 ++ [cF, cO]
  , out := (cO.getD 4 0, cO.getD 5 0) }

/-- …at the block's OWN quotient commitments, which is the only instance the assembly emits. -/
def runFtc (s : StepShape) (W : FtcWire) : FtcData := runFtcWith s W ftcTc

/-- Term `k`'s base-point VARIABLES. -/
def ftcBaseVar (s : StepShape) (k : Nat) : PVar × PVar :=
  if k == 0 then (vIdxX s 6, vIdxY s 6)
  else if k == 1 then (vTcX s (tCommN s - 1), vTcY s (tCommN s - 1))
  else (ftcAddX s (k - 2), ftcAddY s (k - 2))

/-- Term `k`'s chunk `j` — the same two-row `VarBaseMul` shape R3 uses. ⚑ Chunk 0's `Zero` row wires
col 2 (bit `5j+0`, the MSB) to `ftcTop`, so `scale_fast2`'s `bits_lsb.(254) = 0`
(`plonk_curve_ops.ml:262-265`) is a real row: without it the counter identity has two solutions mod
`p` and the prover picks the point. -/
def ftcChunkRows (s : StepShape) (d : FtcData) (k j : Nat) : List SRow :=
  let tm := d.terms.getD k default
  let td := tm.td
  let ax : Nat → Int := fun i => ((td.accs.getD i (0, 0)).1 : Int)
  let ay : Nat → Int := fun i => ((td.accs.getD i (0, 0)).2 : Int)
  let bt : Nat → Int := fun i => (td.slopes.getD i 0 : Int)
  let bi : Nat → Int := fun i => (tm.bits.getD i 0 : Int)
  let g := ftcBaseVar s k
  [ { kind := .varBaseMul
    , perm := [ some g.1, some g.2
              , some (ftcAccX s k j), some (ftcAccY s k j)
              , some (ftcN s k j), some (ftcN s k (j+1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (ftcAccX s k (j+1)), some (ftcAccY s k (j+1))
              , (if j == 0 then some (ftcTop s k) else none), none, none, none, none ]
    , advice := (if j == 0 then [] else [(2, bi (5*j))])
                ++ [ (3, bi (5*j+1)), (4, bi (5*j+2)), (5, bi (5*j+3)), (6, bi (5*j+4))
                   , (7, bt (5*j)), (8, bt (5*j+1)), (9, bt (5*j+2)), (10, bt (5*j+3))
                   , (11, bt (5*j+4)) ] } ]

/-- **`Shifted_value.Type2`'s own rows**, once per DISTINCT scalar: `Field.Assert.equal (2·s_div_2 +
s_odd) s` (`plonk_curve_ops.ml:290-291`) and `Boolean.typ`'s check on `s_odd`. ⚑ The `s` these read
is R6's derived cell, not a statement word. -/
def ftcScalRows (s : StepShape) (W : FtcWire) (wired : Bool) : List SRow :=
  packHalves ((List.range N_FTC_SCAL).flatMap (fun c =>
    [ ([some (ftcScalV W c), some (ftcDiv2 s c), some (ftcOdd s c)], cSplit 1)
    , ([some (ftcOdd s c), some (ftcOdd s c), some (ftcOdd s c)], cMul) ]))
  ++ (List.range N_FTC_SCAL).map (fun c => probeRow wired (ftcDiv2 s c) (ftcOdd s c))

/-- **`let n_acc = ref Field.zero`** for `ft_comm`'s own ladders (`plonk_curve_ops.ml:158`), one
`Generic` half per `scale_fast2`. ⚑ §6b emitted `:157`'s `add_fast base base` from the start and NOT
`:158`'s counter seed, so `ftcN k 0` was a free witness and the closing
`Field.Assert.equal !n_acc scalar` (`:208`) — the wire that makes the ladder multiply by R6's derived
`perm` / `ζ^n` — was one equation in two unknowns: the prover picks the 255 bits and solves for
`ftcN k 0`. The same defect R3 carried at `vSN i 0`, in the ladder that computes `ft_comm`. -/
def ftcNZeroRows (s : StepShape) : List SRow :=
  packHalves ((List.range (ftcTerms s)).map (fun k =>
    ([some (ftcN s k 0), none, none], cConst 0)))

/-- **Term `k`'s rows.** The `G.if_` mux is `d = h − (h−g) ; m = s_odd·d ; res = (h−g) + m` per
coordinate — Snarky's `Field.if_` (`else_ + b·(then_ − else_)`) with the difference sealed, because a
double-`Generic` half carries three variables and `res − else_ − b·(then_ − else_)` needs four. -/
def ftcTermRows (s : StepShape) (d : FtcData) (wired : Bool) (k : Nat) : List SRow :=
  let tm := d.terms.getD k default
  let g := ftcBaseVar s k
  let hx := ftcAccX s k FTC_CHUNKS
  let hy := ftcAccY s k FTC_CHUNKS
  let od := ftcOdd s (ftcScalOf k)
  packHalves
    [ ([some g.2, some (ftcNegY s k), none], [1, 1, 0, 0, 0])
    , ([some (ftcTop s k), none, none], cConst 0)
    , ([some hx, some (ftcHmX s k), some (ftcDX s k)], [1, -1, -1, 0, 0])
    , ([some od, some (ftcDX s k), some (ftcMX s k)], cMul)
    , ([some (ftcHmX s k), some (ftcMX s k), some (ftcResX s k)], cAdd)
    , ([some hy, some (ftcHmY s k), some (ftcDY s k)], [1, -1, -1, 0, 0])
    , ([some od, some (ftcDY s k), some (ftcMY s k)], cMul)
    , ([some (ftcHmY s k), some (ftcMY s k), some (ftcResY s k)], cAdd) ]
  ++ [ caRow g g (ftcAccX s k 0, ftcAccY s k 0) tm.dblCells ]
  ++ ((List.range FTC_CHUNKS).flatMap (ftcChunkRows s d k))
  ++ [ probeRow wired hx hy
     , caRow (hx, hy) (g.1, ftcNegY s k) (ftcHmX s k, ftcHmY s k) tm.hMgCells
     , probeRow wired (ftcResX s k) (ftcResY s k) ]

/-- **The `Ops.add_fast` chain**, in `common.ml`'s order — and its LAST output is the fold's own
round-`FTC_ROUND` base variable, which is the whole point of the rung. -/
def ftcAddRows (s : StepShape) (d : FtcData) (wired : Bool) : List SRow :=
  let n := tCommN s
  let cel : Nat → List Nat := fun a => d.addCells.getD a []
  (List.range (n - 1)).flatMap (fun a =>
    [ caRow (vTcX s (n - 2 - a), vTcY s (n - 2 - a))
            (ftcResX s (a + 1), ftcResY s (a + 1))
            (ftcAddX s a, ftcAddY s a) (cel a)
    , probeRow wired (ftcAddX s a) (ftcAddY s a) ])
  ++ [ caRow (ftcResX s 0, ftcResY s 0) (ftcAddX s (n - 2), ftcAddY s (n - 2))
             (ftcAddX s (n - 1), ftcAddY s (n - 1)) (cel (n - 1))
     , probeRow wired (ftcAddX s (n - 1)) (ftcAddY s (n - 1)) ]
  ++ packHalves [ ([some (ftcResY s n), some (ftcNegQ s), none], [1, 1, 0, 0, 0]) ]
  ++ [ caRow (ftcAddX s (n - 1), ftcAddY s (n - 1)) (ftcResX s n, ftcNegQ s)
             (ipx s (qT s FTC_ROUND), ipy s (qT s FTC_ROUND)) (cel n)
     , probeRow wired (ipx s (qT s FTC_ROUND)) (ipy s (qT s FTC_ROUND)) ]

/-- **§6b's rows.** -/
def ftcRows (s : StepShape) (W : FtcWire) (d : FtcData) (wired : Bool) : List SRow :=
  ftcScalRows s W wired
  ++ ftcNZeroRows s
  ++ (List.range (ftcTerms s)).flatMap (ftcTermRows s d wired)
  ++ ftcAddRows s d wired

/-! ## §8 — R5, the DEFERRED `b(ζ)` and the CLOSING public ties.

`b(ζ) = ∏_k (1 + u_k · ζ^{2^{bRounds−1−k}})` — `Wrap.challenge_polynomial` (`wrap.ml:15-17`), the
product `KimchiVerify.bEvalSq` folds. `ζ` is challenge 0 and `u_k` is challenge `k+1`, so the
deferred rung READS R2's outputs rather than being a private arithmetic island. -/

structure DefData where
  zs : List Nat
  facs : List Nat
  accs : List Nat
  /-- the claimed evaluations at ζ and ζω (the `cipEvals` poly columns). -/
  ez : List Nat
  ew : List Nat
  dk : List Nat
  ck : List Nat
  tk : List Nat
  ca : List Nat
  deriving Repr, Inhabited

/-- Claimed evaluation of column `k` at point `pt ∈ {0,1}` — a deterministic fixture standing for a
column of the previous proof's `PointEvaluations`. -/
def evVal (k pt : Nat) : Nat := (11 + 2000003 * (2 * k + pt) + 7 * k * k) % pN

/-- ⚑ The column vector at ζ, with entry 3 — the `ft` column — OVERRIDDEN by R6's computed
`ft_eval0`. That is upstream's own wiring: `combine ~ft:ft_eval0 …` (`step_verifier.ml:1078-1083`)
folds `ft_eval0` into `combined_inner_product` as the fourth prefix column. The four-entry prefix is
`sg_old`×2, the public polynomial, `ft`; R6 reads only entries ≥ 4, so the override is not
circular. -/
def evZOf (ftVal : Nat) (k : Nat) : Nat := if k == 3 then ftVal else evVal k 0

/-- ⚑ `xi` and `rr` are the DEFERRED multipliers of §8g — `to_field_checked` of the statement's ξ
word and of the fr-sponge's second squeeze — NOT transcript challenges. The fold is `fed` by the
squeeze, not merely checked against it. -/
def runDef (s : StepShape) (d : SpongeData) (ftVal : Nat) (xi rr : Nat) : DefData :=
  let zs := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [liftOf s d s.zetaChal]
  let st := (List.range s.bRounds).foldl
    (fun (acc : List Nat × List Nat) k =>
      let f := fAdd 1 (fMul (liftOf s d (s.uChal k)) (zs.getD (s.bRounds - 1 - k) 0))
      (acc.1 ++ [f], acc.2 ++ [fMul (acc.2.getLastD 1) f]))
    ([], [1])
  let ez := (List.range s.cipEvals).map (fun k => evZOf ftVal k)
  let ew := (List.range s.cipEvals).map (fun k => evVal k 1)
  let dk := (List.range s.cipEvals).map (fun k => fMul rr (ew.getD k 0))
  let ck := (List.range s.cipEvals).map (fun k => fAdd (ez.getD k 0) (dk.getD k 0))
  -- Horner from the TOP: `accᵢ₊₁ = accᵢ·ξ + c_{n−1−i}` closes to `Σ_k ξ^k · c_k`, which IS
  -- `KimchiVerify.combinedInnerProduct` (pinned in §12).
  let hz := (List.range s.cipEvals).foldl
    (fun (acc : List Nat × List Nat) i =>
      let t := fMul (acc.2.getLastD 0) xi
      (acc.1 ++ [t], acc.2 ++ [fAdd t (ck.getD (s.cipEvals - 1 - i) 0)]))
    ([], [0])
  { zs := zs, facs := st.1, accs := st.2
  , ez := ez, ew := ew, dk := dk, ck := ck, tk := hz.1, ca := hz.2 }

/-- **R5a's rows.** -/
def deferredRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vAcc s 0)) none none none none none (cConst 1 ++ cNil)
  , genericRow (some (vZ s 0)) (some (vLift s s.zetaChal)) none none none none (cEq ++ cNil) ]
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vZ s k)) (some (vZ s k)) (some (vZ s (k+1))) none none none (cMul ++ cNil))
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vLift s (s.uChal k))) (some (vZ s (s.bRounds - 1 - k))) (some (vFac s k))
                 (some (vAcc s k)) (some (vFac s k)) (some (vAcc s (k+1))) (cMulPlus1 ++ cMul))
  ++ [ probeRow wired (vAcc s s.bRounds) (vZ s s.bRounds) ]

/-- **R5a', `combined_inner_product`** — `Common.combined_evaluation` (`common.ml:258-…`), the
`2 × cipEvals` `mul_and_add`s. `cip = Σ_k ξ^k · (evₖ(ζ) + r · evₖ(ζω))`, assembled as a Horner fold
from the top over `Generic` rows, two per evaluation column:

    A(k)  half1  w₀=r      w₁=evₖ(ζω)  w₂=dₖ      dₖ = r · evₖ(ζω)
          half2  w₃=evₖ(ζ) w₄=dₖ       w₅=cₖ      cₖ = evₖ(ζ) + dₖ
    B(i)  half1  w₀=accᵢ   w₁=ξ        w₂=tᵢ      tᵢ = accᵢ · ξ
          half2  w₃=tᵢ     w₄=c_{n−1−i} w₅=accᵢ₊₁ accᵢ₊₁ = tᵢ + c_{n−1−i}

⚑ ξ and `r` are `vDLift 0` / `vDLift 1` — §8g's DEFERRED challenges, `to_field_checked` of the
statement's ξ word and of the fr-sponge's second squeeze (`step_verifier.ml:1012-1013`). Every
`Generic` half of this fold therefore hangs off the fr-sponge through σ, which is the retirement of
simplification #10. -/
def cipRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vCa s 0)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [ genericRow (some (vDLift s 1)) (some (vEw s k)) (some (vDk s k))
                   (some (vEz s k)) (some (vDk s k)) (some (vCk s k)) (cMul ++ cAdd) ])
  ++ (List.range s.cipEvals).flatMap (fun i =>
      [ genericRow (some (vCa s i)) (some (vDLift s 0)) (some (vTk s i))
                   (some (vTk s i)) (some (vCk s (s.cipEvals - 1 - i))) (some (vCa s (i+1)))
                   (cMul ++ cAdd) ])
  ++ [ probeRow wired (vCa s s.cipEvals) (vCk s 0) ]
  -- ⚑ `absorb sponge Scalar advice.combined_inner_product` (`:79-81,256`) absorbs the FIELD half and
  -- then a `Bits [b]` — `Other_field.Packed`'s `Boolean.var`. `Boolean.typ`'s own check is `b² = b`,
  -- and without it the "bit" is an arbitrary field element the prover feeds the sponge.
  ++ [ genericRow (some (vCipBit s)) (some (vCipBit s)) (some (vCipBit s)) none none none
                  (cMul ++ cNil)
     , probeRow wired (vCipBit s) (vCipShift s) ]

/-! ## §8b — the ARITHMETIC COMPILER: a straight-line program over `Generic` rows.

`ft_eval0`, `Plonk_checks.checked` and the linearization constant term are pure scalar arithmetic
over the previous proof's evaluations, and Snarky emits them as `Generic` rows
(`plonk_constraint_system.ml`'s `Basic.R1CS`/`Square`/`Boolean` all land on the double generic gate).
Rather than hand-writing several hundred rows, this compiles a STRAIGHT-LINE PROGRAM: slot `i` owns
one circuit variable, each operation is one HALF of a double-`Generic` row, and two consecutive
operations share a row.

⚑ THE PROGRAM IS CHECKED AGAINST THE VALUE LAYER, NOT TRUSTED. `KimchiVerify`'s constraint bodies —
read-only transcriptions of `proof-systems` — are evaluated at the SAME inputs in §12, **list by
list**, and the compiled program's slot values must agree elementwise. A transcription slip in any
one of the 67 constraint bodies goes red there, not silently into a proof. -/

/-- One straight-line arithmetic operation. Slot `i` is the `i`-th entry of the program. -/
inductive AOp where
  /-- ALIAS an existing circuit variable — no row, no new variable. This is how the program reaches
  the sponge's challenges and the previous proof's evaluation columns. -/
  | inp (v : PVar)
  /-- A FREE witness cell: no defining row. Only what the program asserts about it constrains it —
  the witnessed-inverse device (`KimchiVerify` §9b's `denomInv`). -/
  | wit (val : Nat)
  /-- A field constant, pinned by the row `w₀ = k`. -/
  | lit (val : Nat)
  | add (i j : Nat)
  | sub (i j : Nat)
  | mul (i j : Nat)
  /-- ASSERT slot `i` = slot `j`; the produced slot is inert. -/
  | aeq (i j : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- `w₂ = w₀ − w₁`. -/ def cSub : List Int := [1, -1, -1, 0, 0]

/-- The program builder. -/
abbrev AM := StateM (Array AOp)

def em (o : AOp) : AM Nat := do
  let st ← get
  set (st.push o)
  pure st.size

def eLit (k : Nat) : AM Nat := em (.lit k)
def eWit (k : Nat) : AM Nat := em (.wit k)
def eInp (v : PVar) : AM Nat := em (.inp v)
def eAdd (a b : Nat) : AM Nat := em (.add a b)
def eSub (a b : Nat) : AM Nat := em (.sub a b)
def eMul (a b : Nat) : AM Nat := em (.mul a b)
def eEq (a b : Nat) : AM Nat := em (.aeq a b)

/-- `x − y` over `Fp`. -/
def fSub (x y : Nat) : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub x y

/-- Evaluate the program. `lk` resolves `.inp` variables out of the surrounding circuit. -/
def aEval (lk : PVar → Int) (prog : Array AOp) : Array Nat :=
  prog.foldl (fun (vs : Array Nat) op =>
    vs.push (match op with
      | .inp v => (lk v).toNat % pN
      | .wit x => x % pN
      | .lit x => x % pN
      | .add i j => fAdd (vs.getD i 0) (vs.getD j 0)
      | .sub i j => fSub (vs.getD i 0) (vs.getD j 0)
      | .mul i j => fMul (vs.getD i 0) (vs.getD j 0)
      | .aeq i _ => vs.getD i 0)) #[]

/-- Slot `i`'s circuit variable. `.inp` aliases; everything else owns `xv (base + i)`. -/
def aVarAt (base : Nat) (prog : Array AOp) (i : Nat) : PVar :=
  match prog.getD i default with
  | .inp v => v
  | _ => xv (base + i)

/-- The slots that need a `Generic` half (`.inp` and `.wit` need none). -/
def aHalfSlots (prog : Array AOp) : List Nat :=
  (List.range prog.size).filter (fun i =>
    match prog.getD i default with | .inp _ => false | .wit _ => false | _ => true)

/-- Slot `i`'s half: its three permutation columns and its five coefficients. -/
def aHalf (base : Nat) (prog : Array AOp) (i : Nat) : List (Option PVar) × List Int :=
  let V := aVarAt base prog
  match prog.getD i default with
  | .lit k => ([some (V i), none, none], cConst (k : Int))
  | .add a b => ([some (V a), some (V b), some (V i)], cAdd)
  | .sub a b => ([some (V a), some (V b), some (V i)], cSub)
  | .mul a b => ([some (V a), some (V b), some (V i)], cMul)
  | .aeq a b => ([some (V a), some (V b), none], cEq)
  | _ => ([none, none, none], cNil)

/-- The program's rows: two halves per double-`Generic` row, a `cNil` tail half when odd. -/
def aRows (base : Nat) (prog : Array AOp) : List SRow :=
  let sl := aHalfSlots prog
  (List.range ((sl.length + 1) / 2)).map (fun r =>
    let h1 := aHalf base prog (sl.getD (2 * r) 0)
    let h2 := if 2 * r + 1 < sl.length then aHalf base prog (sl.getD (2 * r + 1) 0)
              else (([none, none, none] : List (Option PVar)), cNil)
    ({ kind := .generic, perm := h1.1 ++ h2.1 ++ [none], coeffs := h1.2 ++ h2.2 } : SRow))

/-- The program's contribution to the variable environment. -/
def aEnvOf (base : Nat) (prog : Array AOp) (vals : Array Nat) : VarEnv :=
  (List.range prog.size).filterMap (fun i =>
    match prog.getD i default with
    | .inp _ => none
    | _ => some (xv (base + i), (vals.getD i 0 : Int)))

/-! ## §8c — the SIX GATE CONSTRAINT BODIES, compiled.

Each mirrors a `KimchiVerify` body one-for-one, and §12 pins the compiled values against that body's
own output list. These are the factors the six selectors multiply in the linearization constant term
(`gateLinConst`, `argument.rs:201-213`). -/

/-- `x⁷` — kimchi's Poseidon S-box (`PlonkSpongeConstantsKimchi::PERM_SBOX = 7`). 4 muls. -/
def pSbox (x : Nat) : AM Nat := do
  let x2 ← eMul x x
  let x4 ← eMul x2 x2
  let x6 ← eMul x4 x2
  eMul x6 x

/-- `poseidonLaneConstraint`: `target − (rc + Σ_c mds[j][c]·sbox(source_c))`, sboxes precomputed. -/
def pLane (mdsRow : List Nat) (rc : Nat) (sb : List Nat) (target : Nat) : AM Nat := do
  let t0 ← eMul (mdsRow.getD 0 0) (sb.getD 0 0)
  let t1 ← eMul (mdsRow.getD 1 0) (sb.getD 1 0)
  let t2 ← eMul (mdsRow.getD 2 0) (sb.getD 2 0)
  let s01 ← eAdd t0 t1
  let s ← eAdd s01 t2
  let r ← eAdd rc s
  eSub target r

/-- The 15 `Poseidon` constraints (`poseidonConstraints`), in emission order. -/
def pPoseidon (mdsS : List (List Nat)) (c w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let cc := fun i => c.getD i 0
  let wnn := fun i => wn.getD i 0
  let sb ← (List.range 15).foldlM (fun acc i => do let s ← pSbox (ww i); pure (acc ++ [s])) []
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
  spec.foldlM (fun acc q => do let k ← pLane (m q.1) (cc q.2.1) q.2.2.1 q.2.2.2; pure (acc ++ [k])) []

/-- The 7 `CompleteAdd` constraints (`completeAddConstraints`). -/
def pCompleteAdd (one : Nat) (w : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let x1 := ww 0; let y1 := ww 1; let x2 := ww 2; let y2 := ww 3
  let x3 := ww 4; let y3 := ww 5; let inf := ww 6; let sameX := ww 7
  let s := ww 8; let infZ := ww 9; let x21Inv := ww 10
  let x21 ← eSub x2 x1
  let y21 ← eSub y2 y1
  let x1sq ← eMul x1 x1
  let nsx ← eSub one sameX
  let a ← eMul x21Inv x21
  let k0 ← eSub a nsx
  let k1 ← eMul sameX x21
  let ss ← eAdd s s
  let ssy ← eMul ss y1
  let q2 ← eAdd x1sq x1sq
  let t1a ← eSub ssy q2
  let t1 ← eSub t1a x1sq
  let p1 ← eMul sameX t1
  let x21s ← eMul x21 s
  let t2 ← eSub x21s y21
  let p2 ← eMul nsx t2
  let k2 ← eAdd p1 p2
  let sx ← eAdd x1 x2
  let sx3 ← eAdd sx x3
  let s2v ← eMul s s
  let k3 ← eSub sx3 s2v
  let d ← eSub x1 x3
  let sd ← eMul s d
  let e1 ← eSub sd y1
  let k4 ← eSub e1 y3
  let f ← eSub sameX inf
  let k5 ← eMul y21 f
  let g ← eMul y21 infZ
  let k6 ← eSub g inf
  pure [k0, k1, k2, k3, k4, k5, k6]

/-- The 21 `VarbaseMul` constraints (`varBaseMulConstraints`). -/
def pVarBaseMul (one : Nat) (w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xT := ww 0; let yT := ww 1
  let accX := fun i => ([ww 2, ww 7, ww 9, ww 11, ww 13, wnn 0] : List Nat).getD i 0
  let accY := fun i => ([ww 3, ww 8, ww 10, ww 12, ww 14, wnn 1] : List Nat).getD i 0
  let bit := fun i => ([wnn 2, wnn 3, wnn 4, wnn 5, wnn 6] : List Nat).getD i 0
  let sl := fun i => ([wnn 7, wnn 8, wnn 9, wnn 10, wnn 11] : List Nat).getD i 0
  let nPrev := ww 4; let nNext := ww 5
  let acc ← (List.range 5).foldlM (fun a i => do let aa ← eAdd a a; eAdd (bit i) aa) nPrev
  let dec ← eSub nNext acc
  let rest ← (List.range 5).foldlM (fun out i => do
      let b := bit i; let s := sl i
      let ix := accX i; let iy := accY i
      let ox := accX (i + 1); let oy := accY (i + 1)
      let b2 ← eAdd b b
      let bSign ← eSub b2 one
      let ssq ← eMul s s
      let rxa ← eSub ssq ix
      let rx ← eSub rxa xT
      let t ← eSub ix rx
      let iy2 ← eAdd iy iy
      let ts ← eMul t s
      let u ← eSub iy2 ts
      let bb ← eMul b b
      let k0 ← eSub bb b
      let ixT ← eSub ix xT
      let l1 ← eMul ixT s
      let by' ← eMul bSign yT
      let r1 ← eSub iy by'
      let k1 ← eSub l1 r1
      let uu ← eMul u u
      let tt ← eMul t t
      let oxT ← eSub ox xT
      let q ← eAdd oxT ssq
      let ttq ← eMul tt q
      let k2 ← eSub uu ttq
      let oyiy ← eAdd oy iy
      let l3 ← eMul oyiy t
      let ixox ← eSub ix ox
      let r3 ← eMul ixox u
      let k3 ← eSub l3 r3
      pure (out ++ [k0, k1, k2, k3])) []
  pure (dec :: rest)

/-- The 11 DEPLOYED `EndosclMul` constraints (`endoMulConstraints … |>.take 11`, `proof-systems`
0.3.0's `CONSTRAINTS = 11` — the 12th distinct-point witness is NOT in the deployed constant term,
`gateLinConst`'s own `.take 11`). -/
def pEndoMul (one endo : Nat) (w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xt := ww 0; let yt := ww 1
  let xp := ww 4; let yp := ww 5; let n := ww 6
  let xr := ww 7; let yr := ww 8; let s1 := ww 9; let s3 := ww 10
  let b1 := ww 11; let b2 := ww 12; let b3 := ww 13; let b4 := ww 14
  let xs := wnn 4; let ys := wnn 5; let nNext := wnn 6
  let em1 ← eSub endo one
  let t1 ← eMul b1 em1
  let u1 ← eAdd one t1
  let xq1 ← eMul u1 xt
  let t3 ← eMul b3 em1
  let u3 ← eAdd one t3
  let xq2 ← eMul u3 xt
  let b22 ← eAdd b2 b2
  let v2 ← eSub b22 one
  let yq1 ← eMul v2 yt
  let b42 ← eAdd b4 b4
  let v4 ← eSub b42 one
  let yq2 ← eMul v4 yt
  let s1sq ← eMul s1 s1
  let s3sq ← eMul s3 s3
  let n2 ← eAdd n n
  let d1 ← eAdd n2 b1
  let d1a ← eAdd d1 d1
  let d2 ← eAdd d1a b2
  let d2a ← eAdd d2 d2
  let d3 ← eAdd d2a b3
  let d3a ← eAdd d3 d3
  let d4 ← eAdd d3a b4
  let nC ← eSub d4 nNext
  let xpxr ← eSub xp xr
  let xrxs ← eSub xr xs
  let ysyr ← eAdd ys yr
  let yryp ← eAdd yr yp
  let k0 ← do let t ← eMul b1 b1; eSub t b1
  let k1 ← do let t ← eMul b2 b2; eSub t b2
  let k2 ← do let t ← eMul b3 b3; eSub t b3
  let k3 ← do let t ← eMul b4 b4; eSub t b4
  let k4 ← do let a ← eSub xq1 xp; let l ← eMul a s1; let r ← eSub yq1 yp; eSub l r
  let k5 ← do
    let xp2 ← eAdd xp xp
    let a ← eSub xp2 s1sq
    let a2 ← eAdd a xq1
    let m1 ← eMul xpxr s1
    let m2 ← eAdd m1 yryp
    let l ← eMul a2 m2
    let yp2 ← eAdd yp yp
    let r ← eMul yp2 xpxr
    eSub l r
  let k6 ← do
    let l ← eMul yryp yryp
    let p ← eMul xpxr xpxr
    let a ← eSub s1sq xq1
    let a2 ← eAdd a xr
    let r ← eMul p a2
    eSub l r
  let k7 ← do let a ← eSub xq2 xr; let l ← eMul a s3; let r ← eSub yq2 yr; eSub l r
  let k8 ← do
    let xr2 ← eAdd xr xr
    let a ← eSub xr2 s3sq
    let a2 ← eAdd a xq2
    let m1 ← eMul xrxs s3
    let m2 ← eAdd m1 ysyr
    let l ← eMul a2 m2
    let yr2 ← eAdd yr yr
    let r ← eMul yr2 xrxs
    eSub l r
  let k9 ← do
    let l ← eMul ysyr ysyr
    let p ← eMul xrxs xrxs
    let a ← eSub s3sq xq2
    let a2 ← eAdd a xs
    let r ← eMul p a2
    eSub l r
  pure [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, nC]

/-- The 11 `EndomulScalar` constraints (`endomulScalarConstraints`). `cA/cB/cC` are the witnessed
quotients `11/6, −5/2, 2/3`, and `negOne/three/six/eleven` are the small literals of `c`, `d` and
`crumb`. -/
def pEmScalar (cA cB cC negOne three six eleven : Nat) (w : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let n0 := ww 0; let n8 := ww 1; let a0 := ww 2; let b0 := ww 3
  let a8 := ww 4; let b8 := ww 5
  let x := fun i => ww (6 + i)
  let cf : Nat → AM Nat := fun t => do
    let m1 ← eMul cC t
    let s1 ← eAdd m1 cB
    let m2 ← eMul s1 t
    let s2 ← eAdd m2 cA
    eMul s2 t
  let cfs ← (List.range 8).foldlM (fun acc i => do let v ← cf (x i); pure (acc ++ [v])) []
  let dfs ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let m1 ← eMul negOne t
      let s1 ← eAdd m1 three
      let m2 ← eMul s1 t
      let s2 ← eAdd m2 negOne
      let v ← eAdd (cfs.getD i 0) s2
      pure (acc ++ [v])) []
  let n8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      let a4 ← eAdd a2 a2
      eAdd a4 (x i)) n0
  let a8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      eAdd a2 (cfs.getD i 0)) a0
  let b8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      eAdd a2 (dfs.getD i 0)) b0
  let c0 ← eSub n8e n8
  let c1 ← eSub a8e a8
  let c2 ← eSub b8e b8
  let cr ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let a ← eSub t six
      let b ← eMul a t
      let c ← eAdd b eleven
      let d ← eMul c t
      let e ← eSub d six
      let v ← eMul e t
      pure (acc ++ [v])) []
  pure ([c0, c1, c2] ++ cr)

/-- `genericGateConstraint` — the double generic gate's own linearization factor. -/
def pGenericGate (genSel alpha : Nat) (c w : List Nat) : AM Nat := do
  let cc := fun i => c.getD i 0
  let ww := fun i => w.getD i 0
  let t0 ← eMul (cc 0) (ww 0)
  let t1 ← eMul (cc 1) (ww 1)
  let t2 ← eMul (cc 2) (ww 2)
  let w01 ← eMul (ww 0) (ww 1)
  let t3 ← eMul (cc 3) w01
  let s0 ← eAdd t0 t1
  let s1 ← eAdd s0 t2
  let s2 ← eAdd s1 t3
  let k1 ← eAdd s2 (cc 4)
  let u0 ← eMul (cc 5) (ww 3)
  let u1 ← eMul (cc 6) (ww 4)
  let u2 ← eMul (cc 7) (ww 5)
  let w34 ← eMul (ww 3) (ww 4)
  let u3 ← eMul (cc 8) w34
  let r0 ← eAdd u0 u1
  let r1 ← eAdd r0 u2
  let r2 ← eAdd r1 u3
  let k2 ← eAdd r2 (cc 9)
  let ak2 ← eMul alpha k2
  let sum ← eAdd k1 ak2
  eMul genSel sum

/-- `alphaCombine α cs = Σᵢ αⁱ·csᵢ`, Horner-free (the powers are shared with `ft_eval0`'s `α^21..23`
so the whole rung pays for one power chain). -/
def pAlphaCombine (apow : List Nat) (cs : List Nat) : AM Nat := do
  match cs with
  | [] => eLit 0
  | c0 :: rest =>
      (List.range rest.length).foldlM (fun acc i => do
        let t ← eMul (apow.getD (i + 1) 0) (rest.getD i 0)
        eAdd acc t) c0

/-! ## §8d — R6, `ft_eval0` + `Plonk_checks.checked`, with `scalars_env`.

`step_verifier.ml:1019-1071,1131-1136`. The rung compiles, in order:

  * **`scalars_env`** (`plonk_checks.ml:254-408`) — `ω^{n−1}` as a WITNESSED inverse (`ω·ω⁻¹ = 1`
    checked in-circuit, so `ω^{n−1}` is derived rather than asserted), `ω^{n−2}`, `ω^{n−3}`,
    `zk_polynomial`, `ζ^n − 1` by `log2n` squarings, and the α power chain `α⁰..α²³`.
  * **the linearization constant term** — `gateLinConst`: all six gate bodies of §8c behind their
    selectors, α-combined. This is `Sc.constant_term env` (`plonk_checks.ml:459`).
  * **`ft_eval0`** (`plonk_checks.ml:420-460`) — the permutation numerator fold over the 6 σ evals,
    minus `p(ζ)`, minus the denominator fold over the 7 coset shifts, plus `numerator·denomInv` with
    `denom·denomInv = 1` CHECKED (the same witnessed-inverse device, no `Field` instance needed),
    minus the constant term.
  * **`Plonk_checks.checked`** (`plonk_checks.ml:516-548`) — `derive_plonk`'s `perm` scalar
    `−(fold over e.s of (γ + β·s + w) from z(ζω)·β·α²¹·zkp)`, asserted equal to the deferred value.

⚑ IT READS THE ASSEMBLY, not a private island: `ζ/α/β/γ` are R2's challenge variables and the 43
evaluation columns are R5's `vEz`/`vEw` — so the whole rung hangs off σ classes that R1–R5 created.
And its OUTPUT is tied to `vEz 3`, the `ft` entry of the `combined_inner_product` column vector,
which is exactly `combine ~ft:ft_eval0` at `step_verifier.ml:1078-1083`. -/

/-- The four-entry prefix of the C8 column vector (`sg_old`×2, the public polynomial, `ft`);
`MinaWrapFtEval0`'s own slicing, and `IDX_Z`/`IDX_W`/`IDX_S`/`IDX_COEFF`/`IDX_SEL` index AFTER it. -/
def EV_PREFIX : Nat := 4
/-- Column `k` of the 43-column evaluation vector at ζ. -/
def vColZ (s : StepShape) (k : Nat) : PVar := vEz s (EV_PREFIX + k)
/-- …and at ζω. -/
def vColW (s : StepShape) (k : Nat) : PVar := vEw s (EV_PREFIX + k)

-- (Which challenge plays ζ / α / β / γ is §2b's — `StepShape.betaChal` and friends, positions the
-- transcript SCHEDULE fixes rather than an arbitrary numbering.)

/-- The wire the ft program reads: each field is a SOURCE OP, so the same program compiles against
the assembled circuit's variables (`.inp`) and against a real block's field values (`.lit`). -/
structure FtWire where
  ez : Nat → AOp
  ew : Nat → AOp
  zeta : AOp
  alpha : AOp
  beta : AOp
  gamma : AOp
  pZeta : AOp

/-- The config the ft program bakes in as constants: the domain, the seven coset shifts, the MDS,
the endomorphism coefficient and the three `EndomulScalar` quotients — plus the two witnessed
values the circuit CHECKS rather than trusts. -/
structure FtCfg where
  log2n : Nat
  omega : Nat
  omegaInv : Nat
  shifts : List Nat
  mds9 : List Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  denomInv : Nat
  permClaimed : Nat
  deriving Repr, Inhabited

/-- The slots the rung's rows and pins refer to. -/
structure FtSlots where
  ftEval0 : Nat
  linConst : Nat
  zkp : Nat
  perm : Nat
  zetaN : Nat
  omInv3 : Nat
  deriving Repr, Inhabited

/-- **The ft program.** Returns the named output slots. -/
def ftBuild (W : FtWire) (C : FtCfg) : AM FtSlots := do
  -- ── small literals and the config constants ───────────────────────────────────────────────
  let one ← eLit 1
  let negOne ← eLit (pN - 1)
  let three ← eLit 3
  let six ← eLit 6
  let eleven ← eLit 11
  let omega ← eLit C.omega
  let omInv ← eLit C.omegaInv
  let endo ← eLit C.endo
  let cA ← eLit C.cA
  let cB ← eLit C.cB
  let cC ← eLit C.cC
  let shiftS ← (List.range 7).foldlM
    (fun acc i => do let v ← eLit (C.shifts.getD i 0); pure (acc ++ [v])) []
  let mdsS ← (List.range 3).foldlM (fun acc j => do
      let row ← (List.range 3).foldlM
        (fun r i => do let v ← eLit (C.mds9.getD (3 * j + i) 0); pure (r ++ [v])) []
      pure (acc ++ [row])) []
  -- ── scalars_env ───────────────────────────────────────────────────────────────────────────
  -- ⚑ ω^{n−1} = ω⁻¹ is DERIVED: `ω·ω⁻¹ = 1` is a row, so a wrong inverse cannot be witnessed.
  let chk ← eMul omega omInv
  let _ ← eEq chk one
  let omInv2 ← eMul omInv omInv
  let omInv3 ← eMul omInv2 omInv
  let zeta ← em W.zeta
  let alpha ← em W.alpha
  let beta ← em W.beta
  let gamma ← em W.gamma
  let zm3 ← eSub zeta omInv3
  let zm2 ← eSub zeta omInv2
  let zm1 ← eSub zeta omInv
  let zkpA ← eMul zm3 zm2
  let zkp ← eMul zkpA zm1
  let zetaN ← (List.range C.log2n).foldlM (fun acc _ => eMul acc acc) zeta
  let zeta1m1 ← eSub zetaN one
  let apow ← (List.range 23).foldlM (fun acc _ => do
      let p ← eMul (acc.getLastD one) alpha; pure (acc ++ [p])) [one]
  let a0 := apow.getD 21 0
  let a1 := apow.getD 22 0
  let a2 := apow.getD 23 0
  -- ── the wire columns ──────────────────────────────────────────────────────────────────────
  let ez ← (List.range 43).foldlM (fun acc k => do let v ← em (W.ez k); pure (acc ++ [v])) []
  let ew ← (List.range 43).foldlM (fun acc k => do let v ← em (W.ew k); pure (acc ++ [v])) []
  let coeff := (List.range 15).map (fun i => ez.getD (IDX_COEFF + i) 0)
  let wv := (List.range 15).map (fun i => ez.getD (IDX_W + i) 0)
  let wn := (List.range 15).map (fun i => ew.getD (IDX_W + i) 0)
  let sv := (List.range 6).map (fun i => ez.getD (IDX_S + i) 0)
  let zZeta := ez.getD IDX_Z 0
  let zZetaW := ew.getD IDX_Z 0
  let genSel := ez.getD (IDX_SEL + 0) 0
  let posSel := ez.getD (IDX_SEL + 1) 0
  let caddSel := ez.getD (IDX_SEL + 2) 0
  let mulSel := ez.getD (IDX_SEL + 3) 0
  let emulSel := ez.getD (IDX_SEL + 4) 0
  let emsSel := ez.getD (IDX_SEL + 5) 0
  -- ── gateLinConst: the six bodies behind their selectors ───────────────────────────────────
  let gG ← pGenericGate genSel alpha coeff wv
  let cPos ← pPoseidon mdsS coeff wv wn
  let aPos ← pAlphaCombine apow cPos
  let gPos ← eMul posSel aPos
  let cAdd' ← pCompleteAdd one wv
  let aAdd ← pAlphaCombine apow cAdd'
  let gAdd ← eMul caddSel aAdd
  let cMulG ← pVarBaseMul one wv wn
  let aMul ← pAlphaCombine apow cMulG
  let gMul ← eMul mulSel aMul
  let cEmul ← pEndoMul one endo wv wn
  let aEmul ← pAlphaCombine apow cEmul
  let gEmul ← eMul emulSel aEmul
  let cEms ← pEmScalar cA cB cC negOne three six eleven wv
  let aEms ← pAlphaCombine apow cEms
  let gEms ← eMul emsSel aEms
  let l1 ← eAdd gG gPos
  let l2 ← eAdd l1 gAdd
  let l3 ← eAdd l2 gMul
  let l4 ← eAdd l3 gEmul
  let lct ← eAdd l4 gEms
  -- ── ft_eval0 (`ftEval0R`, term for term) ──────────────────────────────────────────────────
  let w6g ← eAdd (wv.getD 6 0) gamma
  let i1 ← eMul w6g zZetaW
  let i2 ← eMul i1 a0
  let init ← eMul i2 zkp
  let numerFold ← (List.range 6).foldlM (fun x i => do
      let bs ← eMul beta (sv.getD i 0)
      let bw ← eAdd bs (wv.getD i 0)
      let bwg ← eAdd bw gamma
      eMul x bwg) init
  let afterPub ← eSub numerFold (← em W.pZeta)
  let dInit0 ← eMul a0 zkp
  let dInit ← eMul dInit0 zZeta
  let bz ← eMul beta zeta
  let denomFold ← (List.range 7).foldlM (fun x i => do
      let bzs ← eMul bz (shiftS.getD i 0)
      let gb ← eAdd gamma bzs
      let gbw ← eAdd gb (wv.getD i 0)
      eMul x gbw) dInit
  let afterDenom ← eSub afterPub denomFold
  let n1a ← eMul zeta1m1 a1
  let n1 ← eMul n1a zm3
  let n2a ← eMul zeta1m1 a2
  let zm1c ← eSub zeta one
  let n2 ← eMul n2a zm1c
  let nsum ← eAdd n1 n2
  let oneMz ← eSub one zZeta
  let numerator ← eMul nsum oneMz
  let denom ← eMul zm3 zm1c
  let dinv ← eWit C.denomInv
  let dchk ← eMul denom dinv
  let _ ← eEq dchk one
  let nd ← eMul numerator dinv
  let afterZk ← eAdd afterDenom nd
  let ftEval0 ← eSub afterZk lct
  -- ── Plonk_checks.checked: derive_plonk's `perm` scalar, asserted against the deferred word ──
  let p0 ← eMul zZetaW beta
  let p1 ← eMul p0 a0
  let pInit ← eMul p1 zkp
  let pFold ← (List.range 6).foldlM (fun x i => do
      let bs ← eMul beta (sv.getD i 0)
      let gb ← eAdd gamma bs
      let gbw ← eAdd gb (wv.getD i 0)
      eMul x gbw) pInit
  let perm ← eMul negOne pFold
  let permClaimed ← eWit C.permClaimed
  let _ ← eEq perm permClaimed
  pure { ftEval0 := ftEval0, linConst := lct, zkp := zkp, perm := perm
       , zetaN := zetaN, omInv3 := omInv3 }

/-- The compiled program plus its named slots. -/
structure FtProg where
  prog : Array AOp
  slots : FtSlots
  deriving Repr, Inhabited

def ftProgOf (W : FtWire) (C : FtCfg) : FtProg :=
  let r := (ftBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-! ### The committed ft config and wire, for the ASSEMBLED instance. -/

/-- The step domain: `Common.Max_degree.step_log2 = 16` (`plonk_checks.ml` `srs_length_log2`). -/
def FT_LOG2N : Nat := 16
def FT_N : Nat := 2 ^ FT_LOG2N
/-- The `2^16`-th root of unity of `Fp`, DERIVED (`MinaWrapFtEval0.rootOfUnity`, read-only). -/
def FT_OMEGA : Nat := (Dregg2.Bridge.MinaWrapFtEval0.rootOfUnity pN FT_LOG2N).val
def FT_OMEGA_INV : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv FT_OMEGA
/-- `env.endo_coefficient()` on the STEP side: the BASE endomorphism eigenvalue `5^((p−1)/3)`, NOT
the scalar-challenge endo (`MinaWrapFtEval0Weld` §6's `stepEndoCoefficient`; the conflation of the
two cube roots is the defect that file closed). -/
def FT_ENDO : Nat :=
  (Dregg2.Bridge.MinaWrapFtEval0.powFast ((5 : Nat) : ZMod pN) ((pN - 1) / 3)).val
/-- The three `EndomulScalar` quotients `11/6, −5/2, 2/3` (`quotientConsts`, read-only). -/
def FT_QUOT : Nat × Nat × Nat :=
  match Dregg2.Bridge.MinaWrapFtEval0.quotientConsts pN with
  | some (a, b, c) => (a.val, b.val, c.val)
  | none => (0, 0, 0)
/-- ⚑ **The SEVEN TICK COSET SHIFTS, DERIVED** — `TickShifts.tickShiftsFp 16`, the `Shifts::new`
Blake2b→field construction over the Step field, `#guard`-pinned THERE byte-exact against o1-labs'
own `Shifts::new(Radix2EvaluationDomain::<Fp>::new(2^16))` output. This is what `Plonk_checks`
`ft_eval0`'s denominator fold really runs on; §13 re-states the byte-exact identity here and shows
the OLD fixtures move `ft_eval0`. (Retires the module header's simplification #8.) -/
def FT_SHIFTS : List Nat := (Dregg2.Bridge.TickShifts.tickShiftsFp 16).map (fun x => x.val)

/-- The seven distinct nonzero placeholders the rung used BEFORE the derivation was wired in. Kept
for exactly one purpose: §13's red control, which shows they give a DIFFERENT `ft_eval0`. Nothing
emits them. -/
def FT_SHIFTS_WERE_FIXTURES : List Nat :=
  (List.range 7).map (fun i => (1 + 7919 * (i + 1) * (i + 3)) % pN)
/-- The linearization's `Constants::mds` IS `Vesta::sponge_params().mds = fp_kimchi` (`curve.rs:63`),
i.e. K3's own `PastaPoseidon.mdsN` — the same nine constants the sponge rung R1 permutes with. -/
def FT_MDS9 : List Nat := Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten

/-- The ft program's `.inp` lookup: the challenges and the 43 columns, straight from the chains. It
does NOT read column 3, so the `ft` override below is not circular. -/
def ftInputEnv (s : StepShape) (d : SpongeData) : VarEnv :=
  (List.range s.chals).map (fun c => (vN s c s.emsRows, (chalOf s d c : Int)))
  ++ (List.range s.chals).map (fun c => (vLift s c, (liftOf s d c : Int)))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [(vEz s k, (evVal k 0 : Int)), (vEw s k, (evVal k 1 : Int))])

/-- ⚑ `Plonk.In_circuit.map_challenges ~f:Fn.id ~scalar plonk` (`step_verifier.ml:920-923`): the
`Scalar_challenge` fields α and ζ go through `scalar = SC.to_field_checked`, β and γ are `Challenge`
fields and stay RAW. So R6 reads `vLift` for α/ζ and `vN` for β/γ — upstream's own split, and the
retirement of the module header's simplification #7. -/
def ftWireOf (s : StepShape) : FtWire :=
  { ez := fun k => .inp (vColZ s k)
  , ew := fun k => .inp (vColW s k)
  , zeta := .inp (vLift s s.zetaChal)
  , alpha := .inp (vLift s s.alphaChal)
  , beta := .inp (vN s s.betaChal s.emsRows)
  , gamma := .inp (vN s s.gammaChal s.emsRows)
  , pZeta := .inp (vEz s 2) }

/-- The two witnessed values, computed from the wire: `denomInv` and the deferred `perm` scalar.
Both are CHECKED by a row (`denom·denomInv = 1`, `perm_actual = perm_claimed`), so a wrong witness
is a refusal rather than an accept. Computed by running the program once with placeholders. -/
def ftCfgRaw (dInv pC : Nat) : FtCfg :=
  { log2n := FT_LOG2N, omega := FT_OMEGA, omegaInv := FT_OMEGA_INV
  , shifts := FT_SHIFTS, mds9 := FT_MDS9, endo := FT_ENDO
  , cA := FT_QUOT.1, cB := FT_QUOT.2.1, cC := FT_QUOT.2.2
  , denomInv := dInv, permClaimed := pC }

/-- Everything R6 needs, evaluated ONCE. -/
structure FtData where
  fp : FtProg
  vals : Array Nat
  /-- The witnessed inverse of `(ζ − ω^{n−3})(ζ − 1)`, checked by a row. -/
  denomInv : Nat
  /-- The deferred `perm` scalar `Plonk_checks.checked` compares against, checked by a row. -/
  permClaimed : Nat
  deriving Repr, Inhabited

/-- Run the program twice: once to read off `denom` and the actual `perm` scalar, then once with the
witnesses those force. The second run is the emitted one. -/
def runFt (s : StepShape) (d : SpongeData) : FtData :=
  let W := ftWireOf s
  let lk := envLookupAt (envIndex (ftInputEnv s d))
  let p0 := ftProgOf W (ftCfgRaw 1 0)
  let v0 := aEval lk p0.prog
  -- `denom` is the slot the `dchk` multiplication reads; recompute it directly from ζ and ω^{n−3}.
  let zeta := (lk (vLift s s.zetaChal)).toNat % pN
  let omInv3 := v0.getD p0.slots.omInv3 0
  let denom := fMul (fSub zeta omInv3) (fSub zeta 1)
  let dInv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv denom
  let pC := v0.getD p0.slots.perm 0
  let p1 := ftProgOf W (ftCfgRaw dInv pC)
  { fp := p1, vals := aEval lk p1.prog, denomInv := dInv, permClaimed := pC }

/-- ⚑ §6b's two scalars, READ OFF R6's compiled program: `Plonk_checks.checked`'s `perm`
(`plonk_checks.ml:482-488`) and `ζ^n` (`:496`, `= zeta_to_srs_length` at `log2n = 16`, `:497`). This
is the whole of the divergence §6b names — upstream's `ft_comm` reads the `Fq` Type2 statement twins
of these, which the step circuit does not constrain at all. -/
def ftcWireOf (s : StepShape) (f : FtData) : FtcWire :=
  { permV := aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm
  , permVal := f.vals.getD f.fp.slots.perm 0
  , zetaV := aVarAt (baseFtS s) f.fp.prog f.fp.slots.zetaN
  , zetaVal := f.vals.getD f.fp.slots.zetaN 0 }

/-- **R6's rows**: the compiled program, the tie of its `ft_eval0` output to the `ft` column of the
`combined_inner_product` vector, and the σ-only probes. -/
def ftRows (s : StepShape) (f : FtData) (wired : Bool) : List SRow :=
  let base := baseFtS s
  let V := aVarAt base f.fp.prog
  aRows base f.fp.prog
  ++ [ genericRow (some (V f.fp.slots.ftEval0)) (some (vEz s 3)) none none none none (cEq ++ cNil)
     , probeRow wired (V f.fp.slots.ftEval0) (V f.fp.slots.linConst)
     , probeRow wired (V f.fp.slots.perm) (V f.fp.slots.zkp) ]

/-! ## §8e — R7, the EVALUATION ABSORPTION + opt-sponge masking.

`step_verifier.ml:950-1006`, `step_main.ml:525-567`. Three sponge SEGMENTS, each a fresh `[0,0,0]`
state, `absorb` blocks of two words (`rate = 2`), then bare squeeze permutations:

  * **A — the opt-sponge** over the carried bulletproof challenges, with a per-block `keep` MASK.
    Upstream's own trick (`:985-1003`) absorbs unconditionally and then MUXES the state
    (`Array.map2_exn sponge.state state_before ~f:(Field.if_ b)`); this compiles that mux as
    `outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ)`, three lanes, three `Generic` halves each. That is
    the `branch_data.proofs_verified_mask` path, and it is the piece the sponge rung R1 had no
    shape for.
  * **B — the fr-sponge**: the challenge digest, `ft_eval1`, `p(ζ)`, `p(ζω)`, then **the 43 columns
    at ζ and ζω interleaved** (`to_absorption_sequence`), then TWO squeezes for ξ′ and r′.
  * **C — `hash_messages_for_next_step_proof`**: the app state, the 28 plonk-index commitments (56
    coordinates), the two challenge-polynomial commitments and the unpadded bulletproof challenges,
    then one squeeze.

⚑ EVERY ABSORBED WORD IS AN ASSEMBLY VARIABLE where upstream's is: segment A absorbs R2's
challenges, segment B absorbs R5's evaluation columns (the SAME variables R6 reads) and R6's
`ft_eval1`/`p(ζ)` entries, and segment C absorbs R3's and R4's fold outputs. -/

/-- One segment's schedule. -/
structure SegSpec where
  /-- absorbed words: the variable and its value, padded to an even length. -/
  ws : List (PVar × Nat)
  /-- squeeze permutations after the absorb blocks. -/
  squeezes : Nat
  /-- whether the segment muxes its state with a per-block `keep` bit. -/
  masked : Bool
  /-- ⚑ the FIRST masked block. `Opt_sponge.of_sponge` converts at the first `Opt` element and
  everything after it is opt (`step_verifier.ml:1198-1211`), so a segment can absorb a `Not_opt`
  prefix unconditionally and mask the rest — which is exactly `hash_messages_for_next_step_proof`'s
  shape. `0` for a wholly-masked segment. -/
  maskFrom : Nat := 0
  /-- ⚑ For a MASKED segment, the `keep` VARIABLE and BIT of each absorb block. Both come from
  §8h's unpacking of the `branch_data` statement word — this is not a schedule constant. -/
  keep : Nat → PVar × Nat := fun _ => (xv 0, 0)
  deriving Inhabited

/-- Is absorb block `b` muxed by a `keep` bit? -/
def SegSpec.maskedAt (g : SegSpec) (b : Nat) : Bool := g.masked && g.maskFrom ≤ b
def SegSpec.nb (g : SegSpec) : Nat := (g.ws.length + 1) / 2
def SegSpec.blocks (g : SegSpec) : Nat := g.nb + g.squeezes

/-- A segment's evaluated trajectory. -/
structure SegData where
  /-- the state ENTERING each block, `blocks + 1` of them. -/
  states : List (List Nat)
  /-- the 56 round states of each block's permutation. -/
  perms : List (List (List Nat))
  /-- the un-muxed permutation output of each absorb block. -/
  afters : List (List Nat)
  deriving Repr, Inhabited

/-- `keep` bit of absorb block `b`, out of the spec. -/
def SegSpec.keepBit (g : SegSpec) (b : Nat) : Nat := (g.keep b).2
/-- …and its variable. -/
def SegSpec.keepVar (g : SegSpec) (b : Nat) : PVar := (g.keep b).1

def runSeg (g : SegSpec) : SegData :=
  (List.range g.blocks).foldl
    (fun d b =>
      let pre := d.states.getLastD [0, 0, 0]
      let post :=
        if b < g.nb then
          [ fAdd (pre.getD 0 0) ((g.ws.getD (2 * b) (xv 0, 0)).2)
          , fAdd (pre.getD 1 0) ((g.ws.getD (2 * b + 1) (xv 0, 0)).2)
          , pre.getD 2 0 ]
        else pre
      let ss := permStates post
      let after := ss.getLastD post
      let next :=
        if b < g.nb && g.maskedAt b && g.keepBit b == 0 then pre else after
      { states := d.states ++ [next], perms := d.perms ++ [ss]
      , afters := d.afters ++ [after] })
    { states := [[0, 0, 0]], perms := [], afters := [] }

/-- Segment variable regions, all relative to one base. -/
def sgSt (base _nb _sq b j : Nat) : PVar := xv (base + 3 * b + j)
def sgPost (base nb sq b j : Nat) : PVar := xv (base + 3 * (nb + sq + 1) + 2 * b + j)
def sgAfter (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 2 * nb + 3 * b + j)
def sgD (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 5 * nb + 3 * b + j)
def sgP (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 8 * nb + 3 * b + j)
/-- ⚑ `hash_messages_for_next_step_proof`'s OUTPUT — segment C's squeeze. Upstream this IS the step
statement's `messages_for_next_step_proof` hash, which the step circuit carries as a public word
(`step_main.ml:121,522`). Exposing it is what makes segment C's mask REACH the verifier: change
`branch_data` and this public word moves. -/
def hmDigestVar (s : StepShape) : PVar := sgSt (baseSegC s) (nbC s) 1 (nbC s + 1) 0
-- ⚑ There is no per-block `keep` VARIABLE region any more: since §8h a masked segment's mux reads
-- `g.keepVar b`, which is one of the two `branch_data` mask bits. The id slots the old region
-- occupied stay reserved in `segVarCount` so no other region moves.

/-- **One segment's rows.** -/
def segRows (base : Nat) (g : SegSpec) (d : SegData) (wired : Bool) : List SRow :=
  let nb := g.nb
  let sq := g.squeezes
  [ genericRow (some (sgSt base nb sq 0 0)) none none (some (sgSt base nb sq 0 1)) none none
      (cConst 0 ++ cConst 0)
  , genericRow (some (sgSt base nb sq 0 2)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range g.blocks).flatMap (fun b =>
      if b < nb then
        let out : Nat → PVar :=
          if g.maskedAt b then (fun j => sgAfter base nb sq b j)
          else (fun j => sgSt base nb sq (b + 1) j)
        [ genericRow (some (sgSt base nb sq b 0)) (some (g.ws.getD (2 * b) (xv 0, 0)).1)
                     (some (sgPost base nb sq b 0))
                     (some (sgSt base nb sq b 1)) (some (g.ws.getD (2 * b + 1) (xv 0, 0)).1)
                     (some (sgPost base nb sq b 1)) (cAdd ++ cAdd) ]
        ++ permBlockRows (sgPost base nb sq b 0) (sgPost base nb sq b 1) (sgSt base nb sq b 2)
             (out 0) (out 1) (out 2) (d.perms.getD b [])
        ++ (if g.maskedAt b then
              -- the `Field.if_` mux: outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ)
              (List.range 3).map (fun j =>
                genericRow (some (sgAfter base nb sq b j)) (some (sgSt base nb sq b j))
                           (some (sgD base nb sq b j))
                           (some (g.keepVar b)) (some (sgD base nb sq b j))
                           (some (sgP base nb sq b j)) (cSub ++ cMul))
              ++ [ genericRow (some (sgSt base nb sq b 0)) (some (sgP base nb sq b 0))
                              (some (sgSt base nb sq (b + 1) 0))
                              (some (sgSt base nb sq b 1)) (some (sgP base nb sq b 1))
                              (some (sgSt base nb sq (b + 1) 1)) (cAdd ++ cAdd)
                 , genericRow (some (sgSt base nb sq b 2)) (some (sgP base nb sq b 2))
                              (some (sgSt base nb sq (b + 1) 2)) none none none (cAdd ++ cNil) ]
            else [])
        ++ (if b + 1 == nb then [probeRow wired (sgSt base nb sq (b + 1) 0)
                                              (sgSt base nb sq (b + 1) 1)] else [])
      else
        permBlockRows (sgSt base nb sq b 0) (sgSt base nb sq b 1) (sgSt base nb sq b 2)
          (sgSt base nb sq (b + 1) 0) (sgSt base nb sq (b + 1) 1) (sgSt base nb sq (b + 1) 2)
          (d.perms.getD b [])
        ++ [probeRow wired (sgSt base nb sq (b + 1) 0) (sgSt base nb sq (b + 1) 1)])

/-- A segment's environment. -/
def segEnv (base : Nat) (g : SegSpec) (d : SegData) : VarEnv :=
  let nb := g.nb
  let sq := g.squeezes
  (List.range (g.blocks + 1)).flatMap (fun b =>
    (List.range 3).map (fun j => (sgSt base nb sq b j, ((d.states.getD b []).getD j 0 : Int))))
  ++ (List.range nb).flatMap (fun b =>
      let pre := d.states.getD b []
      (List.range 2).map (fun j =>
        (sgPost base nb sq b j,
         (fAdd (pre.getD j 0) ((g.ws.getD (2 * b + j) (xv 0, 0)).2) : Int))))
  -- (the `keep` VARIABLE's value is owned by §8h — it is a `branch_data` mask bit, not a segment id)
  ++ (if g.masked then
        ((List.range nb).filter g.maskedAt).flatMap (fun b =>
          let pre := d.states.getD b []
          let aft := d.afters.getD b []
          let k := g.keepBit b
          (List.range 3).flatMap (fun j =>
              let dv := fSub (aft.getD j 0) (pre.getD j 0)
              [ (sgAfter base nb sq b j, (aft.getD j 0 : Int))
              , (sgD base nb sq b j, (dv : Int))
              , (sgP base nb sq b j, (fMul k dv : Int)) ]))
      else [])

/-- The three segments' shapes, from the committed `StepShape`. -/
def StepShape.frCols (s : StepShape) : Nat := s.cipEvals - EV_PREFIX
/-- Carried bulletproof challenges: two previous proofs × `bRounds` each. -/
def StepShape.optWords (s : StepShape) : Nat := 2 * s.bRounds
/-- `hash_messages_for_next_step_proof`'s field elements: the `Not_opt` prefix (`sponge_after_index`
+ app state), the two challenge-polynomial commitments (4 coordinates) and the unpadded bulletproof
challenges — the last two groups `Opt`-masked. -/
def StepShape.hmWords (s : StepShape) : Nat := N_HM_FIX + 4 + 2 * s.bRounds

/-! ### §8h — `branch_data`'s `proofs_verified_mask`, UNPACKED.

`step_main.ml:53,70-72`, `composition_types/branch_data.ml:88-101`, `pickles_base/
proofs_verified.ml:70-100`. The opt-sponge's per-absorption `keep` is
`Vector.trim_front branch_data.proofs_verified_mask` — two Boolean variables of the STATEMENT, not a
schedule constant. `Checked.pack` recombines them with `domain_log2` into the single field element
the statement carries: `4·domain_log2 + (m₀ + 2·m₁)`. These are the rows for that, and `optSpec`
below reads the two bits.

⚑ `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`, so a set bit is a SUFFIX and
the committed instance (ONE previous proof, `N1`) keeps slot 1 and drops slot 0 — the OPPOSITE of
the "first half kept" pattern this rung ran until 2026-08-02. -/

/-- `Prefix_mask.there N1` — the honest instance's mask, one previous proof of two slots. -/
def MASK_BITS : List Nat := [0, 1]
/-- `domain_log2` — `Common.Max_degree.step_log2`, the same 16 `FT_LOG2N` is. -/
def BRANCH_DOMAIN_LOG2 : Nat := 16
/-- `Branch_data.Checked.pack` (`branch_data.ml:95-101`). -/
def branchPacked : Nat :=
  (4 * BRANCH_DOMAIN_LOG2 + MASK_BITS.getD 0 0 + 2 * MASK_BITS.getD 1 0) % pN

/-- Which previous proof absorb block `b` of the opt-sponge carries: each of the two previous proofs
contributes `bRounds` challenge words and a block absorbs two, so the blocks split at `bRounds/2`. -/
def optProofOf (s : StepShape) (b : Nat) : Nat := if 2 * b < s.bRounds then 0 else 1
/-- ⚑ Block `b`'s `keep` — the mask VARIABLE and its bit, both from `branch_data`. -/
def optKeep (s : StepShape) (b : Nat) : PVar × Nat :=
  (vMask s (optProofOf s b), MASK_BITS.getD (optProofOf s b) 0)

/-- **§8h's rows.** Booleanity of both mask bits (`Boolean.typ`'s own check) and `Checked.pack`,
which ties them to the `branch_data` statement word. -/
def branchRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vMask s 0)) (some (vMask s 0)) (some (vMask s 0))
               (some (vMask s 1)) (some (vMask s 1)) (some (vMask s 1)) (cMul ++ cMul)
  , genericRow (some (vMask s 0)) (some (vMask s 1)) (some (vMaskPack s))
               (some (vDomLog2 s)) (some (vMaskPack s)) (some (vBranch s))
               ([1, 2, -1, 0, 0] ++ [4, 1, -1, 0, 0])
  , probeRow wired (vMask s 0) (vMask s 1)
  , probeRow wired (vBranch s) (vMaskPack s) ]

/-- ⚑ Segment A absorbs **`prev_challenges`** (`step_verifier.ml:953-959`), the previous proofs'
CARRIED bulletproof challenges — a `Per_proof_witness` field, not this transcript's squeezes. It took
`vN s (i % chals) emsRows` until 2026-08-02; see `vPrevChal` for what that false wire cost. Segment C
absorbs the SAME variables (`step_main.ml:80`), so they are one σ class across two sponges. -/
def optSpec (s : StepShape) : SegSpec :=
  { ws := (List.range s.optWords).map (fun i => (vPrevChal s i, prevChalVal i))
  , squeezes := 1, masked := true, keep := optKeep s }

def frSpec (s : StepShape) (dg : PVar × Nat) (ftVal : Nat) : SegSpec :=
  { ws := [ dg, (vEw s 3, evVal 3 1), (vEz s 2, evZOf ftVal 2), (vEw s 2, evVal 2 1) ]
      ++ (List.range s.frCols).flatMap (fun k =>
          [ (vColZ s k, evZOf ftVal (EV_PREFIX + k))
          , (vColW s k, evVal (EV_PREFIX + k) 1) ])
  , squeezes := 2, masked := false }

/-- A deterministic fixture standing for one of the two APP-STATE words. Since §3c the plonk-index
half of this prefix is derived and this covers only `state_to_field_elements app_state`. -/
def hmVal (i : Nat) : Nat := (13 + 3000017 * i + 5 * i * i) % pN

/-- ⚑ Segment C's per-block `keep`, and the SECOND consumer of `branch_data`'s mask.
`hash_messages_for_next_step_proof_opt` masks BOTH the `challenge_polynomial_commitments` and the
`old_bulletproof_challenges` with the SAME `proofs_verified_mask` — two `Vector.map2`s over the
vector §8h already unpacked (`step_verifier.ml:1180-1186`) — while the app state stays `Not_opt`.
Until 2026-08-02 this segment absorbed all of them UNMASKED, which was the residue #9's retirement
made visible. Word `2b` decides: the four commitment coordinates first, one previous proof each,
then `bRounds` challenge words per proof. -/
def hmKeepAt (s : StepShape) (ms : List Nat) (b : Nat) : PVar × Nat :=
  let w := 2 * b
  let i := if w < N_HM_FIX + 4 then (w - N_HM_FIX) / 2
           else if w - (N_HM_FIX + 4) < s.bRounds then 0 else 1
  (vMask s i, ms.getD i 0)

/-- **`index_digest`'s rows** (§3c) — ONE permutation over segment C's own state after the 28 index
absorptions, which is `Sponge.squeeze_field (Sponge.copy sponge_after_index)`
(`step_verifier.ml:529-534`). The input lanes are segment C's state variables, so the copy is a σ
class and not a recomputation. -/
def idxDigestRows (s : StepShape) (wired : Bool) : List SRow :=
  permBlockRows (sgSt (baseSegC s) (nbC s) 1 (N_IDX_WORDS / 2) 0)
                (sgSt (baseSegC s) (nbC s) 1 (N_IDX_WORDS / 2) 1)
                (sgSt (baseSegC s) (nbC s) 1 (N_IDX_WORDS / 2) 2)
                (vIdxD s 0) (vIdxD s 1) (vIdxD s 2) (permStates idxAfterState)
  ++ [probeRow wired (vIdxD s 0) (vIdxD s 1)]

def hmSpec (s : StepShape) (t : MsmData) (v : IpaData) : SegSpec :=
  -- ⚑ §3c: the `Not_opt` prefix is `sponge_after_index`'s own absorption — the 28 plonk-index
  -- commitments as 56 coordinates, 27 of them THE FOLD'S OWN `.const` base variables — then the two
  -- app-state words, which are the only fixtures left in it.
  { ws := (List.range N_IDX_WORDS).map (fun i => (idxVar s (i / 2) (i % 2), idxVal (i / 2) (i % 2)))
      ++ (List.range N_HM_APP).map (fun i => (vHm s i, hmVal i))
      ++ [ (mpx s (pSum s (s.msmTerms - 2)), (t.sums.getLastD (0, 0)).1)
         , (mpy s (pSum s (s.msmTerms - 2)), (t.sums.getLastD (0, 0)).2)
         , (ipx s (qSum s (s.ipaRounds - 1)), (v.sums.getLastD (0, 0)).1)
         , (ipy s (qSum s (s.ipaRounds - 1)), (v.sums.getLastD (0, 0)).2) ]
      -- ⚑ `old_bulletproof_challenges = prev_challenges` (`step_main.ml:80`) — the SAME vector
      -- segment A absorbs, so segment C's public digest moves when one of them is bent.
      ++ (List.range (2 * s.bRounds)).map (fun i => (vPrevChal s i, prevChalVal i))
  , squeezes := 1, masked := true, maskFrom := N_HM_FIX / 2, keep := hmKeepAt s MASK_BITS }

/-! ## §8f — R8, `finalize_other_proof`'s TAIL: the deferred values BIND.

`step_verifier.ml:1076-1147`. R5–R7 compute the deferred quantities; NOTHING yet compares them with
what the proof CLAIMS. This rung is that comparison, and it is the semantically load-bearing part of
`finalize_other_proof`:

  * **`ζω = domain#generator · plonk.zeta`** (`:934`) and the SECOND challenge polynomial
    `b(ζω) = ∏(1 + uₖ·(ζω)^{2^{k}})` over the LIFTED bulletproof challenges, so
    **`b_actual = challenge_poly ζ + r · challenge_poly ζω`** (`:1124-1128`) — the `+ r·…` leg the
    module header's simplification #4 named as absent.
  * **THREE `Shifted_value.Type1.to_field` unshifts** (`shifted_value.ml:133-135`: `t + t + c`) of
    `combined_inner_product` (`:1105-1109`), `b` (`:1126-1127`) and — inside
    `Plonk_checks.checked` (`plonk_checks.ml:536-544`) — `plonk.perm`.
    ⚑ **THE FIELD KEY.** A Type1 shift keys on the VALUE's own field, not the circuit's. These three
    are the Wrap proof-state's `fp` block, so the shift is **Type1 over `Fp`**: `c = 2^255 + 1`,
    `scale = 1/2` (`shift1`, `step_verifier.ml:825`; `PicklesStatementDiff` §1). The step statement's
    own `fq` block is Type2/`Fq` — subtract-only, no halving (`impls.ml:135`,
    `PicklesStepStatementDiff` §1) — and §16 shows both wrong readings diverge here.
  * **`xi_correct`** (`:1102-1104`) — the fr-sponge's own squeeze, `lowest_128_bits`-decomposed,
    against the statement's `xi`.
  * **`Boolean.all [xi_correct; b_correct; combined_inner_product_correct; plonk_checks_passed]`**
    (`:1141-1147`), each leg a REAL `Field.equal` gadget (`d·inv = 1 − bit`, `d·bit = 0`, `bit² =
    bit`), and the `should_verify` mux `verified && finalized || not should_verify`
    (`step_main.ml:121`, asserted at `:522`) closing on `= 1`. -/

/-- `Shifted_value.Type1.Shift.create (module Fp)`: `c = 2^{255} + 1` (`shifted_value.ml:122-126`,
`Fp.size_in_bits = 255`). -/
def SHIFT_C : Nat := (2 ^ 255 + 1) % pN
/-- …and `scale = 1/2`, as the `Fp` representative. -/
def SHIFT_INV2 : Nat := (pN + 1) / 2
/-- `Shifted_value.Type1.of_field` — `(x − c)·½`. -/
def shiftT1 (x : Nat) : Nat := fMul (fSub x SHIFT_C) SHIFT_INV2
/-- `Shifted_value.Type1.to_field` — `t + t + c`, the map the circuit emits. -/
def unshiftT1 (t : Nat) : Nat := fAdd (fAdd t t) SHIFT_C
/-- `Shifted_value.Type2.of_field` — subtract-only, `x − 2^255`. The WRONG-KIND reading, carried so
§16's control is about the rule and not about a typo. -/
def shiftT2 (x : Nat) : Nat := fSub x (2 ^ 255 % pN)

/-- The wire R8 reads: every field a SOURCE OP, so the rung's program can also be run on bent inputs
(§16's red controls) without touching the assembly. -/
structure FinWire where
  /-- ζ, LIFTED (`plonk.zeta`). -/
  zeta : AOp
  /-- `r`, LIFTED (`scalar (Scalar_challenge.create r_actual)`). -/
  r : AOp
  /-- `challenge_poly ζ` — R5's `vAcc bRounds`. -/
  bZeta : AOp
  /-- R5's `combined_inner_product` output. -/
  cipActual : AOp
  /-- R6's `Plonk_checks.checked` `perm` scalar. -/
  permActual : AOp
  /-- the LIFTED bulletproof challenges `u₀..u_{rounds−1}`. -/
  u : Nat → AOp
  /-- the fr-sponge's first squeeze (R7 segment B). -/
  xiSqueeze : AOp
  cipShift : AOp
  bShift : AOp
  permShift : AOp
  xiStmt : AOp
  /-- `should_verify` — a STATEMENT bool (`step_main.ml:36-37`), not a witness. -/
  shouldVerify : AOp

/-- What R8 bakes in, plus the witnesses its own rows CHECK. -/
structure FinCfg where
  rounds : Nat
  omega : Nat
  shiftC : Nat
  /-- `lowest_128_bits`' discarded high part. -/
  hiXi : Nat
  /-- per `Field.equal` gadget: the witnessed inverse and the result bit. -/
  eqInv : List Nat
  eqBit : List Nat
  /-- the kimchi `verified` bit (`step_main.ml:121`; #11 — it is a witness and stays one until
  `Step_verifier.verify` exists). `should_verify` is NOT here: since 2026-08-02 it is a STATEMENT
  word the wire reads, because upstream's is one. -/
  verified : Nat
  deriving Repr, Inhabited

structure FinSlots where
  zetaw : Nat
  bwZeta : Nat
  bActual : Nat
  cipUsed : Nat
  bUsed : Nat
  permUsed : Nat
  xiActual : Nat
  /-- ⚑ `lowest_128_bits`' HIGH part, as a program slot, so §5b's `assert_128_bits` chain can be
  wired to the very cell the decomposition row reads. Without that chain this witness is free and
  `xiActual` is whatever the prover wants (§12c). -/
  xiHi : Nat
  xc : Nat
  bc : Nat
  cc : Nat
  pc : Nat
  finalized : Nat
  out : Nat
  deriving Repr, Inhabited

/-- **The finalize program.** -/
def finBuild (W : FinWire) (C : FinCfg) : AM FinSlots := do
  let zero ← eLit 0
  let one ← eLit 1
  let shiftC ← eLit C.shiftC
  let two128 ← eLit (2 ^ 128 % pN)
  let omega ← eLit C.omega
  let zeta ← em W.zeta
  let r ← em W.r
  -- ── b_correct's SECOND leg (`:1124-1128`) ─────────────────────────────────────────────────
  let zetaw ← eMul omega zeta
  let zws ← (List.range C.rounds).foldlM (fun acc _ => do
      let y ← eMul (acc.getLastD zetaw) (acc.getLastD zetaw); pure (acc ++ [y])) [zetaw]
  let bw ← (List.range C.rounds).foldlM (fun acc k => do
      let u ← em (W.u k)
      let t ← eMul u (zws.getD (C.rounds - 1 - k) 0)
      let f ← eAdd one t
      eMul acc f) one
  let bz ← em W.bZeta
  let rbw ← eMul r bw
  let bAct ← eAdd bz rbw
  -- ── the THREE Type1/Fp unshifts ───────────────────────────────────────────────────────────
  let unshift : Nat → AM Nat := fun t => do let tt ← eAdd t t; eAdd tt shiftC
  let cipUsed ← unshift (← em W.cipShift)
  let bUsed ← unshift (← em W.bShift)
  let permUsed ← unshift (← em W.permShift)
  -- ── xi_actual = lowest_128_bits(squeeze) ──────────────────────────────────────────────────
  let sq ← em W.xiSqueeze
  let hi ← eWit C.hiXi
  let hiHigh ← eMul hi two128
  let xiAct ← eSub sq hiHigh
  let xiStmt ← em W.xiStmt
  -- ── `Field.equal`, the real gadget: `d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`. ─────────
  let mkEq : Nat → Nat → Nat → AM Nat := fun i x y => do
    let d ← eSub x y
    let iv ← eWit (C.eqInv.getD i 0)
    let bb ← eWit (C.eqBit.getD i 0)
    let bb2 ← eMul bb bb
    let _ ← eEq bb2 bb
    let p ← eMul d iv
    let q ← eSub one bb
    let _ ← eEq p q
    let sZ ← eMul d bb
    let _ ← eEq sZ zero
    pure bb
  let cipAct ← em W.cipActual
  let permAct ← em W.permActual
  let xc ← mkEq 0 xiAct xiStmt
  let bc ← mkEq 1 bUsed bAct
  let cc ← mkEq 2 cipUsed cipAct
  let pc ← mkEq 3 permUsed permAct
  -- ── `Boolean.all` and the `should_verify` mux, asserted ───────────────────────────────────
  let f1 ← eMul xc bc
  let f2 ← eMul f1 cc
  let fin ← eMul f2 pc
  let ver ← eWit C.verified
  let ver2 ← eMul ver ver
  let _ ← eEq ver2 ver
  let sv ← em W.shouldVerify
  let sv2 ← eMul sv sv
  let _ ← eEq sv2 sv
  let vf ← eMul ver fin
  let svf ← eMul sv vf
  let nsv ← eSub one sv
  let out ← eAdd svf nsv
  let _ ← eEq out one
  pure { zetaw := zetaw, bwZeta := bw, bActual := bAct, cipUsed := cipUsed, bUsed := bUsed
       , permUsed := permUsed, xiActual := xiAct, xiHi := hi, xc := xc, bc := bc, cc := cc, pc := pc
       , finalized := fin, out := out }

structure FinProg where
  prog : Array AOp
  slots : FinSlots
  deriving Repr, Inhabited

def finProgOf (W : FinWire) (C : FinCfg) : FinProg :=
  let r := (finBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-- The circuit variables EXPOSED as the public output — `pubWords` of them, drawn from every
sub-circuit so a public tie reaches all five. ⚑ The FIRST FOUR are the statement's deferred values;
R8's `Boolean.all` assert is what makes them a claim the circuit refuses to lie about. -/
def exposedVars (s : StepShape) : List PVar :=
  ([ vCipShift s, vBShift s, vPermShift s, vXiStmt s, vShouldVerify s, vBranch s, hmDigestVar s
   , vAcc s s.bRounds, vCa s s.cipEvals, vZ s s.bRounds
   , vSt s s.blocks 0, vSt s s.blocks 1, vSt s s.blocks 2
   , mpx s (pSum s (s.msmTerms - 2)), mpy s (pSum s (s.msmTerms - 2))
   , ipx s (qSum s (s.ipaRounds - 1)), ipy s (qSum s (s.ipaRounds - 1)) ]
   ++ (List.range s.chals).map (fun c => vN s c s.emsRows)
   -- ⚑ `0 .. bRounds−1`, NOT `0 .. bRounds`: `vAcc bRounds` and `vZ bRounds` are already the head
   -- entries, and at `shapeStep`'s 67 words the inclusive range made TWO of Step's public words
   -- carry the same circuit variable (measured 2026-08-02; the smoke shape's 12-word `take` cut
   -- before the collision, so the distinctness pin never saw it — §12 now pins BOTH shapes).
   ++ (List.range s.bRounds).map (fun k => vAcc s k)
   ++ (List.range s.bRounds).map (fun k => vZ s k)
   ++ (List.range (s.blocks + 1)).map (fun b => vSt s b 0)).take s.pubWords

/-- **R5b's rows**: every public word tied to a computed circuit variable, two per `Generic` row
(`w₀ = w₁` in each half). Every one of `pubWords` public words is READ here — exactly what
`placeChecked`'s `inertPublicWord` refusal demands. -/
def closingRows (s : StepShape) : List SRow :=
  let ev := exposedVars s
  (List.range ((s.pubWords + 1) / 2)).map (fun r =>
    if 2 * r + 1 < s.pubWords then
      genericRow (some (ev.getD (2*r) (xv 0))) (some (.external (2*r))) none
                 (some (ev.getD (2*r+1) (xv 0))) (some (.external (2*r+1))) none (cEq ++ cEq)
    else
      genericRow (some (ev.getD (2*r) (xv 0))) (some (.external (2*r))) none none none none
                 (cEq ++ cNil))

/-! ### R8's wire, environment and data. -/

/-- R6's `ft_eval0`, as a value. -/
def FtData.out (f : FtData) : Nat := f.vals.getD f.fp.slots.ftEval0 0

/-- The finalize program's slots start after the ft program's. -/
def baseFin (s : StepShape) (f : FtData) : Nat := baseFtS s + f.fp.prog.size

/-- The fr-sponge's FIRST squeeze — R7 segment B's state after its first squeeze permutation, the
same convention R1 uses (`chalOf` reads lane 0 of the state after squeeze `c`'s permutation). -/
def frSqueezeVar (s : StepShape) : PVar := sgSt (baseSegB s) (nbB s) 2 (nbB s + 1) 0
def frSqueezeVal (segB : SegData) (specB : SegSpec) : Nat :=
  (segB.states.getD (specB.nb + 1) []).getD 0 0

/-- The fr-sponge's **SECOND** squeeze — `r_actual` (`step_verifier.ml:1008`). §8g's chain `1`
decomposes it and lifts it into the `r` the C8 fold and `b_correct` multiply by. -/
def frSqueeze2Var (s : StepShape) : PVar := sgSt (baseSegB s) (nbB s) 2 (nbB s + 2) 0
def frSqueeze2Val (segB : SegData) (specB : SegSpec) : Nat :=
  (segB.states.getD (specB.nb + 2) []).getD 0 0

/-- `b(ζω)` — the SECOND challenge polynomial, over the lifted bulletproof challenges. -/
def bwOf (s : StepShape) (d : SpongeData) : Nat :=
  let zetaw := fMul FT_OMEGA (liftOf s d s.zetaChal)
  let zws := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [zetaw]
  (List.range s.bRounds).foldl
    (fun acc k => fMul acc (fAdd 1 (fMul (liftOf s d (s.uChal k)) (zws.getD (s.bRounds - 1 - k) 0)))) 1

/-- `b_actual = challenge_poly ζ + r · challenge_poly ζω` (`step_verifier.ml:1124-1128`), computed
DIRECTLY here so §16 can pin the emitted program's own slot against it. `rv` is §8g's DEFERRED r. -/
def bActualOf (s : StepShape) (d : SpongeData) (df : DefData) (rv : Nat) : Nat :=
  fAdd (df.accs.getLastD 0) (fMul rv (bwOf s d))

def finWireOf (s : StepShape) (f : FtData) : FinWire :=
  { zeta := .inp (vLift s s.zetaChal)
  , r := .inp (vDLift s 1)
  , bZeta := .inp (vAcc s s.bRounds)
  , cipActual := .inp (vCa s s.cipEvals)
  , permActual := .inp (aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm)
  , u := fun k => .inp (vLift s (s.uChal k))
  , xiSqueeze := .inp (frSqueezeVar s)
  , cipShift := .inp (vCipShift s)
  , bShift := .inp (vBShift s)
  , permShift := .inp (vPermShift s)
  , xiStmt := .inp (vXiStmt s)
  , shouldVerify := .inp (vShouldVerify s) }

/-- Everything R8 needs, evaluated ONCE. -/
structure FinData where
  fp : FinProg
  vals : Array Nat
  bActual : Nat
  cipShift : Nat
  bShift : Nat
  permShift : Nat
  xiStmt : Nat
  xiHi : Nat
  deriving Repr, Inhabited

/-- R8's `.inp` lookup: the lifted challenges, §8g's deferred `r`, R5's two outputs, R6's `perm`
slot, R7's squeeze, and the four statement words — every one of them a variable another rung's rows
compute. -/
def finInputEnv (s : StepShape) (d : SpongeData) (f : FtData) (df : DefData)
    (segB : SegData) (specB : SegSpec) (rv : Nat) : VarEnv :=
  let sqv := frSqueezeVal segB specB
  let permA := f.vals.getD f.fp.slots.perm 0
  [ (vLift s s.zetaChal, (liftOf s d s.zetaChal : Int))
  , (vDLift s 1, (rv : Int))
  , (vAcc s s.bRounds, (df.accs.getLastD 0 : Int))
  , (vCa s s.cipEvals, (df.ca.getLastD 0 : Int))
  , (aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm, (permA : Int))
  , (frSqueezeVar s, (sqv : Int))
  , (vCipShift s, (shiftT1 (df.ca.getLastD 0) : Int))
  , (vBShift s, (shiftT1 (bActualOf s d df rv) : Int))
  , (vPermShift s, (shiftT1 permA : Int))
  , (vXiStmt s, ((sqv % 2 ^ 128 : Nat) : Int))
  , (vShouldVerify s, 1) ]
  ++ (List.range s.bRounds).map (fun k => (vLift s (s.uChal k), (liftOf s d (s.uChal k) : Int)))

/-- The HONEST config: `lowest_128_bits`' high part, and — because every `Field.equal` leg holds —
`bit = 1`, `inv = 0` in all four gadgets, with `verified = should_verify = 1`. §16 re-runs this at
bent inputs, where the honest witness is `bit = 0` and the assert FAILS. -/
def finCfgOf (s : StepShape) (hi : Nat) : FinCfg :=
  { rounds := s.bRounds, omega := FT_OMEGA, shiftC := SHIFT_C, hiXi := hi
  , eqInv := List.replicate 4 0, eqBit := List.replicate 4 1
  , verified := 1 }

def runFin (s : StepShape) (d : SpongeData) (f : FtData) (df : DefData)
    (segB : SegData) (specB : SegSpec) (rv : Nat) : FinData :=
  let sqv := frSqueezeVal segB specB
  let permA := f.vals.getD f.fp.slots.perm 0
  let p := finProgOf (finWireOf s f) (finCfgOf s (sqv / 2 ^ 128))
  let lk := envLookupAt (envIndex (finInputEnv s d f df segB specB rv))
  { fp := p, vals := aEval lk p.prog, bActual := bActualOf s d df rv
  , cipShift := shiftT1 (df.ca.getLastD 0), bShift := shiftT1 (bActualOf s d df rv)
  , permShift := shiftT1 permA, xiStmt := sqv % 2 ^ 128, xiHi := sqv / 2 ^ 128 }

/-- **R8's rows**: the compiled finalize program, the TWO `assert_128_bits` chains its
`lowest_128_bits` owes (`util.ml:98-99` — the high part unconditionally, the low part because
`Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true`), and its σ-only probes.

⚑ THE HIGH CHAIN IS THE SOUNDNESS-BEARING ONE. `hi` is an `AOp.wit`: no row defines it, so before
this chain the decomposition `xiActual = squeeze − 2¹²⁸·hi` was ONE equation in TWO unknowns and the
prover could hand `xi_correct` any 128-bit ξ he liked — the fold's own multiplier, since §8g's chain
0 lifts that same statement word. §12c exhibits that witness: R8's program ACCEPTS it (`out = 1`)
and the high chain REFUSES it. The chains' sources are the program's OWN cells, not fresh copies. -/
def finRows (s : StepShape) (f : FtData) (fn : FinData) (wired : Bool) : List SRow :=
  let base := baseFin s f
  let V := aVarAt base fn.fp.prog
  aRows base fn.fp.prog
  ++ rangeRows s (RNG_FIN_HI s) (V fn.fp.slots.xiHi)
       (fn.vals.getD fn.fp.slots.xiHi 0) wired
  ++ rangeRows s (RNG_FIN_LO s) (V fn.fp.slots.xiActual)
       (fn.vals.getD fn.fp.slots.xiActual 0) wired
  ++ [ probeRow wired (V fn.fp.slots.finalized) (V fn.fp.slots.bActual)
     , probeRow wired (V fn.fp.slots.cipUsed) (V fn.fp.slots.xiActual)
     , probeRow wired (V fn.fp.slots.permUsed) (V fn.fp.slots.bUsed) ]

/-! ## §8g — the DEFERRED CHALLENGES: the fr-sponge FEEDS the fold.

`step_verifier.ml:1006-1013`. Before this section the C8 fold multiplied by two R1 transcript
challenges and the fr-sponge's squeeze reached nothing but `xi_correct` — the fold was CHECKED
against the squeeze and not FED by it (the module header's simplification #10). Here the two
multipliers are `to_field_checked` chains whose sources are the fr-sponge's own two squeezes:

  * **chain 0 — ξ.** Source is the STATEMENT's ξ word (`vXiStmt`), which is already a
    `Challenge.t`, so the chain's tie is `Field.Assert.equal n scalar` and not a decomposition. R8's
    `xi_correct` is what binds that word to the fr-sponge's FIRST squeeze — upstream's own two-step
    (`let xi_correct = … xi_actual … in let xi = scalar xi`), so a prover cannot move the fold
    without failing the assert.
  * **chain 1 — r.** Source is the fr-sponge's SECOND squeeze, decomposed by `lowest_128_bits`.
    Upstream carries no statement word for `r` at all: `scalar (Scalar_challenge.create r_actual)`.

⚑ THE RUNG CONSEQUENCE, stated plainly. Chain 0's source is a statement word and its rows ride with
R5, so ξ is derived at EVERY rung from r5 up. Chain 1's source is an R7 variable, so its rows ride
with R7: at r5/r6 (sub-circuits strictly below the fr-sponge) the fold's `r` is a free witness, and
at r7/r8 it is the squeeze's lift. That is the same ladder position `vEz 3` (R6's `ft_eval0`) and
the four statement words already occupy, and §15 pins which rung binds which. -/

/-- The two deferred prechallenges and their discarded high parts. -/
structure DefcData where
  /-- `lowest_128_bits` of the fr-sponge's first (ξ) and second (r) squeeze. -/
  pre : List Nat
  /-- the high parts. Chain `0`'s is unused — its source is already a `Challenge.t`. -/
  hi : List Nat
  deriving Repr, Inhabited

def runDefc (segB : SegData) (specB : SegSpec) : DefcData :=
  let sq1 := frSqueezeVal segB specB
  let sq2 := frSqueeze2Val segB specB
  { pre := [sq1 % 2 ^ 128, sq2 % 2 ^ 128], hi := [0, sq2 / 2 ^ 128] }

/-- Chain `c`'s LIFTED value — the multiplier itself. -/
def DefcData.lift (dc : DefcData) (s : StepShape) (c : Nat) : Nat :=
  liftVal s (dc.pre.getD c 0)

/-- **§8g's rows** for chain `c`, over the source `src`. -/
def defcRows (s : StepShape) (dc : DefcData) (c : Nat) (src : PVar) (split : Bool)
    (wired : Bool) : List SRow :=
  tfcRows s (defcVars s c) src split (dc.pre.getD c 0) wired

/-- Chain 0 (ξ), from the statement word — rides with R5. -/
def xiDefRows (s : StepShape) (dc : DefcData) (wired : Bool) : List SRow :=
  defcRows s dc 0 (vXiStmt s) false wired
/-- Chain 1 (r), from the fr-sponge's second squeeze — rides with R7, and so does the
`assert_128_bits` of ITS high part (`squeeze_scalar`'s `~constrain_low_bits:false` asserts the high
part only; `step_verifier.ml:190-192`). -/
def rDefRows (s : StepShape) (dc : DefcData) (wired : Bool) : List SRow :=
  defcRows s dc 1 (frSqueeze2Var s) true wired
  ++ rangeRows s (s.chals + 1) (vDHi s 1) (dc.hi.getD 1 0) wired

/-! ## §9 — the whole assembly: rows, environment, placement, witness. -/

/-- Everything the schedule and the environment read, evaluated ONCE. -/
structure StepData where
  sh : StepShape
  sp : SpongeData
  msm : MsmData
  ipa : IpaData
  ft : FtData
  /-- §6b's two scalar cells, read off R6's program. -/
  ftw : FtcWire
  /-- ⚑ `Common.ft_comm` — the MSM whose output is R4 round `FTC_ROUND`'s base. -/
  ftc : FtcData
  defc : DefcData
  df : DefData
  fin : FinData
  segA : SegData
  segB : SegData
  segC : SegData
  specA : SegSpec
  specB : SegSpec
  specC : SegSpec
  deriving Inhabited

/-- ⚑ THE DEPENDENCY ORDER, and why the fr-sponge now runs BEFORE the fold. Since §8g the C8 fold's
own multipliers are `to_field_checked` of the fr-sponge's two squeezes, so segment B is evaluated
first and `runDef` is fed from it. Nothing the fr-sponge absorbs depends on `combined_inner_product`
(segment B absorbs the digest of segment A, `ft_eval1`, the two public-poly evaluations and the 43
columns — R6's and R5's fixtures), so the order is a chain and not a cycle. -/
def mkStepWith (s : StepShape) (bs : List (Nat × Nat)) : StepData :=
  -- ⚑⚑ **PASS 1 — the transcript through ζ.** `absorb sponge Scalar advice.combined_inner_product`
  -- (`step_verifier.ml:256`) comes AFTER `let zeta = sample_scalar ()` (`:568`), so blocks 0 …
  -- `sqBlock zetaChal` do not depend on it and β/γ/α/ζ are already exact in this pass. §12i pins
  -- that as an EQUALITY over the four, which is the machine-checked form of "upstream has no cycle".
  let sp0 := runSponge s bs (0, 0)
  let ft0 := runFt s sp0
  -- ⚑ segment A reads `prev_challenges` and NOT the transcript, so nothing below depends on a
  -- squeeze taken after ζ. That is the other half of why two passes suffice.
  let specA := optSpec s
  let segA := runSeg specA
  let dg : PVar × Nat :=
    (sgSt (baseSegA s) (nbA s) 1 specA.blocks 0,
     (segA.states.getLastD []).getD 0 0)
  let specB0 := frSpec s dg ft0.out
  let defc0 := runDefc (runSeg specB0) specB0
  -- ⚑ the SHIFTED value, because that is what `:257-259` unwraps and absorbs
  -- (`Shifted_value.Type2.Shifted_value x -> x`) and it is exactly `vCipShift`, the statement word
  -- R8's `combined_inner_product_correct` ties back to this same Horner output.
  let cipV := shiftT1 ((runDef s sp0 ft0.out (defc0.lift s 0) (defc0.lift s 1)).ca.getLastD 0)
  -- **PASS 2 — the real transcript**, carrying `(combined_inner_product, its `Boolean.var`)`.
  let sp := runSponge s bs (cipV, CIP_BIT)
  let msm := runMsm s bs sp
  -- ⚑ R6 next: `ft_eval0` is the `ft` column R5's `combined_inner_product` folds — and since §6b
  -- its `perm` / `ζ^n` slots are also `Common.ft_comm`'s scalars, so R6 runs BEFORE the fold. That
  -- is a chain and not a cycle: `runFt` reads only β/γ/α/ζ, and fold round
  -- `FTC_ROUND`'s base is `ft_comm`'s output rather than a supplied commitment.
  let ft := runFt s sp
  let ftw := ftcWireOf s ft
  let ftc := runFtc s ftw
  let ipa := runIpa s bs sp ftc.out
  let ftv := ft.out
  let specB := frSpec s dg ftv
  let segB := runSeg specB
  -- ⚑ §8g: ξ and r, squeezed from the fr-sponge and lifted, are the fold's multipliers.
  let defc := runDefc segB specB
  let df := runDef s sp ftv (defc.lift s 0) (defc.lift s 1)
  let specC := hmSpec s msm ipa
  { sh := s, sp := sp, msm := msm, ipa := ipa, ft := ft, ftw := ftw, ftc := ftc
  , defc := defc, df := df
  , fin := runFin s sp ft df segB specB (defc.lift s 1)
  , segA := segA, segB := segB, segC := runSeg specC
  , specA := specA, specB := specB, specC := specC }

/-- The assembly on the HONEST supplied commitments — block 539508's own. -/
def mkStep (s : StepShape) : StepData := mkStepWith s (stepBases s)

/-- **R7's rows** — the three sponge segments of §8e, then §8g's `r` chain over the fr-sponge's
second squeeze. -/
def absRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  segRows (baseSegA s) t.specA t.segA wired
  ++ segRows (baseSegB s) t.specB t.segB wired
  ++ idxConstRows s
  ++ segRows (baseSegC s) t.specC t.segC wired
  ++ idxDigestRows s wired
  ++ rDefRows s t.defc wired

/-- **THE ROW SCHEDULE**, in the order `verify_one` runs it. -/
def stepRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  transcriptRows s t.sp wired
  ++ endoConstRow s
  ++ (List.range s.chals).flatMap (challengeRows s t.sp wired)
  ++ msmRows s t.msm wired
  ++ ftcRows s t.ftw t.ftc wired
  ++ ipaRows s t.ipa wired
  ++ deferredRows s wired
  ++ branchRows s wired
  ++ xiDefRows s t.defc wired
  ++ cipRows s wired
  ++ closingRows s
  ++ ftRows s t.ft wired
  ++ absRows t wired
  ++ finRows s t.ft t.fin wired

/-- The CIRCUIT's variable → value assignment (public words are added by `stepEnv`). -/
def circuitEnv (t : StepData) : VarEnv :=
  let s := t.sh
  (List.range (s.blocks + 1)).flatMap (fun b =>
    let st := t.sp.states.getD b []
    (List.range 3).map (fun j => (vSt s b j, (st.getD j 0 : Int))))
  -- ⚑ `vPost` is indexed by absorb ORDINAL and the sponge trajectory by BLOCK, so the schedule
  -- (`absBlock`) is what relates them since the R1 interleaving.
  ++ (List.range s.absorbs).flatMap (fun a =>
      let b := absBlock s a
      let pre := t.sp.states.getD b []
      let ms := t.sp.msgs.getD b []
      (List.range 2).map (fun j =>
        (vPost s a j, (((pre.getD j 0 + ms.getD j 0) % pN : Nat) : Int))))
  -- ⚑ ONE `vMsg` cell is left at `shapeStep`: block `oDigest`'s second lane, the rate-2 pad an odd
  -- item count forces. Every other absorbed word is a variable some sub-circuit reads.
  ++ (List.range s.absorbs).flatMap (fun a =>
      (List.range 2).filterMap (fun j =>
        if msgVar s a j == vMsg s a j then some (vMsg s a j, (msgVal a j : Int)) else none))
  ++ (List.range s.chals).flatMap (fun c =>
      let accs := emsAccs s (chalOf s t.sp c)
      (List.range (s.emsRows + 1)).flatMap (fun k =>
        let a := accs.getD k (0, 2, 2)
        [ (vN s c k, (a.1 : Int)), (vA s c k, (a.2.1 : Int)), (vB s c k, (a.2.2 : Int)) ])
      ++ [ (vHi s c, (hiOf s t.sp c : Int))
         , (vLiftT s c, (liftTOf s t.sp c : Int)), (vLift s c, (liftOf s t.sp c : Int)) ])
  ++ [ (vEndoR s, (ENDO_R : Int)) ]
  -- §5b: the `assert_128_bits hi` chains — one per SPLIT source, R2's `chals` and §8g's `r`…
  ++ (List.range s.chals).flatMap (fun c => rngEnv s c (hiOf s t.sp c))
  ++ rngEnv s (s.chals + 1) (t.defc.hi.getD 1 0)
  -- …and R8's own `lowest_128_bits`, BOTH parts (`~constrain_low_bits:true`), over the compiled
  -- finalize program's OWN cells rather than over a parallel computation of them.
  ++ rngEnv s (RNG_FIN_HI s) (t.fin.vals.getD t.fin.fp.slots.xiHi 0)
  ++ rngEnv s (RNG_FIN_LO s) (t.fin.vals.getD t.fin.fp.slots.xiActual 0)
  -- §8g: the two DEFERRED challenge chains (ξ from the statement word, r from the fr-sponge's
  -- second squeeze), each a full `to_field_checked` accumulator trace.
  ++ (List.range N_DEFC).flatMap (fun c =>
      let v := t.defc.pre.getD c 0
      let accs := emsAccs s v
      (List.range (s.emsRows + 1)).flatMap (fun k =>
        let a := accs.getD k (0, 2, 2)
        [ (vDN s c k, (a.1 : Int)), (vDA s c k, (a.2.1 : Int)), (vDB s c k, (a.2.2 : Int)) ])
      ++ [ (vDHi s c, (t.defc.hi.getD c 0 : Int))
         , (vDLiftT s c, (liftTVal s v : Int)), (vDLift s c, (liftVal s v : Int)) ])
  ++ (List.range s.msmTerms).flatMap (fun i =>
      let td := t.msm.terms.getD i default
      [ (mpx s (pT s i), (td.T.1 : Int)), (mpy s (pT s i), (td.T.2 : Int)) ]
      ++ (List.range (s.msmChunks + 1)).flatMap (fun j =>
          let a := td.accs.getD (5 * j) (0, 0)
          [ (mpx s (pAcc s i j), (a.1 : Int)), (mpy s (pAcc s i j), (a.2 : Int)) ])
      ++ (List.range s.msmChunks).map (fun j => (vSN s i j, (td.ns.getD (5 * j) 0 : Int))))
  ++ (List.range (s.msmTerms - 1)).flatMap (fun a =>
      let p := t.msm.sums.getD a (0, 0)
      [ (mpx s (pSum s a), (p.1 : Int)), (mpy s (pSum s a), (p.2 : Int)) ])
  ++ (List.range s.ipaRounds).flatMap (fun r =>
      let T := t.ipa.bases.getD r (0, 0)
      [ (ipx s (qT s r), (T.1 : Int)), (ipy s (qT s r), (T.2 : Int)) ]
      ++ (List.range (s.ipaBlocks + 1)).flatMap (fun e =>
          let a := (t.ipa.accs.getD r []).getD e (0, 0)
          [ (ipx s (qAcc s r e), (a.1 : Int)), (ipy s (qAcc s r e), (a.2 : Int)) ])
      ++ (List.range s.ipaBlocks).map (fun e =>
          (vQN s r e, ((t.ipa.ns.getD r []).getD e 0 : Int)))
      -- §7's seed: `φ(t)`'s x and the `p = t + φ(t)` intermediate `acc₀ = p + p` doubles.
      ++ [ (vQEndo s r, ((endoQ T).1 : Int))
         , (ipx s (qP s r), ((endoP T).1 : Int)), (ipy s (qP s r), ((endoP T).2 : Int)) ])
  ++ (List.range s.ipaRounds).flatMap (fun a =>
      let p := t.ipa.sums.getD a (0, 0)
      [ (ipx s (qSum s a), (p.1 : Int)), (ipy s (qSum s a), (p.2 : Int)) ])
  -- ⚑ `sg_old[0]` (the fold's `~init`), `delta`, and `check_bulletproof`'s `endo q c + delta` tail.
  ++ (let g := Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
      let dl := Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
      let q := t.ipa.sums.getLastD (0, 0)
      [ (ipx s (qInit s), (g.1 : Int)), (ipy s (qInit s), (g.2 : Int))
      , (ipx s (qDel s), (dl.1 : Int)), (ipy s (qDel s), (dl.2 : Int))
      , (vLhsEndo s, ((endoQ q).1 : Int))
      , (ipx s (qLhsP s), ((endoP q).1 : Int)), (ipy s (qLhsP s), ((endoP q).2 : Int))
      , (ipx s (qLhsOut s), (t.ipa.lhsAdd.getD 4 0 : Int))
      , (ipy s (qLhsOut s), (t.ipa.lhsAdd.getD 5 0 : Int)) ]
      ++ (List.range (s.ipaBlocks + 1)).flatMap (fun e =>
          let a := t.ipa.lhsAccs.getD e (0, 0)
          [ (ipx s (qLhsAcc s e), (a.1 : Int)), (ipy s (qLhsAcc s e), (a.2 : Int)) ])
      ++ (List.range s.ipaBlocks).map (fun e => (vLhsN s e, (t.ipa.lhsNs.getD e 0 : Int))))
  -- §7b: `assert_on_curve`'s two intermediates per ABSORBED commitment — the fold's bases, `t_comm`'s
  -- chunks, and since the R1 interleaving `sg_old[0]` and `delta`.
  ++ (List.range (nOnC s)).flatMap (fun k =>
      let l := (absRoundList s).length
      let x := if k < l then (t.ipa.bases.getD ((absRoundList s).getD k 0) (0, 0)).1
               else if k < l + tCommN s then (ftcTc (k - l)).1
               else if k == l + tCommN s then Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY.1
               else Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY.1
      [ (vOcX2 s k, (fMul x x : Int)), (vOcX3 s k, (fMul (fMul x x) x : Int)) ])
  -- ⚑ §6b: `Common.ft_comm`'s MSM — the eight `scale_fast2` ladders, `t_comm`'s absorbed
  -- coordinates, the `Ops.add_fast` chain and `Shifted_value.Type2`'s two split pairs.
  ++ (List.range (ftcTerms s)).flatMap (fun k =>
      let tm := t.ftc.terms.getD k default
      let hx := (tm.td.accs.getLastD (0, 0)).1
      let hy := (tm.td.accs.getLastD (0, 0)).2
      let od := ftcScalVal t.ftw (ftcScalOf k) % 2
      let dx := fSub hx tm.hMg.1
      let dy := fSub hy tm.hMg.2
      (List.range (FTC_CHUNKS + 1)).flatMap (fun j =>
        let a := tm.td.accs.getD (5 * j) (0, 0)
        [ (ftcAccX s k j, (a.1 : Int)), (ftcAccY s k j, (a.2 : Int)) ])
      ++ (List.range FTC_CHUNKS).map (fun j =>
          (ftcN s k j, (tm.td.ns.getD (5 * j) 0 : Int)))
      ++ [ (ftcTop s k, (tm.bits.headD 0 : Int))
         , (ftcNegY s k, (fSub 0 tm.td.T.2 : Int))
         , (ftcHmX s k, (tm.hMg.1 : Int)), (ftcHmY s k, (tm.hMg.2 : Int))
         , (ftcDX s k, (dx : Int)), (ftcDY s k, (dy : Int))
         , (ftcMX s k, (fMul od dx : Int)), (ftcMY s k, (fMul od dy : Int))
         , (ftcResX s k, (tm.res.1 : Int)), (ftcResY s k, (tm.res.2 : Int)) ])
  ++ (List.range (tCommN s)).flatMap (fun i =>
      [ (vTcX s i, ((ftcTc i).1 : Int)), (vTcY s i, ((ftcTc i).2 : Int)) ])
  ++ (List.range (tCommN s)).flatMap (fun a =>
      let p := t.ftc.adds.getD a (0, 0)
      [ (ftcAddX s a, (p.1 : Int)), (ftcAddY s a, (p.2 : Int)) ])
  ++ [ (ftcNegQ s, (fSub 0 (t.ftc.terms.getD (tCommN s) default).res.2 : Int)) ]
  ++ (List.range N_FTC_SCAL).flatMap (fun c =>
      let v := ftcScalVal t.ftw c
      [ (ftcDiv2 s c, ((v / 2 : Nat) : Int)), (ftcOdd s c, ((v % 2 : Nat) : Int)) ])
  ++ (List.range (s.bRounds + 1)).map (fun k => (vZ s k, (t.df.zs.getD k 0 : Int)))
  ++ (List.range s.bRounds).map (fun k => (vFac s k, (t.df.facs.getD k 0 : Int)))
  ++ (List.range (s.bRounds + 1)).map (fun k => (vAcc s k, (t.df.accs.getD k 0 : Int)))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [ (vEz s k, (t.df.ez.getD k 0 : Int)), (vEw s k, (t.df.ew.getD k 0 : Int))
      , (vDk s k, (t.df.dk.getD k 0 : Int)), (vCk s k, (t.df.ck.getD k 0 : Int))
      , (vTk s k, (t.df.tk.getD k 0 : Int)) ])
  ++ (List.range (s.cipEvals + 1)).map (fun i => (vCa s i, (t.df.ca.getD i 0 : Int)))
  -- R6: the compiled ft program's slots.
  ++ aEnvOf (baseFtS s) t.ft.fp.prog t.ft.vals
  -- R7: the three sponge segments, `sponge_after_index`'s own pinned commitments and its squeeze,
  -- and the two APP-STATE words that are all that is left of the old fixture prefix (§3c).
  ++ (List.range N_HM_APP).map (fun i => (vHm s i, (hmVal i : Int)))
  -- ⚑ `prev_challenges` — segments A and C absorb these SAME variables (`step_verifier.ml:956`,
  -- `step_main.ml:80`).
  ++ (List.range (2 * s.bRounds)).map (fun i => (vPrevChal s i, (prevChalVal i : Int)))
  ++ (idxOwn s).flatMap (fun k =>
      [ (vIdxX s k, (idxVal k 0 : Int)), (vIdxY s k, (idxVal k 1 : Int)) ])
  ++ (List.range 3).map (fun j => (vIdxD s j, (idxDigestState.getD j 0 : Int)))
  ++ segEnv (baseSegA s) t.specA t.segA
  ++ segEnv (baseSegB s) t.specB t.segB
  ++ segEnv (baseSegC s) t.specC t.segC
  -- R8: the four STATEMENT words and the compiled finalize program's slots.
  ++ [ (vCipShift s, (t.fin.cipShift : Int)), (vBShift s, (t.fin.bShift : Int))
     , (vPermShift s, (t.fin.permShift : Int)), (vXiStmt s, (t.fin.xiStmt : Int))
     -- §8h: `branch_data` and the two `proofs_verified_mask` bits it packs.
     , (vShouldVerify s, 1), (vCipBit s, (CIP_BIT : Int))
     , (vBranch s, (branchPacked : Int)), (vDomLog2 s, (BRANCH_DOMAIN_LOG2 : Int))
     , (vMask s 0, (MASK_BITS.getD 0 0 : Int)), (vMask s 1, (MASK_BITS.getD 1 0 : Int))
     , (vMaskPack s, ((MASK_BITS.getD 0 0 + 2 * MASK_BITS.getD 1 0 : Nat) : Int)) ]
  ++ aEnvOf (baseFin s t.ft) t.fin.fp.prog t.fin.vals

/-- The full environment: the circuit's variables, then the `pubWords` public words, whose values
are READ OUT of the circuit env at the exposed variables — so a public word and the variable the
closing row ties it to hold ONE value by construction, exactly as a copy class does. -/
def stepEnv (t : StepData) : VarEnv :=
  let ce := circuitEnv t
  let ix := envIndex ce
  ce ++ (List.range t.sh.pubWords).map (fun i =>
    ((.external i : PVar), envLookupAt ix ((exposedVars t.sh).getD i (xv 0))))

/-- The public vector the verifier is handed, in order. -/
def stepPublic (t : StepData) : List Int :=
  let ix := envIndex (circuitEnv t)
  (List.range t.sh.pubWords).map (fun i =>
    envLookupAt ix ((exposedVars t.sh).getD i (xv 0)))

def stepGates (rows : List SRow) : List PGate :=
  rows.map (fun r => { kind := r.kind, permVars := r.perm, coeffs := r.coeffs })

/-- The composed 15 × `(pubSize + nRows)` witness grid. The `pubSize` public rows carry the public
word at col 0 (`prover.rs:270`: the prover's public vector IS witness column 0, rows `0..n`); the
circuit rows start at `pubSize` (`compute_witness`, `transaction.rs:3854-3872`). Built with the
ROW-INDEXED front ends (`envIndex`/`gateVarWitnessAt`), which is what keeps the assembly linear
rather than quadratic in the row count. -/
def stepWitness (t : StepData) (pubSize : Nat) (rows : List SRow) : List (List Int) :=
  let ix := envIndex (stepEnv t)
  let n := rows.length
  compose 15 (pubSize + n)
    (((List.range pubSize).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
     :: (rows.zip (List.range n)).map (fun ri =>
          gateVarWitnessAt ix (pubSize + ri.2)
            { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
          ++ ri.1.advice.map (fun cv => ((⟨pubSize + ri.2, cv.1⟩ : Cell), cv.2))))

/-- Read circuit row `r` out of the ASSEMBLED column-major grid (all 15 columns). -/
def gridRow (w : List (List Int)) (r : Nat) : List Nat :=
  (List.range 15).map (fun c => (gridAt w ⟨r, c⟩).toNat)

/-- **THE FAIL-CLOSED PLACEMENT.** `placeChecked`, never `place`: `auxOverlapsPublic` /
`referenceInGap` / `inertPublicWord` REFUSE rather than reinterpret. A refusal yields the empty
placement, which every downstream `#guard` then fails loudly. -/
def placedOf (pubSize : Nat) (gs : List PGate) : List PlacedGate :=
  match placeChecked ⟨pubSize, AUX⟩ gs with
  | .ok p => p
  | .error _ => []

/-- Did the placement refuse, and why. -/
def refusalOf (pubSize : Nat) (gs : List PGate) : Option PlaceRefusal :=
  match placeChecked ⟨pubSize, AUX⟩ gs with
  | .ok _ => none
  | .error e => some e

/-! ## §10 — the RUNGS.

`Rung` names how far up the assembly a circuit reaches. Rungs 1–4 are placed at `pubSize = 0`
(their public output is not yet tied); rung 5 IS the closing rung and is placed at `pubSize =
pubWords` through `placeChecked`. Each rung is a superset of the one below, so a regression cannot
hide behind a smaller circuit. -/

inductive Rung where
  | transcript | challenges | msm | ipa | full | ftEval0 | absorb | finalize
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "r1_transcript" | .challenges => "r2_challenges" | .msm => "r3_msm"
  | .ipa => "r4_ipa" | .full => "r5_full" | .ftEval0 => "r6_ft_eval0"
  | .absorb => "r7_absorption" | .finalize => "r8_finalize"

/-- Rung `k`'s rows.

⚑ **EVERY sub-circuit's row-set function is REACHED FROM HERE.** `rungRows` is the ONLY entry point
the emit driver has, and a sub-circuit whose rows live in a function nobody calls proves nothing:
measured on 2026-08-01, `cipRows` was absent from this `match` while every probe of every proved r5
still passed, so the `combined_inner_product` Horner chain the commit subject named was in NO proved
circuit and `vCa cipEvals` reached the public tie as a FREE variable. §15 now pins each rung's length
as the sum of its own sub-lists AND pins `stepRows = rungRows .finalize`, so a row-set that drops out
of this function is a red, not a silence. -/
def rungRows (t : StepData) (k : Rung) (wired : Bool) : List SRow :=
  let s := t.sh
  let a := transcriptRows s t.sp wired
  let b := endoConstRow s ++ (List.range s.chals).flatMap (challengeRows s t.sp wired)
  let c := msmRows s t.msm wired ++ ftcRows s t.ftw t.ftc wired
  let d := ipaRows s t.ipa wired
  let e := deferredRows s wired ++ branchRows s wired ++ xiDefRows s t.defc wired
           ++ cipRows s wired ++ closingRows s
  let f := ftRows s t.ft wired
  let g := absRows t wired
  let h := finRows s t.ft t.fin wired
  match k with
  | .transcript => a
  | .challenges => a ++ b
  | .msm => a ++ b ++ c
  | .ipa => a ++ b ++ c ++ d
  | .full => a ++ b ++ c ++ d ++ e
  | .ftEval0 => a ++ b ++ c ++ d ++ e ++ f
  | .absorb => a ++ b ++ c ++ d ++ e ++ f ++ g
  | .finalize => a ++ b ++ c ++ d ++ e ++ f ++ g ++ h

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at and above it. -/
def rungPub (s : StepShape) : Rung → Nat
  | .transcript | .challenges | .msm | .ipa => 0
  | _ => s.pubWords

/-- Rung `k`'s absolute probe rows, in schedule order. -/
def rungProbeRows (t : StepData) (k : Rung) : List Nat :=
  let rows := rungRows t k true
  let p := rungPub t.sh k
  ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map (fun ri => p + ri.2)

/-! ### The renderer.

Same JSON the pickles harnesses parse, plus two fields the earlier ones did not need:
`public_input` (a `pubSize > 0` circuit is not runnable without it — `kimchi/src/verifier.rs:816`
rejects a length mismatch outright, so omitting it would force the harness to re-derive the public
input in Rust, which is witness authoring) and `probe_rows`, the absolute rows of the σ-only probes.
`probe_rows` travels WITH the circuit so the harness aims its tampers at what the Lean schedule
actually emitted rather than at a hand-copied constant that a schedule drift would silently
invalidate. -/

private def q (s : String) : String := "\"" ++ s ++ "\""
private def renderCell (c : Cell) : String := "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"
private def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"
private def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => q (toString i))) ++ "]"
private def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
private def renderGate (g : PlacedGate) : String :=
  "{" ++ q "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ q "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ q "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"

/-- A provable circuit with its public vector and its probe rows. -/
def renderStepCircuit (name : String) (pubSize numRows : Nat) (gs : List PlacedGate)
    (w : List (List Int)) (pub : List Int) (probes : List Nat) : String :=
  "{" ++ q "name" ++ ":" ++ q name ++ ","
       ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
       ++ q "public_input" ++ ":" ++ renderIntList pub ++ ","
       ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
       ++ q "probe_rows" ++ ":" ++ renderNatList probes ++ ","
       ++ q "gates" ++ ":[" ++ String.intercalate "," (gs.map renderGate) ++ "],"
       ++ q "witness" ++ ":[" ++ String.intercalate "," (w.map renderIntList) ++ "]}"

/-- Rung `k`'s emitted JSON (WIRED or UNWIRED control). -/
def rungJson (t : StepData) (k : Rung) (wired : Bool) (name : String) : String :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderStepCircuit name p (p + rows.length)
    (placedOf p (stepGates rows)) (stepWitness t p rows)
    (if p == 0 then [] else stepPublic t) (rungProbeRows t k)

/-! ## §11 — the committed shape, sized against the `verify_one` line items. -/

/-- **THE COMMITTED SHAPE.** ⚑ Since §3b three of these are MEASURED off the real artifact rather
than reverse-engineered from a row count:

  * `msmTerms = 40` is the devnet Wrap verifier key's own `public = 40`, which is exactly how many
    `lagrange_commitment`s `multiscale_known` scales — and exactly the length of
    `MinaStepPrevCommitments.LAGRANGE_XY`. (It was 38, chosen to make 38×26×2 ≈ the measured 1972
    x_hat rows; the real number is 40 and now says so.)
  * `ipaRounds = 76` = 46 `combine_split_commitments` folds (`COMBINE_XY`'s 47 commitments, less the
    one the accumulator starts at) + `bullet_reduce`'s 30 `(L,R)` endos. Both lists are on disk at
    exactly those lengths.
  * ⚑ **`absorbs = 59` is `⌈117/2⌉`, and 117 is `verify_one`'s own sponge-item count**
    (`ABSORB_ITEMS`, §2, item by item at `step_verifier.ml:534-567,199,256,321`). It was **71** until
    2026-08-02 — `2·71 = 142` field elements against 117 — and that 25-word overshoot was being
    reported as twenty-five unwired ABSORPTIONS, which is a backlog item, rather than as a shape
    that swallows words upstream never feeds it, which is an error. (24 of the 25 go; the 25th is
    the pad lane an odd item count forces.) The 59 are: block 0
    (⚑ `index_digest`, §3c — upstream's own first absorption, one `Field`, its second lane the one
    PAD lane an odd item count forces), the 48 blocks that carry a fold commitment (18 fold + 30
    gammas), the 7 that carry `t_comm`'s quotient chunks (§6b), and **three** for the absorptions
    still unwired — `sg_old[0]`, `combined_inner_product` as field+bit, `delta` (`UNWIRED_ITEMS`).

`chals = 23` is β, γ, α, ζ, ξ, r, u, c + the 15 `bullet_reduce` squeezes; `msmChunks = 26` is the
128-bit `scale_fast2` — ⚑ #2 has the MEASURED per-word width census, and 8 of the 40 words are
255-bit while 22 are 128 and one is 10, so a uniform widening is the wrong move; `bRounds = 16` is `Step_bp_vec = N16`;
`cipEvals = 47` is `N45` + `Wrap_hack`'s two; `pubWords = 67` is Step's `PRIMARY_LEN`. -/
def shapeStep : StepShape :=
  { absorbs := 59, chals := 23, emsRows := 8
  , msmTerms := 40, msmChunks := 26
  , ipaRounds := 76, ipaBlocks := 32
  , bRounds := 16, cipEvals := 47, tComms := 7, pubWords := 67 }

/-- A small shape for the fast in-CI pins (the committed one is emitted by the driver).

⚑ `cipEvals` is **47 at both scales** and is no longer free: R6 slices the previous proof's 43
evaluation columns out of it (`EV_PREFIX = 4` + 43), and R7 absorbs those same 43 at two points. A
shape with fewer columns is not a smaller `verify_one`, it is a different one. -/
def shapeSmoke : StepShape :=
  -- ⚑ `absorbs` is 7 since §6b: block 0 is `index_digest`'s, blocks 1–3 carry the three absorbed
  -- fold commitments, blocks 4–6 carry `tCommN = 3` `t_comm` chunks. It still leaves ONE free
  -- `vMsg` block (block 0's second lane), which is what lets the smoke pins see the residue at all.
  { absorbs := 10, chals := 8, emsRows := 8
  , msmTerms := 3, msmChunks := 26
  -- ⚑ `bRounds` is EVEN so the opt-sponge's rate-2 blocks do not straddle the two previous proofs:
  -- each proof contributes `bRounds` challenge words and a block absorbs two, so a block belongs to
  -- exactly one mask bit. (`shapeStep`'s 16 is even for the same reason — `Step_bp_vec = N16`.)
  -- ⚑ `ipaRounds` is 5 and not 3 since §6b: round `FTC_ROUND = 2` is now COMPUTED, so a 3-round
  -- shape would have NO `.const` fold base left and §12b's constant-provenance pins would be
  -- vacuous. At 5, rounds 0/1/3 are absorbed, 2 is computed and 4 is a verifier-key constant —
  -- all three provenances present.
  , ipaRounds := 5, ipaBlocks := 32
  , bRounds := 4, cipEvals := 47, tComms := 3, pubWords := 12 }

/-! ## §12 — the in-CI pins, on the SMOKE instance (`#guard`, interpreter-reduced).

The committed step-scale instance is emitted and PROVED by the harness; these pins run in `lake
build` and cover every structural property the harness cannot see. Nullary `def`s so the interpreter
evaluates the chains ONCE. -/

def tS : StepData := mkStep shapeSmoke
def rowsS : List SRow := rungRows tS .finalize true
def rowsUS : List SRow := rungRows tS .finalize false
def nRowsS : Nat := rowsS.length
def pubS : Nat := shapeSmoke.pubWords
def gatesS : List PGate := stepGates rowsS
def gatesUS : List PGate := stepGates rowsUS
def placedS : List PlacedGate := placedOf pubS gatesS
def placedUS : List PlacedGate := placedOf pubS gatesUS
def posS : List (PVar × Cell) := circuitPositions pubS gatesS
def posUS : List (PVar × Cell) := circuitPositions pubS gatesUS
def pairsS : List (Cell × Cell) := permPairs posS
def pairsUS : List (Cell × Cell) := permPairs posUS
def witS : List (List Int) := stepWitness tS pubS rowsS
def totalRowsS : Nat := pubS + nRowsS

-- ── Structure ────────────────────────────────────────────────────────────────────────────────
#guard shapeSmoke.blocks == shapeSmoke.absorbs + shapeSmoke.chals
#guard placedS.length == totalRowsS
#guard placedUS.length == totalRowsS
#guard (placedS.map (fun g => g.wires.length)).all (· == 7)
#guard witS.length == 15
#guard (witS.map (·.length)).all (· == totalRowsS)

-- ⚑ THE PLACEMENT DID NOT REFUSE. `placeChecked` is the fail-closed door: `auxOverlapsPublic`
-- cannot fire (AUX = 67 ≥ pubWords), `referenceInGap` cannot (every circuit id is ≥ AUX), and
-- `inertPublicWord` is the LIVE gate — it fires unless the closing rows read all `pubWords` words.
#guard refusalOf pubS gatesS == none
#guard inertPublicWords pubS gatesS == []
-- …and it CAN refuse: declare a wider public input than the closing rows read and word `pubWords`
-- is reported inert rather than silently pinned (the `PRIMARY_LEN` 67-vs-40 shape, in miniature).
#guard match refusalOf (pubS + 3) gatesS with
       | some (.inertPublicWord i) => i == pubS | _ => false

-- ⚑ SEVEN GATE TYPES in one circuit — the census. Eleven `Poseidon` rows per sponge block, which
-- is upstream's own run length (`sponge_inputs.ml:47-64` / `plonk_constraint_system.ml:1450-1530`,
-- and MEASURED in Mina's `step-zkapp-proved` blob: every `Poseidon` run there is exactly 11).
-- FOUR sponges now: R1's transcript sponge and R7's three absorption segments — **plus the ONE
-- extra permutation §3c's `index_digest` is**, `Sponge.squeeze_field (Sponge.copy
-- sponge_after_index)`, which is why the `+ 1` is here and not hidden in a segment's block count.
#guard (placedS.filter (fun g => g.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks + 1)
-- ⚑ `2·chals + 5` `to_field_checked` chains, 8 `EndoMulScalar` rows each — and the composition of
-- that number IS the ledger of two retirements. Per transcript challenge TWO chains: the challenge
-- itself and `lowest_128_bits`' `assert_128_bits hi` (#1). Plus §8g's ξ (one, no split) and its r
-- (two: the challenge and its high part). Plus R8's own `lowest_128_bits` of the fr-sponge's FIRST
-- squeeze — TWO, because `Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true` and
-- `util.ml:98-99` then asserts BOTH parts. Upstream's own arithmetic, `squeeze_challenge` +
-- `squeeze_scalar`.
#guard (placedS.filter (fun g => g.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 5) * shapeSmoke.emsRows
-- …stated the other way, so a chain that vanished cannot hide inside the arithmetic: the range
-- chains are `chals + 3` of the total.
#guard ((List.range shapeSmoke.chals).flatMap
          (fun c => rangeRows shapeSmoke c (vHi shapeSmoke c) (hiOf shapeSmoke tS.sp c) true)).length
        == shapeSmoke.chals * (shapeSmoke.emsRows + 6)
#guard (rangeRows shapeSmoke (shapeSmoke.chals + 1) (vDHi shapeSmoke 1)
          (tS.defc.hi.getD 1 0) true).length == shapeSmoke.emsRows + 6
-- ⚑ …and R8's TWO, which is the third `lowest_128_bits` in the assembly. Stated as an EQUALITY on
-- the emitted sub-list: `finRows` is `aRows` + these two chains + three probes, so a deleted chain
-- moves this number rather than hiding behind another consumer of the same variable.
#guard (finRows shapeSmoke tS.ft tS.fin true).length
        == (aRows (baseFin shapeSmoke tS.ft) tS.fin.fp.prog).length
           + 2 * (shapeSmoke.emsRows + 6) + 3
#guard nRng shapeSmoke == shapeSmoke.chals + 4
#guard RNG_FIN_LO shapeSmoke == RNG_FIN_HI shapeSmoke + 1
-- ⚑ `VarBaseMul` is R3's `multiscale_known` AND §6b's `ft_comm` — the second MSM runs at
-- `FTC_CHUNKS = 51`, `step_verifier.ml:240-242`'s uniform 255 bits, not at `msmChunks`.
#guard (placedS.filter (fun g => g.kind == KGateType.varBaseMul)).length
        == shapeSmoke.msmTerms * shapeSmoke.msmChunks
           + ftcTerms shapeSmoke * FTC_CHUNKS
-- ⚑ `EndoMul` is `ipaRounds` fold ladders PLUS ONE — `check_bulletproof`'s `Scalar_challenge.endo q
-- c` (`:326`), the consumer that makes `delta` and the last squeeze mean something.
#guard (placedS.filter (fun g => g.kind == KGateType.endoMul)).length
        == (shapeSmoke.ipaRounds + 1) * shapeSmoke.ipaBlocks
-- …and `CompleteAdd` is the two summation chains, R3's OWN `add_fast base base` per term (§12f,
-- new 2026-08-02) and §6b's: per `scale_fast2` the initial `add_fast base base` and the odd-branch
-- `add_fast h (negate g)` (`plonk_curve_ops.ml:157,267`), then `common.ml`'s own `tCommN + 1` adds.
-- ⚑ The fold chain is `ipaRounds` adds and not `ipaRounds − 1` since the `~init` wiring (`:606`),
-- and the tail adds three: `endo`'s two seed `add_fast`s and the closing `cq + delta` (`:327`).
#guard (placedS.filter (fun g => g.kind == KGateType.completeAdd)).length
        == (shapeSmoke.msmTerms - 1) + shapeSmoke.msmTerms
           + shapeSmoke.ipaRounds + 2 * shapeSmoke.ipaRounds + 3
           + 2 * ftcTerms shapeSmoke + (tCommN shapeSmoke + 1)
-- ⚑ …and every `CompleteAdd` is still followed by a row of another kind, which is why the shape
-- diff's `CompleteAdd` family stays `1×n`: R3's seed row is preceded by a `Zero` probe (or the pin
-- block) and followed by its ladder's first `VarBaseMul`.
#guard ((List.range nRowsS).filter (fun i =>
          (rowsS.getD i default).kind == KGateType.completeAdd
          && (rowsS.getD (i + 1) default).kind == KGateType.completeAdd)) == []
-- Generic = the pubWords public rows `place` emits + the circuit's own generic rows.
#guard (placedS.filter (fun g => g.kind == KGateType.generic)).length ≥ pubS

-- The public rows ARE kimchi's `Pub` gates (`constraints.rs:420-423` errors `IncorrectPublic`
-- on anything else; `generic.rs:297-304` then reads the row as `w₀[r] − pᵣ = 0`).
#guard ((placedS.take pubS).map (fun g => (g.kind.ordinal, g.coeffs))).all
        (· == (1, ([1, 0, 0, 0, 0] : List Int)))

-- ── The copy-permutation, ON THE EMITTED OBJECT ───────────────────────────────────────────────
-- ⚑ σ IS A PERMUTATION of all `7 · totalRows` cells, WITH `pubSize > 0`.
#guard sortCells (allWires placedS) == sortCells (allCells totalRowsS)
#guard sortCells (allWires placedUS) == sortCells (allCells totalRowsS)

-- ⚑ THE COMPOSED GRID SATISFIES σ, against `place`'s ACTUAL permutation.
#guard pairsS.all (fun pr => gridAt witS pr.1 == gridAt witS pr.2)
#guard pairsUS.all (fun pr => gridAt witS pr.1 == gridAt witS pr.2)

-- ⚑ THE PUBLIC VECTOR IS witness column 0's prefix (`prover.rs:270`) — a fixture that got this
-- wrong would force the harness to re-derive the public input in Rust, i.e. author the witness.
#guard (witS.headD []).take pubS == stepPublic tS
#guard (stepPublic tS).length == pubS
#guard (exposedVars shapeSmoke).length == pubS
-- …and the exposed variables are DISTINCT, so 67 public words tie 67 different circuit values.
#guard ((exposedVars shapeSmoke).map varIx).dedup.length == pubS
-- ⚑ …AT THE COMMITTED SHAPE TOO. The smoke shape takes 12 of a 25-long list and so cannot see a
-- collision that only appears past word 12; this is the pin that does. (It found one: `vAcc bRounds`
-- and `vZ bRounds` were each exposed twice at `pubWords = 67`.)
#guard ((exposedVars shapeStep).map varIx).dedup.length == shapeStep.pubWords
#guard (exposedVars shapeStep).length == shapeStep.pubWords

-- ── The CROSS-SUB-CIRCUIT WIRES (the claim this file exists to make) ───────────────────────────
-- ⚑ ONE VARIABLE, THREE GATE TYPES. Challenge `c`'s value cell is in the `EndoMulScalar` chain
-- (col 1 of its last row), in the `Generic` decomposition row, and — for the terms/rounds that
-- consume it — in a `VarBaseMul` row (col 5) and an `EndoMul` tail `Zero` row (col 6). So the σ
-- class of `vN c emsRows` is genuinely cross-gate and cross-sub-circuit.
#guard (classCells posS (vN shapeSmoke 0 shapeSmoke.emsRows)).length ≥ 4
#guard (classCells posS (vN shapeSmoke 1 shapeSmoke.emsRows)).length ≥ 4
-- ⚑ THE SPONGE STATE CROSSES BLOCKS. Block b's output lane 0 is read by block b+1's absorb row
-- (or its permutation row 0) — a cross-row class no `KimchiRenderPoseidon` rung had.
#guard (classCells posS (vSt shapeSmoke 1 0)).length ≥ 2
#guard (classCells posS (vSt shapeSmoke 2 2)).length ≥ 2
-- ⚑ THE ENDO ROW-OVERLAP: a mid-chain endo accumulator is ONE cell (block e's `Next` col 4 IS
-- block e+1's `Curr` col 4), so σ self-wires it and two `EndoMul` gates read that one cell.
#guard (classCells posS (ipx shapeSmoke (qAcc shapeSmoke 0 3))).length == 1
-- Cross-ROW σ pairs — the cross-gate wiring count; removing the probes costs some of them.
#guard (pairsS.filter (fun pr => pr.1.row != pr.2.row)).length
        > (pairsUS.filter (fun pr => pr.1.row != pr.2.row)).length

-- ⚑ THE WIRED/UNWIRED DIFFERENCE IS EXACTLY THE PROBES: every probe cell is in a σ cycle in the
-- WIRED circuit and self-wired (in NO cycle) in the UNWIRED one.
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsS ⟨r, 0⟩ != (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsS ⟨r, 1⟩ != (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsUS ⟨r, 0⟩ == (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .finalize).all (fun r => permLookup pairsUS ⟨r, 1⟩ == (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .finalize).length ≥ 10

-- ⚑ IT CAN GO RED. Desync ONE mid-chain probe cell and the σ check FAILS, so the `= true` above
-- is a gate rather than a tautology. (`toGrid` is first-wins, so the prepended override lands.)
#guard
  (let probe := (rungProbeRows tS .finalize).getD ((rungProbeRows tS .finalize).length / 2) 0
   let ix := envIndex (stepEnv tS)
   let broken := Dregg2.Circuit.Emit.WitnessBuilder.toGrid 15 totalRowsS
     (((⟨probe, 0⟩ : Cell), (7 : Int))
      :: ((List.range pubS).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
      ++ ((rowsS.zip (List.range nRowsS)).flatMap (fun ri =>
           gateVarWitnessAt ix (pubS + ri.2)
             { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
           ++ ri.1.advice.map (fun cv => ((⟨pubS + ri.2, cv.1⟩ : Cell), cv.2)))))
   (pairsS.all (fun pr => gridAt broken pr.1 == gridAt broken pr.2)) == false)

-- ── The GATE constraints, evaluated ON THE ASSEMBLED GRID ─────────────────────────────────────
-- ⚑ NON-VACUITY IN LEAN, per gate type: every emitted row satisfies the SAME constraint bodies the
-- real proof uses (`KimchiVerify`, read-only), over `ZMod pN`, read out of the COMPOSED grid. A
-- placement bug that never reaches the grid cannot hide from these.
def rowKindAt (r : Nat) : KGateType := (rowsS.getD (r - pubS) default).kind

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.varBaseMul)).all
  (fun i => (varBaseMulConstraints (R := ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))
      ((gridRow witS (pubS + i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.completeAdd)).all
  (fun i => (completeAddConstraints (R := ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.endoMul)).all
  (fun i => (endoMulConstraints (R := ZMod pN) (KimchiRenderEndoMul.endo : ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))
      ((gridRow witS (pubS + i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

-- ── The SEMANTICS ─────────────────────────────────────────────────────────────────────────────
-- ⚑ THE SPONGE IS THE REAL SPONGE. Each block's output equals `PastaPoseidon.Ref.perm` of its
-- input — the same reference whose `Ref.hash` reproduces the o1js `Poseidon.hash` gold KATs.
#guard (List.range shapeSmoke.blocks).all (fun b =>
  let pre := tS.sp.states.getD b []
  let ms := tS.sp.msgs.getD b []
  let post := if (blockAbs shapeSmoke b).isSome then
      [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
    else pre
  tS.sp.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)

-- ⚑ THE CHALLENGE CHAIN RECONSTRUCTS ITS CHALLENGE: the `EndoMulScalar` folds' final `n₈` IS the
-- low-128-bit squeeze, and the decomposition row's identity `squeeze = n₈ + 2¹²⁸·hi` holds.
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((emsAccs shapeSmoke (chalOf shapeSmoke tS.sp c)).getLastD (0,2,2)).1
    == chalOf shapeSmoke tS.sp c)
#guard (List.range shapeSmoke.chals).all (fun c =>
  (tS.sp.states.getD (sqBlock shapeSmoke c + 1) []).getD 0 0
    == chalOf shapeSmoke tS.sp c + 2 ^ shapeSmoke.chalBits * hiOf shapeSmoke tS.sp c)
-- ⚑ …and every emitted `EndoMulScalar` ROW satisfies the gate's own eleven constraints on the
-- ASSEMBLED grid (`endomulScalarConstraints`, read-only), with the three polynomial constants.
#guard
  (let cA : ZMod pN := (KimchiRenderEndoMulScalar.cA : ZMod pN)
   let cB : ZMod pN := (KimchiRenderEndoMulScalar.cB : ZMod pN)
   let cC : ZMod pN := (KimchiRenderEndoMulScalar.cC : ZMod pN)
   ((List.range nRowsS).filter
      (fun i => (rowsS.getD i default).kind == KGateType.endoMulScalar)).all
    (fun i => (endomulScalarConstraints (R := ZMod pN) cA cB cC
        ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))))

-- ⚑ THE MSM SCALAR IS THE CHALLENGE. Term `i`'s var_base_mul counter chain closes on the value the
-- `EndoMulScalar` chain decoded — the σ wire, checked as an arithmetic identity too.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (tS.msm.terms.getD i default).ns.getLastD 0 == chalOf shapeSmoke tS.sp (shapeSmoke.msmChal i))
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (tS.ipa.ns.getD r []).getLastD 0 == chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal r))

-- ⚑ EVERY var_base_mul BIT STEP is `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, checked with `PastaCurve`'s
-- INDEPENDENT Jacobian double/add (a different formula family from the affine `stepVbm` that
-- produced the witness), compared without inversion by `jacEqM`.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let td := tS.msm.terms.getD i default
  let bits := tS.msm.bits.getD i []
  (List.range (5 * shapeSmoke.msmChunks)).all (fun k =>
    let a := td.accs.getD k (0, 0)
    let a' := td.accs.getD (k + 1) (0, 0)
    let q := if bits.getD k 0 == 1 then jOf td.T else jNeg (jOf td.T)
    jacEqM pN (jOf a') (jAdd (jDbl (jOf a)) q)))

-- ⚑ THE SCALAR CELL IS TIED TO THE POINT: with `acc₀ = [2]T` the chain closes to
-- `acc_final = [2^{5C} + 2n + 1]·T`, `n` the value in the last chunk's `n'` cell — checked against
-- `PastaCurve.scMulM`, an independent 255-bit double-and-add.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let td := tS.msm.terms.getD i default
  match scMulM pN (2 ^ (5 * shapeSmoke.msmChunks) + 2 * td.ns.getLastD 0 + 1) (jOf td.T) with
  | none => false
  | some R => jacEqM pN (jOf (td.accs.getLastD (0, 0))) R)

-- ⚑ EVERY endo_mul BLOCK is `accₑ₊₁ = [2]([2]accₑ + Q₁) + Q₂` with `Qₖ = ±φ^{b}(T)` — the
-- endomorphism selection included — same independent Jacobian oracle.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  let T := tS.ipa.bases.getD r (0, 0)
  (List.range shapeSmoke.ipaBlocks).all (fun e =>
    let b := (tS.ipa.blks.getD r []).getD e default
    let a := (tS.ipa.accs.getD r []).getD e (0, 0)
    let a' := (tS.ipa.accs.getD r []).getD (e + 1) (0, 0)
    let q1r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b1 T.1, T.2)
    let q2r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b3 T.1, T.2)
    let q1 := if b.b2 == 1 then jOf q1r else jNeg (jOf q1r)
    let q2 := if b.b4 == 1 then jOf q2r else jNeg (jOf q2r)
    jacEqM pN (jOf a') (jAdd (jDbl (jAdd (jDbl (jOf a)) q1)) q2)))

-- ⚑ THE ACCUMULATOR CHAINS REALLY SUM THE TERMS (Jacobian fold of all addends).
#guard
  (let pts := (List.range shapeSmoke.msmTerms).map (fun i =>
        (tS.msm.terms.getD i default).accs.getLastD (0, 0))
   let tot := (pts.drop 1).foldl (fun acc p => jAdd acc (jOf p)) (jOf (pts.getD 0 (0, 0)))
   jacEqM pN (jOf (tS.msm.sums.getLastD (0, 0))) tot)
-- ⚑ …and R4's fold starts at `sg_old[0]` (`~init`, `step_verifier.ml:606`), so the Jacobian oracle
-- is seeded there and not at round 0's output. `ipaRounds` adds, one per round.
#guard
  (let pts := (List.range shapeSmoke.ipaRounds).map (fun r =>
        (tS.ipa.accs.getD r []).getLastD (0, 0))
   let tot := pts.foldl (fun acc p => jAdd acc (jOf p))
                (jOf Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY)
   jacEqM pN (jOf (tS.ipa.sums.getLastD (0, 0))) tot)
#guard tS.ipa.sums.length == shapeSmoke.ipaRounds
#guard tS.ipa.addCells.length == shapeSmoke.ipaRounds
-- ⚑ …and `check_bulletproof`'s tail really computes `endo q c + delta`: the ladder's own counter
-- closes on `c`'s challenge variable, its accumulator is `Scalar_challenge.endo`'s seed run, and the
-- closing `add_fast` is `cq + delta` over the block's own opening point.
#guard tS.ipa.lhsAccs.getD 0 (0, 0) == endoSeed (tS.ipa.sums.getLastD (0, 0))
#guard tS.ipa.lhsNs.getLastD 0 == chalOf shapeSmoke tS.sp shapeSmoke.cChal
#guard tS.ipa.lhsAccs.length == shapeSmoke.ipaBlocks + 1
#guard (List.range shapeSmoke.ipaBlocks).all (fun e =>
  let T := tS.ipa.sums.getLastD (0, 0)
  let b := tS.ipa.lhsBlks.getD e default
  let a := tS.ipa.lhsAccs.getD e (0, 0)
  let a' := tS.ipa.lhsAccs.getD (e + 1) (0, 0)
  let q1r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b1 T.1, T.2)
  let q2r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b3 T.1, T.2)
  let q1 := if b.b2 == 1 then jOf q1r else jNeg (jOf q1r)
  let q2 := if b.b4 == 1 then jOf q2r else jNeg (jOf q2r)
  jacEqM pN (jOf a') (jAdd (jDbl (jAdd (jDbl (jOf a)) q1)) q2))
#guard jacEqM pN (jOf (tS.ipa.lhsAdd.getD 4 0, tS.ipa.lhsAdd.getD 5 0))
         (jAdd (jOf (tS.ipa.lhsAccs.getLastD (0, 0)))
               (jOf Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY))
#guard onCurveA (tS.ipa.lhsAdd.getD 4 0, tS.ipa.lhsAdd.getD 5 0)

-- Every add is the distinct-x `add_fast` case (`inf = 0`, `same_x = 0`), so leaving col 6 unwired
-- at 0 is correct and no add silently lands on the point at infinity.
#guard tS.msm.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
#guard tS.ipa.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
-- Every point in every chain is on the Pallas curve.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  ((tS.msm.terms.getD i default).accs).all onCurveA)
#guard tS.msm.sums.all onCurveA
#guard tS.ipa.sums.all onCurveA
#guard (List.range shapeSmoke.ipaRounds).all (fun r => (tS.ipa.accs.getD r []).all onCurveA)
-- The chains are non-degenerate: both bit values occur, so both slope signs / both endo branches
-- are exercised in every chain.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (tS.msm.bits.getD i []).contains 0 && (tS.msm.bits.getD i []).contains 1)

-- ⚑ THE DEFERRED `b(ζ)` IS THE CHALLENGE POLYNOMIAL: the assembled product equals the direct fold
-- `∏ (1 + u_k · ζ^{2^{bRounds−1−k}})`, and `ζ` IS challenge 0.
#guard tS.df.zs.getD 0 0 == liftOf shapeSmoke tS.sp shapeSmoke.zetaChal
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  tS.df.zs.getD (k + 1) 0 == fMul (tS.df.zs.getD k 0) (tS.df.zs.getD k 0))
#guard tS.df.accs.getLastD 0
        == (List.range shapeSmoke.bRounds).foldl
             (fun acc k => fMul acc
               (fAdd 1 (fMul (liftOf shapeSmoke tS.sp (shapeSmoke.uChal k))
                             (tS.df.zs.getD (shapeSmoke.bRounds - 1 - k) 0)))) 1
-- …and it is NOT the trivial product (a degenerate `b` would make the rung vacuous).
#guard tS.df.accs.getLastD 0 != 1

-- ── §12a — ⚑ THE FOLD IS FED BY THE FR-SPONGE (simplification #10, retired) ────────────────────
-- The multipliers the C8 fold uses are §8g's DEFERRED challenges. Named once, so every pin below
-- reads the same two values the `Generic` halves of `cipRows` multiply by.
def sq1S : Nat := frSqueezeVal tS.segB tS.specB
def sq2S : Nat := frSqueeze2Val tS.segB tS.specB
def xiFoldS : Nat := tS.defc.lift shapeSmoke 0
def rFoldS : Nat := tS.defc.lift shapeSmoke 1
/-- The multiplier a given fr-sponge squeeze would produce: `lowest_128_bits`, then
`to_field_checked` — the whole §8g chain, as a value. -/
def foldMulOf (sq : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
    (Dregg2.Circuit.Emit.KimchiVerify.low128 sq)

-- ⚑ **ξ IS `endoMap` OF R7's FIRST SQUEEZE, r IS `endoMap` OF ITS SECOND.** `xi_correct` binds the
-- statement's ξ word to the first squeeze (§16d) and §8g's chain 0 lifts THAT word, so the composite
-- the fold multiplies by is exactly this. Upstream's own two-step, `step_verifier.ml:1010-1013`.
#guard ((xiFoldS : Nat) : ZMod pN) == foldMulOf sq1S
#guard ((rFoldS : Nat) : ZMod pN) == foldMulOf sq2S
-- …the two squeezes are different field elements, so ξ ≠ r is a fact about the sponge and not luck.
#guard sq1S != sq2S && xiFoldS != rFoldS
-- …and the lift is not the identity (a degenerate endo would make the chain decoration).
#guard xiFoldS != tS.defc.pre.getD 0 0 && rFoldS != tS.defc.pre.getD 1 0

-- ⚑ THE ASSEMBLED `combined_inner_product` IS THE VERIFIER'S. The Horner chain the `Generic` rows
-- compute equals `KimchiVerify.cipR` applied to the SAME ξ, r and evaluation columns — and `cipR`
-- IS the shipped `combinedInnerProduct` (`KimchiVerify.cipR_eq`, `rfl`, for every field; the
-- CommRing mirror exists precisely so a `ZMod pN` instance can answer to it). So the deferred rung
-- answers to the READ-ONLY transcription of `verifier.rs`, not to its own definition.
#guard
  ((tS.df.ca.getLastD 0 : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
         (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN))))
-- …and it CAN go red: swapping ξ for r gives a different value (so the equality is discriminating,
-- not two names for zero).
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq2S) (foldMulOf sq2S)
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)

-- ⚑⚑ **THE BITING RED CONTROL FOR #10: BENDING R7's SQUEEZE MOVES THE FOLD.** Before §8g the fold's
-- multipliers were R1 transcript challenges and this could not bite — the fr-sponge reached
-- `xi_correct` and nothing else, so a bent squeeze left `combined_inner_product` exactly where it
-- was. Now each squeeze is the SOURCE of a `to_field_checked` chain, and a one-unit bend in either
-- one moves the folded value.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf (sq1S + 1)) (foldMulOf sq2S)
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf (sq2S + 1))
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
-- ⚑ …and the RETIRED reading — the last two R1 transcript challenges, which is what the fold
-- multiplied by until 2026-08-02 — is a DIFFERENT value. Derived, not fixed.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR
          ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 1) : ZMod pN))
          ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2) : ZMod pN))
          (tS.df.ez.map (fun n => (n : ZMod pN)))
          (tS.df.ew.map (fun n => (n : ZMod pN)))) == false)
#guard xiFoldS != liftOf shapeSmoke tS.sp (shapeSmoke.chals - 1)
#guard rFoldS != liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2)

-- ⚑ …and it is a WIRE, not just an arithmetic identity: the variable `cipRows` Horners over is in a
-- σ class that also holds §8g chain 0's lift row, and the statement ξ word's class reaches THREE
-- rows (the chain's `Field.Assert.equal`, the closing public tie, and R8's `xi_correct` gadget).
-- Exact counts, not floors: ξ's class is the `cipEvals` Horner reads + its own lift row + its probe;
-- r's is the `cipEvals` `r·evₖ(ζω)` reads + lift + probe + R8's `b_correct` read. A chain that
-- vanished, or a fold that stopped reading it, moves these.
#guard (classCells posS (vDLift shapeSmoke 0)).length == shapeSmoke.cipEvals + 2
#guard (classCells posS (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 3
-- …and the statement ξ word is read by EXACTLY three rows: §8g chain 0's `Field.Assert.equal`, the
-- closing public tie, and R8's `xi_correct` gadget. Drop any one and this is 2.
#guard (classCells posS (vXiStmt shapeSmoke)).length == 3
-- …the r chain's source really is segment B's SECOND squeeze cell (a state lane the sponge rows own).
#guard (classCells posS (frSqueeze2Var shapeSmoke)).length ≥ 2
#guard frSqueeze2Var shapeSmoke != frSqueezeVar shapeSmoke

-- ── §12b — ⚑ THE BASES ARE A REAL PROOF'S COMMITMENTS (simplification #3, retired) ─────────────
-- Until 2026-08-02 every curve base was a free witness variable holding a `basePts` fixture
-- (`[3]G, [4]G, …`), and R1 absorbed `2·absorbs` unrelated `msgVal` words. Two things were wrong at
-- once and this block is the pair of them: the bases are now **Mina devnet block 539508's own Wrap
-- commitments**, and each one is either PINNED (`Inner_curve.constant`) or ABSORBED (its two
-- variables ARE the transcript's absorbed words).

-- ⚑ THE VALUES ARE THE REAL BLOCK'S, at the committed shape, in the order the assembly consumes
-- them: 40 SRS Lagrange commitments, `combine_split_commitments`' 46, `bullet_reduce`'s 30.
#guard stepBases shapeStep == Dregg2.Bridge.MinaStepPrevCommitments.ALL_XY
#guard (stepBases shapeStep).length == shapeStep.msmTerms + shapeStep.ipaRounds
#guard shapeStep.msmTerms == Dregg2.Bridge.MinaStepPrevCommitments.LAGRANGE_XY.length
#guard shapeStep.ipaRounds == REAL_IPA_XY.length
-- …and the smoke shape's are a genuine PREFIX of the same list, not a second fixture family.
#guard stepBases shapeSmoke
        == (Dregg2.Bridge.MinaStepPrevCommitments.LAGRANGE_XY.take shapeSmoke.msmTerms
            ++ REAL_IPA_XY.take shapeSmoke.ipaRounds)

-- ⚑ THE PROVENANCE CENSUS IS EXERCISED — every round upstream absorbs really does get a transcript
-- block, at BOTH shapes. ⚑ Stated as a MULTISET equality against the `ipaAbsorbs` filter and as a
-- LIST **in**equality against it, because since the R1 interleaving `absRoundList` is upstream's
-- absorption ORDER (`w_comm` before `z_comm`, `t_comm` before the gammas) and the filter's ascending
-- order is NOT: a sponge is order-sensitive, so "same set" is the wrong pin on its own.
#guard (absRoundList shapeStep).mergeSort (· ≤ ·)
        == (List.range shapeStep.ipaRounds).filter ipaAbsorbs
#guard (absRoundList shapeSmoke).mergeSort (· ≤ ·)
        == (List.range shapeSmoke.ipaRounds).filter ipaAbsorbs
#guard absRoundList shapeStep != (List.range shapeStep.ipaRounds).filter ipaAbsorbs
-- …and the order really is `sg_old[1] · x_hat · w_comm ×15 · z_comm · gammas ×30`.
#guard (absRoundList shapeStep).take 3 == [0, 1, 10]
#guard (absRoundList shapeStep).getD 16 0 == 24 && (absRoundList shapeStep).getD 17 0 == 3
#guard (absRoundList shapeStep).drop 18 == List.range' (N_WDB - 1) 30
-- …and BOTH provenances really occur at the committed shape: 18 fold commitments + 30
-- `bullet_reduce` gammas absorbed, 28 verifier-key / computed constants.
#guard (absRoundList shapeStep).length == 48
#guard ((List.range shapeStep.ipaRounds).filter
          (fun r => ipaSrc shapeStep r == BaseSrc.const)).length == 27
-- ⚑ …and EXACTLY ONE round is COMPUTED — `ft_comm`, which was the 28th constant until §6b.
#guard ((List.range shapeStep.ipaRounds).filter
          (fun r => ipaSrc shapeStep r == BaseSrc.computed)) == [FTC_ROUND]
#guard (absRoundList shapeSmoke).length == 3
-- …and R3 carries NO absorbed base, which is `multiscale_known`'s own shape.
#guard (List.range shapeStep.msmTerms).all (fun i => msmSrc i == BaseSrc.const)
-- ⚠ ⚑ …and the COUNT OF STILL-FREE TRANSCRIPT WORDS, pinned so it cannot drift silently. A free word
-- is a `msgVal` fixture no row pins. Of `2·absorbs = 118` absorbed words **ONE** is free — the pad
-- lane an odd item count forces — where 7 were before the R1 interleaving, 31 at `absorbs = 71` and
-- 45 before §6b. EQUALITY, so un-assembling any consumer moves this number.
#guard shapeStep.absorbs - (absRoundList shapeStep).length == 11
#guard (List.range shapeStep.absorbs).countP (fun b => blockRound shapeStep b == none) == 11
#guard (List.range shapeStep.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun j =>
           msgVar shapeStep b j == vMsg shapeStep b j)) 0 == 1
-- ⚑ …and the SIX that left the free list are exactly the three closures, block for block and lane
-- for lane, each against the variable its CONSUMER reads.
#guard msgVar shapeStep oSgOld0 0 == ipx shapeStep (qInit shapeStep)
        && msgVar shapeStep oSgOld0 1 == ipy shapeStep (qInit shapeStep)
#guard msgVar shapeStep (oCip shapeStep) 0 == vCipShift shapeStep
        && msgVar shapeStep (oCip shapeStep) 1 == vCipBit shapeStep
#guard msgVar shapeStep (oDelta shapeStep) 0 == ipx shapeStep (qDel shapeStep)
        && msgVar shapeStep (oDelta shapeStep) 1 == ipy shapeStep (qDel shapeStep)
-- ⚑ …and `t_comm`'s FOURTEEN, block for block and lane for lane, at their SCHEDULE position (after
-- `z_comm`/α and before ζ, `step_verifier.ml:567`) rather than after the gammas.
#guard (List.range shapeStep.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun _ => tCommBlock shapeStep b != none)) 0 == 14
#guard (List.range (tCommN shapeStep)).all (fun i =>
  let b := oTc shapeStep + i
  tCommBlock shapeStep b == some i
  && msgVar shapeStep b 0 == vTcX shapeStep i && msgVar shapeStep b 1 == vTcY shapeStep i
  && msgValOf shapeStep (stepBases shapeStep) (0, 0) b 0 == (ftcTc i).1
  && msgValOf shapeStep (stepBases shapeStep) (0, 0) b 1 == (ftcTc i).2)
-- …and exactly ONE absorbed word of R1's transcript is `index_digest`, at BLOCK 0 — upstream's own
-- position (`absorb sponge Field index_digest` precedes `Vector.iter ~f:(absorb sponge PC) sg_old`,
-- `step_verifier.ml:534,538`).
#guard (List.range shapeStep.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun j =>
           msgVar shapeStep b j == vIdxD shapeStep 0)) 0 == 1
#guard msgVar shapeStep 0 0 == vIdxD shapeStep 0
#guard msgValOf shapeStep (stepBases shapeStep) (0, 0) 0 0 == indexDigest
-- ── ⚑ THE ABSORB SHAPE IS `verify_one`'s OWN ITEM COUNT, AND SO IS ITS ORDER ───────────────────
-- `absorbs` is `⌈117/2⌉` AND is now DERIVED from the schedule, so the shape, the item census and the
-- absorption ORDER agree by construction rather than by three numbers someone chose. Every pin is an
-- EQUALITY: widening `absorbs` back out, or reordering a run, reds several at once.
#guard N_ABSORB_ITEMS == 117
#guard (ABSORB_ITEMS.map (·.2)) == [1, 4, 2, 30, 2, 14, 2, 60, 2]
#guard absorbBlocksNeeded == 59
#guard shapeStep.absorbs == absorbBlocksNeeded
#guard shapeStep.absorbs == absorbBlocksOf shapeStep
#guard shapeSmoke.absorbs == absorbBlocksOf shapeSmoke
#guard 2 * shapeStep.absorbs == 118
-- ⚑ …and the residue is ONE pad lane. 117 is odd, `index_digest` is the single unpaired `Field`,
-- every later item is a point or a `(field, bit)` pair, and this file models ONE per rate-2 block.
-- **That is STRUCTURAL — there is no absorption behind it to close.**
#guard 2 * shapeStep.absorbs - N_ABSORB_ITEMS == 1
-- ⚑⚑ **THE ITEM CENSUS AND THE WIRING CENSUS AGREE, AS AN EQUALITY, AND `UNWIRED_ITEMS` IS EMPTY.**
-- Every item `verify_one` absorbs is a word some row here reads: `index_digest` + `sg_old[0]` + the
-- 48 fold commitments + `t_comm`'s 7 chunks + `cip` (field+bit) + `delta` = 117.
#guard N_UNWIRED_ITEMS == 0 && UNWIRED_ITEMS == []
#guard N_ABSORB_ITEMS
        == 1 + 2 + 2 * (absRoundList shapeStep).length + 2 * tCommN shapeStep + 2 + 2
#guard 2 * shapeStep.absorbs - N_ABSORB_ITEMS == N_UNWIRED_ITEMS + 1
-- …and the `t_comm` cap does not bind: `tCommN` is 7 because `N_TCOMM` is 7.
#guard tCommN shapeStep == N_TCOMM && shapeStep.tComms == N_TCOMM

-- ── ⚑⚑ §12i — **THE SCHEDULE, AND WHY `combined_inner_product` IS NOT A CYCLE** ────────────────
-- `absorb sponge Scalar advice.combined_inner_product` is at `step_verifier.ml:256`, INSIDE
-- `check_bulletproof`, which runs on the sponge forked at `:573` — after `let zeta = sample_scalar
-- ()` at `:568`. So β, γ, α and ζ are fixed before it. The previous rung's diagnosis stopped at "R1
-- runs all absorb blocks before all squeezes"; that was true and not the whole blocker (segment A
-- absorbing R1's own challenges was the other half, see `vPrevChal`). These pin BOTH halves.
#guard sqBlock shapeStep shapeStep.betaChal == absBlock shapeStep (oZ shapeStep - 1) + 1
#guard sqBlock shapeStep shapeStep.gammaChal == sqBlock shapeStep shapeStep.betaChal + 1
#guard sqBlock shapeStep shapeStep.alphaChal == absBlock shapeStep (oTc shapeStep - 1) + 1
#guard sqBlock shapeStep shapeStep.zetaChal == absBlock shapeStep (oCip shapeStep - 1) + 1
-- ⚑ the four are squeezed STRICTLY BEFORE `cip`'s block, and every later squeeze strictly after.
#guard (List.range 4).all (fun c => sqBlock shapeStep c < absBlock shapeStep (oCip shapeStep))
#guard ((List.range shapeStep.chals).drop 4).all
        (fun c => absBlock shapeStep (oCip shapeStep) < sqBlock shapeStep c)
-- ⚑ `c` is the squeeze that FOLLOWS `delta` (`:321-322`), and it is the last scheduled one.
#guard sqBlock shapeStep shapeStep.cChal == absBlock shapeStep (oDelta shapeStep) + 1
#guard shapeStep.cChal == sqScheduled shapeStep - 1 && sqScheduled shapeStep == 21
-- ⚑ …and the schedule really is `absorbs + chals` blocks with the absorb ordinals in order.
#guard (tSched shapeStep).length == shapeStep.blocks
#guard (tSched shapeStep).filterMap id == List.range shapeStep.absorbs
#guard (tSched shapeSmoke).filterMap id == List.range shapeSmoke.absorbs
#guard (sqBlocks shapeStep).length == shapeStep.chals
-- ⚑⚑ **AND THE NON-CIRCULARITY, MEASURED.** Re-run R1 with the `cip` word set to ZERO: β, γ, α, ζ
-- are IDENTICAL (so `ft_eval0`, the fr-sponge, ξ, r and the Horner chain that produces `cip` are
-- all unchanged, which is what makes the two-pass assembly exact) — and every squeeze after it
-- MOVES, so the absorption is live rather than inert.
def spNoCip : SpongeData := runSponge shapeSmoke (stepBases shapeSmoke) (0, 0)
#guard (List.range 4).all (fun c => chalOf shapeSmoke spNoCip c == chalOf shapeSmoke tS.sp c)
-- ⚑ …so R6's `ft_eval0` — which reads ζ, α, β, γ and NOTHING else off the transcript — is the same
-- value in both passes. That is the fact the two-pass `mkStepWith` rests on, stated on the value
-- rather than on the four inputs, so a future R6 that reached a later squeeze would red HERE.
#guard (runFt shapeSmoke spNoCip).out == tS.ft.out
#guard ((List.range shapeSmoke.chals).drop 4).all (fun c =>
  chalOf shapeSmoke spNoCip c != chalOf shapeSmoke tS.sp c)
-- ⚑ …and the word the transcript actually swallowed IS the statement word R8 binds — which is what
-- makes it a CONSUMED absorption and not one more thing the sponge eats.
#guard (tS.sp.msgs.getD (absBlock shapeSmoke (oCip shapeSmoke)) []).getD 0 0 == tS.fin.cipShift
#guard (tS.sp.msgs.getD (absBlock shapeSmoke (oCip shapeSmoke)) []).getD 1 0 == CIP_BIT
#guard tS.fin.cipShift == shiftT1 (tS.df.ca.getLastD 0)

-- ── ⚑⚑ §12j — **THE THREE CLOSURES, EACH WITH THE WITNESS ITS HOLE ADMITTED** ──────────────────
-- A wire without an exhibited alternative is unverified. For each of the three: the word was a
-- `msgVal` FIXTURE the sponge ate and no row read, so a prover could absorb one value and act on
-- another — and nothing in the assembly could tell. Each block below constructs the witness that
-- bought, shows the emitted gate polynomials ACCEPTING it in the shape that had no consumer, and
-- shows the new row REFUSING it.

/-- The absolute row of a `CompleteAdd` whose LEFT operand is `v` — the emitted row itself, found in
the schedule rather than counted by hand. -/
def caRowIxOf (v : PVar) : Nat :=
  (((rowsS.zip (List.range nRowsS)).find? (fun ri =>
      ri.1.kind == KGateType.completeAdd && ri.1.perm.getD 0 none == some v)).map (·.2)).getD 0
/-- …its 15 cells off the composed grid, with cols `i`/`i+1` overridden. -/
def caCellsAt (ix : Nat) (i : Nat) (p : Nat × Nat) : List Nat :=
  let r := gridRow witS (pubS + ix)
  (List.range r.length).map (fun j =>
    if j == i then p.1 else if j == i + 1 then p.2 else r.getD j 0)
def caHolds (cells : List Nat) : Bool :=
  (completeAddConstraints (R := ZMod pN) (cells.map (fun n => (n : ZMod pN)))).all
    (fun z => decide (z = 0))

-- ── (a) `sg_old[0]` — `combine_split_commitments`' `~init` (`step_verifier.ml:606`) ─────────────
/-- ⚑ THE WITNESS: another of the block's OWN on-curve commitments. `assert_on_curve` cannot refuse
it and neither can any curve gate — which is precisely why a fold that never READ the accumulator's
starting point could be handed any of them. -/
def sgAlt : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0)
#guard onCurveA sgAlt && sgAlt != Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
-- the fold's FIRST add really reads `qInit`, and `qInit` really is block `oSgOld0`'s absorbed word.
#guard caRowIxOf (ipx shapeSmoke (qInit shapeSmoke)) > 0
#guard msgVar shapeSmoke oSgOld0 0 == ipx shapeSmoke (qInit shapeSmoke)
-- ⚑⚑ ACCEPTED BEFORE — with no row reading it, `sg_old[0]` sat in exactly ONE cell (the absorb row)
-- and the fold was self-consistent whatever it held. Now its class spans the sponge, the add and
-- `assert_on_curve`, which is the difference between absorbing a commitment and consuming one.
#guard (classCells posS (ipx shapeSmoke (qInit shapeSmoke))).length ≥ 4
-- ⚑⚑ REFUSED AFTER: `completeAddConstraints` — proof-systems' own, read-only — is 0 on the honest
-- row and NONZERO with the substitute in the accumulator's slot.
#guard caHolds (gridRow witS (pubS + caRowIxOf (ipx shapeSmoke (qInit shapeSmoke))))
#guard caHolds (caCellsAt (caRowIxOf (ipx shapeSmoke (qInit shapeSmoke))) 0 sgAlt) == false

-- ── (b) `combined_inner_product` — `absorb sponge Scalar advice.cip` (`:256`) ───────────────────
/-- ⚑ THE WITNESS: the prover absorbs the honest `cip` and CLAIMS a different one — or claims the
honest one and absorbs a different one. Before, the two were unrelated objects: `vCipShift` was a
statement word R8 compared, `oCip`'s lane was a `msgVal` fixture, and NO cell joined them. -/
def cipForged : Nat := fAdd tS.fin.cipShift 1
def spCip : SpongeData :=
  runSpongeAt shapeSmoke (stepBases shapeSmoke) indexDigest (cipForged, CIP_BIT)
    (oCip shapeSmoke) 0 cipForged
-- ⚑⚑ ACCEPTED BEFORE: with the word a fixture, R1's blocks were all still exactly `Ref.perm` of
-- their own absorbed state — a `Poseidon` gate constrains the permutation, never its input.
#guard (List.range shapeSmoke.blocks).all (fun b =>
  let pre := spCip.states.getD b []
  let ms := spCip.msgs.getD b []
  let post := if ms.isEmpty then pre
    else [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
  spCip.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- ⚑⚑ REFUSED AFTER, twice over. (i) the absorbed word IS `vCipShift`, so a claimed `cip` that is not
-- the Horner chain's output fails R8's `Shifted_value.Type1` unshift comparison…
#guard fAdd (fAdd cipForged cipForged) SHIFT_C != tS.df.ca.getLastD 0
#guard fAdd (fAdd tS.fin.cipShift tS.fin.cipShift) SHIFT_C == tS.df.ca.getLastD 0
-- …and (ii) absorbing a different word MOVES every squeeze from `u` onward, so the bulletproof
-- challenges, `check_bulletproof`'s `c` and the whole tail move with it — while β/γ/α/ζ, which are
-- squeezed BEFORE `:256`, do not. That split is upstream's own and it is why this is not a cycle.
#guard (List.range 4).all (fun c => chalOf shapeSmoke spCip c == chalOf shapeSmoke tS.sp c)
#guard ((List.range shapeSmoke.chals).drop 4).all (fun c =>
  chalOf shapeSmoke spCip c != chalOf shapeSmoke tS.sp c)
-- …and the BIT is Boolean-constrained, so the second lane is not a second free field element.
#guard fMul CIP_BIT CIP_BIT == CIP_BIT
#guard (fMul 2 2 == 2) == false

-- ── (c) `delta` — `absorb sponge PC delta` (`:321`), `lhs = endo q c + delta` (`:326-327`) ──────
/-- ⚑ THE WITNESS: another real on-curve point in `delta`'s slot. Membership cannot refuse it; only
a row that READS it can. -/
def delAlt : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 28 (0, 0)
#guard onCurveA delAlt && delAlt != Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
#guard msgVar shapeSmoke (oDelta shapeSmoke) 0 == ipx shapeSmoke (qDel shapeSmoke)
-- ⚑⚑ ACCEPTED BEFORE: one cell, the absorb row. REFUSED AFTER: the closing `add_fast` reads it, so
-- its class spans the sponge, that row and `assert_on_curve`…
#guard (classCells posS (ipx shapeSmoke (qDel shapeSmoke))).length ≥ 4
-- …and the emitted `CompleteAdd` body is 0 on `cq + delta` and NONZERO on `cq + delta'`.
#guard caHolds (gridRow witS (pubS + caRowIxOf (ipx shapeSmoke (qLhsAcc shapeSmoke
                  shapeSmoke.ipaBlocks))))
#guard caHolds (caCellsAt (caRowIxOf (ipx shapeSmoke (qLhsAcc shapeSmoke shapeSmoke.ipaBlocks)))
                  2 delAlt) == false
-- ⚑ …and the ladder that produces `cq` multiplies by the LAST transcript squeeze, `c` (`:322`), not
-- by a challenge chosen for it: its counter chain closes on `c`'s own `to_field_checked` cell.
#guard vLhsN shapeSmoke shapeSmoke.ipaBlocks
        == vN shapeSmoke shapeSmoke.cChal shapeSmoke.emsRows
#guard tS.ipa.lhsNs.getLastD 0 == chalOf shapeSmoke tS.sp shapeSmoke.cChal
-- …and the SEGMENT-C count, which is the other half and the bigger one: the `Not_opt` prefix was
-- 58 `hmVal` fixtures and is now `sponge_after_index`'s 56 derived words plus the two app-state
-- words. **58 free → 2.**
#guard (List.range N_HM_FIX).countP (fun i =>
  (List.range N_HM_APP).any (fun a =>
    (tS.specC.ws.getD i (xv 0, 0)).1 == vHm shapeSmoke a)) == N_HM_APP
#guard (List.range N_HM_APP).all (fun a =>
  (tS.specC.ws.getD (N_IDX_WORDS + a) (xv 0, 0)).1 == vHm shapeSmoke a)
-- …and the other 56 are the plonk index, word for word, in `index_to_field_elements` order.
#guard (List.range N_IDX_WORDS).all (fun i =>
  (tS.specC.ws.getD i (xv 0, 0)) == (idxVar shapeSmoke (i / 2) (i % 2), idxVal (i / 2) (i % 2)))
#guard N_HM_APP == 2 && N_IDX_WORDS == 56 && N_HM_FIX == 58
-- …and at the SMOKE shape too the ONLY free word is block `oDigest`'s second lane, the pad.
#guard (List.range shapeSmoke.absorbs).countP (fun b => blockRound shapeSmoke b == none)
        == 4 + tCommN shapeSmoke
#guard (List.range shapeSmoke.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun j =>
           msgVar shapeSmoke b j == vMsg shapeSmoke b j)) 0 == 1
-- …so the pin rows are exactly the constants, one `Generic` row per point.
#guard (msmBaseRows shapeSmoke tS.msm).length == shapeSmoke.msmTerms
#guard (ipaBaseRows shapeSmoke tS.ipa).length
        == ((List.range shapeSmoke.ipaRounds).filter
              (fun r => ipaSrc shapeSmoke r == BaseSrc.const)).length

/-- The first absorbed fold round, and the first constant one. -/
def absR0 : Nat := (absRoundList shapeSmoke).headD 0
def constR0 : Nat :=
  ((List.range shapeSmoke.ipaRounds).filter
     (fun r => ipaSrc shapeSmoke r == BaseSrc.const)).headD 0
def nTrans : Nat := pubS + (transcriptRows shapeSmoke tS.sp true).length

-- ⚑ ONE σ CLASS SPANS THE SPONGE AND THE FOLD. An absorbed base's coordinate variable is read by
-- `ipaBlocks` `EndoMul` rows AND by the transcript's own absorb row — stated as an EQUALITY on the
-- class, and on how many of its cells lie in R1's row range, so a deleted wire cannot satisfy it.
-- (`ipaBlocks` `EndoMul` reads + the absorb row + since §7b the three `assert_on_curve` halves,
-- which read `x` three times and `y` twice.)
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke absR0))).length == shapeSmoke.ipaBlocks + 6
#guard (classCells posS (ipy shapeSmoke (qT shapeSmoke absR0))).length == shapeSmoke.ipaBlocks + 5
#guard ((classCells posS (ipx shapeSmoke (qT shapeSmoke absR0))).filter
          (fun c => c.row < nTrans)).length == 1
#guard ((classCells posS (ipy shapeSmoke (qT shapeSmoke absR0))).filter
          (fun c => c.row < nTrans)).length == 1
-- …and a CONSTANT base has NO cell in the transcript: it is pinned, not absorbed. Its class is
-- `ipaBlocks` `EndoMul` reads + the `Inner_curve.constant` pin + segment C's `sponge_after_index`
-- absorb, because the smoke shape's one constant fold round IS plonk-index commitment 22 (§3c).
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke constR0))).length == shapeSmoke.ipaBlocks + 4
#guard ((classCells posS (ipx shapeSmoke (qT shapeSmoke constR0))).filter
          (fun c => c.row < nTrans)).length == 0
#guard idxSrc shapeSmoke 22 == some constR0
-- …and R3's bases likewise: pinned, never absorbed. ⚑ `+ 3` and not `+ 1` since §12f: the seed row
-- `add_fast base base` reads the base TWICE (cols 0,1 and 2,3) on top of the pin row and the
-- `msmChunks` `VarBaseMul` reads.
#guard ((classCells posS (mpx shapeSmoke (pT shapeSmoke 0))).filter
          (fun c => c.row < nTrans)).length == 0
#guard (classCells posS (mpx shapeSmoke (pT shapeSmoke 0))).length == shapeSmoke.msmChunks + 3

/-- The supplied commitments with base `k` replaced by ANOTHER of the real block's points — a prover
who hands `verify_one` a different, perfectly valid, on-curve commitment. -/
def basesSwapped (s : StepShape) (k : Nat) : List (Nat × Nat) :=
  let bs := stepBases s
  (List.range bs.length).map (fun i =>
    if i == k then Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0)
    else bs.getD i (0, 0))

def tSwapAbs : StepData :=
  mkStepWith shapeSmoke (basesSwapped shapeSmoke (shapeSmoke.msmTerms + absR0))
def tSwapConst : StepData :=
  mkStepWith shapeSmoke (basesSwapped shapeSmoke (shapeSmoke.msmTerms + constR0))

-- ⚑⚑ **THE BITING RED CONTROL FOR #3: BENDING A SUPPLIED COMMITMENT MOVES THE MSM.** With
-- `basePts` this was impossible in both directions — the bases were unabsorbed, so a swapped
-- commitment left every challenge alone, and they were free witnesses, so nothing pinned them.
-- Swap ONE absorbed commitment and EVERY challenge moves, because the transcript sponge swallowed
-- its coordinates before the first squeeze.
#guard (List.range shapeSmoke.chals).all (fun c =>
  chalOf shapeSmoke tSwapAbs.sp c != chalOf shapeSmoke tS.sp c)
-- …the fold output moves,
#guard tSwapAbs.ipa.sums.getLastD (0, 0) != tS.ipa.sums.getLastD (0, 0)
-- …the x_hat MSM moves too (its scalars are those challenges), though its own bases did not,
#guard tSwapAbs.msm.sums.getLastD (0, 0) != tS.msm.sums.getLastD (0, 0)
-- …and it reaches all the way to `combined_inner_product` and `b(ζ)`.
#guard tSwapAbs.df.ca.getLastD 0 != tS.df.ca.getLastD 0
#guard tSwapAbs.df.accs.getLastD 0 != tS.df.accs.getLastD 0

-- ⚑ THE CONTRAST THAT MAKES IT A CENSUS AND NOT A BLANKET. A CONSTANT base is not absorbed, so
-- swapping it leaves every challenge exactly where it was — and it still moves the fold, which is
-- what the pin row exists to forbid.
#guard (List.range shapeSmoke.chals).all (fun c =>
  chalOf shapeSmoke tSwapConst.sp c == chalOf shapeSmoke tS.sp c)
#guard tSwapConst.ipa.sums.getLastD (0, 0) != tS.ipa.sums.getLastD (0, 0)

-- ⚑ …and the pin ROW is what refuses it. `Inner_curve.constant` emits `w₀ = x` ∥ `w₃ = y`, and the
-- SAME row's generic-gate body — `KimchiVerify.genericGateConstraint`, read-only — is 0 on the
-- honest coordinates and NONZERO on the swapped ones. So a prover who supplies a different SRS /
-- verifier-key point is refused, not believed.
def pinRowOf (r : Nat) : SRow :=
  baseConstRow (ipx shapeSmoke (qT shapeSmoke r)) (ipy shapeSmoke (qT shapeSmoke r))
    (tS.ipa.bases.getD r (0, 0))
def pinBody (row : SRow) (p : Nat × Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    (row.coeffs.map (fun c => ((c : Int) : ZMod pN)))
    [(p.1 : ZMod pN), 0, 0, (p.2 : ZMod pN), 0, 0]
#guard pinBody (pinRowOf constR0) (tS.ipa.bases.getD constR0 (0, 0)) == 0
#guard (pinBody (pinRowOf constR0) (tSwapConst.ipa.bases.getD constR0 (0, 0)) == 0) == false
-- …and the swap really did change the point, so the red control is not testing equality with itself.
#guard tSwapConst.ipa.bases.getD constR0 (0, 0) != tS.ipa.bases.getD constR0 (0, 0)
#guard tSwapAbs.ipa.bases.getD absR0 (0, 0) != tS.ipa.bases.getD absR0 (0, 0)

-- ── §12b′ — ⚑ A SUPPLIED POINT IS NOW CHECKED ON THE CURVE (§7b, #3's second residue) ──────────
-- Every kimchi curve gate constrains the ADDITION ARITHMETIC and nothing else: `EndoMul`'s
-- polynomials hold for any `(x, y)` in the field. Upstream never has to say so, because a supplied
-- point arrives through `Inner_curve.typ`, whose `check` IS `assert_on_curve`
-- (`snarky_curve.ml:212-229`). This file read the previous proof's commitments in as bare
-- coordinate variables. The exhibit below is an off-curve one, and it passed.

/-- ⚑ THE FORGERY THE MISSING CHECK ALLOWED: absorbed base `absR0`'s `y` bumped by one — a point
that is NOT on Pallas. Nothing else changes; the prover absorbs what he supplies, so the transcript
still swallows exactly these two coordinates and every downstream value is internally consistent. -/
def basesOffCurve (s : StepShape) : List (Nat × Nat) :=
  let bs := stepBases s
  let k := s.msmTerms + absR0
  (List.range bs.length).map (fun i =>
    let p := bs.getD i (0, 0)
    if i == k then (p.1, fAdd p.2 1) else p)

def tOffCurve : StepData := mkStepWith shapeSmoke (basesOffCurve shapeSmoke)
def offPt : Nat × Nat := tOffCurve.ipa.bases.getD absR0 (0, 0)
def honPt : Nat × Nat := tS.ipa.bases.getD absR0 (0, 0)

-- The exhibited point is genuinely OFF the curve, and the honest one is on it — same `x`.
#guard onCurveA honPt
#guard onCurveA offPt == false
#guard offPt.1 == honPt.1 && offPt.2 != honPt.2
-- …and every honest supplied point is on the curve, so the check is SATISFIABLE as well as
-- refutable, at both shapes.
#guard (absRoundList shapeSmoke).all (fun r => onCurveA (tS.ipa.bases.getD r (0, 0)))
#guard (Dregg2.Bridge.MinaStepPrevCommitments.ALL_XY).all onCurveA

/-- The bent instance's R4 rung, composed. -/
def rowsOff : List SRow := rungRows tOffCurve .ipa true
def witOff : List (List Int) := stepWitness tOffCurve 0 rowsOff

-- ⚑⚑ **THE EXHIBIT: EVERY CURVE GATE ACCEPTS THE OFF-CURVE POINT.** `KimchiVerify`'s read-only
-- transcriptions of proof-systems' own `EndoMul` and `CompleteAdd` polynomials are ZERO on every
-- one of those rows of the BENT assembly's composed grid. That is the hole, stated on the emitted
-- object: the fold gadget never looks at membership, so the whole of R4 was satisfied.
#guard ((List.range rowsOff.length).filter
          (fun i => (rowsOff.getD i default).kind == KGateType.endoMul)).all
  (fun i => (endoMulConstraints (R := ZMod pN) (KimchiRenderEndoMul.endo : ZMod pN)
      ((gridRow witOff i).map (fun n => (n : ZMod pN)))
      ((gridRow witOff (i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))
#guard ((List.range rowsOff.length).filter
          (fun i => (rowsOff.getD i default).kind == KGateType.completeAdd)).all
  (fun i => (completeAddConstraints (R := ZMod pN)
      ((gridRow witOff i).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

/-- The absolute row of R4's FIRST `assert_on_curve` row, in the `.ipa` rung. -/
def onCRow0 : Nat := (rungRows tS .msm true).length + (ipaBaseRows shapeSmoke tS.ipa).length
                     + (ipaSeedPinRows shapeSmoke).length
def nOnCRows : Nat := (onCurveRows shapeSmoke).length
/-- A row's own double-`Generic` body, read out of a composed grid. -/
def genBodyAt (rows : List SRow) (w : List (List Int)) (pub r : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    ((rows.getD (r - pub) default).coeffs.map (fun c => ((c : Int) : ZMod pN)))
    ((gridRow w r).take 6 |>.map (fun n => (n : ZMod pN)))

-- ⚑⚑ **AND THE NEW ROWS REFUSE IT.** The same grid, the same rows: `assert_on_curve`'s own
-- `Generic` body is ZERO on the honest assembly and NONZERO on the bent one. Refused where it was
-- accepted, on the emitted object rather than in the value layer.
#guard (List.range nOnCRows).all (fun k => genBodyAt rowsS witS pubS (pubS + onCRow0 + k) == 0)
#guard ((List.range nOnCRows).all (fun k => genBodyAt rowsOff witOff 0 (onCRow0 + k) == 0)) == false
-- …and it is the `assert_square` half that goes red and NOT the `x²`/`x³` ones: the bend was in
-- `y`, which enters `assert_on_curve` only through `y·y − x³ − b`. That is the first point's THIRD
-- half, so it lands in row `onCRow0 + 1`, and row `onCRow0` — the two halves that read `x` alone —
-- still holds. A control that reddened both rows would be measuring the re-run, not the check.
#guard genBodyAt rowsOff witOff 0 onCRow0 == 0
#guard (genBodyAt rowsOff witOff 0 (onCRow0 + 1) == 0) == false

-- ⚑ EVERY `Generic` ROW OF THE HONEST ASSEMBLY SATISFIES ITS OWN BODY, on the composed grid — the
-- one gate family §12's sweeps did not evaluate. (The `pubS` public rows are excluded: a public row
-- is `w₀ − pᵣ = 0` and the `pᵣ` term is the prover's, `generic.rs:297-304`.)
#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.generic)).all
  (fun i => genBodyAt rowsS witS pubS (pubS + i) == 0)

-- ⚑ THE ROWS ARE THE CENSUS, stated as equalities. One `assert_on_curve` per ABSORBED base — three
-- `Generic` halves each, packed two to a row — and NOT ONE for a constant base, which is pinned
-- coordinate-for-coordinate instead. A deleted check moves both numbers.
#guard nOnC shapeSmoke == (absRoundList shapeSmoke).length + tCommN shapeSmoke + 2
#guard nOnC shapeStep == 48 + 7 + 2
#guard nOnCRows == (3 * nOnC shapeSmoke + 1) / 2
#guard (onCurveRows shapeStep).length == (3 * 57 + 1) / 2
-- ⚑ …and the two that arrived with the R1 interleaving are `sg_old[0]` and `delta`, at the tail of
-- the checked list and over the very variables the fold's `~init` and the `cq + delta` add read.
#guard onCVar shapeStep (48 + 7) == (ipx shapeStep (qInit shapeStep), ipy shapeStep (qInit shapeStep))
#guard onCVar shapeStep (48 + 8) == (ipx shapeStep (qDel shapeStep), ipy shapeStep (qDel shapeStep))
#guard Dregg2.Bridge.MinaStepPrevCommitments.onCurve
         Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
#guard Dregg2.Bridge.MinaStepPrevCommitments.onCurve
         Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
-- …and the checked variables ARE the fold's own base coordinates, not a fresh copy: `x`'s class
-- gains the two `assert_on_curve` halves that read it (`x·x` and `x2·x`) on top of the
-- `ipaBlocks` `EndoMul` reads and the transcript's absorb row.
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke absR0))).length == shapeSmoke.ipaBlocks + 6
#guard (classCells posS (ipy shapeSmoke (qT shapeSmoke absR0))).length == shapeSmoke.ipaBlocks + 5
-- …and a CONSTANT base's class gains NOTHING from §7b — pinned, not checked, which is upstream's
-- own split (`Inner_curve.constant` is a literal and carries no `check`). Its `ipaBlocks + 2` is the
-- `EndoMul` reads, the pin row and segment C's index absorb, and no `assert_on_curve` half.
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke constR0))).length == shapeSmoke.ipaBlocks + 4
-- …and the two intermediates really are `x²` and `x³` of that point.
#guard tS.ipa.bases.getD absR0 (0, 0) == honPt
#guard fMul honPt.1 honPt.1 == fMul honPt.1 honPt.1
#guard fMul (fMul honPt.1 honPt.1) honPt.1 != 0

-- ── §12c — ⚑ THE CHALLENGE HIGH PART IS RANGE-CHECKED (simplification #1, retired) ─────────────
-- `lowest_128_bits ~constrain_low_bits:true` asserts BOTH parts (`util.ml:98-99`) and
-- `assert_n_bits ~n:128` is `ignore (to_field_checked … ~num_bits:128)` — the chain emits, only the
-- value is dropped (`step_verifier.ml:88-97`). R2 emitted the LOW chain and the decomposition row
-- and stopped there, which left the decomposition row as one equation in two unknowns.

/-- The transcript squeeze challenge `c` is split out of. -/
def sqOf (c : Nat) : Nat := (tS.sp.states.getD (sqBlock shapeSmoke c + 1) []).getD 0 0
/-- The honest `(combined_inner_product, bit)` pair transcript block `oCip` absorbs — the statement
word R8 binds, so a control that re-runs the sponge feeds it what the assembly feeds it. -/
def cipWordOf (t : StepData) : Nat × Nat := (t.fin.cipShift, CIP_BIT)
def TWO128 : Nat := 2 ^ 128 % pN
def INV_TWO128 : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv TWO128
/-- ⚑ THE FORGERY THE MISSING CHECK ALLOWED: the prover picks ANY 128-bit low part and the
decomposition row hands back the high part that makes it hold. -/
def forgedLo : Nat := (chalOf shapeSmoke tS.sp 0 + 1) % 2 ^ 128
def forgedHi : Nat := fMul (fSub (sqOf 0) forgedLo) INV_TWO128

-- The forged pair satisfies the decomposition row EXACTLY as the honest pair does…
#guard fAdd forgedLo (fMul TWO128 forgedHi) == sqOf 0 % pN
#guard fAdd (chalOf shapeSmoke tS.sp 0) (fMul TWO128 (hiOf shapeSmoke tS.sp 0)) == sqOf 0 % pN
-- …the forged LOW part passes its own `to_field_checked` chain (it is a 128-bit value, so the
-- `EndoMulScalar` fold reconstructs it)…
#guard forgedLo < 2 ^ 128
#guard ((emsAccs shapeSmoke forgedLo).getLastD (0, 2, 2)).1 == forgedLo
-- …and it is a DIFFERENT challenge from the honest one. That is the whole attack: Fiat-Shamir
-- becomes prover-chosen.
#guard forgedLo != chalOf shapeSmoke tS.sp 0

-- ⚑⚑ **THE BITING RED CONTROL FOR #1.** The forced high part does NOT fit in 128 bits, so the new
-- chain's `EndoMulScalar` fold cannot reconstruct it and `Field.Assert.equal n scalar` fails. An
-- out-of-range challenge is REFUSED where it was accepted this morning.
#guard 2 ^ 128 ≤ forgedHi
#guard ((emsAccs shapeSmoke forgedHi).getLastD (0, 2, 2)).1 != forgedHi
-- …and the check is SATISFIABLE as well as refutable: the honest high part fits and its own chain
-- reconstructs it, at every challenge.
#guard (List.range shapeSmoke.chals).all (fun c => hiOf shapeSmoke tS.sp c < 2 ^ 128)
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((emsAccs shapeSmoke (hiOf shapeSmoke tS.sp c)).getLastD (0, 2, 2)).1 == hiOf shapeSmoke tS.sp c)
#guard tS.defc.hi.getD 1 0 < 2 ^ 128
#guard ((emsAccs shapeSmoke (tS.defc.hi.getD 1 0)).getLastD (0, 2, 2)).1 == tS.defc.hi.getD 1 0

-- ⚑ …and the chain is WIRED TO THE DECOMPOSITION ROW's OWN `hi` CELL, not to a fresh copy: `vHi c`
-- is read by exactly two rows — the split row that produced it and the range chain's tie. Equality,
-- because a floor of `≥ 1` holds with the whole chain deleted.
#guard (List.range shapeSmoke.chals).all (fun c =>
  (classCells posS (vHi shapeSmoke c)).length == 2)
#guard (classCells posS (vDHi shapeSmoke 1)).length == 2
-- …and §8g's ξ chain has NO high part at all, because its source is already a `Challenge.t` —
-- upstream splits nothing there either (`let xi = scalar xi`).
#guard (classCells posS (vDHi shapeSmoke 0)).length == 0

-- ── §12c′ — ⚑ THE THIRD `lowest_128_bits`: R8's, AND IT WAS THE WORST OF THE THREE ─────────────
-- The two above are R2's transcript squeezes and §8g's `r`. The THIRD lives INSIDE the compiled
-- finalize program (§8f): `xi_actual = lowest_128_bits (squeeze fr_sponge)`
-- (`step_verifier.ml:820-822,1102`), where the high part is an `AOp.wit` — a cell NO row defines.
-- It is the worst of the three because §8g's chain 0 lifts the very word `xi_correct` compares
-- against INTO THE FOLD, so a prover who chooses ξ chooses `combined_inner_product`'s multiplier.

/-- R8's own `lowest_128_bits` cells, as circuit variables. -/
def finHiVar : PVar := aVarAt (baseFin shapeSmoke tS.ft) tS.fin.fp.prog tS.fin.fp.slots.xiHi
def finLoVar : PVar := aVarAt (baseFin shapeSmoke tS.ft) tS.fin.fp.prog tS.fin.fp.slots.xiActual

/-- Re-run R8's finalize program with a CHOSEN ξ: the statement word set to `xi'` and
`lowest_128_bits`' high part set to `hi'`. Every other input, and every `Field.equal` witness, is
the honest one — so what this measures is whether R8's own gadget accepts, not whether some other
leg was sabotaged. Returns `(out, xi_correct, xi_actual)`; `out` is the value the rung's last row
ASSERTS equals 1. -/
def finAtChosenXi (xi' hi' : Nat) : Nat × Nat × Nat :=
  let s := shapeSmoke
  let env := (finInputEnv s tS.sp tS.ft tS.df tS.segB tS.specB rFoldS).map
    (fun p => if p.1 == vXiStmt s then (p.1, (xi' : Int)) else p)
  let p := finProgOf (finWireOf s tS.ft) (finCfgOf s hi')
  let vs := aEval (envLookupAt (envIndex env)) p.prog
  (vs.getD p.slots.out 0, vs.getD p.slots.xc 0, vs.getD p.slots.xiActual 0)

/-- ⚑ THE FORGERY R8's MISSING HIGH CHAIN ALLOWED: the prover names the ξ he wants and the
decomposition row hands back the high part that makes `xi_correct` hold. -/
def forgedXi : Nat := (tS.fin.xiStmt + 1) % 2 ^ 128
def forgedXiHi : Nat := fMul (fSub sq1S forgedXi) INV_TWO128

-- The forged pair satisfies R8's decomposition EXACTLY as the honest pair does…
#guard fAdd forgedXi (fMul TWO128 forgedXiHi) == sq1S % pN
#guard fAdd tS.fin.xiStmt (fMul TWO128 tS.fin.xiHi) == sq1S % pN
-- …the forged ξ is a legal `Challenge.t`, so §8g's chain 0 (`Field.Assert.equal n scalar`, no
-- split) reconstructs it and the FOLD accepts it as its multiplier…
#guard forgedXi < 2 ^ 128
#guard ((emsAccs shapeSmoke forgedXi).getLastD (0, 2, 2)).1 == forgedXi
-- …and it is a DIFFERENT ξ from the honest one.
#guard forgedXi != tS.fin.xiStmt

-- ⚑⚑ **THE EXHIBIT: R8's PROGRAM ACCEPTS IT.** `out = 1` — the value the rung's last row asserts —
-- with `xi_correct = 1` and `xi_actual` equal to the ξ the prover named. Every other leg honest.
#guard finAtChosenXi forgedXi forgedXiHi == (1, 1, forgedXi)
-- …and the honest pair does the same, so the helper is measuring the gadget and not a broken input.
#guard finAtChosenXi tS.fin.xiStmt tS.fin.xiHi == (1, 1, tS.fin.xiStmt)
-- ⚑ …and the forgery is NOT a no-op: the fold's own multiplier moves, and so does
-- `combined_inner_product` — this is Fiat-Shamir becoming prover-chosen, not a relabelling.
#guard (Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) forgedXi
         == foldMulOf sq1S) == false
#guard (Dregg2.Circuit.Emit.KimchiVerify.cipR
          (Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) forgedXi)
          (foldMulOf sq2S)
          (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN)))
        == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
             (tS.df.ez.map (fun n => (n : ZMod pN)))
             (tS.df.ew.map (fun n => (n : ZMod pN)))) == false

-- ⚑⚑ **AND THE NEW HIGH CHAIN REFUSES IT.** The forced high part does not fit in 128 bits, so its
-- `EndoMulScalar` fold cannot reconstruct it and the chain's `Field.Assert.equal n scalar` fails.
-- Accepted before, REFUSED after — the same shape §12c has for R2.
#guard 2 ^ 128 ≤ forgedXiHi
#guard ((emsAccs shapeSmoke forgedXiHi).getLastD (0, 2, 2)).1 != forgedXiHi
-- …and the chain is SATISFIABLE: the honest high part fits and its own chain reconstructs it, as
-- does the honest low part (`~constrain_low_bits:true` asserts that one too, `util.ml:99`).
#guard tS.fin.xiHi < 2 ^ 128 && tS.fin.xiStmt < 2 ^ 128
#guard ((emsAccs shapeSmoke tS.fin.xiHi).getLastD (0, 2, 2)).1 == tS.fin.xiHi
#guard ((emsAccs shapeSmoke tS.fin.xiStmt).getLastD (0, 2, 2)).1 == tS.fin.xiStmt
-- …and the split is doing work: the squeeze is NOT already 128 bits, so `hi ≠ 0`.
#guard tS.fin.xiHi != 0

-- ⚑ …and the chains are wired to the PROGRAM's OWN cells, not to fresh copies. `hi` is an
-- `AOp.wit`: with the chain gone its class is ONE cell (the `hi·2¹²⁸` multiply that reads it) and
-- nothing else in the assembly touches it — so this equality, unlike a floor, cannot survive the
-- chain's deletion.
#guard (classCells posS finHiVar).length == 2
-- `xi_actual`'s four: the `sub` row that defines it, `xi_correct`'s own difference row, its σ-only
-- probe, and the new low chain's tie.
#guard (classCells posS finLoVar).length == 4
-- …and they really are the finalize program's slots, not a parallel pair: the values agree.
#guard tS.fin.vals.getD tS.fin.fp.slots.xiHi 0 == tS.fin.xiHi
#guard tS.fin.vals.getD tS.fin.fp.slots.xiActual 0 == tS.fin.xiStmt

-- ── §12d — ⚑ THE SPONGE **INPUT** IS DERIVED: `sponge_after_index` ─────────────────────────────
-- §12c and §12c′ close one half of Fiat–Shamir: GIVEN the sponge state, no challenge here is
-- prover-chosen. This is the other half. Until 2026-08-02 the plonk index the transcript starts
-- from was 58 `hmVal` fixtures no row pinned, so a prover chose the sponge's INPUT and steered every
-- squeeze without breaking a single decomposition. `step_verifier.ml:1149-1157` derives it —
-- `Sponge.absorb` of `index_to_field_elements index`, the wrap verifier key's 28 commitments — and
-- `:529-535` squeezes a copy of that sponge and absorbs the result as the transcript's FIRST word.

-- ⚑ THE 56 ABSORBED WORDS ARE THE PLONK INDEX, in `index_to_field_elements` order
-- (`side_loaded_verification_key.ml:159-183`: `sigma_comm @ coefficients_comm @` six selectors).
#guard Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.length == N_IDX_COMMS
#guard (List.range N_IDX_WORDS).all (fun i =>
  idxWordAt i == Dregg2.Bridge.MinaStepPrevCommitments.INDEX_WORDS.getD i 0)

-- ⚑ …AND 27 OF THE 28 **ARE THE FOLD'S OWN `.const` BASES** — the plonk index the sponge hashes and
-- the plonk index `combine_split_commitments` multiplies by are ONE object, not two copies that
-- agree today. Stated at `shapeStep`: the smoke shape's 3 IPA rounds cannot reach round 40, so it
-- pins all 28 itself, which is why the σ pins below are smoke and the census pins are step.
#guard (List.range N_IDX_COMMS).countP (fun k => idxSrc shapeStep k != none) == 27
#guard idxOwn shapeStep == [6]
-- …and the smoke shape reaches exactly ONE of them (round 4 = `generic_comm`, index commitment 22),
-- so both legs of `idxVar` are exercised at both scales.
#guard idxOwn shapeSmoke == (List.range N_IDX_COMMS).filter (fun k => k != 22)
#guard (List.range N_IDX_COMMS).all (fun k =>
  match idxSrc shapeStep k with
  | some r => ipaSrc shapeStep r == BaseSrc.const
              && REAL_IPA_XY.getD r (0, 0)
                 == Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0)
  | none => k == 6)
-- …27 DISTINCT rounds, so two index words cannot be quietly sharing one base.
#guard ((List.range N_IDX_COMMS).filterMap (idxSrc shapeStep)).dedup.length == 27
-- ⚑ …and there is now NO constant fold round the index census fails to claim: the fold's 27
-- constants are EXACTLY the plonk index minus `sigma_comm[6]`, because the twenty-eighth —
-- `COMBINE_XY[3]`, `ft_comm` — stopped being a constant when §6b computed it. (This pin read
-- `== [2]` until 2026-08-02; that `2` was the residue, and it is the round §6b writes.)
#guard ((List.range shapeStep.ipaRounds).filter (fun r =>
          ipaSrc shapeStep r == BaseSrc.const
          && !(((List.range N_IDX_COMMS).filterMap (idxSrc shapeStep)).contains r))) == []
-- …and the 28th index commitment, `sigma_comm[6]`, is the one `Vector.split m.sigma_comm` hands to
-- `Common.ft_comm` as `sigma_comm_last` (`common.ml:243-246`) — hence pinned here and not routed.
#guard idxSrc shapeStep 6 == none && idxRoundOf 6 == none

-- ⚑ SEGMENT C's `Not_opt` PREFIX **IS** `sponge_after_index`. Its state after the 28 index blocks
-- is exactly the sponge upstream copies (`Sponge.copy after_index`, `:1163`), and `index_digest` is
-- one more permutation of that state.
#guard tS.segC.states.getD (N_IDX_WORDS / 2) [] == idxAfterState
#guard idxDigestState == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm idxAfterState
#guard indexDigest == idxDigestState.getD 0 0
-- …and it is not degenerate: the state moved off zero, the digest is nonzero, and it is a DIFFERENT
-- value from segment C's own final squeeze (which absorbs 30 more words after it).
#guard idxAfterState != [0, 0, 0]
#guard indexDigest != 0
#guard indexDigest != (tS.segC.states.getLastD []).getD 0 0

-- ⚑ THE WIRES. Each pinned index coordinate is read by its `Inner_curve.constant` row and by
-- segment C's own absorb row — two cells, an equality, so deleting either leg reds.
-- ⚑ …with TWO exceptions the census names. Commitment 22 owns NO variable at this shape — `idxVar`
-- routes it to the fold's round-4 base, which is the whole substance of §3c. And commitment 6,
-- `sigma_comm_last`, is also §6b's term-0 BASE: `FTC_CHUNKS` `VarBaseMul` reads, the doubling's two
-- and the odd-branch add's one, on top of the pin row and segment C's absorb.
#guard (List.range N_IDX_COMMS).all (fun k =>
  if k == 22 then (classCells posS (vIdxX shapeSmoke k)).length == 0
                  && (classCells posS (vIdxY shapeSmoke k)).length == 0
  else if k == 6 then (classCells posS (vIdxX shapeSmoke k)).length == FTC_CHUNKS + 5
                      && (classCells posS (vIdxY shapeSmoke k)).length == FTC_CHUNKS + 5
  else (classCells posS (vIdxX shapeSmoke k)).length == 2
       && (classCells posS (vIdxY shapeSmoke k)).length == 2)
#guard idxVar shapeSmoke 22 0 == ipx shapeSmoke (qT shapeSmoke constR0)
#guard (classCells posS (idxVar shapeSmoke 22 0)).length == shapeSmoke.ipaBlocks + 4

-- …and `index_digest`'s three output lanes: lane 0 is read by the digest permutation's closing
-- `Zero` row, by its σ-only probe, AND by R1's block-0 absorb row — that last cell is the whole
-- point, and it is what a `.length ≥ 2` floor would not have caught.
#guard (classCells posS (vIdxD shapeSmoke 0)).length == 3
#guard (classCells posS (vIdxD shapeSmoke 1)).length == 2
#guard (classCells posS (vIdxD shapeSmoke 2)).length == 1
#guard ((classCells posS (vIdxD shapeSmoke 0)).filter (fun c => c.row < nTrans)).length == 1

/-- The state entering the LAST index absorb block: everything before it is untouched by the word
the prover grinds, so a candidate costs TWO permutations rather than fifty-eight. -/
def idxPreLast : List Nat := (idxStatesWith idxWordAt).getD (N_IDX_COMMS - 1) []
/-- `index_digest` when the LAST index word is `w` and every earlier one is honest. -/
def idxDigestAtLast (w : Nat) : Nat :=
  (Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
    (Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
      [ (idxPreLast.getD 0 0 + idxWordAt (N_IDX_WORDS - 2)) % pN
      , (idxPreLast.getD 1 0 + w) % pN, idxPreLast.getD 2 0 ])).getD 0 0

-- the helper reproduces the assembly's own digest on the honest word, so what follows measures the
-- grind and not a second sponge.
#guard idxDigestAtLast (idxWordAt (N_IDX_WORDS - 1)) == indexDigest

/-- ⚑ THE TARGET THE PROVER CHOOSES. Any predicate on the squeeze will do; this one asks for a
digest divisible by 16, which the honest key does not give. -/
def GRIND_MOD : Nat := 16
def grindCand (t : Nat) : Nat := (idxWordAt (N_IDX_WORDS - 1) + t) % pN
/-- …and the SEARCH: the first offset whose digest hits it. This is the attack, run. -/
def grindT : Nat :=
  (((List.range 48).map (· + 1)).find?
     (fun t => idxDigestAtLast (grindCand t) % GRIND_MOD == 0)).getD 0
def groundWord : Nat := grindCand grindT
def groundDigest : Nat := idxDigestAtLast groundWord

-- ⚑⚑ **THE EXHIBIT: THE GRIND SUCCEEDS.** The honest key MISSES the chosen target; the prover finds
-- an input that HITS it, by addition, in under 48 tries — and the resulting `index_digest` is a
-- different value from the honest one.
#guard indexDigest % GRIND_MOD != 0
#guard grindT != 0
#guard groundDigest % GRIND_MOD == 0
#guard groundDigest != indexDigest
#guard groundWord != idxWordAt (N_IDX_WORDS - 1)

/-- R1's transcript at the GROUND digest — the assembly's own `runSpongeWith`, one word changed. -/
def spGround : SpongeData :=
  runSpongeWith shapeSmoke (stepBases shapeSmoke) groundDigest (cipWordOf tS)

-- ⚑⚑ **AND IT STEERS EVERY SQUEEZE.** One plonk-index word, chosen by the prover, and EVERY
-- transcript challenge moves — β, γ, α, ζ, ξ, and with them the x_hat MSM's scalars, the fold's
-- weights and `combined_inner_product`. That is Fiat–Shamir's input becoming prover-chosen, which
-- is the attack the range checks of §12c/§12c′ do not touch.
#guard (List.range shapeSmoke.chals).all (fun c =>
  chalOf shapeSmoke spGround c != chalOf shapeSmoke tS.sp c)
#guard (spGround.states.getLastD []).getD 0 0 != (tS.sp.states.getLastD []).getD 0 0

/-- Segment C re-run with the ground word in the last index slot. -/
def segCGround : SegData :=
  runSeg { tS.specC with
           ws := tS.specC.ws.set (N_IDX_WORDS - 1) (idxVar shapeSmoke 27 1, groundWord) }

-- ⚑ **THE HOLE, ON THE EMITTED OBJECT.** The sponge itself never objects: with the ground word in
-- place, every one of segment C's blocks is still exactly `Ref.perm` of its absorbed state (or the
-- state unchanged, where the mask drops it). A `Poseidon` gate constrains the permutation and NOT
-- what was fed to it, so before §3c there was nothing in the assembly that could refuse this.
#guard (List.range tS.specC.blocks).all (fun b =>
  let ws := tS.specC.ws.set (N_IDX_WORDS - 1) (idxVar shapeSmoke 27 1, groundWord)
  let pre := segCGround.states.getD b []
  let post := if b < tS.specC.nb then
      [ fAdd (pre.getD 0 0) ((ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  if b < tS.specC.nb && tS.specC.maskedAt b && tS.specC.keepBit b == 0 then
    segCGround.states.getD (b + 1) [] == pre
  else segCGround.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- …and it really is a different sponge, so the pin above is not comparing the honest run to itself.
#guard (segCGround.states.getLastD []).getD 0 0 != (tS.segC.states.getLastD []).getD 0 0

/-- The `Inner_curve.constant` row §3c emits for index commitment `k`. -/
def idxPinRow (k : Nat) : SRow :=
  baseConstRow (vIdxX shapeSmoke k) (vIdxY shapeSmoke k)
    (Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0))

-- ⚑⚑ **AND THE DERIVED VERSION REFUSES IT.** The pin row's OWN generic-gate body —
-- `KimchiVerify.genericGateConstraint`, proof-systems' polynomial, read-only — is 0 on the verifier
-- key's coordinates and NONZERO on the ground one. Accepted this morning, refused now.
#guard pinBody (idxPinRow 27) (idxVal 27 0, idxVal 27 1) == 0
#guard (pinBody (idxPinRow 27) (idxVal 27 0, groundWord) == 0) == false
-- …and the check is SATISFIABLE at every one of the 28, not just the one the grind used.
#guard (List.range N_IDX_COMMS).all (fun k => pinBody (idxPinRow k) (idxVal k 0, idxVal k 1) == 0)
-- ⚑ …and at the COMMITTED shape the same word is refused TWICE, because it is not a private
-- variable there: index commitment 27 is `endomul_scalar_comm`, which is fold round 9's base, so
-- bending it moves `combine_split_commitments` as well as failing round 9's own pin row.
#guard idxSrc shapeStep 27 == some 9
#guard idxVar shapeStep 27 1 == ipy shapeStep (qT shapeStep 9)
#guard REAL_IPA_XY.getD 9 (0, 0)
        == Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD 27 (0, 0)

-- ── §12e — ⚑ `Common.ft_comm`'s MSM, AND `t_comm` STOPS BEING FREE (#5's head, retired) ────────
-- The previous rung derived `sponge_after_index` and left 45 of R1's 142 absorbed words free,
-- naming `t_comm`'s 14 as the ones that could only leave the list by being CONSUMED. §6b consumes
-- them, and everything below is stated on the EMITTED object rather than on the intention.

-- ⚑ THE SHAPE IS `common.ml`'s, counted. Eight `scale_fast2`s at `chunks_needed ~num_bits:254 = 51`
-- five-bit chunks (`plonk_curve_ops.ml:69-70,254-257`), and the `tCommN` cap does NOT bind at the
-- committed shape — so no quotient chunk silently stays a free witness there.
#guard tCommN shapeStep == N_TCOMM
#guard tCommN shapeStep == Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.length
#guard ftcTerms shapeStep == 8
#guard tCommN shapeSmoke == 3 && ftcTerms shapeSmoke == 4
#guard FTC_CHUNKS == (254 + 4) / 5 && 5 * FTC_CHUNKS == 255
-- …and it is a DIFFERENT width from R3's, which is exactly what #2's warning is about.
#guard FTC_CHUNKS != shapeSmoke.msmChunks

-- ⚑ THE ROW CENSUS, as an equality over its own sub-lists: the two `Shifted_value.Type2` splits,
-- `ftcTerms` ladders and `common.ml`'s add chain. A vanished sub-list moves this number.
#guard (ftcRows shapeSmoke tS.ftw tS.ftc true).length
        == (ftcScalRows shapeSmoke tS.ftw true).length
           + (ftcNZeroRows shapeSmoke).length
           + ftcTerms shapeSmoke * (ftcTermRows shapeSmoke tS.ftc true 0).length
           + (ftcAddRows shapeSmoke tS.ftc true).length
-- ⚑ …and `plonk_curve_ops.ml:158`'s counter seed is pinned for every one of them (§12f): one
-- `Generic` half per `scale_fast2`, packed two to a row.
#guard (ftcNZeroRows shapeSmoke).length == (ftcTerms shapeSmoke + 1) / 2
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (classCells posS (ftcN shapeSmoke k 0)).length == 2)
-- …one term is `2·FTC_CHUNKS` chunk rows, the doubling and odd-branch `add_fast`s, two probes and
-- the four `Generic` rows of the top-bit assert, the negate and `G.if_`'s six halves.
#guard (ftcTermRows shapeSmoke tS.ftc true 0).length == 2 * FTC_CHUNKS + 8
#guard (ftcAddRows shapeSmoke tS.ftc true).length == 2 * (tCommN shapeSmoke - 1) + 5
#guard (ftcRows shapeSmoke tS.ftw tS.ftc true).length == 455
-- …and `common.ml`'s own operation count: `tCommN + 1` `Ops.add_fast`s, `ftcTerms` scales.
#guard tS.ftc.addCells.length == tCommN shapeSmoke + 1
#guard tS.ftc.terms.length == ftcTerms shapeSmoke
#guard tS.ftc.adds.length == tCommN shapeSmoke

-- ⚑⚑ **`t_comm`'s COORDINATES ARE THE TRANSCRIPT'S WORDS AND THE MSM's OPERANDS.** One σ class
-- spanning `Poseidon`, `assert_on_curve` and `VarBaseMul`. The Horner SEED `t_comm[n−1]` is term 1's
-- base, so its class is the whole ladder; a chunk that is only an ADDEND still has five cells.
-- Equalities, so a deleted leg reds rather than passing a floor.
#guard (classCells posS (vTcX shapeSmoke (tCommN shapeSmoke - 1))).length == FTC_CHUNKS + 7
#guard (classCells posS (vTcY shapeSmoke (tCommN shapeSmoke - 1))).length == FTC_CHUNKS + 6
#guard (classCells posS (vTcX shapeSmoke 0)).length == 5
#guard (classCells posS (vTcY shapeSmoke 0)).length == 4
#guard ((classCells posS (vTcX shapeSmoke 0)).filter (fun c => c.row < nTrans)).length == 1
#guard ((classCells posS (vTcY shapeSmoke 0)).filter (fun c => c.row < nTrans)).length == 1
-- ⚑ …AND THE CONTRAST THAT SAYS WHAT "FREE" MEANT. A surviving `vMsg` word's class is ONE cell —
-- the absorb row. That is the class every `t_comm` word was in before §6b: no row pins it, no
-- gadget reads it, and a `Poseidon` gate constrains the permutation and not what was fed to it.
#guard (classCells posS (vMsg shapeSmoke 0 1)).length == 1
-- …and `t_comm` is the FOURTH provenance in the assembly, in none of the other three lists.
#guard Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.all (fun p =>
  !(Dregg2.Bridge.MinaStepPrevCommitments.ALL_XY.contains p)
  && !(Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.contains p))

-- ⚑ THE SCALARS ARE R6's OWN CELLS and not statement words (§6b's named divergence, a
-- strengthening): `Plonk_checks.checked`'s `perm` and the `ζ^n` slot.
#guard tS.ftw.permV == aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog tS.ft.fp.slots.perm
#guard tS.ftw.zetaV == aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog tS.ft.fp.slots.zetaN
#guard tS.ftw.permVal == tS.ft.vals.getD tS.ft.fp.slots.perm 0
#guard tS.ftw.zetaVal == tS.ft.vals.getD tS.ft.fp.slots.zetaN 0
#guard tS.ftw.permVal != 0 && tS.ftw.zetaVal != 0 && tS.ftw.permVal != tS.ftw.zetaVal
-- …`Shifted_value.Type2`'s split reconstructs each of them, and `s_div_2 < 2^254`, so
-- `scale_fast2`'s top-bit assert is SATISFIABLE and not decoration.
#guard (List.range N_FTC_SCAL).all (fun c =>
  let v := ftcScalVal tS.ftw c
  2 * (v / 2) + v % 2 == v && v / 2 < 2 ^ 254)
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (tS.ftc.terms.getD k default).bits.headD 1 == 0)
-- …the ladder's FINAL counter cell IS `s_div_2`'s variable, per term — `Field.Assert.equal !n_acc
-- scalar` (`plonk_curve_ops.ml:208`) — and every term's chain really reconstructs it.
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  ftcN shapeSmoke k FTC_CHUNKS == ftcDiv2 shapeSmoke (ftcScalOf k))
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (tS.ftc.terms.getD k default).td.ns.getLastD 0 == ftcScalVal tS.ftw (ftcScalOf k) / 2)
-- …and the SHARING is upstream's: `scale_fast2` takes an already-split pair, so the `n−1` Horner
-- scales and the closing one read ONE `s_div_2` class and `perm` reads its own.
#guard (classCells posS (ftcDiv2 shapeSmoke 0)).length == 3
#guard (classCells posS (ftcDiv2 shapeSmoke 1)).length == 5
#guard (classCells posS (ftcOdd shapeSmoke 1)).length == 11

/-- `[2^n]·P` in Jacobian. -/
def jPow2 (n : Nat) (P : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (List.range n).foldl (fun Q _ => jDbl Q) P
/-- `[s + 2^255]·g` — `scale_fast2`'s own semantics (`plonk_curve_ops.ml:236-249`;
`shifted_value.ml:140-150`: `to_field t = t + 2^{size_in_bits}`), computed by `PastaCurve`'s
INVERSION-FREE Jacobian double-and-add, an entirely separate formula family from the affine ladder. -/
def ftcJacScale (g : Nat × Nat) (sv : Nat) : Nat × Nat × Nat :=
  match scMulM pN sv (jOf g) with
  | some R => jAdd (jPow2 255 (jOf g)) R
  | none => jPow2 255 (jOf g)

-- ⚑⚑ **THE LADDER COMPUTES WHAT `scale_fast2` SAYS IT DOES**, checked against that oracle without
-- inversion. Both scalar blocks, so `perm` and `ζ^n` are each exercised.
#guard jacEqM pN (jOf (tS.ftc.terms.getD 0 default).res) (ftcJacScale ftcSigma tS.ftw.permVal)
#guard jacEqM pN (jOf (tS.ftc.terms.getD 1 default).res)
                 (ftcJacScale (ftcTc (tCommN shapeSmoke - 1)) tS.ftw.zetaVal)
-- …and the oracle DISCRIMINATES: a one-off scalar gives a different point, so the pin is not
-- comparing a value with itself.
#guard (jacEqM pN (jOf (tS.ftc.terms.getD 0 default).res)
                  (ftcJacScale ftcSigma (tS.ftw.permVal + 1))) == false

-- ⚑⚑ **AND THE `Ops.add_fast` CHAIN IS `common.ml:246-256`, add for add**, recomputed in Jacobian
-- from the ladders' own outputs: the `n−1` Horner adds, `f_comm + chunked_t_comm`, and the closing
-- `+ negate (scale chunked_t_comm zeta_to_domain_size)`.
#guard (List.range (tCommN shapeSmoke - 1)).all (fun a =>
  jacEqM pN (jOf (tS.ftc.adds.getD a (0, 0)))
            (jAdd (jOf (ftcTc (tCommN shapeSmoke - 2 - a)))
                  (jOf (tS.ftc.terms.getD (a + 1) default).res)))
#guard jacEqM pN (jOf (tS.ftc.adds.getD (tCommN shapeSmoke - 1) (0, 0)))
                 (jAdd (jOf (tS.ftc.terms.getD 0 default).res)
                       (jOf (tS.ftc.adds.getD (tCommN shapeSmoke - 2) (0, 0))))
#guard jacEqM pN (jOf tS.ftc.out)
                 (jAdd (jOf (tS.ftc.adds.getD (tCommN shapeSmoke - 1) (0, 0)))
                       (jNeg (jOf (tS.ftc.terms.getD (tCommN shapeSmoke) default).res)))
-- …and `ft_comm` is a genuine curve point, not a coordinate pair that happens to satisfy the gates.
#guard onCurveA tS.ftc.out

-- ⚑⚑ **R4 ROUND `FTC_ROUND`'s BASE IS THIS MSM's OUTPUT.** Not a supplied commitment and not an
-- `Inner_curve.constant`: the `complete_add` closing `common.ml:255-256` writes the fold's own base
-- variables. `combine_split_commitments`' commitment 3 IS `ft_comm` (`step_verifier.ml:606`), and
-- round `r` folds commitment `r+1`.
#guard ipaSrc shapeSmoke FTC_ROUND == BaseSrc.computed
#guard ipaSrc shapeStep FTC_ROUND == BaseSrc.computed
#guard tS.ipa.bases.getD FTC_ROUND (0, 0) == tS.ftc.out
#guard ((ftcAddRows shapeSmoke tS.ftc true).getLastD default).perm
        == [ some (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))
           , some (ipy shapeSmoke (qT shapeSmoke FTC_ROUND)), none, none, none, none, none ]
#guard (let rs := ftcAddRows shapeSmoke tS.ftc true
        let r := rs.getD (rs.length - 2) default
        r.kind == KGateType.completeAdd
        && r.perm.getD 4 none == some (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))
        && r.perm.getD 5 none == some (ipy shapeSmoke (qT shapeSmoke FTC_ROUND)))
-- …the supplied list still carries the real block's own `COMBINE_XY[3]` and the assembly IGNORES
-- it — which is the point: a derived value cannot agree with a fixture by construction, because the
-- scalars here are R6's and not the block's `Fq` deferred values.
#guard ipaBaseOf shapeSmoke (stepBases shapeSmoke) FTC_ROUND
        == Dregg2.Bridge.MinaStepPrevCommitments.COMBINE_XY.getD 3 (0, 0)
#guard tS.ftc.out != Dregg2.Bridge.MinaStepPrevCommitments.COMBINE_XY.getD 3 (0, 0)
-- …no pin row for it, and its class is the 32 `EndoMul` reads plus the add's output and the probe.
#guard (ipaBaseRows shapeSmoke tS.ipa).all (fun r =>
  r.perm.headD none != some (ipx shapeSmoke (qT shapeSmoke FTC_ROUND)))
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))).length
        == shapeSmoke.ipaBlocks + 4
#guard ((classCells posS (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))).filter
          (fun c => c.row < nTrans)).length == 0

/-- `Common.ft_comm` re-run with `t_comm[i]` replaced by another of the real block's points — a
prover who hands `verify_one` a different, perfectly valid, ON-CURVE quotient commitment. -/
def tcSwapped (i : Nat) : Nat → Nat × Nat := fun k =>
  if k == i then Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0) else ftcTc k
def ftcSwap0 : FtcData := runFtcWith shapeSmoke tS.ftw (tcSwapped 0)

-- ⚑⚑ **IT IS CONSUMED, AND THAT IS THE WHOLE DIFFERENCE FROM ABSORBING IT.** Substitute ONE
-- quotient chunk — chunk 0, which is only a Horner ADDEND and no scale's base — and `ft_comm` moves,
-- so R4 round `FTC_ROUND`'s base moves and the fold moves with it. Before §6b that substitution
-- changed one sponge input and NOTHING else in the circuit.
#guard ftcSwap0.out != tS.ftc.out
#guard (runIpa shapeSmoke (stepBases shapeSmoke) tS.sp ftcSwap0.out).sums.getLastD (0, 0)
        != tS.ipa.sums.getLastD (0, 0)
-- …and the Horner SEED matters too, through the ladder rather than through an add.
#guard (ftcScaleTerm (Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0))
                     tS.ftw.zetaVal).res != (tS.ftc.terms.getD 1 default).res
-- …and so does each SCALAR: bend `perm` by one and `f_comm` moves, so `ft_comm` does.
#guard (ftcScaleTerm ftcSigma (tS.ftw.permVal + 1)).res != (tS.ftc.terms.getD 0 default).res
-- ⚠ ⚑ **AND SAY WHAT THAT DOES NOT DO.** An ON-CURVE substitution is REFUSED by no rung in this
-- assembly. It moves `ft_comm`, R4 round `FTC_ROUND`'s base, the fold and every downstream value —
-- and the check that would refuse it is the IPA opening, i.e. `verified`, which is simplification
-- #11 and is still a witnessed boolean. What §6b buys is narrower and is the thing that was
-- missing: `t_comm` is no longer a word the sponge eats and NOTHING reads. It is an
-- `Inner_curve.typ` value carrying a membership check, an operand of a sub-circuit, and a term in
-- the point R4 folds — so a grind on it is refused (below) instead of being invisible.

-- ⚑⚑ **THE FORMULA, AGAINST A GOLD o1-labs' OWN `SRS::verify` PINNED.** Everything above checks
-- the assembly against itself and against `PastaCurve`. This checks `common.ml:246-256` — the shape
-- §6b's row schedule implements — against the REAL block. `MinaWrapGroupGate` reproduces devnet
-- block 539508's `ft_comm` over the group law (`ftComm_reproduces_kimchi`) and o1-labs' `SRS::verify`
-- accepts the opening proof at that point. The transcription below is §6b's OWN order — seed at
-- `t_comm.(n−1)`, fold `t_comm.(i) + scale res zeta_to_srs_length` downto 0, then
-- `f_comm + chunked + negate (scale chunked zeta_to_domain_size)` — over `MinaWrapGroupGate`'s
-- projective primitives, at the block's own `perm` / ζ powers / commitments. It lands on the gold.
-- ⚠ AND IT SETTLES THE ζ QUESTION §6b names: at the real block the two ζ powers are DIFFERENT
-- (`max_poly_size = 2^15` against `domain_size = 2^14`), where this assembly's `log2n =
-- srs_length_log2 = 16` collapses them. That is a shape fact and it is why the two Horner scalars
-- share one `Shifted_value.Type2` pair HERE and would not THERE.
def ftcHornerReal : Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt :=
  (List.range (N_TCOMM - 1)).foldl
    (fun acc j =>
      Dregg2.Circuit.Emit.MinaWrapGroupGate.padd
        (Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS.getD (N_TCOMM - 2 - j) (0, 0, 0))
        (Dregg2.Circuit.Emit.MinaWrapGroupGate.smul
          Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_SRS acc))
    (Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS.getD (N_TCOMM - 1) (0, 0, 0))
/-- `common.ml:246,255-256` at the real block, with `zeta_to_domain_size` as a PARAMETER so the
Maller-factor conflation is a red control and not a coincidence. -/
def ftcRealAt (zDom : Nat) : Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt :=
  Dregg2.Circuit.Emit.MinaWrapGroupGate.padd
    (Dregg2.Circuit.Emit.MinaWrapGroupGate.padd
      (Dregg2.Circuit.Emit.MinaWrapGroupGate.smul
        Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR
        Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6)
      ftcHornerReal)
    (Dregg2.Circuit.Emit.MinaWrapGroupGate.pneg
      (Dregg2.Circuit.Emit.MinaWrapGroupGate.smul zDom ftcHornerReal))
/-- `zeta_to_domain_size = ζⁿ`, i.e. one MORE than the Maller factor the gate carries. -/
def ZETA_DOM : Nat := Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_DOM_M1 + 1

#guard Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN (ftcRealAt ZETA_DOM)
         Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD
-- …and the Horner alone reproduces kimchi's own `chunk_commitment(zeta_to_srs_len)` gold, so the
-- `downto` order is right and not merely consistent with the sum.
#guard Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN ftcHornerReal
         Dregg2.Circuit.Emit.MinaWrapGroupGate.CHUNKED_T_GOLD
-- ⚑ …and the MALLER FACTOR is load-bearing. `common.ml:256` scales by `zeta_to_domain_size` and the
-- `+ chunked` term is what leaves `(ζⁿ − 1)`; reading `zeta_to_domain_size` AS the Maller factor —
-- the conflation this transcription could most easily have made — gives a DIFFERENT point.
#guard (Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN
          (ftcRealAt Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_DOM_M1)
          Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD) == false
-- …and the two ζ powers really are DIFFERENT at the real block, so `ZETA_SRS` cannot be standing in
-- for `ZETA_DOM` in the pin above.
#guard Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_SRS != ZETA_DOM
#guard (Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN
          (ftcRealAt Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_SRS)
          Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD) == false
-- ⚑ …and the POINTS the assembly consumes ARE that gold's own inputs: `ftcSigma` is
-- `sigma_comm[6]` and `ftcTc` is the block's `t_comm`, coordinate for coordinate.
#guard (List.range N_TCOMM).all (fun i =>
  let p := Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS.getD i (0, 0, 0)
  ftcTc i == (p.1, p.2.1))

-- ── §12e′ — ⚠ ⚑ THE ζ-POWER COLLAPSE: NAMED AT FULL RESOLUTION, DELIBERATELY NOT HALF-FIXED ────
-- `plonk_checks.ml:496-497` computes TWO DIFFERENT values:
--     zeta_to_domain_size = env.zeta_to_n_minus_1 + F.one     -- ζ^{domain_size} of the PREVIOUS
--                                                                WRAP PROOF's own domain
--     zeta_to_srs_length  = pow2pow zeta env.srs_length_log2  -- ζ^{2^srs_length_log2}
-- and `step_verifier.ml:1053` passes `~srs_length_log2:Common.Max_degree.step_log2` = 16
-- (`common.ml:7-9`, `Backend.Tick.Rounds.n`). `Common.ft_comm` multiplies by the SECOND at every
-- Horner step and by the FIRST at the closing scale (`common.ml:251,256`), so upstream's ladder
-- reads TWO cells and this one reads ONE — `ftcScalOf` sends term `n` to the same scalar block as
-- terms `1..n−1`, because R6 is compiled at `log2n = FT_LOG2N = 16` and its `zetaN` slot therefore
-- plays both roles. The collapse is pinned as an EQUALITY here so it is a stated property of the
-- object and not a reader's inference.
#guard N_FTC_SCAL == 2
#guard ftcScalOf (tCommN shapeSmoke) == ftcScalOf 1
#guard ftcScalV tS.ftw (ftcScalOf (tCommN shapeSmoke)) == ftcScalV tS.ftw (ftcScalOf 1)
-- ⚠ …and it is WRONG AT EVERY REAL BLOCK, not fitted to one. The multi-block conformance lane
-- measures `zeta_to_srs_len` = ζ^{2^15} against `zeta_to_domain_size` = ζ^{2^14} on **5/5** devnet
-- blocks (539508 / 540890 / 540906 / 540922 / 540929). The two pins above this section already
-- REFUTE the collapse at 539508: the powers differ, and feeding `ZETA_SRS` where
-- `zeta_to_domain_size` belongs gives a point that is NOT `FT_COMM_GOLD`. So the values are
-- distinguishable and this assembly cannot distinguish them.
-- ⚑ **AND THE FIX IS NAMED PRECISELY, BECAUSE THE OBVIOUS ONE IS WRONG.** It is NOT "give `FtcWire`
-- a third slot": `srs_length_log2 = step_log2 = 16` is CORRECT here, so a `FT_SRS_LOG2` would be
-- `FT_LOG2N` again and the third slot would compute the same field element twice — a
-- partially-distinguished power that still reads one value, which LOOKS retired and is not. The
-- value that is wrong is **R6's DOMAIN**: `ftCfg`'s `log2n`, which this file sets to `FT_LOG2N = 16`
-- and a previous wrap proof sets to `2^14`. Separating the powers therefore means RE-DOMAINING R6
-- and re-welding §13's whole `ft_eval0` chain, `zkPolyR`, `omega` and `MinaWrapFtEval0` at the new
-- domain — a rung, not a hunk. Until that lands, `BRANCH_DOMAIN_LOG2 == FT_LOG2N` is the single
-- place the conflation is written down, and it is pinned.
#guard BRANCH_DOMAIN_LOG2 == FT_LOG2N
#guard FT_N == 2 ^ 16
#guard ftcSigma == ((Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).1,
                    (Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).2.1)

-- ⚑⚑ THE GRIND THAT WAS OPEN UNTIL THIS LANDED (§12d's shape, aimed at `t_comm`).
/-- The transcript block `t_comm`'s LAST chunk occupies — the last absorb block, so a candidate
costs TWO permutations rather than twelve. -/
def tcOrd : Nat := oCip shapeSmoke - 1
/-- …as a BLOCK index. ⚑ Since the R1 interleaving the very next block is ζ's squeeze (`:568`
immediately follows `receive without t_comm` at `:567`), so a candidate still costs TWO permutations
and the challenge it steers is ζ rather than the old numbering's challenge 0. -/
def tcBlk : Nat := absBlock shapeSmoke tcOrd
def tcHon : Nat := (ftcTc (tCommN shapeSmoke - 1)).2
/-- ζ when that word is `w` and every earlier one is honest. -/
def tcChalAt (w : Nat) : Nat :=
  let pre := tS.sp.states.getD tcBlk []
  ((Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
     (Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
       [ (pre.getD 0 0 + (ftcTc (tCommN shapeSmoke - 1)).1) % pN
       , (pre.getD 1 0 + w) % pN, pre.getD 2 0 ])).getD 0 0) % 2 ^ shapeSmoke.chalBits

-- the block really is `t_comm`'s last, ζ really is the squeeze that follows it, and the helper
-- reproduces the assembly's OWN challenge on the honest word — so what follows measures the grind
-- and not a second sponge.
#guard tcOrd == oCip shapeSmoke - 1
#guard sqBlock shapeSmoke shapeSmoke.zetaChal == tcBlk + 1
#guard tCommBlock shapeSmoke tcOrd == some (tCommN shapeSmoke - 1)
#guard msgVar shapeSmoke tcOrd 1 == vTcY shapeSmoke (tCommN shapeSmoke - 1)
#guard tcChalAt tcHon == chalOf shapeSmoke tS.sp shapeSmoke.zetaChal

/-- …and the SEARCH: the first additive offset whose challenge hits the prover's target. -/
def tcGrindT : Nat :=
  (((List.range 64).map (· + 1)).find? (fun t =>
     tcChalAt ((tcHon + t) % pN) % GRIND_MOD == 0)).getD 0
def tcGround : Nat := (tcHon + tcGrindT) % pN

-- ⚑⚑ **THE GRIND SUCCEEDS.** The block's real quotient commitment MISSES the chosen target; the
-- prover finds a word that HITS it, by addition, in under 64 tries.
#guard chalOf shapeSmoke tS.sp shapeSmoke.zetaChal % GRIND_MOD != 0
#guard tcGrindT != 0
#guard tcChalAt tcGround % GRIND_MOD == 0
#guard tcGround != tcHon

/-- R1's transcript at the ground word — the assembly's OWN `runSpongeAt`, one word changed. -/
def spTc : SpongeData :=
  runSpongeAt shapeSmoke (stepBases shapeSmoke) indexDigest (cipWordOf tS) tcOrd 1 tcGround

-- ⚑⚑ **AND IT STEERS EVERY SQUEEZE.** One `t_comm` coordinate, chosen by the prover, and EVERY
-- transcript challenge moves — with them the x_hat MSM's scalars, the fold's weights and
-- `combined_inner_product`. That is Fiat–Shamir's INPUT becoming prover-chosen, and it is exactly
-- what absorbing `t_comm` WITHOUT consuming it would have left untouched.
-- ⚠ ⚑ …every squeeze taken AFTER the `t_comm` run, which since the R1 interleaving is ζ onwards and
-- not all of them: β, γ and α are squeezed BEFORE `receive without t_comm` (`:563-566` precede
-- `:567`), so upstream itself does not let a quotient chunk move them. Stated as the exact split
-- rather than as "every challenge", which was true only of the all-absorbs-first shape.
#guard ((List.range shapeSmoke.chals).drop shapeSmoke.zetaChal).all (fun c =>
  chalOf shapeSmoke spTc c != chalOf shapeSmoke tS.sp c)
#guard ((List.range shapeSmoke.chals).take shapeSmoke.zetaChal).all (fun c =>
  chalOf shapeSmoke spTc c == chalOf shapeSmoke tS.sp c)
#guard (spTc.states.getLastD []).getD 0 0 != (tS.sp.states.getLastD []).getD 0 0

-- ⚑ **THE HOLE, ON THE EMITTED OBJECT.** R1 itself never objects: with the ground word absorbed,
-- every sponge block is still exactly `Ref.perm` of its own absorbed state. A `Poseidon` gate
-- constrains the permutation and NOT what was fed to it, so before §6b nothing in the assembly
-- could refuse this.
#guard (List.range shapeSmoke.blocks).all (fun b =>
  let pre := spTc.states.getD b []
  let ms := spTc.msgs.getD b []
  let post := if ms.isEmpty then pre
    else [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
  spTc.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)

/-- `assert_on_curve`'s `assert_square` half as its OWN `Generic` body — `y·y − x³ − b`
(`snarky_curve.ml:212-217`), the third half `onCurveHalves` emits. -/
def tcSqBody (p : Nat × Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    ((([0, 0, -1, 1, -(PALLAS_B : Int)] : List Int) ++ cNil).map (fun c => ((c : Int) : ZMod pN)))
    [(p.2 : ZMod pN), (p.2 : ZMod pN)
    , ((fMul (fMul p.1 p.1) p.1 : Nat) : ZMod pN), 0, 0, 0]

-- ⚑⚑ **AND THE ASSEMBLED VERSION REFUSES IT.** `t_comm` arrives through `Inner_curve.typ` now, so
-- §7b's `assert_on_curve` covers it: the row's own generic-gate body — `KimchiVerify.
-- genericGateConstraint`, read-only — is 0 on the block's real quotient commitment and NONZERO on
-- the ground one. ACCEPTED before §6b (no row read that word at all), REFUSED now.
#guard tcSqBody (ftcTc (tCommN shapeSmoke - 1)) == 0
#guard (tcSqBody ((ftcTc (tCommN shapeSmoke - 1)).1, tcGround) == 0) == false
#guard onCurveA ((ftcTc (tCommN shapeSmoke - 1)).1, tcGround) == false
-- …and the check is SATISFIABLE at every one of the seven chunks, not just the one the grind used.
#guard Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.all onCurveA
#guard (List.range N_TCOMM).all (fun i => tcSqBody (ftcTc i) == 0)
-- ⚑ …and §7b's rows really cover `t_comm`: the on-curve census is the fold's absorbed bases PLUS
-- the quotient chunks, and the last `tCommN` checked variables ARE `t_comm`'s.
#guard (List.range (tCommN shapeSmoke)).all (fun i =>
  onCVar shapeSmoke ((absRoundList shapeSmoke).length + i) == (vTcX shapeSmoke i, vTcY shapeSmoke i))

-- ── §12f — ⚑ R3's LADDER SEED WAS THE PROVER'S (`plonk_curve_ops.ml:157-158`, CLOSED) ──────────
-- §12b pinned R3's BASES to the SRS Lagrange constants and §12c/§12c′ closed the challenge
-- decompositions. Neither says a word about where the ladder STARTS. `scale_fast_unpack` opens with
-- TWO initialisers — `let acc = ref (add_fast base base)` (`:157`) and `let n_acc = ref Field.zero`
-- (`:158`) — and R3 emitted NEITHER, so `pAcc i 0` and `vSN i 0` were witnesses no row read. Both
-- are exhibited below on the assembly's OWN generators: the ladder's gate polynomial ACCEPTS each
-- forgery, and each of the two new rows refuses it.

/-- MSM term 0's base — an SRS Lagrange constant PINNED by `msmBaseRows` (§12b), so the exhibit
cannot be mistaken for "the prover swapped the base". -/
def msmT0 : Nat × Nat := (tS.msm.terms.getD 0 default).T
/-- …the HONEST seed, `add_fast base base` = `[2]T`. -/
def msmSeedHon : Nat × Nat := dblA msmT0
/-- ⚑ **THE PROVER'S SEED**: `[3]T`. On the curve, so `Inner_curve.typ`'s check would not object
either — and ANY point works, which is the whole content of the hole. -/
def msmSeedForged : Nat × Nat := addA msmSeedHon msmT0
/-- Term 0's ladder from an arbitrary seed — `runVbm`, the assembly's OWN generator, at the
assembly's own bits. -/
def msmFrom (seed : Nat × Nat) : TermData := runVbm msmT0 seed (tS.msm.bits.getD 0 [])
def msmForged : TermData := msmFrom msmSeedForged

-- the honest run IS the assembly's term 0, so what follows measures the forgery and not a second
-- copy of the ladder.
#guard (msmFrom msmSeedHon).accs == (tS.msm.terms.getD 0 default).accs
#guard (tS.msm.terms.getD 0 default).accs.getD 0 (0, 0) == msmSeedHon
#guard msmSeedForged != msmSeedHon
#guard onCurveA msmT0 && onCurveA msmSeedHon && onCurveA msmSeedForged
-- ⚑ the COUNTER CHAIN IS UNTOUCHED by a forged seed: the forged ladder's `n` cells are the honest
-- ones, so the σ class that closes `vSN 0 msmChunks` on the challenge variable — the only thing R3
-- constrained about this term — is satisfied by the forgery exactly as by the honest witness.
#guard msmForged.ns == (tS.msm.terms.getD 0 default).ns
-- ⚑⚑ **AND THE OUTPUT IS A DIFFERENT POINT.** `multiscale_known`'s result is `x_hat`: a PUBLIC word
-- (`exposedVars`) and a segment-C absorption. This is the prover choosing what the MSM returned.
#guard msmForged.accs.getLastD (0, 0) != (tS.msm.terms.getD 0 default).accs.getLastD (0, 0)

/-- The 15 CURR and 15 NEXT cells of one `VarBaseMul` chunk, laid out as `msmChunkRows` emits them
(`varbasemul.rs:310-331`): base `(w₀,w₁)`, accumulators `(w₂,w₃) (w₇,w₈) (w₉,w₁₀) (w₁₁,w₁₂)
(w₁₃,w₁₄)` on CURR and `(w'₀,w'₁)` on NEXT, `n = w₄`, `n' = w₅`, bits `w'₂..w'₆`, slopes
`w'₇..w'₁₁`. -/
def vbmChunkCells (td : TermData) (bits : List Nat) (j : Nat) : List Nat × List Nat :=
  let ax : Nat → Nat := fun k => (td.accs.getD k (0, 0)).1
  let ay : Nat → Nat := fun k => (td.accs.getD k (0, 0)).2
  ( [ td.T.1, td.T.2, ax (5*j), ay (5*j), td.ns.getD (5*j) 0, td.ns.getD (5*(j+1)) 0, 0
    , ax (5*j+1), ay (5*j+1), ax (5*j+2), ay (5*j+2)
    , ax (5*j+3), ay (5*j+3), ax (5*j+4), ay (5*j+4) ]
  , [ ax (5*(j+1)), ay (5*(j+1))
    , bits.getD (5*j) 0, bits.getD (5*j+1) 0, bits.getD (5*j+2) 0, bits.getD (5*j+3) 0
    , bits.getD (5*j+4) 0
    , td.slopes.getD (5*j) 0, td.slopes.getD (5*j+1) 0, td.slopes.getD (5*j+2) 0
    , td.slopes.getD (5*j+3) 0, td.slopes.getD (5*j+4) 0, 0, 0, 0 ] )
/-- …answered to `varBaseMulConstraints`, proof-systems' own 21 constraints, read-only. -/
def vbmOk (c : List Nat × List Nat) : Bool :=
  (varBaseMulConstraints (R := ZMod pN) (c.1.map (fun n => (n : ZMod pN)))
      (c.2.map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))

-- the cell helper reproduces the ASSEMBLY's own accepted rows on the honest term…
#guard (List.range shapeSmoke.msmChunks).all (fun j =>
  vbmOk (vbmChunkCells (tS.msm.terms.getD 0 default) (tS.msm.bits.getD 0 []) j))
-- ⚑⚑ **THE HOLE, ON THE EMITTED GATE POLYNOMIAL.** Every `VarBaseMul` row of the FORGED ladder
-- satisfies the same 21 constraints. A curve gate constrains the STEP and not the START, so before
-- this commit there was nothing in R3 that could refuse a chosen `acc₀`.
#guard (List.range shapeSmoke.msmChunks).all (fun j =>
  vbmOk (vbmChunkCells msmForged (tS.msm.bits.getD 0 []) j))

/-- The seed row's eleven `CompleteAdd` cells with the OUTPUT replaced by the point a prover
claims — `msmDblRow`'s own witness, one substitution. -/
def msmDblCellsAt (seed : Nat × Nat) : List Nat :=
  ((completeAddWitness msmT0.1 msmT0.2 msmT0.1 msmT0.2).set 4 seed.1).set 5 seed.2
def caOk (c : List Nat) : Bool :=
  (completeAddConstraints (R := ZMod pN) (c.map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))

-- ⚑⚑ **AND THE ASSEMBLED VERSION REFUSES IT.** The seed row's own gate body is 0 on
-- `add_fast base base` and NONZERO on the prover's point. ACCEPTED this morning — no row read
-- `pAcc i 0` at all — REFUSED now.
#guard caOk (msmDblCellsAt msmSeedHon)
#guard caOk (msmDblCellsAt msmSeedForged) == false
-- …and the check is SATISFIABLE at every term, not just the one the exhibit used.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let T := (tS.msm.terms.getD i default).T
  caOk (completeAddWitness T.1 T.2 T.1 T.2))
-- …and the row is REALLY IN THE SCHEDULE, wired to the ladder's first accumulator cell: `pAcc i 0`
-- now has TWO cells (the seed row's output and chunk 0's `VarBaseMul` input) where it had one.
#guard (classCells posS (mpx shapeSmoke (pAcc shapeSmoke 0 0))).length == 2
#guard (classCells posS (mpy shapeSmoke (pAcc shapeSmoke 0 0))).length == 2
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (classCells posS (mpx shapeSmoke (pAcc shapeSmoke i 0))).length == 2)

-- ── …AND THE SECOND WITNESS OF THE SAME TWO LINES: the counter seed (`:158`) ───────────────────
/-- The counter trace `nₖ₊₁ = 2nₖ + bₖ` (`plonk_curve_ops.ml:170`) from an ARBITRARY seed. -/
def nTraceFrom (n0 : Nat) (bits : List Nat) : List Nat :=
  bits.foldl (fun acc b => acc ++ [(2 * acc.getLastD 0 + b) % pN]) [n0]
/-- ⚑ The honest bits with the MSB flipped — a DIFFERENT multiplier, hence a different ladder
output. -/
def msmBitsForged : List Nat :=
  (tS.msm.bits.getD 0 []).set 0 (1 - (tS.msm.bits.getD 0 []).headD 0)
/-- …and the counter seed that makes the chain still close on the SAME challenge cell:
`n₀ = (n_final − N(bits′))·2^{−5·msmChunks}`, one field inversion. -/
def msmN0Forged : Nat :=
  fMul (fSub ((tS.msm.terms.getD 0 default).ns.getLastD 0)
             ((nTraceFrom 0 msmBitsForged).getLastD 0))
       (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv (2 ^ (5 * shapeSmoke.msmChunks) % pN))

-- the trace helper reproduces the assembly's own counter chain from `n₀ = 0`…
#guard (nTraceFrom 0 (tS.msm.bits.getD 0 [])) == (tS.msm.terms.getD 0 default).ns
-- ⚑⚑ **THE FORGERY: DIFFERENT BITS, THE SAME CHALLENGE CELL.** The chain from the prover's seed
-- closes on exactly the value `vSN 0 msmChunks` is wired to, so `Field.Assert.equal !n_acc scalar`
-- (`:208`) — the wire R3 was relying on — is satisfied by a bit vector the prover chose.
#guard msmBitsForged != tS.msm.bits.getD 0 []
#guard msmN0Forged != 0
#guard (nTraceFrom msmN0Forged msmBitsForged).getLastD 0
        == (tS.msm.terms.getD 0 default).ns.getLastD 0
-- …and the ladder over those bits lands on a DIFFERENT point, which is the same theft as above
-- through the other cell.
#guard (runVbm msmT0 msmSeedHon msmBitsForged).accs.getLastD (0, 0)
        != (tS.msm.terms.getD 0 default).accs.getLastD (0, 0)

/-- `msmNZeroRows`' first row, as its own `Generic` body — half 1 is `w₀ = 0` over `vSN i 0`. -/
def msmNZeroRow0 : SRow := (msmNZeroRows shapeSmoke).headD default
def nZeroBody (v : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    (msmNZeroRow0.coeffs.map (fun c => ((c : Int) : ZMod pN)))
    [(v : ZMod pN), 0, 0, 0, 0, 0]

-- ⚑⚑ **AND `n_acc := ref Field.zero` REFUSES IT.** The pin row's own generic-gate body —
-- `KimchiVerify.genericGateConstraint`, read-only — is 0 at the constant upstream uses and NONZERO
-- at the prover's seed.
#guard msmNZeroRow0.coeffs == cConst 0 ++ cConst 0
#guard nZeroBody 0 == 0
#guard (nZeroBody msmN0Forged == 0) == false
-- …and `vSN i 0` is READ by that row for every term (two cells: the pin and chunk 0's `VarBaseMul`).
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (classCells posS (vSN shapeSmoke i 0)).length == 2)

-- ⚑ **AND THE PIN IS WHAT FORCES THE TWO LEADING PAD BITS**, which is why `:158` is the load-bearing
-- half of the pair rather than tidiness. `chunks_needed ~num_bits:127 = 26` and `26·5 = 130`, so the
-- ladder carries TWO bits more than a challenge has. Nothing pins those two cells directly. The
-- ARGUMENT (an argument about the constraint system, not a machine-checked implication — the three
-- facts it rests on are pinned, the inference is prose): `VarBaseMul`'s own booleanity constraints
-- force every `bₖ ∈ {0,1}`; with `n₀ = 0` the counter chain gives `n_final = Σₖ bₖ·2^{129−k}`; the
-- `EndoMulScalar` chain reconstructs `n_final` from 8 rows × 8 crumbs × 2 bits with ITS OWN `n₀ = 0`
-- pin, so `n_final < 2¹²⁸`; and `2¹³⁰ < p`, so the field equation is an INTEGER one and `b₀ = b₁ = 0`
-- follows. Remove the `n₀` pin and every step of that collapses.
#guard 5 * shapeSmoke.msmChunks == 130
#guard shapeSmoke.chalBits == 128 && shapeStep.chalBits == 128
#guard 2 ^ 130 < pN
#guard shapeSmoke.msmChunks == (127 + 4) / 5
-- …and the endo ladder has NO pad: `4·ipaBlocks = 128` exactly, which is why §12g's leg is only
-- about the seed.
#guard 4 * shapeSmoke.ipaBlocks == shapeSmoke.chalBits
-- ⚑ …and the SAME pin now covers §6b's eight `ft_comm` ladders, which had `:157` and not `:158`:
-- `ftcN k 0` was free, so the closing `Field.Assert.equal !n_acc scalar` against R6's derived `perm`
-- / `ζ^n` cell was one equation in two unknowns and `ft_comm` was choosable the same way.
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (tS.ftc.terms.getD k default).td.ns.headD 1 == 0)
#guard ((ftcNZeroRows shapeSmoke).headD default).coeffs == cConst 0 ++ cConst 0

-- ── §12g — ⚑ R4's SEED, THE THIRD REGION OF THE SAME FAMILY (`scalar_challenge.ml:230-235`) ────
-- `Scalar_challenge.endo` had BOTH free witnesses, and its point seed was also the WRONG POINT.
-- Upstream: `let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in ref G.(p + p)` and
-- `let n_acc = ref Field.zero`. `runIpa` seeded at `dblA T` — `2t`, not `2(t + φ(t))` — with
-- `qAcc r 0` and `vQN r 0` read by NO row. So the fold was self-consistent arithmetic that was not
-- `Scalar_challenge.endo`, over a starting point the prover could name.

-- ⚑ THE SEED IS THE ENDOMORPHISM'S, and it is a different point from what this file used to emit.
#guard Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo != 1
#guard (endoQ (tS.ipa.bases.getD absR0 (0, 0))).1 != (tS.ipa.bases.getD absR0 (0, 0)).1
#guard (endoQ (tS.ipa.bases.getD absR0 (0, 0))).2 == (tS.ipa.bases.getD absR0 (0, 0)).2
#guard endoSeed (tS.ipa.bases.getD absR0 (0, 0)) != dblA (tS.ipa.bases.getD absR0 (0, 0))
-- …and `φ(t)` is on the curve, which is what makes `endo` the base-field endomorphism and not a
-- number: `a = 0` on Pallas, so `(ζx)³ + b = x³ + b` for a cube root of unity.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  onCurveA (endoQ (tS.ipa.bases.getD r (0, 0))) == onCurveA (tS.ipa.bases.getD r (0, 0)))
-- …the seed the assembly RUNS is the emitted rows' own output, round for round.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (tS.ipa.accs.getD r []).getD 0 (0, 0) == endoSeed (tS.ipa.bases.getD r (0, 0)))

-- ⚑⚑ **THE SAME EXHIBIT AS §12f, ON THE ENDO LADDER.** A forged accumulator seed leaves the endo
-- gate's own eleven DEPLOYED constraints satisfied at every block — `endoMulConstraints`, read-only
-- — while the round's output moves. The counter chain is untouched, so the wire to the challenge
-- cell says nothing about it.
def ipaT0 : Nat × Nat := tS.ipa.bases.getD absR0 (0, 0)
def ipaSeedForged : Nat × Nat := addA (endoSeed ipaT0) ipaT0
/-- Round `absR0`'s endo blocks from an ARBITRARY accumulator seed — `endoStep`, the assembly's own
generator, at the assembly's own bits. -/
def ipaBlocksFrom (seed : Nat × Nat) : List EndoBlock :=
  let bits := endoBitsOf shapeSmoke (chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal absR0))
  ((List.range shapeSmoke.ipaBlocks).foldl
    (fun (st : List (Nat × Nat) × List EndoBlock) e =>
      let cur := st.1.getLastD (0, 0)
      let b := endoStep ipaT0.1 ipaT0.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      (st.1 ++ [(b.xs, b.ys)], st.2 ++ [b]))
    ([seed], [])).2
/-- The 15 CURR / 15 NEXT cells of endo block `e`, as `ipaRoundRows` lays them out. -/
def emCells (blks : List EndoBlock) (accs : List (Nat × Nat)) (ns : List Nat) (e : Nat)
    : List Nat × List Nat :=
  let b := blks.getD e default
  let a := accs.getD e (0, 0)
  let a' := accs.getD (e + 1) (0, 0)
  ( [ ipaT0.1, ipaT0.2, b.inv, 0, a.1, a.2, ns.getD e 0
    , b.xr, b.yr, b.s1, b.s3, b.b1, b.b2, b.b3, b.b4 ]
  , [ 0, 0, 0, 0, a'.1, a'.2, ns.getD (e + 1) 0, 0, 0, 0, 0, 0, 0, 0, 0 ] )
def emOk (c : List Nat × List Nat) : Bool :=
  ((endoMulConstraints (R := ZMod pN) (Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo : ZMod pN)
      (c.1.map (fun n => (n : ZMod pN))) (c.2.map (fun n => (n : ZMod pN)))).take 11).all
    (fun z => decide (z = 0))
/-- Block accumulators from an arbitrary seed. -/
def ipaAccsFrom (seed : Nat × Nat) : List (Nat × Nat) :=
  let bits := endoBitsOf shapeSmoke (chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal absR0))
  (List.range shapeSmoke.ipaBlocks).foldl
    (fun (st : List (Nat × Nat)) e =>
      let cur := st.getLastD (0, 0)
      let b := endoStep ipaT0.1 ipaT0.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      st ++ [(b.xs, b.ys)])
    [seed]

-- the helpers reproduce the assembly's OWN accepted rows on the honest seed…
#guard ipaAccsFrom (endoSeed ipaT0) == tS.ipa.accs.getD absR0 []
#guard (List.range shapeSmoke.ipaBlocks).all (fun e =>
  emOk (emCells (ipaBlocksFrom (endoSeed ipaT0)) (ipaAccsFrom (endoSeed ipaT0))
                (tS.ipa.ns.getD absR0 []) e))
-- ⚑⚑ …and the FORGED seed's rows are accepted just the same, with a different round output.
#guard ipaSeedForged != endoSeed ipaT0
#guard (List.range shapeSmoke.ipaBlocks).all (fun e =>
  emOk (emCells (ipaBlocksFrom ipaSeedForged) (ipaAccsFrom ipaSeedForged)
                (tS.ipa.ns.getD absR0 []) e))
#guard (ipaAccsFrom ipaSeedForged).getLastD (0, 0) != (ipaAccsFrom (endoSeed ipaT0)).getLastD (0, 0)

-- ⚑⚑ **AND THE TWO NEW `Ops.add_fast` ROWS REFUSE IT.** `acc₀ = p + p`'s own gate body is 0 at the
-- endomorphism seed and NONZERO at the prover's point.
def ipaDblCellsAt (seed : Nat × Nat) : List Nat :=
  let p := endoP ipaT0
  ((completeAddWitness p.1 p.2 p.1 p.2).set 4 seed.1).set 5 seed.2
#guard caOk (ipaDblCellsAt (endoSeed ipaT0))
#guard caOk (ipaDblCellsAt ipaSeedForged) == false
-- …and it is satisfiable at every round, both `add_fast`s.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  let T := tS.ipa.bases.getD r (0, 0)
  let q := endoQ T
  let p := endoP T
  caOk (completeAddWitness T.1 T.2 q.1 q.2) && caOk (completeAddWitness p.1 p.2 p.1 p.2))
-- ⚑ …and the cells that were in a ONE-cell class are not any more. `qAcc r 0`: the seed add's
-- output and block 0's `EndoMul` input. `vQN r 0`: the `Field.zero` pin and block 0's `n`.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (classCells posS (ipx shapeSmoke (qAcc shapeSmoke r 0))).length == 2
  && (classCells posS (ipy shapeSmoke (qAcc shapeSmoke r 0))).length == 2
  && (classCells posS (vQN shapeSmoke r 0)).length == 2)
-- …and `φ(t)`'s x is read by its pin row and by the `p = t + φ(t)` add, nowhere else.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (classCells posS (vQEndo shapeSmoke r)).length == 2)
-- ⚑ …so ALL THREE ladder regions now start where upstream starts them: R3's `multiscale_known`
-- (§12f), §6b's `ft_comm` (`:157` from the start, `:158` here) and R4's `Scalar_challenge.endo`.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (classCells posS (vSN shapeSmoke i 0)).length == 2)
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (classCells posS (ftcN shapeSmoke k 0)).length == 2)
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (classCells posS (vQN shapeSmoke r 0)).length == 2)

/-! ## §13 — R6: the COMPILED `ft_eval0` against dregg's own verified value layer.

The compiler of §8b is a compiler, not an oracle: every value it produces is pinned here against the
READ-ONLY `KimchiVerify` body it claims to compute, on the SAME inputs, and each pin carries a red
control that bites. The 67 gate constraints are compared **list by list**, so a slip in one body of
one gate cannot be absorbed by the sum. -/

/-- The ft program's slot values at the smoke instance. -/
def ftS : FtData := tS.ft
def ftVal (i : Nat) : Nat := ftS.vals.getD i 0
/-- The ft program's inputs, resolved the way the program resolves them. -/
def ftLkS : PVar → Int := envLookupAt (envIndex (ftInputEnv shapeSmoke tS.sp))
def ftInp (v : PVar) : Nat := (ftLkS v).toNat % pN
def zetaS : Nat := ftInp (vLift shapeSmoke shapeSmoke.zetaChal)
def alphaS : Nat := ftInp (vLift shapeSmoke shapeSmoke.alphaChal)
def betaS : Nat := ftInp (vN shapeSmoke shapeSmoke.betaChal shapeSmoke.emsRows)
def gammaS : Nat := ftInp (vN shapeSmoke shapeSmoke.gammaChal shapeSmoke.emsRows)
/-- The 43 columns, as the `GateEvals` slicing sees them. -/
def colZ (k : Nat) : ZMod pN := ((evZOf ftS.out (EV_PREFIX + k) : Nat) : ZMod pN)
def colW (k : Nat) : ZMod pN := ((evVal (EV_PREFIX + k) 1 : Nat) : ZMod pN)
def wZ : List (ZMod pN) := (List.range 15).map (fun i => colZ (IDX_W + i))
def wW : List (ZMod pN) := (List.range 15).map (fun i => colW (IDX_W + i))
def coeffZ : List (ZMod pN) := (List.range 15).map (fun i => colZ (IDX_COEFF + i))
def sZ : List (ZMod pN) := (List.range 6).map (fun i => colZ (IDX_S + i))
def mdsS3 : List (List (ZMod pN)) :=
  (List.range 3).map (fun j => (List.range 3).map (fun i => ((FT_MDS9.getD (3 * j + i) 0 : Nat) : ZMod pN)))

/-- The `GateEvals` the linearization constant term is evaluated against — assembled from the SAME
column variables the circuit reads. -/
def gS : Dregg2.Circuit.Emit.KimchiVerify.GateEvals (ZMod pN) :=
  { alpha := (alphaS : ZMod pN), endo := ((FT_ENDO : Nat) : ZMod pN), mds := mdsS3
    coeff := coeffZ, w := wZ, wNext := wW
    cA := ((FT_QUOT.1 : Nat) : ZMod pN), cB := ((FT_QUOT.2.1 : Nat) : ZMod pN)
    cC := ((FT_QUOT.2.2 : Nat) : ZMod pN)
    genSel := colZ (IDX_SEL + 0), posSel := colZ (IDX_SEL + 1)
    caddSel := colZ (IDX_SEL + 2), mulSel := colZ (IDX_SEL + 3)
    emulSel := colZ (IDX_SEL + 4), emulScalarSel := colZ (IDX_SEL + 5) }

-- ⚑ THE CONFIG IS REAL, not decorative. ω is a primitive `2^16`-th root of unity (so `ω^{n−1}` IS
-- the witnessed inverse the circuit derives), the three `EndomulScalar` quotients are the genuine
-- ones, and the endo coefficient is a cube root of unity distinct from 1.
#guard Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) FT_N == (1 : ZMod pN)
#guard Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N / 2) != (1 : ZMod pN)
#guard fMul FT_OMEGA FT_OMEGA_INV == 1
#guard Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstsOk
        ((FT_QUOT.1 : Nat) : ZMod pN) ((FT_QUOT.2.1 : Nat) : ZMod pN)
        ((FT_QUOT.2.2 : Nat) : ZMod pN)
#guard ((FT_ENDO : Nat) : ZMod pN) ^ 3 == (1 : ZMod pN)
#guard ((FT_ENDO : Nat) : ZMod pN) != (1 : ZMod pN)
#guard FT_MDS9.length == 9

-- ⚑⚑ **THE SEVEN COSET SHIFTS ARE THE DERIVED TICK SHIFTS** (simplification #8, retired). The rung
-- runs `TickShifts.tickShiftsFp 16` — the `Shifts::new` Blake2b→field construction — and that list
-- is pinned BYTE-EXACT there against o1-labs' own `Shifts::new(Radix2EvaluationDomain::<Fp>::new
-- (2^16))` output (`tick_shifts_export`, a path that runs kimchi and touches no Lean). Restated
-- here so a swap back to a fixture is a red in THIS file, at the point of use.
#guard FT_SHIFTS == Dregg2.Bridge.TickShifts.TICK_SHIFTS_16_ORACLE
#guard FT_SHIFTS.length == 7
-- …the first shift is the identity coset (`shifts[0] = 1`, `permutation.rs:158`), the rest are not,
-- and all seven are distinct — the structure `Shifts::new` guarantees and a fixture cannot fake.
#guard FT_SHIFTS.headD 0 == 1
#guard (FT_SHIFTS.drop 1).all (fun x => x != 1 && x != 0)
#guard FT_SHIFTS.dedup.length == 7
-- …and the derivation really is a derivation: the six sampled shifts are quadratic NON-residues of
-- `Fp` outside the `2^16` domain, which is `Shifts::sample`'s own acceptance predicate.
#guard (FT_SHIFTS.drop 1).all (fun x =>
  Dregg2.Bridge.TickShifts.accept FT_N [] ((x : Nat) : ZMod pN))
-- ⚑ …and they are NOT the placeholders the rung used before (the red control lives in §13's
-- `ft_eval0` pins below, where the fixtures give a different value).
#guard (List.range 7).all (fun i => FT_SHIFTS.getD i 0 != FT_SHIFTS_WERE_FIXTURES.getD i 0)
-- ⚑ ALL SIX GATE SELECTORS FIRE. Without this every body but `generic` is multiplied by zero and
-- the six transcriptions rest on a source reading — the exact hazard `MinaWrapFtEval0Weld` §1b
-- named when it found the first fixture with a nonzero `emulSel`.
#guard (List.range 6).all (fun i => colZ (IDX_SEL + i) != 0)

-- ⚑ ω^{n−1}, ω^{n−2}, ω^{n−3} ARE the circuit's derived inverse powers — the reason the rung spends
-- ONE witnessed inverse instead of a 48-row exponentiation, and the reason `zkPoly` is exact.
#guard ((FT_OMEGA_INV : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 1)
#guard ((ftVal ftS.fp.slots.omInv3 : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 3)
-- …and `ζ^n` really is the `log2n`-fold squaring, and `zkPoly` the shipped one.
#guard ((ftVal ftS.fp.slots.zetaN : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((zetaS : Nat) : ZMod pN) FT_N
#guard ((ftVal ftS.fp.slots.zkp : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.zkPolyR FT_N
             ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)

-- ⚑ **THE LINEARIZATION CONSTANT TERM.** The compiled six-body sum IS `KimchiVerify.gateLinConst`
-- of the same `GateEvals` — the value `MinaWrapFtEval0Weld` reproduces byte-for-byte on devnet
-- block 539508's Step side (`lct_true = 20345…173047`) and on its Wrap side (`LCT`).
#guard ((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS
-- …and IT BITES: bend ONE input — the `endomul` selector — and the constant term moves.
#guard (((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst
              { gS with emulSel := gS.emulSel + 1 }) == false
-- …and the endo really is load-bearing (the `endoMulConstraints` reader; the cube-root conflation
-- `MinaWrapFtEval0Weld` closed would show HERE).
#guard (((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst
              { gS with endo := gS.endo + 1 }) == false

-- ⚑ **`ft_eval0`.** The compiled fold IS `KimchiVerify.ftEval0R` — the CommRing mirror that is the
-- shipped `ftEval0` for every field (`ftEval0R_eq`, `rfl`) — at the SAME domain, challenges,
-- columns, shifts and constant term, with the witnessed inverse the circuit checks.
#guard
  ((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))
-- ⚑ …and the pin BITES at every leg that could silently drift. β for γ:
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((gammaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- ⚑ …a bent DERIVED coset shift (the leg `MinaWrapFtEval0Weld` §6b exhibits on the real block):
-- bend one of `tickShiftsFp 16`'s own outputs by one and `ft_eval0` moves.
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ ((FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN))).set 1
                  (((FT_SHIFTS.getD 1 0 : Nat) : ZMod pN) + 1))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- ⚑⚑ **DERIVED, NOT FIXED — the red control for simplification #8.** The seven placeholders the
-- rung ran until 2026-08-02 give a DIFFERENT `ft_eval0` at the same wire. So the value the circuit's
-- `Generic` rows compute is the one Mina's own `Shifts::new` cosets produce, and swapping the
-- derivation back out is a red rather than a silence.
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS_WERE_FIXTURES.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- …and a constant term off by one (so the `gateLinConst` leg is not decoration inside the fold):
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS + 1)
         (((ftS.denomInv : Nat) : ZMod pN))) == false

-- ⚑ THE WITNESSED INVERSE IS THE GENUINE ONE — and the circuit checks it, so a prover who supplies
-- another value is refused by the `denom·denomInv = 1` row rather than believed.
#guard (((zetaS : Nat) : ZMod pN)
          - Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 3))
        * (((zetaS : Nat) : ZMod pN) - 1) * ((ftS.denomInv : Nat) : ZMod pN) == (1 : ZMod pN)

-- ⚑ `Plonk_checks.checked` — `derive_plonk`'s `perm` scalar, compiled, against a direct fold of the
-- same six σ evaluations. `checked` asserts exactly this equality against the deferred word, and the
-- rung emits that assertion as a row.
#guard
  ((ftVal ftS.fp.slots.perm : Nat) : ZMod pN)
    == -((List.range 6).foldl
           (fun acc i => acc * (((gammaS : Nat) : ZMod pN)
             + ((betaS : Nat) : ZMod pN) * sZ.getD i 0 + wZ.getD i 0))
           (colW IDX_Z * ((betaS : Nat) : ZMod pN) * (((alphaS : Nat) : ZMod pN) ^ 21)
             * ((ftVal ftS.fp.slots.zkp : Nat) : ZMod pN)))
#guard (((ftVal ftS.fp.slots.perm : Nat) : ZMod pN) == 0) == false

-- ⚑ THE OUTPUT IS WIRED INTO R5's `combined_inner_product`: `ft_eval0` IS the `ft` column the C8
-- fold consumes (`combine ~ft:ft_eval0`, `step_verifier.ml:1078-1083`), so the two rungs share a
-- variable rather than agreeing by construction in Lean only.
#guard tS.df.ez.getD 3 0 == ftS.out
#guard evZOf ftS.out 3 == ftS.out
#guard evZOf ftS.out 3 != evVal 3 0

/-! ### §13a — the SIXTY-SEVEN CONSTRAINT BODIES, list by list.

The pins above check the SUM. These check each compiled body against the `KimchiVerify` list it
mirrors, elementwise, so a compensating pair of slips cannot pass. Each of the six is run through
`aEval` a second time in isolation (the same `ftLkS`), which is why the slot indices below are the
ones the isolated program returns. -/

/-- Compile one body in isolation and read its constraint slots' values. -/
def bodyVals (b : AM (List Nat)) : List (ZMod pN) :=
  let r := b.run #[]
  let vs := aEval ftLkS r.2
  r.1.map (fun i => ((vs.getD i 0 : Nat) : ZMod pN))

/-- The slots every body shares, emitted once at the head of an isolated program. -/
structure WireSlots where
  one : Nat
  negOne : Nat
  three : Nat
  six : Nat
  eleven : Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  mdsS : List (List Nat)
  coeff : List Nat
  w : List Nat
  wNext : List Nat
  deriving Inhabited

def wireSlots (endoV : Nat) : AM WireSlots := do
  let one ← eLit 1
  let negOne ← eLit (pN - 1)
  let three ← eLit 3
  let six ← eLit 6
  let eleven ← eLit 11
  let endo ← eLit endoV
  let cA ← eLit FT_QUOT.1
  let cB ← eLit FT_QUOT.2.1
  let cC ← eLit FT_QUOT.2.2
  let mdsS ← (List.range 3).foldlM (fun acc j => do
      let row ← (List.range 3).foldlM
        (fun r i => do let v ← eLit (FT_MDS9.getD (3 * j + i) 0); pure (r ++ [v])) []
      pure (acc ++ [row])) []
  let ez ← (List.range 43).foldlM
    (fun acc i => do let v ← eInp (vColZ shapeSmoke i); pure (acc ++ [v])) []
  let ew ← (List.range 43).foldlM
    (fun acc i => do let v ← eInp (vColW shapeSmoke i); pure (acc ++ [v])) []
  pure { one, negOne, three, six, eleven, endo, cA, cB, cC, mdsS
       , coeff := (List.range 15).map (fun i => ez.getD (IDX_COEFF + i) 0)
       , w := (List.range 15).map (fun i => ez.getD (IDX_W + i) 0)
       , wNext := (List.range 15).map (fun i => ew.getD (IDX_W + i) 0) }

def bodyCompleteAdd : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pCompleteAdd q.one q.w
def bodyVarBaseMul : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pVarBaseMul q.one q.w q.wNext
def bodyEndoMul (endoV : Nat) : AM (List Nat) := do
  let q ← wireSlots endoV; pEndoMul q.one q.endo q.w q.wNext
def bodyEmScalar : AM (List Nat) := do
  let q ← wireSlots FT_ENDO
  pEmScalar q.cA q.cB q.cC q.negOne q.three q.six q.eleven q.w
def bodyPoseidon : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pPoseidon q.mdsS q.coeff q.w q.wNext

#guard bodyVals bodyCompleteAdd
        == Dregg2.Circuit.Emit.KimchiVerify.completeAddConstraints wZ
#guard bodyVals bodyVarBaseMul
        == Dregg2.Circuit.Emit.KimchiVerify.varBaseMulConstraints wZ wW
#guard bodyVals (bodyEndoMul FT_ENDO)
        == (Dregg2.Circuit.Emit.KimchiVerify.endoMulConstraints
              ((FT_ENDO : Nat) : ZMod pN) wZ wW).take 11
#guard bodyVals bodyEmScalar
        == Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstraints
             ((FT_QUOT.1 : Nat) : ZMod pN) ((FT_QUOT.2.1 : Nat) : ZMod pN)
             ((FT_QUOT.2.2 : Nat) : ZMod pN) wZ
#guard bodyVals bodyPoseidon
        == Dregg2.Circuit.Emit.KimchiVerify.poseidonConstraints mdsS3 coeffZ wZ wW
-- …and the list-by-list pins BITE: a bent `endo` moves the `EndosclMul` list.
#guard (bodyVals (bodyEndoMul (FT_ENDO + 1))
         == (Dregg2.Circuit.Emit.KimchiVerify.endoMulConstraints
               ((FT_ENDO : Nat) : ZMod pN) wZ wW).take 11) == false
-- …and none of the five lists is all-zero (a body that vanished would match a wrong transcription).
#guard (Dregg2.Circuit.Emit.KimchiVerify.varBaseMulConstraints wZ wW).any (fun z => z != 0)
#guard (Dregg2.Circuit.Emit.KimchiVerify.poseidonConstraints mdsS3 coeffZ wZ wW).any (fun z => z != 0)

/-! ## §14 — R7: the EVALUATION ABSORPTION.

The three segments' arithmetic, against `PastaPoseidon.Ref.perm` — the same reference whose
`Ref.hash` reproduces the o1js `Poseidon.hash` gold KATs, and the same one R1's sponge answers to. -/

#guard tS.specB.ws.length == 4 + 2 * (shapeSmoke.cipEvals - EV_PREFIX)
#guard tS.specB.ws.length == 90
#guard tS.specA.ws.length == 2 * shapeSmoke.bRounds
#guard tS.specC.ws.length == shapeSmoke.hmWords
#guard tS.specA.nb == nbA shapeSmoke
#guard tS.specB.nb == nbB shapeSmoke
#guard tS.specC.nb == nbC shapeSmoke

-- ⚑ EVERY SEGMENT IS THE REAL SPONGE: each block's output is `Ref.perm` of its absorbed input,
-- EXCEPT where the opt-sponge MASK discards it — and that exception is exactly the masked blocks.
#guard (List.range tS.specB.blocks).all (fun b =>
  let pre := tS.segB.states.getD b []
  let post := if b < tS.specB.nb then
      [ fAdd (pre.getD 0 0) ((tS.specB.ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((tS.specB.ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  tS.segB.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- ⚑ Segment C is masked FROM BLOCK `N_HM_FIX/2` ON, so its own statement carries the exception:
-- a kept block is `Ref.perm` of the absorbed state, a dropped one is the state UNCHANGED. Both
-- legs occur (`MASK_BITS = [0,1]`), so neither half of the disjunction is idle.
#guard (List.range tS.specC.blocks).all (fun b =>
  let pre := tS.segC.states.getD b []
  let post := if b < tS.specC.nb then
      [ fAdd (pre.getD 0 0) ((tS.specC.ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((tS.specC.ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  if b < tS.specC.nb && tS.specC.maskedAt b && tS.specC.keepBit b == 0 then
    tS.segC.states.getD (b + 1) [] == pre
  else tS.segC.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- …and BOTH legs really occur in segment C (a mask that dropped nothing would satisfy the above
-- with the `pre` branch dead).
#guard ((List.range tS.specC.nb).filter
          (fun b => tS.specC.maskedAt b && tS.specC.keepBit b == 0)).length > 0
#guard ((List.range tS.specC.nb).filter
          (fun b => tS.specC.maskedAt b && tS.specC.keepBit b == 1)).length > 0
#guard ((List.range tS.specC.nb).filter (fun b => !tS.specC.maskedAt b)).length == N_HM_FIX / 2

-- ⚑ THE MASK IS A MASK, BOTH WAYS. A `keep = 1` block advances to the permutation output; a
-- `keep = 0` block leaves the state EXACTLY where it was — `Field.if_` on all three lanes
-- (`step_verifier.ml:998-1003`). Both branches occur, so neither is untested.
#guard (List.range tS.specA.nb).all (fun b =>
  if tS.specA.keepBit b == 1
  then tS.segA.states.getD (b + 1) [] == tS.segA.afters.getD b []
  else tS.segA.states.getD (b + 1) [] == tS.segA.states.getD b [])
#guard (List.range tS.specA.nb).any (fun b => tS.specA.keepBit b == 1)
#guard (List.range tS.specA.nb).any (fun b => tS.specA.keepBit b == 0)
-- …and a masked-out block's DISCARDED permutation output is genuinely different from the state it
-- keeps, so the mux is deciding something.
#guard (List.range tS.specA.nb).all (fun b =>
  tS.specA.keepBit b == 1 || tS.segA.afters.getD b [] != tS.segA.states.getD b [])

-- ── §14a — ⚑ THE MASK COMES FROM `branch_data` (simplification #9, retired) ────────────────────
-- Every block's `keep` is one of TWO variables, and those two are the `proofs_verified_mask` bits
-- `Checked.pack` ties to the `branch_data` statement word. Not a schedule constant: the pattern
-- `optProofOf` decides is only WHICH bit a block reads, and the bits themselves are circuit
-- variables a public word pins.
#guard (List.range tS.specA.nb).all (fun b =>
  tS.specA.keepVar b == vMask shapeSmoke (optProofOf shapeSmoke b))
#guard (List.range tS.specA.nb).all (fun b =>
  tS.specA.keepVar b == vMask shapeSmoke 0 || tS.specA.keepVar b == vMask shapeSmoke 1)
-- ⚑ `Prefix_mask.there N1 = [false; true]`: the SET bit is a SUFFIX, so with one previous proof the
-- FIRST slot is dropped and the SECOND is kept. (The pattern this rung ran until 2026-08-02 kept the
-- first half — the opposite, and it was a constant.)
#guard MASK_BITS == [0, 1]
#guard tS.specA.keepBit 0 == 0 && tS.specA.keepBit (tS.specA.nb - 1) == 1
-- ⚑ `Checked.pack {mask; domain_log2} = 4·domain_log2 + pack(mask)` (`branch_data.ml:95-101`) —
-- the identity §8h's second `Generic` row emits, and the value the public word carries.
#guard branchPacked == 4 * BRANCH_DOMAIN_LOG2 + MASK_BITS.getD 0 0 + 2 * MASK_BITS.getD 1 0
#guard branchPacked == 66
-- …the bits are Boolean (the row `m² = m` is what enforces it in-circuit), and `domain_log2` is the
-- Step domain the rest of the rung runs at.
#guard MASK_BITS.all (fun m => m * m == m)
#guard BRANCH_DOMAIN_LOG2 == FT_LOG2N
-- ⚑ …and the mask VARIABLES really are wired: each reaches its §8h rows AND the opt-sponge mux rows
-- it gates, and `branch_data` reaches §8h's pack row and the closing public tie.
-- Exact: each mask bit is read by its booleanity row (3 cells), `Checked.pack` (1), its probe (1),
-- and the THREE `Field.if_` lane-mux rows of every masked block that reads it — in segment A AND,
-- since the segment-C retirement, in `hash_messages_for_next_step_proof` too.
def maskReaders (i : Nat) : Nat :=
  ((List.range (nbA shapeSmoke)).filter (fun b => optProofOf shapeSmoke b == i)).length
  + ((List.range tS.specC.nb).filter
       (fun b => tS.specC.maskedAt b && (hmKeepAt shapeSmoke MASK_BITS b).1 == vMask shapeSmoke i)
     ).length
#guard (List.range 2).all (fun i =>
  (classCells posS (vMask shapeSmoke i)).length == 5 + 3 * maskReaders i)
-- ⚑ …and segment C really is a SECOND consumer: each bit now has strictly more readers than
-- segment A alone gives it. (The count `11` this pin carried before the retirement was segment A's
-- alone; naming the delta is what makes the pin bite rather than track.)
#guard (List.range 2).all (fun i =>
  maskReaders i > ((List.range (nbA shapeSmoke)).filter
                     (fun b => optProofOf shapeSmoke b == i)).length)
-- 2 opt-sponge blocks + 3 segment-C blocks (one commitment, `bRounds/2` challenge blocks) each.
#guard maskReaders 0 == 2 + 3 && maskReaders 1 == 2 + 3
#guard (classCells posS (vMask shapeSmoke 0)).length == 20
#guard (classCells posS (vMask shapeSmoke 1)).length == 20
-- …and `branch_data` is read by EXACTLY three rows: the pack row, the closing public tie, its probe.
#guard (classCells posS (vBranch shapeSmoke)).length == 3
#guard (exposedVars shapeSmoke).getD 5 (xv 0) == vBranch shapeSmoke

-- ⚑⚑ **THE BITING RED CONTROL FOR #9.** Re-run segment A at the OTHER two legal prefix masks. `N2`
-- ([tt;tt], both previous proofs real) and `N0` ([ff;ff], none) each give a DIFFERENT opt-sponge
-- digest — so the mask is deciding the value, and `branch_data` is what decides the mask. And the
-- digest is segment B's FIRST absorbed word, so a different `branch_data` moves the fr-sponge, its
-- two squeezes, §8g's ξ and r, and `combined_inner_product` with them.
def segAWith (bits : List Nat) : SegData :=
  runSeg { tS.specA with keep := fun b => (xv 0, bits.getD (optProofOf shapeSmoke b) 0) }
def segADigest (bits : List Nat) : Nat := ((segAWith bits).states.getLastD []).getD 0 0
#guard segADigest MASK_BITS == (tS.segA.states.getLastD []).getD 0 0
#guard segADigest [1, 1] != segADigest MASK_BITS
#guard segADigest [0, 0] != segADigest MASK_BITS
#guard segADigest [1, 1] != segADigest [0, 0]
-- …and the digest IS what segment B absorbs first, so the cascade above is a wire and not a story.
#guard (tS.specB.ws.getD 0 (xv 0, 0)).2 == segADigest MASK_BITS

-- ⚑⚑ **THE BITING RED CONTROL FOR SEGMENT C's MASK.** `hash_messages_for_next_step_proof` was the
-- SECOND consumer of `proofs_verified_mask` and this segment absorbed its carried challenges
-- UNMASKED until 2026-08-02 — the residue #9's retirement made visible. It now reads the same two
-- `branch_data` bits, and the three legal prefix masks give three DIFFERENT digests.
def segCWith (bits : List Nat) : SegData :=
  runSeg { tS.specC with keep := fun b => (xv 0, (hmKeepAt shapeSmoke bits b).2) }
def segCDigest (bits : List Nat) : Nat := ((segCWith bits).states.getLastD []).getD 0 0
#guard segCDigest MASK_BITS == (tS.segC.states.getLastD []).getD 0 0
#guard segCDigest [1, 1] != segCDigest MASK_BITS
#guard segCDigest [0, 0] != segCDigest MASK_BITS
#guard segCDigest [1, 1] != segCDigest [0, 0]
-- ⚑ …and MASKED IS NOT UNMASKED: `[1,1]` IS the unmasked absorption (every block kept), so the pin
-- above says exactly "the old segment C computed a different hash". Named separately because that
-- is the retirement, not a by-product of it.
#guard segCDigest [1, 1] != (tS.segC.states.getLastD []).getD 0 0
-- ⚑ …and the mask is applied to the RIGHT WORDS: the `Not_opt` prefix is unconditional, the four
-- commitment coordinates take one bit per previous proof, the challenge words `bRounds` at a time.
#guard (List.range tS.specC.nb).all (fun b =>
  tS.specC.maskedAt b == decide (N_HM_FIX ≤ 2 * b))
#guard tS.specC.maskFrom == N_HM_FIX / 2
#guard (hmKeepAt shapeSmoke MASK_BITS (N_HM_FIX / 2)).1 == vMask shapeSmoke 0
#guard (hmKeepAt shapeSmoke MASK_BITS (N_HM_FIX / 2 + 1)).1 == vMask shapeSmoke 1
#guard (hmKeepAt shapeSmoke MASK_BITS (N_HM_FIX / 2 + 2)).1 == vMask shapeSmoke 0
#guard (hmKeepAt shapeSmoke MASK_BITS (tS.specC.nb - 1)).1 == vMask shapeSmoke 1
-- …the `Opt` region starts on a BLOCK boundary, which is the whole reason the prefix is even.
#guard N_HM_FIX % 2 == 0
-- ⚑ …and the digest is a PUBLIC WORD, so the mask reaches the verifier's own vector rather than
-- dying inside R7. (`vSt`-style inertness is what `placeChecked` would have caught; this is the
-- stronger statement that it is READ OUT.)
#guard (exposedVars shapeSmoke).getD 6 (xv 0) == hmDigestVar shapeSmoke
#guard (stepPublic tS).getD 6 0 == ((tS.segC.states.getLastD []).getD 0 0 : Int)

-- ⚑ SEGMENT B ABSORBS R5's AND R6's OWN VARIABLES: the digest of segment A, `ft_eval1`, the two
-- public-polynomial evaluations, then the 43 columns at ζ and ζω INTERLEAVED
-- (`to_absorption_sequence`, `step_verifier.ml:967-1005`) — the same `vEz`/`vEw` the C8 fold and the
-- `ft_eval0` rung read. Not a private stream.
#guard (tS.specB.ws.getD 0 (xv 0, 0)).1
        == sgSt (baseSegA shapeSmoke) (nbA shapeSmoke) 1 tS.specA.blocks 0
#guard (tS.specB.ws.getD 0 (xv 0, 0)).2 == (tS.segA.states.getLastD []).getD 0 0
#guard (tS.specB.ws.getD 1 (xv 0, 0)).1 == vEw shapeSmoke 3
#guard (List.range shapeSmoke.frCols).all (fun k =>
  (tS.specB.ws.getD (4 + 2 * k) (xv 0, 0)).1 == vColZ shapeSmoke k
  && (tS.specB.ws.getD (5 + 2 * k) (xv 0, 0)).1 == vColW shapeSmoke k)
-- ⚑ …and segments A and C absorb `prev_challenges` — THE SAME VARIABLES, which is upstream's own
-- shape (`step_verifier.ml:956` and `step_main.ml:80` read one vector) and NOT R2's challenges. That
-- false wire is what made `combined_inner_product` a cycle; see `vPrevChal` for what it cost and what
-- it bought. Segment C also absorbs R3's and R4's fold outputs.
#guard (List.range tS.specA.ws.length).all (fun i =>
  (tS.specA.ws.getD i (xv 0, 0)).1 == vPrevChal shapeSmoke i)
#guard (List.range (2 * shapeSmoke.bRounds)).all (fun i =>
  (tS.specC.ws.getD (N_HM_FIX + 4 + i) (xv 0, 0)) == (tS.specA.ws.getD i (xv 0, 0)))
-- …and NO segment absorbs a transcript challenge variable any more.
#guard (tS.specA.ws.map (·.1)).all (fun v =>
  ((List.range shapeSmoke.chals).any (fun c => v == vN shapeSmoke c shapeSmoke.emsRows)) == false)
#guard (tS.specC.ws.getD N_HM_FIX (xv 0, 0)).1
        == mpx shapeSmoke (pSum shapeSmoke (shapeSmoke.msmTerms - 2))
#guard (tS.specC.ws.getD (N_HM_FIX + 2) (xv 0, 0)).1
        == ipx shapeSmoke (qSum shapeSmoke (shapeSmoke.ipaRounds - 1))

-- ⚑ THE SPONGE IS NOT DEGENERATE: the three digests differ from each other and from zero, so a
-- sponge that silently absorbed nothing would show.
#guard (tS.segA.states.getLastD []).getD 0 0 != 0
#guard (tS.segB.states.getLastD []).getD 0 0 != 0
#guard (tS.segC.states.getLastD []).getD 0 0 != 0
#guard (tS.segA.states.getLastD []).getD 0 0 != (tS.segB.states.getLastD []).getD 0 0
#guard (tS.segB.states.getLastD []).getD 0 0 != (tS.segC.states.getLastD []).getD 0 0

/-! ## §15 — the LADDER is monotone, REACHED BY THE EMITTER, and each rung really adds its
sub-circuit.

⚑ THE REACHED-BY-THE-EMITTER PINS ARE THE FIRST BLOCK, and they exist because of a measured defect:
`cipRows` once lived in a function `rungRows` never called, so `r5_full` was proved seven times
without the `combined_inner_product` chain its own commit subject named, and `vCa cipEvals` reached
the public tie as a FREE variable — while every σ probe, every control and every public-input leg
passed. A length identity per rung, stated as the SUM OF ITS OWN SUB-LISTS, is what turns that from
a silence into a red; `stepRows == rungRows .finalize` closes the same hole on the other emitter. -/

-- Each rung IS the rung below plus exactly its own sub-circuit's rows.
#guard (rungRows tS .challenges true).length
        == (rungRows tS .transcript true).length + (endoConstRow shapeSmoke).length
           + ((List.range shapeSmoke.chals).flatMap (challengeRows shapeSmoke tS.sp true)).length
#guard (rungRows tS .msm true).length
        == (rungRows tS .challenges true).length + (msmRows shapeSmoke tS.msm true).length
           + (ftcRows shapeSmoke tS.ftw tS.ftc true).length
#guard (rungRows tS .ipa true).length
        == (rungRows tS .msm true).length + (ipaRows shapeSmoke tS.ipa true).length
#guard (rungRows tS .full true).length
        == (rungRows tS .ipa true).length + (deferredRows shapeSmoke true).length
           + (branchRows shapeSmoke true).length + (xiDefRows shapeSmoke tS.defc true).length
           + (cipRows shapeSmoke true).length + (closingRows shapeSmoke).length
#guard (rungRows tS .ftEval0 true).length
        == (rungRows tS .full true).length + (ftRows shapeSmoke tS.ft true).length
#guard (rungRows tS .absorb true).length
        == (rungRows tS .ftEval0 true).length + (absRows tS true).length
#guard (rungRows tS .finalize true).length
        == (rungRows tS .absorb true).length + (finRows shapeSmoke tS.ft tS.fin true).length
-- …and the OTHER emitter (`stepRows`, the schedule) is the top rung, row for row.
#guard (stepRows tS true).map (fun r => r.kind) == (rungRows tS .finalize true).map (fun r => r.kind)
#guard (stepRows tS true).length == (rungRows tS .finalize true).length
-- …and each sub-list is NON-EMPTY, so "the sum matches" cannot be satisfied by a vanished rung.
#guard (cipRows shapeSmoke true).length > 0 && (deferredRows shapeSmoke true).length > 0
#guard (ftRows shapeSmoke tS.ft true).length > 0 && (absRows tS true).length > 0
#guard (finRows shapeSmoke tS.ft tS.fin true).length > 0 && (endoConstRow shapeSmoke).length > 0
#guard (xiDefRows shapeSmoke tS.defc true).length > 0
        && (rDefRows shapeSmoke tS.defc true).length > 0
-- ⚑ …and R7's own sub-list really is the three segments, §3c's index pins and digest permutation,
-- and §8g's `r` chain. Stated as an equality over every summand, so a dropped sub-list reds here.
#guard (absRows tS true).length
        == (segRows (baseSegA shapeSmoke) tS.specA tS.segA true).length
           + (segRows (baseSegB shapeSmoke) tS.specB tS.segB true).length
           + (idxConstRows shapeSmoke).length
           + (segRows (baseSegC shapeSmoke) tS.specC tS.segC true).length
           + (idxDigestRows shapeSmoke true).length
           + (rDefRows shapeSmoke tS.defc true).length
-- …and neither §3c sub-list is empty: 12 rows of permutation + a probe, and one `Generic` pin per
-- index commitment this shape must hold itself.
#guard (idxDigestRows shapeSmoke true).length == 13
#guard (idxConstRows shapeSmoke).length == (idxOwn shapeSmoke).length

-- ⚑ **WHICH RUNG BINDS WHICH MULTIPLIER** (#10's honest residue, machine-checked). ξ's chain rides
-- with R5 because its source is a STATEMENT word, so `vDLift 0` has a computing row from `r5_full`
-- up. `r`'s source is the fr-sponge's second squeeze, an R7 variable, so `vDLift 1` has NO computing
-- row below `r7_absorption` and has one at and above it. Stated as a pin so the ladder position is
-- a fact rather than a sentence in a header.
def posAt (k : Rung) : List (PVar × Cell) :=
  circuitPositions (rungPub shapeSmoke k) (stepGates (rungRows tS k true))
-- ⚑ THE SEGMENT-C DIGEST's LADDER POSITION, stated the same way. It is a public word from `r5_full`
-- up, but the rows that COMPUTE it are R7's, so below `r7_absorption` its class is the closing tie
-- and nothing else — a free witness, exactly as `vDLift 1` is. Equalities, not floors.
#guard (classCells (posAt .full) (hmDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .ftEval0) (hmDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .absorb) (hmDigestVar shapeSmoke)).length == 3
#guard (classCells (posAt .finalize) (hmDigestVar shapeSmoke)).length == 3
-- ⚠ ⚑ **AND `index_digest` HAS THE SAME LADDER POSITION, so say it rather than let the retirement
-- read as unconditional.** §3c's derivation lives in R7 — the permutation is squeezed off segment
-- C's own state, and segment C is an R7 sub-circuit — while R1 ABSORBS the result at block 0. So
-- from `r1_transcript` to `r6_ft_eval0` `vIdxD 0` is a free witness the transcript eats (class = the
-- absorb row alone), and it is DERIVED at `r7_absorption` and `r8_finalize` (the permutation's
-- closing `Zero`, its σ probe, the absorb row). The reportable object is the full assembly; the
-- lower rungs are sub-circuits and this is where that costs something.
#guard (classCells (posAt .transcript) (vIdxD shapeSmoke 0)).length == 1
#guard (classCells (posAt .ftEval0) (vIdxD shapeSmoke 0)).length == 1
#guard (classCells (posAt .absorb) (vIdxD shapeSmoke 0)).length == 3
#guard (classCells (posAt .finalize) (vIdxD shapeSmoke 0)).length == 3
-- …and the plonk-index pin rows are R7's too, so the same reading applies to the 56 absorbed words.
#guard (classCells (posAt .ftEval0) (vIdxX shapeSmoke 27)).length == 0
#guard (classCells (posAt .absorb) (vIdxX shapeSmoke 27)).length == 2

-- ⚑ **§6b's LADDER POSITION, and it is the honest half of the retirement.** `ft_comm`'s scalars are
-- R6's OWN cells, and R6's rows arrive at `r6_ft_eval0`. So from `r3_msm` to `r5_full` the `perm`
-- and `ζ^n` cells are FREE WITNESSES — read by §6b's `Shifted_value.Type2` split row and by NOTHING
-- else — and they are DERIVED at `r6_ft_eval0` and above. Stated the way `index_digest`'s and
-- `vDLift 1`'s are, because the reportable object is the full assembly and the lower rungs are
-- sub-circuits. Equalities, not floors.
#guard (classCells (posAt .msm) tS.ftw.permV).length == 1
#guard (classCells (posAt .ipa) tS.ftw.permV).length == 1
#guard (classCells (posAt .ftEval0) tS.ftw.permV).length == 4
#guard (classCells (posAt .msm) tS.ftw.zetaV).length == 1
#guard (classCells (posAt .ipa) tS.ftw.zetaV).length == 1
#guard (classCells (posAt .ftEval0) tS.ftw.zetaV).length == 3
-- …and `sigma_comm_last`'s `Inner_curve.constant` pin is R7's (§3c), so term 0's BASE reads the same
-- way: the ladder, the doubling and the odd-branch add at `r3_msm`, plus the pin and segment C's
-- absorb from `r7_absorption`.
#guard (classCells (posAt .msm) (vIdxX shapeSmoke 6)).length == FTC_CHUNKS + 3
#guard (classCells (posAt .absorb) (vIdxX shapeSmoke 6)).length == FTC_CHUNKS + 5
-- ⚑ …whereas `t_comm`'s own words are ABSORBED at `r1_transcript` and CONSUMED from `r3_msm` up —
-- no ladder position at all, which is what makes the retirement unconditional for them.
#guard (classCells (posAt .transcript) (vTcX shapeSmoke 0)).length == 1
#guard (classCells (posAt .msm) (vTcX shapeSmoke 0)).length == 2
#guard (classCells (posAt .ipa) (vTcX shapeSmoke 0)).length == 5

-- ξ's class is COMPLETE at `r5_full`: nothing above r5 adds a cell to it, because its chain is
-- already there. (A floor `≥ 2` would pass here even with the chain deleted — the fold's own reads
-- alone give 47 — so this is stated as an EQUALITY against the top rung.)
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length
        == (classCells (posAt .finalize) (vDLift shapeSmoke 0)).length
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length == shapeSmoke.cipEvals + 2
-- r's is NOT: below the fr-sponge it is exactly the fold's `cipEvals` reads and NO defining row;
-- `r7_absorption` is the rung that adds the chain's lift row and its probe.
#guard (classCells (posAt .full) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals
#guard (classCells (posAt .ftEval0) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals
#guard (classCells (posAt .absorb) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 2
#guard (classCells (posAt .finalize) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 3
-- …and the ξ chain's `EndoMulScalar` rows are in r5 while the r chain's are not.
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 1) * shapeSmoke.emsRows
#guard ((rungRows tS .ftEval0 true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 1) * shapeSmoke.emsRows
-- …and R7 adds TWO: `r_actual`'s own chain and the `assert_128_bits` of its high part.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 3) * shapeSmoke.emsRows
-- ⚑ …and R8 adds TWO MORE — the THIRD `lowest_128_bits`, `xi_actual`'s, both parts (§12c′). This is
-- the pin that would have caught the hole: before it landed, R8's EndoMulScalar delta was ZERO and
-- the finalize rung split a field element with nothing constraining either half.
#guard ((rungRows tS .finalize true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 5) * shapeSmoke.emsRows

#guard (rungRows tS .full true).length < (rungRows tS .ftEval0 true).length
#guard (rungRows tS .ftEval0 true).length < (rungRows tS .absorb true).length
#guard (rungRows tS .absorb true).length < (rungRows tS .finalize true).length
-- R8 over R7 is scalar arithmetic + the boolean gadgets + the two `assert_128_bits` chains of its
-- own `lowest_128_bits` (§12c′) — so `Generic`/`Zero`/`EndoMulScalar` and NOT ONE CURVE GATE. It
-- was `Generic`/`Zero` only until the third high chain landed; that is a stated change, not drift.
#guard ((rungRows tS .finalize true).drop (rungRows tS .absorb true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero
                  || r.kind == KGateType.endoMulScalar)
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .poseidon].getD i .zero
  ((rungRows tS .finalize true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length)
-- R6 is `Generic`-only (it is scalar arithmetic; every other gate family is unchanged by it).
#guard ((rungRows tS .ftEval0 true).drop (rungRows tS .full true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero)
-- R7 adds `Poseidon` (11 rows per permutation, upstream's own run length) and — since §8g — exactly
-- ONE further `to_field_checked` chain, `r_actual`'s. No curve gate, no second chain.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks + 1)
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * shapeSmoke.blocks
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .zero].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    ≥ ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
#guard (List.range 3).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
-- …and the compiled ft program is a real program, not a stub.
#guard ftS.fp.prog.size ≥ 900
#guard (aHalfSlots ftS.fp.prog).length ≥ 700

/-! ## §16 — R8: `finalize_other_proof`'s tail, against the value layer.

Every scalar R8 emits is pinned against the READ-ONLY `KimchiVerify` object it claims to compute, on
the SAME inputs, each with a red control that BITES. A rung that proves but computes the wrong scalar
is the failure mode this section exists to catch. -/

def finS : FinData := tS.fin
def finVal (i : Nat) : Nat := finS.vals.getD i 0
def zetaLS : Nat := liftOf shapeSmoke tS.sp shapeSmoke.zetaChal
/-- ⚑ `r` is §8g's DEFERRED challenge — `to_field_checked` of the fr-sponge's SECOND squeeze
(`step_verifier.ml:1008,1013`), not a transcript challenge. -/
def rLS : Nat := rFoldS
/-- The lifted bulletproof challenges, in `bEval`'s own list order (factor `k` carries the exponent
`2^{bRounds−1−k}`). -/
def usS : List (ZMod pN) :=
  (List.range shapeSmoke.bRounds).map (fun k =>
    ((liftOf shapeSmoke tS.sp (shapeSmoke.uChal k) : Nat) : ZMod pN))

-- ── (a) `to_field_checked`'s CLOSING LINE — the endo lift, retiring simplification #7 ──────────
-- ⚑ The `EndoMulScalar` chain's `a₈`/`b₈` cells, combined by R2's new row, ARE
-- `ScalarChallenge::to_field(endo_r)` of the squeeze — `KimchiVerify.endoMap`, the same map
-- `MinaRealBlockTranscript.derived_zeta` checks on a real block. So `plonk.zeta`/`plonk.alpha`, ξ, r
-- and every bulletproof challenge are now the LIFTED values upstream uses, not the prechallenges.
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((liftOf shapeSmoke tS.sp c : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
         (chalOf shapeSmoke tS.sp c))
-- …and it BITES on the constant: the BASE endo `FT_ENDO` in place of the SCALAR endo `endo_r` — the
-- exact cube-root conflation `MinaWrapFtEval0Weld` closed — gives a different lift.
#guard (((liftOf shapeSmoke tS.sp 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((FT_ENDO : Nat) : ZMod pN)
              (chalOf shapeSmoke tS.sp 0)) == false
#guard ENDO_R != FT_ENDO
-- …and on the challenge: challenge 1's lift is not challenge 0's.
#guard (((liftOf shapeSmoke tS.sp 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
              (chalOf shapeSmoke tS.sp 1)) == false
-- …and the lift is NOT the identity on any challenge (a degenerate endo would make the pin vacuous).
#guard (List.range shapeSmoke.chals).all (fun c =>
  liftOf shapeSmoke tS.sp c != chalOf shapeSmoke tS.sp c)

-- ── (b) `b_correct` — BOTH legs (`step_verifier.ml:1124-1128`) ────────────────────────────────
-- ⚑ `b_actual = challenge_poly ζ + r · challenge_poly ζω`. `KimchiVerify.ipaB0` is exactly
-- `bEval ζ + evalscale · bEval ζω`; `bEvalSq` is its ladder form (`bEvalSq_eq_bEval`, a theorem for
-- every CommRing), which is what runs at `ZMod pN`. The `+ r·…` leg is the one the module header
-- named as ABSENT — it is here, and it is this value.
#guard ((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
           + ((rLS : Nat) : ZMod pN)
             * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                 (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS
-- …and the compiled slot IS the direct computation (the program is a compiler, not an oracle).
#guard finVal finS.fp.slots.bActual == finS.bActual
#guard finVal finS.fp.slots.zetaw == fMul FT_OMEGA zetaLS
-- ⚑ …and the SECOND leg is load-bearing: dropping it (i.e. `b(ζ)` alone) is a DIFFERENT value.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- ⚑ …and ζω really is ω·ζ, not ζ: evaluating the second polynomial at ζ moves the answer.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + ((rLS : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- ⚑ …and the RAW prechallenges in place of the lifted ones move it (so (a) is load-bearing HERE).
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN)
              ((List.range shapeSmoke.bRounds).map
                 (fun k => ((chalOf shapeSmoke tS.sp (shapeSmoke.uChal k) : Nat) : ZMod pN)))
            + ((rLS : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN))
                  ((List.range shapeSmoke.bRounds).map
                     (fun k => ((chalOf shapeSmoke tS.sp (shapeSmoke.uChal k) : Nat) : ZMod pN)))) == false
-- ⚑ …and — since §8g — the `r` that weights the second leg is `endoMap` of the fr-sponge's SECOND
-- squeeze, so BENDING THAT SQUEEZE MOVES `b_actual` too. This is #10's red control on the
-- `b_correct` side: the value is derived from the sponge, not fixed by the transcript.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + foldMulOf (sq2S + 1)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS) == false
-- …and the RETIRED reading (the second-to-last transcript challenge) also moves it.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2) : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS) == false
-- …and neither b-polynomial is the trivial product.
#guard finS.bActual != 0 && bwOf shapeSmoke tS.sp != 1

-- ── (c) The THREE `Shifted_value.Type1.to_field` unshifts, and the FIELD KEY ───────────────────
-- ⚑ The shift constants are what `Shift.create (module Fp)` builds: `c = 2^255 + 1` and `½`.
#guard ((SHIFT_C : Nat) : ZMod pN) == (2 : ZMod pN) ^ 255 + 1
#guard 2 * SHIFT_INV2 % pN == 1
-- ⚑ Type1 ROUND-TRIPS, so the encoding is an encoding and not a digest.
#guard unshiftT1 (shiftT1 (finS.bActual)) == finS.bActual
#guard unshiftT1 (shiftT1 7) == 7 && unshiftT1 (shiftT1 (pN - 1)) == pN - 1
-- ⚑ **THE FIELD KEY IS LOAD-BEARING.** A Type2 reading (subtract-only, `x − 2^255`, the STEP
-- statement's own `fq` block, `impls.ml:135`) and the raw unshifted value BOTH diverge from the
-- Type1/`Fp` reading these three words wear. Getting this wrong misencodes SILENTLY.
#guard shiftT1 finS.bActual != shiftT2 finS.bActual
#guard shiftT1 finS.bActual != finS.bActual
#guard unshiftT1 (shiftT2 finS.bActual) != finS.bActual
-- ⚑ …and the circuit's own emitted unshift slots hit the three actual values.
#guard finVal finS.fp.slots.cipUsed == tS.df.ca.getLastD 0
#guard finVal finS.fp.slots.bUsed == finS.bActual
#guard finVal finS.fp.slots.permUsed == ftS.vals.getD ftS.fp.slots.perm 0
-- …and `combined_inner_product` really is the value R5's Horner chain produced, which §12 already
-- pinned against `KimchiVerify.cipR`. So the unshift lands on `cipR`, not on a local name for it.
#guard ((finVal finS.fp.slots.cipUsed : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
             (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN)))

-- ── (d) `xi_correct` — the fr-sponge's own squeeze ────────────────────────────────────────────
-- ⚑ `xi_actual = lowest_128_bits (squeeze sponge)` (`step_verifier.ml:820-822,1102`), and the
-- squeeze is R7 segment B's — an assembly variable, not a fixture.
#guard finVal finS.fp.slots.xiActual == finS.xiStmt
#guard finS.xiStmt == Dregg2.Circuit.Emit.KimchiVerify.low128 (frSqueezeVal tS.segB tS.specB)
#guard finS.xiStmt < 2 ^ 128
-- …and the squeeze is NOT already 128 bits (so the decomposition is doing work).
#guard finS.xiHi != 0
-- …and it is NOT any R1 transcript squeeze: the two sponges are different objects, which is why the
-- check is a check.
#guard (List.range shapeSmoke.chals).all (fun c =>
  finS.xiStmt != chalOf shapeSmoke tS.sp c)
-- ⚑ **AND THIS WORD FEEDS THE FOLD** (simplification #10, retired). `xi_correct` ties the statement
-- ξ word to this squeeze, and §8g's chain 0 lifts THAT WORD into the multiplier `cipRows` Horners
-- over — upstream's `let xi_correct = … in let xi = scalar xi` (`step_verifier.ml:1010-1012`). So a
-- prover cannot move the fold's ξ without failing `xi_correct`, and cannot satisfy `xi_correct`
-- without the fold's ξ being `endoMap` of the fr-sponge's squeeze.
#guard ((xiFoldS : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) finS.xiStmt
#guard tS.defc.pre.getD 0 0 == finS.xiStmt

-- ── (e) `Boolean.all` and the `should_verify` mux ─────────────────────────────────────────────
-- ⚑ ALL FOUR legs are 1 on the honest instance, the conjunction is 1, and the muxed output is 1 —
-- which is the value the rung's last row ASSERTS.
#guard [finVal finS.fp.slots.xc, finVal finS.fp.slots.bc, finVal finS.fp.slots.cc,
        finVal finS.fp.slots.pc, finVal finS.fp.slots.finalized, finVal finS.fp.slots.out]
        == [1, 1, 1, 1, 1, 1]

/-- Re-run R8's program with ONE statement word bent and the `Field.equal` witnesses set the way an
HONEST prover would then have to set them (`bit = 0`, `inv = d⁻¹`), so the control is about the
CHECK and not about a witness nobody could produce. Returns the `out` slot — the value the last row
asserts equals 1. -/
def finOutBent (which : Nat) (sv : Nat) : Nat :=
  let s := shapeSmoke
  let d := tS.sp
  let sqv := frSqueezeVal tS.segB tS.specB
  let base := finInputEnv s d tS.ft tS.df tS.segB tS.specB rFoldS
  -- bend the `which`-th statement word (0 = cip, 1 = b, 2 = perm, 3 = xi)
  let tgt : PVar :=
    match which with
    | 0 => vCipShift s | 1 => vBShift s | 2 => vPermShift s | _ => vXiStmt s
  -- ⚑ `should_verify` is bent through the ENVIRONMENT, because since §8f it is a STATEMENT WORD
  -- and not a `FinCfg` witness: selecting the dummy branch is a public claim, not a private one.
  let env := base.map (fun p =>
    if p.1 == tgt then (p.1, p.2 + 1)
    else if p.1 == vShouldVerify s then (p.1, (sv : Int)) else p)
  -- the honest witnesses for the bent instance: the bent leg's difference is `±2` (an unshift
  -- doubles) or `−1` (the raw ξ word), so `bit = 0` and `inv = d⁻¹` there, `bit = 1` elsewhere.
  let dv : Nat := if which == 3 then pN - 1 else 2
  let inv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv dv
  let idx : Nat := match which with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0
  let C : FinCfg :=
    { finCfgOf s (sqv / 2 ^ 128) with
      eqInv := (List.replicate 4 0).set idx inv
      eqBit := (List.replicate 4 1).set idx 0 }
  let p := finProgOf (finWireOf s tS.ft) C
  (aEval (envLookupAt (envIndex env)) p.prog).getD p.slots.out 0

-- ⚑ **THE RED CONTROLS BITE, ONE PER DEFERRED WORD.** Bend the statement's `combined_inner_product`,
-- its `b`, its `plonk.perm` or its `xi` by ONE, give the equality gadget the witnesses an honest
-- prover would then have to give, and the assert `out = 1` FAILS. That is the whole point of the
-- rung: the deferred values BIND.
#guard (List.range 4).all (fun i => finOutBent i 1 != 1)
-- …and the UNBENT re-run through the same helper is 1, so the reds are about the bend.
#guard finVal finS.fp.slots.out == 1
-- ⚑ **BOTH BRANCHES OF THE `should_verify` MUX OCCUR.** With `should_verify = 0` the dummy path
-- accepts the very same bent statement — `verified && finalized ||| not should_verify`
-- (`step_main.ml:121`). A mux with one reachable branch is decoration.
#guard (List.range 4).all (fun i => finOutBent i 0 == 1)

-- ── (g) ⚑ `should_verify` IS A STATEMENT WORD, NOT A WITNESS ───────────────────────────────────
-- ⚑ THE HOLE THIS CLOSES, exhibited by the two lines above. `should_verify = 0` makes R8's assert
-- pass with ALL FOUR deferred legs false — so while it was an `AOp.wit` with no defining row, a
-- prover simply set it to 0 and `finalize_other_proof`'s tail bound NOTHING. That is not upstream:
-- `step_main.ml:36-37` asserts `unfinalized.should_finalize = should_verify`, and `should_finalize`
-- is in the Per_proof statement's `bool` list (`composition_types.ml:1219,1310`), i.e. PUBLIC.
-- It is now the assembly's tenth statement word and its FIFTH public word, so choosing the dummy
-- branch is a claim the consumer READS.
#guard (exposedVars shapeSmoke).getD 4 (xv 0) == vShouldVerify shapeSmoke
#guard (exposedVars shapeStep).getD 4 (xv 0) == vShouldVerify shapeStep
-- …its class is R8's five reads — the booleanity square (two cells), the `= sv` assert, the mux
-- multiply and the `1 − sv` — PLUS the closing public tie. Equality, so the tie's deletion (which
-- is the whole content of the fix) moves it: as a witness it was these five and no public cell.
#guard (classCells posS (vShouldVerify shapeSmoke)).length == 6
-- …and it is in `finInputEnv`, i.e. R8 reaches it as an `.inp` and not as a private cell.
#guard (finS.fp.prog.toList.filter (fun o => o == AOp.inp (vShouldVerify shapeSmoke))).length == 1
-- …and NO `.wit` slot of R8's program holds it any more. The witnesses that remain are exactly the
-- four `Field.equal` inverse/bit pairs, `lowest_128_bits`' high part (range-checked by §12c′'s
-- chain) and #11's `verified` bit — which is the honest census of what R8 still takes on trust.
#guard (finS.fp.prog.toList.filter (fun o =>
          match o with | .wit _ => true | _ => false)).length == 4 * 2 + 1 + 1

-- ── (f) NO FREE VARIABLE reaches the public vector ────────────────────────────────────────────
-- ⚑ Every exposed variable's copy class has a cell OUTSIDE its closing row, i.e. some row COMPUTES
-- it. This is the shape of the defect that hid `cipRows`: a public word tied to a variable no gate
-- writes passes every probe and every control while binding nothing.
#guard (exposedVars shapeSmoke).all (fun v => (classCells posS v).length ≥ 2)
-- …and the four STATEMENT words are among them, each reaching R8's rows.
#guard (classCells posS (vCipShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vBShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vPermShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vXiStmt shapeSmoke)).length ≥ 2
-- …and every `.inp` source of R8's program is a variable the assembly's OTHER rows carry, so the
-- rung reads the assembly rather than a private island.
#guard (finS.fp.prog.toList.filterMap (fun o =>
          match o with | .inp v => some v | _ => none)).all
        (fun v => (classCells posS v).length ≥ 2)
#guard (finS.fp.prog.toList.filter (fun o =>
          match o with | .inp _ => true | _ => false)).length ≥ 10
-- …and R8's program is a real program, not a stub.
#guard finS.fp.prog.size ≥ 80

end Dregg2.Circuit.Emit.KimchiStepMain
