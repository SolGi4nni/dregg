# `verify_block`, leg by leg — what dregg closes, and BY WHAT

**Pinned target:** `mina-rust @ 82480cd468f1963b73dc0b700161036411449e4c` (v0.19.0,
`/Users/ember/dev/mina-rust`), with `kimchi` from `proof-systems` tag `0.3.0`, rev
`a73ca6ed580a346344ba80a88137b100237070dc` (`Cargo.lock`), unpacked at
`~/.cargo/git/checkouts/proof-systems-c874fc66c693964b/a73ca6e/kimchi`.

⚠ **`~/dev/openmina @ 8e68037a` is a STUB TWIN** — `verify_impl` there returns literal `true`
with the whole body commented out. Do not read it as the implementation. `~/dev/mina` (OCaml)
has no `.git` and is corroboration only, never the pinned target.

Written 2026-08-08 by the lane that built B1/B2/B3/C2/C3/D1/D2.

---

## 0. The pin is the right one — established, not assumed

The leg list is anchored on `mina-rust @ 82480cd46`. Two independent checks say that is the
protocol version devnet actually runs, and a devnet acceptance test is gated behind this.

1. **The chain id includes the protocol version.** `ChainId::compute`
   (`crates/core/src/chain_id.rs:244-265`) hashes the genesis state hash, the constraint-system
   digests, the genesis constants, **and `md5_hash(protocol_transaction_version)` and
   `md5_hash(protocol_network_version)`** (`:262-263`). A devnet on a different protocol version
   serves a different chain id.
2. **Upstream recomputes it, and the test passes at the pinned rev.**
   `chain_id::test::test_devnet_chain_id` (`:532-554`) recomputes `DEVNET_CHAIN_ID` from
   `devnet::CONSTRAINT_SYSTEM_DIGESTS`, genesis `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`,
   `PROTOCOL_TRANSACTION_VERSION = 3` and `PROTOCOL_NETWORK_VERSION = 3`
   (`crates/core/src/constants.rs:317-319`), tx pool 3000. Run at the pinned rev:

   ```
   $ cargo test -p mina-core --lib chain_id
   test chain_id::test::test_devnet_chain_id     ... ok
   test chain_id::test::test_devnet_chain_id_as_hex   ... ok
   test chain_id::test::test_mainnet_chain_id    ... ok
   test chain_id::test::test_mainnet_chain_id_as_hex  ... ok
   test result: ok. 4 passed; 0 failed; 0 ignored
   ```

3. **Live devnet serves exactly that chain id, today.** Read-only GraphQL against
   `api.minascan.io/node/devnet/v1/graphql` on **2026-08-08**, height **542569**:
   `chainId = 29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6` — byte-identical to
   `DEVNET_CHAIN_ID` (`chain_id.rs:487-490`) and to the `chain_id` recorded in our own fixture
   `metatheory/fixtures/pickles-extractors/mina_devnet_block.json` (fetched 2026-07-28, height
   539508), whose `genesis_state_hash` is also the test's genesis hash.

**Verdict: the pin is correct.** Devnet runs the protocol version `mina-rust @ 82480cd46` targets.

⚠ Unchanged and still true: **mainnet is not reachable at this rev** — the embedded
`mainnet_*_verifier_index.json` are a stale serde format and `BlockVerifier::make()` panics
(`docs/MINA-REAL-BLOCK-GATE.md` §5). Everything below is devnet.

---

## 1. `verify_block` is two conjuncts

`crates/ledger/src/proofs/verification.rs:750-784`:

```rust
let accum_check = accumulator_check::accumulator_check(srs, &[protocol_state_proof]).unwrap_or(false);
let verified    = verify_impl(&protocol_state_hash, protocol_state_proof, &vk).unwrap_or(false);
let ok = accum_check && verified;
```

and `verify_impl` (`:857-894`) is `compute_deferred_values` · `run_checks` ·
`get_message_for_next_step_proof` · `get_message_for_next_wrap_proof` · `get_prepared_statement` ·
`to_public_input` · `verify_with`, conjoined with `run_checks`' verdict at `:893`.

---

## 2. ⚑ A NOTE ON THE COUNT, AND A CORRECTION TO THE BRIEF

This lane was briefed with "**28 legs. 12 closed by constraint, 6 at value layer only, 10 open**,"
attributed to an audit. **That table is not in this repo** — `git grep` finds no 28-leg
enumeration in `docs/`, `metatheory/docs/` or `HORIZONLOG.md`. It could not be re-read, so it
could not be re-marked. What follows is a **re-derivation from the same source**, with its own
count, marked by this lane. It is **22 legs**, not 28; the difference is decomposition granularity,
not disagreement about the object.

⚠ **And the brief's "12 closed by constraint" should not be relied on.** This lane probed exactly
one leg the tree describes as closed and found the description overstated (§4, D1b). The word
"constraint" was not the tree's own — but the same class of overstatement was there, and one
datapoint out of one is not a reason to trust the other eleven. **Nothing in the Mina cone is
closed by AIR constraint at the preamble layer**: `shapeOkRec` / `picklesWrapShapeOk` is a
compiled Lean decision the observer *calls*; no AIR row forces it. That is CONSUMER REFUSAL, and
it is a real mechanism — but it is not the one the word "constraint" names.

---

## 3. The table

**Closure kinds**, used strictly:

* **CONSTRAINT** — an AIR row forces it; a prover cannot produce an accepted proof without it.
* **SEAM** — forced by a fold's in-circuit `cb.connect`s, where the pin list is a Lean-emitted
  `SeamSpec` (`circuit/descriptors/seams/*.json`) with S1 (the pins name exactly the published
  slots) and S2 (the refutable composition theorem). ⚑ Added 2026-08-08 — this is the third honest
  value between CONSTRAINT and CONSUMER REFUSAL: real in the parent proof, Lean-named, but
  recursion wiring on the undischarged FRI/STARK floor, not an AIR row. See §7.
* **CODEC** — the wire type admits no encoding of a violation; forced by construction at decode.
* **CONSUMER REFUSAL** — the node evaluates a decision (here: compiled Lean) and refuses the block.
* **VALUE LAYER** — computed and compared somewhere, but not on any path the node runs.
* **OPEN** — not checked anywhere.

| # | leg | source | closure | where the forcing lives |
|---|---|---|---|---|
| A1 | `accumulator_check` (`batch_dlog_accumulator_check` on Vesta) | `verification.rs:772` | **VALUE LAYER** | asserted in `MinaRealBlockGate`'s Rust ground-truth preamble on one block; not run per block |
| B1 | `non_chunking` — every `prev_evals` vector ≤ 1 | `verification.rs:568-629` | **CONSTRAINT** (relation) ⚑ 2026-08-08 | `dregg-mina-preamble-legs::v1` (`MinaPreambleLegsAir`): `MAXLEN·(MAXLEN−1) = 0` — the wire summary is a bit, and `maxPairLen_le_one_iff_nonChunking` is why a bit decides the list universal; PLUS the empty walk (which upstream's `all` accepts vacuously, `nonChunking_nil`) refused by `PAIR_COUNT·PAIR_INV − 1 = 0`. ⚠ slot-to-wire binding is the HOST's (§8). Consumer refusal (`preambleLegsOk`) still runs beside it |
| B2 | `validate_feature_flags` | `verification.rs:631-642`, body `:74-142` | **CODEC** ⚑ NEW | `mina_pickles.rs:619-627` refuses any set flag and `:616` any `Some` joint combiner; `:749-758` now refuses a present `lookup_sorted` (it did not before today — §4). `the_flagless_contract_is_a_theorem` proves by `rfl` that at zero flags the body IS "every optional evaluation absent" |
| B3 | step domain log2 ≤ `BACKEND_TICK_ROUNDS_N` | `verification.rs:644-651` | **CONSTRAINT** (relation) ⚑ 2026-08-08 | `dregg-mina-preamble-legs::v1`: `DOMAIN_LOG2 + Σ2ⁱ·SBITᵢ − 16 = 0` with boolean bits — a 17 has NO satisfying row (`a_17_domain_has_no_accepted_row`), and the real block's 16 is AT the boundary and proves. ⚠ binding: HOST (§8) |
| B4 | `actual_wrap_domain ≤ 15` | `verification.rs:653-662` | **OPEN** | `wrapDomainOk` authored + proven; not on the wire (the Wrap VK's domain is pinned config, not decoded) |
| B5 | `actual_wrap_domain ≥ 13` | `verification.rs:663-666` | **OPEN** | as B4. ⚠ upstream's two identifiers are SWAPPED — `greatest_wrap_domain` is bound to `13` — and reading the names instead of the destructuring gives the EMPTY interval (`the_swapped_names_give_the_empty_interval`) |
| C0 | `compute_deferred_values` / `expand_deferred` | `verification.rs:676-738` | **VALUE LAYER** | `gates::gate_b` in the offline extractor |
| C1 | `messages_for_next_step_proof.hash()` | `verification.rs:869-873` | **VALUE LAYER** | `gates::gate_c` + `segd_slot12_probe`; the digit-level agreement is real and is not run by the node |
| C2 | `messages_for_next_wrap_proof.hash()` | `verification.rs:875-876` | **VALUE LAYER** (digest) / **proven schedule** ⚑ NEW | preimage schedule proven in `PicklesVerifyPreamble` §7 — 32 Fq fields, padding FIRST, Tock-sized slots, >2 slots a refusal; the DIGEST is `gate_c`'s. See §5 |
| C3 | `to_public_input(npublic_input)` | `verification.rs:885-886`, body `prepared_statement.rs:53-181` | **CONSTRAINT** (length relation) ⚑ 2026-08-08 / **VALUE LAYER** (the 40 words) | `dregg-mina-preamble-legs::v1`: `PUB_LEN − 24 − N_CHAL = 0` — the produced length COMPUTED in-constraint from the challenge count (`one_challenge_short_is_refused`: a 15-challenge packing against a 40 index has no row). The word VALUES stay `gates::wrap_public_input`. ⚠ binding: HOST (§8) |
| D1a | `prev_challenges.len() == index.prev_challenges` | `verifier.rs:810-815` | **CONSTRAINT** (relation) ⚑ 2026-08-08 | `dregg-mina-preamble-legs::v1`: `PROOF_PREV − IDX_PREV = 0`; consumer refusal (`shapeOkRec`'s first conjunct, since P6) still runs beside it. ⚠ binding: HOST (§8) |
| D1b | `public_input.len() == index.public` | `verifier.rs:816-820`, re-checked `:834-839` | **CONSTRAINT** (relation) ⚑ 2026-08-08 — **was mis-marked, see §4** | `dregg-mina-preamble-legs::v1`: `PUB_LEN − IDX_PUBLIC = 0` — the equality itself as a polynomial. `the_41_word_index_has_no_accepted_row`: ANY row carrying 16 challenges refuses an index declaring 41 — the pair the VK digest cannot separate, separated by an emitted constraint. ⚠ binding: HOST (§8) |
| D2 | `check_proof_evals_len` | `verifier.rs:822-831`, body `:640-779` | **CODEC** ⚑ NEW | the binprot `Pickles__Wrap_wire_proof.Stable.V1` stores exactly ONE `(ζ, ζω)` scalar pair per evaluation (`mina_pickles.rs:766-787`) — a chunked evaluation **has no encoding**. With the exact-fit / every-byte-consumed discipline this is stronger than a runtime compare |
| D3 | `t_comm.len() ≤ 7 · chunk_size` | `verifier.rs:259-266` | **CONSUMER REFUSAL** | `shapeOkRec`'s last conjunct |
| D4 | `chunk_size` derivation | `verifier.rs:823-830` | **CONSUMER REFUSAL** | `shapeOkRec` pins `chunkSize = 1`; `chunkSizeOf` now transcribes the derivation with its `<` guard and truncating division |
| D5 | `public_comm` — the negated Lagrange MSM | `verifier.rs:833-858` | **VALUE LAYER** | `MinaWrapPublicCommGate`, `by decide` on one block |
| D6 | Fiat–Shamir transcript order (β γ α ζ v u) | `verifier.rs:126-405` | **VALUE LAYER** | `MinaRealBlockTranscript` — DERIVED on block 539508, not per block |
| D7 | public evaluation at ζ, ζω | `verifier.rs:332-379` | **VALUE LAYER** | `publicEval`, swept at both deployed fields; fixture-bound |
| D8 | permutation argument inside `ft(ζ)` | `verifier.rs:411-462` | **VALUE LAYER** | `ftEval0R` on block 539508 |
| D9 | linearization / gate constraints at ζ | `verifier.rs:464-487` | **VALUE LAYER** | `evalToks` + the six gate bodies; `linConstTerm` DERIVED |
| D10 | `f_comm` MSM + `ft_comm` (Maller) | `verifier.rs:889-965` | **VALUE LAYER** | `FtCommWeld` — reproduces the `ft_comm` o1-labs' own `SRS::verify` accepts, on one block |
| D11 | `combined_inner_product` + batch assembly | `verifier.rs:492-606` | **VALUE LAYER** | `cipR`, all 47 `es` entries incl. the recursion prefix |
| D12 | the IPA opening relation | `ipa.rs:301-502` | **VALUE LAYER** | K4c's deferral; the terminal `⟨s, srs.g⟩` MSM is ~3.5 h serial / ~28 GB per block |

**Not counted as a leg:** D-plookup (`verifier.rs:179-247`) is feature-gated and unreachable on
the devnet blockchain index — B2's codec refusal makes a lookup-enabled proof undecodable here.

---

## 4. ⚑⚑ THE DEFECT THIS LANE FOUND, AND FIXED

`KimchiVerify.shapeOkRec`'s docblock says it is "**every** length/shape assert of `to_batch`'s
preamble." It was not, in two places, and one of them was live.

**D1b.** `shapeOkRec`'s second conjunct is `decide (0 < publicLen)`, with a line comment citing
`verifier.rs:816-820`. That line is `public_input.len() != verifier_index.public` — an **equality
between two independently-derived quantities**. `0 < publicLen` is not a weaker form of it; it is
a different predicate. And on the deployed path `publicLen` arrives from
`mina_pickles::MinaWrapIndexParams::DEVNET_BLOCKCHAIN.public_len = 40` — **trusted config** — so
the conjunct compared a constant against zero and **could not fail**:

* `PicklesWrapShapeGate.the_old_public_conjunct_could_not_fail_on_this_path` — for every non-zero
  `publicLen`, the old gate's verdict is *unchanged*. A conjunct constant over its input's whole
  live range is not a check.
* `PicklesWrapShapeGate.the_old_gate_admits_a_public_input_it_should_refuse` — the old gate
  **ACCEPTS** an index declaring 41 public inputs against a 40-word packing, which is
  `VerifyError::IncorrectPubicInputLength` upstream.

⚑ It composes with a blindness this tree had already proven:
`MinaWrapVkDigestChain.the_index_digest_cannot_see_the_circuit_shape` shows kimchi's index
`digest()` binds `public` to `_`, so the 40-word and 41-word indices have the **same VK digest** —
the pin cannot separate them either. **Nothing on the deployed path pinned the count to 40.** Now
`publicInputLenOk (toPublicInputLen nChal) publicLen` does, with the produced length COMPUTED from
the wire's challenge count rather than supplied beside it.

**B2, second find.** `mina_pickles::decode_proof_at` refused a `Some` on every optional evaluation
group *except* `lookup_sorted`, which it walked and accepted. With all eight feature flags clear —
which the same decoder enforces — `validate_feature_flags` requires every `lookup_sorted[i]`
absent, so a present one is exactly a `validate_feature_flags` violation that this path accepted
and upstream refuses. Closed; falsifier in
`mina_observer::a_present_lookup_sorted_evaluation_is_refused_by_the_codec`.

**D2, third find — a closure kind that was better than expected.** `check_proof_evals_len` cannot
be violated on our wire at all: the binprot Wrap proof stores one scalar pair per evaluation, so
there is no encoding of a chunked one. That is CODEC closure, and it is worth writing down because
the obvious move — adding a runtime length compare — would have been checking something the type
already forces, while B1's object (`prev_evals`, a genuine `ArrayN16`) was the one that needed it.

---

## 5. What is still undone here, priced rather than labelled

**C2's digest.** `hash_fields` over the 32-element Fq preimage. The schedule is proven; the digest
is not built. This is **undone work, not a boundary**: it is 16 Fq absorb links of exactly the
shape `MinaWrapVkDigestChain` runs at 28 links, and that file's
`the_descriptor_is_the_deployed_phase1_link` proves such a chain needs **no new AIR**
(`vkChainDesc = MinaPhase1Chain.chainDesc`, by `rfl`). What is absent is the Fq-side instantiation
and its fixture. Next item.

**B4/B5.** Authored and proven, not wired: the Wrap VK's own domain is pinned config on this path,
not decoded, so there is nothing to compare against yet. Modelling the Wrap VK is P8/P9.

**Everything at D5–D12 stays VALUE LAYER**, and the reason is measured, not rhetorical: those
theorems are `by decide` over the literal constants of one extracted block, they need values that
are not on the wire (`messages_for_next_step_proof.app_state` is literally `()`), and their cost is
kernel-`decide` cost per block. See `bridge/src/mina_observer.rs`'s table and
`docs/MINA-REAL-BLOCK-GATE.md` §7.

---

## 6. The answer to the headline question

**How many of upstream's legs does dregg close BY CONSTRAINT?**

**Five leg-relations are forced by emitted polynomials as of 2026-08-08** — B1 (both halves:
the chunking bound and the non-empty walk), B3, C3's length, D1a and D1b — by
`dregg-mina-preamble-legs::v1` (`metatheory/Dregg2/Circuit/Emit/MinaPreambleLegsAir.lean`,
Lean-authored, 30 columns, 38 constraints, no table, no lookup, committed = declared). Both
polarities run in release at the deployed prover (`circuit/tests/mina_preamble_legs_proves.rs`,
`test result: ok. 10 passed`): the real block's tuple proves, and each of six falsifiers —
including the 41-word index of §4 and a 17 step domain — is refused with `OodEvaluationMismatch`,
the constraint system's own verdict, on the adversarial rail (`prove_vm_descriptor2_unchecked`,
so no producer pre-flight fires first).

⚠ **Said at its true kind, not a word stronger:** what the AIR forces is the RELATION over the
eight PUBLISHED slots — no accepted (proof, PI) pair violates a leg. The BINDING of those slots
to the real wire (`WrapProofShape`'s counts, the pinned index params) is the verifying HOST's,
exactly the position `MinaBodyPreimageBitsAir`'s 302 limbs are in; §8 names it. The earlier
verdict — zero — remains true of every OTHER row of this table: B2/D2 stay CODEC, the
`shapeOkRec` count conjuncts and D3/D4 stay CONSUMER REFUSAL, D5–D12 stay VALUE LAYER.

**What moved on 2026-08-08, second pass:** five legs from CONSUMER REFUSAL to CONSTRAINT
(relation), with the consumer refusal still running beside the AIR on the deployed path. Earlier
the same day: four legs OPEN → CONSUMER REFUSAL (B1, B3, C3-length, D1b), one silently-accepted
violation → CODEC (B2), one OPEN → CODEC re-mark (D2), C2's preimage schedule proven. Two remain
OPEN (B4, B5) with the blocker named.

---

## 7. ⚑ The SEAM rows — tower-side conjuncts, not `verify_block` legs (added 2026-08-08)

These are NOT rows of the table in §3: they close conjuncts of the **dregg-side wrap tower**
(the finalize/kimchi-gadget recursion), not legs of `verify_block`. They are recorded here because
this document is where closure kinds are used strictly, and these three carried the tree's worst
closure-kind drift — *a claim true of the FOLD, attributed to the AIR* — four separate times.

| conjunct | closure | named artifact |
|---|---|---|
| `xiCorrect` (the conjunction's record-ξ is the endo lift of `v′`) | **SEAM** | `dregg-seam-xi-endo-to-conjunction::v1` — S1 `the_xi_seam_welds_the_lift_to_the_record`, S2 `xi_seam_certifies`, refuter `xi_seam_S2_needs_the_seam`, honest pole `the_xi_seam_composes_on_the_block` (`metatheory/Dregg2/Circuit/Emit/MinaSeams.lean`) |
| `v′` provenance (the finalize `v′` is the low 128 bits of the chain's terminal squeeze) | **SEAM** | `dregg-seam-chain-vprime-to-finalize::v1` — S1 `the_v_prime_seam_is_the_terminal_squeeze`, S2 `v_prime_seam_certifies`, refuter `v_prime_seam_S2_needs_the_seam` |
| fresh sponge start (the chain began at `(0,0,0)`) | **SEAM** | `dregg-seam-chain-fresh-sponge::v1` — S1 `the_fresh_sponge_seam_zeroes_the_whole_incoming_state`, S2 `fresh_sponge_seam_certifies` (⚠ its dropped-seam form is not refutable at this layer — the composed sentence is existential over the tape; stated in the file) |

The mechanism: the pin lists are Lean-emitted (`circuit/descriptors/seams/*.json`, from
`MinaSeams.lean` via `EmitSeamSpecs.lean`); the fold functions are READERS
(`circuit-prove/src/seam.rs::apply_seam`) that author no index arithmetic and refuse a seam end
whose recomputed fingerprint lanes disagree with the loaded descriptor; the drift gate is
`circuit-prove/tests/seam_specs.rs`; and the conjunction's ξ block is a declared **PORT**
(`conjunctionPortedAir`) whose census (`CoveredPort`) refuses to elaborate without a covering seam.

⚑ Three load-bearing claims that were stronger than their mechanism, restated at their true kind:
*"53/53 forced"* is **3/53 unconditional** (HORIZONLOG, corrected 2026-08-08 — never state the
count without the split); *"all 66 fold sites pin child VK identity"* is **recursion wiring plus
CONSUMER REFUSAL** (`fold_vk_pin.rs`'s opening docblock: *"the verb matters: TAKEN, not FORCED"*);
and `xiCorrect` is **SEAM**, above — the AIR half of it is a column equality between two blocks its
own theorem proves free.

---

## 8. ⚑ The CONSTRAINT rows' residual, named once (added 2026-08-08, second pass)

The five CONSTRAINT (relation) rows in §3 share one residual, and it is stated here rather than
five times: **the AIR forces the relation over its eight published slots; the slot-to-wire
binding is the verifying host's.** A proof of `dregg-mina-preamble-legs::v1` shows there EXISTS
no accepted row whose tuple violates B1/B3/C3-length/D1a/D1b — the falsifiers are non-existence
demonstrated at the deployed prover, not comparisons a process ran. But which eight numbers
occupy the slots is fixed by whoever checks the PI vector: today that is the same consumer that
runs the compiled gate, handing it the numbers `mina_pickles::decode_proof_at` measured
(`bulletproof_challenge_count = 16`, `prev_eval_pairs = 43`, `prev_eval_max_len = 1`,
`branch_domain_log2`, and the pinned `public_len = 40` / `prev_challenges = 2`).

Publication is the weld's REACHABILITY: a recursion fold that consumes `air_public_targets` can
`cb.connect` these slots to the wire-decode's own carriers, at which point the binding moves from
HOST to SEAM/CONSTRAINT. Until that fold exists, describing these rows as "the leg is closed by
constraint, full stop" would be the exact closure-kind drift §7 records — the honest sentence is
**"the relation is an emitted constraint; the binding is the host's PI supply."** The consumer
refusal (`preambleLegsOk` in `dregg_mina_wrap_shape_ok`) keeps running on the deployed path
unchanged, so nothing weakened.

Mechanics, for the reader who wants to re-run it:

```
cd metatheory && lake build Dregg2.Circuit.Emit.MinaPreambleLegsAir     # the AIR + both polarities in Lean
lake env lean --run MinaPreambleLegsEmit.lean ../circuit/tests/fixtures  # the Lean-owned witness row
cargo test -p dregg-circuit --release --test mina_preamble_legs_proves -- --nocapture
```
