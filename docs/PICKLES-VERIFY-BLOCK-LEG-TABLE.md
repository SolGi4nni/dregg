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
* **CODEC** — the wire type admits no encoding of a violation; forced by construction at decode.
* **CONSUMER REFUSAL** — the node evaluates a decision (here: compiled Lean) and refuses the block.
* **VALUE LAYER** — computed and compared somewhere, but not on any path the node runs.
* **OPEN** — not checked anywhere.

| # | leg | source | closure | where the forcing lives |
|---|---|---|---|---|
| A1 | `accumulator_check` (`batch_dlog_accumulator_check` on Vesta) | `verification.rs:772` | **VALUE LAYER** | asserted in `MinaRealBlockGate`'s Rust ground-truth preamble on one block; not run per block |
| B1 | `non_chunking` — every `prev_evals` vector ≤ 1 | `verification.rs:568-629` | **CONSUMER REFUSAL** ⚑ NEW | `PicklesVerifyPreamble.nonChunking` → `preambleLegsOk` → `dregg_mina_wrap_shape_ok` → `mina_observer::check_block_proofs`; the wire summary is proved equivalent to the list predicate by `maxPairLen_le_one_iff_nonChunking` |
| B2 | `validate_feature_flags` | `verification.rs:631-642`, body `:74-142` | **CODEC** ⚑ NEW | `mina_pickles.rs:619-627` refuses any set flag and `:616` any `Some` joint combiner; `:749-758` now refuses a present `lookup_sorted` (it did not before today — §4). `the_flagless_contract_is_a_theorem` proves by `rfl` that at zero flags the body IS "every optional evaluation absent" |
| B3 | step domain log2 ≤ `BACKEND_TICK_ROUNDS_N` | `verification.rs:644-651` | **CONSUMER REFUSAL** ⚑ NEW | `stepDomainOk` in `preambleLegsOk`; `branch_domain_log2` was already decoded (`mina_pickles.rs:640`) and fed nothing |
| B4 | `actual_wrap_domain ≤ 15` | `verification.rs:653-662` | **OPEN** | `wrapDomainOk` authored + proven; not on the wire (the Wrap VK's domain is pinned config, not decoded) |
| B5 | `actual_wrap_domain ≥ 13` | `verification.rs:663-666` | **OPEN** | as B4. ⚠ upstream's two identifiers are SWAPPED — `greatest_wrap_domain` is bound to `13` — and reading the names instead of the destructuring gives the EMPTY interval (`the_swapped_names_give_the_empty_interval`) |
| C0 | `compute_deferred_values` / `expand_deferred` | `verification.rs:676-738` | **VALUE LAYER** | `gates::gate_b` in the offline extractor |
| C1 | `messages_for_next_step_proof.hash()` | `verification.rs:869-873` | **VALUE LAYER** | `gates::gate_c` + `segd_slot12_probe`; the digit-level agreement is real and is not run by the node |
| C2 | `messages_for_next_wrap_proof.hash()` | `verification.rs:875-876` | **VALUE LAYER** (digest) / **proven schedule** ⚑ NEW | preimage schedule proven in `PicklesVerifyPreamble` §7 — 32 Fq fields, padding FIRST, Tock-sized slots, >2 slots a refusal; the DIGEST is `gate_c`'s. See §5 |
| C3 | `to_public_input(npublic_input)` | `verification.rs:885-886`, body `prepared_statement.rs:53-181` | **CONSUMER REFUSAL** (length) ⚑ NEW / **VALUE LAYER** (the 40 words) | `toPublicInputLen` is `24 + nChal`, proven injective in `nChal` and `= 40` at the tick rounds, and conjoined into the gate via D1b. The word VALUES are `gates::wrap_public_input` |
| D1a | `prev_challenges.len() == index.prev_challenges` | `verifier.rs:810-815` | **CONSUMER REFUSAL** | `KimchiVerify.shapeOkRec`'s first conjunct — closed since 2026-07-28 (P6) |
| D1b | `public_input.len() == index.public` | `verifier.rs:816-820`, re-checked `:834-839` | **CONSUMER REFUSAL** ⚑ NEW — **was mis-marked, see §4** | `publicInputLenOk (toPublicInputLen nChal) publicLen` in `preambleLegsOk` |
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

**Zero**, at every layer this table covers. No AIR row forces any leg of `verify_block`. The
strongest closures dregg has here are **CODEC** (B2, D2 — a violation has no encoding) and
**CONSUMER REFUSAL** (B1, B3, C3-length, D1a, D1b, D3, D4 — the node evaluates a Lean-authored
decision and refuses the block). Both are real and both are on the deployed path; neither is what
"closed by constraint" means, and this lane found the distinction was worth being strict about.

**What moved today:** four legs from OPEN to CONSUMER REFUSAL (B1, B3, C3-length, D1b), one from a
silently-accepted violation to CODEC (B2), one re-marked from OPEN to CODEC after reading the wire
type (D2), and C2's preimage schedule from nothing to proven. Two remain OPEN (B4, B5) with the
blocker named. The preamble half of `verify_block` is now closed against the pinned target; the
arithmetic half is where it was.
