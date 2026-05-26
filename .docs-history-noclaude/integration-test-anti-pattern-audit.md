# Integration Test Anti-Pattern Audit Report

**Scope:** All `#[test]` functions and `demo-agent/examples/` binaries across the workspace.  
**Method:** Static analysis (no `cargo test` executed). Heuristic script + targeted manual review.  
**Date:** 2026-05-25

---

## Executive Summary

| Metric | Count |
|---|---|
| `.rs` files scanned | ~2,800 |
| `#[test]` functions found | ~600+ |
| `demo-agent/examples/` binaries | 35 `main()` functions |
| **Critical mass of duplicate stubs** | **~151 `panic!("blocked")` placeholders across 13 files** |
| High-confidence anti-patterns | 47 individual tests / test groups |

The single biggest source of noise is a **mass duplicate-stub epidemic**: ~151 ignored placeholder tests share the exact same 2-line body (`panic!("blocked")`). They provide zero signal, bloat test counts, and slow compilation. The second-largest gap is the `demo-agent/examples/` suite: many are treated as integration tests in CI but contain 0–1 assertions amid 200–900 lines of setup/print logic.

---

## Anti-Pattern 1: Constructor / API-Shape Tests (Testing Existence, Not Behavior)

**Definition:** Tests that instantiate a value or reference a function but perform no observable-behavior assertion. They only verify that code compiles or that a type has a certain shape.

**Impact:** Zero regression signal; compilation already guarantees this.

| File | Test Name | Lines | Assertion Count | Confidence |
|---|---|---|---|---|
| `teasting/tests/cross_federation_captp_turn.rs` | `handoff_certificate_validate_via_dregg_captp_api_exists` | 6 | 0 | **High** |
| `teasting/tests/cross_federation_captp_turn.rs` | `cellid_and_federationid_are_distinct_types` | 8 | 0 | **High** |
| `dregg-storage-templates/src/blinded_queue.rs` | `descriptor_validates_against_canonical_program` | 4 | 0* | **Medium** |
| `dregg-storage-templates/src/cap_inbox.rs` | `descriptor_validates_against_canonical_program` | 4 | 0* | **Medium** |
| `dregg-storage-templates/src/programmable_queue.rs` | `descriptor_validates_against_canonical_program` | 4 | 0* | **Medium** |
| `dregg-storage-templates/src/pubsub_topic.rs` | `descriptor_validates_against_canonical_program` | 4 | 0* | **Medium** |
| `dregg-storage-templates/src/relay_operator.rs` | `descriptor_validates_against_canonical_program` | 4 | 0* | **Medium** |
| `teasting/tests/invariants.rs` | `test_constitution_valid_basic` | 3 | 1 (helper) | Low |

*These call `.expect("...")` which panics on failure, so they do assert validity, but they assert only that the descriptor struct validates against its own definition—essentially a compile-time/API-shape check.

**Recommendations**
- Delete `handoff_certificate_validate_via_dregg_captp_api_exists` and `cellid_and_federationid_are_distinct_types`; compilation already enforces both.
- Either delete the `descriptor_validates_against_canonical_program` quintet or replace them with structural assertions (e.g., assert specific field values, not just that validation returns `Ok`).

---

## Anti-Pattern 2: Tautological Tests (Same Input → Same Output)

**Definition:** Tests that assert an output equals itself, or that two values computed by the *same* code path from the *same* inputs are equal.

**Impact:** Passes vacuously; does not verify correctness against an independent oracle.

| File | Test Name | Issue | Confidence |
|---|---|---|---|
| `apps/privacy-voting/src/proposal.rs` | `derive_proposal_id_is_deterministic` | `assert_eq!(derive_proposal_id("hello"), derive_proposal_id("hello"))` — left and right are the same expression. | **High** |
| `teasting/tests/invariants.rs` | `test_routing_consistency` | `governance_commitment` and `runtime_commitment` are both produced by `compute_routes_commitment(&routes_data)`. Asserting equality of two identical computations is tautological. | **High** |
| `teasting/tests/bridge_four_phase_extended.rs` | `portable_note_carries_every_public_input_for_verifier_closure` | Asserts `proof.nullifier == nullifier.0`, `proof.value == 500`, etc., where the left side is literally constructed from the right-side variables moments earlier. | **High** |
| `teasting/tests/cross_federation.rs` | `test_atomic_swap_across_federations` | Several balance assertions (`assert_eq!(alice_a_final.state.balance(), 4000)`) verify state that was just mutated by the *same* setup code; the test does not exercise an adversarial path (e.g., wrong preimage, timeout without reveal) that would catch a bug. | Medium |

**Recommendations**
- Replace `derive_proposal_id_is_deterministic` with a test that compares against a hard-coded known-good hash (golden value).
- Replace `test_routing_consistency` with a test that mutates one side and asserts inequality, or uses an independent Merkle-root oracle.
- For `portable_note_carries_every_public_input_for_verifier_closure`, either delete or assert properties that are *not* trivially equal to the constructor inputs (e.g., signature validity).
- For the atomic-swap test, add adversarial cases: wrong preimage rejected, timeout without reveal leads to refund.

---

## Anti-Pattern 3: Roundtrip Tests Without Edge Cases

**Definition:** Serialize → deserialize → assert equality. Never tests malformed input, truncation, or version mismatch.

| File | Test Name | Lines | Confidence |
|---|---|---|---|
| `apps/gallery/src/private_vickrey.rs` | `test_label_serialization_roundtrip` | 5 | **High** |
| `apps/gallery/src/private_vickrey.rs` | `test_phase3_encryption_roundtrip` | 5 | **High** |
| `apps/privacy-voting/src/ballot.rs` | `reveal_roundtrip` | 7 | **High** |
| `apps/subscription/src/crypto.rs` | `roundtrip_alice` | 7 | **High** |

**Recommendations**
- Add adversarial cases: truncated bytes, flipped bit, wrong key, empty payload.
- If the codec is `serde`-derived, consider deleting the roundtrip test entirely and relying on `serde_test` or fuzzing.

---

## Anti-Pattern 4: Tests Asserting Implementation Details

**Definition:** Tests reach into private or semi-private fields (`state.fields[0]`, `delegation.snapshot`, `receipt.derivation_records`) rather than verifying observable behavior.

**Impact:** Brittle on refactoring; changing internal representation breaks tests even when behavior is correct.

| File | Test Name | Fields / Details Asserted | Confidence |
|---|---|---|---|
| `teasting/tests/cross_federation.rs` | `test_atomic_swap_across_federations` | `state.balance()`, `state.fields[0]` | **High** |
| `tests/src/full_pipeline.rs` | `test_full_delegation_and_revocation` | `child_cell.delegation`, `delegation.snapshot`, `receipt.derivation_records` | **High** |
| `tests/src/full_pipeline.rs` | `test_full_note_lifecycle` | `note.asset_type()`, `note.value()`, `witness.commitment()`, `witness.nullifier()` | **High** |
| `tests/src/dfa_circuit.rs` | `test_dfa_valid_trace_proves_and_verifies` | Field-level trace assertions (script-detected) | Medium |
| `teasting/tests/storage_faults.rs` | `inbox_eviction_race_check_then_act` | Internal inbox state fields (script-detected) | Medium |
| `teasting/tests/storage_lifecycle.rs` | `tampered_dequeue_proof_rejected` | Internal queue proof fields (script-detected) | Medium |
| `tests/src/sovereign_proof.rs` | `test_backward_compat_witness_path_still_works` | Internal witness path structure (script-detected) | Medium |

**Recommendations**
- Replace field assertions with public API assertions (e.g., `ledger.get_balance(id) == expected`).
- If the field is intentionally public, document the stability guarantee; otherwise make it `pub(crate)` and test via the public surface.

---

## Anti-Pattern 5: Duplicate Tests (Identical Bodies Across Files)

**Definition:** Multiple tests share the exact same body, usually because they are copy-pasted placeholders.

**Impact:** Inflates test count, slows compile times, hides real coverage gaps.

### Mass Duplicate Stub Epidemic

**~151 `#[ignore]` placeholder tests** across 13 files share the identical body `panic!("blocked")`. These are not tests; they are TODO items masquerading as code.

| File | `panic!("blocked")` Count |
|---|---|
| `tests/src/executor_honesty_threats.rs` | 21 |
| `tests/src/sovereign_witness_threats.rs` | 19 |
| `tests/src/gamma2_bilateral_binding.rs` | 19 |
| `tests/src/witnessed_predicate_kinds.rs` | 18 |
| `tests/src/state_constraint_variants.rs` | 16 |
| `teasting/tests/adversarial_federation.rs` | 12 |
| `teasting/tests/cross_federation_captp_turn.rs` | 11 |
| `teasting/tests/silver_vision_substrate.rs` | 10 |
| `tests/src/authorization_variants.rs` | 7 |
| `tests/src/state_constraint_executor.rs` | 6 |
| `tests/src/state_constraint_composition.rs` | 6 |
| `tests/src/slot_caveat_composition_stress.rs` | 3 |
| `teasting/tests/bridge_four_phase_extended.rs` | 3 |

### Cross-File Duplication of Non-Ignored Tests

| Test Name | Files |
|---|---|
| `grant_sender_action_shape` | `dregg-storage-templates/src/programmable_queue.rs` (duplicates `cap_inbox.rs`) |
| `descriptor_validates_against_canonical_program` | `blinded_queue.rs`, `cap_inbox.rs`, `programmable_queue.rs`, `pubsub_topic.rs`, `relay_operator.rs` |

**Recommendations**
- **Delete all `panic!("blocked")` stubs.** Track unimplemented integration tests in a single markdown file (e.g., `teasting/TODO.md`) rather than as individual test functions.
- Merge the `grant_sender_action_shape` duplication into a single parameterized test in a shared test module.
- Merge the `descriptor_validates_against_canonical_program` quintet into one test that iterates over all five descriptors.

---

## Anti-Pattern 6: Tests with No Meaningful Assertions

**Definition:** Tests (or example binaries run as tests) that execute large amounts of setup code but never verify the final state, or verify only that no panic occurred.

### `demo-agent/examples/` — Setup-Only Binaries

These are run as integration tests in CI. Many have **0 assertions** and 200–900 lines of setup/print logic.

| File | `main()` Lines | Assertions | Confidence |
|---|---|---|---|
| `demo-agent/examples/bench_summary.rs` | 525 | **0** | **High** |
| `demo-agent/examples/intent_lifecycle.rs` | 579 | **0** | **High** |
| `demo-agent/examples/progressive_disclosure.rs` | 311 | **0** | **High** |
| `demo-agent/examples/cipherclerk_lifecycle.rs` | 226 | 1 | **High** |
| `demo-agent/examples/multi_silo_budget.rs` | 380 | 1 | **High** |
| `demo-agent/examples/web_auth_flow.rs` | 326 | 1 | **High** |
| `demo-agent/examples/unified_harness.rs` | 200 | 0 | **High** |
| `demo-agent/examples/cross_fed_atomic.rs` | 367 | 12 | Low |
| `demo-agent/examples/cross_federation_nft_swap.rs` | 532 | 9 | Low |

*Note:* Some examples with >1 assertions still spend 90% of their lines on setup and print logic, but the assertion count alone does not make them “setup-only.” The worst offenders are those with **0 assertions**.

### Short Tests with Zero Assertions

| File | Test Name | Lines | Confidence |
|---|---|---|---|
| `teasting/tests/fuzz_captp.rs` | `test_fuzz_captp_gc_500_actions` | 9 | **High** |
| `teasting/tests/fuzz_captp.rs` | `test_fuzz_captp_interleaved_import_export` | 14 | **High** |

*Note:* `teasting/tests/invariants.rs` contains several tests (`test_nullifier_uniqueness_basic`, `test_directory_version_monotonicity_basic`, `test_gc_consistency_basic`) that were script-flagged as 0-assertion, but they call helpers (`assert_no_double_spend`, `assert_directory_version_monotonicity`, `assert_gc_consistency`) that contain assertions internally. These are **false positives** from the static heuristic and are not listed above.

**Recommendations**
- Convert setup-only examples into real integration tests with state assertions (e.g., assert final ledger balances, assert STARK verification result).
- If an example is purely demonstrative/print-based, move it out of the test path (e.g., to `examples/demo/`) and exclude it from CI coverage.
- Delete or add assertions to `test_fuzz_captp_gc_500_actions` and `test_fuzz_captp_interleaved_import_export`; otherwise they only test that the code does not panic on a fixed input.

---

## Anti-Pattern 7: Overspecified Error Messages (Exact String / Variant Equality)

**Definition:** Tests assert that an error equals an exact string or an exact enum variant, rather than checking the *category* of error. This breaks whenever error text is reworded or a new variant is introduced.

| File | Test Name | Exact Match | Confidence |
|---|---|---|---|
| `teasting/tests/defi_primitives.rs` | `test_commit_reveal_frontrunning_rejected` | `assert_eq!(err, CommitRevealFulfillmentError::NoCommitment)` | **High** |
| `teasting/tests/defi_primitives.rs` | `test_commit_reveal_wrong_secret_rejected` | `assert_eq!(err, CommitRevealFulfillmentError::SecretMismatch)` | **High** |
| `teasting/tests/defi_primitives.rs` | `test_value_commitment_inflation_rejected` | `assert_eq!(err, ConservationError::SignatureInvalid)` | **High** |
| `teasting/tests/defi_primitives.rs` | `test_value_commitment_wrong_message_rejected` | `assert_eq!(err, ConservationError::SignatureInvalid)` | **High** |
| `apps/gallery/src/private_vickrey.rs` | `test_cannot_evaluate_twice` | `assert_eq!(err, "already evaluated")` | **High** |
| `apps/gallery/src/private_vickrey.rs` | `test_cannot_evaluate_without_all_bids` | `assert_eq!(err, "not all bids received")` | **High** |
| `apps/gallery/src/private_vickrey.rs` | `test_federated_single_node_cannot_decode` | Exact error string matching (pattern in body) | **High** |
| `teasting/tests/cross_federation.rs` | `test_atomic_swap_across_federations` | `assert_eq!(replay_result, ConditionalResult::InvalidProof("proof already used".to_string()))` | **High** |

**Recommendations**
- Replace `assert_eq!(err, ExactVariant)` with `assert!(matches!(err, ExactVariant))` so the test still passes if a wrapper variant is added.
- Replace `assert_eq!(err, "exact string")` with `assert!(err.contains("already evaluated"))` or, better, return a typed error enum and match on the variant.
- For `ConditionalResult::InvalidProof("proof already used")`, match on `InvalidProof(_)` and assert the message contains the keyword, or split `InvalidProof` into `InvalidProof::AlreadyUsed` and `InvalidProof::Other(String)`.

---

## Anti-Pattern 8: Tests That Are Purely Setup Code

**Definition:** Tests that spend the vast majority of their lines constructing fixtures, mock networks, or print statements, with only a token assertion at the end (or none at all). These are often “smoke tests” that verify the setup code compiles and runs, but they do not verify business logic.

This anti-pattern heavily overlaps with Anti-Pattern 6. The distinguishing factor is **proportion**: >90% setup, <10% verification.

| File | Test / `main()` | Total Lines | Assertions | Setup % |
|---|---|---|---|---|
| `demo-agent/examples/bench_summary.rs` | `main` | 525 | 0 | ~100% |
| `demo-agent/examples/intent_lifecycle.rs` | `main` | 579 | 0 | ~100% |
| `demo-agent/examples/progressive_disclosure.rs` | `main` | 311 | 0 | ~100% |
| `demo-agent/examples/cipherclerk_lifecycle.rs` | `main` | 226 | 1 | ~99% |
| `demo-agent/examples/multi_silo_budget.rs` | `main` | 380 | 1 | ~99% |
| `demo-agent/examples/web_auth_flow.rs` | `main` | 326 | 1 | ~99% |
| `demo-agent/examples/unified_harness.rs` | `main` | 200 | 0 | ~100% |
| `demo-agent/examples/cross_federation_nft_swap.rs` | `main` | 532 | 1 | ~99% |
| `teasting/tests/cross_federation.rs` | `test_atomic_swap_across_federations` | 218 | 16 | ~85% |

**Recommendations**
- Extract setup into shared `TestHarness` or `fixture!` macros so each test expresses intent in ≤20 lines.
- Add adversarial assertions: after the happy-path setup, mutate one variable and assert failure.
- For examples, either convert them to true integration tests (state assertions, not `println!`) or move them to `examples/` and remove from coverage.

---

## Confidence & Methodology Notes

| Heuristic | False-Positive Risk | Mitigation |
|---|---|---|
| Line count + assertion count | **High** for tests that call helper macros (e.g., `assert_no_double_spend`) | Manual review of flagged tests; legitimate helpers were removed from the final list. |
| `#[ignore]` + `panic!("blocked")` | **Low** | Every occurrence was verified via `grep`; body is unambiguous. |
| Exact error string matching | **Low** | Direct pattern match on `assert_eq!(..., "...")` or `assert_eq!(..., Enum::Variant)`. |
| Field access detection | Medium | Manual review of top 20 flagged tests; some public-API getters were deemed acceptable. |

---

## Prioritized Remediation Roadmap

1. **Immediate (low effort, high impact)**
   - Delete all `panic!("blocked")` stubs (~151 tests across 13 files).
   - Delete `handoff_certificate_validate_via_dregg_captp_api_exists` and `cellid_and_federationid_are_distinct_types`.
   - Replace exact error-string assertions in `defi_primitives.rs` and `private_vickrey.rs` with `matches!` or `contains` checks.

2. **Short-term (medium effort)**
   - Convert the 7 worst setup-only `demo-agent/examples/` binaries into real integration tests with state assertions, or move them out of the test path.
   - Merge duplicate `descriptor_validates_against_canonical_program` and `grant_sender_action_shape` tests into parameterized tests.

3. **Medium-term (higher effort)**
   - Refactor `test_atomic_swap_across_federations` to use a public API rather than direct field access, and add adversarial paths (wrong preimage, timeout without reveal).
   - Add edge-case coverage to roundtrip tests (truncation, bit-flip, wrong key).
   - Extract shared setup code in `full_pipeline.rs` and `cross_federation.rs` into reusable harnesses.

---

*End of report.*
