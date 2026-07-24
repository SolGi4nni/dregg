# Class-Completion Hunt — 2026-07-24 (remaining instances of the 4 HEAD-health classes)

The HEAD-health audit found 4 dangerous classes; we fixed the known instances. This read-only hunt
found the REST (fix the class, not the instance). Ranked most-dangerous first.

## TOP 5
1. **CLASS 1 — `federation/src/revocation.rs:151` `RevocationVerifier::verify` = revocation bypass.**
   The root is read OFF the proof (`proof.attested_root.merkle_root`); "quorum" is a NON-crypto count
   (`quorum_signatures.len() >= threshold`, never verified — `types/src/lib.rs:597,606-614`). A fabricated
   `RevocationProof` (any merkle_root + junk unverified signatures + a valid non-membership proof against
   THAT chosen root + small threshold) → `valid:true` → a revoked token shows "not revoked". LATENT (only
   re-exported `federation/src/lib.rs:171`, no runtime caller) but a public API on a default member — one
   wire-up = live forgery. FIX: gate on a trusted committee like the sound sibling
   `federation/src/federation.rs:328 verify_attested_root` (`root.is_valid(&self.members)`), or DELETE the
   vacuous API. Template: `credentials/src/revocation.rs:229`.
2. **CLASS 2 — `sandstorm-bridge/tests/real_spk_fixture.rs` silent-disable.** `sample.spk` is
   gitignored/untracked → `load_fixture()→None→return` reports GREEN; the anti-tamper reject tooth
   (`a_tampered_real_spk_is_refused`) + e2e parse tooth assert NOTHING. FIX: commit a real signed
   `sample.spk` (LFS) so the teeth run, OR make absence a hard `panic!`/`#[ignore]` (never a silent `return`).
3. **CLASS 3 — a committed migration wave leaves 3 default-member LIBs broken + soundness tests DARK.**
   Incomplete `usize→u64` SetField index widening (`turn/src/builder.rs:624`, commit d1e4ac3d58) +
   `WholeChainProofBytes.board_window` (953a746cab) + `Effect::{CreateHybridCell,RotatePqIdentity}` +
   `StateConstraint::FieldsCountEquals` non-exhaustive matches. Broken LIBs: **deos-js-runtime, dregg-node,
   starbridge-v2** (+ starbridge-identity/nameservice/web-surface, dregg-coord tests). Worse, the SOUNDNESS
   test binaries **`teasting predicate_soundness`, `teasting protocol_coverage_gate`, `sdk
   sovereign_rotated_wide`** don't compile → their teeth CANNOT RUN. CLASS 3 silently feeds CLASS 2/4.
   (circuit/circuit-prove failures are entangled with THIS-session WIP — dirty — leave them.) These are
   type/import breaks, none itself a soundness hole, but they dark the tests that would catch soundness holes.
4. **CLASS 2 — `tee-verify/tests/nitro_real.rs:34,42` vacuous-negative.** `verify_nitro_core(mutated).is_err()`
   with NO in-test positive baseline → if `nitro_att.bin` drifts, mutation fails anyway → passes for the
   wrong reason. FIX: assert the UNMUTATED `REAL_DOC` verifies first, then the mutation is refused.
5. **CLASS 4 — `exec-lean/tests/lean_state_producer_coverage.rs:384` `#[ignore]`d falsifier FAILS TODAY.**
   `produce_via_lean` commits `root != pre_root` on the Lean-commits/Rust-rejects `RevokeDelegation`
   residual (execute_via_lean correctly leaves pre_root). A real producer-path state-commitment divergence,
   honestly labeled — and doubly dark (crate is also a CLASS 3 non-compile). Un-dark it via CLASS 3, then
   the falsifier's real failure is exposed.

## CLASS 1 also (documented, sound-as-used — standing hazards)
- `sdk/src/privacy.rs:790 verify_predicate_unlinkable` (x==x, but a huge ⚠SAFETY block; only consumer is
  the CUSTODIAL `/credential verify` at `discord-bot/src/identity_proof.rs:287` where custody makes it OK).
  Hazard: any NON-custodial caller must use `verify_predicate_proof_third_party`. Add a custody type-marker.
- `wasm/src/lib.rs:736` (workspace-EXCLUDED browser demo; caller-supplied fact_commitment from the prover's
  own output = x==x in the demo flow). Doc/typing only.
- SOUND (checked, not vacuous): bridge present.rs {2928,3017,3185}, sdk/verify.rs, federation.rs {311,328},
  token/revocation.rs:327 (hybrid, pins enrolled key), credentials/revocation.rs:217, sdk privacy.rs:815.

## CLASS 2 also — benign/guarded (cleared): the other tee-verify files, circuit exact_nullifier (SHA-pin
non-vacuity guard, exemplary), the include_bytes! source self-hash pins. `tdx_chutes.rs:143` real DCAP is
`#[ignore]+collateral-fetch` (dormant, capture a fixture for offline crypto verify).

## CLASS 4 — census: 0 clear-cut silenced (a), 2 boundary (the exec-lean one above + node
submit_queue_drainer.rs:632 durability-atomicity, a WEAK falsifier over a live hole — no crash-window
inject so likely passes), ~22 documented-blocked (tests/src/gamma2/sovereign/executor/state_constraint
`panic!("blocked")`, node dfa_relay_closure honest-path regression, circuit cap_open self-verify stale IR-v2),
~125 legit slow/GPU/live/soak. NOT holes (comment refs): intent fulfillment.rs:2347 (now live+un-ignored).
