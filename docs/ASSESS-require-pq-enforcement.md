# Assessment: require_pq enforcement — deployable now?

Read-only assessment (2026-07-24) of the ONE named PQ residual: `require_pq`
"DEFAULT-OFF, verified-when-present but not enforced." Connects to
[[project-pq-metatheory-connected]].

## Verdict: ALREADY ENFORCED AT THE NODE (the premise is stale)

The residual as stated is **stale for the deployed node.** The `AtomicBool::new(false)`
at `turn/src/executor/mod.rs:1249` / `:1332` / `:1385` is the **bare-library**
default only. The NODE flips it ON by default at both authoritative admission
chokepoints via `node/src/executor_setup.rs:634 require_pq_admission`:

- `new_submit_executor` (`executor_setup.rs:601`) → HTTP submit ingress, queue
  drainers, `commit_effects_as`, services (all the `api.rs` / `submit_queue_drainer.rs`
  / `equivocation_court_service.rs` submit sites).
- the blocklace finalized-turn executor (`blocklace_sync.rs:6173`) → the cross-node
  authoritative commit path.
- deliberately **NOT** `new_verify_executor` (`executor_setup.rs:645`) — read/proof
  re-execution replays already-admitted (possibly pre-flip classical) history.

The flip landed in commit `46536d7bcf` (2026-07-16, "require_pq ON by default
(approved) … blast radius measured = 0"), ember-approved, blast radius measured
empirically (node `--lib` suite ON vs OFF → identical failures, ON-only diff empty).

`pq_admission_required` (`executor_setup.rs:605`) makes the default ON and is
fail-safe: it only returns OFF when **both** `DREGG_REQUIRE_PQ=0` **and**
`DREGG_ALLOW_UNAUDITED_PQ=1` are set (the explicit unaudited migration window).
`DREGG_REQUIRE_PQ=0` **alone never downgrades a native node.**

The genuinely-open items are (a) **doc drift** — `docs/PQ-CRYPTO.md §4` and the
doc-comments at `turn/src/pq.rs:31-32` / `turn/src/action.rs:454-456` still describe
the OLD "default off; node admission MAY require" posture; the node **DOES** require
by default now — and (b) an **onboarding coverage** seam (below), not a soundness gap.

## 1. What require_pq=true REJECTS (a SUBSET, fail-closed)

Two enforcement layers, both gated on `executor.require_pq()`:

**Outer envelope** — `node/src/signed_turn_validation.rs::validate_signed_turn`
(SignedTurn.pq_signature / pq_signer), run at every `new_submit_executor` ingress
and the finalized-turn path:
- no outer PQ signature → `PqSignatureRequired` (`:177-178`).
- outer/inner PQ envelope half-present → `IncompletePqEnvelope` (`:173-174`, both modes).
- PQ present but the **agent (signer) cell** carries no committed `pq_identity()` and
  no host enrollment → `PqIdentityNotEnrolled` (`:209`); agent cell absent from ledger
  under require_pq → `PqIdentityNotEnrolled` (`:211-212`).
- carried key ≠ committed/enrolled key → `SubstitutedPqPublicKey` (`:197`, `:205`).
- present-but-invalid PQ signature → `InvalidPqSignature` (`:230-231`), **fail-closed
  regardless of require_pq**.

**Inner action auth** — `turn/src/executor/authorize.rs::verify_hybrid_signature`
(+ the `AuthRequired::Signature`/`::Either` arms), reached only by ed25519/hybrid
**signature-authorized** actions (token/proof/custom auth have their own crypto and
are NOT gated by require_pq here):
- classical `Authorization::Signature(..)` under require_pq → `InvalidAuthorization`
  "classical-only signature rejected" (`authorize.rs:706-713`, `:814-821`).
- `HybridSignature` with **absent** PQ half (`ml_dsa` empty) under require_pq →
  "post-quantum signature half required but absent" (`:1125-1131`).
- `HybridSignature`, PQ present, but the **target cell** has no committed
  `pq_identity()` and no enrollment under require_pq → "required post-quantum
  target-cell identity is not committed in the live cell" (`:1103-1110`).
- present-but-invalid PQ half → "ML-DSA-65 signature half failed" (`:1116-1124`),
  **fail-closed regardless of require_pq**.

So enforcement rejects: classical-only turns, hybrid-with-absent-PQ turns, and
signature-authorized turns whose agent/target cell lacks a committed or enrolled PQ
anchor. Honest hybrid turns to PQ-bound cells pass. This is the correct fail-closed
posture for a classical-only identity — not an over-broad reject.

## 2. Is the deployed flow already PQ-complete?

Mostly yes, for the node's own perimeter:
- Rust SDK default signer is hybrid end-to-end: `AgentCipherclerk::sign_turn`
  (`sdk/src/cipherclerk.rs:3103`) always emits outer `pq_signature`/`pq_signer`
  (`:3110-3111`); `sign_action` (`:3279`) defaults to `sign_action_hybrid` (`:3284`)
  → `Authorization::HybridSignature`. `sign_action_classical` has no production callers.
- sdk-ts / sdk-py ride the same hybrid signer (envelope assembled by
  `wasm/src/lib.rs:2234 assemble_signed_turn_envelope` through the SDK serializer).
- Local-clerk cells and federation-roster cells are enrolled unconditionally by
  `enroll_known_pq_identities` (`executor_setup.rs:190`, called at `:349`).
- Cells born via `Effect::CreateHybridCell` (`turn/src/action.rs:1582`) commit a
  `pq_identity` at birth (`cell/src/cell.rs:656 install_pq_identity`) and pass.

The **coverage seam**: the SDK's default `TurnBuilder::create_cell`
(`sdk/src/turns.rs:192`) still lowers to plain `Effect::CreateCell`
(`action.rs:1073`) — **no PQ anchor at birth**. `create_hybrid_cell`
(`turns.rs:205`) is opt-in. So a new external agent cell created through the default
helper is classical-only; a turn signed from it (or targeting it) is rejected under
require_pq (`PqIdentityNotEnrolled` at the envelope, or the target-cell branch at
`authorize.rs:1103`). This is fail-closed-correct, but it means **new-user onboarding
must use hybrid cell creation** to be admissible.

## 3. The enable path

There is **no library default to flip** — the node already enforces. Nothing here is
byte-affecting (no VK / no regen; require_pq is admission policy, not circuit).
Remaining work is doc + onboarding, not a switch:
- **Doc reconciliation (no code):** update `docs/PQ-CRYPTO.md §4` and the
  `turn/src/pq.rs:31` / `turn/src/action.rs:454` doc-comments to say the node
  requires by default (not "MAY require").
- **Onboarding default (SDK, non-circuit):** make the default agent/cell onboarding
  path emit `CreateHybridCell` so new external identities are born admissible under
  require_pq. This is a client-side SDK change, byte-safe at the node.

## 4. Breakage inventory (every require_pq consumer)

| Site | Kind | Honest flow? |
|---|---|---|
| `node/src/executor_setup.rs:634` (admission), `blocklace_sync.rs:6173` | production ON-by-default | the deployed posture; measured blast radius 0 |
| `node/src/signed_turn_validation.rs:177,211` (checks) | production gate | correct |
| `turn/src/executor/authorize.rs:706,814,1103,1125` (checks) | production gate | correct |
| Rust SDK / sdk-ts / sdk-py default signers | hybrid already | pass |
| default `TurnBuilder::create_cell` onboarding | classical cell birth | **would reject** — fix onboarding to hybrid |
| `wasm/*` executors (no `require_pq_admission`) | light-client / verifier / envelope-assembly, default OFF | correct — not an admission node |
| `sdk-ts/test/rust-verifier/src/main.rs:106` | differential test tool (ON+OFF) | test |
| `dregg-sdk-net/src/remote.rs:823,840` | `#[test]` fixtures | test |
| `node/tests/pq_turn_identity_enrollment.rs`, `turn/tests/pq_cell_identity.rs`, `turn/src/executor/authorize.rs:3305+` | tests | test |
| `dregg-lean-ffi/build.rs:2133` `DREGG_REQUIRE_PQ_CORES` | build-time keygen-core gate (unrelated to admission) | n/a |

No production honest flow breaks that the node does not already handle. The one real
seam is external onboarding via the classical `create_cell` helper.

## 5. Recommendation

**ENFORCE = already done (deployed default ON since 2026-07-16).** No flip is owed.
The two remaining, byte-safe, non-circuit items:
1. Reconcile the stale docs (`PQ-CRYPTO.md §4`, `pq.rs`/`action.rs` doc-comments) to
   the actual deployed posture.
2. Default external onboarding to `CreateHybridCell` so new user cells are born
   admissible under require_pq (SDK-side, node byte-safe).

HOLD nothing. The soundness posture is fail-closed and correct today; a
present-but-invalid PQ half already rejects in either mode.

**Caveat (resolution honesty):** enforcement is real admission policy, but the PQ
half's *cryptographic* floor is still the lattice/hash floor documented in
`docs/PQ-CRYPTO.md` (existence-form MSIS/MLWE degenerate at deployed params;
adversary-indexed statement in `CryptoFloorTeeth`). "require_pq ON" means the node
demands a verifying ML-DSA half bound to an enrolled identity — it does not by itself
add cryptographic hardness beyond that floor.

## 6. ⚠ WOUND — the PQ identity authority plane has NO AIR row (coverage gap, 2026-07-25)

§1-§5 assess **admission policy**. This section records what §2's "cells born via
`Effect::CreateHybridCell` commit a `pq_identity` at birth" does **not** say: neither
PQ verb has a circuit.

`Effect::CreateHybridCell` (`turn/src/action.rs:1569`) and `Effect::RotatePqIdentity`
(`:1582`) are the only two verbs that install and advance the committed
`CellPqIdentity { key_epoch, ml_dsa_key_commitment }`. Both are **executor-only**:

- The checks — ML-DSA-65 possession over `pq::cell_pq_{creation,rotation}_message`,
  epoch-zero-at-birth, `expected_epoch` equality, new-key-differs, exactly-+1 with
  overflow refusal — live in `apply_create_hybrid_cell` / `apply_rotate_pq_identity`
  (`turn/src/executor/apply.rs`) and `Cell::{install,rotate}_pq_identity`
  (`cell/src/cell.rs:656` / `:674`). All **trusted Rust**; none is a constraint.
- The anchor **is** bound into committed state — `compute_canonical_state_commitment`
  (`cell/src/commitment.rs:223`) and the 8-felt `authority_residue_bytes` (`:978`)
  both absorb it, so it cannot be omitted or substituted without moving the root.
  **Binding is not constraining:** the root moves, and no circuit says the move was a
  legal rotation.
- **What a light client learns: nothing about the identity op.** The checked EffectVM
  projection (`try_convert_turn_effects_to_vm`) **refuses** turns carrying either verb
  by name (`EffectVmProjectionError::PqIdentityEffect`), so no cohort proof over such a
  turn exists at all. Descriptor refinement / the per-turn fold / cohort-run
  verification all quantify over projected VM effect rows; there is no row here to
  quantify over. Fail-closed and honest — but it means PQ authority is exactly as
  strong as trust in the executor, which is the thing PQ was meant to survive.
- **Partially closed already:** a Lean-authored, Lean-proven rotation authority
  descriptor exists — `dregg-pq-identity-rotation::v1`
  (`metatheory/Dregg2/Circuit/Emit/PqIdentityAuthorityEmit.lean`,
  `satisfied_implies_exact_rotation`; width 127 / 108 PIs / 120 constraints, parsed by
  the production IR2 parser in `circuit/tests/pq_identity_authority_descriptor.rs`).
  It is **not** a `V3_STAGED_REGISTRY_TSV` member, has no producer and no committed VK,
  and its own header says parsing it "does not make the row deployable and does not
  discharge either ML-DSA premise". There is **no** PQ *birth* descriptor, not even
  staged.

**Not a felt-width wound.** `docs/WOUND-felt-width-boundaries-2026-07-19.md` catalogues
32-byte digests NARROWED to ~31 bits at a security boundary; nothing is narrowed here
(the anchor rides its full 32-byte key commitment into the 8-felt authority digest).
This is a **coverage** gap: a kernel verb with no AIR row.

**Live record / drift gate.** The classification is pinned in
`circuit/tests/effect_enum_descriptor_residual_gate.rs` as the
`EXPECTED_REFUSED_RESIDUALS` set, whose `refused_residuals_are_refused_by_the_live_projection`
test executes the production projection (top-level and nested under
`ExerciseViaCapability`) to keep "fail-closed" a checked fact rather than prose. A verb
leaves that set only by gaining a deployed rung.

**Closure route.** Deploy the Lean rotation row (registry membership + producer + VK
epoch) and discharge the ML-DSA premises; author the birth row. Both are VK-affecting.
