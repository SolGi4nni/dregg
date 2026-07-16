# EXCELLENCE BACKLOG — 2026-07-16

Mined from the documentation campaign: the ~600 doc-vs-code findings, the
rewrite-phase adversarial-verify results, and the HORIZONLOG sweep, filtered to
findings that name an ENGINEERING wound (something to build/fix/gate/plan) rather
than mere doc drift. A doc that lied because the *system* has a hole is a work
item; a doc that lied because time passed is not.

Ranked by value. "CHEAP" = under a day; "LANE" = its own workstream. Items marked
✓verified were re-checked against code at HEAD on 2026-07-16.

## LANDED (2026-07-16 continuation)

Fixed + committed this session (each verified; teeth where applicable):
- **#1 TurnExecuted** (`856f8e4df`) — verifier now checks the executor's canonical
  message; the vacuous green test corrected + a reject-the-bare-hash tooth added.
- **#6 endpoints default** (`1c269ce5c`) — SDK defaults + lib doc repointed off the
  dead fg-goose host onto the dregg.net product family.
- **de-fossil** (`ac444e13d`) — three stale comments corrected (cohort widths
  1581→1647; ShieldedClearing endpoint descriptor BUILT not NAMED; wasm p3-rev).
- **missing gates** (`+ gitleaks/docs-refs/p3-rev`) — doc ref-integrity linter,
  plonky3-rev single-source, gitleaks-in-CI.
- **bridge-conservation alert** (`c6ceadbcd`) — restored as a real seam-gated rule.
- **#10 zkOracle binding, honestly reframed** (`772a6bf3f`) — deep-read REVERSED the
  premise: the cross-leg binding is DEPLOYED (`zkoracle-prove/src/attestation.rs`
  `content_commitment` + `CrossLegMismatch` + committed-substring), not absent — the
  Lean theorem is just weaker than the code. Doc now states that gap accurately.

Two soundness lanes deep-scoped this session (fix-shapes, ready to drive):
- **zkOracle cross-leg-binding lane** — lift the deployed `content_commitment`
  binding into `zkOracle_sound`: model a shared `contentCommitment` witness the
  three legs each bind to. HARD PART: the legs are three type universes
  (`PaymentFacts` / `List T` / `List Value`) with no common substrate — needs them
  unified onto a byte-response model before a binding hypothesis is faithful.
- **cap-graph non-amp emit lane** — `circuit/src/cap_delegation_nonamp_descriptor.rs`
  test `nonamp_leg_does_not_bind_the_hashed_rights_felt:411` pins the defect: col 4
  (`DELEG_GRANTED_MASK_RECON_COL`, the reconstructed granted mask) and col 72 (the
  rights felt `siteCapEdgeLeaf` hashes) are related by NO constraint, so a prover
  can tamper the rights felt while keeping granted bits honest → confer arbitrary
  rights. FIX: add a binding constraint (col 4 ↔ col 72) in the LEAN EMIT (law #1 —
  the descriptor is Lean-emitted, loaded here), regen the descriptor, flip the two
  pinning tests red→correct. Latent (descriptor UNWIRED), so no VK epoch, but it IS
  a descriptor regen. `state_commit` group-4 chain misindex (`:508`) rides the same
  emit pass.

New follow-up lanes surfaced while fixing (each named, none laundered):
- **RECURSION_P3_REV drift** — the VK-hash constant (`c14b5fc0…`) has ALREADY
  drifted from the authoritative fork pin (`0a4a554e…`): the VK-custody wound made
  real. `check-p3-rev.sh` WARNs on it. Fix re-keys the VK → ember's ceremony call.
- **bridge must emit `dregg_bridge_conservation_ok`** — the alert is gated on a
  metric `bridge/` does not yet emit (node emits 30 dregg_* metrics, none bridge).
- **`docs/THE-GRAIN.md` + `docs/ASSURANCE.md`** — dead refs across ~12 grain-*
  crates; the grain R-ladder is a real present feature, so CREATE the docs.
- **468 dead doc refs** — cleanup pass, then re-enable the docs-refs PR trigger.
- **repo-wide fg-goose sweep** — discord bot, TUI, deploy Caddyfile still carry it.
- **ShieldedRingDescriptorRefines** — the serialized-trace→apex refinement residual
  the ShieldedClearing header keeps named; a candidate closure lane.

Held for careful single-driver / ember: **cap-graph non-amp emit** and **zkOracle
binding** (Lean, need build cycles); **VK custody** (commitment-shaped, ceremony
sequencing); **Custom-VK cluster** (another terminal actively driving it).

## Biggest single-day wins

### 1. `TurnExecuted` verifies the WRONG signing message — CHEAP ✓verified
The conditional verifier checks ed25519 over the **bare** `receipt.receipt_hash()`
(`turn/src/conditional.rs:491-498`), while the executor signs the domain-prefixed
v3 message `b"executor-receipt-sig-v3:" ++ receipt_hash` (`turn/src/turn.rs:1062`,
`executor/mod.rs:1635`). An honest executor-signed receipt can therefore **never**
satisfy a `TurnExecuted` proof condition. Live correctness bug.
**Move:** verify over `canonical_executor_signed_message()`; keep a legacy branch
only if old receipts must validate; green/red test pair (honest satisfies,
tampered rejects).

### 6. Public verify surface is dead-by-default — CHEAP ✓verified
`sdk/src/endpoints.rs:51-57` still defaults every host to the dead
`*.dregg.fg-goose.online`; that default projects into `verify-badge.js`,
`transclude.js`, `transclusion/index.html`, and `manifest-firefox.json`. The site
JS was de-staled today (configurable endpoint, honest empty state), but the SDK
ROOT is untouched, so anything reading the default still points at a dead host.
**Move:** kill the SDK default (honest no-endpoint error, matching
`extension/src/endpoints.ts:22`); scrub remaining JS/manifest projections; fix
`~/dev/dregg-site` claims upstream (incl. the 404 template's double-escaped og:url).

### 7. agent-platform demo 404s on its headline button — CHEAP
`play.html` is served from the bin at `GET /`, but its run flow POSTs
`/keyless-drive` — a route that exists only in a dev-only Python sidecar with a
hardcoded laptop path (`agent-platform/src/serve.rs:349,766`;
`demo/keyless-grain-proxy.py:9`). Served from the bin, the headline flow always
fails. Related: `dregg-agent` CLI still drives *unminted* `run_goal`.
**Move:** implement `/keyless-drive` in serve.rs (or rewire onto `/drive`+`/act`);
route the CLI through the minted path.

### 8. Federation-id derivation fork hazard — CHEAP
Genesis derives `federation_id` via `derive_federation_id_hybrid_with_epoch`
(`node/src/genesis.rs:95`), but the add-validator reroll still uses the ed-only
derivation (`federation/src/identity.rs:65`) — divergent federation ids after any
membership change, undermining the PQ hybrid identity the redteam work just
migrated onto.
**Move:** route reroll through hybrid derivation + a genesis-id == rerolled-id
test over the same roster.

### 12. DFA route-commitment relay: the two-edit closure, undone a month — CHEAP
`route_circuit_vk` exists nowhere and `DslCircuitDfaVerifier` is never registered
in `node/src` (the relay's Dfa caveat is fail-closed, so safe — but the built
verifier is dead machinery). HORIZONLOG L4341.
**Move:** mint `route_circuit_vk`, register the verifier in executor setup, one
relay test.

### 13a. Full-ledger clone per HTTP request — CHEAP
`post_evaluate_proposal` clones the *entire ledger* on every
`/turn/atomic/evaluate` (`node/src/api.rs:6471`; the cfg(test)-only claim is false).
**Move:** `begin_restore_point()` O(touched) pattern.

## Highest-stakes lanes

### 2. Discord payments run on a MockWatcher; the bot holds the seed — LANE ✓verified
Both `PayState` constructors unconditionally build `MockWatcher`
(`discord-bot/src/pay.rs:445`) — real on-chain $DREGG/USDC deposits credit no one;
the real `SolanaWatcher` is never constructed. The bot process also loads
`DREGG_PAY_SEED`, making it custodian rather than watch-only.
**Move (PAYMENTS-GO-LIVE):** construct SolanaWatcher from env; split seed custody
into a separate sweeper service; put MockWatcher behind an explicit devnet flag.
Textbook fixture-on-a-live-path.

### 3. The Custom-VK path — three connected circuit holes (one weld cluster) — LANE
The deployed custom `proofBind` gate is still a vacuous `True` with the real
`boundAt` verifier only STAGED (`CustomApex.lean:7-10,50`,
`proof_verify.rs:957`); `customVmDescriptor2R24`'s welded twin is **unsatisfiable**
(4th `LIVE_ONLY_BARE_KEYS` member — custom turns permanently exempt from the
welded requirement, `proof_verify.rs:620`); and the chain fold's custom arm folds
the commitment-only node while the built, both-polarity-tested state-binding node
(`prove_custom_binding_node_state_segmented`) sits unrouted
(`ivc_turn_chain.rs:2868`). An in-flight lane is suggested by the untracked
`circuit-prove/tests/custom_state_binding_cross_pin.rs` — finish it.
**Move:** thread the umem/state witness through the custom leaf so the welded twin
is satisfiable; wire the state-binding node into the fold; flip proofBind
True→boundAt at the next VK epoch. **This is the path complex game mechanics ride.**

### 4. Solana bridge — the 3 P1 suspects, now with verbatim locations — LANE (relabel = CHEAP)
Sharpens the known P1 close-value-holes: (1) `rotate()` admits the next epoch's
stake table via `verify_supermajority` *without* the `tally_authorized` voter
binding (`solana_provenance.rs:697-726`, its own doc admits it); (2)
`derive_stake_table` proves inclusion of supplied accounts only, no completeness
floor, so an omitted-stake rotation shrinks the ≥2/3 denominator (`:457-527`); (3)
`ConsensusEvidence.slot` is doc-labeled "finalized" while the verified relation is
exact-slot optimistic confirmation — a fossil over-claim in code
(`solana_trustless.rs:69-75`).
**Move:** named adversarial-test lane per suspect; relabel the field-doc now (cheap).

### 5. EVM value contracts — slasher drain + placeholder tree + mock selector — LANE
Sharpens rung-1 launchpad (critical path): `DreggDeployerGate.slash()` lets an
admin-appointed slasher move pooled bond ETH to an arbitrary recipient with zero
invariant/Halmos coverage (`launchpad/DreggDeployerGate.sol:44`); `DreggVault`'s
Merkle tree is the labeled keccak stand-in with O(n) `_computeRoot` on a
value-holding contract; `chain/src/withdraw.rs:291` carries a mock selector.
**Move:** slash invariant tests (≤ that deployer's bond, no cross-deployer drain) +
timelock; bound/replace the placeholder tree; real selector + tooth.

### 9. cap-graph GENUINE-NON-AMP descriptor — pinned defects, fix never landed — LANE ✓verified
The non-amp leg doesn't bind the hashed rights felt and its state_commit group-4
chain is misindexed; tests *pin the wrong behavior* awaiting a Lean emit fix
(`cap_delegation_nonamp_descriptor.rs:411,508`). Latent (unwired) — but wired, a
prover could confer ANY rights.
**Move:** land the Lean emit fix (`EffectVmEmitCapReshape.lean` /
`EffectVmEmitAttenuateA.lean`); the two pins flip red → that red IS the fix.

### 10. `zkOracle_sound` has no cross-leg binding — LANE
The theorem quantifies over an independent `decoStmt` and independent `body` with
no connecting hypothesis — the three conjuncts can be about different data
(`ZkOracle.lean:77-93`). Binding is absent, not "an explicit hypothesis."
**Move:** add the shared-commitment binding (DECO `encode facts` = the CFG input's
Poseidon2 commitment); thread it as a shared witness in the deployed circuit.

### 11-VK. VK custody folds only ONE content-derived component — CHEAP→LANE ✓verified
Of the four components folded into the recursive VK hash
(`recursive_witness_bundle.rs:135-172`), only the AIR descriptor fingerprint is
content-derived. `RECURSION_P3_REV` and the verifier-surface label are
**hand-mirrored strings** ("bumping the rev without bumping this string would
silently let old recursive proofs verify against new code"), and
`RECURSIVE_VK_PROGRAM_BYTES` is a constant label. A forgotten bump ships a changed
verifier under an unchanged VK — the exact custody property the pin exists to
provide.
**Move (do before the freeze ceremony pins anything):** content-hash all four
components (git-blob-hash the verifier source + program bytes; derive the rev from
the locked manifest).

## The missing-gates bundle — each kills a whole finding class

- **Docs/code ref-integrity linter** (LANE) — the dominant class this campaign:
  dozens of `file:line` pins drifted, dead paths (`docs/THE-GRAIN.md`,
  `docs/ASSURANCE.md`) referenced. Fail on missing file, warn on missing symbol.
  Arm it now while the corpus is clean, so it ratchets from green.
- **plonky3 rev single-source** (CHEAP) — CI pins `REV=0a4a554e` in 3 workflows
  while `wasm/Cargo.toml:252` instructs a *different* rev. One env/file + grep gate.
- **gitleaks in CI** (CHEAP) — `.gitleaks.toml` is enforced only by local hooks.
- **Rewrite-artifact grep** (CHEAP) — literal tool-call fragments were committed in
  ≥4 docs (cleaned); a pre-commit grep over docs/+site/ prevents recurrence.
- **S2 `--ignored` gauntlet** (LANE) running the 8 deployed binding teeth — owed
  twice (HORIZONLOG L8645+L8710); prevents the stale-teeth (4 RED harness) incident.
- **`dregg_mcp` effects-catalog exhaustiveness test** (CHEAP) — hardcoded 31-entry
  list vs 34 Effect variants, with a doc-comment claiming it never drifts
  (`dregg_mcp.rs:1186` vs `action.rs:1061`).
- **Bridge-conservation alert** (CHEAP) — `BridgeConservationBreach` exists only as
  a comment in the Prometheus rules; no page for the worst bridge failure class.
- **Status-boards-are-not-docs** (register law) — every per-row status table
  audited (`ALG-COMPLEXITY-AUDIT`, `WELD-STATE`) was wrong in both directions.
  Status lives in HORIZONLOG + gates; docs teach what-is.

## Fossil-comment sweep — code carrying the same lies the docs did — CHEAP (one pass)
`turn_proving.rs:2767` "broken" beside a closed seam; stale 1626 cohort-width in
`bare_floor_refuse_weld.rs` (real 1647/1692+); `ShieldedClearing.lean:60` claims
the endpoint descriptor is named-not-built while `ShieldedRingEndpointDescriptor`
is deployed; the `EffectVmEmitRotationV3.lean:5759` bare-transfer-face comment.
One sweep lane, each with the correct current-resolution sentence.

## Built-but-unwired sweep — decide delete-vs-wire, mostly CHEAP each
Checkpoint pipeline (`store_checkpoint` zero callers — likely delete, superseded by
the attested-root quorum); cockpit Trust card renders `TrustPanel::demo()` not the
ledger; deos-chat `WorkerRequest::SendMessage` doesn't exist; dregg-dsl differential
drives a re-derived mirror not the emitted `{Name}P3Air` (mirror-verification sin);
extension `defaultResolveObject` fixture-only on the live surface; `deos-js/src/mud.rs`
never declared; cosmos-lightclient has no `[[bin]]`.

## Sharpeners for tracked workstreams (NEW only)
- **P0 repro build:** `scripts/fetch-lean-seed.sh:148` installs UNVERIFIED when the
  .sha256 sidecar is missing — make missing-sidecar fail-closed (CHEAP); the lassie
  recipe's step-0 values no longer match `lean-seed.pin`.
- **P1 freeze / VK ceremony:** no governance-pinned `RecursionVk` constant+assert
  (HORIZONLOG L8423); **no value-bearing Transfer has ever traversed the full wrap**
  — one recorded Transfer-apex wrap run is the cheap decider.
- **Ops pre-launch:** every `docs/ops/` runbook grounds on the SUPERSEDED deploy/aws
  systemd topology — an operator mid-incident hits not-found on every command. One
  re-grounding pass onto the real docker-compose edge (LANE).
