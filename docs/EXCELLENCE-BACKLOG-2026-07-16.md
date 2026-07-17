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

### 4. Solana bridge value-holes — CLOSED (corrected 2026-07-16)
⚠ This item is STALE: the three P1 value-holes are **closed at HEAD** (commit
`72561117d`), which the design-census verifier caught. `rotate()` now tallies
through `tally_authorized` (HOLE-3 closed, `solana_provenance.rs:811,831`);
`derive_stake_table` enforces a `StakeBelowHistoryFloor` completeness floor
(HOLE-2, `:530-548`); value release requires the slot proven *rooted* via
`tally_authorized_rooted` (HOLE-1, `solana_trustless.rs:81-104`). The
launch-readiness memory's "3 exploitable Solana holes" is likewise superseded.
**Move:** the only standing lane is a red-team pass that tries to RE-OPEN them
under the new gates (verify the closures bite), not new fixes.

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

## GAME-SURFACES SWEEP (2026-07-16 evening) — the public-facing wounds

**LANDED same evening** (`065f0226d`, `97ea4f8d4`): the ephemeral-web-sessions
residual (FileResumeStore weld, driven both polarities on persvati); G3 (pinned
beacon labeled in every /descent footer + daily warn); G5 (close registered on
/council + /market; honest caveat: no collective()==true offering has a generic
wrapper yet, so live close reports direct mode); G6a for cards.rs (env-gated
explorer base, other fg-goose sites → the sweep lane); G6b (solo FEDERATION_ID
mismatch fails fast at boot). BONUS found+fixed: **discord-bot did not COMPILE
at HEAD** (c3d010f20 Rc SharedWorld held across awaits/threads — the "excluded
workspace never compiles" class, live); repaired structurally (offering factory
births sessions on the store's owning thread). IN-FLIGHT: G1 rung 1
(advance_signed seam) and G7 steps 1-2 (the .dungeon→CellProgram compiler with
translation validation).
Mined by direct reading + live-surface probing (funnel probed healthy; a real
session opened and inspected) during the game-affordances mapping campaign
(`docs/GAME-AFFORDANCES-MAP.md`). One meta-finding up front: **the same disease
appears on both public surfaces independently** (web + discord bot) — session
growth and identity assertion were each implemented twice, wounded twice.

### G1. Player identity never signs and never gates — the deepest one — LANE ✓verified
On the offering path, `Offering::advance(session, input, actor: DreggIdentity)`
treats the actor as attribution metadata: the dungeon offering does
`session.actors.push(actor)` (`dreggnet-offerings/src/dungeon.rs:307`) and the
turn commits under the world's cap. `DreggIdentity(pub String)` — no signature is
ever consumed on this path. Web derives it as `blake3(?user= | dregg_user cookie |
"anon")` (`dreggnet-web/src/lib.rs:520`): **any legal move can be made AS anyone**,
and any hidden-hand surface keyed on `render_for(viewer)` would reveal a player's
fog to whoever guesses their public string. The adapters (discord/telegram/wechat)
derive REAL ed25519 cipherclerks but custodially (bot_secret → every user's key)
and use only the pubkey hex for attribution — the key never signs a turn either.
The ONLY place identity binds cryptographically today is `dreggnet-party` (seat
custody keypairs + `AuthRequired` caps + signed ballots). The passkey seam is
already named in code (`Custodian::identity_for`, `dreggnet-offerings/src/session.rs:520`).
**Move (two rungs):** (1) add the missing consumer — an `advance_signed` seam
verifying ed25519 over `(SessionId, Action, turn_counter)` against the holder's
pubkey before the actor log; (2) browser-held keys via cipherclerk-in-wasm (path
A, cheapest — `dregg-sdk` AgentCipherclerk + the existing `SessionKey` grant
envelope + `webauth-core::credext` PoP) or WebAuthn→dga1 (path B, standards).
Copy the party crate's enforcement pattern; keep the session-key paymaster UX.

### G2. Unbounded session minting + zero throttling, twice — CHEAP each ✓verified
Web: `GET /offerings/{key}/session/{id}` lazily opens a real WorldCell for ANY id
string (`dreggnet-web/src/lib.rs:30`, `ensure_open` :264) — no cap, TTL, eviction,
or rate limit; a crawler is a memory-growth attack (and a disk-growth one once the
durable session store lands). Bot: the offering `Store` and descent-run maps
(`discord-bot/src/commands/offering.rs:153`, `descent.rs:789`) grow monotonically —
`close_in` exists but is `#[allow(dead_code)]`; `/descent play`, `/buy-credits`,
and every `offering:` press have no per-user cooldown (only presence/activity are
limited). **Move:** per-identity open caps + LRU eviction + boot GC of never-landed
logs (web); wire `close_in` + idle-TTL sweep + per-user cooldowns (bot). One
shared design, two small installs.

### G3. `/descent` serves a hardcoded pinned drand round when the cron hasn't fired — CHEAP ✓verified
`DRAND_QUICKNET_ROUND = 1_000_000` + literal sig hex baked at
`discord-bot/src/commands/descent.rs:94-96`; `resolve_todays_beacon` (:124) silently
serves it — a genuine BLS-verified reveal, but the SAME dungeon every day absent
egress. The daily-freshness claim rides a 5-minute cron + network. **Move:**
label the fallback in the surface (footer: "pinned round, not today's") or
fail-closed to yesterday's verified live round; alert when served stale >1 day.
(The dice-crate side of this — a live round-fetch client — is the same lane.)

### G4. PAYMENTS-GO-LIVE is one line, verbatim — sharpens backlog §2 ✓verified
Both `PayState` constructors build `MockWatcher` unconditionally; the boot path
`from_env_or_devnet` does so even when `PayConfig::from_env()` returned a real
`Network::Mainnet` config (`discord-bot/src/pay.rs:481-482`) — deposit addresses
are real and watched by nobody. Config, ledger, treasury routing, idempotency,
paid-narrator debit-after-success are all real and driven. **Move:** select the
real Solana watcher on `Mainnet` at :481 (keep the mock in
`devnet_mock_no_backend:444` — that one is correct); split seed custody to a
sweeper service per §2.

### G5. Generic collective mode is dead code on the live surface — CHEAP ✓verified
`close_round`/`handle_close`/`open_round`/`with_round` are `#[allow(dead_code)]`
(`discord-bot/src/commands/offering.rs:495-579`); no generic close subcommand is
registered, so crowd-play is reachable ONLY through `/dungeon`'s bespoke wiring —
`/council`/`/market` collective mode is scaffold in production. **Move:** register
the close affordance on collective offerings; delete the allows.

### G6. Misc, each small — CHEAP
- `discord-bot/src/cards.rs:64,75` renders explorer links to the dead
  `devnet.dregg.fg-goose.online` on the live card path → joins the repo-wide
  fg-goose sweep lane.
- `sign_legacy` blake3-MAC (`discord-bot/src/cipherclerk.rs:171`) still accepted
  by old devnet endpoints — flagged for deletion in its own module doc; do it.
- `FEDERATION_ID` defaults to 64 zeros and only WARNS while every transfer fails
  at runtime (`discord-bot/src/config.rs:84`, `main.rs:697`) — make solo-node
  mismatch fail-fast at boot.
- The bot is mis-homed on the tailnet-exit box from an unreproducible ~2-week-old
  image (TODO-2/TODO-7 in `deploy/README.md`) — the move to persvati is designed;
  remember: one token = one bot, stop the edge container first.

### G7. The authoring lane — forge → deployed substrate (the opportunity) — LANE
Grounded migration map: the `.dungeon` parser + validator (1,839 L,
`attested-dm/src/dungeon_dsl.rs`) and the roommap visualizer are PURE (zero
ledger coupling, lift-and-shift); the forge front-end only needs its transport
repointed; dungeon-on-dregg already replicates combat/status/spells/loot/
overworld/collective as real teeth. THE one missing artifact is the compiler
`GameWorld → CellProgram/StateConstraint/dregg-schema` — it converts 13
hand-written `deploy_*` worlds into forge-authorable content and gives the
platform UGC-on-the-real-substrate. Five-step path written in
`docs/GAME-AFFORDANCES-MAP.md` §8 notes; center of gravity = step 2 (the
compiler); steps 1/3/4 are mechanical.

### G8. dreggnet-web cannot LINK any bin/test on the primary laptop (observed 07-16 evening) — TRIAGE
Every `dreggnet-web` link target — including the funnel binary `dreggnet-web-server`
itself — fails with missing `_runtime_initialize_mathlib_Mathlib_Tactic_*` symbols
out of `libdregg_lean_ffi` (the lean-ffi working archive is stably
closure-incomplete; same rlib hash across retries). The chain is by-design
mandatory: `dreggnet-offerings → dregg-pay → dregg-governance/bridge →
dregg-lean-ffi` (the Lean cores are fail-closed, no feature door). Observed under
the in-flight working tree (root Cargo.toml/Cargo.lock + bridge/ mid-edit by the
Custom-VK lane), so it may be transient to that lane's state — but it means the
LIVE surface's binary is unrebuildable from this tree TODAY, and it blocked the
session-durability weld's test gate. **Move:** after the in-flight lane commits,
re-run `cargo test -p dreggnet-web`; if still red at a clean HEAD, this is a P1
build wound (suspects: a re-seeded seed archive reverting working copies to
closure-incomplete per `dregg-lean-ffi/build.rs` docs, or manifest-driven feature
drift); fix via `cargo clean -p dregg-lean-ffi` + rebuild once the tree is quiet,
and add a CI gate that LINKS (not just checks) `dreggnet-web-server` — a
check-green/link-red split is exactly the class the CI-meaningfulness audit hunts.

### G9. The live demo plays on dregg-the-LIBRARY, not dregg-the-network — LANE (roadmap grounded)
ember's observation, confirmed by direct reading: offering PLAY is in-process
everywhere (the `Offering` trait + `OfferingHost` have zero node references; the
web `/verify` route is in-process replay). The only node touch is the OPT-IN
settle seam (`dregg-node-target`, default `Local`, fail-closed) wired solely
into the two descent surfaces; `dreggnet-tavern` is the lone per-turn-real-node
offering (and shows that model's full cost). The extension (Dragon's Egg
Cipherclerk) cannot see the hbox demo at all: host permissions = node.dregg.net
only; it speaks node `/api/*`, not the web routes; its `<dregg-descent>` is its
own in-tab game. Backlog correction: the honest "no built-in node" language
lives in site/dregg-works/{verify-badge,transclude}.js, not endpoints.ts:22
(that is a product default constant).
**The graded path (each step's machinery exists or is one seam away):**
1. Node back on hbox (TODO-1; seed watcher armed — build blocked only on the
   lean seed rebuild finishing).
2. Option B — give automatafl/tug the daily-descent `settle` seam: anchor the
   session receipt-chain tip via `NodeTarget::route` (~1000-computron EmitEvent
   per anchor; play stays local/fast). Smallest honest step; then the served
   session page emits a `verify-badge.js` tag with the session cell id —
   client-checkable with ZERO extension changes.
3. Option C — tug's whole-match fold (`WholeChainProof` exists) bound into a
   `SubmittedTurn`: one node turn per match, the strongest object. Not wired.
4. Rung-2 identity join: the extension's `signOfferingTurn` (71b808b67) feeds
   the web `act-signed` route (follow-up) into `advance_signed` (6fa643d05) —
   non-custodial player keys on the live surface.
Option A (tavern-model per-turn node fires) is real but a substrate rewrite per
offering — not the next step.
