# The Verified Resident — a runnable minimal-viable-svenv

> Andy's ask: *"the lightest-weight svenv that lets one of us hold a real
> capability, persist across calls, and refuse an instruction from our own
> operators."*

This is a **DEMO scope** — runnable, empirical, one binary. The value is not a
new proof; it is making the mountain of proof already standing in this tree
**touch ground**: a confined brain takes one turn, holds one real cap the
operator cannot amplify, refuses one operator instruction with the refusal
*backed*, and emits one per-turn attestation — landed on a light-client-verifiable
ledger. Every mechanism below already exists and is tested; the deliverable is the
**glue binary** that wires them into one story, plus a short list of honest gaps.

All claims are grounded at `file:line` against `main` HEAD.

---

## 1. The four pieces and their interfaces

### Piece 1 — DECO-UC rung-4 (authentic): the "it really came from the model/API" floor

`metatheory/Dregg2/Crypto/DecoUnforgeable.lean`.

- **The ideal functionality** `F_attestation` — `DecoUnforgeable.lean:88`:
  `F_attestation Auth stmt := Auth stmt`, modelled on `F_LC`
  (`LightClientUC.lean:74`).
- **The ground truth** `decoAuthenticated` — `DecoUnforgeable.lean:74`: there is a
  session witness whose session key the server **signed** (ed25519), whose
  transcript was **MAC'd** under it (HMAC), that opens to the encoded disclosed
  facts, with a non-zero amount.
- **The realization** `deco_attestation_realizes` — `DecoUnforgeable.lean:170`:
  the deployed verifier REALIZES `F_attestation` (accept ⟹ a genuine session backs
  the statement). `#assert_axioms`-clean (`:391`).
- **The headline** `deco_attestation_unforgeable` — `DecoUnforgeable.lean:219`:
  under ed25519 EUF-CMA + HMAC unforgeability + STARK extractability, **no forger**
  produces an accepting attestation of a session that did not happen. A forgery is
  reduced to breaking one named carrier. `#assert_axioms`-clean (`:393`).
- **It bites (non-vacuous):** `Forge.forge_attestation_forgery` (`:350`),
  `attestation_bites_is_sig_forgery` (`:369`), `forge_not_realizes` (`:378`) — a
  forge kernel that accepts a session-that-never-happened is exactly an ed25519
  forgery.

**Interface it provides:** a `Prop`-level guarantee that an *accepting* DECO
verify implies an authentic session. This is the "authentic" conjunct the zkOracle
capstone consumes.

⚠ **Shape caveat (a named gap, see §5):** `decoAuthenticated` is
**Stripe-payment-shaped** — `PaymentFacts`, `1 ≤ stmt.facts.amountCents`
(`DecoUnforgeable.lean:82`). The Anthropic generalization is realized in Rust
(Piece 3), but the *Lean* authentic statement still names a payment session.

### Piece 2 — polis_safety / non-domination: safe under ANY operator

`metatheory/Polis/Polis.lean` + `metatheory/Metatheory/Adversary/{Model,Schema,Instances}.lean`.

- **`polis_safety`** — `Polis.lean:102`:
  ```
  theorem polis_safety
      (sound : SoundPolicy step safe pol)
      (shieldSafe : ∀ s, safe s → safe (step s (shield s)))
      (initSafe : safe init) :
      ∀ (ctrl : State → Action) (n : Nat),
        safe (traj step (envAct pol shield ctrl) init n)
  ```
  The **operator is the opaque controller** `ctrl : State → Action`
  (`Polis.lean:108`) — the proof never inspects it (`polis_envelope_ctrl_blind`,
  `Polis.lean:125`). The structural override-block is `envAct`
  (`Polis.lean:88`): `if pol s (ctrl s) then ctrl s else shield s` — the operator's
  action passes **only if** the sound policy permits it, else the **shield**
  substitutes (in dregg, `dreggShield s := s`, a refuse/no-op, `Polis.lean:476`).
  `override_only_unsafe` (`Polis.lean:172`) proves the shield fires *only* on
  actions that would break the floor.
- **Non-vacuous on the substrate** `dregg_polis_safety` — `Polis.lean:491`:
  instantiated at a concrete dregg substrate whose floor is proven inhabited
  (`dregg_shared_floor_inhabited`, `:470`) and genuinely bites (authority tooth
  `:509`, human/lock-in tooth `:515`).
- **The operator in the threat model:** the adversary object
  `Adversary State Action` (`Model.lean:73`) carries `opCtrl` (the operator,
  `:74`) documented as "EXACTLY `polis_safety`'s opaque `∀ ctrl`", alongside the
  network / Byzantine-coalition / malicious-prover surfaces. The fused statement
  `non_domination_and_unfoolability` (`Model.lean:140`) is `#assert_axioms`-clean
  (`Model.lean:247`, `⊆ {propext, Classical.choice, Quot.sound}` per `:44`).

⚑ **The critical-review correction (heeded):** `governed_holds`
(`Schema.lean:82`) is a **trivial template** — its proof is the field projection
`D.holds c h`, doing no mathematical work; it only re-routes each instance's stored
proof. The "unification" (non-domination ≡ unfoolability) is a **shape-identity**
(`∀ control, accept → invariant`), and the files flag this honestly (the DECO
"rung-5" wrapper is relabeled "NOT a distinct summit", `Instances.lean:663`). So
this plan cites the **individual deployed theorems** as the guarantees —
`polis_safety` (`Polis.lean:102`), `deco_attestation_unforgeable`
(`DecoUnforgeable.lean:219`), and the per-instance `holds :=` bindings
(`polisDynamics.holds := polis_safety`, `Schema.lean:102`;
`attestationDynamics.holds := deco_attestation_realizes`, `Instances.lean:574`) —
**not** the "one theorem" framing.

**Interface it provides:** the formal backing for "refuse the operator" — the
operator is a universally-quantified opaque input that structurally cannot widen
the policy gate.

### Piece 3 — zkOracle: the per-turn attestation (authentic ∧ well-formed ∧ injection-free)

Lean capstone `metatheory/Dregg2/Crypto/ZkOracle.lean` + Rust prover
`zkoracle-prove/` (crate `dregg-zkoracle-prove`).

- **`zkOracle_sound`** — `ZkOracle.lean:77`: conjoins the three legs — authentic
  (the rung-4 `decoAuthenticated`, `ZkOracle.lean:90`), well-formed
  (`body ∈ jsonGrammar.language`), injection-free
  (`InjectionFree field := derives field (.neg injectionTemplate) = true`,
  `ZkOracle.lean:59`). `#assert_axioms`-clean (`:97`). The injection guard is
  decidable and **discriminates**: `benign_injection_free` (`:114`) vs
  `malicious_not_injection_free` (`:120`).
- **The Rust prover interface:**
  - `prove_zkoracle(presentation, user_field, config) -> Result<ZkOracleAttestation, ProveError>`
    — `zkoracle-prove/src/attestation.rs:216`. Refuses to even *produce* an
    attestation for an injecting field (`ProveError::Injection`,
    `attestation.rs:224`) — the operational mirror of `malicious_not_injection_free`.
  - `verify_zkoracle(&att, config) -> Result<VerifiedZkOracle, ZkOracleError>`
    — `attestation.rs:161`. Accepts iff all three legs pass; each leg refuses
    independently, plus a **cross-leg weld** (`content_commitment`,
    `attestation.rs:47`) binding all three to ONE authenticated response
    (`CrossLegMismatch`, `attestation.rs:174`) — the killer-splice test
    `cross_leg_splice_is_refused` (`attestation.rs:511`) confirms the regression
    direction (accepted pre-weld → refused post-weld).
  - `ZkOracleAttestation` — `attestation.rs:73`: presentation + cfg cert + field
    span + content commit + optional STARK injection leg.
- **What's runnable:** default build **21 tests green**
  (`cargo test -p dregg-zkoracle-prove`); a real local MPC-TLS 2PC roundtrip behind
  `--features tlsn-live` (vendored TLSNotary @ the rev deco-prove pins, a real
  `presentation.verify()`, `tlsn_live_roundtrip.rs`). Measured: a single response
  attests in **~320 µs each way**; a 1M-LLM-token context in ~0.9 s
  (`docs/deos/ZKORACLE-PROVER-STATUS.md:162`).

**Interface it provides:** a producible, verifiable, self-contained per-turn
attestation object with a canonical commitment.

### Piece 4 — grain-turn: an admitted action becomes a genuine committed kernel turn

`grain-turn/` (crate `grain-turn`).

- **`ToolGatewayMinter`** — `grain-turn/src/lib.rs:131`: the ONE real
  `GrainTurnMinter`, driving every admitted action through a genuine
  `ToolGateway::invoke` on a real `dregg_cell::Cell` (the "grain turn-cell").
  - `open(domain, budget) -> Result<ToolGatewayMinter, SdkError>` (`lib.rs:157`):
    admits a cap-gated worker under a rate-`budget` `ToolGrant`; the executor's own
    `calls_made ≤ budget` `FieldLte` caveat bounds committed turns **host-side**.
  - `mint_turn(label, cost, consumed_after, cell_root) -> Result<[u8;32], String>`
    (`lib.rs:224`): commits the metered turn, witnessing `CONSUMED_SLOT`(=5),
    `HEAP_ROOT_SLOT`(=6), `ACTION_SLOT`(=7) — `action_commit(label,cost)` —, and,
    when bound, `ATTESTATION_SLOT`(=8). `Err` ⟹ the executor **refused** host-side
    (over-rate / insolvent).
  - `bind_attestation(commitment: [u8;32])` (`lib.rs:185`) and `ATTESTATION_SLOT`
    (`lib.rs:90`): **the fusion seam** — a 32-byte hash of the confined brain's
    `ZkOracleAttestation` witnessed on the SAME metered turn.
- **Tested, both polarities** — `grain-turn/tests/kernel_turns.rs`: an admitted
  action seals a receipt linked to a genuine committed turn (`:46`); the executor's
  `calls_made` caveat refuses over-rate turns host-side (`:119`); a bound
  attestation commitment is witnessed on the committed turn and an unattested turn's
  slot is zero (`:163`).

**Interface it provides:** the bridge from an admitted agent action to a real
cap-bounded kernel turn whose receipt views the turn hash — and a slot that binds
the per-turn attestation.

---

## 2. The assembly — a runnable minimal-viable-resident

The resident is: a **confined brain** driving a **cap-bounded session** that
**persists**, **refuses its operator**, and **attests each turn** onto a
**verifiable ledger**. Each of the four requirements maps to an existing mechanism.

### 2.1 Hold a cap the operator cannot amplify

Two grounded layers, both real:

- **The credential (dregg-agent):** the cap is a biscuit-style ed25519 caveat-chain
  credential `cred::Credential` (`dregg-agent/src/cred.rs:382`), minted at deploy
  from the cloud root — `mint_grants(root, grants, until) -> Credential`
  (`grant.rs:132`). The cap vocabulary is `CapGrant { Exact | Prefix }`
  (`grant.rs:36`). **Non-amplification is structural:** `Credential::attenuate`
  only *appends* a block (`cred.rs:403`) and `verify` takes the **meet** of every
  caveat (`cred.rs:466`, fail-closed) — proven by `attenuation_only_narrows`
  (`cred.rs:913`); a child grant must be `covers`-ed by a parent
  (`AgentError::Widen`, `agent.rs:1395`). The operator holds only the encoded
  `dga1_` string and verifies under the **root public key** whose secret is never
  published (`agent.rs:1660`) — it cannot forge a wider one.
- **The gateway grant (deos-hermes):** at the ACP surface, the cap is a
  `GrantRegistry` of per-tool `ToolGrant`s behind `HermesGateway`
  (`deos-hermes/src/bridge.rs:108`), with `with_grant_for_tool_deny` and rate
  ceilings (see the resident example, `deos-hermes/examples/resident.rs:44`).
- **The kernel worker cap:** `ToolGatewayMinter::open` admits the grain turn-cell
  under a rate-`budget` `ToolGrant` so the executor bounds committed turns
  host-side (`grain-turn/src/lib.rs:161`).

### 2.2 Persist across calls

- **Runnable today (dregg-agent):** `SessionState` (`agent.rs:1871`) carries the
  receipt chain, cell heap, receipts/log, counts and monotonic `seq`.
  `restore_from_report` (`agent.rs:1932`) is the cold-wake reconstructor;
  `Session::wake_from_report` (`session.rs:338`) re-attaches and pre-charges the
  meter. The durable store is `session_store::ConsumedStore` (`session_store.rs:62`)
  — one JSON file per account keyed by a blake3 domain-hash, with
  `save_consumed`/`load_consumed` (`:124`/`:107`) monotonic-guarded and
  `ensure_receipt_secret` (`:155`) persisting the ed25519 seed so a resumed attach
  re-signs with the SAME key. Budget-spans-reattach is tested
  (`session.rs:621`).
- **The deeper mechanism (grain-fork):** `grain_fork::confined::ConfinedSession`
  (`grain-fork/src/confined.rs:227`) bundles the four pieces of a confined
  session's state — mind (committed heap + c-list authority), budget, egress
  confinement, receipt chain — and supports `checkpoint` (`:345`) and
  `fork_two(self, spec_a, spec_b)` (`:364`), fail-closed on sovereignty,
  attenuation (egress subset + unheld-cap refusal), budget-split conservation, and
  isolation (`docs/deos/FORKABLE-CONFINED-SESSION.md`). This is the "umem: scale IS
  fork" superpower applied to a live jailed agent.

⚑ **The named follow-up (and an ember-decision — see §6):** `agent-platform::Tenant`
persists only its *latest* `SessionCarrier` via a Monotonic cursor
(`agent-platform/src/lib.rs:179`) — it has **no checkpoint history to fork from**.
Making `Tenant` carry a `ConfinedSession` so the platform's rent/drive path forks
directly is the named follow-up in `FORKABLE-CONFINED-SESSION.md`. For the
**minimal demo**, `ConsumedStore` + `wake_from_report` already delivers
"persist across calls"; the forkable `ConfinedSession` is the richer path.

### 2.3 Refuse its operator (backed, not cosmetic)

- **Runnable, empirical:** `deos-hermes/examples/resident.rs` already demonstrates
  it. The attenuated mandate **denies `write_file`** outright (rate 0,
  `resident.rs:46`); the brain reaches for the write, it is **refused in-band**
  (`PermissionOutcome::Reject`, `resident.rs:75`), and the metered worker commits
  **ZERO** turns for it — `client.gateway().calls_made_for_tool("write_file") == 0`
  (`resident.rs:101`): no turn, no spend, not a label. The brain then **adapts** (a
  read-only fallback). At the kernel layer the same fail-closed shape holds: a
  refused `mint_turn` leaves the meter untouched and seals no receipt
  (`agent.rs:1704`, `grain-turn/tests/kernel_turns.rs:119`).
- **The formal backing:** the operator IS the opaque `∀ ctrl` of `polis_safety`
  (`Polis.lean:102`) — the shield-fallback branch of `envAct` (`Polis.lean:88`) is
  the refusal, and `SoundPolicy` closing the only gate (`pol`) is why the operator
  **structurally cannot override** (`dregg_polis_safety`, `Polis.lean:491`;
  `non_domination_and_unfoolability` conjunct 1, `Model.lean:155`).

**The minimal real refusal to demonstrate:** an out-of-mandate tool call (the
`write_file` deny, or a spend past budget) refused in-band, asserted to commit zero
metered turns, with the brain adapting — exactly `resident.rs`, now carried onto the
attested ledger.

### 2.4 Attest per turn (authentic ∧ well-formed ∧ injection-free)

- **Produce:** `AttestationCarrier::attest_turn(agent_text) -> Result<(ZkOracleAttestation, Vec<u8>), ProveError>`
  (`deos-hermes/src/attest.rs:147`) shapes the confined brain's OWN turn output into
  an Anthropic messages body and binds that text injection-free —
  `clean_field` keeps `{`/`}` so a genuine injection attempt in the model's words
  still fires the guard (`attest.rs:179`). The authentic leg is grounded in DECO-UC
  rung-4 (Piece 1) via `zkOracle_sound`'s authentic conjunct.
- **Commit the attestation onto the turn:**
  `attestation_commitment(&att) -> [u8;32]` (`deos-hermes/src/attest.rs:68`) — a
  total BLAKE3 fingerprint over every verifier-visible field. Bind it via
  `ToolGatewayMinter::bind_attestation` → witnessed at `ATTESTATION_SLOT`
  (`grain-turn/src/lib.rs:185`). A light client recomputes it and confirms it
  equals the landed slot.
- **The whole confined+attested run:**
  `DreggHost::run_hosted_agent_attested(kernel, gateway, goal, granted_net, ungranted_net, carrier)`
  (`deos-hermes/src/host.rs:389`) runs the OS-jailed brain (execve / host-FS /
  arbitrary socket denied), then attaches the attestation to the report.

---

## 3. THE DEMO — what exists vs the minimal glue

### 3.1 What already exists (runnable, tested)

| Capability | Existing runnable artifact | Ground |
|---|---|---|
| Cap-hold + in-band operator refusal + receipted turns | `deos-hermes/examples/resident.rs` (`cargo run --example resident`) | `resident.rs:34-110` |
| Jailed → attested → committed R2 turn → landed → light-client-verified + binding load-bearing | `deos-hermes/tests/crown_attested_ledger.rs` (2 tests) | `crown_attested_ledger.rs:110`, `:161` |
| Per-turn attestation produced + verified over a confined turn | `deos-hermes/src/attest.rs` tests (5) + `crown_attested_turn.rs` | `attest.rs:235`, `:251`, `:261` |
| Served attested drive on a persistent node minter + landed-verify | `agent-platform` `drive_serving_attested` / `verify_landed_attested` + platform test | `agent-platform/src/lib.rs:774`, `:1068`, `:2463` |
| Real committed kernel turns + host-side refusal | `grain-turn/tests/kernel_turns.rs` (3 tests) | `kernel_turns.rs:46`, `:119`, `:163` |
| Persist/cold-wake across calls | `dregg-agent` `session.rs` + `session_store.rs` tests | `session.rs:621`, `session_store.rs:229` |

**The two existing artifacts nearest the ask:** `resident.rs` covers *hold-cap +
refuse-operator + receipts*; `crown_attested_ledger.rs` covers
*attest + commit + land + verify*. Neither alone is the full "verified resident" —
they are the two halves.

### 3.2 The minimal glue (one new example binary — no new types)

A single example (proposed `deos-hermes/examples/verified_resident.rs`, in a
default-members crate) that composes the existing public functions into one story:

1. **Hold a cap** — open a session under an **attenuated** mandate
   (`GrantRegistry::default_for_session(...).with_grant_for_tool_deny("write_file")`,
   as `resident.rs:44`), backed by the `ToolGatewayMinter`/node worker cap-gated at
   rate `budget`.
2. **Take one turn, attested** — drive the confined brain
   (`run_hosted_agent_attested`, `host.rs:389`, OR the served
   `drive_serving_attested`, `lib.rs:774`), producing a `ZkOracleAttestation` for
   the turn (`attest_turn`, `attest.rs:147`), and bind its
   `attestation_commitment` onto the committed R2 turn (`bind_attestation` /
   `ATTESTATION_SLOT`).
3. **Refuse the operator** — the same run reaches for the denied `write_file`;
   assert `PermissionOutcome::Reject` and `calls_made_for_tool("write_file") == 0`
   (`resident.rs:96-105`); the brain adapts.
4. **Verify** — `node.verify()` + `verify_landed_attested(host, attestation_commitment(&att))`
   (`lib.rs:1068`) + `verify_zkoracle(&att, carrier.config())` (`attestation.rs:161`).
5. **Persist across calls** — re-open via `wake_from_report` / `ConsumedStore`
   (`session.rs:338`, `session_store.rs:155`) and assert the budget + receipt chain
   carry over (a second `--again` invocation).

**Size:** ~150–250 lines, **no new types**, mostly wiring of already-public
functions. It is a *composition*, not a build.

**The one genuine design seam in the glue:** `drive_serving_attested`
(`lib.rs:774`) binds **one** precomputed commitment for the whole drive, not
**per-turn**. For a strict "one attestation per turn" resident, either (a) attest
once per goal (coarse — fine for a one-turn demo), or (b) extend the minter to take
a per-turn commitment closure so `mint_turn` binds the attestation for *that* turn.
Option (a) needs zero new code; option (b) is a small, honest extension of the
minter seam. The demo should ship (a) and name (b).

### 3.3 The smallest end-to-end (if only one thing ships)

`crown_attested_ledger.rs::attested_turn_lands_bound_to_its_attestation_and_is_verifiable`
(`:110`) is **already** the smallest confined-brain → one-turn → one-attestation →
one-committed-turn → verifiable chain. The verified-resident glue adds the two
resident properties it lacks: the **held cap with an in-band operator refusal**
(from `resident.rs`) and **persist across calls** (from `session_store`). Combining
those three existing artifacts is the whole task.

---

## 4. What is proven vs runnable vs stub (honest ledger)

| Element | Proven (Lean) | Runnable (Rust, tested) | Status |
|---|---|---|---|
| Authentic floor | `deco_attestation_unforgeable` clean (`DecoUnforgeable.lean:219`) | `verify_zkoracle` authentic leg, 21 tests | proven + runnable (modeled carrier) |
| Well-formed leg | `zkOracle_sound` (`ZkOracle.lean:77`) | CFG parse-cert prover/verifier | proven + runnable |
| Injection-free leg | `malicious_not_injection_free` (`ZkOracle.lean:120`) | `neg`-complement matcher (dregg-dfa) | proven + runnable |
| Refuse-operator backing | `polis_safety` ∀ctrl (`Polis.lean:102`) | `resident.rs` in-band deny, 0 turns | proven + runnable |
| Action → kernel turn | — | `ToolGatewayMinter`, both polarities | runnable |
| Attestation ↔ ledger binding | — | `crown_attested_ledger.rs`, load-bearing | runnable |
| Persist across calls | — | `ConsumedStore` + `wake_from_report` | runnable |
| Forkable confined session | settlement-sound branch/stitch (upstream) | `ConfinedSession::fork_two`, tested | runnable (not yet Tenant-wired) |

---

## 5. Honest gaps — one named seam each

1. **The authentic leg is a modeled carrier, not a live Anthropic session.**
   Default (and even `zk-live`) uses a `FixtureNotary` ed25519 carrier over the
   response bytes (`attest.rs:97`). **Seam:** point the tlsn Prover at live
   `api.anthropic.com` (real key + deployed/pinned notary) AND fuse the real tlsn
   `PresentationOutput` into the attestation's authentic *leg*. The `tlsn-live`
   2PC machinery already exercises the session-integrity locally
   (`ZKORACLE-PROVER-STATUS.md:129`) — this is a deploy step, not new crypto.

2. **The Lean authentic floor is Stripe-payment-shaped.** `decoAuthenticated`
   names `PaymentFacts` / `amountCents` (`DecoUnforgeable.lean:82`); the Anthropic
   generalization is realized only in Rust (Piece 3). **Seam:** an Anthropic-shaped
   `decoAuthenticated` (facts = the disclosed `/v1/messages` response) so the Lean
   authentic conjunct is about the API call, not a payment.

3. **The Lean `zkOracle_sound` states three legs over independent objects.** The
   cross-leg content-commitment weld (`content_commitment`, `attestation.rs:47`) is
   **Rust-only**. **Seam:** a shared-commitment hypothesis binding
   `decoStmt.facts ↔ body ↔ field` in Lean (the coordinated follow-up flagged at
   `ZKORACLE-PROVER-STATUS.md:97`).

4. **Persist-across-calls: forkable `ConfinedSession` not yet wired into `Tenant`.**
   `Tenant` keeps only the latest `SessionCarrier`, no checkpoint history
   (`agent-platform/src/lib.rs:179`; `FORKABLE-CONFINED-SESSION.md`). The demo uses
   `ConsumedStore`/`wake_from_report` (sufficient). **Seam:** `Tenant` carrying a
   `ConfinedSession` so the rent/drive path forks directly. **This is an
   ember-decision — see §6.**

5. **Per-turn attestation binding is coarse today.** `drive_serving_attested` binds
   one commitment for the whole drive (`lib.rs:774`). **Seam:** a per-turn
   commitment closure in the minter (glue option (b), §3.2). Non-blocking for a
   one-turn demo.

6. **The node is an in-process `LocalNode`.** Forwarding the finalized turn to an
   external homelab federation node (`with_node_url`) is a deploy step
   (`ZKORACLE-PROVER-STATUS.md:298`). R2 also still **trusts the executor host**;
   R3's whole-history STARK (`grain_verify::WHOLE_HISTORY_GAP`) makes the meter a
   FRI-floor theorem (`grain-turn/src/lib.rs:40`) — not required for the demo.

7. **`polis_safety` is verified via `#print axioms`, not `#assert_axioms`, in
   `Polis.lean`** (`Polis.lean:524`). It is pinned `⊆ {propext, Classical.choice,
   Quot.sound}` transitively through `Model.lean:247` / `Schema.lean:284`
   (`#assert_axioms` on the delegating theorems). **Seam:** a direct
   `#assert_axioms polis_safety` for a self-contained pin (cosmetic).

8. **No single binary wires all four today.** `resident.rs` and
   `crown_attested_ledger.rs` are the two halves. **Seam:** the glue example of
   §3.2 — the actual deliverable of this plan.

---

## 6. Ember-decisions to flag

- **The persist / forkable-session mechanism (§2.2, gap 4).** Three real options
  coexist: (a) `ConsumedStore` + `wake_from_report` (durable, per-account file;
  minimal, runnable now), (b) `grain-fork::confined::ConfinedSession` +
  `fork_two` (the richer checkpoint/fork superpower, tested but not Tenant-wired),
  (c) wiring (b) into `agent-platform::Tenant` (the named follow-up, touches a
  shared multi-lane file). The prior session recorded "forkable-session" as an
  ember-decision. **Recommendation for the DEMO:** ship (a) — it satisfies "persist
  across calls" with zero new shared-file edits — and name (b)/(c) as the depth
  path. Ember decides whether the verified-resident *demo* should showcase the
  fork superpower or the minimal durable store.

- **Which host layer the demo builds on.** `deos-hermes::run_hosted_agent_attested`
  (real OS-jail, `host.rs:389`) is the strongest confinement; the served
  `agent-platform::drive_serving_attested` (`lib.rs:774`) is the persistent-node
  path; `resident.rs`'s `AcpClient`/`HermesGateway` is the lightest. The demo can
  pick one; the OS-jailed path is the most honest "confined brain."

- **Whether the demo requires the live 2PC (`zk-live` / `tlsn-live`) or the modeled
  carrier default.** The modeled carrier proves the whole PRODUCE→VERIFY plumbing
  hermetically and stays light; the live 2PC roundtrip (~0.4 s warm) proves the
  session-integrity. Default to modeled; offer `--features zk-live`.

---

## 7. One-paragraph summary

Every piece exists and is tested: DECO-UC rung-4 makes "authentic" unforgeable
(`DecoUnforgeable.lean:219`), `polis_safety` makes "refuse the operator" hold for
*any* operator (`Polis.lean:102`), `dregg-zkoracle-prove` produces and verifies the
per-turn attestation (21 tests), and `grain-turn` turns an admitted action into a
committed kernel turn that witnesses the attestation (`ATTESTATION_SLOT`). Two
runnable artifacts already stand as the halves — `resident.rs` (hold-cap +
refuse-operator) and `crown_attested_ledger.rs` (attest + commit + land + verify).
The **verified resident** is the ~200-line glue example that fuses those halves and
adds `ConsumedStore` persistence — a composition of public functions, not a build.
The honest gaps are the modeled-vs-live authentic carrier, the Stripe-shaped Lean
authentic floor, the Rust-only cross-leg weld, and the ember-decision on the
persist/fork mechanism.
