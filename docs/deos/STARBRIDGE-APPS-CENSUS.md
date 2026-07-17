# starbridge-apps census — power, composition, and voting on dregg

A grounded, read-only survey of `starbridge-apps/` at HEAD
(`1ca697a9696`, branch `main`). Every claim is cited `file:line`. The
question this doc answers: **what is each app, how do we make each one
individually more powerful, how do the apps compose with each other and
with the substrate — and what does a real voting app on dregg look
like?**

> Method note. A **starbridge-app** is not a stack — it is *data*: a set of
> `FactoryDescriptor`s whose `state_constraints` become the born cell's
> `CellProgram`, plus signed turn-builders. "The answer is never
> `Effect::FooApp`" (`starbridge-apps/README.md:31`). Every app below is
> built from the generic primitives (`Caveat`, `StateConstraint`,
> `Authorization`, `Factory`) — so power comes from *composing more
> substrate*, never from a new kernel effect.

The shared grammar every app draws on:
`StateConstraint::{WriteOnce, Monotonic, StrictMonotonic, MonotonicSequence,
AffineLe, AffineEq, FieldLteField, FieldEquals, MemberOf, BoundedBy, AnyOf,
Immutable, ClearanceDominates}` evaluated by the executor on every turn
that touches a cell, plus the `Payable` DSI for cross-app value moves, and
the deos two-tempo gated fire (a live-state precondition gate + executor
re-enforcement of the installed caveats).

**Eight** apps are seeded into the live node at genesis
(`node/src/starbridge_seed.rs:479`–`490`): `nameservice`, `identity`,
`subscription`, `governed-namespace`, `compartment-workflow-mandate`,
`storage-gateway-mandate`, `privacy-voting`, `bounty-board` (plus the
cap-inbox factory). The rest are built + tested library crates with a
ready-but-unwired `register(ctx)` entrypoint (or, for
`branch-stitch-multiplayer`, a runnable binary demonstrator) — adding the
`register()` call to `register_starbridge_factory_descriptors()` (`:473`) is
the one-line-per-app step from library-live to genesis-live, the
lowest-risk high-leverage move for all of them.

---

## Part 1 — the per-app census

Each entry: **what-is** (the real mechanism, `file:line`), **power-now**
(load-bearing vs stub, tests, seeded?), **make-it-stronger** (more
substrate), **compose-with** (other apps + the flagship crates
`confined-swarm` / `auditable-fund`).

### agent-orchestration

- **what-is:** A durable + auditable multi-agent orchestration plane. A
  coordinator dispatch-board cell hands each worker an attenuated
  `Mandate` (tool-set ∧ sub-budget ∧ sub-task); the non-amplification
  lattice `granted ⊑ held` is `Mandate::le` / `Mandate::attenuate`
  (`src/lib.rs:201`, `:210`). The board policy IS a `CellProgram`:
  `coordinator_constraints()` (`src/lib.rs:271`) =
  `AffineLe(spent_a+spent_b−budget ≤ 0)` + `WriteOnce(LEAD/BUDGET)` +
  `Monotonic(SPENT_*)` + `StrictMonotonic(EPOCH)`, baked into
  `orchestration_factory_descriptor()` (`:315`). A durable
  `OrchestrationEngine` (`:624`) drives each `WorkStep` as a verified turn
  checkpointed to an `OrchestrationLog`, with `recover` (`:882`) and
  `audit_run` (`:995`) re-deriving the receipt chain to prove no worker
  exceeded its mandate.
- **power-now:** Heavily load-bearing — the richest of its batch. Full
  5-axis template plus a real crash-recovery + exactly-once + light-client
  audit engine. Extensive `src/lib.rs::tests` + `starbridge-apps/agent-orchestration/tests/orchestration_teeth.rs`,
  `starbridge-apps/agent-orchestration/tests/service.rs`, `starbridge-apps/agent-orchestration/tests/deos_surface.rs` (mounted axum),
  `starbridge-apps/agent-orchestration/tests/mcp_binding.rs`, `starbridge-apps/agent-orchestration/tests/userspace_verify.rs`. Factory-birth via
  `EmbeddedExecutor`. **Not** seeded.
- **make-it-stronger:** The mandate is a fixed 2-worker shape
  (`SPENT_A`/`SPENT_B`) — generalize to N workers over a real
  cap-attenuation tree so sub-coordinators re-delegate. Bind each
  `WorkStep` receipt to an R2 attested turn / zkOracle attestation so the
  audit witnesses external tool effects, not just meter advances. Fund
  workers via a prepaid `execution-lease` cell (BUDGET becomes a real
  conserved lease, not a scalar). Fork the coordinator via branch-stitch so
  competing plans diverge and settle.
- **compose-with:** Feed worker `Mandate`s into
  `compartment-workflow-mandate`'s clearance graph; log outputs into
  `agent-provenance`; meter spend through `billing`; settle sub-tasks via
  `bounty-board.payout`. With **confined-swarm**: each worker mandate
  becomes a jailed body's egress grant. With **auditable-fund**: the swarm
  BUDGET is a real conserved fund `audit_run` re-witnesses. This is the
  closest existing cousin to `confined-swarm` at the app layer.

### agent-provenance

- **what-is:** A verifiable, append-only, tamper-evident agent memory. A
  provenance log is a factory-born sovereign cell whose caveats are its
  rules: `Monotonic(HEAD)` + `WriteOnce(entry_i)` in
  `provenance_state_constraints()` (`src/lib.rs:177`), baked into
  `provenance_factory_descriptor()` (`:215`). Entries form a blake3 hash
  chain — `link_hash(prev, claim)=blake3(prev‖claim)` (`:131`), verified by
  the third-party `verify_chain` (`:161`). `build_append_action` (`:252`)
  writes `entry_slot(i)`, advances HEAD. Deos surface `provenance_app`
  (`:451`) exposes verifier ⊂ recorder ⊂ owner tiers with gated
  `append_entry` (`:572`).
- **power-now:** Load-bearing core; strong tests incl. the end-to-end
  `factory_born_log_appends_chain_rejects_overwrite_and_verifies`
  (`:866`). Axes: verified core + deos + service + card + `derived` (a
  `dregg-query` non-omission completeness certificate). **Not** seeded.
- **make-it-stronger:** `derived.rs` already reaches for a `dregg-query`
  MMR completeness cert — weld the light-client batch circuit so "these are
  ALL the entries" is proven, not asserted. Build the documented cross-cell
  chaining (TIP→next-cell genesis, `ENTRY_CAPACITY` `:111`) for unbounded
  logs. Attach a zkOracle attestation to each claim so a recorded tool-call
  is proof-carrying at write time.
- **compose-with:** The natural audit sink for `agent-orchestration` worker
  steps and `compartment-workflow-mandate` advances — append each committed
  receipt hash as a claim, one verifiable cross-app trail. With
  **confined-swarm**: a jailed body's every action is appended (unforgeable
  body-log). With **auditable-fund**: append every settlement receipt so
  `verify_chain` audits a spend history.

### billing

- **what-is:** A customer-facing billing plane — views + ceilings over
  settled turns, no new primitive. `cap_invariants()` (`src/lib.rs:162`) =
  `WriteOnce(CAP/PROVIDER/START)` + `Monotonic(SPENT)` +
  `FieldLteField(SPENT ≤ CAP)`, the executor-enforced 402: an over-cap
  charge is refused in-band. A `SpendCap` rides the proven
  `cell/src/allowance.rs` capacity; `charge_effects` (`:325`) is a
  `SetField` + a conserving `Transfer` (payment via the `Payable` DSI,
  `BillingWallet` `:394`). An `Invoice` is an aggregation view over
  settle-receipt hashes sealed as its own turn receipt
  (`build_seal_invoice_action` `:555`).
- **power-now:** Load-bearing composition; the cap ceiling + value move are
  real verified turns. The allowance heap ledger + invoice `body_hash`
  mirror are honestly flagged executor-side (light-client circuit binding is
  the named next slice). Rich modules (cap/estimate/invoice/recurring/
  usage/alerts). **Not** seeded.
- **make-it-stronger:** Weld the light-client batch circuit so the allowance
  ledger + sealed invoice digest are provable to a non-re-executing verifier
  (the stated gap). Denominate the cap in a real prepaid `execution-lease`
  so the account IS the funded budget. Attach zkOracle attestation for
  off-ledger metered usage (API calls) so `quantity` is proof-carrying.
- **compose-with:** The metering organ for `agent-orchestration` (swarm
  BUDGET → billing account; each worker step a charge under cap) and
  `compartment-workflow-mandate` (per-step debit → a charge). `BountyTreasury`
  and `BillingWallet` share the `Payable` interface — a bounty payout can
  settle a billing charge. With **auditable-fund**: the cap becomes an
  auditable fund's withdrawal ceiling; with **confined-swarm**: per-body
  budgets.

### bounty-board

- **what-is:** Escrow-backed bounties as a one-way state machine — the
  reference 4-axis template. `bounty_state_constraints()` (`src/lib.rs:128`)
  = `WriteOnce(TITLE/REWARD/CLAIMANT/SUBMISSION)` + `StrictMonotonic(STATE)`,
  baked into `bounty_factory_descriptor()` (`:170`). Lifecycle
  OPEN→CLAIMED→SUBMITTED→PAID; `StrictMonotonic` gives no-double-claim /
  no-re-open / no-double-payout; `WriteOnce(CLAIMANT)` gives
  first-claimer-wins. Deos `bounty_app` (`:452`) with gated
  `claim`/`submit`/`payout` carrying live-state preconditions. A
  `BountyTreasury` (`:781`) implements `Payable` so a payout is a real
  cross-app conserving `Transfer`.
- **power-now:** The most mature/canonical app; the exemplar the others
  copy. Full verified-core + deos + service + card, all tested incl.
  `factory_born_bounty_runs_lifecycle_and_rejects_double_claim` (`:1045`).
  **SEEDED** (`node/src/starbridge_seed.rs:486`). Payable cross-app payout
  tested against an escrow cell.
- **make-it-stronger:** Make the escrowed reward a real locked fund at post
  time (prepaid lease) released only on PAID, not a scalar except through
  `BountyTreasury`. Add a claimant cap-attenuation so a claim mints a scoped
  work capability. Bind the SUBMISSION artifact to a zkOracle / R2
  attestation so "work delivered" is proof-carrying before payout.
- **compose-with:** The settlement layer for `agent-orchestration` (worker
  completes a sub-task → payout — the treasury already pays into another
  app's cell). Record transitions into `agent-provenance`; gate `payout`
  behind a `compartment-workflow-mandate` clearance; meter via `billing`.
  With **auditable-fund**: the treasury IS an auditable fund; with
  **confined-swarm**: bounties are the task market a jailed swarm claims
  from.

### branch-stitch-multiplayer

- **what-is:** The distributed-Houyhnhnm flagship as a runnable binary
  (`src/main.rs`, no lib). Two participants fork ONE shared verified
  `World`, diverge on independent branches, and stitch through a single
  proven gate via `starbridge_v2::branch_stitch_session::BranchStitchSession`.
  Three beats: BEAT A (`:93`) disjoint edits merge clean, main pristine;
  BEAT B (`:156`) a same-address clash is refused fail-closed with both
  readings kept (no silent LWW); BEAT C (`:189`) a `gift` cap revoked
  between branch and settlement is LINEAR-DROPPED while disjoint state still
  settles — the live `settlement_soundness` gate, asserted non-vacuous both
  ways.
- **power-now:** A demonstrator, not a library — no `FactoryDescriptor` /
  `register`; a `cargo run` binary + integration test
  (`three_beat_branch_and_stitch_multiplayer` `:306`). It IS the executable
  witness of settlement soundness. The primitive itself lives in
  `starbridge-v2`. **Not** seeded (it is a binary).
- **make-it-stronger:** Promote the arc into a reusable session API
  (fork→diverge→stitch as a service), not a hardcoded 2-cast demo. Wire real
  transport so the two casts are separate federation nodes. Generalize to
  N-way stitch and cap-attenuated branch grants.
- **compose-with:** The fork/merge substrate every other app wants: fork an
  `agent-orchestration` coordinator to try competing plans; branch a
  `bounty-board` submission dispute; diverge a `compartment-workflow-mandate`
  charter and stitch officer sign-offs. With **confined-swarm**: each jailed
  body runs on its own branch and stitches under the settlement gate — the
  multiplayer spine for the whole set.

### compartment-workflow-mandate

- **what-is:** A charter DAG (review→redact→sign) with compartment
  clearance. `cwm_cell_program()` (`src/lib.rs:283`) is a
  `CellProgram::Cases`: an `Always` case (`WriteOnce` config +
  `FieldLteField(STEP_CURSOR ≤ CHARTER_TERMINAL)`) plus a
  `MethodIs("advance_step")` case carrying `MonotonicSequence(STEP_CURSOR)`
  (exact +1) and the `ClearanceDominates` tooth
  (`clearance_dominates_constraint` `:343`) — the acting officer's clearance
  (slot 5) must dominate the entered step's compartment (slot 6) in the
  root-bound charter graph (`charter_clearance_graph` `:192`). Deos
  `fire_advance_step` (`:814`) reads the live cursor so a clerk past
  `review` is a real executor refusal.
- **power-now:** Substantially built (self-described "scaffold" but with a
  real `ClearanceDominates` executor tooth bound to a stored graph root),
  full deos+service+card+reactor axes + an `ORGAN 2` `colonist_job` module.
  Tests incl. `starbridge-apps/compartment-workflow-mandate/tests/cwm_lean_differential.rs`,
  `starbridge-apps/compartment-workflow-mandate/tests/colonist_job_lean_differential.rs`. **SEEDED**
  (`node/src/starbridge_seed.rs:483`). Honest follow-ons flagged (SPEND
  debit wiring, `SenderAuthorized` + revocation-root witness for
  `cwm_safety_forever`).
- **make-it-stronger:** Wire the `SPEND_POLICY_SLOT` per-step debit to a
  real conserving Transfer / prepaid lease. Add `SenderAuthorized` +
  revocation-root witness on `advance_step` to close `cwm_safety_forever`
  (revoked clearance dies mid-charter). Make the actor clearance a
  cap-attenuated credential minted per officer, not a raw label.
- **compose-with:** The clearance/approval layer over the others: gate
  `agent-orchestration` worker steps and `bounty-board.payout` behind a
  charter advance; append advances to `agent-provenance`; meter per-step
  debit via `billing`. With **confined-swarm**: the charter is the mandate a
  jailed body advances one clearance-checked step at a time; with
  **auditable-fund**: the spend policy draws an auditable fund.

### compute-exchange

- **what-is:** A trustless compute marketplace as one factory-born job cell,
  `POSTED→BID→SETTLED`. `job_cell_program()` (`src/lib.rs:372`) is a
  method-dispatched `Cases` over 8 slots with four caveat organs: BUDGET
  `FieldLteField{BID≤BUDGET}` (`:425`), ACCEPTED `WriteOnce(BID)` (`:429`),
  settle `AffineEq{PAID+REFUNDED−BUDGET=0}` + no-mint `AffineLe` (`:398`,
  `:450`), LIFECYCLE `StrictMonotonic(STATE)` (`:459`); unknown methods
  default-deny. Bonus `ComputeFundVault` (`:189`) is a pooled multi-sponsor
  fund on the proven `ShareVault` house-capacity.
- **power-now:** Fully load-bearing; 29 tests across 5 files incl.
  `factory_birth.rs` (over-budget + double-settle refused on a born cell) and
  `compute_fund.rs` (conservation, inflation-attack defeated). Three faces.
  `register()` (`:685`) **unwired**; not seeded.
- **make-it-stronger:** Wire `register()` (one line). Attenuate a real
  provider cap down the ladder via `CapTemplate{attenuatable:true}` (`:497`).
  Settle out of `ComputeFundVault` custody via a prepaid execution-lease.
  Gate `settle` on a zkOracle/R2 attestation that the SPEC_HASH work was
  delivered. Federate the `dregg://` sturdyref (`:889`) for cross-membrane
  bidding.
- **compose-with:** `ComputeFundVault` bridges to **auditable-fund**. With
  **confined-swarm**: SPEC_HASH is a work order a jailed body runs, settle
  pays it via the conserving split. Pipeline: `bounty-board` (discovery) →
  compute-exchange (escrowed settle) → `identity`/`nameservice` (party
  binding).

### domains

- **what-is:** BYO custom-domain binding (ACME-style proof-of-DNS-control) as
  a per-domain sovereign cell, 6 slots (`src/lib.rs:109`).
  `domain_invariants()` (`:211`): `WriteOnce(DOMAIN/OWNER/CHALLENGE_NONCE)` +
  `Monotonic(VERIFICATION_STATE/VERIFIED_SEQ)` — takeover / nonce-reissue /
  un-verify are executor refusals; SITE is free-repoint. `cap.rs` bind-cap is
  a real `dregg-auth` ed25519 caveat-chain (`verify_bind_authority` `:118`,
  `mint_domain_bind_cap` `:82`, proven no-amplify). DNS seam real (`MockDns`
  in tests, `LiveDns` hickory behind `live-dns`, `live.rs:82`).
- **power-now:** Load-bearing; `starbridge-apps/domains/tests/domain_lifecycle.rs` 3 e2e pass. Not
  seeded; `register()` (`:612`) unused outside tests; no gateway consumer
  wired.
- **make-it-stronger:** Close the honest gap (`:57`): thread DNS-challenge
  issuance through a witnessed-predicate program so an off-challenge verify is
  a refusal. Replace the trusted resolver read with a zkOracle
  proof-of-TXT-record on `verify`. Prepaid execution-lease on `bind` to meter
  the Sybil floor. Federate the binding set so `site_for_host` is
  light-client-verifiable across a gateway fleet (not a single-process map).
- **compose-with:** Explicit dual of **nameservice** (name granted vs domain
  proven). Feeds **edge-mandate** / gateway (`is_verified` an on-demand-TLS
  gate; `site_for_host` a Host→site router). With **confined-swarm**: the
  attenuated bind-cap is exactly what a jailed agent should hold to bind one
  domain.

### edge-mandate

- **what-is:** Binds an SSH pubkey → dregg account + spend-ceiling +
  attenuated tool-set as one "mandate cell", lowered to an OpenSSH
  forced-command line. 7-slot `CellProgram::Predicate` (`src/lib.rs:363`):
  `AffineLe(spent−budget≤0)` + `WriteOnce(SUBJECT/ACCOUNT/BUDGET/CAPS_DIGEST)`
  + `Monotonic(SPENT/REVOKED)` + `StrictMonotonic(EPOCH)`. Authority object
  `CapMandate` is a caps lattice with `le`/`attenuate`/`authorizes`
  (`:171`+), lifted from `dregg_auth::Grant`. `authorized_keys_line` (`:944`)
  is a pure fn of committed state, `None` if revoked.
- **power-now:** Load-bearing; three faces; `starbridge-apps/edge-mandate/tests/edge_mandate.rs:81` real
  factory-birth (enrol→spend→over-budget REFUSED→revoke). Not seeded; live
  sshd deploy step out-of-crate (`:88`).
- **make-it-stronger:** Hand the minted `SelfCell` cap (`:396`) to the hosted
  session as a further-attenuatable ocap so the attach session runs UNDER it.
  Make each `spend` an R2-attested receipt. Replace the raw BUDGET scalar with
  a composed execution-lease. zkOracle-attest off-ledger vendor spend.
- **compose-with:** Same `Mandate` lattice as **agent-orchestration** at an
  access edge. With **confined-swarm**: each enrolled key drops into a
  confined `dregg-agent attach` session (`Confinement::Hosted` `:582`) — so
  edge-mandate is the front-gate admitting members INTO a confined swarm.
  Stack: execution-lease underwrites the budget.

### escrow-market

- **what-is:** A sealed atomic-swap marketplace ("X iff Y"). Core
  `SealedEscrowMarket` (`src/lib.rs:180`) wraps the protocol-proven
  `dregg_cell::escrow_sealed` (imaged by `metatheory/…/SealedEscrow.lean`):
  `open` seals terms + stands up per-asset custody cells; `deposit` runs a
  forge-rejecting `deposit_leg`; `settle` is atomic 2-of-2; `reclaim` a
  one-shot half-open defence. A demoted legacy slot-caveat lifecycle
  (`escrow_cell_program()` `:373`) carries TRUSTLINE `FieldLteField` +
  MAILBOX `WriteOnce` + FLASHWELL `AffineEq{RELEASED+REFUNDED−ESCROWED=0}` +
  LIFECYCLE `StrictMonotonic`. `EscrowVault` (`:1176`) is the `Payable` face.
- **power-now:** Heavily load-bearing. `starbridge-apps/escrow-market/tests/cross_app_value_flow.rs:94`
  proves the FIRST cross-app token flow: bounty-board mints CREDIT → pays
  escrow via shared `Payable` → settles onward, Σδ=0 throughout on one
  executor (`both_apps_share_one_payable_interface` `:256`). Not seeded;
  consumed as a library by **first-room** / starbridge-v2.
- **make-it-stronger:** Land the named in-circuit `SettleEscrow` effect
  (`service.rs:30`) so a light client (not a re-executor) witnesses
  settle-atomicity from a batch (R2). Add a per-party attenuated-cap ladder
  (deposit-cap can't settle). Prepaid execution-lease on `open` to bound
  custody lifetime / auto-reclaim ghosted legs. zkOracle-attest delivery.
- **compose-with:** Already composes with **bounty-board** via `Payable`.
  `EscrowVault` makes any Payable app a value source/sink. With
  **auditable-fund**: the FLASHWELL conservation predicate is the flagged
  first customer for `dregg-userspace-verify` (verify a closed deal's
  conservation from receipts without re-executing). With **confined-swarm**:
  the settlement primitive for a swarm's metered task payout.

### first-room

- **what-is:** A runnable composition exemplar — owns NO
  FactoryDescriptor/CellProgram by design (`card.rs:5`). Its core is the weld
  of two landed organs through ONE `EmbeddedExecutor` (`scenario.rs:349`): a
  JOB organ (`compartment-workflow-mandate::colonist_job` DAG) and an ECONOMY
  organ (`escrow-market` factory-born). Real value leg: `Effect::Mint` onto a
  reward vault cap-gated by `grant_faceted(…EFFECT_MINT)` then
  `EscrowVault::release`→kernel `Effect::Transfer`, asserting per-asset Σδ=0
  (`:461`).
- **power-now:** Fully load-bearing; `examples/first_room.rs` prints the live
  transcript; a 5-cheat battery each provably refused in-band on its named
  tooth (`MonotonicSequence`, `FieldLteField×2`, `ClearanceDominates`,
  `AffineEq`). Example/test-driven; not seeded.
- **make-it-stronger:** The honest seam: the job→pay LINK is a host-side
  `if job_done` gate (`scenario.rs:435`), NOT an in-circuit cross-cell caveat
  (`dregg_cell::Preconditions` constrains only the action's own target cell).
  Strengthen with a cross-cell StateConstraint binding the pay Transfer to
  `job.cursor == JOB_TERMINAL` (the one named enforcement-primitive gap).
  Wrap the cycle as an R2 attested turn; fork the ledger to run the cheat
  battery as counterfactuals.
- **compose-with:** Already welds **compartment-workflow-mandate +
  escrow-market** (+ storage-gateway-mandate as "David's Door"). Natural
  harness for **confined-swarm**: each swarm member is an inhabitant holding a
  scoped workflow-mandate, refused in-band on the same legs — the room renders
  the whole swarm's genuine actions vs refusals. With **auditable-fund**: swap
  the local CREDIT pool for an audited conserving fund.

### gallery

- **what-is:** A sealed-submission (commit-reveal) juried-curation gallery on
  one factory-born cell. Seal `BLAKE3_derive_key(…, artist‖piece‖nonce)`
  (`src/lib.rs:106`). `gallery_cell_program()` (`:370`) is `Cases`: an Always
  case with `gallery_invariants()` (every board slot + curator/featured
  `WriteOnce`, `Monotonic(PHASE)` floor) plus `StrictMonotonic(PHASE)` scoped
  to close/curate; default-deny. `next_free_submit_slot` reads live state to
  avoid collisions (`:754`).
- **power-now:** Load-bearing; floor + factory-birth + deos-seam + service
  tests prove swap-refusal (WriteOnce) and rewind/stall-refusal
  (StrictMonotonic) on a born cell. Not seeded.
- **make-it-stronger:** Give curation settlement teeth by borrowing the
  sealed-auction settlement leg (README notes gallery deliberately has NO
  settlement leg). Mint attenuated per-artist submission caps so each artist
  gets exactly one slot. zkOracle-attest the featured merit-score so
  `featured()` (currently max-digest) is a witnessed jury verdict.
- **compose-with:** Shares the exact commit-reveal core with
  **sealed-auction** (gallery=display, auction=payout). Pairs with
  **bounty-board** (a bounty funds an open call). **auditable-fund** supplies
  the prize pool it lacks. **confined-swarm**: confined agent-artists each
  hold an attenuated submit cap; the program guarantees no member
  front-runs/swaps another's piece.

### sealed-auction

- **what-is:** A first-price sealed-bid auction settling through the verified
  per-asset executor. `Bid{bidder,value,nonce}` seals as `BLAKE3_derive_key`
  (`src/lib.rs:127`), Rust image of Lean `SealedAuction.sealOf`. `reveal`
  rejects any seal not in `commitments` (anti-front-run `:265`); `settle`
  folds a two-leg `award_ring` through `dregg_intent::verified_settle`
  (atomicity + conservation). On-ledger floor `auction_factory_descriptor()`
  (`:540`) bakes `WriteOnce(SELLER/HIGH_BID/WINNER)` + `Monotonic(PHASE)` +
  `WriteOnce(COMMIT_BASE+i)` per bidder; `StrictMonotonic(PHASE)` on
  close/resolve.
- **power-now:** Load-bearing; 12 in-crate tests (full-flow settle,
  conservation, atomicity-abort on unfunded winner, impostor rejection,
  uncommitted-cannot-win) + floor/factory-birth. Mirrors
  `metatheory/…/SealedAuction.lean`. `register()` (`:979`) unwired; not
  seeded.
- **make-it-stronger:** zkOracle-attest the winner selection (`winner()` is a
  plaintext max; an attested-argmax removes trust in the auctioneer).
  Attenuate the bidder tier into a per-bidder single-use commit cap. Prepaid
  execution-lease on resolve so award is guaranteed-funded before commit opens
  (removes the `SettlementRejected` abort). Federate the descriptor VK so
  multiple nodes birth the same auction and agree the winner.
- **compose-with:** Settlement rides `dregg-intent::verified_settle`, shared
  with **escrow-market** / **supply-chain**. With **auditable-fund**: the
  award ring debits an audit-trailed conserved fund. With **confined-swarm**:
  the sealed-bid mechanism is a task/compute-slot allocator for confined
  agents competing for a slot.

### governed-namespace

- **what-is:** Governance-bound atomic route-table swap on a Sovereign cell —
  a full **propose → vote → commit** lifecycle (grounded in detail in §2.1c).
  `governance_program()` (`src/lib.rs:323`) is a `CellProgram::Cases`
  (default-deny) over 6 slots: `governance_committee_root`(2, `WriteOnce`),
  `threshold`(3, `WriteOnce`), `pending_proposal_root`(5). Propose/vote gated
  by `SenderAuthorized{PublicRoot{set_root_index:2}}`; commit carries a
  threshold-signature `Authorization::Custom{WitnessedPredicate{Custom{vk_hash:
  GOVERNANCE_VK}}}` (`:890`) with the sig in `witness_blobs[0]`. A
  `GovernanceCommitReactor` (`reactor.rs:47`) auto-fires `commit` once
  `tally ≥ threshold` (`:103`).
- **power-now:** Load-bearing floor. **SEEDED** (`starbridge_seed.rs:482`).
  Rich tests incl. `commit_threshold_sig.rs` (real k-of-n BLS via
  `dregg-federation`+`dregg-hints`) and the reactor driving a real executor
  end-to-end. Honest caveat: the executor's cryptographic acceptance of the
  `Authorization::Custom` proof depends on the propagation lane (`:125`); the
  slot-caveat regressions pass regardless.
- **make-it-stronger:** Register a real `GOVERNANCE_VK` threshold verifier so
  `commit` becomes an in-circuit accept (the one open seam). Weighted /
  quadratic voting by attesting vote-weight via a zkOracle. Cap-attenuation:
  mint per-member vote-only facets so a member delegates a *vote-only*
  attenuation. R2-attested `commit` so cross-federation light clients witness
  the swap.
- **compose-with:** The constitutional root for a resource: mounts
  **nameservice** name-cells as governed routes; credential-gated voting
  composes **identity** presentations as a vote precondition; committee
  membership can be an **org** role-cap set. With **confined-swarm** /
  **auditable-fund**: the committee-gated policy-swap root for a swarm's route
  table or a fund's policy.

### guard

- **what-is:** Per-subject abuse-governance (makes a KYC-free substrate
  responsibly openable). `guard_program()` (`src/lib.rs:303`) is `Cases`
  (default-deny), 5 slots. Two teeth: a metered rate ceiling
  (`FieldLteField{consumed ≤ ceiling}` + `Monotonic(consumed)`) and **account
  standing** (`good`/`flagged`/`suspended`) that only a governance-gated
  `set_standing` case can move (`SenderAuthorized{PublicRoot{GOVERNANCE_ROOT}}`
  `:359`), while `consume_quota` freezes `standing` `Immutable` (no
  self-write). `effective_ceiling` (`:201`): suspended→0, flagged→base/2.
- **power-now:** Load-bearing + reused; `consume_admit` is differential-tested
  byte-for-byte against the verified `tool_access_delegation::deleg_admit`
  Lean mirror (`:991`). Not seeded.
- **make-it-stronger:** Make `governance_root` a real **org** admin role-cap
  set (multi-authority moderation). Prepaid execution-lease: bind `ceiling` to
  a paid lease so quota is purchasable, not `WriteOnce`-frozen.
  zkOracle-attested abuse signals feeding an automated `set_standing`.
  Federation-consensus standing so a suspend on one node propagates.
- **compose-with:** Directly reuses **tool-access-delegation**'s verified
  counter+ceiling. Standing tiers gate any downstream app's `Effect` (a
  suspended subject's ceiling=0). With **confined-swarm**: the per-agent abuse
  ceiling + standing for jailed bodies; with **auditable-fund**: rate-limits
  fund operations per subject.

### identity

- **what-is:** Userspace verifiable credentials over `dregg-credentials` (all
  ZK — blinded merkle, predicate disclosure, ring proof, non-revocation —
  lives in that crate). Per-issuer Sovereign cell. `issuer_program()`
  (`src/lib.rs:210`): `WriteOnce(SCHEMA_COMMITMENT)`,
  `MonotonicSequence(ISSUANCE_COUNTER)` (closes replay),
  `Monotonic(REVOCATION_ROOT)` (append-only),
  `SenderAuthorized{PublicRoot{ISSUER_AUTH_ROOT}}`. Present/verify builders
  emit only commitments (no PII).
- **power-now:** Load-bearing; the `SenderAuthorized` authority tooth is REAL
  on the green path (`EmbeddedExecutor` defaults to the STARK-backed
  `MerkleMembershipStarkVerifier`; a non-member issuer is refused even with a
  genuine proof for its own pk, the app's `deos_seam.rs` tooth d). **SEEDED**
  (`starbridge_seed.rs:480`). `credential_set_commitment` (`:1129`) reduces
  `(issuer,schema)` to an `AuthorizedSet::CredentialSet` other apps bake into
  `SenderAuthorized`.
- **make-it-stronger:** Land the G39 non-revocation STARK so verify binds
  `REVOCATION_HASH` to the slot directly (`:410` TODO). Multi-sig issuance
  (KYC notary + bank co-signer, anticipated `:170`). zkOracle attestation to
  bootstrap issuer trust. Fork a confined presentation session per
  relying-party.
- **compose-with:** THE credential-across-trust-boundary keystone (issuer cell
  is a `dregg://` sturdyref a foreign-federation verifier reacquires). Feeds
  **governed-namespace** credential-gated voting, **guard**
  subject-attestation, **org** member identity, and any app's
  `SenderAuthorized{CredentialSet}` — **this is the eligibility primitive the
  voting app draws on.**

### kvstore

- **what-is:** A verified key-value register store — the worked
  CELLS-AS-SERVICE-OBJECTS exemplar. `store_program()` (`src/lib.rs:204`) is
  `Cases`: `put`/`delete` carry `Monotonic(VERSION)`, `put` additionally the
  capacity tooth `FieldLte(COUNT ≤ CAPACITY)`; a catch-all `Always` admits
  agent nonce turns. `get` is the named OFE cross-cell-read seam (`KvStore::get`
  always refuses to desugar, `:388`). Handles route through
  `invoke_with_descriptor` (double-enforced auth: front-door + executor
  signature).
- **power-now:** Load-bearing service primitive but **no `FactoryDescriptor`**
  (a service cell, not a factory-minted family — no factory-birth path). Not
  seeded.
- **make-it-stronger:** Add a `FactoryDescriptor` so stores are factory-born
  with cap-attenuation (a read-only attenuated handle vs a writer).
  `SenderAuthorized` per-register ACLs. Prepaid execution-lease metering
  writes. R2-attested turns so the KV history is a light-client-replayable
  audit log.
- **compose-with:** The generic verified-state substrate other apps mount for
  config/index: backs **governed-namespace**'s service registry index, **org**
  roster caches, **nameservice** reverse-index. With **confined-swarm**:
  per-agent scratch state; with **auditable-fund**: a rollback-proof balance
  ledger.

### nameservice

- **what-is:** A per-name Sovereign-cell registry (rent + ownership state
  machine), generic Effects only — the largest and anchor/exemplar app
  (`src/lib.rs`, 2299 lines). `name_cell_program()` (`:219`) over slots
  `NAME_HASH`(2, `WriteOnce`), `EXPIRY`(4, `Monotonic`), `REVOKED`(5,
  `WriteOnce` tombstone), `OWNER_PK`(7), `PENDING_OWNER_PK`(8). The
  sophisticated part is `owner_authorization_constraints()` (`:285`) — F1–F7
  single-level `AnyOf` disjunctions encoding "owner-image + authority-register
  move only by the current owner; authority rotation is a staged
  propose→accept handoff signed by the incoming key". A credential-gated
  attested tier (`build_register_with_credential_action` `:1418`).
- **power-now:** Load-bearing floor with the strongest sender-authorization
  proof of the set. **SEEDED first** (`starbridge_seed.rs:479`; genesis
  `nameservice-registry` marker `:588`). Richest test suite (9 files). Each
  name cell is a `dregg://` sturdyref (web-of-cells keystone).
- **make-it-stronger:** `FieldDelta(EXPIRY, +rent_epoch)` for exact renew
  (Tier-1 TODO `:542`). Dispute-resolution + reverse-index factories (blocked
  on paired escrow / `CommittedMap`). Prepaid execution-lease as the rent
  mechanism itself. Cap-attenuate the owner cap into `ResourcePrefix` facets
  for subdomains. zkOracle-attested off-chain DNS bridge.
- **compose-with:** `RESOLVE_TARGET` points names at any reacquirable cell —
  resolves **governed-namespace** routes, **identity** issuers, **org** cells,
  **kvstore** stores by name. With **confined-swarm**: name the
  agents/services; with **auditable-fund**: name the fund + payees.

### org

- **what-is:** Teams/organizations (IAM) with no new authorization primitive —
  a role IS an attenuation of the dregg-auth cap lattice. Org cell slots
  (`src/lib.rs:114`): `ROOT_PUBKEY`(0, `WriteOnce`), `SEQ`(2, `Monotonic`
  audit height), `NAME`(4, `WriteOnce`). Two enforcement surfaces: executor
  invariants (identity/name sealed, audit append-only) and **role-cap
  attenuation** — `role.rs` maps Role→Permission set; `cap.rs` mints the
  org-owner grant `AnyOf(ALL)` pinned `AttrEq{org}` and `attenuate_to_role`
  appends one `AnyOf(role perms)` caveat. No-amplify proven at
  `metatheory/Dregg2/Authority/Caveat.lean attenuate_subset` (a viewer
  appending `write` makes the meet unsatisfiable, never wider).
- **power-now:** Load-bearing dual-surface; the role-cap authorize (viewer's
  admin attempt refused unforgeably) is REAL. Not seeded. Honest gap (`:63`):
  the roster's source of truth is the pure `Org` record mirrored into the
  heap; threading full roster mutation through a per-member `SetField`
  allow-list program is the modeled production lane.
- **make-it-stronger:** Close the gap — a `Cases` program with per-member
  `SetField` allow-list so off-roster writes are executor refusals.
  Time-boxed role-caps via the existing `NotAfter` attenuation as prepaid role
  leases. Federation-consensus org so membership replicates. R2-attested
  membership turns.
- **compose-with:** The IAM layer for every other app — org role-caps become
  the `SenderAuthorized`/committee sets in **governed-namespace** (committee =
  org admins), **guard** (`governance_root` = org moderators), **identity**
  (issuer authority = org), **nameservice** (org-owned names). With
  **confined-swarm**: orgs own agent fleets with role-gated control; with
  **auditable-fund**: org roles gate treasury actions (Billing pays, Owner
  transfers). **For voting: an org is a natural electorate — its roster is the
  `ELECTORATE_ROOT`.**

### storage-gateway-mandate

- **what-is:** A content-addressed object-store mandate. 9 slots
  (`src/lib.rs:105`): `VOLUME_SPENT` (Monotonic debit),
  `COMMITMENT_ANCHOR/VOLUME_CEILING/KEY_PREFIX_HASH/READ_COMPARTMENT`
  (WriteOnce), plus `CLEARANCE_GRAPH_ROOT`+`ACTOR_CLEARANCE` feeding a
  `StateConstraint::ClearanceDominates` MLS-style graph-walk
  (`clearance_dominates_constraint` `:250`). `sgm_cell_program` (`:327`) is
  `Cases`: GET gated by clearance-dominance, PUT by prefix, all bounded by
  `FieldLteField(VOLUME_SPENT ≤ VOLUME_CEILING)`.
- **power-now:** Load-bearing + **SEEDED** (`starbridge_seed.rs:484`). Tests
  incl. `sgm_lean_differential.rs` mirroring
  `metatheory/…/StorageGatewayMandate*.lean`. The `ClearanceDominates` tooth
  is a real executor refusal.
- **make-it-stronger:** Attach an R2 attested turn so each PUT carries a
  content-attestation receipt (payloads sit off-slot). Wire a prepaid
  execution-lease so `VOLUME_CEILING` is a purchased slice. Cap-attenuate to
  mint scoped read-only sub-gateways (delegate a compartment).
- **compose-with:** Payload store for **subscription** (queue holds
  key-hashes, gateway holds bytes) and **supply-chain-provenance** (custody
  docs). A **confined-swarm** worker gets a rate-attenuated PUT cap;
  **auditable-fund** meters `VOLUME_SPENT` as billable.

### subscription

- **what-is:** A publisher/consumer queue = the `CapInbox` rebuilt as
  cell-programs. 8 slots (`src/lib.rs:199`): `SEQ_HEAD`/`SEQ_TAIL`
  (`MonotonicSequence`, invariant tail≤head), `PUBLISHERS_ROOT`/
  `CONSUMERS_ROOT` (auth sets). `subscription_program` (`:303`) is `Cases`,
  each method pinning `SenderAuthorized{PublicRoot}` + per-slot `Immutable`.
  `build_bounty_state_publish_action` (`:868`) is a cross-app bridge.
- **power-now:** Load-bearing + **SEEDED** (`starbridge_seed.rs:481`).
  Heaviest test suite (22 program tests). Has a `Reactor` for event-driven
  consume.
- **make-it-stronger:** zkOracle attestation so a consumer proves it consumed
  message N without revealing payload. Federation/consensus so head/tail
  replicate (multi-writer queue). Prepaid-lease per publish for
  spam-resistance beyond `CAPACITY`.
- **compose-with:** Already bridges to **bounty-board**; it's the event bus
  for **swarm-orchestration** (dispatch notifications) and **tussle** (frame
  events). **confined-swarm** agents publish/consume tasks; store payloads in
  **storage-gateway-mandate**.

### supply-chain-provenance

- **what-is:** Single-custodianship as a *conservation law*. Item cell slots
  (`src/lib.rs:134`): `CUSTODIAN` (`AnyOf[Immutable, SenderInSlot]` — the
  actor-bound baton; flips only in a turn signed by the incoming holder),
  `EPOCH` (`StrictMonotonic`), `HEAD` (`Monotonic`), `LINK_BASE+i` (`WriteOnce`
  custody-receipt digests). A handoff is a cap-attenuated transfer
  (`item_factory_descriptor:360`). **Axis 5:** `derived.rs` certifies a
  provenance summary as a non-forgeable derived view via `dregg_query` Q1
  conjunctive-query + Q2 MMR `server_cannot_omit_position` non-omission proof
  to a light client.
- **power-now:** Load-bearing, not seeded. Forged-handoff refused on two real
  teeth (cap-graph + `SenderInSlot`). Uses the strongest query substrate
  (`dregg-query`).
- **make-it-stronger:** Each handoff link embeds a physical-scan R2
  attestation. zkOracle for off-chain custody events. Federation so the item
  cell migrates custody across nodes with consensus on `EPOCH`.
- **compose-with:** The `dregg-query` non-omission proof is the reusable jewel
  — hand it to **nameservice** (prove no name omitted) and **auditable-fund**
  (prove no transaction omitted) — **and to the voting tally (prove no ballot
  omitted).** Custody docs live in **storage-gateway-mandate**.

### swarm-orchestration

- **what-is:** A COORDINATOR dispatch-board cell coordinating WORKER agent
  cells with cap-secured, receipted budget. 5 slots (`src/lib.rs:124`): `LEAD`
  (WriteOnce), `BUDGET` (WriteOnce mandate), `SPENT_A`/`SPENT_B` (Monotonic
  worker meters), `EPOCH` (StrictMonotonic). Keystone caveat `AffineLe {
  spent_a + spent_b − budget ≤ 0 }` (`:166`) — atomic collective budget.
  **Dispatch is async**: coordinator `EmitEvent` deposits a wake, the worker
  DRAINS in its own separate receipted turn (two receipt hashes; causality
  visible, synchronization not forced).
- **power-now:** Load-bearing, not seeded. Budget-breach + over-grant are real
  executor refusals (`AffineLe` + cap-graph). Fixed-arity today
  (`WORKER_METERS=2`).
- **make-it-stronger:** Generalize past 2 workers to an N-worker
  Merkle-rooted meter set. Give each worker a cap-attenuated sub-budget
  (delegate a slice of `BUDGET`, non-amplifying). Prepaid execution-lease so
  `BUDGET` is purchased. R2 attested turns so a worker's act leg carries
  proof-of-work.
- **compose-with:** This IS the orchestration layer for the **confined-swarm**
  flagship — jailed agent bodies become the WORKER cells, egress metered
  against `SPENT_x`; **tool-access-delegation** mandates ARE the caps workers
  dispatch under; **subscription** carries the wake events; **auditable-fund**
  settles worker payouts against `BUDGET`. (Note: `agent-orchestration` is the
  durable/audited cousin; the two should unify.)

### tool-access-delegation — the capability-attenuation app

- **what-is:** The object-capability model for AI tool/MCP delegation. A
  grantor mints a mandate cell whose caveats the executor checks on every
  invocation. 4 slots (`src/lib.rs:84`): `CALLS_MADE` (Monotonic rate-counter,
  `FieldLteField ≤ rate_limit`), `RATE_LIMIT`/`DEADLINE`/`TOOL_ID` (all
  `WriteOnce`). **Attenuation is the point** (`:20`): `delegate(worker)` emits
  `Effect::GrantCapability(invoke-cap → worker, NARROWED)` grounded on
  `intent/src/agent_mandate.rs::Mandate::sub_delegate` (strictly narrows
  keep/budget/caveat); `derive_no_amplify` (`:466`) guarantees a re-grant is
  narrowed never widened. `revoke` uses `Effect::RevokeDelegation`.
- **power-now:** Load-bearing, not seeded. Rust surface for verified
  `metatheory/Dregg2/Apps/ToolAccessDelegation.lean` (7 `#assert_axioms`-clean
  theorems: over-rate/past-deadline/out-of-scope/conserves/no-amplify/forged/
  revoked all rejected). Over-rate/deadline/scope are real executor `= none`
  refusals.
- **make-it-stronger — directly serves the liquid-democracy vote-cap
  design:** a vote-cap IS exactly this mandate (`TOOL_ID`→proposal-scope,
  `RATE_LIMIT`→vote weight, `delegate`→transitive vote delegation). The
  `sub_delegate` non-amplification already guarantees a delegated vote can't
  exceed the delegator's weight. Add a multi-hop delegation-chain proof (each
  hop narrows, chain re-derivable like supply-chain's links), a `WriteOnce`
  delegatee-set so re-delegation is auditable, and prepaid-lease so votes are
  metered.
- **compose-with:** The cap-minting substrate under **swarm-orchestration**
  (worker invoke-caps) and **confined-swarm** (a jailed body's single egress
  door = a `TOOL_ID`-scoped mandate); pairs with **subscription** (audit
  reactor publishes invocation logs). **This is the delegation engine the
  voting app's liquid democracy is built on.**

### tussle

- **what-is:** A two-figure fighting-game frame engine on a two-cell DeosApp.
  Each figure cell has 4 joint slots pinned to a `JointState` enum via
  `StateConstraint::SymMemberOf` (the typed-`sym` atom — an out-of-enum pose is
  refused; `Figure::joint_program:239`). `PHASE` (`Monotonic`,
  COMMIT→REVEAL→RESOLVED); move flow is commit-reveal
  (`fire_commit_move/reveal_move/resolve_frame`). `resolution.rs`: scoring is a
  conserving bank→figure transfer, not a mint.
- **power-now:** Load-bearing gameplay, not seeded. The commit-reveal
  `Monotonic(PHASE)` and `SymMemberOf` are real fire-path executor refusals;
  score-conservation is a balanced transfer leg.
- **make-it-stronger:** Hidden-move commit-reveal is a natural zkOracle/attested
  fit (prove a revealed move matches its seal in-circuit). Fork the ledger to
  run speculative rollback/replay of frames. Federation/consensus for
  multiplayer matchmaking.
- **compose-with:** Its commit-reveal phase machine is a reusable pattern for
  **tool-access-delegation** sealed-bid vote-caps and **subscription**
  fair-ordering (**and for the secret-ballot voting design's commit-reveal
  tally**). A **confined-swarm** could field AI fighters; **auditable-fund** as
  the wager/prize pool.

### execution-lease (substrate primitive)

- **what-is:** Durable execution as a PAYABLE RESOURCE — a fly.io/cloudflare-lite
  provider that LEASES durable execution slots, metered and paid through the
  value layer, no new kernel effect (`src/lib.rs:1`). A lease is a cap-bounded
  cell whose committed HEAP holds the agent's durable execution image
  (`EXEC_COLL`: a checkpoint step + state digest + working memory), folded into
  the cell's state commitment (`compute_heap_root`) so it SURVIVES, is PASSABLE,
  is WITNESSED. The meter is a `obligation_standing::StandingObligation` (owes
  `rent_per_period` every `period` blocks; recurring forge-detectors bite); the
  payment is a `Payable` `pay` desugaring to ONE conserving `Effect::Transfer`;
  the delivery is a `Monotonic` checkpoint-cursor advance; the lapse is
  non-payment (the schedule audit lapses the lease, further delivery refused).
- **power-now:** Load-bearing model with the full 4-axis template
  (core/service/card/deos). Honest gap: "durable execution" is a committed umem
  cell-heap checkpoint, not a real container runtime.
- **make-it-stronger / compose-with:** **This is the "prepaid budget"
  primitive every other app should adopt** — orchestration BUDGET, bounty
  reward escrow, billing cap, storage VOLUME_CEILING, and the voting app's
  time-boxed poll window all want to be real conserved leases rather than
  scalars. `vat` already builds directly on it.

### vat (substrate primitive)

- **what-is:** "HAVE A DREGG COMPUTER" — a private, always-there, durable,
  **forkable** cloud computer that belongs to you, not the provider, because it
  is a receipted cell (`src/lib.rs:1`). It is an `execution-lease` with a
  lifecycle: persist (the lease's committed umem execution image), meter/pay
  (the lease's rent obligation + `Payable` Transfer), and **fork** (clone the
  execution-image cell — the branch/stitch pushout — two divergent computers
  from one point). Adds a lifecycle state machine (`VatState`:
  Created→Running↔Sleeping→Lapsed→Reaped, on a `Monotonic` phase axis + a
  non-monotone up axis) and a placement binding (which backend holds the
  running World).
- **power-now:** Smallest app (832 LOC) — a thin lifecycle + placement layer
  over the lease; the economics + durable cursor are the lease's, re-enforced by
  the same executor teeth.
- **make-it-stronger / compose-with:** The **fork** primitive is the same one
  `branch-stitch-multiplayer` and `confined-swarm` use — a vat is the durable
  home a confined swarm's workers run inside. Compose with `agent-platform`'s R2
  attested turn so a provider "cannot lie about what it did" is a light-client
  fact, not a promise.

---

## Part 2 — the voting deep-dive

Voting on dregg is not a new feature to invent — it is an *assembly* of
primitives that already exist and already bite. This section grounds what
exists across four layers, then designs the substrate-native voting app and
separates **buildable-now** from **new work**.

### 2.1 What already exists

There are **four** governance/voting mechanisms in the tree today, at four
different altitudes. They are complementary, not redundant.

#### (a) Federation-level constitutional consensus — the uncensorable tally

`blocklace/src/constitution.rs` implements the Constitutional Consensus
paper (arXiv:2505.19216): membership itself is voted.

- **The constitution** (`constitution.rs:30`) is `{ participants,
  threshold, timeout_waves, version, routes_commitment }`. `threshold`
  defaults to `2n/3 + 1` (`compute_threshold`, `Constitution::new:63`).
- **Proposals** (`MembershipProposal`, `:184`): `Join` / `Leave` /
  `AmendThreshold` / `AmendRoutes`. `required_votes_for` (`:94`) enforces
  the **H-rule**: changing the threshold `T→T'` needs `max(T,T')` votes — a
  minority cannot lower the bar to seize control, a majority cannot raise it
  to lock others out.
- **Votes are blocks** (`MembershipVote`, `:238`): a vote is a block payload
  referencing the proposal block in its causal past. A proposal passes when
  `threshold` **distinct** approving participants exist in the blocklace
  *and* the proposal is in a finalized leader's causal past.
- **The tally** (`VoteTracker`, `:257`): `record_vote` (`:301`) admits only
  current participants (`is_participant`) and dedups by voter key into a
  `HashSet` (distinct-voter counting is by construction). `has_passed`
  (`:352`) checks the threshold. `proposal_tallies` (`:305`) backs the live
  `GET /api/membership` surface.
- **Auto-eviction without a vote** (`auto_evict_equivocator`, `:161`): an
  equivocation proof (two conflicting signed blocks,
  `blocklace/src/lib.rs:253` `EquivocationProof`, `evidence.rs`
  `EvidenceOfEquivocation`) is self-evident — the equivocator is removed
  immediately, threshold recomputed. This is the poster's "equivocators
  auto-evicted".

This layer is **uncensorable by construction**: votes ride the blocklace,
so no operator can drop a ballot without it surviving in a peer's causal
past, and the tally is a distinct-voter set anyone re-derives. The safety
floor under it is the non-domination theorem (§2.2).

#### (b) Polis council — in-cell M-of-N quorum (the reusable ballot-in-a-cell)

`starbridge-apps/polis/src/lib.rs` `council` module: a governance cell whose
`StateConstraint` program IS an M-of-N approval machine.

- A `CouncilCharter { members, threshold }` content-addresses to a
  `FactoryDescriptor` — the `factory_vk` IS the governance terms ("is this
  the constitutional council?" is a hash check, `lib.rs` docstring `:24`).
- **The threshold gate is a single `AffineLe`** (`:637`):
  `AffineLe { terms: (M, APPROVED_FLAG_SLOT) ∷ [(−1, approval_slot_i) | i], c: 0 }`
  — i.e. `M·flag − Σ approvalᵢ ≤ 0`. Arming the certified flag *demands*
  `Σ approvals ≥ M` in the same post-state; `APPROVED`/`EXECUTED` require
  `flag == 1`. Per-member approval slots are `MemberOf{0,1}` + `Monotonic`
  (no un-approve) + `BoundedBy` a staged proposal (`:661`–`:671`).
- **Actor-bound approvals** (`:680`): with published member keys each
  approval slot carries `AnyOf[Immutable{slot_i}, SenderIs{member_i}]` — a
  slot flips only in a turn *sent by* that member. A stolen/shared capability
  cannot flip another member's slot; the operator cannot relay approvals
  (the e2e `approval_slots_are_actor_bound`).

This is the **general "a quorum decision in one cell" primitive** — a
tally, a threshold, and distinct-voter binding, all executor-enforced, all
light-client-legible (`inspect_council` decodes it from 16 slots). It is the
16-slot cell's structural ceiling (`AffineLe` over ≤ ~3 member slots),
documented at `:886`.

#### (c) governed-namespace — propose → vote → commit with a Reactor auto-committer

`starbridge-apps/governed-namespace/src/lib.rs`: a full governance lifecycle
over a resource (a route table). Three methods (`:66`–`:85`):
`propose_table_update` → `vote_on_proposal` → `commit_table_update`. The
pending proposal + vote tally lives in `pending_proposal_root` (slot 5,
per-method caveats); `governance_committee_root` (slot 2, `Immutable`) and
`threshold` (slot 3, `Immutable`) pin the electorate; the commit is an
`Authorization::Custom` **threshold-signature carrier** (`:127`) verified by
a registered verifier, and a **`Reactor`** (`:190`) watches for committed
votes and *auto-fires* the swap at quorum. This is the pattern for "a vote
that, on passing, atomically executes an effect".

#### (d) privacy-voting — the one-person-one-vote ballot substrate

`starbridge-apps/privacy-voting/src/lib.rs` (SEEDED, `starbridge_seed.rs:485`;
live `dregg voting open|tally|close` CLI). Two factory-born cell kinds:

- **Poll cell** (`poll_factory_descriptor` `:197`): `WriteOnce(QUESTION_HASH)`,
  `Monotonic(TALLY_YES/NO/ABSTAIN)`, `WriteOnce(CLOSED)`. A tally can only
  ever *increase* (no erasing votes), the question is fixed, the poll closes
  once (`poll_state_constraints` `:135`).
- **Ballot cell** (`ballot_factory_descriptor` `:219`): `WriteOnce(POLL_REF)`
  + `WriteOnce(VOTE)` — **one vote per ballot cell**, enforced by the
  substrate (`ballot_state_constraints` `:161`; the tooth
  `double_vote_is_write_once_violation` `:966` and the factory-born e2e
  `factory_born_ballot_enforces_one_vote_per_cell` `:1069`).
- **Unlinkability today** (`:33`–`:42`): ballot cells are minted under a
  caller-chosen blinding `token_id`, so the ballot id `derive_raw(owner,
  token_id)` is not linkable to the voter's primary cell unless the token is
  reused. The `VOTE` slot records the *choice code*, not identity. The
  docstring is honest: a production privacy tier would *additionally* blind
  the choice and prove tally consistency in zero knowledge — "this crate
  lands the unlinkable-ballot-cell + one-vote-per-cell + monotone-tally
  substrate that such a tier composes on top of."
- **Rights ladder** (`:506`): `VIEWER (Signature) ⊂ VOTER (Either) ⊂
  ADMINISTRATOR (None/root)` — read ⊂ cast ⊂ tally/close on the real
  attenuation lattice.

#### (e) The soundness floor — non-domination ≡ unfoolability

`metatheory/Metatheory/Adversary/Model.lean` `non_domination_and_unfoolability`
(`:140`): for EVERY adversary `A`, the operator `A.opCtrl` driving the
enveloped machine can never push it out of the safe floor (non-domination,
`polis_safety`) AND no forged proof `A.forgedPI/forgedProof` is ever accepted
as a genuine kernel step (unfoolability). Both conjuncts are the *same* `∀ A`
over the *same* object (`:120`–`:127`). Axiom-clean (`#print axioms`, `:242`).
This is the formal statement that **whoever runs the vote-hosting node
cannot rig it and cannot forge an accepted tally** — the theorem under an
uncensorable ballot.

The Polis Lean corpus (66 files, `metatheory/Polis/`) supplies the
surrounding theory: `PolisPolitician`, `PolisSandbox*` (adversary/attack
models), `PolisNonConfusion`, `PolisAuth*` (authorization reachability),
`PolisViability`, `PolisGovernorTheory`, `PolisDominationDregg`.

### 2.2 Where the pieces map to voting requirements

| Requirement | Primitive that carries it (today) | Status |
|---|---|---|
| **Eligibility** (who may vote) | a ballot cell minted only to holders of an eligibility cap; council `members` / constitution `participants`; committee root (governed-namespace slot 2) | buildable-now (identity-linked); zk-eligibility = new |
| **One-vote / no-double** | `WriteOnce(VOTE)` on the ballot cell (`privacy-voting:161`); distinct-voter `HashSet` (`VoteTracker:301`); node **nullifier set** `used_proof_hashes` (`node/src/state.rs:196`) | buildable-now |
| **Verifiable tally** | `Monotonic` tally slots + light-client receipt; `inspect_council` / `proposal_tallies` re-derivable | buildable-now (LC read); succinct proof = weld work |
| **Quorum / threshold** | council `AffineLe { M·flag − Σ approvals ≤ 0 }` (`polis:637`); constitution `2n/3+1` H-rule (`constitution:94`); governed-namespace `threshold` slot | buildable-now |
| **Delegation (liquid democracy)** | macaroon caveat attenuation (AND-only, `macaroon/src/lib.rs:9`); `Mandate::attenuate` (`agent-orchestration:210`); a transferable vote-cap | buildable-now (cap transfer); on-ledger delegation graph = light new work |
| **Privacy (secret ballot)** | blinding `token_id` unlinkability (`privacy-voting:36`); macaroon **third-party discharge caveat** (`caveat_3p.rs`) to prove eligibility without revealing identity; zkOracle attestation | partial-now (unlinkable cell); blinded-choice + zk-tally = new |
| **Uncensorability** | votes as blocklace blocks in causal past; equivocator auto-eviction; non-domination theorem (`Model.lean:140`) | buildable-now (on the federation) |
| **Atomic enactment on pass** | governed-namespace `Reactor` quorum auto-committer (`:190`); `Authorization::Custom` threshold-sig carrier | buildable-now |

### 2.3 The design — a substrate-native voting app

The design is a **poll = a cap-bounded, factory-born governance cell**; a
**ballot = a cap** (one vote); a **tally = a verifiable turn**; the whole
thing hostable **on the federation** so no operator can drop a ballot or rig
the count. It generalizes `privacy-voting` (which is the tally substrate)
and folds in the council quorum gate and the governed-namespace enactment
Reactor.

**Cell shapes.**

1. **Poll cell** — extends `privacy-voting`'s poll: `WriteOnce(QUESTION_HASH,
   OPTIONS_ROOT, ELECTORATE_ROOT, QUORUM_M, DEADLINE_HEIGHT)`,
   `Monotonic(TALLY_i)` per option, `WriteOnce(CLOSED)`, plus a **quorum
   gate** lifted from the council: `AffineLe { Σ TALLY_i − QUORUM_M ≥ 0 }`
   guarding the `RESULT` slot so a result can only be certified once quorum
   is met (mirror of `polis:637`). `ELECTORATE_ROOT` is a merkle root over
   eligible voter identities/caps (mirror of governed-namespace's
   `governance_committee_root`, `Immutable`).

2. **Ballot cap** — a factory-born ballot cell (`privacy-voting:219`) minted
   **only** to a holder of an *eligibility capability* (see below):
   `WriteOnce(POLL_REF)` + `WriteOnce(VOTE)`. One vote per ballot is the
   `WriteOnce(VOTE)` tooth that already bites (`:966`, `:1069`). The ballot
   is minted under a blinding `token_id` (`:36`) so the ballot cell is
   unlinkable to the voter's primary cell.

**Eligibility as a cap grant.** The poll issuer holds a root capability over
the poll and grants each eligible voter a *single, non-amplifiable*
`ballot-mint` capability (macaroon attenuation, `macaroon:9`; `Mandate`
lattice, `agent-orchestration:210`). Because macaroon caveats are AND-only
and removing one is HMAC-impossible (`macaroon:10`), a voter cannot widen a
one-ballot cap into two. Eligibility = "you hold a cap in `ELECTORATE_ROOT`".

**One-vote / no-double at three depths.** (i) `WriteOnce(VOTE)` per ballot
cell; (ii) the ballot-mint cap is single-use (attenuated to one birth);
(iii) at the federation level, the vote-proof hash lands in the node
**nullifier set** `used_proof_hashes` (`node/src/state.rs:196`) — the same
mechanism that stops a proof satisfying two conditional turns — so a replayed
ballot proof is rejected network-wide, exactly like the mint dedup the brief
names.

**The tally as a verifiable turn.** Each vote bumps `Monotonic(TALLY_i)` on
the poll cell; the monotone caveat means a stale/replayed value can never
shrink the board (`tally_decrease_is_monotonic_violation` `:989`). Anyone
light-client-verifies the running count off the receipt log (no re-execution;
`inspect`-style decode as in `inspect_council` / `proposal_tallies`). The
**final result** is a single certification turn gated by the quorum `AffineLe`
— it commits only if `Σ TALLY ≥ QUORUM_M` and the deadline passed. On the
federation, that turn is finalized by consensus, so its acceptance is the
`2n/3+1` safety of the blocklace, and non-domination (`Model.lean:140`)
says the operator cannot forge it.

**Delegation / liquid democracy.** A vote-cap is a capability, and
capabilities attenuate and transfer. A voter delegates by handing their
attenuated `ballot-mint` cap to a delegate (or by a `SetField` on a poll-cell
delegation slot recording `voter → delegate`, an on-ledger delegation graph
the tally reads). The AND-only attenuation lattice guarantees a delegate's
authority never exceeds what was delegated; a delegation is itself a signed,
receipted turn (auditable). Re-delegation chains compose exactly like
`Mandate::attenuate` sub-coordinators (`agent-orchestration:201`).

**Privacy (secret ballot), in tiers.**
- *Tier 0 (buildable-now):* unlinkable ballot cell (blinding token,
  `:36`) — the tally sees choices, not identities, and the ballot id does
  not link to the voter's primary cell.
- *Tier 1 (light new work):* prove eligibility **without revealing
  identity** via a macaroon **third-party discharge caveat** (`caveat_3p.rs`)
  or a zkOracle attestation — the ballot-mint turn carries a discharge that
  says "the bearer is in `ELECTORATE_ROOT`" without naming who, the same
  attestation shape `confined-swarm`/`auditable-fund` already compose
  (`dregg_zkoracle_prove::verify_zkoracle`).
- *Tier 2 (real new work):* blind the *choice* and prove tally consistency
  in zero knowledge (a homomorphic/mix-net tally with a succinct proof that
  the published totals equal the sum of blinded ballots). `privacy-voting`'s
  docstring names exactly this as the tier that composes on top (`:39`).

**Uncensorable hosting.** Host the poll on the federation: ballots are
blocklace blocks, so a ballot in any peer's causal past cannot be dropped;
the tally is a distinct-voter derivation anyone recomputes; a
double-voting/equivocating operator is auto-evicted (`constitution:161`).
The whole thing sits under `non_domination_and_unfoolability`
(`Model.lean:140`).

**Enactment.** For governance polls (a proposal that *does* something on
pass), reuse the governed-namespace `Reactor` (`:190`): it watches the poll
cell and, at quorum, atomically fires the enactment effect as one verified
turn — vote-and-execute bound in a single receipt.

### 2.4 Buildable-now vs new work

**Buildable-now** (assembly of shipping primitives, no kernel change):
- Multi-option polls with a quorum gate — extend `privacy-voting`'s two
  factories with the council `AffineLe` quorum tooth and an `ELECTORATE_ROOT`
  `Immutable` slot. All caveats already exist.
- Eligibility-as-cap + single-use ballot-mint via macaroon attenuation.
- One-vote at all three depths (`WriteOnce`, single-use cap, node nullifier
  set) — every mechanism already ships.
- Verifiable monotone tally + quorum-gated result certification, light-client
  readable.
- Cap-transfer delegation (hand the attenuated ballot cap).
- Uncensorable federation hosting (blocklace votes + auto-eviction).
- Reactor auto-enactment on pass (governed-namespace pattern).
- Tier-0 privacy (unlinkable ballot cell).

**New work** (named, not shimmed):
- **On-ledger delegation graph** with cycle-prevention and transitive weight
  accounting (liquid democracy proper) — light: a delegation slot + a tally
  that walks the graph. Cross-cell reads are the documented `polis` gap
  (`polis/src/lib.rs:` "Cross-cell reads"), so the honest carry is copying
  the delegation commitment into the tally turn.
- **Tier-1 zk-eligibility** — wire the macaroon third-party discharge / a
  zkOracle attestation of "in `ELECTORATE_ROOT`" into the ballot-mint turn.
  The attestation primitive ships; the electorate-membership circuit is the
  new piece.
- **Tier-2 secret-choice tally** — blinded ballots + a succinct proof that
  published totals = Σ blinded ballots. This is the genuine cryptographic
  build (the tier `privacy-voting:39` defers).
- **Succinct tally proof** — today the tally is light-client *readable* off
  receipts; a single succinct "the count is C and complete" proof is the same
  batch-circuit weld `billing` / `agent-provenance` also want.

---

## Part 3 — the ranked build menu

Ranked by leverage × tractability. Tiers, not a strict order.

### Tier 1 — high leverage, tractable now

1. **The voting app (buildable-now core).** Extend `privacy-voting` into a
   multi-option, quorum-gated, eligibility-capped poll with cap-transfer
   delegation and Reactor auto-enactment, hostable on the federation. Every
   ingredient ships; this is assembly. The single highest-leverage build —
   it is the app ember named, and it lands a real governance primitive the
   whole app set (and the federation itself) can vote with. *(new work
   deferred: zk-eligibility, secret-choice tally, delegation-graph weight.)*
2. **`Payable`/treasury unification into an escrow-fund spine.** `billing`
   `BillingWallet`, `bounty-board` `BountyTreasury`, and `auditable-fund`
   already share the `Payable` DSI. Land one shared escrow/fund cell that all
   three draw on so payouts, charges, and fund withdrawals are one conserved
   value layer. High leverage: turns 3+ apps into one economy.
3. **Prepaid `execution-lease` as the universal budget.** Replace scalar
   budgets (orchestration BUDGET, bounty reward, billing cap) with real
   prepaid lease cells (conserved, metered, lapsing). One substitution makes
   every app's "budget" a witnessed, fundable resource.

### Tier 2 — high leverage, moderate work

4. **The light-client batch circuit weld** — the *shared* gap named by
   `billing` (allowance ledger + invoice digest), `agent-provenance` (MMR
   completeness), and the voting tally (succinct count). One weld unlocks
   "provable to a non-re-executing verifier" across all three.
5. **Attestation-carrying receipts everywhere.** Bind `agent-orchestration`
   worker steps, `bounty-board` submissions, and voting eligibility to R2
   attested turns / zkOracle attestations (`grain-turn::ATTESTATION_SLOT`
   `:90`; `agent-platform::drive_serving_attested` `:774`). Makes "what the
   agent/voter did" proof-carrying, not asserted.
6. **`branch-stitch` promoted to a reusable session service.** Turn the
   demonstrator into an API so any app forks/diverges/stitches under the
   settlement gate — the multiplayer spine for orchestration plans, bounty
   disputes, and contested charters.

### Tier 3 — composition wins (small glue, real payoff)

7. **`agent-provenance` as the universal audit sink** — append every
   committed receipt hash (orchestration steps, charges, bounty transitions,
   votes) into one `verify_chain`-auditable trail.
8. **`compartment-workflow-mandate` clearance over payouts/enactment** — gate
   `bounty-board.payout` and voting enactment behind a charter advance
   (officer sign-off).
9. **`confined-swarm` ↔ `agent-orchestration` merge** — the jailed,
   provably-independent swarm is the natural body for orchestration's
   mandated workers; unify the two mandate notions.

### Tier 4 — deeper cryptographic work (named, real)

10. **Tier-2 secret-ballot tally** (blinded choices + zk tally proof).
11. **On-ledger liquid-democracy delegation graph** (transitive weight,
    cycle-prevention) — needs the cross-cell-read carry `polis` documents.

---

*Read-only census; no code changed. Grounded at `1ca697a9696`.*
