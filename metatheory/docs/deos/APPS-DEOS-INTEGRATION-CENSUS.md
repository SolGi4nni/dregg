# Apps · deos / web-of-cells integration census

This is the whole-app harsh look: for every app and demo artifact, does it actually use the
deos composition layer — `DeosApp` / `DeosCell` / `CellAffordance` / `GatedAffordance` /
`AffordanceSurface`, the web-of-cells (`CapTpServer`, `dregg://` sturdyref publish, nameservice
announce), and rehydration (`Sturdyref` / `Membrane` / frustum-snapshot)? Each row carries one
verdict, the integration effort, a keep / rebuild / retire call, and the concrete work it would
take.

The frame: deos is the **composition surface**, not the verification layer. An app's *floor* is
its `FactoryDescriptor` + the installed `CellProgram` (slot caveats) + real signed turns through
the executor. The floor is where soundness lives. The deos layer is the *skin*: per-viewer
affordance projection, the cap∧state gate that lights a button off live cell state, the `dregg://`
publish that puts a cell IN the web-of-cells, and the per-viewer rehydratable snapshot. A "floor"
app is correct and load-bearing; it is simply pre-deos at the surface.

## The three shapes a row can be

- **deos-native** — `DeosApp`/`DeosCell`/`CellAffordance` are the app's surface, exercised green:
  per-viewer projection, real verified fires (anti-ghost 403), `dregg://` publish, and per-viewer
  rehydration. *No app's `src/` is here.*
- **partially-integrated** — the floor is real and green, and a deos re-expression exists and
  passes, but it lives in a `tests/reexpress_deos_app.rs` (a side-proof), not the shipped `src/`
  surface. Two of these actually drive the deos stack; the rest have a green floor at full parity
  with the leading cohort but no re-expression yet.
- **pre-deos-toy** — the surface is the old bones: `register(ctx)` wiring a bare `FactoryDescriptor`
  + `InspectorDescriptor`, hand-copied generated JS, `dregg://` appearing only as an inert
  `uri_prefix` inspector string. The floor underneath may still be real and verified (most are) or
  may be a stub / placeholder (a few are).

There is no `infra` row: every entry is an app or a demo artifact, none is a shared library being
censused as plumbing.

## The roster

| App | Verdict | Effort | Keep / Rebuild / Retire | What it would take |
| --- | --- | --- | --- | --- |
| **supply-chain-provenance** | partially-integrated *(deos stack live)* | small | **keep** | Promote `item_spec()`/`item_app()` from `tests/reexpress_deos_app.rs` into `src/lib.rs`; make `register(ctx)` mount the `DeosApp`. Close the one self-disclosed seam: route the fire onto the FULL custody `CellProgram` (a live `TurnExecutor` seeded with `custody_constraints()`) so the actor-bound `AnyOf[Immutable,SenderInSlot]` + `StrictMonotonic(epoch)` + `Monotonic(head)` + `WriteOnce(links)` caveats bite IN the fire path. Replace the scaffold emit/edit stand-ins with the real multi-effect handoff + `Effect::GrantCapability`. Re-expression already written, 9/9 green. |
| **swarm-orchestration** | partially-integrated *(deos stack live)* | small | **rebuild-on-deos** | Promote `board_app`/`board_spec` into `src/lib.rs` as the canonical surface. Replace scaffold emit/edit PLACEHOLDER effects with the real `SetField(meter)+SetField(epoch)+EmitEvent(wake)` dispatch turn. Close the load-bearing seam the test admits: run the fire against the FACTORY-BORN coordinator cell carrying `swarm_constraints()`, so the `AffineLe` budget gate, `WriteOnce` mandate/lead, and `StrictMonotonic` epoch BITE in the deos path. Update `manifest.json` to advertise the `DeosApp` mount instead of raw kernel endpoints. Keep the factory-birth floor as the executor-truth layer. |
| **subscription** | partially-integrated | small | **keep** | The deos re-expression ALREADY exists and is green — it lives in `app-framework/tests/reexpress_subscription.rs` (more complete than swarm-orchestration's). Make it crate-resident: copy it into `subscription/tests/`, and/or add a public `subscription_deos_app(cclerk, executor) -> DeosApp` to `src/lib.rs` from an `AppSpec` mirroring `subscription_spec()`. Promotion/relocation, not authoring. Floor is real and green (factory-birth + 25-case adversarial `program.rs`, real signatures). |
| **agent-provenance** | partially-integrated | small | **keep** | Add a `tests/reexpress_deos_app.rs` (the proven additive recipe its siblings carry) + a `manifest.json`; no floor change. Write a board/log `AppSpec` (reader⊂appender⊂owner ladder), `.into_app()`, assert per-viewer projection + real fires + anti-ghost 403; `.web_of_cells()` + `publish_all` for a real `dregg://` log-cell sturdyref; `snapshot`/`rehydrate` (incomparable identity ⇒ `RehydrateError::Amplification` — the natural deos home for the existing `verify_chain`); `mount()` for `/surface.js` + `/manifest`. Rich multi-effect append drops to a raw `CellAffordance`. Keep a test asserting the `WriteOnce` tooth still refuses an overwrite through the fire path. Floor (real executor, `Authorization::Signature`, factory-birth, `AgentProvenanceGated.lean`) is correct and deos-shaped. |
| **escrow-market** | partially-integrated | small | **rebuild-on-deos** | Add a `tests/reexpress_deos_app.rs` modeled 1:1 on supply-chain-provenance's; NO framework or `src/lib.rs` change (the deos stack is already re-exported from `dregg_app_framework`, an existing dep). Wrap as `CellSpec("escrow")` on the natural ladder (observer Signature⊂buyer Either⊂seller None); `.publish(...)` the escrow cell; `.discoverable(["escrow","marketplace"])`. Drive the axum surface end-to-end: per-viewer projection, cap-gated fires (`/escrow/fire/settle` ⇒ 403 for a buyer, 200 for the seller via the genuine `is_attenuation` gate), `publish_all`, snapshot/rehydrate, `/surface.js` + `/manifest`. Only Cargo delta = dev-deps axum/tokio/tower. KEEP the floor as-is — it is the two-party organ-composed generalization of bounty-board, births through the real factory path, routes every op through the verified executor with real Ed25519, four executor-enforced caveats with adversarial teeth; NOT a kernel-poker. |
| **governed-namespace** | partially-integrated | medium | **rebuild-on-deos** | Re-express the four ops as a `DeosApp::builder` over one `DeosCell` for the namespace cell, exactly as `examples/deos_council_board.rs` does for a propose/approve board: `propose_table_update`/`vote_on_proposal` ⇒ committee-cap affordances, `register_service` ⇒ cap-only, `commit_table_update` ⇒ a `GatedAffordance` whose gate is a `CellProgram::Predicate` precondition (threshold-met AND dispute-window-elapsed). Add `.web_of_cells()` + `.discoverable()`. Drop the four hand-rolled `<dregg-namespace*>` inspectors for the generated `<dregg-affordance-surface>`. Medium because the `Authorization::Custom` threshold-sig path (`GOVERNANCE_VK` `WitnessedPredicate`) is richer than the council-board lattice gate and needs the `WitnessedPredicateRegistry`-into-executor lane wired in. Existing executor-integration tests carry over. |
| **identity** | partially-integrated | medium | **rebuild-on-deos** | Additive deos re-expression in a new `tests/reexpress_deos_app.rs` over the issuer cell, verbatim the two integrated siblings' pattern; leave `src/lib.rs` UNTOUCHED. Declare 4 `CellAffordance`s (issue/revoke/present/verify) carrying the SAME real `Effect` the `build_*_action` turn-builders already produce; `.gated(...)` over the existing `WriteOnce`/`MonotonicSequence`/`Monotonic`/`SenderAuthorized` constraints; map issuer/holder/verifier onto the `AuthRequired` ladder; `.web_of_cells()` + `.discoverable()` to publish the issuer cell (a verifier on another federation reacquires it — the credential-across-trust-boundary story this app IS about); `snapshot`/`rehydrate`; drop the hand-rolled inspectors + JS for the generated component + `manifest()`. No new dep. The honest fire→executor seam is the shared one; the floor's `factory_birth.rs` + `integration_issue_present_verify.rs` already prove the caveats refuse hostile turns. |
| **bounty-board** | pre-deos-toy | small | **rebuild-on-deos** | Add a `DeosApp`/`AppSpec` layer (in `src/lib.rs` or `tests/reexpress_deos_app.rs`). Wrap the four turn-builders as `CellAffordance`s on one `DeosCell`: post/claim/submit/payout. Make them `.gated(GatedAffordance)` with the SAME `StateConstraint` predicates already in the crate (claim gated on STATE==OPEN, submit on CLAIMED, payout on SUBMITTED) so the button-set reacts to live cell state (the htmx tooth) instead of relying only on the executor to reject. `.publish(AuthRequired::Signature)` + `.discoverable(["bounties"])`. All required types ALREADY re-exported from `dregg_app_framework` (an existing dep) — zero new deps. The lifecycle maps onto gated affordances almost verbatim — the canonical 4-state `pending_cond()` approve-button example. Floor (factory descriptor, slot caveats, real signed turns, executor-verified lifecycle + adversarial refusals) is done and correct. |
| **compartment-workflow-mandate** | pre-deos-toy | medium | **rebuild-on-deos** | Re-express on the deos bones, reusing the proven core. Wrap the two methods as `CellAffordance`s: `advance_step` ⇒ `AuthRequired::Signature` gating the existing `SetField`+`EmitEvent`; clearance-label admission (`step_clearance_ok`) maps onto the affordance gate (`is_attenuation`). Bundle as a `DeosCell` + `AffordanceSurface`; build a `DeosApp` with `.publish()` + `.discoverable()`. Register via `register_affordance_surface`/`DeosApp::register`. Replace the 5s-polling custom-element inspector with membrane rehydration. Genuinely-new (why it's medium, not small): the clearance-graph-root verifier (`CLEARANCE_GRAPH_ROOT_SLOT`) and the Stingray spend-policy debit wiring (`SPEND_POLICY_SLOT`). KEEP the proven core: the Lean-mapped factory descriptor + birth caveats and the Lean-differential tooth (`cwm_lean_differential.rs` pins an 8-row vector against `cwmDiffCorpus`). |
| **nameservice** | pre-deos-toy | medium | **rebuild-on-deos** | Re-express on the composed deos framework. Convert the five turn-builders + the credential tier into `CellAffordance`s on a name `DeosCell` (each carries its existing `Effect` verbatim), gated on `AuthRequired` tiers that ARE the roles (public=resolve; owner-cap=renew/transfer/revoke/set_target; credential tier=`AuthRequired::Custom`). Wrap in `DeosApp::builder` with `.publish(...)` + `.discoverable(["names"])` so each registered name cell becomes a real `dregg://` sturdyref — THE payoff: `RESOLVE_TARGET_SLOT` stops storing opaque `blake3(uri)` and starts pointing at reacquirable sturdyrefs, so a nameservice that names the web-of-cells finally lives IN it (and `DeosApp::announce`, which every other app targets, gets its keystone). Projection + rehydration come free. PRESERVE wholesale: factory descriptor, three slot caveats + tests, child VK, the `CredentialSet` cross-app tier, anti-drift constants. |
| **privacy-voting** | pre-deos-toy | small | **rebuild-on-deos** | Add a deos composition layer on top of the good floor. Express the four ops as affordances: open_poll/close_poll as poll-admin-tier, cast_vote as ballot-holder-tier on the ballot cell, record_tally on the poll cell. Bridge each caveat onto a live-state gate via `GatedAffordance::new(affordance, CellProgram)` — it takes exactly the `WriteOnce`/`Monotonic` vocabulary `poll_state_constraints()`/`ballot_state_constraints()` already construct, so a gated cast_vote button lights IFF `VOTE_SLOT` is unset and record_tally lights IFF the increase is monotone (1:1 map, no new constraint logic). `.publish(AuthRequired)` + `CapTpServer` so a federated peer reacquires the live tally board, replacing the inert `uri_prefix` string. The one real subtlety: the scaffold emit/edit path does NOT carry `StateConstraint`s, so use the `DeosCell` + `GatedAffordance` path (the supply-chain sibling shows it). Floor (factory descriptors + caveats + the `factory_born_*` executor tests) stays intact. |
| **sealed-auction** | pre-deos-toy | medium | **rebuild-on-deos** | Add `tests/reexpress_deos_app.rs` + `tests/factory_birth.rs` + a `dregg-app-framework` dev-dep (today it depends only on intent/cell/types/blake3). Model the auction as ONE `DeosCell` on the coordinator cell, with phase + a commitment-board (`WriteOnce`/`Monotonic` commit set) as the `CellProgram` state. Expose three GATED affordances so the cap∧state gate IS the protocol gate: commit (phase==Commit), reveal (phase==Reveal, fired by a bidder holding its own cap), settle (phase==Reveal, lead/seller). `.publish(AuthRequired::Signature)`; per-viewer projection; rehydratable frustum-snapshot of the SEALED board (commitments visible, secret values culled). The hard/novel piece (why medium): putting the commit phase ON-LEDGER (a `WriteOnce`-gated commit-board cell) so anti-front-running is enforced by the executor, not an in-process `BTreeMap` — the README's own named follow-up, what makes the deos version more capable. Settle already routes through `settle_ring_verified`; the 582-line `SealedAuction.lean` proves the protocol; verified core reused wholesale. |
| **storage-gateway-mandate** | pre-deos-toy | medium | **rebuild-on-deos** | Convert the four turn-builders into `CellAffordance`s carrying their existing `Effect` chains, each with an `AuthRequired` gate (init ⇒ Signature/root; ops ⇒ reader/writer tier). Make the ops `GatedAffordance`s so the button reflects live state: the volume budget the factory encodes becomes the gate (`FieldLteField{VOLUME_SPENT, VOLUME_CEILING}` + per-op cost headroom); PUT prefix + GET clearance move from `sgm_admit` into the gated condition. Bundle as `DeosCell`, `.publish(AuthRequired::Signature)` + `.discoverable(["storage"])`; wrap in `DeosApp::builder`; replace `register(ctx)` body with `app.register(&ctx)` + `app.mount()`. Keep the `FactoryDescriptor`. Finally MOUNT it at node startup (the open `DEVNET-COMPOSITION.md` TODO) so it stops being test-only. Medium because the load-bearing primitives all exist. KEEP the load-bearing part: the Lean-mirrored mandate (op allowlist, prefix scope, GET clearance, Stingray budget) with a differential corpus in `StorageGatewayMandate/Core.lean §C`. |
| **tool-access-delegation** | pre-deos-toy | small | **rebuild-on-deos** | Does NOT touch the deos stack at all (grep across the crate ⇒ zero hits); only deos-adjacent token is the inert `uri_prefix` string. Register installs only the OLD bones. The work: a ~25-line `DeosApp::builder` adding one `DeosCell` for the mandate cell with three `CellAffordance`s (grant_tool_access @ grantor / invoke_tool @ worker / revoke_tool_access @ grantor) wrapping the EXISTING `Effect` vectors from the three turn-builders. The worker⊂grantor attenuation ladder is this app's native ocap story, so tiers map cleanly. Yields projection, the `dregg://` publish (mandate cell as a sturdyref a worker on another federation reacquires — the natural home for cross-agent tool delegation), rehydration, the component, the manifest. NOT a throwaway: `factory_birth.rs` drives the genuine executor (grant ⇒ metered invokes ⇒ hostile over-rate/rollback/re-scope all REFUSED) and `lean_differential.rs` pins the admit corpus to `ToolAccessDelegation.lean`. Floor PRESERVED untouched. Side note: Cargo/README claim `Immutable` on rate_limit/tool_id but the code correctly uses `WriteOnce` (stale doc drift). |
| **polis** | pre-deos-toy | medium | **keep** | A PURE cell-program library (depends ONLY on `dregg-cell`): content-addressed `FactoryDescriptor`s whose `StateConstraint` predicate programs ARE the enforced state machines (council M-of-N, constitution-as-program, forward-certified amendments, worker mandates, KERI pre-rotation) + pure `inspect_*` decoders. NOT a toy — mirrors the frozen settlement blueprint, ~28 program tests + e2e teeth, companion `PreRotation.lean`. Squarely pre-deos: zero affordance/web-of-cells/rehydration. KEEP — the program core is exactly the right backing state for `DeosCell`s; integration is ADDITIVE, a wrapper. Medium: (1) add `dregg-app-framework` behind a new `starbridge-polis-deos` crate or a `deos` feature, keeping the pure lib light; (2) wrap each of the 5 families as a `DeosCell` with `GatedAffordance`s whose effect-templates are the existing `sdk/src/polis.rs` turn shapes and whose live-state preconditions are the lifecycle gates already encoded (`TemporalGate`, `KeyRotationGate`); (3) `publish()` into the WebOfCells + `announce()`; (4) membrane snapshots for a light-client board view — matching polis's own stated goal ("governance the polis can READ"). Medium only because the wrapper spans 5 families × multiple affordances + wiring + new tests; the hard core exists and is proven. |
| **anonymous_credit_check** *(demo-agent example)* | pre-deos-toy | large | **keep** | A near-total rewrite as a `DeosApp` over the cell/affordance substrate, not a patch. Add deps the crate lacks (`dregg-app-framework` + affordance/rehydration/captp_server/discovery). Model the bank's threshold policy as a `DeosCell` (state holds the Poseidon2 `threshold_commitment`) with a `CellProgram`; the credit-check becomes a `CellAffordance` whose `effect_template` is a real `Effect`, gated by `AuthRequired` (via `is_attenuation`) rather than by Alice holding `(threshold, blinding)` as plaintext locals. Route proof submission through `AffordanceSurface::fire_through_executor` so the committed-threshold STARK becomes the witness for a verified TURN emitting a `TurnReceipt`. Publish the bank cell as a `dregg://` sturdyref (replacing the simulated "secure channel" = local variable passing). Use the membrane so the auditor rehydrates a per-viewer frustum-snapshot. KEEP the cryptographic core verbatim (`CommittedThresholdAir`, 37-col trace, `fact_commitment` binding, the four adversary checks) — it is the in-circuit witness for the fire. |
| **ai_agent_mcp_workflow** *(demo-agent example)* | pre-deos-toy | medium | **rebuild-on-deos** | Imports ONLY `dregg_sdk` + `dregg_token`, pokes kernel token primitives, hand-builds JSON-RPC strings; the "MCP" tools are NAMES only. The damning tell: security outcomes are `println` strings, not assertions — the selective-disclosure match treats even the `Err "(mock path used)"` arm as success; token IDs are decorative `blake3` literals. A REAL deos MCP/web-of-cells server already exists at `node/src/mcp.rs` (serves `dregg://about/ontology/cell/{id}/receipt/{hash}`, real `dregg_authorize`/`dregg_delegate`/`dregg_prove_predicate` backed by the executor, gated by the cap biscuit) — this example reuses those exact tool names while sharing ZERO code. Rebuild (~250-400 lines, all existing public API): model the three tools as `CellAffordance`s on a `DeosCell` "api-gateway", `.web_of_cells()` + `publish_all` for the `dregg://` sturdyref, drive each phase via `predict_fire`→`settle` so AUTHORIZED/DENIED become REAL receipts/refusals. The STORY (agent gets a cap via MCP, proves selectively, delegates narrower) is the marquee deos pitch — worth keeping, on the real stack. |
| **atomic_swap_demo** *(demo-agent example)* | pre-deos-toy | medium | **rebuild-on-deos** | Re-express as a factory-born escrow/swap cell on the deos stack, following the existing `escrow-market` pattern (which already IS trustless two-party atomic settlement — the same story this toy gestures at). Drop the toy primitives — replace `Note`/`NullifierSet`/`Action{Authorization::Unchecked, spending_proof: vec![0x01], note_tree_root:[0u8;32]}` with a factory-born cell whose `CellProgram` carries conservation as a real slot caveat (`SumEqualsAcross`/value-neutral split, `StrictMonotonic` lifecycle, `WriteOnce` party-binds). Authorize via `AppCipherclerk::make_action` (`Signature`, not `Unchecked`); route through `EmbeddedExecutor::submit_action` so the turn is ACTUALLY EXECUTED (the toy builds a turn and never runs it). Wrap as a `DeosApp` with cap-gated affordances per role (maker⊂taker⊂matcher), publish the swap-board cell, add snapshot/rehydrate, emit the manifest. A `tests/reexpress_deos_app.rs` asserts the conservation/lifecycle tooth still bites. The multi-party `CommitmentMode::Partial` fragment composition is the one genuinely interesting idea worth carrying forward — on real signatures + real execution. |
| **compute-exchange** | pre-deos-toy | large | **retire** | No source to integrate — deos integration = a from-scratch deos-native crate (the legacy source is gone, pruned in `8bec1d12b`). Full scope (~2000 LOC mirroring swarm-orchestration): add to workspace members + a Cargo.toml; write `src/lib.rs` with a `FactoryDescriptor` whose installed `CellProgram::Predicate` IS the marketplace policy (escrow conservation `released+refunded==escrowed` via `AffineLe` + slot caveats); write `tests/reexpress_deos_app.rs` (per-tier affordances on Signature⊂Either⊂None, projection, real fires, `.web_of_cells()`, rehydration, generated component + manifest); write `tests/factory_birth.rs`; update `manifest.json` from `status:unported`. The legacy `apps/compute-exchange` was itself a pre-deos toy (BROKEN, 8 P0s — escrows never sent to engine, signature parsed-and-discarded, hardcoded caller, decorative ZK), so nothing is salvageable. **Retire**: the live escrow-market + sealed-auction + swarm-orchestration already cover the escrow/auction/matching shapes; only rebuild if ember specifically wants a GPU/proof-as-a-service market demo. |
| **gallery** | pre-deos-toy | large | **rebuild-on-deos** | A manifest-only roadmap stub — `manifest.json` (563B) is its ONLY file. No Cargo.toml, no `src/`, no Rust. Not a workspace member. Self-declares `status:unported`, `legacy_path:apps/gallery` — but that path is GONE (the whole `apps/` tree was deleted in the migration; the back-reference dangles). It is BELOW even the "toy that pokes primitives" shape — a toy at least has source. The README states it verbatim: "roadmap stubs, not apps … deliberately not faked into half-working crates." Deos integration = a from-scratch BUILD: create the crate (Cargo.toml as a workspace member + `src/lib.rs` with `FactoryDescriptor`(s) + turn-builders, no `Unchecked`/`[0u8;64]`); wrap as a `DeosApp`/`DeosCell` mirroring supply-chain-provenance (real `dregg://` sturdyrefs + per-viewer rehydration with the no-peek refusal); the commit phase hides the bid behind a commitment; `pages/` surface importing `constants.generated.js`; passing `factory_birth.rs` + `reexpress_deos_app.rs`. CRITICAL: reconcile against sealed-auction — both are commit-reveal sealed-bid; decide whether gallery is a distinct surface or folds in. Do NOT keep as-is: a dangling-legacy-path stub misrepresents the inventory. |
| **dregg-demo-agent** *(binary)* | pre-deos-toy | medium | **retire** | A 478-line single `src/main.rs` end-to-end pipeline demo (`bin = dregg-agent-demo`) that pokes kernel primitives directly: hand-builds a `Ledger`, inserts 3 cells with raw `Permissions`/`AuthRequired::Proof`, mints+attenuates a `MacaroonToken`, generates a real `MerkleStarkAir` STARK proof of federation membership, feeds it via `ActionBuilder::with_proof` into `TurnExecutor::with_proof_verifier`, then re-runs with a flipped byte to show fail-closed rejection. The textbook old-bones shape; ZERO deos integration (grep across `src/` + 43 examples + Cargo.toml ⇒ nothing). **Retire**: its entire teaching value (a real STARK proof authorizes a real verified turn; tampering fails closed) is now demonstrated INSIDE the deos apps' executor fire path and their `reexpress_deos_app` tests on the genuine `is_attenuation` gate. It uses real primitives (not a parallel model) so it is not wrong — it teaches the OLD bones that `DEOS-APPS.md` explicitly contrasts against. Its one distinct nugget (STARK-proof-as-turn-authorization) is better folded into one deos app's affordance fire path. It IS a workspace member with 43 `[[example]]` targets, so retiring is an eviction (drop from members + delete the dir); as a `[[bin]]` with no dependents, removal is clean. *A per-example keep/retire pass is a separate, larger census; the grep confirms none of the 43 touch the deos stack.* |
| **agent_network** *(demo-agent example)* | pre-deos-toy | small | **retire** | A 1028-line `examples/*.rs` `main()` poking kernel primitives: `Cell::with_balance` + raw `Permissions{AuthRequired::None}` on every field, `SpawnWithDelegation`/`Introduce`/`PipelinedSend`, `TurnExecutor::new`, `BudgetGate`, `MacaroonToken::attenuate`, `verify_receipt_chain`. The 8-cell "AI agent network" is pure narration: cells are anonymous `[seed;32]` keypairs with ALL permissions `None` (nothing can be refused), and every domain concept is a `blake3` string. Textbook "screams I am a toy" shape. **Retire, don't rebuild** — the deos-native rebuild target already ships and is smaller + more capable: swarm-orchestration (563 LOC) covers this exact scenario with executor-refused caveats (not in-script asserts), plus agent-provenance + tool-access-delegation. The toy's root→dev→agent→tool attenuation+budget+receipts is a strict WEAKER subset. Delete the file + drop the `[[example]]` stanza; point readers at swarm-orchestration. (Effort "small" only in that the rebuild = an existing app; actually re-doing it on `DeosApp` would be small-to-medium AND fully redundant.) |

## Headline counts

**22 entries** censused: 15 starbridge-apps with code + 2 starbridge-app stubs (gallery,
compute-exchange) + the demo-agent binary + 4 demo-agent examples.

| Shape | Count | Members |
| --- | --- | --- |
| **deos-native (in shipped `src/`)** | **0** | *none* |
| **partially-integrated** | **7** | supply-chain-provenance, swarm-orchestration, subscription, agent-provenance, escrow-market, governed-namespace, identity |
| **pre-deos-toy** | **15** | bounty-board, compartment-workflow-mandate, nameservice, polis, privacy-voting, sealed-auction, storage-gateway-mandate, tool-access-delegation, compute-exchange, gallery, dregg-demo-agent, agent_network, ai_agent_mcp_workflow, anonymous_credit_check, atomic_swap_demo |
| **infra** | **0** | *(no entry is censused as plumbing)* |

Two finer cuts inside "partially-integrated":

- **Actually drive the deos stack** (a green `reexpress_deos_app.rs` exercising
  affordances/web-of-cells/rehydration): **2** — supply-chain-provenance and swarm-orchestration.
- **Subscription** has a green deos re-expression too, but it lives in
  `app-framework/tests/reexpress_subscription.rs` (the framework tree), not the app's own tests —
  locationally adrift, semantically at full parity.
- The other four (agent-provenance, escrow-market, governed-namespace, identity) have a green,
  correct floor at the same maturity tier as the leading cohort, with the re-expression test not
  yet written.

Disposition: **keep 5** (supply-chain-provenance, subscription, agent-provenance, polis,
anonymous_credit_check) · **rebuild-on-deos 14** · **retire 3** (compute-exchange, dregg-demo-agent,
agent_network). Effort: **small 9 · medium 10 · large 3**.

## Priority — what to integrate first

The leverage order is: **promote what is already proven** (the surface exists, just relocate it) →
**paint-by-numbers re-expressions** that grow no new framework (the recipe is mechanical, the floor
is green) → **the rebuilds whose deos version is genuinely more capable** (an on-ledger gate the
floor cannot express) → **the demos worth keeping**. Retirements run in parallel; they unblock
nothing but they stop the inventory from lying.

### Tier 1 — promote the proven surface (do these first; lowest risk, highest signal)

These three already have a green deos surface. The work is relocation + seam-closure, not
authoring — and each becomes a *crate-resident exemplar* the rebuilds copy.

1. **supply-chain-provenance** — *the reference port.* Already 9/9 green and deos-native in test;
   promote `item_app()` into `src/`, close the fire→full-`CellProgram` seam, swap the scaffold
   stand-ins for the real multi-effect handoff + `GrantCapability`. Once this ships from `src/`, it
   is the canonical "this is what deos-native looks like" the other 14 rebuilds clone.
2. **subscription** — *the most complete re-expression of all*, merely mislocated. Copy
   `reexpress_subscription.rs` into the crate and/or expose `subscription_deos_app()`. Near-zero
   risk; immediate parity.
3. **swarm-orchestration** — the second deos-native test; promote `board_app` into `src/`, close
   the factory-born-cell fire seam (so `AffineLe`/`WriteOnce`/`StrictMonotonic` bite in the deos
   path), give it real dispatch effects, fix `manifest.json`. This is the multi-agent exemplar.

### Tier 2 — additive paint-by-numbers (small effort, green floor, copy the Tier-1 exemplar)

Each adds one `tests/reexpress_deos_app.rs`, grows no framework, and touches a correct floor.
Order within the tier favors the apps whose *story* is most deos-shaped (cross-trust-boundary,
cross-agent, marketplace):

4. **agent-provenance** — the rehydrated cold snapshot IS the third-party-auditable artifact; the
   existing `verify_chain` has its natural deos home here.
5. **identity** — credential presentation across a trust boundary is *the* web-of-cells story (a
   verifier on another federation reacquires the issuer cell). Medium only for the `Custom` path.
6. **escrow-market** — the already-noted first dregg-userspace-verify customer; trustless
   two-party settlement; only a dev-dep delta. (Becomes the escrow exemplar atomic_swap_demo and
   compute-exchange both lean on.)
7. **bounty-board** — the canonical gated-lifecycle (4-state `pending_cond` approve button); makes
   gated affordances react to live state.
8. **tool-access-delegation** — the worker⊂grantor ocap ladder is native; ~25-line builder.
9. **privacy-voting** — shows the `DeosCell`+`GatedAffordance` path (the scaffold emit/edit path
   carries no `StateConstraint`s — the one subtlety, already demonstrated by the supply-chain
   sibling).

### Tier 3 — rebuilds where deos is genuinely more capable (medium; the on-ledger gate is the payoff)

These earn the "rebuild" label because the deos version enforces something the floor cannot:

10. **nameservice** — *the keystone.* `RESOLVE_TARGET_SLOT` stops storing opaque `blake3(uri)` and
    starts pointing at reacquirable `dregg://` sturdyrefs — a nameservice that names the
    web-of-cells finally lives IN it, and `DeosApp::announce` (every other app's discovery target)
    gets its keystone. High cross-app leverage; do this early in Tier 3.
11. **sealed-auction** — putting the commit phase ON-LEDGER (a `WriteOnce` commit-board cell) makes
    anti-front-running an executor refusal, not an in-process `BTreeMap`. The README's own
    follow-up; the verified core (`settle_ring_verified`, the 582-line Lean) is reused wholesale.
12. **storage-gateway-mandate** — the volume budget becomes a live gate; and *actually mount it at
    node startup* (the open `DEVNET-COMPOSITION.md` TODO) so it stops being test-only.
13. **governed-namespace** — needs the `WitnessedPredicateRegistry`-into-executor lane (a shared
    in-flight dependency); the council-board example is the near-twin.
14. **compartment-workflow-mandate** — carries two genuinely-new legs (clearance-graph-root
    verifier + Stingray spend-policy debit) beyond the wrapping.

### Tier 4 — keep-and-wrap the pure cores; rebuild the keepable demos

15. **polis** — KEEP the proven program library; add the deos wrapper additively behind a `deos`
    feature / a `starbridge-polis-deos` crate (5 families × affordances). Larger surface, but the
    hard semantic core is done; the deos layer already knows polis-shaped governance.
16. **anonymous_credit_check** — KEEP the cryptographic core (`CommittedThresholdAir`) verbatim;
    rebuild the shell on a `DeosCell` so the committed-threshold STARK becomes a verified turn's
    witness. Large because the crate lacks every deos dep today.
17. **atomic_swap_demo** — rebuild on the escrow-market pattern (real signatures + real execution);
    carry the `CommitmentMode::Partial` fragment idea forward.
18. **ai_agent_mcp_workflow** — rebuild so AUTHORIZED/DENIED become real receipts, not `println`;
    the marquee MCP-cap-token story deserves the real stack (the real server already exists at
    `node/src/mcp.rs`).

### Retire (run in parallel; do not block any of the above)

- **compute-exchange** — no salvageable source; escrow-market + sealed-auction + swarm-orchestration
  already cover its shapes. Delete the dangling stub. *(Rebuild only on an explicit
  GPU/proof-market product call.)*
- **dregg-demo-agent** *(binary)* — old-bones pipeline; its STARK-as-authorization nugget folds into
  a deos app's fire path. Eviction (drop from workspace members + delete; clean, no dependents).
- **agent_network** *(example)* — pure narration with all-`None` permissions; swarm-orchestration
  is the strictly-stronger deos-native replacement. Delete the file + its `[[example]]` stanza.

**gallery** is a rebuild, not a retire — *but* it must first be reconciled against sealed-auction
(both are commit-reveal sealed-bid). If no distinct product need survives that reconciliation, fold
its surface into sealed-auction and retire the stub; otherwise build it from the
nameservice/supply-chain-provenance paint-by-numbers template. Until then it is a dangling-legacy
manifest that misrepresents the inventory.

## The honest verdict — do our apps integrate deos / web-of-cells?

**Not yet at the surface — but the gap is a skin, not a foundation, and it is thin.**

No app ships a deos-native `src/`. Zero of 22 mount a `DeosApp` as their production surface; the
canonical surface everywhere is still the old bones (`register(ctx)` → `FactoryDescriptor` +
`InspectorDescriptor` + hand-copied generated JS), and `dregg://` appears in most apps only as an
inert `uri_prefix` inspector string — the addressing convention, not web-of-cells cell publication.
Read purely on shipped surfaces, **the answer is no**: the apps do not yet integrate deos /
web-of-cells in production.

The redeeming truths, all load-bearing:

1. **The floors are real.** Most pre-deos rows are NOT throwaway toys — they birth through the real
   factory path, route every op through the verified executor with real Ed25519 (no
   `Authorization::Unchecked`, no `[0u8;64]`, no cheat effects), and carry executor-enforced slot
   caveats with adversarial teeth, several with companion Lean differentials. The verification layer
   — the part that is hard and the part that matters — is already correct and is exactly the right
   backing state for `DeosCell`s. Integration is **additive** for the green-floor cohort: a wrapper,
   not a rewrite.

2. **The deos stack is real and proven.** `DeosApp`/`DeosCell`/`CellAffordance`/`GatedAffordance`/
   `AffordanceSurface`/`CapTpServer`/rehydration all exist in `app-framework`, are re-exported for
   every app that already depends on the framework, and are exercised green end-to-end (per-viewer
   projection, anti-ghost 403 fires, `dregg://` publish, lattice-respecting rehydration) by THREE
   re-expression tests today — supply-chain-provenance, swarm-orchestration, and the framework's own
   subscription test. The composition surface is not a sketch; it ships, it just ships in `tests/`.

3. **The pattern is paint-by-numbers.** The same move repeats across nearly every "what it would
   take": add one `tests/reexpress_deos_app.rs` modeled on an existing sibling; wrap the existing
   turn-builders' `Effect`s as `CellAffordance`s on the natural Signature⊂Either⊂None rights ladder;
   `.gated(...)` over the caveats the crate already constructs (they map 1:1); `.publish(...)` +
   `.discoverable(...)`. The framework grows nothing; the floor stays untouched.

So the accurate one-liner: **our verified cores are deos-shaped and our deos layer is real and
green — but the two are joined only in side-proofs, not in any shipped app.** The leading cohort
(supply-chain-provenance, swarm-orchestration, subscription) is one *promotion* away from
deos-native; the green-floor cohort is one *additive re-expression test* away; the genuine rebuilds
(nameservice, sealed-auction, storage-gateway-mandate) are where deos earns its keep by enforcing an
on-ledger gate the floor cannot express; and three demos that teach the old bones should retire into
the deos apps that already teach the same lessons through the verified fire path. The honest claim
to make in public copy is therefore the precise one: *deos integration is demonstrated and green,
and is being promoted from proof into product* — never *the apps are deos-native* (none yet is),
until at least one `src/` mounts a `DeosApp`.

## Where this lives

- **The deos composition stack:** `app-framework/src/deos_app.rs`, `affordance.rs`
  (`GatedAffordance` at line 536), `scaffold.rs`, `captp_server.rs`, `rehydration.rs`; re-exported
  from `app-framework/src/lib.rs`.
- **The two deos-native re-expression tests (the templates every rebuild copies):**
  `starbridge-apps/supply-chain-provenance/tests/reexpress_deos_app.rs` and
  `starbridge-apps/swarm-orchestration/tests/reexpress_deos_app.rs`.
- **The most-complete re-expression (mislocated):** `app-framework/tests/reexpress_subscription.rs`.
- **The deos-native exemplar apps the framework ships:**
  `app-framework/examples/deos_council_board.rs` (governance — the governed-namespace / polis twin)
  and `examples/deos_app_in_an_afternoon.rs` (the `predict_fire`→`settle` + `publish_all` walk).
- **The real deos MCP / web-of-cells server** (the `ai_agent_mcp_workflow` rebuild target):
  `node/src/mcp.rs`.
- **The app roster:** `starbridge-apps/*` (18 dirs incl. the `shared`/`polis` libraries and the two
  stubs gallery + compute-exchange); the demo binary + examples at `demo-agent/`.
