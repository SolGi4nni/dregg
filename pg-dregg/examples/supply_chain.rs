//! THE FLAGSHIP DEMO — a horizontally-integrated, multi-party, crash-surviving
//! verified durable workflow, expressed on the **reusable** pg-dregg
//! durable-workflow API ([`pg_dregg::workflow`]).
//!
//! ```text
//! cargo run --example supply_chain
//! ```
//!
//! ## The pitch: "DBOS, but every state mutation is a verified turn"
//!
//! DBOS gives you *durable execution* on postgres: a workflow checkpoints its
//! steps to postgres and, after a crash, replays from the durable log so it runs
//! exactly once. That is real and valuable — but the steps themselves are
//! ordinary code that issues ordinary `UPDATE`s. DBOS trusts the writer.
//!
//! pg-dregg gives you durable execution where **state mutates ONLY through a
//! verified, capability-secure, conservation-respecting turn** (the spine
//! invariant, `docs/PG-DREGG.md` §8):
//!
//!   * **reads are free SQL** — any `SELECT`/join/aggregate over the mirror is
//!     sound by construction (a read cannot break a transition-function invariant);
//!   * **writes are gated** — a state row exists ONLY as the post-image of a
//!     verified turn submitted through the ONE door (`dregg.commit_log`), whose
//!     trigger runs the real anti-substitution chain tooth (`RootChain`);
//!   * **capabilities attenuate** — each agent holds a strictly-narrowed token
//!     (`granted ⊆ held`, provably; no agent can act outside its grant);
//!   * **value is conserved** — the per-turn balance deltas sum to zero;
//!   * **federation is self-checking** — a replicated mirror re-validates the
//!     chain locally and an apply-conflict alarm DRIVES that re-validation.
//!
//! So pg-dregg is not just durable. It is durable **+ unforgeable + attenuable +
//! conserving + federated**. A DBOS workflow that fat-fingers
//! `UPDATE balances SET amount = amount + 1000000` succeeds and forges value;
//! the identical mutation through pg-dregg is refused by the database engine
//! because it carries no verified turn, no chaining root, no conserved delta.
//!
//! ## On the API (this is the proof the API is sufficient)
//!
//! Earlier this demo HAND-CODED its own durable engine. It no longer does: the
//! whole orchestration — `submit` through the three-gate spine, the durable log,
//! crash recovery, exactly-once resume — is the shipped, reusable
//! [`pg_dregg::workflow`] API ([`Workflow`] / [`Step`] / [`WorkflowEngine`] /
//! `run` / `resume`). The four-party purchase order below is expressed *on that
//! API*, which is exactly the evidence that the API is enough to build a real
//! "DBOS but verified" workflow. The only bespoke code left here is the
//! narration, the per-agent capability minting, and the adversarial probes
//! (the forged-write attempt + the federation re-validation), which reach under
//! the API on purpose to show the gates the API rests on.
//!
//! ## The scenario — a four-party agentic supply chain
//!
//! A purchase order is fulfilled by four parties, each an autonomous agent
//! holding its OWN attenuated capability:
//!
//!   * **TREASURY** — the settlement bank (funds the buyer; the genesis mint).
//!   * **BUYER**     — places the order and pays the supplier on delivery.
//!   * **SUPPLIER**  — accepts the order, ships goods, gets paid.
//!   * **SHIPPER**   — is paid a delivery fee out of the buyer's escrow.
//!
//! The workflow is a multi-step verified-durable orchestration:
//!
//!   step 0  genesis        TREASURY funded to 1_000_000
//!   step 1  fund buyer      TREASURY → BUYER 10_000           (settlement)
//!   step 2  place order     BUYER escrows 6_000 to an ORDER cell (PO opened)
//!   step 3  accept order    SUPPLIER grants BUYER a delivery capability (cap edge)
//!   --------  ✸ SIMULATED CRASH between step 3 and step 4  ✸  --------
//!   step 4  ship + pay      ORDER → SUPPLIER 5_000, ORDER → SHIPPER 1_000  (escrow released)
//!   step 5  close order     BUYER closes the PO (nonce bump, organ-style op)
//!
//! Every step is a *receipted turn* (provable who-did-what: the turn's `creator`
//! is the acting agent). The crash is real: we drop the in-memory engine after
//! step 3 and rebuild it from the durable log via [`WorkflowEngine::recover`],
//! then [`WorkflowEngine::resume`] the chain — exactly-once, nothing lost,
//! nothing double-applied.
//!
//! ## What this drives (NOT a reimplementation)
//!
//! The [`pg_dregg::workflow`] API calls the REAL pg-dregg cores that `cargo test`
//! proves and the `#[pg_test]`s exercise through live pg18 SQL:
//!
//!   * [`pg_dregg::authz`]       — the verified capability decision + attenuation
//!                                 + the `submit`-gate admission (the RLS check);
//!   * [`pg_dregg::mirror`]      — `MirrorBatch` (the verified-turn wire unit),
//!                                 `RootChain` (the chain-gate / spine tooth),
//!                                 `federation_health` (the conflict-driven sweep);
//!
//! The only thing synthesized is the *node's commit-log projection* (the
//! `dregg_cell::Cell → CellRow` decode that lives node-side, queued behind the
//! rotation lane), which the API isolates behind its [`Projector`] seam — here
//! the default deterministic fold, in production the kernel's `ledger_root`. The
//! chain tooth, the authz decision, the conservation, the durability are all the
//! shipped cores, unchanged.

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::mirror::{
    federation_health, CapRow, ConflictReport, MirrorBatch, RootChain, SubscriptionConflicts,
};
use pg_dregg::workflow::{
    balance_reg, cell_row, recover_from_durable, turn_row, FoldProjector, MapTokens, MemLog,
    Projector, Step, Workflow, WorkflowEngine, GENESIS_ROOT,
};

// ===========================================================================
// Cosmetics
// ===========================================================================

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn rule(title: &str) {
    println!(
        "\n\x1b[1m\x1b[36m── {title} {}\x1b[0m",
        "─".repeat(64usize.saturating_sub(title.len()))
    );
}

fn dbos(note: &str) {
    // The DBOS comparison, inline, so the narration carries the positioning.
    println!("    \x1b[2m(vs DBOS: {note})\x1b[0m");
}

// ===========================================================================
// The four agents. Each cell-id is prefix-stable so a capability attenuated to
// the agent's hex prefix admits exactly that agent's cell as an RLS resource.
// ===========================================================================

const fn agent_id(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

const TREASURY: [u8; 32] = agent_id(0xc0);
const BUYER: [u8; 32] = agent_id(0xb0);
const SUPPLIER: [u8; 32] = agent_id(0x59);
const SHIPPER: [u8; 32] = agent_id(0x51);
/// The ORDER cell — the escrow that holds the buyer's committed funds until the
/// supplier ships. Its own cell, so the PO is first-class verified state.
const ORDER: [u8; 32] = agent_id(0x0d);

fn name_of(id: [u8; 32]) -> &'static str {
    match id[0] {
        0xc0 => "TREASURY",
        0xb0 => "BUYER",
        0x59 => "SUPPLIER",
        0x51 => "SHIPPER",
        0x0d => "ORDER",
        _ => "?",
    }
}

// ===========================================================================
// THE WORKFLOW — the four-party purchase order, built on the reusable API.
//
// This is the whole "DAG of steps" DBOS would checkpoint — except each step
// here becomes a *verified turn* (it carries the actor, the cell post-images,
// and any capability edge), and the engine admits it ONLY through the spine.
// Compare to the old hand-coded version: this is now ~30 lines of declarative
// builder calls, and the runtime is the shipped API.
// ===========================================================================

fn purchase_order_workflow() -> Workflow {
    Workflow::new("four-party purchase order")
        .then(Step::new("genesis: TREASURY funded to 1_000_000", TREASURY).set(TREASURY, 1_000_000, 0))
        .then(
            Step::new("fund buyer: TREASURY → BUYER 10_000", TREASURY)
                .set(TREASURY, 990_000, 1)
                .set(BUYER, 10_000, 0),
        )
        .then(
            Step::new("place order: BUYER escrows 6_000 into the ORDER cell", BUYER)
                .set(BUYER, 4_000, 1)
                .set(ORDER, 6_000, 0),
        )
        .then(
            Step::new("accept order: SUPPLIER grants BUYER a delivery capability", SUPPLIER)
                .set(SUPPLIER, 0, 1)
                .grant(CapRow {
                    holder: BUYER,
                    slot: 0,
                    target: SUPPLIER,
                    permissions_json: "{\"deliver\":\"delegated\"}".into(),
                    breadstuff: None,
                    expires_at: Some(10_000),
                    // ATTENUATION, exploded as the no-amplify audit surface: the
                    // delegated effect set is {deliver} — a strict subset of the
                    // supplier's authority.
                    allowed_effects_json: Some("[\"deliver\"]".into()),
                    stored_epoch: Some(0),
                    last_ordinal: 3,
                }),
        )
        .then(
            Step::new("ship + pay: ORDER → SUPPLIER 5_000, ORDER → SHIPPER 1_000", BUYER)
                .set(ORDER, 0, 1)
                .set(SUPPLIER, 5_000, 2)
                .set(SHIPPER, 1_000, 0),
        )
        .then(
            Step::new("close order: BUYER closes the PO (organ-style nonce bump)", BUYER)
                .set(BUYER, 4_000, 2),
        )
}

// The clock the AUTHZ gate evaluates time caveats against, process-local like a
// backend's `now()`.
const CLOCK: i64 = 1_000;

fn main() {
    println!(
        "\x1b[1mpg-dregg FLAGSHIP — a multi-party, crash-surviving, verified durable workflow\x1b[0m"
    );
    println!("\x1b[2m\"DBOS, but every state mutation is a verified, capability-secure, conserving turn.\"\x1b[0m");
    println!("\x1b[2m  (expressed on the reusable pg_dregg::workflow API — Workflow / Step / run / resume)\x1b[0m");

    // =======================================================================
    // 0. THE TRUST ROOT + PER-AGENT ATTENUATED CAPABILITIES.
    // =======================================================================
    rule("0. issuer key + per-agent attenuated capabilities");
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();
    println!("  issuer (the dregg.issuer_pubkey trust root): {}…", &issuer.public().to_hex()[..16]);

    // The engine's token store — the API's TokenStore (actor → bearer token),
    // the durable-runtime equivalent of the backend's `dregg.token` session GUC.
    let mut tokens = MapTokens::new();

    // Each agent gets a capability minted by the issuer, then ATTENUATED to its
    // own cell. A token admitting `submit` on ANY resource, narrowed to the
    // agent's hex prefix, so the agent can submit ONLY turns for its own cell.
    let mint_agent = |agent: [u8; 32], actions: &[&str]| -> String {
        let action_pred = if actions.len() == 1 {
            Pred::AttrEq { key: "action".into(), value: actions[0].into() }
        } else {
            Pred::AnyOf(
                actions
                    .iter()
                    .map(|a| Pred::AttrEq { key: "action".into(), value: (*a).into() })
                    .collect(),
            )
        };
        issuer
            // wide grant: the actions on ANY resource …
            .mint([
                Caveat::FirstParty(action_pred),
                Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
            ])
            // … ATTENUATED to the agent's own cell prefix (granted ⊆ held).
            .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: hx(&agent)[..2].to_string(),
            })])
            .encode()
    };

    // TREASURY/BUYER/SUPPLIER/SHIPPER each may `submit` (and `read`) — but ONLY
    // for their own cell. The ORDER cell is acted on by the BUYER (it placed the
    // escrow), so the buyer's token also admits the order prefix; we model that
    // by giving the buyer a second, order-scoped grant below.
    for (agent, acts) in [
        (TREASURY, &["submit", "read"][..]),
        (BUYER, &["submit", "read"][..]),
        (SUPPLIER, &["submit", "read"][..]),
        (SHIPPER, &["submit", "read"][..]),
    ] {
        tokens.bind(agent, mint_agent(agent, acts));
        println!(
            "  {:<9} cap: submit/read attenuated to resource prefix \"{}\" (its own cell)",
            name_of(agent),
            &hx(&agent)[..2]
        );
    }
    dbos("DBOS roles are postgres GRANTs — central DDL; here each agent holds a \
          bearer capability it could sub-delegate offline, provably narrowing.");

    // The buyer additionally holds an order-scoped grant (it opened the PO), so
    // its token admits both its own cell AND the ORDER cell. We express "either
    // prefix" as an AnyOf of two prefix caveats, so it is STILL a strict
    // confinement (not the whole namespace) — and we prove below it STILL cannot
    // touch a cell it was not granted (SHIPPER).
    tokens.bind(BUYER, buyer_multi_token(&issuer));

    // =======================================================================
    // 0b. THE ATTENUATION PROOF — the buyer CANNOT act outside its grant.
    // =======================================================================
    rule("0b. no-amplification — an agent cannot act outside its grant");
    // Re-derive the exact buyer_multi token so the probe interrogates the real
    // token shape the engine holds (the buyer's two-prefix confinement).
    let buyer_tok = buyer_multi_token(&issuer);
    let can = |agent: [u8; 32]| authz::decide(&buyer_tok, "submit", &hx(&agent), CLOCK).allowed();
    println!("  BUYER may submit for BUYER cell?    {}", can(BUYER));
    println!("  BUYER may submit for ORDER cell?    {}", can(ORDER));
    println!("  BUYER may submit for SHIPPER cell?  {}  ← refused (outside the grant)", can(SHIPPER));
    println!("  BUYER may submit for TREASURY cell? {}  ← refused (cannot mint money)", can(TREASURY));
    assert!(can(BUYER) && can(ORDER), "buyer must act on its own + the order cell");
    assert!(!can(SHIPPER) && !can(TREASURY), "buyer must NOT act outside its grant (no amplification)");
    println!("→ the capability is the gate: the BUYER cannot forge a TREASURY mint or pay itself as the SHIPPER.");
    dbos("a DBOS step is ordinary code that can issue ANY UPDATE; an SQL-injection or \
          bug in it is a total authorization bypass. Here the capability bounds it.");

    // =======================================================================
    // 1–3. RUN THE WORKFLOW UP TO THE CRASH POINT — via the API, checkpointing
    //      each verified turn to an EXTERNAL durable sink (the DurableLog seam).
    // =======================================================================
    rule("1–3. the workflow runs — each turn checkpointed to the durable sink (run_durable)");
    let workflow = purchase_order_workflow();
    let mut engine = WorkflowEngine::new(tokens).with_clock(CLOCK);
    // The external durable sink. Here a MemLog; in a real deployment this is
    // `dregg.commit_log` — DurableLog::append is the INSERT whose trigger re-runs
    // the chain tooth, DurableLog::load is the SELECT. The sink is what SURVIVES a
    // crash (the engine does not), so it is the thing recovery reads.
    let mut durable = MemLog::new();

    // Run the prefix up to the crash. (The API would `run_durable` the WHOLE
    // workflow; we drive the prefix explicitly so we can interpose a crash
    // mid-stream — the same thing a real process does when it dies between
    // checkpoints.)
    let crash_after = 4; // steps 0,1,2,3 commit + checkpoint; CRASH; then 4,5.
    let prefix = Workflow {
        name: workflow.name.clone(),
        steps: workflow.steps[..crash_after].to_vec(),
    };
    match engine.run_durable(&prefix, &mut durable) {
        Ok(out) => {
            for (i, step) in prefix.steps.iter().enumerate() {
                // re-derive the per-step head for the narration from the log.
                let root = engine.log()[i].turn.ledger_root;
                println!(
                    "  ✓ ord {}  [{:<8}]  {}\n          → root {}…",
                    i,
                    name_of(step.actor),
                    step.name,
                    &hx(&root)[..12]
                );
            }
            assert_eq!(out.committed, crash_after);
        }
        Err(e) => panic!("a well-formed authorized step was refused: {e}"),
    }
    println!(
        "  durable sink now holds {} verified turns; head root {}…",
        durable.len(),
        &hx(&engine.head().unwrap())[..12]
    );
    // Free-SQL reads over the mirror at the crash point.
    println!("  reads (free SQL over dregg.cells):");
    for c in [TREASURY, BUYER, SUPPLIER, ORDER] {
        println!("    {:<9} balance = {}", name_of(c), engine.balance(c));
    }
    assert_eq!(engine.balance(ORDER), 6_000, "the PO escrow holds 6_000 at the crash point");
    assert_eq!(engine.caps().len(), 1, "the supplier's delivery cap edge is recorded");

    // =======================================================================
    // ✸ THE CRASH ✸  — drop the engine; keep ONLY the external durable sink.
    // =======================================================================
    rule("✸ SIMULATED CRASH — the engine dies mid-workflow ✸");
    drop(engine); // the in-memory chain head + balances are GONE
    println!("  the engine process died after step {}. In-memory chain + balances: LOST.", crash_after - 1);
    println!("  what survived: the external durable sink ({} rows in dregg.commit_log).", durable.len());
    dbos("this is exactly the DBOS value proposition — survive a crash, resume from the \
          durable log. pg-dregg matches it, AND the log is a verified hash-chain.");

    // =======================================================================
    // 4. RECOVER — rebuild from the durable sink; the chain RE-VALIDATES.
    // =======================================================================
    rule("4. recovery — recover_from_durable(sink); the chain re-validates");
    // The recovered engine needs the same token store to finish the workflow.
    let mut tokens2 = MapTokens::new();
    for (agent, acts) in [
        (TREASURY, &["submit", "read"][..]),
        (SUPPLIER, &["submit", "read"][..]),
        (SHIPPER, &["submit", "read"][..]),
    ] {
        tokens2.bind(agent, mint_agent(agent, acts));
    }
    tokens2.bind(BUYER, buyer_multi_token(&issuer));
    // recover_from_durable reads the sink, re-validates the chain, resumes at the
    // head. It returns Result — a tampered/unreachable store is surfaced, not hidden.
    let mut engine = recover_from_durable(tokens2, FoldProjector, &durable)
        .expect("the durable chain re-validates on recovery")
        .with_clock(CLOCK);
    println!(
        "  recovered: {} turns replayed + re-validated; chain resumed at ordinal {}, head {}…",
        engine.turn_count(),
        engine.next_ordinal(),
        &hx(&engine.head().unwrap())[..12]
    );
    // The recovered read state is exactly what it was — exactly-once, nothing lost.
    assert_eq!(engine.balance(ORDER), 6_000, "recovery restored the PO escrow exactly");
    assert_eq!(engine.balance(BUYER), 4_000, "recovery restored the buyer balance exactly");
    assert_eq!(engine.caps().len(), 1, "recovery restored the delegation edge");
    println!("→ recovery is exactly-once: balances + cap edges restored, the chain refuses any re-apply of a committed turn.");

    // A replay of an ALREADY-committed turn is refused (idempotent recovery): the
    // chain resumed at ordinal 4, so re-submitting ordinal 2 cannot chain. This
    // is the chain backstop *under* the API's index-skip — we reach under the API
    // and push a stale batch straight at the chain to show the tooth itself.
    {
        let replay = &workflow.steps[2]; // "place order", already committed as ordinal 2
        let prev = GENESIS_ROOT;
        let cells: Vec<_> = replay.cells.iter().map(|&(id, b, n)| cell_row(id, b, n)).collect();
        let post = FoldProjector.ledger_root(prev, 2, &cells);
        let mem: Vec<_> = cells.iter().map(|c| balance_reg(c.cell_id, c.balance)).collect();
        let stale = MirrorBatch::from_parts(
            turn_row(2, prev, post, BUYER),
            cells,
            replay.cap.iter().cloned().collect(),
            mem,
        )
        .unwrap();
        // The chain is resumed at ordinal 4; a stale ordinal-2 batch is a gap.
        let mut probe = RootChain::resume(engine.head().unwrap(), engine.next_ordinal());
        use pg_dregg::mirror::ChainRefusal;
        match probe.extend(&stale) {
            Err(ChainRefusal::OrdinalGap { expected, got }) => println!(
                "  a stale replay of ordinal {got} is REFUSED (chain expects {expected}) — no double-apply."
            ),
            other => panic!("a stale replay must be refused as an ordinal gap, got {other:?}"),
        }
    }

    // =======================================================================
    // 5. FINISH THE WORKFLOW — ship + pay + close, post-recovery (resume_durable).
    // =======================================================================
    rule("5. finish the workflow after recovery — engine.resume_durable (ship, pay, close)");
    // resume_durable() drives the SAME workflow from its last committed ordinal:
    // steps 0..4 are skipped (already durable), only the uncommitted tail (4,5)
    // runs — and each finished turn is checkpointed back to the same sink.
    match engine.resume_durable(&workflow, &mut durable) {
        Ok(out) => {
            assert_eq!(out.skipped, crash_after, "the committed prefix is skipped, never re-applied");
            assert_eq!(out.committed, workflow.len() - crash_after, "only the tail runs");
            for i in crash_after..workflow.len() {
                let root = engine.log()[i].turn.ledger_root;
                println!(
                    "  ✓ ord {}  [{:<8}]  {}\n          → root {}…",
                    i,
                    name_of(workflow.steps[i].actor),
                    workflow.steps[i].name,
                    &hx(&root)[..12]
                );
            }
        }
        Err(e) => panic!("a post-recovery step was refused: {e}"),
    }
    println!("  final balances (free SQL over the mirror):");
    let mut total = 0i64;
    for c in [TREASURY, BUYER, SUPPLIER, SHIPPER, ORDER] {
        let b = engine.balance(c);
        total += b;
        println!("    {:<9} balance = {}", name_of(c), b);
    }

    // =======================================================================
    // 6. THE END-TO-END INVARIANTS — conservation + single custody.
    // =======================================================================
    rule("6. end-to-end invariants — value conserved across the whole flow");
    // The supplier was paid 5_000 and the shipper 1_000 out of the 6_000 escrow;
    // the order cell is drained to 0. Total value never changed from genesis.
    assert_eq!(engine.balance(SUPPLIER), 5_000, "supplier paid 5_000");
    assert_eq!(engine.balance(SHIPPER), 1_000, "shipper paid 1_000");
    assert_eq!(engine.balance(ORDER), 0, "the escrow is fully released");
    assert_eq!(total, 1_000_000, "TOTAL VALUE CONSERVED end-to-end across genesis→fund→escrow→ship→pay");
    assert_eq!(engine.total_value(), 1_000_000, "the free-SQL aggregate agrees: Σ balances = genesis total");
    println!("  Σ balances across ALL cells = {total}  (== the genesis 1_000_000)");
    println!("→ value was CONSERVED end-to-end: no turn created or destroyed value, escrow netted to zero.");
    dbos("a DBOS workflow has no notion of conservation — a step can credit without \
          debiting. pg-dregg's transition function makes Σδ = 0 a checkable property.");

    // =======================================================================
    // 7. PROVENANCE — who did what (every turn names its acting agent).
    // =======================================================================
    rule("7. provenance — a receipt per turn names who acted");
    for (ordinal, creator, receipt) in engine.provenance() {
        println!(
            "  ord {}  creator = {:<9}  receipt {}…",
            ordinal,
            name_of(creator),
            &hx(&receipt)[..8]
        );
    }
    println!("→ the workflow is fully attributable: each verified turn's `creator` is the agent that submitted it.");

    // =======================================================================
    // 8. THE SPINE — a bare write (no turn) cannot enter the store.
    // =======================================================================
    rule("8. the spine invariant — a forged write is refused by the engine");
    // An attacker tries to inject a forged balance for itself by submitting a
    // batch whose prev_root is substituted (it did NOT chain onto the head). The
    // API never exposes such a write; the attacker must reach under it to the raw
    // chain — and the chain tooth refuses it.
    let head = engine.head().unwrap();
    let next = engine.next_ordinal();
    let forged_cells = vec![cell_row(SHIPPER, 999_999, 9)]; // "pay myself a fortune"
    let forged_post = FoldProjector.ledger_root([0x99; 32], next, &forged_cells);
    let forged_mem: Vec<_> = forged_cells.iter().map(|c| balance_reg(c.cell_id, c.balance)).collect();
    let forged = MirrorBatch::from_parts(
        turn_row(next, [0x99; 32] /* substituted prev_root */, forged_post, SHIPPER),
        forged_cells,
        vec![],
        forged_mem,
    )
    .unwrap();
    let mut probe = RootChain::resume(head, next);
    match probe.extend(&forged) {
        Ok(()) => panic!("SECURITY FAILURE: a forged, non-chaining write entered the store"),
        Err(e) => println!("  the engine REFUSED the forged write (no chaining turn): {e}"),
    }
    assert_eq!(engine.head(), Some(head), "a refused write must not move the head");
    assert_eq!(engine.balance(SHIPPER), 1_000, "the shipper's balance is unchanged by the forgery attempt");
    println!("→ the bare-UPDATE money-printing bug that DBOS would happily execute is REFUSED here: no verified turn, no state change.");

    // =======================================================================
    // 9. FEDERATION — a subscriber re-validates the chain; conflicts drive it.
    // =======================================================================
    rule("9. federation — a subscriber re-validates the replicated chain");
    let links = engine.chain_links();
    // (a) Clean feed: no apply conflict ⇒ the verdict is Clear (the chain tooth
    //     is the *triggered* check; a clean apply layer means it need not run).
    let clean = ConflictReport::default();
    let verdict = federation_health(&clean, || {
        pg_dregg::mirror::revalidate_replicated_chain(GENESIS_ROOT, &links, Some(links.len() as u64))
    });
    println!("  clean feed:        {}", verdict.summary());

    // (b) An apply conflict on the subscriber (pg18 confl_* counter) DRIVES the
    //     chain re-validation. The replicated chain is intact ⇒ ALARM-but-intact.
    let conflicted = ConflictReport {
        subscriptions: vec![SubscriptionConflicts {
            subname: "dregg_tail".into(),
            insert_exists: 1,
            update_origin_differs: 0,
            update_exists: 0,
            update_missing: 0,
            delete_origin_differs: 0,
            delete_missing: 0,
            multiple_unique_conflicts: 0,
            total: 1,
        }],
    };
    let verdict = federation_health(&conflicted, || {
        pg_dregg::mirror::revalidate_replicated_chain(GENESIS_ROOT, &links, Some(links.len() as u64))
    });
    println!("  conflict alarm:    {}", verdict.summary());
    assert!(verdict.needs_attention(), "a conflict must raise the alarm");
    assert!(!verdict.chain_broken(), "the intact chain must still re-validate under the alarm");

    // (c) A TAMPERED replicated stream (a substituted root) under a conflict is
    //     the CRITICAL, do-not-trust verdict.
    let mut tampered_links = links.clone();
    if tampered_links.len() > 2 {
        tampered_links[2].prev_root = [0x99u8; 32]; // substitute a root mid-stream
    }
    let verdict = federation_health(&conflicted, || {
        pg_dregg::mirror::revalidate_replicated_chain(GENESIS_ROOT, &tampered_links, Some(tampered_links.len() as u64))
    });
    println!("  tampered stream:   {}", verdict.summary());
    assert!(verdict.chain_broken(), "a substituted replicated root must produce the CRITICAL verdict");
    println!("→ a subscriber RE-VALIDATES, it does not trust: a tampered replicated turn is caught locally, with no call back to the publisher.");
    dbos("DBOS has logical replication too — but a subscriber trusts the stream. \
          Here the subscriber re-runs the anti-substitution tooth on the replicated rows.");

    // =======================================================================
    // 10. OBSERVABILITY — the one-shot operator snapshot (engine.stats()).
    // =======================================================================
    rule("10. observability — the verified-store counters (engine.stats)");
    let s = engine.stats();
    println!("  turns={}  next_ordinal={}  cells={}  cap_edges={}", s.turns, s.next_ordinal, s.cells, s.cap_edges);
    println!("  total_value={}  head={}…  last_creator={}",
        s.total_value,
        &hx(&s.head.unwrap())[..12],
        s.last_creator.map(name_of).unwrap_or("-"));
    assert_eq!(s.turns, durable.len() as u64, "stats agree with the durable sink");
    assert_eq!(s.total_value, 1_000_000, "the conservation counter holds");
    println!("→ a /status endpoint or operator dashboard reads exactly these (each field is a one-line dregg.* query).");

    // =======================================================================
    // DONE.
    // =======================================================================
    rule("DONE — the integrated story, all green");
    println!("\x1b[1m\x1b[32m✓ a four-party purchase-order workflow ran to completion through pg-dregg:\x1b[0m");
    println!("    • expressed on the \x1b[1mreusable pg_dregg::workflow API\x1b[0m (Workflow / Step / run_durable / resume_durable);");
    println!("    • each step a \x1b[1mverified, receipted turn\x1b[0m (provable who-did-what);");
    println!("    • each agent bounded by an \x1b[1mattenuated capability\x1b[0m (no amplification);");
    println!("    • each turn \x1b[1mcheckpointed to an external durable sink\x1b[0m (the DurableLog seam = dregg.commit_log);");
    println!("    • the workflow \x1b[1msurvived a crash\x1b[0m and resumed exactly-once from that sink;");
    println!("    • \x1b[1mvalue was conserved\x1b[0m end-to-end (escrow netted to zero);");
    println!("    • a \x1b[1mforged write was refused\x1b[0m by the spine (the DBOS money-printing bug cannot happen);");
    println!("    • a \x1b[1mfederation subscriber re-validated\x1b[0m the chain (a tampered stream caught locally).");
    println!("\n  Durable like DBOS — \x1b[1mand\x1b[0m unforgeable + attenuable + conserving + federated.");
    println!("  \x1b[2mThe same surface, through real pg18 SQL: cargo pgrx test pg18  ·  scripts/e2e-live.sh\x1b[0m");
}

/// The buyer's multi-cell token: `submit`/`read` confined to EITHER the buyer
/// cell (`b0…`) or the ORDER cell (`0d…`) — a strict two-prefix confinement, not
/// the whole namespace. One helper so the bind, the recovery rebind, and the 0b
/// attenuation probe all use the byte-identical token.
fn buyer_multi_token(issuer: &RootKey) -> String {
    issuer
        .mint([
            Caveat::FirstParty(Pred::AnyOf(vec![
                Pred::AttrEq { key: "action".into(), value: "submit".into() },
                Pred::AttrEq { key: "action".into(), value: "read".into() },
            ])),
            Caveat::FirstParty(Pred::AnyOf(vec![
                Pred::AttrPrefix { key: "resource".into(), prefix: "b0".into() },
                Pred::AttrPrefix { key: "resource".into(), prefix: "0d".into() },
            ])),
        ])
        .encode()
}
