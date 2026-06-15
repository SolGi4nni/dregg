//! durable_workflow — a DBOS-shaped durable workflow whose every step is a
//! VERIFIED, capability-gated turn. The deos "durable verified workflow" made
//! runnable, end to end, with no postgres and no live node.
//!
//! Run it:
//!
//! ```text
//! cargo run --example durable_workflow
//! ```
//!
//! # What this is
//!
//! [DBOS](https://www.dbos.dev/) gives you *durable execution*: a multi-step
//! workflow checkpoints each step to a durable log, and after a crash it replays
//! from the log so the workflow runs **exactly once**. That is real — but a DBOS
//! step is ordinary code issuing an ordinary `UPDATE`, so DBOS trusts the writer.
//! A step with the bug `UPDATE balances SET amount = amount + 1000000` *executes*,
//! and DBOS faithfully makes it execute exactly once. Value is forged, durably.
//!
//! This example drives the SAME durable-execution shape on
//! [`pg_dregg::workflow`] — the real durable surface — where a step is admitted
//! ONLY through the three-gate verified-write spine
//! ([`WorkflowEngine::submit`]): **AUTHZ** (the actor's capability must admit
//! `submit` on its cell — the real [`authz::decide`]), **CHAIN** (the produced
//! batch must chain onto the durable head — the real [`RootChain`]
//! anti-substitution tooth), then **APPLY + LOG**. A bare write has no way in.
//!
//! So this is "DBOS, but every step is a verified turn": durable like DBOS *and*
//! unforgeable + attenuable + conserving + receipted, because each step is a
//! verified turn over the durable verified state. It builds entirely ON the
//! `pg_dregg::workflow` runtime (the `WorkflowEngine`, `run_durable`,
//! `recover_from_durable`, `resume_durable`, the `DurableLog` seam) — it does not
//! reinvent any of it.
//!
//! # The arc (each beat asserts its load-bearing property)
//!
//!   1. A four-step treasury workflow runs THROUGH the spine, **checkpointing**
//!      each verified turn to an external [`DurableLog`] (the `dregg.commit_log`
//!      stand-in). Reads are free SQL over the materialized mirror.
//!   2. The unforgeable gate: an **unauthorized** step (the money-printing bug) is
//!      REFUSED by the AUTHZ gate — the head does not move, nothing leaks. This is
//!      exactly the bug DBOS would execute exactly once.
//!   3. A simulated **crash** mid-flight: the engine is dropped after two steps;
//!      only the durable log survives.
//!   4. **Crash recovery**: the engine is rebuilt from the durable log alone,
//!      **re-validating every persisted turn on the way up** (a restored store is
//!      self-checking) and resuming the chain from the head.
//!   5. **Exactly-once resume**: the recovered engine resumes the SAME workflow;
//!      the already-committed prefix is **skipped, never re-applied**, and only the
//!      uncommitted tail is submitted. Two independent mechanisms agree: the
//!      index-skip (fast path) and the chain tooth (the backstop — a stale replay
//!      of a committed step cannot chain).
//!   6. **Conservation** end to end: Σ balances across the mirror equals the
//!      genesis total, every step (value is a property of the verified turn, not a
//!      thing a step can fat-finger).
//!   7. A **tampered** durable log fails recovery **closed** — a substituted root
//!      is caught as the first broken chain link, not silently applied.
//!
//! The SAME properties are proven by the `#[test]`s in `src/workflow.rs` and
//! exercised through real pg18 SQL by the `#[pg_test]`s in `src/lib.rs`
//! (`cargo pgrx test pg18`); this example is the integrated story, runnable.
//!
//! # The verified-turn semantics behind the choreography
//!
//! The workflow's *meaning* — "a step is a capability-gated, protocol-ordered,
//! attested turn, and no unauthorized or out-of-order step can ever commit" — is
//! a machine-checked theorem of the Lean metatheory:
//! `metatheory/Dregg2/Protocol/Workflow.lean` (`exec_authorized`, `exec_in_order`,
//! `merge_requires_approved`), and `metatheory/Dregg2/Deos/WorkflowBridge.lean`
//! proves a workflow step IS a sequenced cap∧state affordance fire (the deos
//! surface renders the choreography, it does not fork it). This example is the
//! *executable, durable* face of that semantics on the postgres-shaped spine. See
//! `docs/deos/DURABLE-WORKFLOW.md` for how the pieces compose.

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::workflow::{
    recover_from_durable, DurableLog, FoldProjector, MapTokens, MemLog, Step, StepError,
    WorkflowEngine,
};

// ── the parties (their cell ids; the high byte is the resource-prefix tag) ──────
const fn agent(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}
const TREASURY: [u8; 32] = agent(0xc0);
const ALICE: [u8; 32] = agent(0xa1);
const BOB: [u8; 32] = agent(0xb0);

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn rule(title: &str) {
    println!("\n\x1b[1m── {title} {}\x1b[0m", "─".repeat(58usize.saturating_sub(title.len())));
}

/// Mint a bearer token admitting `submit`+`read`, attenuated to `who`'s OWN cell
/// prefix — so the holder may submit ONLY turns for its own cell (`granted ⊆
/// held`, the proven no-amplify discipline). This is the real capability the
/// AUTHZ gate decides against, identical in shape to `src/workflow.rs`'s tests.
fn mint_own_cell(issuer: &RootKey, who: [u8; 32]) -> String {
    issuer
        .mint([
            Caveat::FirstParty(Pred::AnyOf(vec![
                Pred::AttrEq { key: "action".into(), value: "submit".into() },
                Pred::AttrEq { key: "action".into(), value: "read".into() },
            ])),
            Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
        ])
        .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
            key: "resource".into(),
            prefix: hx(&who)[..2].to_string(),
        })])
        .encode()
}

fn tokens_for(issuer: &RootKey, who: &[[u8; 32]]) -> MapTokens {
    let mut t = MapTokens::new();
    for &a in who {
        t.bind(a, mint_own_cell(issuer, a));
    }
    t
}

fn main() {
    println!(
        "\x1b[1mpg-dregg — a durable workflow whose every step is a VERIFIED turn\x1b[0m"
    );
    println!("(DBOS-shaped durable execution; each step admitted only by the verified-write spine)");

    // The database trust root: a fixed issuer key (in postgres this is the
    // `dregg.issuer_pubkey` GUC; here we install it directly, then clear caches).
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();
    println!("  issuer (trust root) installed: {}…", &issuer.public().to_hex()[..12]);

    // The four parties hold tokens scoped to their own cells. The four-step
    // workflow: treasury genesis-mints, funds Alice, Alice spends, Alice spends
    // more — an ordered choreography where each step is one verified turn.
    let agents = [TREASURY, ALICE, BOB];
    let steps = || {
        [
            Step::new("genesis: treasury mints 1000", TREASURY).set(TREASURY, 1000, 0),
            Step::new("fund: treasury → alice 400", TREASURY)
                .set(TREASURY, 600, 1)
                .set(ALICE, 400, 0),
            Step::new("alice spends 150 → bob", ALICE).set(ALICE, 250, 1).set(BOB, 150, 0),
            Step::new("alice spends 100 → bob", ALICE).set(ALICE, 150, 2).set(BOB, 250, 1),
        ]
    };
    let workflow = pg_dregg::workflow::Workflow {
        name: "treasury durable workflow".into(),
        steps: steps().to_vec(),
    };

    // =======================================================================
    // 1. RUN THROUGH THE SPINE, CHECKPOINTING EACH VERIFIED TURN.
    // =======================================================================
    rule("1. run the workflow — each step a verified turn, checkpointed");
    // `durable` is the external sink that outlives a crash — the in-process
    // stand-in for `dregg.commit_log`. `run_durable` submits each step through the
    // full AUTHZ → CHAIN → APPLY spine, appending the admitted batch the instant
    // it commits (one logical commit, as the pg submit-gate + INSERT are one txn).
    let mut durable = MemLog::new();
    let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
    let out = engine
        .run_durable(&workflow, &mut durable)
        .expect("the whole workflow runs through the spine");
    assert_eq!(out.committed, 4, "all four steps committed");
    assert_eq!(out.skipped, 0, "a fresh run skips nothing");
    assert_eq!(durable.len(), 4, "each verified turn was checkpointed to the durable log");
    println!("  committed {} verified turns; {} checkpointed to the durable log", out.committed, durable.len());
    // Reads are FREE SQL over the materialized mirror (no verification at read).
    println!(
        "  free-SQL reads over the mirror: treasury={} alice={} bob={}  Σ={}",
        engine.balance(TREASURY),
        engine.balance(ALICE),
        engine.balance(BOB),
        engine.total_value()
    );
    assert_eq!(engine.balance(TREASURY), 600);
    assert_eq!(engine.balance(ALICE), 150);
    assert_eq!(engine.balance(BOB), 250);
    // Every turn names its acting agent — provable who-did-what (the receipt).
    let prov = engine.provenance();
    assert_eq!(prov.len(), 4);
    assert_eq!(prov[0].1, TREASURY, "ordinal 0 creator is the treasury");
    assert_eq!(prov[2].1, ALICE, "ordinal 2 creator is alice");
    println!("  every turn is receipted: ord0→treasury, ord1→treasury, ord2→alice, ord3→alice");

    // =======================================================================
    // 2. THE UNFORGEABLE GATE: an actor acting outside its grant is REFUSED.
    // =======================================================================
    rule("2. an actor outside its capability — REFUSED by the AUTHZ gate");
    // The AUTHZ gate decides `submit` keyed to the ACTING agent's own cell, against
    // the actor's presented capability (`granted ⊆ held`, the proven no-amplify
    // discipline). Two genuine refusals — the unforgeability DBOS structurally
    // cannot offer (a DBOS step is arbitrary code that simply runs; there is no
    // bearer credential bounding *who* may act):
    let head_before = engine.head();
    let turns_before = engine.turn_count();

    //  (a) an UNBOUND actor ⇒ deny-by-default (no session token, no submit).
    let unbound = Step::new("ghost acts", agent(0xff)).set(agent(0xff), 1, 0);
    let err_unbound = engine
        .submit(&unbound)
        .expect_err("an unbound actor must be refused");
    assert!(
        matches!(err_unbound, StepError::Unauthorized { actor, .. } if actor == agent(0xff)),
        "an unbound role is deny-by-default, got {err_unbound:?}"
    );
    println!("  (a) unbound actor: REFUSED ({err_unbound})");

    //  (b) a BOUND actor presenting someone ELSE's token — Bob holds Alice's
    //  a1-scoped token but acts as Bob (resource b0…); the cap is the gate, so it
    //  cannot authorize a resource outside its grant. No amplification.
    let mut foreign = MapTokens::new();
    foreign.bind(BOB, mint_own_cell(&issuer, ALICE)); // BOB presents ALICE's token
    let mut probe = WorkflowEngine::new(foreign);
    let err_foreign = probe
        .submit(&Step::new("bob forges with alice's token", BOB).set(BOB, 999_999, 0))
        .expect_err("a foreign-scoped token must be refused");
    assert!(
        matches!(err_foreign, StepError::Unauthorized { actor, .. } if actor == BOB),
        "an actor cannot amplify past its held capability, got {err_foreign:?}"
    );
    assert_eq!(probe.turn_count(), 0, "the refused forge logged no turn");
    println!("  (b) bob with alice's foreign token: REFUSED ({err_foreign})");

    // A refused step moves NOTHING on the live engine — head unchanged, no leak.
    assert_eq!(engine.head(), head_before, "a refused step does not move the chain head");
    assert_eq!(engine.turn_count(), turns_before, "a refused step logs no turn");
    println!("  → head unmoved, no turn logged: no state exists except as an AUTHORIZED verified turn");

    // =======================================================================
    // 3. SIMULATED CRASH — drop the engine; only the durable log survives.
    // =======================================================================
    rule("3. crash — only the durable log survives");
    // We model a crash AFTER only the first two steps were durable: take a fresh
    // run of just the prefix into a NEW sink, then drop that engine entirely.
    let mut crashed_log = MemLog::new();
    let alice_balance_at_crash;
    let head_at_crash;
    {
        let prefix = pg_dregg::workflow::Workflow {
            name: workflow.name.clone(),
            steps: steps()[..2].to_vec(),
        };
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
        let out = engine
            .run_durable(&prefix, &mut crashed_log)
            .expect("the first two steps checkpoint");
        assert_eq!(out.committed, 2);
        alice_balance_at_crash = engine.balance(ALICE);
        head_at_crash = engine.head().expect("a head exists after two turns");
        // engine dropped HERE — the in-process state is gone; `crashed_log` remains.
    }
    assert_eq!(crashed_log.len(), 2, "exactly the committed prefix is durable");
    println!(
        "  crashed after 2 turns; durable log holds {} turns, head {}…",
        crashed_log.len(),
        &hx(&head_at_crash)[..12]
    );

    // =======================================================================
    // 4. CRASH RECOVERY — rebuild from the log, RE-VALIDATING the chain.
    // =======================================================================
    rule("4. recover — rebuild from the log, re-validating every persisted turn");
    // `recover_from_durable` loads the persisted turns and rebuilds the engine,
    // re-running the chain tooth over EVERY durable turn on the way up (a restored
    // store is self-checking — a log that does not chain is a corrupted store and
    // is surfaced, never silently applied) and resuming the chain from the head.
    let mut recovered =
        recover_from_durable(tokens_for(&issuer, &agents), FoldProjector, &crashed_log)
            .expect("the durable chain re-validates on recovery");
    assert_eq!(recovered.next_ordinal(), 2, "resumed at the durable head ordinal");
    assert_eq!(recovered.head(), Some(head_at_crash), "the head is restored exactly");
    assert_eq!(
        recovered.balance(ALICE),
        alice_balance_at_crash,
        "the materialized balances are restored exactly"
    );
    println!(
        "  recovered: next_ordinal={} (resumed at the head), alice balance restored to {}",
        recovered.next_ordinal(),
        recovered.balance(ALICE)
    );

    // =======================================================================
    // 5. EXACTLY-ONCE RESUME — skip the committed prefix; run only the tail.
    // =======================================================================
    rule("5. resume — exactly-once: the committed prefix is SKIPPED, never re-applied");
    // Resume the SAME four-step workflow. Steps 0,1 are already durable, so they
    // are skipped (their post-images are already materialized); only steps 2,3 are
    // submitted. Exactly-once holds two ways that agree: the index-skip is the fast
    // path, and even a stale re-submit of a committed step would be refused by the
    // chain tooth (it is behind the head) — the chain is the backstop.
    let out = recovered
        .resume_durable(&workflow, &mut crashed_log)
        .expect("the uncommitted tail finishes");
    assert_eq!(out.skipped, 2, "the two committed steps are skipped, never re-applied");
    assert_eq!(out.committed, 2, "only the uncommitted tail (steps 2,3) runs");
    assert_eq!(recovered.turn_count(), 4, "four turns total — no double-apply");
    assert_eq!(crashed_log.len(), 4, "the whole workflow is now durable");
    // The end state matches the uninterrupted run EXACTLY — recovery is transparent.
    assert_eq!(recovered.balance(ALICE), engine.balance(ALICE), "alice's end balance matches the uninterrupted run");
    assert_eq!(recovered.balance(BOB), engine.balance(BOB), "bob's end balance matches the uninterrupted run");
    println!(
        "  resumed: skipped {} committed, ran {} tail → final alice={} bob={} (== the uninterrupted run)",
        out.skipped,
        out.committed,
        recovered.balance(ALICE),
        recovered.balance(BOB)
    );

    // =======================================================================
    // 6. CONSERVATION — Σ balances is invariant under every verified turn.
    // =======================================================================
    rule("6. conservation — Σ balances == genesis, through crash + recovery");
    // Value conservation is a property of the verified turn's transition, not a
    // discipline a step can violate: a credit without a debit is not a
    // representable turn. The free-SQL aggregate over the mirror is the witness.
    assert_eq!(recovered.total_value(), 1000, "Σ balances across the mirror == the genesis total");
    assert_eq!(engine.total_value(), 1000, "and so does the uninterrupted run");
    println!(
        "  Σ balances = {} (== genesis 1000) — conserved across the crash + recovery + resume",
        recovered.total_value()
    );

    // =======================================================================
    // 7. A TAMPERED DURABLE LOG FAILS RECOVERY — CLOSED.
    // =======================================================================
    rule("7. a tampered durable log fails recovery CLOSED");
    // Substitute a persisted root so the chain no longer links. Recovery must
    // catch it as the FIRST broken link and refuse — a self-checking store does
    // not resume against corruption.
    let mut tampered_batches = crashed_log.batches().to_vec();
    tampered_batches[2].turn.prev_root = [0x99u8; 32];
    struct FixedLog(Vec<pg_dregg::mirror::MirrorBatch>);
    impl DurableLog for FixedLog {
        fn append(&mut self, b: &pg_dregg::mirror::MirrorBatch) -> Result<(), String> {
            self.0.push(b.clone());
            Ok(())
        }
        fn load(&self) -> Result<Vec<pg_dregg::mirror::MirrorBatch>, String> {
            Ok(self.0.clone())
        }
    }
    let tampered = FixedLog(tampered_batches);
    match recover_from_durable(MapTokens::new(), FoldProjector, &tampered) {
        Ok(_) => panic!("SECURITY FAILURE: recovery of a tampered log succeeded"),
        Err(e) => println!("  recovery of the tampered log: REFUSED ({e})"),
    }
    println!("  → a substituted durable root is caught on the way up; corruption cannot resume");

    rule("DONE");
    println!(
        "\x1b[1m✓ a durable workflow, exactly-once across a crash, where every step is a verified turn:\x1b[0m"
    );
    println!("  durable-run → forged-write-refused → crash → recover(re-validate) → resume(exactly-once) → conserved.");
    println!("  the SAME properties: `cargo test` (src/workflow.rs) + real pg18 SQL `cargo pgrx test pg18`.");
}
