//! Property / fuzz tests for the DURABLE WORKFLOW RUNTIME — the DBOS-shaped
//! exactly-once + conservation discipline, fuzzed. The crown jewel here is
//! `crash_at_any_step_recovers_exactly_once`: for an ARBITRARY conserving
//! workflow and an ARBITRARY crash point, recovering from the durable log and
//! resuming yields the IDENTICAL final state as a no-crash run — no turn lost,
//! none double-applied — and value is conserved throughout. This is the property
//! that separates pg-dregg from a bare durable-execution engine (DBOS makes a
//! step run once; pg-dregg makes it run once AND conserve AND stay attenuable),
//! fuzzed over crash interleavings the unit tests fix.
//!
//! Run: `cargo test --test proptest_workflow`
//!
//! NOTE: the authz core uses process-global state (issuer key, LRU, revocation
//! set), so these tests SERIALIZE on a guard, exactly as the unit tests do.

use std::sync::Mutex;

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::workflow::{
    recover_from_durable, FoldProjector, MapTokens, MemLog, Step, StepError, Workflow,
    WorkflowEngine,
};
use proptest::prelude::*;

static SERIAL: Mutex<()> = Mutex::new(());
fn lock() -> std::sync::MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(|p| p.into_inner())
}

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

const fn agent(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

/// The fixed issuer, installed as THE trust root with caches cleared.
fn install() -> RootKey {
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();
    issuer
}

/// A token admitting `submit` on the agent's own cell prefix (so it may submit
/// ONLY turns for its own cell — `granted ⊆ held`, the attenuation discipline).
fn own_cell_token(issuer: &RootKey, a: [u8; 32]) -> String {
    issuer
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "submit".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: hx(&a)[..2].to_string(),
            }),
        ])
        .encode()
}

fn tokens_for(issuer: &RootKey, agents: &[[u8; 32]]) -> MapTokens {
    let mut t = MapTokens::new();
    for &a in agents {
        t.bind(a, own_cell_token(issuer, a));
    }
    t
}

/// Build a CONSERVING workflow: a genesis mint of `float` to agent 0, then a
/// sequence of `moves` unit transfers around a ring of `agents`. Each transfer is
/// (1 debit + 1 credit), so Σ balances stays == `float` at every step. Returns
/// the workflow and the agent set it acts over.
fn conserving_workflow(float: i64, moves: &[u8], agents: &[[u8; 32]]) -> Workflow {
    let mut wf = Workflow::new("fuzz-conserving");
    wf.push(Step::new("genesis", agents[0]).set(agents[0], float, 0));

    let mut bal: Vec<i64> = vec![0; agents.len()];
    bal[0] = float;
    let mut nonce: Vec<u64> = vec![1; agents.len()];
    let mut holder = 0usize;
    for &m in moves {
        // The receiver is chosen by the fuzz byte (mod ring size); a self-transfer
        // (to == holder) is skipped so every emitted step is a real 2-cell move.
        let to = (m as usize) % agents.len();
        if to == holder || bal[holder] < 1 {
            continue;
        }
        bal[holder] -= 1;
        bal[to] += 1;
        wf.push(
            Step::new("xfer", agents[holder])
                .set(agents[holder], bal[holder], nonce[holder])
                .set(agents[to], bal[to], nonce[to]),
        );
        nonce[holder] += 1;
        nonce[to] += 1;
        holder = to;
    }
    wf
}

/// Run a workflow to completion (no crash), returning the final per-agent
/// balances + the turn count — the ORACLE the crash-recovery path must match.
fn run_to_completion(wf: &Workflow, issuer: &RootKey, agents: &[[u8; 32]]) -> (Vec<i64>, usize) {
    let mut engine = WorkflowEngine::new(tokens_for(issuer, agents)).with_clock(1_000);
    engine
        .run(wf)
        .expect("a conserving authorized workflow must run clean");
    let bals = agents.iter().map(|&a| engine.balance(a)).collect();
    (bals, engine.turn_count())
}

fn ring4() -> Vec<[u8; 32]> {
    (0..4).map(|k| agent(0x30 + k)).collect()
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 200, ..ProptestConfig::default() })]

    /// THE CROWN JEWEL — crash at ANY step recovers EXACTLY ONCE. For an arbitrary
    /// conserving workflow and an arbitrary crash point, the durable log holds the
    /// committed prefix; recovering from it (re-validating the chain) and resuming
    /// the tail yields the IDENTICAL final balances + turn count as a no-crash run.
    /// Nothing is lost (the tail finishes), nothing is double-applied (the prefix
    /// is skipped), and the chain refuses any re-apply.
    #[test]
    fn crash_at_any_step_recovers_exactly_once(
        moves in prop::collection::vec(0u8..4, 1..24),
        crash_frac in 0u8..=100,
    ) {
        let _g = lock();
        let issuer = install();
        let agents = ring4();
        let wf = conserving_workflow(1_000, &moves, &agents);
        prop_assume!(wf.len() >= 2); // need at least genesis + one transfer to crash mid-stream

        // The no-crash oracle.
        let (oracle_bals, oracle_turns) = run_to_completion(&wf, &issuer, &agents);

        // Run a PREFIX (the crash point), checkpointing to an external durable log,
        // then "crash" (drop the engine, keep only the log).
        let crash_after = ((wf.len() as u32 * crash_frac as u32) / 100).max(1) as usize;
        let crash_after = crash_after.min(wf.len());
        let prefix = Workflow { name: wf.name.clone(), steps: wf.steps[..crash_after].to_vec() };

        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents)).with_clock(1_000);
        let mut durable = MemLog::new();
        engine.run_durable(&prefix, &mut durable).expect("the prefix commits clean");
        let durable_len_at_crash = durable.len();
        drop(engine); // ✸ CRASH ✸ — in-memory chain + balances gone; only `durable` survives.
        prop_assert_eq!(durable_len_at_crash, crash_after, "every prefix step is durable");

        // Recover from the durable log (re-validates every persisted turn) and
        // resume the SAME workflow — the uncommitted tail.
        let mut engine = recover_from_durable(tokens_for(&issuer, &agents), FoldProjector, &durable)
            .expect("the durable chain re-validates on recovery")
            .with_clock(1_000);
        let out = engine.resume_durable(&wf, &mut durable).expect("the tail finishes");

        // Exactly-once: the committed prefix is skipped, the tail runs, the totals add up.
        prop_assert_eq!(out.skipped, crash_after, "the durable prefix is skipped, never re-applied");
        prop_assert_eq!(out.skipped + out.committed, wf.len(), "skipped + committed == the whole workflow");
        prop_assert_eq!(engine.turn_count(), oracle_turns, "the same number of turns as a no-crash run");

        // The recovered final state is IDENTICAL to the no-crash oracle.
        let recovered_bals: Vec<i64> = agents.iter().map(|&a| engine.balance(a)).collect();
        prop_assert_eq!(&recovered_bals, &oracle_bals, "crash-recovery reproduces the no-crash final state exactly");

        // Conservation held throughout: Σ balances == the genesis float.
        prop_assert_eq!(engine.total_value(), 1_000, "value is conserved across the recovered workflow");
    }

    /// A SECOND crash (resume itself crashes mid-tail) STILL recovers exactly-once:
    /// recovering from the resumed log and resuming again finishes the remaining
    /// tail with the identical final state. Recovery is idempotent under repeated
    /// crashes — a turn committed in the first resume is never re-applied in the second.
    #[test]
    fn a_second_crash_during_resume_still_finishes_exactly_once(
        moves in prop::collection::vec(0u8..4, 4..24),
    ) {
        let _g = lock();
        let issuer = install();
        let agents = ring4();
        let wf = conserving_workflow(1_000, &moves, &agents);
        prop_assume!(wf.len() >= 4);

        let (oracle_bals, oracle_turns) = run_to_completion(&wf, &issuer, &agents);

        // Crash 1: commit a third, keep the log.
        let c1 = (wf.len() / 3).max(1);
        let p1 = Workflow { name: wf.name.clone(), steps: wf.steps[..c1].to_vec() };
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents)).with_clock(1_000);
        let mut durable = MemLog::new();
        engine.run_durable(&p1, &mut durable).unwrap();
        drop(engine);

        // Recover, then resume only a SECOND third (a partial tail), then crash again.
        let c2 = (2 * wf.len() / 3).max(c1 + 1).min(wf.len());
        let p2 = Workflow { name: wf.name.clone(), steps: wf.steps[..c2].to_vec() };
        let mut engine = recover_from_durable(tokens_for(&issuer, &agents), FoldProjector, &durable)
            .expect("recover 1")
            .with_clock(1_000);
        engine.resume_durable(&p2, &mut durable).unwrap();
        drop(engine); // ✸ CRASH 2 ✸

        // Recover again + finish the whole workflow.
        let mut engine = recover_from_durable(tokens_for(&issuer, &agents), FoldProjector, &durable)
            .expect("recover 2")
            .with_clock(1_000);
        let out = engine.resume_durable(&wf, &mut durable).unwrap();

        prop_assert_eq!(out.skipped, c2, "the twice-committed prefix is skipped");
        prop_assert_eq!(engine.turn_count(), oracle_turns, "two crashes lose / duplicate nothing");
        let bals: Vec<i64> = agents.iter().map(|&a| engine.balance(a)).collect();
        prop_assert_eq!(&bals, &oracle_bals, "two crashes still reproduce the no-crash state");
        prop_assert_eq!(engine.total_value(), 1_000, "conservation survives repeated crashes");
    }

    /// A TAMPERED durable log fails recovery CLOSED. Substituting any persisted
    /// turn's prev_root makes the chain not re-validate, so recovery RETURNS an
    /// error (the FIRST broken link) rather than silently resuming a forged store —
    /// the self-checking-store property, fuzzed over which turn is tampered.
    #[test]
    fn a_tampered_durable_log_fails_recovery_closed(
        moves in prop::collection::vec(0u8..4, 4..20),
        sub in any::<[u8; 32]>(),
    ) {
        let _g = lock();
        let issuer = install();
        let agents = ring4();
        let wf = conserving_workflow(1_000, &moves, &agents);
        prop_assume!(wf.len() >= 3);

        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents)).with_clock(1_000);
        engine.run(&wf).expect("runs");
        let mut log = engine.into_log();

        // Tamper a non-genesis turn's prev_root (so it no longer chains onto its
        // predecessor). Pick the middle turn; assume the substitution actually differs.
        let idx = log.len() / 2;
        prop_assume!(sub != log[idx].turn.prev_root);
        log[idx].turn.prev_root = sub;

        let result = WorkflowEngine::try_recover_with(MapTokens::new(), FoldProjector, log);
        prop_assert!(result.is_err(), "recovery of a tampered durable log must fail closed");
    }

    /// A workflow whose step acts OUTSIDE its grant is refused by the AUTHZ gate at
    /// exactly that step, leaving a CLEAN durable prefix (every step before the
    /// refusal is durable; the refused step and everything after are not). The
    /// no-amplification gate composes with durability: a step a capability does not
    /// admit cannot commit, no matter how the workflow is shaped.
    #[test]
    fn an_unauthorized_step_stops_with_a_clean_durable_prefix(
        good_prefix in 1usize..8,
    ) {
        let _g = lock();
        let issuer = install();
        let agents = ring4();
        // BOB is the intruder — NOT bound, and acting on its own cell which no other
        // agent's token admits. Build: `good_prefix` authorized self-acts by agent 0,
        // then a BOB step (unauthorized), then a trailing authorized step.
        let bob = agent(0xb0);
        let a0 = agents[0];
        let mut wf = Workflow::new("partial-auth");
        for k in 0..good_prefix {
            wf.push(Step::new("ok", a0).set(a0, 100 + k as i64, k as u64));
        }
        wf.push(Step::new("intruder", bob).set(bob, 999, 0));
        wf.push(Step::new("never", a0).set(a0, 1, good_prefix as u64));

        // Only agent 0 is bound (BOB is not), so the BOB step is deny-by-default.
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &[a0])).with_clock(1_000);
        let mut durable = MemLog::new();
        let err = engine.run_durable(&wf, &mut durable).unwrap_err();

        prop_assert!(matches!(err, StepError::Unauthorized { actor, .. } if actor == bob),
            "the intruder step is refused by the authz gate");
        // Exactly the authorized prefix is durable — the refusal left a clean log.
        prop_assert_eq!(durable.len(), good_prefix, "only the authorized prefix committed");
        prop_assert_eq!(engine.turn_count(), good_prefix, "the refused step moved nothing");
    }
}
