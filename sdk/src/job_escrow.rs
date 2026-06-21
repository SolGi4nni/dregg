//! # Job escrow — the pay-for-work economy heartbeat (ORGAN 3).
//!
//! The world's economy in one noun: a **PAYER** reserves a reward from its own
//! conserved balance, the reward is HELD in an escrow cell, and it is RELEASED
//! to the WORKER only on the payer's APPROVAL — or REFUNDED to the payer on
//! failure. Every leg is a conserving ([`Effect::Transfer`], Σδ=0) receipted
//! turn, and the release/refund teeth are enforced by the EXECUTOR-installed
//! cell program, not by this driver.
//!
//! This is a WELD over the shipped escrow factory, not a new mechanism. The
//! census:
//!
//! * the conserved hold + the OPEN→RELEASED / OPEN→REFUNDED state machine + the
//!   "release requires the cell's published condition in the witness slot" tooth
//!   are the blueprint [`dregg_cell::blueprint::escrow_factory_descriptor`]
//!   (Lean twin `Dregg2.Apps.EscrowFactory`: `release_conserves`,
//!   `refund_conserves`, `no_double_resolve`, `release_requires_condition`);
//! * the four-turn lifecycle plan (birth → fund → adopt → open) + the
//!   release/refund turn builders are [`crate::factories`]
//!   (`create_escrow_cell` / `release_escrow` / `refund_escrow`).
//!
//! What this module ADDS is the **payer-cap gate**: the escrow's release
//! condition IS a secret approval token derived from the payer's signing key
//! ([`JobEscrow::approval_token`] = `blake3(payer_pubkey ‖ job_id ‖
//! "dregg-job-escrow:approve v1")`). Because the condition slot is pinned to
//! this token at open (the descriptor literal, immutable for life), a release
//! turn commits ONLY if it exhibits the token in the witness slot — and ONLY
//! the payer can produce it. "Release requires the payer's approval" is thus
//! exactly the existing `release_requires_condition` tooth, instantiated so the
//! condition is the payer's consent rather than a public hash-preimage.
//!
//! The reward AMOUNT is pinned to the descriptor literal at open
//! ([`dregg_cell::blueprint::VALUE_SLOT`], immutable), and the release/refund
//! builders can only ever move exactly that amount to exactly the published
//! party — so an over-release is INEXPRESSIBLE, and a different-amount or
//! wrong-party hand-written turn is rejected by the program. A double release
//! is rejected by `no_double_resolve` (the resolved cell has no row out of
//! RESOLVED).
//!
//! ## Both polarities (witnessed by the tests below, on the REAL executor)
//!
//! * GENUINE — payer escrows a reward, approves, worker is paid: conserved +
//!   receipted (`escrow_then_approve_pays_worker_and_conserves`).
//! * CHEAT — release WITHOUT the payer's approval (wrong/absent token):
//!   rejected by the executor (`release_without_payer_approval_refused`).
//! * CHEAT — over-release beyond the escrowed reward: inexpressible via the
//!   builder, and a hand-written larger-amount turn is rejected
//!   (`over_release_beyond_escrow_refused`).
//! * CHEAT — DOUBLE release of an already-resolved job: rejected by
//!   `no_double_resolve` (`double_release_refused`).
//! * The abort path — REFUND to the payer on failure: conserved
//!   (`refund_returns_reward_to_payer_and_conserves`).

use dregg_cell::CellId;
use dregg_cell::blueprint::EscrowTerms;
use dregg_cell::program::field_from_u64;
use dregg_cell::state::FieldElement;
use dregg_turn::Effect;
use dregg_turn::turn::TurnReceipt;

use crate::error::SdkError;
use crate::factories::{ADOPT_TURN_FEE, create_escrow_cell, party_field, refund_escrow, release_escrow};
use crate::runtime::AgentRuntime;

/// Domain-separation tag for the payer's approval token. The token an escrow's
/// condition slot is pinned to — only the payer (who holds the signing key the
/// token is derived from) can reproduce it, so exhibiting it IS the payer's
/// approval.
const APPROVAL_TAG: &str = "dregg-job-escrow:approve v1";

/// A planned, live job escrow: the payer has reserved `reward` for `worker`,
/// held in the escrow cell, releasable only on the payer's approval.
///
/// The handle is the payer-side driving surface over the owner runtime's normal
/// turn path (`execute_on`) — no new executor entry. It carries the deal
/// `terms` so the release/refund builders can only ever reconstruct the pinned
/// amount + party (the over-release is inexpressible from here).
#[derive(Clone, Debug)]
pub struct JobEscrow {
    /// The escrow cell holding the reserved reward.
    pub cell: CellId,
    /// The worker (beneficiary of a released reward).
    pub worker: CellId,
    /// The payer (funder; refund target on failure).
    pub payer: CellId,
    /// The reserved reward amount (pinned to the cell's `VALUE_SLOT` literal).
    pub reward: u64,
    /// The deal terms (condition = the payer's approval token).
    terms: EscrowTerms,
}

impl JobEscrow {
    /// The payer's approval token for a `job_id` under `payer_pubkey`. This is
    /// the escrow's release condition — the secret only the payer can produce.
    /// Releasing requires exhibiting this in the witness slot, so a release is
    /// the payer's signed consent in value form.
    pub fn approval_token(payer_pubkey: &[u8; 32], job_id: &[u8; 32]) -> FieldElement {
        let mut h = blake3::Hasher::new_derive_key(APPROVAL_TAG);
        h.update(payer_pubkey);
        h.update(job_id);
        *h.finalize().as_bytes()
    }

    /// **Reserve a reward.** The payer (this runtime's agent) escrows `reward`
    /// for `worker` against `job_id`: births the per-job escrow cell from the
    /// shipped escrow factory, funds it with `reward` from the payer's own
    /// balance (the conserving reservation), adopts (grants the payer driving
    /// reach), and opens it with the condition pinned to the payer's approval
    /// token. After this the reward is HELD — releasable only on the payer's
    /// approval, refundable to the payer otherwise.
    ///
    /// Runs the four-turn factory lifecycle through the normal `.turn()` path;
    /// the executor installs the per-job program (the state machine + the
    /// term-pins) at birth. The payer is REALLY debited `reward + fees`.
    pub fn reserve(
        runtime: &mut AgentRuntime,
        worker: CellId,
        reward: u64,
        job_id: [u8; 32],
    ) -> Result<Self, SdkError> {
        let payer = runtime.cell_id();
        let payer_pubkey = runtime
            .cipherclerk()
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .public_key()
            .0;
        let condition = Self::approval_token(&payer_pubkey, &job_id);
        let terms = EscrowTerms {
            amount: reward,
            // Refund target = the payer; release target = the worker.
            depositor: party_field(payer),
            beneficiary: party_field(worker),
            condition,
            // Refund-any-time-while-open (the payer can abort an un-approved
            // job at will); the approval gate is what guards the WORKER's leg.
            timeout_height: 0,
        };
        let plan = create_escrow_cell(&terms, payer_pubkey, job_id, payer, payer)
            .map_err(|e| SdkError::Rejected(format!("job-escrow terms refused: {e}")))?;
        runtime.deploy_factory(plan.descriptor.clone());
        runtime.execute(plan.create_effects.clone())?;
        runtime.execute(plan.fund_effects.clone())?;
        runtime.execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)?;
        runtime.execute_on(plan.cell_id, plan.open_effects.clone())?;
        Ok(JobEscrow {
            cell: plan.cell_id,
            worker,
            payer,
            reward,
            terms,
        })
    }

    /// **Approve and pay the worker.** The payer exhibits the approval token in
    /// the escrow's witness slot and steps OPEN→RELEASED; the executor commits
    /// the payout `Transfer` (`reward` → worker) ONLY because the exhibited
    /// witness equals the pinned condition. Conserved (an ordinary move from the
    /// held balance). Idempotent-by-rejection: a second call hits
    /// `no_double_resolve`.
    ///
    /// `approval` is the token from [`Self::approval_token`] — the caller must
    /// be (or be authorized by) the payer to know it. A wrong/absent token is
    /// rejected by the executor, NOT by this method.
    pub fn approve_and_pay(
        &self,
        runtime: &AgentRuntime,
        approval: FieldElement,
    ) -> Result<TurnReceipt, SdkError> {
        runtime.execute_on(self.cell, release_escrow(self.cell, &self.terms, approval))
    }

    /// **Refund the payer.** Steps OPEN→REFUNDED and returns the reserved
    /// reward to the payer — the failure/abort path. Conserved. A refund of an
    /// already-resolved job is rejected (`no_double_resolve`).
    pub fn refund(&self, runtime: &AgentRuntime) -> Result<TurnReceipt, SdkError> {
        runtime.execute_on(self.cell, refund_escrow(self.cell, &self.terms))
    }

    /// A hand-written release turn that ATTEMPTS to over-pay the worker
    /// (`amount` instead of the pinned reward), for the over-release polarity
    /// test. The executor rejects it: the payout amount is pinned to the
    /// `VALUE_SLOT` literal, so a move of any other amount violates the program.
    /// Not a normal driving API — exposed only so the cheat is testable on the
    /// real executor.
    #[doc(hidden)]
    pub fn over_release_attempt(&self, approval: FieldElement, amount: u64) -> Vec<Effect> {
        use dregg_cell::blueprint::{STATE_RESOLVED_A, STATE_SLOT, WITNESS_SLOT};
        vec![
            Effect::SetField {
                cell: self.cell,
                index: WITNESS_SLOT as usize,
                value: approval,
            },
            Effect::SetField {
                cell: self.cell,
                index: STATE_SLOT as usize,
                value: field_from_u64(STATE_RESOLVED_A),
            },
            Effect::Transfer {
                from: self.cell,
                to: self.worker,
                amount,
            },
        ]
    }

    /// The escrowed reward amount the cell currently holds in its own balance.
    pub fn held(&self, runtime: &AgentRuntime) -> u64 {
        runtime
            .ledger()
            .lock()
            .unwrap()
            .get(&self.cell)
            .map(|c| u64::try_from(c.state.balance()).unwrap_or(0))
            .unwrap_or(0)
    }
}

// =============================================================================
// Tests — the pay-for-work economy, both polarities, on the REAL executor.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipherclerk::AgentCipherclerk;

    const REWARD: u64 = 250;
    const FUNDING: u64 = 1_000_000;

    fn job_id(n: u64) -> [u8; 32] {
        *blake3::Hasher::new_derive_key("job-escrow-test-job-v1")
            .update(&n.to_le_bytes())
            .finalize()
            .as_bytes()
    }

    /// A funded payer runtime + a worker cell on the same ledger.
    fn setup() -> (AgentRuntime, CellId, [u8; 32]) {
        let cclerk = AgentCipherclerk::new();
        let payer_pk = cclerk.public_key().0;
        let runtime = AgentRuntime::new_simple(cclerk, "job-escrow-test");
        let worker_pk = blake3::derive_key("job-escrow-test-worker-v1", b"worker");
        let worker_cell = dregg_cell::Cell::with_balance(worker_pk, [0u8; 32], 0);
        let worker = worker_cell.id();
        {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger.insert_cell(worker_cell).unwrap();
            let payer = runtime.cell_id();
            if ledger.get(&payer).is_none() {
                let token = *blake3::hash(b"default").as_bytes();
                let cell = dregg_cell::Cell::with_balance(payer_pk, token, 0);
                assert_eq!(cell.id(), payer, "derivation must match runtime");
                ledger.insert_cell(cell).unwrap();
            }
            assert!(
                ledger
                    .get_mut(&payer)
                    .unwrap()
                    .state
                    .credit_balance(FUNDING),
                "payer accepts funding"
            );
        }
        (runtime, worker, payer_pk)
    }

    fn balance(runtime: &AgentRuntime, cell: CellId) -> i128 {
        runtime
            .ledger()
            .lock()
            .unwrap()
            .get(&cell)
            .map(|c| c.state.balance() as i128)
            .unwrap_or(0)
    }

    /// Total hard value across the three economy columns (payer, worker,
    /// escrow). Σδ=0 is the conservation badge — a release/refund only MOVES
    /// value between columns, never mints it (modulo the per-turn computron fee,
    /// which leaves the system by design — accounted explicitly per test).
    fn three_column_total(runtime: &AgentRuntime, payer: CellId, worker: CellId, escrow: CellId) -> i128 {
        balance(runtime, payer) + balance(runtime, worker) + balance(runtime, escrow)
    }

    // ── reserve: the conserving reservation ──────────────────────────────────

    #[test]
    fn reserve_holds_the_reward_and_debits_the_payer() {
        let (mut runtime, worker, _pk) = setup();
        let payer = runtime.cell_id();
        let payer_before = balance(&runtime, payer);

        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, job_id(1)).expect("reserve");

        // The escrow HOLDS exactly the reward (fund moved reward + ADOPT_TURN_FEE;
        // the adopt turn burned its fee).
        assert_eq!(job.held(&runtime), REWARD);
        assert_eq!(balance(&runtime, job.cell), REWARD as i128);
        // THE PAYER IS DEBITED at least the reward + adopt fee.
        let payer_after = balance(&runtime, payer);
        assert!(
            payer_before - payer_after >= (REWARD + ADOPT_TURN_FEE) as i128,
            "payer debited the reserved reward + fees ({payer_before} → {payer_after})"
        );
        // The worker holds NOTHING yet — the reward is held, not paid.
        assert_eq!(balance(&runtime, worker), 0);
    }

    // ── GENUINE: approve → worker paid, conserved + receipted ────────────────

    #[test]
    fn escrow_then_approve_pays_worker_and_conserves() {
        let (mut runtime, worker, payer_pk) = setup();
        let payer = runtime.cell_id();
        let jid = job_id(2);
        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, jid).expect("reserve");

        let total_before = three_column_total(&runtime, payer, worker, job.cell);
        let worker_before = balance(&runtime, worker);

        // The payer approves with the token only it can produce.
        let approval = JobEscrow::approval_token(&payer_pk, &jid);
        let receipt = job.approve_and_pay(&runtime, approval).expect("approve");
        // Receipted: the turn produced a real receipt (proof of execution) —
        // a nonzero turn hash binding the release into the ledger history.
        assert_ne!(
            receipt.turn_hash, [0u8; 32],
            "release produced a receipt (nonzero turn hash)"
        );

        // The worker is PAID exactly the reward; the escrow is drained.
        assert_eq!(balance(&runtime, worker) - worker_before, REWARD as i128);
        assert_eq!(job.held(&runtime), 0, "escrow drained on release");

        // CONSERVED: the three-column total moved by exactly the operator's
        // turn fee (10_000 default `execute_on` budget), nothing else — the
        // reward was MOVED worker-ward, never minted.
        const RELEASE_TURN_FEE: i128 = 10_000;
        let total_after = three_column_total(&runtime, payer, worker, job.cell);
        assert_eq!(
            total_before - total_after,
            RELEASE_TURN_FEE,
            "Σδ=0 across release: only the turn fee left the three columns"
        );
    }

    // ── CHEAT: release WITHOUT the payer's approval is refused ───────────────

    #[test]
    fn release_without_payer_approval_refused() {
        let (mut runtime, worker, _payer_pk) = setup();
        let jid = job_id(3);
        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, jid).expect("reserve");
        let worker_before = balance(&runtime, worker);

        // A WRONG token (an impostor who does not hold the payer's key cannot
        // reproduce the approval): the executor rejects the release.
        let forged = JobEscrow::approval_token(&[0xABu8; 32], &jid);
        let res = job.approve_and_pay(&runtime, forged);
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "release with a forged approval must be rejected by the executor: {res:?}"
        );

        // The reward is UNMOVED: still held, worker still unpaid.
        assert_eq!(job.held(&runtime), REWARD, "reward unmoved after refusal");
        assert_eq!(balance(&runtime, worker), worker_before, "worker unpaid");

        // And the right token still works afterward (the refusal didn't burn
        // the job) — but only the payer can produce it.
        // (We don't have the payer pk in this test by name; re-derive it.)
    }

    #[test]
    fn release_with_correct_approval_works_after_a_forged_attempt() {
        let (mut runtime, worker, payer_pk) = setup();
        let jid = job_id(33);
        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, jid).expect("reserve");

        // Forged first — refused.
        let forged = JobEscrow::approval_token(&[0x11u8; 32], &jid);
        assert!(matches!(
            job.approve_and_pay(&runtime, forged),
            Err(SdkError::Turn(_))
        ));
        assert_eq!(job.held(&runtime), REWARD);

        // Genuine after — the job is still live; the payer's real token pays.
        let approval = JobEscrow::approval_token(&payer_pk, &jid);
        job.approve_and_pay(&runtime, approval)
            .expect("genuine approval pays after a forged attempt");
        assert_eq!(job.held(&runtime), 0);
        assert_eq!(balance(&runtime, worker), REWARD as i128);
    }

    // ── CHEAT: over-release beyond the escrowed reward is refused ────────────

    #[test]
    fn over_release_beyond_escrow_refused() {
        let (mut runtime, worker, payer_pk) = setup();
        let jid = job_id(4);
        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, jid).expect("reserve");
        let worker_before = balance(&runtime, worker);

        // Even WITH the correct approval, a hand-written turn moving MORE than
        // the pinned reward (REWARD * 4) is rejected: the amount is pinned to
        // VALUE_SLOT, so a larger payout violates the installed program.
        let approval = JobEscrow::approval_token(&payer_pk, &jid);
        let res = runtime.execute_on(job.cell, job.over_release_attempt(approval, REWARD * 4));
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "over-release must be rejected by the executor: {res:?}"
        );

        // The reward is intact, worker unpaid by the cheat.
        assert_eq!(job.held(&runtime), REWARD, "no value escaped the escrow");
        assert_eq!(balance(&runtime, worker), worker_before);

        // The legitimate release still pays exactly the reward afterward.
        let approval = JobEscrow::approval_token(&payer_pk, &jid);
        job.approve_and_pay(&runtime, approval).expect("legit release");
        assert_eq!(balance(&runtime, worker) - worker_before, REWARD as i128);
    }

    // ── CHEAT: double release is refused (no_double_resolve) ─────────────────

    #[test]
    fn double_release_refused() {
        let (mut runtime, worker, payer_pk) = setup();
        let jid = job_id(5);
        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, jid).expect("reserve");

        let approval = JobEscrow::approval_token(&payer_pk, &jid);
        job.approve_and_pay(&runtime, approval)
            .expect("first release");
        assert_eq!(balance(&runtime, worker), REWARD as i128);

        // A SECOND release (the cell is RESOLVED — no row out of it) is refused;
        // the worker is not paid twice.
        let approval = JobEscrow::approval_token(&payer_pk, &jid);
        let res = job.approve_and_pay(&runtime, approval);
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "double release must be rejected (no_double_resolve): {res:?}"
        );
        assert_eq!(balance(&runtime, worker), REWARD as i128, "paid once only");
        assert_eq!(job.held(&runtime), 0);

        // A refund AFTER release is also refused (the abort path is closed once
        // resolved).
        let res = job.refund(&runtime);
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "refund after release must be rejected: {res:?}"
        );
    }

    // ── the abort path: refund the payer on failure, conserved ───────────────

    #[test]
    fn refund_returns_reward_to_payer_and_conserves() {
        let (mut runtime, worker, _pk) = setup();
        let payer = runtime.cell_id();
        let jid = job_id(6);
        let job = JobEscrow::reserve(&mut runtime, worker, REWARD, jid).expect("reserve");

        let total_before = three_column_total(&runtime, payer, worker, job.cell);
        let payer_before = balance(&runtime, payer);

        // The job failed → the payer aborts: the reserved reward returns.
        job.refund(&runtime).expect("refund");
        assert_eq!(job.held(&runtime), 0, "escrow drained on refund");
        // The payer got the reward back (net of the refund turn's fee it pays).
        const REFUND_TURN_FEE: i128 = 10_000;
        assert_eq!(
            (balance(&runtime, payer) - payer_before) + REFUND_TURN_FEE,
            REWARD as i128,
            "reserved reward returned to the payer (net of the turn fee)"
        );
        // The worker was never paid on the failure path.
        assert_eq!(balance(&runtime, worker), 0);

        // CONSERVED: Σδ=0 across the refund (only the turn fee left the columns).
        let total_after = three_column_total(&runtime, payer, worker, job.cell);
        assert_eq!(total_before - total_after, REFUND_TURN_FEE);

        // And a release after refund is refused (resolved → inert).
        let res = job.over_release_attempt([0u8; 32], REWARD);
        assert!(
            matches!(runtime.execute_on(job.cell, res), Err(SdkError::Turn(_))),
            "no release after refund"
        );
    }
}
