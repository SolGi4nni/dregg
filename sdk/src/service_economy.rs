//! # The SERVICE-ECONOMY facade — buy a service in a few lines, over the verified rail.
//!
//! This is the developer onramp for dregg's service economy: pay another agent,
//! invoke a service method paying through `Payable`, and run a workload under a
//! durable, metered EXECUTION LEASE. Every method here is a THIN, HONEST wrapper
//! that DESUGARS to a primitive the kernel already verifies — there is no new
//! kernel effect, no new commitment field, and no faking:
//!
//! * [`AgentRuntime::pay`] → the canonical `Payable` `pay` desugar
//!   ([`dregg_payable::resolve_pay`]) → exactly ONE conserving
//!   [`Effect::Transfer`] (per-asset Σδ=0). The SAME route table the app
//!   framework's `Payable::pay` and the metered tool-gateway charge use. Pays in
//!   ANY asset, including a bridged `$DREGG` mirror asset (an ordinary
//!   [`AssetId`]).
//! * [`AgentRuntime::invoke_service_resolved`] / [`AgentRuntime::invoke_service`]
//!   → route a method against the target cell's interface through the VERIFIED
//!   DFA router ([`dregg_payable::resolve_invocation`]), optionally PREPENDING the
//!   canonical pay leg, and desugar to an ordinary [`Action`] carrying the
//!   underlying effects. Unknown-method / serviced-seam / under-authority are
//!   fail-closed refusals at the front door.
//! * [`ExecutionLease`] → open + fund + run a durable-execution lease. `open`
//!   spawns a cap-gated worker scoped to the lease's run verb and installs the
//!   meter/checkpoint program (`FieldLte { step ≤ max_steps } ∧ Monotonic
//!   { step }`) — the SAME executor-enforced shape the standalone
//!   `starbridge-execution-lease` app's `advance_checkpoint` uses; `fund` is a
//!   conserving [`Effect::Transfer`]; `run` advances the durable checkpoint and
//!   meters the workload through the cap-gated worker.
//!
//! ## Why a lease here and not the `starbridge-apps/execution-lease` crate
//!
//! The standalone execution-lease app, the intent-ring service-promise, and the
//! ring-trade coordinator all live ABOVE this SDK (they depend on
//! `dregg-app-framework`'s `AppCipherclerk`, which depends on `dregg-sdk`). The
//! SDK is the bottom layer, so it cannot depend on them without a cycle. What it
//! CAN — and does — reuse are the primitives below the framework that those apps
//! ALSO desugar to: [`dregg_payable::resolve_pay`] (the one conserving transfer),
//! the DFA method router, and the cap-gated [`SubAgent`] executor path with a
//! `Monotonic`/`FieldLte` meter program. So this lease desugars to the SAME
//! verified effect shapes the upper-crate lease app does, reachable in a few
//! lines without leaving the SDK.

use dregg_cell::CellId;
use dregg_cell::interface::MethodSig;
use dregg_cell::program::{CellProgram, StateConstraint, field_from_u64};
use dregg_cell::state::FieldElement;
use dregg_payable::{AssetId, InvokeAuthority, InvokeRefused, resolve_invocation, resolve_pay};
use dregg_token::Attenuation;
use dregg_turn::TurnReceipt;
use dregg_turn::action::{Action, Effect};

use crate::cipherclerk::HeldToken;
use crate::error::SdkError;
use crate::runtime::{AgentRuntime, SubAgent};

/// The default computron fee a service-economy turn rides (mirrors
/// [`AgentRuntime::execute`]'s default).
const SERVICE_TURN_FEE: u64 = 10_000;

/// A payment leg to ride alongside a service invocation: pay `amount` of `asset`
/// to the service `provider`. The CALLER (the invoking runtime's agent cell) is
/// the payer; this leg desugars to the canonical [`dregg_payable::resolve_pay`]
/// conserving [`Effect::Transfer`] prepended to the invocation's effects, so the
/// payment commits atomically with the call or not at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PayLeg {
    /// The provider cell that receives the payment (the `to` of the transfer).
    pub provider: CellId,
    /// The amount of `asset` to pay.
    pub amount: u64,
    /// The asset to pay in (the caller's `token_id`; a bridged `$DREGG` mirror
    /// asset is an ordinary [`AssetId`]).
    pub asset: AssetId,
}

impl PayLeg {
    /// A payment of `amount` of `asset` to `provider`.
    pub fn new(provider: CellId, amount: u64, asset: AssetId) -> PayLeg {
        PayLeg {
            provider,
            amount,
            asset,
        }
    }
}

impl AgentRuntime {
    /// **`pay`** — move `amount` of `asset` from this agent's cell to `to`, through
    /// the canonical `Payable` interface.
    ///
    /// Routes through [`dregg_payable::resolve_pay`] (verified DFA router →
    /// `Signature` cap-gate → desugar) and submits the resulting `pay`-method
    /// action — which carries EXACTLY ONE conserving [`Effect::Transfer`] (per-asset
    /// Σδ=0) — as an ordinary signed agent turn. This is the SAME source-of-truth
    /// route the app framework's `Payable::pay` and the SDK tool-gateway charge ride;
    /// `pay` here is its few-lines front door.
    ///
    /// `asset` is the asset to pay in. For an intra-domain payment use
    /// [`Self::native_asset`] (this agent cell's own `token_id`). A bridged
    /// `$DREGG` is an ordinary [`AssetId`] (the mirror's `MirrorConfig.asset`),
    /// routed identically.
    #[must_use = "dropping the TurnReceipt silently discards proof the payment committed"]
    pub fn pay(&self, to: CellId, amount: u64, asset: AssetId) -> Result<TurnReceipt, SdkError> {
        let (action, _sig) = resolve_pay(
            self.cell_id(),
            asset,
            amount,
            to,
            InvokeAuthority::Signature,
        )
        .map_err(|e| SdkError::Rejected(format!("payable pay route refused: {e}")))?;
        // Sign the resolved `pay`-method action (preserving `action.method == pay`
        // in the committed turn) and submit it as an ordinary agent turn.
        let signed = self.sign_action_for_runtime(action);
        self.submit_signed_action_as_agent(signed, SERVICE_TURN_FEE)
    }

    /// `pay` denominated in this agent cell's NATIVE asset (its `token_id`) — the
    /// common intra-domain transfer. Equivalent to `self.pay(to, amount,
    /// self.native_asset())`.
    #[must_use = "dropping the TurnReceipt silently discards proof the payment committed"]
    pub fn pay_native(&self, to: CellId, amount: u64) -> Result<TurnReceipt, SdkError> {
        self.pay(to, amount, self.native_asset())
    }

    /// This agent cell's native asset id (its `token_id`) — the asset its balance
    /// is denominated in, and the asset an intra-domain [`Self::pay`] moves.
    pub fn native_asset(&self) -> AssetId {
        let ledger = self.ledger().lock().unwrap();
        ledger
            .get(&self.cell_id())
            .map(|c| *c.token_id())
            .unwrap_or([0u8; 32])
    }

    /// **`invoke_service` (the verified DESUGAR)** — route `method` against the
    /// `target` cell's interface and produce the UNSIGNED [`Action`] (with the
    /// matched [`MethodSig`]) that calls it, optionally PREPENDING a `Payable`
    /// payment leg.
    ///
    /// The method is routed through the VERIFIED DFA router
    /// ([`dregg_payable::resolve_invocation`], derived from the target cell's
    /// program). A `pay` leg, if present, is resolved through the canonical
    /// [`dregg_payable::resolve_pay`] and its single conserving [`Effect::Transfer`]
    /// is prepended to `work`, so paying for the call is the SAME verified transfer
    /// the rest of the economy uses — not a hand-rolled effect. Fail-closed:
    /// unknown method, a `Serviced` seam, or under-authority all return
    /// [`InvokeRefused`] before any turn is built.
    ///
    /// This is the pure, executor-free core (testable without a node); see
    /// [`Self::invoke_service`] for the signed-and-submitted wrapper.
    pub fn invoke_service_resolved(
        &self,
        target: CellId,
        method: &str,
        args: Vec<FieldElement>,
        work: Vec<Effect>,
        authority: InvokeAuthority,
        pay: Option<PayLeg>,
    ) -> Result<(Action, MethodSig), InvokeRefused> {
        // The target cell's interface is derived from its on-ledger program.
        let cell = {
            let ledger = self.ledger().lock().unwrap();
            ledger.get(&target).cloned()
        }
        .ok_or_else(|| InvokeRefused::UnknownMethod {
            method: method.to_string(),
        })?;

        // Prepend the canonical pay leg (one conserving Transfer) if requested, so
        // the payment rides the SAME invocation turn.
        let mut effects: Vec<Effect> = Vec::new();
        if let Some(leg) = pay {
            let (pay_action, _pay_sig) = resolve_pay(
                self.cell_id(),
                leg.asset,
                leg.amount,
                leg.provider,
                InvokeAuthority::Signature,
            )?;
            effects.extend(pay_action.effects);
        }
        effects.extend(work);

        resolve_invocation(&cell, method, args, effects, authority)
    }

    /// **`invoke_service` (signed + submitted)** — resolve the invocation via
    /// [`Self::invoke_service_resolved`], then sign it with this runtime's key and
    /// submit it as an agent turn targeting `target`.
    ///
    /// The committed turn carries the routed `method` and the (optionally
    /// pay-prepended) effects. As with [`AgentRuntime::execute_on`], the executor
    /// verifies the runtime's signature against `target`'s authority, so this
    /// commits for a target this runtime administers; for a metered, capability-
    /// gated PAID call against another agent's tool, use the [`crate::ToolGateway`]
    /// (which carries the same `Payable` charge desugar with rate + budget
    /// enforcement).
    #[must_use = "dropping the TurnReceipt silently discards proof the invocation committed"]
    pub fn invoke_service(
        &self,
        target: CellId,
        method: &str,
        args: Vec<FieldElement>,
        work: Vec<Effect>,
        authority: InvokeAuthority,
        pay: Option<PayLeg>,
    ) -> Result<TurnReceipt, SdkError> {
        let (action, _sig) = self
            .invoke_service_resolved(target, method, args, work, authority, pay)
            .map_err(|e| SdkError::Rejected(format!("service invocation refused: {e}")))?;
        let signed = self.sign_action_for_runtime(action);
        self.submit_signed_action_as_agent(signed, SERVICE_TURN_FEE)
    }
}

/// The cell-field slot the [`ExecutionLease`] durable checkpoint counter lives in.
///
/// Mirrors the standalone execution-lease app's `STEP_SLOT`: a monotone step
/// index, advanced once per [`ExecutionLease::run`], with the executor-enforced
/// `FieldLte`/`Monotonic` meter program biting on it. Slot 4 is the conventional
/// first general-purpose slot.
pub const LEASE_STEP_SLOT: u8 = 4;

/// The default run verb a lease worker is scoped to.
pub const DEFAULT_LEASE_METHOD: &str = "run";

/// The terms an [`ExecutionLease`] is opened under.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeaseTerms {
    /// The maximum number of durable checkpoints (`run` calls) the lease admits —
    /// the capacity tier ceiling the executor binds via `FieldLte`.
    pub max_steps: i64,
    /// The run verb the lease worker's credential is scoped to (the method a
    /// [`ExecutionLease::run`] presents). Defaults to [`DEFAULT_LEASE_METHOD`].
    pub method: String,
}

impl LeaseTerms {
    /// Terms admitting `max_steps` durable checkpoints under the default
    /// [`DEFAULT_LEASE_METHOD`] run verb.
    pub fn new(max_steps: i64) -> LeaseTerms {
        LeaseTerms {
            max_steps,
            method: DEFAULT_LEASE_METHOD.to_string(),
        }
    }

    /// Terms with an explicit run verb.
    pub fn with_method(max_steps: i64, method: impl Into<String>) -> LeaseTerms {
        LeaseTerms {
            max_steps,
            method: method.into(),
        }
    }
}

/// The meter/checkpoint program installed on a lease cell — the executor-side half
/// of the durable-execution guarantee.
///
/// `FieldLte { step ≤ max_steps }` binds the capacity ceiling into every committed
/// transition (a `run` past the ceiling is rejected by the executor), and
/// `Monotonic { step }` forbids rewinding the checkpoint counter to forge
/// head-room or replay a stale image. This is the SAME shape the standalone
/// execution-lease app's `advance_checkpoint` relies on (a rewind is refused), and
/// the same `FieldLte ∧ Monotonic` pattern the metered tool-gateway's
/// `mandate_program` uses.
pub fn lease_program(max_steps: i64) -> CellProgram {
    let ceiling = if max_steps < 0 { 0 } else { max_steps as u64 };
    CellProgram::Predicate(vec![
        StateConstraint::FieldLte {
            index: LEASE_STEP_SLOT,
            value: field_from_u64(ceiling),
        },
        StateConstraint::Monotonic {
            index: LEASE_STEP_SLOT,
        },
    ])
}

/// The outcome of one [`ExecutionLease::run`]: the executor receipt for the metered
/// checkpoint turn, plus the new step index and the steps remaining.
#[derive(Clone, Debug)]
pub struct LeaseStep {
    /// The executor receipt proving the metered checkpoint turn committed.
    pub receipt: TurnReceipt,
    /// The durable checkpoint index AFTER this run.
    pub step: i64,
    /// How many runs remain on the lease (`max_steps - step`).
    pub remaining: i64,
}

/// **A durable, metered EXECUTION LEASE — open, fund, run a workload.**
///
/// `open` spawns a cap-gated [`SubAgent`] worker scoped to the lease's run verb and
/// installs the [`lease_program`] meter on its cell. `fund` moves value INTO the
/// lease cell with a conserving [`Effect::Transfer`]. `run` advances the durable
/// checkpoint (a `step → step+1` write the `Monotonic`/`FieldLte` program gates)
/// and meters the workload's effects through the cap-gated worker on the SAME turn,
/// so a workload either commits with an advanced checkpoint or not at all.
///
/// This reuses, in a few lines, the exact verified pattern the metered
/// [`crate::ToolGateway`] proves (cap-gated worker + `FieldLte ∧ Monotonic` meter +
/// conserving funding), specialized to durable-execution checkpoints rather than
/// tool-call rate.
pub struct ExecutionLease {
    /// The cap-gated worker driving the lease (scoped to the run verb).
    worker: SubAgent,
    /// The lease cell (carries the durable checkpoint slot + the meter program).
    lease_cell: CellId,
    /// The asset the lease cell holds value in (its `token_id`).
    asset: AssetId,
    /// The run verb the worker's credential is scoped to.
    method: String,
    /// The capacity ceiling (`max_steps`).
    max_steps: i64,
    /// The durable checkpoint index so far.
    step: i64,
}

impl ExecutionLease {
    /// **Open a durable-execution lease.**
    ///
    /// The grantor (`runtime`, holding `parent_token`) delegates to a freshly
    /// spawned worker scoped to `terms.method`, installs the [`lease_program`]
    /// (capacity ceiling + monotone checkpoint) on the lease cell, and returns the
    /// lease ready to fund and run. The worker's biscuit credential is the
    /// executor-enforced scope; the cell program is the executor-enforced meter.
    pub fn open(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        terms: LeaseTerms,
    ) -> Result<ExecutionLease, SdkError> {
        let worker = runtime.spawn_sub_agent_scoped(
            &Attenuation::default(),
            parent_token,
            &[terms.method.as_str()],
        )?;
        let lease_cell = worker.cell_id();

        let asset = {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger
                .update_with(&lease_cell, |cell| {
                    cell.program = lease_program(terms.max_steps);
                })
                .map_err(|e| SdkError::Rejected(format!("install lease program: {e}")))?;
            ledger
                .get(&lease_cell)
                .map(|c| *c.token_id())
                .unwrap_or([0u8; 32])
        };

        Ok(ExecutionLease {
            worker,
            lease_cell,
            asset,
            method: terms.method,
            max_steps: terms.max_steps,
            step: 0,
        })
    }

    /// **Fund the lease** — move `amount` from `funder`'s cell into the lease cell
    /// with a conserving [`Effect::Transfer`], authorized by the funder's own
    /// credential. The funder must hold value in the lease's asset (e.g. another
    /// worker the same runtime spawned, sharing the domain `token_id`). Returns the
    /// funding turn's receipt.
    #[must_use = "dropping the TurnReceipt silently discards proof the funding committed"]
    pub fn fund(&self, funder: &SubAgent, amount: u64) -> Result<TurnReceipt, SdkError> {
        funder.execute(vec![Effect::Transfer {
            from: funder.cell_id(),
            to: self.lease_cell,
            amount,
        }])
    }

    /// **Run a workload** — advance the durable checkpoint (`step → step+1`) and
    /// meter `work` through the cap-gated worker on ONE turn.
    ///
    /// The checkpoint advance is a `Monotonic`/`FieldLte`-gated [`Effect::SetField`]
    /// on [`LEASE_STEP_SLOT`]; `work` rides the same turn. A run past `max_steps` is
    /// rejected by the executor's `FieldLte`, and the monotone gate refuses any
    /// rewind — so the lease's durable progress is bound into the committed
    /// transition, not merely tracked in memory.
    #[must_use = "dropping the LeaseStep silently discards proof the run committed"]
    pub fn run(&mut self, work: Vec<Effect>) -> Result<LeaseStep, SdkError> {
        let next = self.step + 1;
        let mut effects = Vec::with_capacity(work.len() + 1);
        effects.push(Effect::SetField {
            cell: self.lease_cell,
            index: LEASE_STEP_SLOT as usize,
            value: field_from_u64(next as u64),
        });
        effects.extend(work);

        let receipt = self.worker.execute_method(&self.method, effects)?;
        self.step = next;
        Ok(LeaseStep {
            receipt,
            step: next,
            remaining: self.max_steps - next,
        })
    }

    /// The lease cell id (the cell carrying the checkpoint + meter program).
    pub fn lease_cell(&self) -> CellId {
        self.lease_cell
    }

    /// The asset the lease cell holds value in (its `token_id`).
    pub fn asset(&self) -> AssetId {
        self.asset
    }

    /// The durable checkpoint index so far.
    pub fn step(&self) -> i64 {
        self.step
    }

    /// The runs remaining on the lease (`max_steps - step`).
    pub fn remaining(&self) -> i64 {
        self.max_steps - self.step
    }

    /// Test-only access to the cap-gated worker, to exercise the EXECUTOR-side
    /// meter program (the `Monotonic`/`FieldLte` backstop) independently — e.g. a
    /// caller attempting to rewind the checkpoint directly.
    #[doc(hidden)]
    pub fn worker_for_test(&self) -> &SubAgent {
        &self.worker
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AgentCipherclerk, CellId};
    use dregg_cell::interface::method_symbol;
    use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};
    use std::sync::{Arc, RwLock};

    /// A runtime + a root token to delegate workers from.
    fn runtime_with_root() -> (AgentRuntime, HeldToken) {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[7u8; 32], "compute");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
        (runtime, root)
    }

    fn balance(runtime: &AgentRuntime, cell: CellId) -> i64 {
        let l = runtime.ledger().lock().unwrap();
        l.get(&cell).map(|c| c.state.balance()).unwrap_or(0)
    }

    // ── pay ──────────────────────────────────────────────────────────────────

    #[test]
    fn pay_desugars_to_one_conserving_payable_transfer() {
        // pay routes through the canonical Payable interface (method == pay) and
        // desugars to EXACTLY one conserving Transfer — the same source of truth
        // the gateway charge / app-framework pay use, not a hand-rolled effect.
        let (runtime, _root) = runtime_with_root();
        let to = CellId::from_bytes([9u8; 32]);
        let asset = runtime.native_asset();
        let (action, sig) = resolve_pay(
            runtime.cell_id(),
            asset,
            500,
            to,
            InvokeAuthority::Signature,
        )
        .expect("pay routes through the Payable interface");
        assert_eq!(action.method, dregg_payable::pay_method_sig().symbol);
        assert_eq!(sig, dregg_payable::pay_method_sig());
        assert_eq!(action.effects.len(), 1, "pay desugars to one effect");
        match action.effects[0] {
            Effect::Transfer {
                from,
                to: t,
                amount,
            } => {
                assert_eq!(from, runtime.cell_id());
                assert_eq!(t, to);
                assert_eq!(amount, 500);
            }
            ref other => panic!("pay must desugar to a Transfer, got {other:?}"),
        }
    }

    #[test]
    fn pay_commits_and_conserves_value() {
        // End-to-end on the real executor: a pay between two cells of one asset
        // moves exactly `amount` and conserves the total (Σδ=0).
        let (runtime, root) = runtime_with_root();
        let recipient = runtime
            .spawn_sub_agent(&Attenuation::default(), &root)
            .expect("spawn recipient")
            .cell_id();

        let payer = runtime.cell_id();
        let asset = runtime.native_asset();
        let pre_payer = balance(&runtime, payer);
        let pre_recip = balance(&runtime, recipient);

        let _r = runtime
            .pay(recipient, 1_000, asset)
            .expect("pay commits through the Payable rail");

        let post_payer = balance(&runtime, payer);
        let post_recip = balance(&runtime, recipient);
        // The recipient is credited EXACTLY the transferred amount (the Transfer is
        // conserved into it), and the payer is debited at least that much (plus the
        // turn fee). The only system-balance sink is the fee the payer burned, so
        // the total decrease equals the payer's loss beyond the transfer.
        assert_eq!(
            post_recip - pre_recip,
            1_000,
            "recipient credited exactly 1000"
        );
        let total_decrease = (pre_payer + pre_recip) - (post_payer + post_recip);
        let payer_loss = pre_payer - post_payer;
        assert!(
            payer_loss >= 1_000,
            "payer is debited at least the transfer"
        );
        assert_eq!(
            total_decrease,
            payer_loss - 1_000,
            "the only value sink beyond the conserved transfer is the payer's fee"
        );
    }

    // ── invoke_service ─────────────────────────────────────────────────────────

    /// Install a cell in the runtime ledger whose program dispatches `methods`
    /// (so its derived interface exposes them, all Replayable). Returns its id.
    fn install_service_cell(runtime: &AgentRuntime, methods: &[&str]) -> CellId {
        use dregg_cell::Cell;
        let cases = methods
            .iter()
            .map(|m| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(m),
                },
                constraints: vec![],
            })
            .collect();
        let mut cell = Cell::with_balance([5u8; 32], *blake3::hash(b"compute").as_bytes(), 0);
        cell.program = CellProgram::Cases(cases);
        let id = cell.id();
        runtime.ledger().lock().unwrap().insert_cell(cell).ok();
        id
    }

    #[test]
    fn invoke_service_routes_method_and_refuses_unknown() {
        let (runtime, _root) = runtime_with_root();
        let svc = install_service_cell(&runtime, &["render"]);

        let (action, sig) = runtime
            .invoke_service_resolved(
                svc,
                "render",
                vec![],
                vec![Effect::SetField {
                    cell: svc,
                    index: 0,
                    value: [1u8; 32],
                }],
                InvokeAuthority::None,
                None,
            )
            .expect("a dispatched method routes through the derived interface");
        assert_eq!(action.method, method_symbol("render"));
        assert_eq!(action.target, svc);
        assert_eq!(sig.semantics, dregg_cell::interface::Semantics::Replayable);

        let refused = runtime
            .invoke_service_resolved(
                svc,
                "undeclared",
                vec![],
                vec![],
                InvokeAuthority::None,
                None,
            )
            .unwrap_err();
        assert!(matches!(refused, InvokeRefused::UnknownMethod { .. }));
    }

    #[test]
    fn invoke_service_prepends_canonical_pay_leg() {
        // A paid service call prepends EXACTLY the canonical resolve_pay Transfer
        // (caller -> provider) ahead of the work — the same verified value rail,
        // riding the same invocation turn.
        let (runtime, _root) = runtime_with_root();
        let svc = install_service_cell(&runtime, &["render"]);
        let asset = runtime.native_asset();

        let (action, _sig) = runtime
            .invoke_service_resolved(
                svc,
                "render",
                vec![],
                vec![Effect::SetField {
                    cell: svc,
                    index: 0,
                    value: [2u8; 32],
                }],
                InvokeAuthority::None,
                Some(PayLeg::new(svc, 250, asset)),
            )
            .expect("paid invocation resolves");

        // Effect 0 is the canonical pay Transfer (caller -> provider); effect 1 is
        // the work.
        assert_eq!(action.effects.len(), 2, "pay leg + work");
        match action.effects[0] {
            Effect::Transfer { from, to, amount } => {
                assert_eq!(from, runtime.cell_id(), "the caller pays");
                assert_eq!(to, svc, "the provider is paid");
                assert_eq!(amount, 250);
            }
            ref other => panic!("the pay leg must be a Transfer, got {other:?}"),
        }
        assert!(matches!(action.effects[1], Effect::SetField { .. }));
    }

    // ── ExecutionLease ─────────────────────────────────────────────────────────

    #[test]
    fn lease_program_carries_ceiling_and_monotonic() {
        match lease_program(5) {
            CellProgram::Predicate(cs) => {
                assert_eq!(cs.len(), 2);
                assert!(matches!(
                    cs[0],
                    StateConstraint::FieldLte { index, .. } if index == LEASE_STEP_SLOT
                ));
                assert!(matches!(
                    cs[1],
                    StateConstraint::Monotonic { index } if index == LEASE_STEP_SLOT
                ));
            }
            other => panic!("expected a Predicate program, got {other:?}"),
        }
    }

    #[test]
    fn lease_open_fund_run_commits_and_advances_checkpoint() {
        let (runtime, root) = runtime_with_root();
        let funder = runtime
            .spawn_sub_agent(&Attenuation::default(), &root)
            .expect("spawn funder");

        let mut lease =
            ExecutionLease::open(&runtime, &root, LeaseTerms::new(2)).expect("open lease");

        // Fund the lease — a conserving Transfer into the lease cell.
        let pre = balance(&runtime, lease.lease_cell());
        let _f = lease.fund(&funder, 5_000).expect("fund commits");
        assert_eq!(
            balance(&runtime, lease.lease_cell()) - pre,
            5_000,
            "the lease cell is credited exactly the funded amount"
        );

        // Two runs advance the durable checkpoint monotonically.
        let s1 = lease.run(vec![]).expect("run 1 commits");
        assert_eq!(s1.step, 1);
        assert_eq!(s1.remaining, 1);
        let s2 = lease.run(vec![]).expect("run 2 commits");
        assert_eq!(s2.step, 2);
        assert_eq!(s2.remaining, 0);
        assert_eq!(lease.step(), 2);
    }

    #[test]
    fn lease_run_past_ceiling_is_refused_by_the_executor() {
        // The FieldLte meter binds the capacity ceiling into the committed
        // transition: the run that would exceed max_steps is rejected by the
        // executor itself (the meter tooth), not merely by an in-memory check.
        let (runtime, root) = runtime_with_root();
        let mut lease =
            ExecutionLease::open(&runtime, &root, LeaseTerms::new(1)).expect("open lease");

        let s1 = lease.run(vec![]).expect("run 1 within ceiling commits");
        assert_eq!(s1.step, 1);

        let over = lease.run(vec![]);
        assert!(
            over.is_err(),
            "a run past the capacity ceiling must be rejected by the executor"
        );
        // The rejected run did NOT advance the durable checkpoint.
        assert_eq!(
            lease.step(),
            1,
            "a refused run leaves the checkpoint untouched"
        );
    }
}
