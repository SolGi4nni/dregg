//! # `grain-turn` — the R2 kernel-turn weld, KERNEL-facing half.
//!
//! *THE-GRAIN.md face #1 (Unfoolable), rung R2: "actions become kernel turns,
//! receipts become views" (`turn_receipt_hash` populated).*
//!
//! `dregg-agent`'s [`AgentCloud::drive_state`] is, by default, a PARALLEL universe:
//! a local [`ReplenishingMeter`], a `BTreeMap<String, String>` heap, a BLAKE3
//! `cell_root`, an ed25519 receipt chain — **no executor, no `dregg_cell::Cell`, no
//! kernel turn**. The [`GrainTurnMinter`] seam
//! ([`dregg_agent::agent::GrainTurnMinter`]) is the bridge; this crate is its ONE
//! real implementation: [`ToolGatewayMinter`] turns every admitted agent action
//! into a **genuine committed executor turn** on a real `dregg_cell::Cell` (the
//! "grain turn-cell"), and hands back that turn's `turn_hash`, which the agent run
//! loop seals into the action's [`AgentReceipt`] as its `turn_receipt_hash` — the
//! receipt becomes a typed VIEW over a real kernel transition.
//!
//! ## The grain turn-cell
//!
//! The grain turn-cell IS the [`ToolGateway`]'s cap-gated worker cell. Its slots:
//!
//! * **`calls_made`** (slot [`CALLS_MADE_SLOT`](dregg_sdk::CALLS_MADE_SLOT), = 4) — the metered turn counter the
//!   gateway advances `c → c+1` on every committed invocation, carrying the proven
//!   [`mandate_program`](dregg_sdk::ToolGateway) backstop
//!   `FieldLte { calls_made ≤ rate_limit } ∧ Monotonic { calls_made }`. This is the
//!   host-side meter: the EXECUTOR ITSELF rejects an over-rate or rolled-back
//!   counter write, even against a buggy or bypassing session loop.
//! * **`consumed`** (slot [`CONSUMED_SLOT`], = 5) — the session meter's post-draw
//!   consumed total, written as witness state on the same metered turn.
//! * **`heap_root`** (slot [`HEAP_ROOT_SLOT`], = 6) — the agent's committed cell
//!   root at the point of the call, likewise witnessed on the turn.
//! * **`action`** (slot [`ACTION_SLOT`], = 7) — [`action_commit`]`(label, cost)`,
//!   the BLAKE3 commit to WHICH action this turn was minted for and what it drew;
//!   the kernel transition itself commits to the action, so a receipt and its
//!   linked turn cannot silently disagree about what was done.
//! * the cell **nonce** — advanced by the executor on every committed turn (the
//!   anti-replay/anti-reorder link binding each turn to its predecessor's receipt).
//!
//! ## Honest scope (R2, not R3)
//!
//! R2 makes the executor's own `calls_made` caveat (`FieldLte` + `Monotonic`)
//! enforce the meter **host-side** — the meter stops being merely session-local: a
//! session loop that skipped or double-counted its local meter still cannot drive
//! the on-ledger counter past the granted ceiling, because the executor rejects the
//! turn. It still TRUSTS THE EXECUTOR HOST that committed the turn — that residual
//! is exactly what R3's whole-history STARK leg (`WHOLE_HISTORY_GAP`) removes: R2
//! makes the meter a kernel caveat, R3 makes it a FRI-floor theorem.
//!
//! The rate ceiling is set to the agent's **budget**, so `calls_made ≤ budget`
//! host-side is the call-count face of the session meter. For the flat cost-1 path
//! the two coincide exactly; for variable-cost (`Spend`) actions the on-ledger
//! `calls_made ≤ budget` is a conservative call-count backstop under the session
//! meter's value bound (the session meter remains the value ceiling).

use std::sync::{Arc, RwLock};

use dregg_agent::agent::GrainTurnMinter;
use dregg_cell::program::field_from_u64;
use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, CALLS_MADE_SLOT, CellId, Effect, SdkError, ToolGateway,
    ToolGrant,
};

#[cfg(feature = "prover")]
mod finalize;
#[cfg(feature = "prover")]
pub use finalize::{finalize_grain_turn, finalize_session};

/// **A captured grain turn — the R3-adapter input.** Everything
/// [`finalize_grain_turn`](crate::finalize_grain_turn) needs to mint the rotated
/// wide-anchored EffectVM leg(s) for a turn `ToolGatewayMinter` committed, so it
/// becomes the `FinalizedTurn`(s) the whole-history fold folds. Captured on EVERY
/// [`mint_turn`](GrainTurnMinter::mint_turn) (cheap — two `Cell` clones + the effect
/// list), independent of whether the `prover` R3 leg is ever minted.
///
/// The `effects` are the FULL committed set the executor applied to the worker cell:
/// the gateway's `calls_made` `SetField` PREPENDED to the tool's witness work — the
/// same order [`ToolGateway::invoke`] built, so the EffectVM projection reproduces the
/// committed transition (there is no per-call charge on the grain grant, so no charge
/// `Transfer` rides).
#[derive(Clone, Debug)]
pub struct GrainTurnRecord {
    /// The committed turn hash — the R2 link (the manifest entry).
    pub turn_hash: [u8; 32],
    /// The grain worker cell BEFORE the executor committed this turn (its pre-state:
    /// balance / nonce / fields / cap root — the leg's genesis old-root).
    pub before_cell: dregg_cell::Cell,
    /// The grain worker cell AFTER the committed turn (its post-state — the executor's
    /// on-ledger head for this turn).
    pub after_cell: dregg_cell::Cell,
    /// The FULL effect list the executor applied (gateway `calls_made` SetField ‖ work).
    pub effects: Vec<Effect>,
}

/// Slot on the grain turn-cell that witnesses the session meter's post-draw
/// `consumed` total (written on the metered turn). Distinct from
/// [`CALLS_MADE_SLOT`](dregg_sdk::CALLS_MADE_SLOT) (the gateway-owned counter) and [`HEAP_ROOT_SLOT`].
pub const CONSUMED_SLOT: usize = 5;

/// Slot on the grain turn-cell that witnesses the agent's committed cell
/// `heap_root` at the point of the call (written on the metered turn).
pub const HEAP_ROOT_SLOT: usize = 6;

/// Slot on the grain turn-cell that witnesses WHICH action this turn was minted
/// for: [`action_commit`]`(label, cost)` — the BLAKE3 commit binding the action
/// label and its budget draw into the committed kernel state. Without this slot
/// the turn would witness only meter state (a turn happened, the meter moved);
/// with it, the kernel transition itself commits to *what* the action was, so a
/// receipt and its linked turn cannot silently disagree about the action.
pub const ACTION_SLOT: usize = 7;

/// Slot on the grain turn-cell that witnesses the commitment to the zkOracle
/// attestation the turn was driven UNDER — a 32-byte hash of the confined brain's
/// [`ZkOracleAttestation`](dregg_zkoracle_prove::ZkOracleAttestation) (authentic ∧
/// well-formed ∧ injection-free) bound onto the SAME metered turn. Written only when
/// a commitment is [`bound`](ToolGatewayMinter::bind_attestation); an unattested turn
/// leaves it at the cell's zero default, so a landed receipt reveals whether the turn
/// was driven by an attested brain. THE FUSION: the on-ledger turn now commits to
/// "this action was driven by a jailed, attested brain" — a light client holding the
/// attestation recomputes its commitment and confirms it equals THIS slot.
///
/// grain-turn stays crypto-agnostic: it commits to a caller-supplied 32-byte hash.
/// The canonical hash of a `ZkOracleAttestation` is
/// `deos_hermes::attestation_commitment` (where the attestation type lives).
pub const ATTESTATION_SLOT: usize = 8;

/// Domain separator for [`action_commit`].
pub const ACTION_COMMIT_DOMAIN: &[u8] = b"dregg-grain-action-commit-v1";

/// The canonical action commit witnessed at [`ACTION_SLOT`] on every grain turn:
/// `BLAKE3(domain ‖ len(label) ‖ label ‖ cost)`. Length-prefixed so `(label,
/// cost)` pairs cannot collide by concatenation. Pure — a verifier holding a
/// receipt's `(action, cost)` recomputes it to check what the turn witnessed.
pub fn action_commit(label: &str, cost: i64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(ACTION_COMMIT_DOMAIN);
    h.update(&(label.len() as u64).to_le_bytes());
    h.update(label.as_bytes());
    h.update(&cost.to_le_bytes());
    *h.finalize().as_bytes()
}

/// A large-but-finite deadline for the grain mandate — the DEADLINE conjunct of
/// `delegAdmit` is not the meter here (the rate ceiling is), so it is set far out;
/// a real deployment binds it to the lease expiry.
const GRAIN_DEADLINE: i64 = i64::MAX / 2;

/// The single allowlisted tool id the grain mandate is scoped to (the SCOPE
/// conjunct); every grain turn presents this id.
const GRAIN_TOOL_ID: i64 = 1;

/// The executor method verb the grain worker's biscuit credential is scoped to.
const GRAIN_TOOL_METHOD: &str = "grain.turn";

/// **The REAL [`GrainTurnMinter`]** — drives every admitted agent action through a
/// genuine [`ToolGateway::invoke`] on a real `dregg_cell::Cell` grain turn-cell.
///
/// Construct one with [`ToolGatewayMinter::open`] (it mints a fresh runtime, admits
/// a cap-gated worker under a rate-`budget` [`ToolGrant`], and installs the
/// `mandate_program` backstop on the worker cell), then hand `Some(&mut minter)` to
/// [`AgentCloud::run_goal_minted`](dregg_agent::agent::AgentCloud::run_goal_minted)
/// / [`Session::run_goal_minted`](dregg_agent::session::Session::run_goal_minted).
/// Each admitted action becomes a committed kernel turn; a turn the executor
/// REFUSES (over-rate / insolvent) is surfaced as an `Err`, and the agent run loop
/// admits nothing for it (no draw, no receipt).
pub struct ToolGatewayMinter {
    /// The shared ledger the worker turns commit against (also the read path for
    /// [`read_slot`](Self::read_slot) — what the grain turn-cell REALLY committed).
    runtime: AgentRuntime,
    /// The cap-gated worker + its metered `calls_made` counter + the mandate cell.
    gateway: ToolGateway,
    /// The presentation clock/height every grain turn is stamped at. The DEADLINE
    /// leg is far out; the meter is the RATE leg (`calls_made ≤ budget`).
    now: i64,
    /// The committed turn hashes, in order — the "committed-turn manifest" a
    /// grain-verify R2 tooth checks the agent's receipts against.
    minted: Vec<[u8; 32]>,
    /// The zkOracle attestation commitment (a 32-byte hash of the confined brain's
    /// [`ZkOracleAttestation`](dregg_zkoracle_prove::ZkOracleAttestation)) to bind onto
    /// the turns this minter commits — witnessed at [`ATTESTATION_SLOT`]. `None` = the
    /// turns are unattested (the slot stays at its zero default). Set with
    /// [`bind_attestation`](Self::bind_attestation).
    pending_attestation: Option<[u8; 32]>,
    /// The per-turn R3-adapter records (pre-cell, effects, post-cell) captured on every
    /// committed turn — the input `finalize_session` folds into `FinalizedTurn`s.
    records: Vec<GrainTurnRecord>,
}

impl ToolGatewayMinter {
    /// Open a grain turn-cell: a fresh runtime + a [`ToolGateway`] whose cap-gated
    /// worker cell IS the grain turn-cell. The rate ceiling is `budget`, so the
    /// executor's own `calls_made` `FieldLte` caveat bounds the number of committed
    /// turns host-side (the meter as a kernel caveat). Fails only if the executor
    /// refuses to admit the worker.
    pub fn open(domain: &str, budget: i64) -> Result<ToolGatewayMinter, SdkError> {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[0x6au8; 32], domain);
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), domain);
        let grant = ToolGrant {
            tool_id: GRAIN_TOOL_ID,
            rate_limit: budget.max(0),
            deadline: GRAIN_DEADLINE,
            tool_method: GRAIN_TOOL_METHOD.to_string(),
        };
        let gateway = ToolGateway::admit(&runtime, &root, grant)?;
        Ok(ToolGatewayMinter {
            runtime,
            gateway,
            now: 0,
            minted: Vec::new(),
            pending_attestation: None,
            records: Vec::new(),
        })
    }

    /// Like [`ToolGatewayMinter::open`], but stamps the OWNER-SIGNED ENVELOPE on the grain
    /// worker cell. `owner_vk_hash` = `dregg_turn::executor::owner_envelope::owner_envelope_vk`
    /// over the renter/owner pubkey (`RenterAnchor.pubkey`, held by `AgentPlatform::rent`).
    /// The host, lacking the owner key, cannot escalate its authority over the grain through
    /// the executor. See [`crate::ToolGatewayMinter::open`] for the rest of the lifecycle.
    pub fn open_enveloped(
        domain: &str,
        budget: i64,
        owner_vk_hash: [u8; 32],
    ) -> Result<ToolGatewayMinter, SdkError> {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[0x6au8; 32], domain);
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), domain);
        let grant = ToolGrant {
            tool_id: GRAIN_TOOL_ID,
            rate_limit: budget.max(0),
            deadline: GRAIN_DEADLINE,
            tool_method: GRAIN_TOOL_METHOD.to_string(),
        };
        let gateway = ToolGateway::admit_enveloped(&runtime, &root, grant, owner_vk_hash)?;
        Ok(ToolGatewayMinter {
            runtime,
            gateway,
            now: 0,
            minted: Vec::new(),
            pending_attestation: None,
            records: Vec::new(),
        })
    }

    /// **Bind a zkOracle attestation commitment onto this minter's turns.** Every turn
    /// minted after this call witnesses `commitment` at [`ATTESTATION_SLOT`] — the
    /// on-ledger turn now commits to "this action was driven by an attested brain."
    /// `commitment` is the canonical hash of the confined brain's
    /// [`ZkOracleAttestation`](dregg_zkoracle_prove::ZkOracleAttestation)
    /// (`deos_hermes::attestation_commitment`); a light client re-verifies the
    /// attestation and confirms its recomputed commitment equals the landed slot. Pass
    /// the commitment for the brain turn that drove this action.
    pub fn bind_attestation(&mut self, commitment: [u8; 32]) {
        self.pending_attestation = Some(commitment);
    }

    /// The attestation commitment currently bound (witnessed on the next turn), or
    /// `None` if the turns are unattested.
    pub fn bound_attestation(&self) -> Option<[u8; 32]> {
        self.pending_attestation
    }

    /// Read a witnessed slot straight off the COMMITTED grain turn-cell state in
    /// the real ledger (not a tracked mirror). `None` if the cell is absent or the
    /// index is out of range. This is the ground-truth read the slot-witness tests
    /// use: what the kernel actually committed, not what this struct remembers.
    pub fn read_slot(&self, index: usize) -> Option<[u8; 32]> {
        let ledger = self.runtime.ledger().lock().ok()?;
        let cell = ledger.get(&self.gateway.worker_cell())?;
        cell.state.fields.get(index).copied()
    }

    /// The grain turn-cell id (the mandate cell carrying `calls_made`).
    pub fn grain_cell(&self) -> CellId {
        self.gateway.worker_cell()
    }

    /// The grain worker cell's current [`Permissions`](dregg_cell::Permissions) — for
    /// verifying the owner-signed envelope stamp ([`Self::open_enveloped`]).
    pub fn worker_permissions(&self) -> Option<dregg_cell::Permissions> {
        self.runtime
            .ledger()
            .lock()
            .ok()?
            .get(&self.grain_cell())
            .map(|c| c.permissions.clone())
    }

    /// The number of grain turns committed so far (the on-ledger `calls_made`).
    pub fn calls_made(&self) -> i64 {
        self.gateway.calls_made()
    }

    /// The committed turn hashes, in order — the manifest a grain-verify R2 tooth
    /// checks each agent receipt's `turn_receipt_hash` against ("this link names a
    /// genuine committed turn").
    pub fn committed_turns(&self) -> &[[u8; 32]] {
        &self.minted
    }

    /// The per-turn R3-adapter records captured for this session, in commit order —
    /// the input [`finalize_session`](crate::finalize_session) folds into the
    /// `FinalizedTurn` chain (available whether or not the `prover` leg is minted;
    /// the capture itself is on the commit path).
    pub fn records(&self) -> &[GrainTurnRecord] {
        &self.records
    }

    /// Clone the CURRENT committed grain worker cell straight off the real ledger
    /// (a genuine `Cell` snapshot, not a mirror) — the pre/post state the R3 leg
    /// binds. `None` if the cell is absent (never, after admission).
    fn snapshot_worker_cell(&self) -> Option<dregg_cell::Cell> {
        let ledger = self.runtime.ledger().lock().ok()?;
        ledger.get(&self.gateway.worker_cell()).cloned()
    }
}

impl GrainTurnMinter for ToolGatewayMinter {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        let cell = self.gateway.worker_cell();
        // The tool's witness work rides the SAME metered turn as the gateway's
        // `calls_made : c → c+1` advance: the session's consumed total, the
        // agent's heap root, AND the action commit (`action_commit(label, cost)`)
        // are written as grain-turn-cell state, so the committed turn witnesses
        // WHAT the action was — which action, at what cost, over which heap —
        // not merely that a turn happened.
        let mut work = vec![
            Effect::SetField {
                cell,
                index: CONSUMED_SLOT,
                value: field_from_u64(consumed_after.max(0) as u64),
            },
            Effect::SetField {
                cell,
                index: HEAP_ROOT_SLOT,
                value: cell_root,
            },
            Effect::SetField {
                cell,
                index: ACTION_SLOT,
                value: action_commit(label, cost),
            },
        ];
        // THE FUSION: when an attestation commitment is bound, witness it on the SAME
        // metered turn — the committed kernel transition now commits to the confined
        // brain's zkOracle attestation, so the landed receipt binds "driven by an
        // attested brain." An unattested turn omits it (the slot stays zero).
        if let Some(commitment) = self.pending_attestation {
            work.push(Effect::SetField {
                cell,
                index: ATTESTATION_SLOT,
                value: commitment,
            });
        }
        // R3-ADAPTER CAPTURE (pre-state). Snapshot the worker cell BEFORE the commit and
        // reconstruct the FULL effect set the executor will apply — the gateway prepends
        // `SetField { calls_made : c → c+1 }` to `work` (`ToolGateway::invoke`), so the
        // captured list mirrors the committed transition the R3 rotated leg re-proves.
        let before_cell = self.snapshot_worker_cell();
        let mut committed_effects = Vec::with_capacity(work.len() + 1);
        committed_effects.push(Effect::SetField {
            cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64((self.gateway.calls_made() + 1) as u64),
        });
        committed_effects.extend(work.iter().cloned());

        // The genuine executor turn. `Err` = the executor refused host-side (its
        // `calls_made` caveat over-rate, or an insolvent turn) — the agent run loop
        // treats it as a refused action (no draw, no receipt).
        let receipt = self
            .gateway
            .invoke(GRAIN_TOOL_ID, self.now, work)
            .map_err(|e| e.to_string())?;
        let turn_hash = receipt.receipt.turn_hash;
        self.minted.push(turn_hash);

        // R3-ADAPTER CAPTURE (post-state). Record the committed turn only if both
        // snapshots exist (they always do after admission) — a missing snapshot is not
        // fatal to the R2 turn, so it degrades to "not R3-finalizable", never a panic.
        if let (Some(before_cell), Some(after_cell)) = (before_cell, self.snapshot_worker_cell()) {
            self.records.push(GrainTurnRecord {
                turn_hash,
                before_cell,
                after_cell,
                effects: committed_effects,
            });
        }
        Ok(turn_hash)
    }
}

#[cfg(test)]
mod envelope_stamp_tests {
    use super::*;
    use dregg_cell::AuthRequired;

    #[test]
    fn open_enveloped_stamps_owner_gated_authority() {
        let owner_vk = [0x42u8; 32];
        let m = ToolGatewayMinter::open_enveloped("env-test", 10, owner_vk)
            .expect("admit enveloped grain");
        let perms = m.worker_permissions().expect("worker permissions");
        // Authority-WIDENING is owner-gated: the host, lacking the owner key, cannot craft a
        // Delegate/SetPermissions/SetVerificationKey turn through the executor.
        assert!(
            matches!(perms.set_permissions, AuthRequired::Custom { vk_hash } if vk_hash == owner_vk)
        );
        assert!(matches!(perms.delegate, AuthRequired::Custom { vk_hash } if vk_hash == owner_vk));
        assert!(
            matches!(perms.set_verification_key, AuthRequired::Custom { vk_hash } if vk_hash == owner_vk)
        );
        // set_state stays Signature — the host still advances calls_made; only escalation is locked.
        assert!(matches!(perms.set_state, AuthRequired::Signature));

        // Contrast: a plain (non-enveloped) worker is NOT owner-gated.
        let plain = ToolGatewayMinter::open("plain", 10).expect("admit plain grain");
        let pp = plain.worker_permissions().expect("plain perms");
        assert!(
            !matches!(pp.delegate, AuthRequired::Custom { .. }),
            "plain worker delegate must not be owner-Custom-gated"
        );
    }
}
