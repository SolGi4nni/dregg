//! The DISTRIBUTED backing — a dregg cell resolved by a REAL turn.
//!
//! In `FIRMAMENT.md §3` the distributed end of the gradation is a dregg cell
//! on a (possibly remote) federation. The invocation is a turn through the
//! executor-PD; attenuation/delegation is the real `recKDelegateAtten` gate
//! (`granted ⊆ held`, the capability crown / `checkSubset`); revocation is the
//! group-key epoch lift.
//!
//! This module wires to the GENUINE dregg executor — NOT a mock. It holds a
//! real [`dregg_cell::Ledger`] and a real [`dregg_turn::TurnExecutor`], and:
//!
//! - [`DistributedBacking::invoke`] resolves a cap by reading the target cell
//!   out of the real ledger (a turn would normally carry an effect; the
//!   minimal invoke is a presence/authority resolution against the real
//!   cell-state).
//! - [`DistributedBacking::delegate`] runs a GENUINE `Effect::GrantCapability`
//!   turn through `TurnExecutor::execute`, so the `granted ⊆ held` law is
//!   enforced by the real executor's attenuation gate (the same
//!   `is_attenuation` the `capability_attenuation` invariant exercises). A
//!   widening grant is rejected by the executor with `DelegationDenied` —
//!   the real distributed half of "adoption is attenuation".
//!
//! On a real firmament the executor-PD runs `execFullForestG`; here on the
//! host we drive the executor that PD embeds, so the attenuation semantics are
//! byte-for-byte the deployed ones.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnExecutor,
    TurnResult,
};

use crate::{Backing, Bounds, Resolution, ResolveError, Rights};

/// The distributed backing: a real dregg ledger + executor. `n` is the number
/// of machines the federation spans; `n = 1` is the firmament's collapsed
/// limit (synchronous commit, immediate revocation).
pub struct DistributedBacking {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The distance parameter for THIS federation (how spread the cells are).
    pub n: u32,
}

impl DistributedBacking {
    /// A fresh single-machine (`n = 1`) federation with an empty ledger.
    pub fn new() -> Self {
        DistributedBacking {
            ledger: Ledger::new(),
            executor: TurnExecutor::new(ComputronCosts::zero()),
            n: 1,
        }
    }

    /// Set the distance parameter (the number of machines). `n = 1` keeps the
    /// strong local bounds; `n > 1` relaxes them (the reach-out to the wire).
    pub fn with_distance(mut self, n: u32) -> Self {
        self.n = n;
        self
    }

    /// Seed a cell into the real ledger with permissive permissions, returning
    /// its [`CellId`]. (The deterministic key derivation mirrors the
    /// protocol-test generators so cells are addressable by seed.)
    pub fn seed_cell(&mut self, seed: u8) -> CellId {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(7);
        let mut cell = Cell::with_balance(pk, [0u8; 32], 10_000);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let id = cell.id();
        self.ledger.insert_cell(cell).expect("seed cell");
        id
    }

    /// Grant `holder` an ORIGINAL capability over `target` with `rights` —
    /// the firmament minting a dregg cell-cap into a holder's c-list. (This is
    /// the distributed analog of [`crate::LocalBacking::install`].)
    pub fn install(&mut self, holder: CellId, target: CellId, rights: Rights) {
        let cell = self.ledger.get_mut(&holder).expect("holder cell exists");
        // Replace any auto-granted cap to `target` with one at exactly `rights`.
        if let Some(slot) = cell.capabilities.lookup_by_target(&target).map(|c| c.slot) {
            cell.capabilities.revoke(slot);
        }
        cell.capabilities.grant(target, rights);
    }

    /// Resolve (invoke) a holder's capability over `target` with `rights`.
    ///
    /// Models a turn that resolves the cap against real cell-state: the held
    /// cap must exist and cover the requested `rights` (`requested ⊆ held`,
    /// the REAL [`dregg_cell::is_attenuation`]). Returns a [`Resolution`] with
    /// the `n`-parametrized bounds (collapsing to strong-local at `n = 1`).
    pub fn invoke(
        &self,
        holder: CellId,
        target: CellId,
        rights: &Rights,
    ) -> Result<Resolution, ResolveError> {
        let cell = self
            .ledger
            .get(&holder)
            .ok_or(ResolveError::TargetNotFound)?;
        let held = cell
            .capabilities
            .lookup_by_target(&target)
            .ok_or(ResolveError::TargetNotFound)?;
        if !dregg_cell::is_attenuation(&held.permissions, rights) {
            return Err(ResolveError::Unauthorized(format!(
                "dregg cap-authority check: requested {:?} exceeds held {:?} over cell",
                rights, held.permissions
            )));
        }
        Ok(Resolution {
            backing: Backing::DistributedTurn,
            bounds: Bounds::distributed(self.n),
            note: format!(
                "turn resolved cap over cell (held {:?}, n={})",
                held.permissions, self.n
            ),
        })
    }

    /// `recKDelegateAtten` — the DISTRIBUTED attenuation primitive, run as a
    /// GENUINE turn through the real executor.
    ///
    /// `granter` issues `Effect::GrantCapability(target, narrower)` to
    /// `recipient`. The REAL executor enforces `granted ⊆ held`: it commits
    /// iff the grant is attenuating, and rejects with `DelegationDenied`
    /// otherwise. This is the real distributed half of "adoption is
    /// attenuation" — byte-for-byte the deployed semantics. Returns `Ok(())`
    /// on a committed (attenuating) grant; `Err(BackingRejected)` if the
    /// executor refused (a widening grant).
    pub fn delegate(
        &mut self,
        granter: CellId,
        recipient: CellId,
        target: CellId,
        narrower: Rights,
    ) -> Result<(), ResolveError> {
        let nonce = self
            .ledger
            .get(&granter)
            .expect("granter exists")
            .state
            .nonce();
        // Chain into the REAL receipt chain: `None` for the granter's first turn,
        // the prior receipt's hash thereafter (the executor enforces this per-agent
        // as `ReceiptChainMismatch`). Threading it lets a cell delegate MORE THAN
        // ONCE through one backing without a spurious replay rejection.
        let previous_receipt_hash = self.executor.get_last_receipt_hash(&granter);
        // Chain the delegated cap onto the granter's HELD cap over `target`: the
        // executor's grant arm (`grant_ref`) folds this `provenance` in as the
        // installed cap's PARENT (`cap_provenance(target, new_slot, parent, …)`),
        // so the child's revocation-nullifier transitively binds the ancestor —
        // a revoke of the granter's held cap kills this delegation too (the seL4
        // MDB subtree teardown). Fall back to a mint-rooted parent only if the
        // granter holds no such cap (the executor's attenuation gate then rejects).
        let parent_provenance = self
            .ledger
            .get(&granter)
            .and_then(|c| c.capabilities.lookup_by_target(&target))
            .map(|held| held.provenance)
            .unwrap_or_else(dregg_cell::derivation::mint_provenance);
        let cap = CapabilityRef {
            target,
            slot: 0, // rewritten by the executor on grant
            permissions: narrower,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
            provenance: parent_provenance,
        };
        let action = Action {
            target: granter,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::GrantCapability {
                from: granter,
                to: recipient,
                cap,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        let turn = Turn {
            agent: granter,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let result = self.executor.execute(&turn, &mut self.ledger);
        match result {
            r if r.is_committed() => Ok(()),
            TurnResult::Rejected { reason, .. } => Err(ResolveError::BackingRejected(format!(
                "executor refused grant: {:?}",
                reason
            ))),
            other => Err(ResolveError::BackingRejected(format!(
                "unexpected: {:?}",
                other
            ))),
        }
    }

    /// Does `recipient` hold a cap over `target`? (Used to confirm a delegate
    /// landed — the distributed analog of `LocalBacking::is_live`.)
    pub fn holds_cap(&self, recipient: CellId, target: CellId) -> bool {
        self.ledger
            .get(&recipient)
            .map(|c| c.capabilities.lookup_by_target(&target).is_some())
            .unwrap_or(false)
    }

    /// The rights `recipient` holds over `target`, if any.
    pub fn rights_held(&self, recipient: CellId, target: CellId) -> Option<Rights> {
        self.ledger.get(&recipient).and_then(|c| {
            c.capabilities
                .lookup_by_target(&target)
                .map(|r| r.permissions.clone())
        })
    }
}

impl Default for DistributedBacking {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_executor_enforces_attenuation_on_delegate() {
        let mut fed = DistributedBacking::new();
        let granter = fed.seed_cell(0);
        let recipient = fed.seed_cell(1);
        let target = fed.seed_cell(2);

        // Granter holds Signature over target.
        fed.install(granter, target, AuthRequired::Signature);

        // Attenuating delegate (Signature -> Impossible is narrower) COMMITS
        // through the real executor.
        assert!(fed
            .delegate(granter, recipient, target, AuthRequired::Impossible)
            .is_ok());
        assert!(fed.holds_cap(recipient, target));
        assert_eq!(
            fed.rights_held(recipient, target),
            Some(AuthRequired::Impossible)
        );
    }

    #[test]
    fn real_executor_rejects_amplifying_delegate() {
        let mut fed = DistributedBacking::new();
        let granter = fed.seed_cell(0);
        let recipient = fed.seed_cell(1);
        let target = fed.seed_cell(2);

        // Granter holds only Signature over target.
        fed.install(granter, target, AuthRequired::Signature);

        // Amplifying delegate (Signature -> None is WIDER) is REJECTED by the
        // real executor (DelegationDenied), and recipient gets nothing.
        let r = fed.delegate(granter, recipient, target, AuthRequired::None);
        assert!(r.is_err());
        assert!(!fed.holds_cap(recipient, target));
    }
}
