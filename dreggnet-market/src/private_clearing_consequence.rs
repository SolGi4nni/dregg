//! Reusable game-consequence gate for a verified private Dark Bazaar clearing.
//!
//! A [`PrivateClearingReceipt`] is not accepted by itself. The gate corroborates
//! every public field against the still-live, authoritatively settled
//! [`DarkBazaarSession`], pins the exact verified statement, winner and settlement
//! turn plus a deployment-selected target cell and opaque consequence tag, then
//! derives a one-shot consequence id from that complete context. A quest, raid,
//! unlock, dungeon choice, or other engine consumer supplies one real cap-bounded
//! turn as a closure.
//!
//! Replay is consumed only after the game turn returns a shape-valid committed
//! receipt. Target mismatch, forged source receipt, or executor refusal therefore
//! changes neither replay state nor game state. If a process dies after the game
//! commit but before replay persistence, [`PrivateClearingConsequenceGate::recover_committed_game_turn`]
//! re-observes the target engine's committed receipt/state and consumes the same
//! derived consequence id without dispatching the turn again.
//!
//! This is deliberately a process-local consumer, not a transferable receipt
//! verifier. Its input receipt was produced by `settle_private_verified`; the
//! settled session is the independent authority that prevents a caller from
//! constructing a lookalike receipt and choosing another winner or price. A
//! durable deployment should persist the consumed consequence ids. The recovery
//! observer is engine-specific and must return a receipt only after checking the
//! configured target/tag's committed state; the generic gate cannot infer a
//! quest's state semantics from opaque cell hashes.

use std::collections::BTreeSet;

use dregg_app_framework::{CellId, TurnReceipt};
use dregg_circuit_prove::dark_bazaar_private::{self, PublicStatement};
use dreggnet_offerings::DreggIdentity;

use crate::DarkBazaarSession;
use crate::private_clearing::PrivateClearingReceipt;

const CONSEQUENCE_DOMAIN: &str = "dreggnet-market/private-clearing-consequence/v1";
const CONSEQUENCE_TAG_DOMAIN: &str = "dreggnet-market/private-clearing-consequence-tag/v1";

/// Deployment-selected identity of a game mechanic authorized by a private
/// clearing. A target cell can expose several distinct consequences without
/// sharing a replay namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrivateClearingConsequenceTag(pub [u8; 32]);

impl PrivateClearingConsequenceTag {
    /// Derive a stable tag from a product-owned label such as
    /// `wardens-keep/crown/red/v1` or `raid/frost-gate/unlock/v1`.
    pub fn from_label(label: &str) -> Self {
        Self(
            *blake3::Hasher::new_derive_key(CONSEQUENCE_TAG_DOMAIN)
                .update(&(label.len() as u64).to_be_bytes())
                .update(label.as_bytes())
                .finalize()
                .as_bytes(),
        )
    }
}

/// Complete binding for a committed cross-game consequence. `game_turn_hash`
/// is the consuming engine's real executor turn, not a synthetic marker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateClearingConsequenceReceipt {
    pub consequence_id: [u8; 32],
    pub consequence_tag: PrivateClearingConsequenceTag,
    pub private_session: u32,
    pub private_root: [u32; 8],
    pub winner: DreggIdentity,
    pub price: u32,
    pub target_cell: CellId,
    pub settlement_turn_hash: [u8; 32],
    pub game_turn_hash: [u8; 32],
    pub disposition: PrivateClearingConsequenceDisposition,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateClearingConsequenceDisposition {
    Committed,
    Recovered,
}

/// Durable target-engine observation for the narrow post-game/pre-replay crash
/// window. A host records this tuple in, or reconstructs it from, the game
/// engine's own committed receipt/state index. Recovery checks every routing
/// field before accepting the enclosed turn receipt.
#[derive(Clone, Debug)]
pub struct PrivateClearingCommittedObservation {
    consequence_id: [u8; 32],
    target_cell: CellId,
    consequence_tag: PrivateClearingConsequenceTag,
    game_receipt: TurnReceipt,
}

impl PrivateClearingCommittedObservation {
    pub fn new(
        consequence_id: [u8; 32],
        target_cell: CellId,
        consequence_tag: PrivateClearingConsequenceTag,
        game_receipt: TurnReceipt,
    ) -> Self {
        Self {
            consequence_id,
            target_cell,
            consequence_tag,
            game_receipt,
        }
    }

    pub const fn consequence_id(&self) -> [u8; 32] {
        self.consequence_id
    }

    pub const fn target_cell(&self) -> CellId {
        self.target_cell
    }

    pub const fn consequence_tag(&self) -> PrivateClearingConsequenceTag {
        self.consequence_tag
    }

    pub fn game_receipt(&self) -> &TurnReceipt {
        &self.game_receipt
    }
}

/// Exact source capability pinned from the receipt returned by
/// `settle_private_verified`. Keeping the root and settlement turn here is
/// load-bearing: if either were accepted from each application, a caller could
/// alter it to derive a fresh consequence id and bypass replay protection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateClearingConsequenceSource {
    statement: PublicStatement,
    winner: DreggIdentity,
    settlement_turn_hash: [u8; 32],
}

impl PrivateClearingConsequenceSource {
    /// Pin the exact private result immediately after authoritative settlement.
    /// The gate still corroborates it against the settled session on every use.
    pub fn from_verified_receipt(
        receipt: &PrivateClearingReceipt,
    ) -> Result<Self, PrivateClearingConsequenceError> {
        if receipt.statement.rule != dark_bazaar_private::RULE_ID {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong private rule",
            ));
        }
        if receipt.statement.v_star != 1 {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong clearing volume",
            ));
        }
        if receipt.settlement_turn.turn_hash == [0; 32] {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "zero settlement turn hash",
            ));
        }
        Ok(Self {
            statement: receipt.statement,
            winner: receipt.winner.clone(),
            settlement_turn_hash: receipt.settlement_turn.turn_hash,
        })
    }

    pub const fn statement(&self) -> PublicStatement {
        self.statement
    }

    pub fn winner(&self) -> &DreggIdentity {
        &self.winner
    }

    pub const fn settlement_turn_hash(&self) -> [u8; 32] {
        self.settlement_turn_hash
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateClearingConsequenceError {
    TargetMismatch,
    MarketNotSettled,
    ReceiptMismatch(&'static str),
    AlreadyConsumed,
    GameRefused(String),
    InvalidGameTurn(&'static str),
    ReplayCommitInterrupted(String),
    RecoveryObservation(String),
    RecoveryNotFound,
}

impl std::fmt::Display for PrivateClearingConsequenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TargetMismatch => write!(f, "private clearing consequence targets another cell"),
            Self::MarketNotSettled => {
                write!(f, "private clearing consequence needs a settled market")
            }
            Self::ReceiptMismatch(reason) => {
                write!(f, "private clearing consequence receipt mismatch: {reason}")
            }
            Self::AlreadyConsumed => write!(f, "private clearing consequence was already consumed"),
            Self::GameRefused(reason) => write!(f, "private clearing game turn refused: {reason}"),
            Self::InvalidGameTurn(reason) => {
                write!(f, "private clearing game turn is invalid: {reason}")
            }
            Self::ReplayCommitInterrupted(reason) => write!(
                f,
                "game turn committed before consequence replay state persisted: {reason}"
            ),
            Self::RecoveryObservation(reason) => {
                write!(f, "private clearing consequence recovery failed: {reason}")
            }
            Self::RecoveryNotFound => write!(
                f,
                "private clearing consequence was not observed in target game state"
            ),
        }
    }
}

impl std::error::Error for PrivateClearingConsequenceError {}

/// Deployment policy and process-local replay state for one receipt-bound game
/// consequence. Instantiate a separate gate per configured target/tag pair.
pub struct PrivateClearingConsequenceGate {
    target_cell: CellId,
    source: PrivateClearingConsequenceSource,
    consequence_tag: PrivateClearingConsequenceTag,
    consumed: BTreeSet<[u8; 32]>,
}

impl PrivateClearingConsequenceGate {
    pub fn new(
        target_cell: CellId,
        source: PrivateClearingConsequenceSource,
        consequence_tag: PrivateClearingConsequenceTag,
    ) -> Self {
        Self {
            target_cell,
            source,
            consequence_tag,
            consumed: BTreeSet::new(),
        }
    }

    pub const fn target_cell(&self) -> CellId {
        self.target_cell
    }

    pub const fn consequence_tag(&self) -> PrivateClearingConsequenceTag {
        self.consequence_tag
    }

    pub fn source(&self) -> &PrivateClearingConsequenceSource {
        &self.source
    }

    pub fn consumed_count(&self) -> usize {
        self.consumed.len()
    }

    /// Restore previously committed consequence ids before accepting work.
    /// Durable hosts persist `receipt.consequence_id` after a successful turn.
    pub fn restore_consumed<I>(&mut self, ids: I)
    where
        I: IntoIterator<Item = [u8; 32]>,
    {
        self.consumed.extend(ids);
    }

    /// Stable ordered replay projection suitable for a small durable sidecar.
    pub fn consumed_ids(&self) -> impl ExactSizeIterator<Item = &[u8; 32]> {
        self.consumed.iter()
    }

    /// Corroborate the proof-produced receipt against authoritative settled
    /// market state, then run exactly one caller-supplied real game turn.
    ///
    /// Replay is recorded only after a nonzero committed game turn returns. A
    /// target mismatch, forged receipt, or executor refusal therefore leaves the
    /// one-shot authorization available and burns no ghost consequence.
    pub fn apply_game_turn<F>(
        &mut self,
        session: &DarkBazaarSession,
        receipt: &PrivateClearingReceipt,
        target_cell: CellId,
        game_turn: F,
    ) -> Result<PrivateClearingConsequenceReceipt, PrivateClearingConsequenceError>
    where
        F: FnOnce() -> Result<TurnReceipt, String>,
    {
        self.apply_game_turn_with_commit_hook(session, receipt, target_cell, game_turn, |_, _| {
            Ok(())
        })
    }

    /// Hook-bearing form for durable/fault-injection integrations. The hook runs
    /// after the target game turn committed and passed receipt-shape checks, but
    /// before the in-memory replay set advances. A hook error deliberately leaves
    /// the id unconsumed so restart recovery can re-observe the game commit.
    pub fn apply_game_turn_with_commit_hook<F, H>(
        &mut self,
        session: &DarkBazaarSession,
        receipt: &PrivateClearingReceipt,
        target_cell: CellId,
        game_turn: F,
        after_game_commit: H,
    ) -> Result<PrivateClearingConsequenceReceipt, PrivateClearingConsequenceError>
    where
        F: FnOnce() -> Result<TurnReceipt, String>,
        H: FnOnce([u8; 32], &TurnReceipt) -> Result<(), String>,
    {
        if target_cell != self.target_cell {
            return Err(PrivateClearingConsequenceError::TargetMismatch);
        }
        self.validate(session, receipt)?;
        let consequence_id = self.consequence_id(receipt);
        if self.consumed.contains(&consequence_id) {
            return Err(PrivateClearingConsequenceError::AlreadyConsumed);
        }

        let game_receipt = game_turn().map_err(PrivateClearingConsequenceError::GameRefused)?;
        Self::validate_game_receipt(&game_receipt)?;
        after_game_commit(consequence_id, &game_receipt)
            .map_err(PrivateClearingConsequenceError::ReplayCommitInterrupted)?;
        let inserted = self.consumed.insert(consequence_id);
        debug_assert!(inserted, "replay was checked immediately before insertion");

        Ok(self.finish_receipt(
            receipt,
            target_cell,
            consequence_id,
            &game_receipt,
            PrivateClearingConsequenceDisposition::Committed,
        ))
    }

    /// Recover the precise crash window after a target turn committed but before
    /// consequence replay persistence. `observe` receives the independently
    /// derived id, pinned target, and tag. It must query the target engine's
    /// durable state/receipt history and return `Some(receipt)` only when that
    /// exact consequence is already committed. The game turn is never dispatched
    /// by this method.
    pub fn recover_committed_game_turn<O>(
        &mut self,
        session: &DarkBazaarSession,
        receipt: &PrivateClearingReceipt,
        target_cell: CellId,
        observe: O,
    ) -> Result<PrivateClearingConsequenceReceipt, PrivateClearingConsequenceError>
    where
        O: FnOnce(
            [u8; 32],
            CellId,
            PrivateClearingConsequenceTag,
        ) -> Result<Option<PrivateClearingCommittedObservation>, String>,
    {
        if target_cell != self.target_cell {
            return Err(PrivateClearingConsequenceError::TargetMismatch);
        }
        self.validate(session, receipt)?;
        let consequence_id = self.consequence_id(receipt);
        if self.consumed.contains(&consequence_id) {
            return Err(PrivateClearingConsequenceError::AlreadyConsumed);
        }
        let Some(observation) = observe(consequence_id, self.target_cell, self.consequence_tag)
            .map_err(PrivateClearingConsequenceError::RecoveryObservation)?
        else {
            return Err(PrivateClearingConsequenceError::RecoveryNotFound);
        };
        if observation.consequence_id != consequence_id
            || observation.target_cell != self.target_cell
            || observation.consequence_tag != self.consequence_tag
        {
            return Err(PrivateClearingConsequenceError::RecoveryObservation(
                "observation routing does not match the derived consequence".to_owned(),
            ));
        }
        Self::validate_game_receipt(&observation.game_receipt)?;
        let inserted = self.consumed.insert(consequence_id);
        debug_assert!(inserted, "replay was checked immediately before recovery");
        Ok(self.finish_receipt(
            receipt,
            target_cell,
            consequence_id,
            &observation.game_receipt,
            PrivateClearingConsequenceDisposition::Recovered,
        ))
    }

    fn finish_receipt(
        &self,
        receipt: &PrivateClearingReceipt,
        target_cell: CellId,
        consequence_id: [u8; 32],
        game_receipt: &TurnReceipt,
        disposition: PrivateClearingConsequenceDisposition,
    ) -> PrivateClearingConsequenceReceipt {
        PrivateClearingConsequenceReceipt {
            consequence_id,
            consequence_tag: self.consequence_tag,
            private_session: receipt.statement.session,
            private_root: receipt.statement.order_root,
            winner: receipt.winner.clone(),
            price: receipt.price(),
            target_cell,
            settlement_turn_hash: receipt.settlement_turn.turn_hash,
            game_turn_hash: game_receipt.turn_hash,
            disposition,
        }
    }

    fn validate_game_receipt(
        game_receipt: &TurnReceipt,
    ) -> Result<(), PrivateClearingConsequenceError> {
        if game_receipt.turn_hash == [0; 32] {
            return Err(PrivateClearingConsequenceError::InvalidGameTurn(
                "zero turn hash",
            ));
        }
        if game_receipt.action_count == 0 {
            return Err(PrivateClearingConsequenceError::InvalidGameTurn(
                "empty action set",
            ));
        }
        if game_receipt.pre_state_hash == game_receipt.post_state_hash {
            return Err(PrivateClearingConsequenceError::InvalidGameTurn(
                "state did not change",
            ));
        }
        Ok(())
    }

    fn validate(
        &self,
        session: &DarkBazaarSession,
        receipt: &PrivateClearingReceipt,
    ) -> Result<(), PrivateClearingConsequenceError> {
        if !session.is_settled() {
            return Err(PrivateClearingConsequenceError::MarketNotSettled);
        }
        if receipt.statement != self.source.statement
            || receipt.winner != self.source.winner
            || receipt.settlement_turn.turn_hash != self.source.settlement_turn_hash
        {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "receipt differs from pinned verified source",
            ));
        }
        if receipt.statement.rule != dark_bazaar_private::RULE_ID {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong private rule",
            ));
        }
        if receipt.statement.session != session.private_proof_session() {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong private session",
            ));
        }
        if receipt.volume() != 1 {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong clearing volume",
            ));
        }
        if session.winning_actor() != Some(&self.source.winner)
            || session.winning_actor() != Some(&receipt.winner)
        {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong winner",
            ));
        }
        let live_price = session
            .clearing()
            .and_then(|clearing| u32::try_from(clearing.price()).ok());
        if live_price != Some(self.source.statement.p_star) {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "wrong price",
            ));
        }
        if receipt.settlement_turn.turn_hash == [0; 32] {
            return Err(PrivateClearingConsequenceError::ReceiptMismatch(
                "zero settlement turn hash",
            ));
        }
        Ok(())
    }

    fn consequence_id(&self, receipt: &PrivateClearingReceipt) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(CONSEQUENCE_DOMAIN);
        hasher.update(&self.target_cell.0);
        hasher.update(&self.consequence_tag.0);
        hasher.update(&receipt.statement.session.to_be_bytes());
        hasher.update(&receipt.statement.rule.to_be_bytes());
        for lane in receipt.statement.order_root {
            hasher.update(&lane.to_be_bytes());
        }
        hasher.update(&receipt.statement.p_star.to_be_bytes());
        hasher.update(&receipt.statement.v_star.to_be_bytes());
        hasher.update(&(receipt.winner.0.len() as u64).to_be_bytes());
        hasher.update(receipt.winner.0.as_bytes());
        hasher.update(&receipt.settlement_turn.turn_hash);
        *hasher.finalize().as_bytes()
    }
}
