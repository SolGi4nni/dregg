//! Store-authenticated devnet activation and predecessor authority for exact FNSP-v3.
//!
//! The exact accumulator and exact-frame chain are federation-global.  Ordinary receipts remain
//! per actor and may interleave freely.  This module captures both coordinates without conflating
//! them: one store-authenticated global exact predecessor plus the current actor's independently
//! indexed receipt predecessor.

use core::fmt;
use std::error::Error;

use dregg_cell::CellId;
use dregg_persist::{
    CommittedExactFnspV3FrameHeadV1, ExactFnspV3StateHeadV1, PersistentStore,
    StoreAuthenticatedExactFnspV3ActivationV1, StoreError, UntrustedExactFnspV3ActivationV1,
};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::ExactFnspV3ReceiptEpochV1;
use dregg_types::{PublicKey, Signature, SigningKey, sign, verify};

/// Narrow owned signing authority which may safely move into off-lock exact proof/execution work.
///
/// This deliberately does not clone or expose the full cipherclerk, its receipt maps, or any other
/// node state.  Capture happens under the node-state lock; frame signing later proves the same key
/// which the durable activation pins.
pub(crate) struct ExactFnspV3ExecutorSignerAuthority {
    signing_key: SigningKey,
    public_key: PublicKey,
}

impl ExactFnspV3ExecutorSignerAuthority {
    pub(crate) fn capture(cclerk: &AgentCipherclerk) -> Self {
        Self {
            signing_key: cclerk.gossip_signing_key(),
            public_key: cclerk.public_key(),
        }
    }

    pub(crate) const fn public_key(&self) -> PublicKey {
        self.public_key
    }

    pub(crate) fn sign(&self, message: &[u8]) -> Signature {
        sign(&self.signing_key, message)
    }

    pub(crate) fn sign_and_self_verify(
        &self,
        message: &[u8],
    ) -> Result<Signature, ExactFnspV3ActivationError> {
        let signature = self.sign(message);
        if !verify(&self.public_key, message, &signature) {
            return Err(ExactFnspV3ActivationError::ExecutorSignatureSelfCheckFailed);
        }
        Ok(signature)
    }
}

/// Opaque proof that the runtime epoch is byte-identical to the sole authenticated store row.
pub(crate) struct StoreAuthorizedExactFnspV3Activation {
    epoch: ExactFnspV3ReceiptEpochV1,
    stored: StoreAuthenticatedExactFnspV3ActivationV1,
}

impl StoreAuthorizedExactFnspV3Activation {
    pub(crate) const fn epoch(&self) -> &ExactFnspV3ReceiptEpochV1 {
        &self.epoch
    }

    pub(crate) const fn stored(&self) -> &StoreAuthenticatedExactFnspV3ActivationV1 {
        &self.stored
    }
}

/// The sole global exact predecessor and this turn actor's independent receipt predecessor.
///
/// `committed_head == None` is possible only before the first exact frame.  The player receipt
/// predecessor may be absent for a new actor even when many exact frames already exist.
pub(crate) struct StoreAuthorizedExactFnspV3Predecessor {
    activation: StoreAuthorizedExactFnspV3Activation,
    committed_head: Option<CommittedExactFnspV3FrameHeadV1>,
    receipt_log_index: u64,
    player_predecessor_receipt_index: Option<u64>,
    player_predecessor_receipt_hash: Option<[u8; 32]>,
    actor: CellId,
}

impl StoreAuthorizedExactFnspV3Predecessor {
    pub(crate) const fn activation(&self) -> &StoreAuthorizedExactFnspV3Activation {
        &self.activation
    }

    pub(crate) const fn committed_head(&self) -> Option<&CommittedExactFnspV3FrameHeadV1> {
        self.committed_head.as_ref()
    }

    pub(crate) const fn receipt_log_index(&self) -> u64 {
        self.receipt_log_index
    }

    pub(crate) const fn player_predecessor_receipt_index(&self) -> Option<u64> {
        self.player_predecessor_receipt_index
    }

    pub(crate) const fn player_predecessor_receipt_hash(&self) -> Option<[u8; 32]> {
        self.player_predecessor_receipt_hash
    }

    pub(crate) const fn actor(&self) -> CellId {
        self.actor
    }
}

/// Load the global exact predecessor and the selected actor's current full-receipt predecessor.
///
/// This must run while the caller holds the node-state lock: the cipherclerk's O(1) per-actor head
/// map and the durable receipt cursor are captured as one pre-execution staleness key.  Persistence
/// independently proves both rows again inside the later atomic writer.
pub(crate) fn exact_fnsp_v3_current_predecessor(
    store: &PersistentStore,
    cclerk: &AgentCipherclerk,
    epoch: ExactFnspV3ReceiptEpochV1,
    actor: CellId,
) -> Result<StoreAuthorizedExactFnspV3Predecessor, ExactFnspV3ActivationError> {
    let signer = ExactFnspV3ExecutorSignerAuthority::capture(cclerk);
    let activation = authorize_exact_fnsp_v3_activation(store, &signer, epoch)?;
    let current_exact = store
        .exact_fnsp_v3_state_head()
        .map_err(ExactFnspV3ActivationError::Store)?
        .ok_or(ExactFnspV3ActivationError::ExactStateUninitialized)?;
    let committed_head = store
        .exact_fnsp_v3_committed_frame_head()
        .map_err(ExactFnspV3ActivationError::Store)?;
    if let Some(head) = committed_head.as_ref()
        && (head.epoch() != activation.stored().epoch()
            || head.activation_hash() != activation.stored().activation_hash()
            || head.federation_id() != activation.stored().federation_id())
    {
        return Err(ExactFnspV3ActivationError::StoredHeadMismatch);
    }
    validate_current_exact_predecessor(
        current_exact,
        activation.stored().exact_initial(),
        committed_head.as_ref().map(|head| head.exact_after()),
    )?;

    let (receipt_log_index, _) = store
        .receipt_chain_head()
        .map_err(ExactFnspV3ActivationError::Store)?;
    let player_predecessor_receipt_index = cclerk.agent_receipt_head_log_index(&actor);
    let player_predecessor_receipt_hash = cclerk.agent_receipt_head_hash(&actor);
    if player_predecessor_receipt_index.is_some() != player_predecessor_receipt_hash.is_some()
        || player_predecessor_receipt_index.is_some_and(|index| index >= receipt_log_index)
    {
        return Err(ExactFnspV3ActivationError::PlayerReceiptCoordinateMismatch);
    }

    Ok(StoreAuthorizedExactFnspV3Predecessor {
        activation,
        committed_head,
        receipt_log_index,
        player_predecessor_receipt_index,
        player_predecessor_receipt_hash,
        actor,
    })
}

fn validate_current_exact_predecessor(
    current: ExactFnspV3StateHeadV1,
    activation_initial: ExactFnspV3StateHeadV1,
    committed_after: Option<ExactFnspV3StateHeadV1>,
) -> Result<(), ExactFnspV3ActivationError> {
    if current != committed_after.unwrap_or(activation_initial) {
        return Err(ExactFnspV3ActivationError::ExactCurrentHeadMismatch);
    }
    Ok(())
}

/// Authenticate and persist-once the federation-global exact receipt flag day.
fn authorize_exact_fnsp_v3_activation(
    store: &PersistentStore,
    signer: &ExactFnspV3ExecutorSignerAuthority,
    epoch: ExactFnspV3ReceiptEpochV1,
) -> Result<StoreAuthorizedExactFnspV3Activation, ExactFnspV3ActivationError> {
    if epoch.executor_public_key() != signer.public_key().0 {
        return Err(ExactFnspV3ActivationError::ExecutorKeyMismatch);
    }
    let current_exact = store
        .exact_fnsp_v3_state_head()
        .map_err(ExactFnspV3ActivationError::Store)?
        .ok_or(ExactFnspV3ActivationError::ExactStateUninitialized)?;

    if let Some(stored) = store
        .exact_fnsp_v3_activation()
        .map_err(ExactFnspV3ActivationError::Store)?
    {
        validate_stored(&stored, signer, &epoch)?;
        return Ok(StoreAuthorizedExactFnspV3Activation { epoch, stored });
    }
    if !same_exact_state(current_exact, epoch.exact_initial()) {
        return Err(ExactFnspV3ActivationError::ExactInitialMismatch);
    }
    let message = UntrustedExactFnspV3ActivationV1::signature_message(epoch.activation_hash());
    let signature = signer.sign_and_self_verify(&message)?;
    let candidate = UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
        epoch.epoch().get(),
        current_exact,
        epoch.federation_id(),
        epoch.receipt_cutover_next_index(),
        epoch.receipt_cutover_tail_hash(),
        epoch.activation_hash(),
        signer.public_key().0,
        signature,
    )
    .map_err(ExactFnspV3ActivationError::Store)?;
    let stored = store
        .install_exact_fnsp_v3_activation(candidate)
        .map_err(ExactFnspV3ActivationError::Store)?;
    validate_stored(&stored, signer, &epoch)?;
    Ok(StoreAuthorizedExactFnspV3Activation { epoch, stored })
}

fn same_exact_state(
    stored: ExactFnspV3StateHeadV1,
    runtime: dregg_turn::ExactFnspV3StatePoint,
) -> bool {
    stored.root() == runtime.root()
        && stored.count() == runtime.count()
        && stored.fns3() == runtime.fns3()
}

fn validate_stored(
    stored: &StoreAuthenticatedExactFnspV3ActivationV1,
    signer: &ExactFnspV3ExecutorSignerAuthority,
    epoch: &ExactFnspV3ReceiptEpochV1,
) -> Result<(), ExactFnspV3ActivationError> {
    if stored.epoch() != epoch.epoch().get()
        || stored.activation_hash() != epoch.activation_hash()
        || stored.federation_id() != epoch.federation_id()
        || stored.receipt_cutover_next_index() != epoch.receipt_cutover_next_index()
        || stored.receipt_cutover_tail_hash() != epoch.receipt_cutover_tail_hash()
        || !same_exact_state(stored.exact_initial(), epoch.exact_initial())
        || stored.executor_public_key() != signer.public_key().0
    {
        return Err(ExactFnspV3ActivationError::StoredActivationMismatch);
    }
    Ok(())
}

#[derive(Debug)]
pub(crate) enum ExactFnspV3ActivationError {
    ExactStateUninitialized,
    ExactInitialMismatch,
    ExactCurrentHeadMismatch,
    ExecutorKeyMismatch,
    ExecutorSignatureSelfCheckFailed,
    StoredActivationMismatch,
    StoredHeadMismatch,
    PlayerReceiptCoordinateMismatch,
    Store(StoreError),
}

impl fmt::Display for ExactFnspV3ActivationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExactStateUninitialized => {
                f.write_str("exact FNSP-v3 activation exact state is uninitialized")
            }
            Self::ExactInitialMismatch => {
                f.write_str("exact FNSP-v3 activation exact initial prefix mismatch")
            }
            Self::ExactCurrentHeadMismatch => f.write_str(
                "exact FNSP-v3 current exact state disagrees with its global durable predecessor",
            ),
            Self::ExecutorKeyMismatch => {
                f.write_str("runtime exact FNSP-v3 epoch names a different executor key")
            }
            Self::ExecutorSignatureSelfCheckFailed => {
                f.write_str("exact FNSP-v3 executor signature failed self-verification")
            }
            Self::StoredActivationMismatch => {
                f.write_str("runtime exact FNSP-v3 epoch differs from stored activation")
            }
            Self::StoredHeadMismatch => {
                f.write_str("stored exact FNSP-v3 head differs from stored global activation")
            }
            Self::PlayerReceiptCoordinateMismatch => f.write_str(
                "exact FNSP-v3 player receipt head index/hash disagree with durable log cursor",
            ),
            Self::Store(error) => write!(f, "exact FNSP-v3 activation store refused: {error}"),
        }
    }
}

impl Error for ExactFnspV3ActivationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Store(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn post_frame_restart_uses_committed_after_not_activation_initial() {
        let store = PersistentStore::open_in_memory().expect("store");
        let initial = store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("initial");
        let after = store
            .prepare_exact_fnsp_v3_append([0xA1; 32], 1)
            .expect("successor")
            .successor();

        assert!(validate_current_exact_predecessor(after, initial, Some(after)).is_ok());
        assert!(
            validate_current_exact_predecessor(initial, initial, Some(after)).is_err(),
            "a corrupt rollback behind the committed frame must fail closed"
        );
        assert!(
            validate_current_exact_predecessor(after, initial, None).is_err(),
            "an advanced exact head without a committed frame must fail closed"
        );
    }
}
