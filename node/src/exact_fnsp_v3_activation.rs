//! Store-authenticated devnet activation for the exact FNSP-v3 receipt epoch.
//!
//! `ExactFnspV3ReceiptEpochV1::prepare` is structural: it does not prove the legacy tip is a
//! durable, executor-signed receipt or that the exact initial point is the store-reconstructed
//! prefix.  This module closes those obligations and returns an opaque activation which the
//! executor/frame join can consume.  The current devnet policy is the node executor's Ed25519
//! signature; it is intentionally not described as threshold finality.

use core::fmt;
use std::error::Error;

use dregg_persist::{
    CommittedExactFnspV3FrameHeadV1, PersistentStore, StoreAuthenticatedExactFnspV3ActivationV1,
    StoreError, UntrustedExactFnspV3ActivationV1,
};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{ExactFnspV3ReceiptEpochV1, Finality, TurnReceipt};
use dregg_types::sign;

/// Opaque proof that the runtime epoch is byte-identical to the sole authenticated store row.
pub(crate) struct StoreAuthorizedExactFnspV3Activation {
    epoch: ExactFnspV3ReceiptEpochV1,
    stored: StoreAuthenticatedExactFnspV3ActivationV1,
}

/// The store's sole current exact receipt predecessor.
///
/// `committed_head == None` is possible only before the first frame.  Once a durable frame exists,
/// callers cannot choose to restart from the activation or supply a different head.
pub(crate) struct StoreAuthorizedExactFnspV3Predecessor {
    activation: StoreAuthorizedExactFnspV3Activation,
    committed_head: Option<CommittedExactFnspV3FrameHeadV1>,
}

impl StoreAuthorizedExactFnspV3Predecessor {
    pub(crate) const fn activation(&self) -> &StoreAuthorizedExactFnspV3Activation {
        &self.activation
    }

    pub(crate) const fn committed_head(&self) -> Option<&CommittedExactFnspV3FrameHeadV1> {
        self.committed_head.as_ref()
    }
}

/// Load exactly one authenticated predecessor: activation before frame zero, committed head after.
pub(crate) fn exact_fnsp_v3_current_predecessor(
    store: &PersistentStore,
    cclerk: &AgentCipherclerk,
    epoch: ExactFnspV3ReceiptEpochV1,
    legacy_tip: &TurnReceipt,
) -> Result<StoreAuthorizedExactFnspV3Predecessor, ExactFnspV3ActivationError> {
    let activation = authorize_exact_fnsp_v3_activation(store, cclerk, epoch, legacy_tip)?;
    let committed_head = store
        .exact_fnsp_v3_committed_frame_head()
        .map_err(ExactFnspV3ActivationError::Store)?;
    if let Some(head) = committed_head.as_ref()
        && (head.epoch() != activation.stored().epoch()
            || head.activation_hash() != activation.stored().activation_hash()
            || head.federation_id() != activation.stored().federation_id()
            || head.agent() != activation.stored().agent())
    {
        return Err(ExactFnspV3ActivationError::StoredHeadMismatch);
    }
    Ok(StoreAuthorizedExactFnspV3Predecessor {
        activation,
        committed_head,
    })
}

impl StoreAuthorizedExactFnspV3Activation {
    pub(crate) const fn epoch(&self) -> &ExactFnspV3ReceiptEpochV1 {
        &self.epoch
    }

    pub(crate) const fn stored(&self) -> &StoreAuthenticatedExactFnspV3ActivationV1 {
        &self.stored
    }
}

/// Authenticate and persist-once the exact receipt flag day.
///
/// On first activation the supplied legacy tip must be the current durable receipt-log tail.  On
/// restart it may be historical, but its byte-exact row and executor signature must still exist.
fn authorize_exact_fnsp_v3_activation(
    store: &PersistentStore,
    cclerk: &AgentCipherclerk,
    epoch: ExactFnspV3ReceiptEpochV1,
    legacy_tip: &TurnReceipt,
) -> Result<StoreAuthorizedExactFnspV3Activation, ExactFnspV3ActivationError> {
    if legacy_tip.finality != Finality::Final
        || legacy_tip.receipt_hash() != epoch.legacy_tip_receipt_hash()
        || legacy_tip.post_state_hash != epoch.legacy_tip_outer_commit().to_bytes()
        || legacy_tip.federation_id != epoch.federation_id()
        || legacy_tip.agent != epoch.agent()
    {
        return Err(ExactFnspV3ActivationError::LegacyTipMismatch);
    }
    dregg_turn::verify_receipt_signature_with_keys(legacy_tip, &[cclerk.public_key().0])
        .map_err(|_| ExactFnspV3ActivationError::LegacyTipSignatureInvalid)?;

    let encoded_tip = postcard::to_stdvec(legacy_tip)
        .map_err(|error| ExactFnspV3ActivationError::ReceiptEncoding(error.to_string()))?;
    let durable_chain = store
        .load_receipt_chain()
        .map_err(ExactFnspV3ActivationError::Store)?;
    let tip_index = durable_chain
        .iter()
        .position(|encoded| encoded == &encoded_tip)
        .ok_or(ExactFnspV3ActivationError::LegacyTipNotDurable)?;

    let exact_initial = store
        .exact_fnsp_v3_state_head()
        .map_err(ExactFnspV3ActivationError::Store)?
        .ok_or(ExactFnspV3ActivationError::ExactStateUninitialized)?;
    if exact_initial.root() != epoch.exact_initial().root()
        || exact_initial.count() != epoch.exact_initial().count()
        || exact_initial.fns3() != epoch.exact_initial().fns3()
    {
        return Err(ExactFnspV3ActivationError::ExactInitialMismatch);
    }

    if let Some(stored) = store
        .exact_fnsp_v3_activation()
        .map_err(ExactFnspV3ActivationError::Store)?
    {
        validate_stored(&stored, cclerk, &epoch, exact_initial)?;
        return Ok(StoreAuthorizedExactFnspV3Activation { epoch, stored });
    }
    if tip_index + 1 != durable_chain.len() {
        return Err(ExactFnspV3ActivationError::LegacyTipNotTerminal);
    }

    let message = UntrustedExactFnspV3ActivationV1::signature_message(epoch.activation_hash());
    let signature = sign(&cclerk.gossip_signing_key(), &message);
    let candidate = UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
        epoch.epoch().get(),
        exact_initial,
        epoch.federation_id(),
        epoch.agent().0,
        epoch.legacy_tip_receipt_hash(),
        epoch.legacy_tip_outer_commit().to_bytes(),
        epoch.activation_hash(),
        cclerk.public_key().0,
        signature,
    )
    .map_err(ExactFnspV3ActivationError::Store)?;
    let stored = store
        .install_exact_fnsp_v3_activation(candidate)
        .map_err(ExactFnspV3ActivationError::Store)?;
    validate_stored(&stored, cclerk, &epoch, exact_initial)?;
    Ok(StoreAuthorizedExactFnspV3Activation { epoch, stored })
}

fn validate_stored(
    stored: &StoreAuthenticatedExactFnspV3ActivationV1,
    cclerk: &AgentCipherclerk,
    epoch: &ExactFnspV3ReceiptEpochV1,
    exact_initial: dregg_persist::ExactFnspV3StateHeadV1,
) -> Result<(), ExactFnspV3ActivationError> {
    if stored.epoch() != epoch.epoch().get()
        || stored.activation_hash() != epoch.activation_hash()
        || stored.federation_id() != epoch.federation_id()
        || stored.agent() != epoch.agent().0
        || stored.legacy_tip_receipt_hash() != epoch.legacy_tip_receipt_hash()
        || stored.legacy_tip_outer_commit() != epoch.legacy_tip_outer_commit().to_bytes()
        || stored.exact_initial() != exact_initial
        || stored.executor_public_key() != cclerk.public_key().0
    {
        return Err(ExactFnspV3ActivationError::StoredActivationMismatch);
    }
    Ok(())
}

#[derive(Debug)]
pub(crate) enum ExactFnspV3ActivationError {
    LegacyTipMismatch,
    LegacyTipSignatureInvalid,
    LegacyTipNotDurable,
    LegacyTipNotTerminal,
    ExactStateUninitialized,
    ExactInitialMismatch,
    StoredActivationMismatch,
    StoredHeadMismatch,
    ReceiptEncoding(String),
    Store(StoreError),
}

impl fmt::Display for ExactFnspV3ActivationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LegacyTipMismatch => {
                f.write_str("exact FNSP-v3 activation legacy tip/epoch mismatch")
            }
            Self::LegacyTipSignatureInvalid => {
                f.write_str("exact FNSP-v3 activation legacy tip signature invalid")
            }
            Self::LegacyTipNotDurable => {
                f.write_str("exact FNSP-v3 activation legacy tip is absent from durable receipts")
            }
            Self::LegacyTipNotTerminal => f.write_str(
                "exact FNSP-v3 first activation legacy tip is not the durable receipt tail",
            ),
            Self::ExactStateUninitialized => {
                f.write_str("exact FNSP-v3 activation exact state is uninitialized")
            }
            Self::ExactInitialMismatch => {
                f.write_str("exact FNSP-v3 activation exact initial prefix mismatch")
            }
            Self::StoredActivationMismatch => {
                f.write_str("runtime exact FNSP-v3 epoch differs from stored activation")
            }
            Self::StoredHeadMismatch => {
                f.write_str("stored exact FNSP-v3 head differs from stored activation")
            }
            Self::ReceiptEncoding(error) => {
                write!(
                    f,
                    "exact FNSP-v3 activation receipt encoding failed: {error}"
                )
            }
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
