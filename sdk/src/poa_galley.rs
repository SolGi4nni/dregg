//! Path of Angels Galley player-command transport.
//!
//! The canonical command vocabulary, event classifier, turn-shape decoder,
//! signer binding, and client scaffold live in `dregg-turn`, below this SDK.
//! Keeping that authority below the client layer lets persistence/finality code
//! classify the exact same carrier without acquiring an SDK dependency.  This
//! module remains the source-compatible SDK surface and owns only the HTTP route
//! advertised to clients.
//!
//! The server issues an opaque action token bound to the deployment, daily,
//! predecessor head, next sequence, allowed action constraints, and expiry.
//! Player identity is derived only from the verified outer `SignedTurn`; holder
//! sponsorship carries one short-lived capability-receipt id.  The node must
//! consume those capabilities atomically with an accepted event.

/// Emerging node route serving the Galley projection and opaque action tokens.
pub const GALLEY_API_PATH_V1: &str = "/node/api/poa/galley/v1";

pub use dregg_turn::poa_galley_carrier::{
    GALLEY_COMMAND_METHOD_V1, GALLEY_COMMAND_TOPIC_V1, GalleyActionToken, GalleyCarrierError,
    GalleyCommandError, GalleyEventRoute, GalleyPlayerCommandV1, HOLDER_SPONSORSHIP_TAG_V1,
    HolderCapabilityReceiptId, OPEN_MAINTENANCE_TAG_V1, PERFORM_TAG_V1, PUBLIC_VOTE_TAG_V1,
    PublicVoteChoice, VISIT_COMMONS_TAG_V1, classify_galley_event,
    command_from_exact_galley_signed_turn, command_from_exact_galley_turn, galley_command_event,
    galley_player_cell, galley_player_command_turn,
};
