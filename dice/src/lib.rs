//! # dregg-dice — verifiable randomness for the attested-dm game engine
//!
//! This crate is the minimal first slice of Phase 2 ("Non-grindable randomness")
//! of `docs/DESIGN-verifiable-game.md`. It provides the *derivation and
//! verification* machinery for game randomness, with the unpredictability source
//! itself behind a trait so a VRF/beacon backend drops in later.
//!
//! ## What it gives you
//!
//! - [`EventId::derive`] — a domain-separated binding of a draw to its full
//!   transition context: game, sequence, pre-state, action, purpose
//!   (`event_kind`), and `draw_count`. Distinct domain tags per hashed object
//!   prevent cross-protocol preimage collisions.
//! - [`RandomnessSource`] — a pluggable source: a producer ([`RandomnessSource::evidence`])
//!   and a pure verifier ([`RandomnessSource::seed`]) that re-derives the seed and
//!   checks the evidence. Implemented: [`CommitReveal`], [`Deterministic`],
//!   [`MockBeacon`], the real post-quantum [`ServerVrf`] (the one-time `pqvrf`
//!   LB-VRF), and [`Hybrid`] — a **genesis-committed LB-VRF key-chain** + a real
//!   verified **schedule-bound hash-chain beacon** ([`HashChainBeacon`]) with
//!   **timeout finalization**.
//! - [`DrawStream`] — an indexed XOF draw stream from a verified [`Seed`], with an
//!   **unbiased, reject-free** bounded mapping ([`DrawStream::draw_bounded`]).
//! - [`RandomnessRequest`] / [`RandomnessEvidence`] — serde-serializable
//!   structures mirroring the design, plus [`RandomnessRequest::commitment`], the
//!   receipt-shaped hash an engine stores before the result exists.
//!
//! ## Trust levels — read this before claiming anything
//!
//! **The seed-derivation and draw-stream verifier are correct regardless of
//! source.** Given a `Seed`, everyone reconstructs the identical draw stream, and
//! the transcript commitment binds `draw_count` and every draw. Grinding by
//! changing `draw_count`, `event_kind`, the action, or the pre-state is *always*
//! detectable, because all of those move the [`EventId`], hence the seed, hence
//! the transcript.
//!
//! **The unpredictability guarantee depends entirely on the source:**
//!
//! - [`Deterministic`] provides **no** unpredictability. Whoever knows the
//!   context knows every draw. It is for tests and reproducible offline play.
//! - [`CommitReveal`] prevents either party from *unilaterally choosing* the
//!   outcome (the server is bound to a pre-published commitment; the player's
//!   contribution is mixed in). **But commit-reveal does NOT prevent selective
//!   abort:** the last party to reveal learns the result first and can simply
//!   refuse to reveal on an unfavorable outcome, so the transition never lands.
//!   This crate deliberately does not describe commit-reveal as non-abortable.
//!   Closing the abort gap needs timeout finalization with a deterministic
//!   consequence (a follow-up) so a withheld reveal cannot silently reroll.
//! - [`MockBeacon`] folds in a beacon output but does **not** verify the beacon's
//!   signature or finality — it is a wiring/test stand-in, not a guarantee.
//! - [`ServerVrf`] is the real post-quantum **LB-VRF** (`pqvrf`, Esgin et al. Set I):
//!   the output is the unique VRF value for a `(key, input)` pair — a forged output
//!   or proof is rejected by `pqvrf::verify`, its uniqueness reducing to Module-SIS.
//!   This is the lattice replacement for the rejected classical ECVRF. The key is
//!   one-time (Set I); each event uses its own committed key epoch. Output
//!   pseudorandomness rests on MLWE (assumed).
//! - [`Hybrid`] (genesis-committed LB-VRF key-chain + delayed schedule-bound
//!   beacon + timeout finalization) is the recommended endpoint that closes
//!   unilateral reroll on *both* sides. The [`Beacon`] behind it is pluggable; the
//!   shipped, testable model is [`HashChainBeacon`], a forward-secure hash chain
//!   whose future rounds are unpredictable at commit (preimage resistance) and
//!   whose anchor is genesis-pinned. It is honestly *not* a threshold construction
//!   — it trusts a single operator. A real threshold **drand-BLS** beacon
//!   ([`BeaconKind::Drand`]) is the production path; its round verification is a BLS
//!   pairing check against the pinned group key, and wiring the live drand group
//!   key + round fetch is the one remaining gap for escape hatch #2 (the verifier
//!   fails closed on the `Drand` variant — see [`verify_beacon_round`]).
//!
//! ### The six non-grindability escape hatches, honestly
//!
//! The design names six things that make randomness non-grindable. With the
//! [`Hybrid`] source (genesis-committed LB-VRF key-chain + delayed beacon + timeout
//! finalization):
//!
//! | # | Escape hatch | Status |
//! |---|---|---|
//! | 1 | Server key bound at genesis | **Closed by [`Hybrid`]** — a Merkle root over per-epoch LB-VRF public keys is pinned into `game_binding` ([`Hybrid::genesis_binding`]); epoch = `seq`, and the verifier checks the eval key's membership at leaf `seq` ([`verify_epoch_membership`]). A per-turn key swap fails. ([`ServerVrf`] alone uses the simpler per-event committed key.) |
//! | 2 | Beacon round from a fixed schedule | **Closed at the schedule layer** — the round is a deterministic function of `seq` ([`BeaconSchedule::expected_round`]), so no favourable-round picking; **beacon-signature caveat:** the shipped [`HashChainBeacon`] verifies rounds against a genesis-pinned anchor, but a real threshold **drand-BLS** beacon is the remaining gap |
//! | 3 | Player action bound before the beacon deadline | **Closed** — `action_hash` is bound into the `EventId` before the seed exists |
//! | 4 | VRF one-output-per-input | **Closed by [`ServerVrf`]/[`Hybrid`]** — the LB-VRF output is the *unique* value for `(key, input)`; a forged output/proof fails `pqvrf::verify` (uniqueness reduces to Module-SIS) |
//! | 5 | Timeout finalization so withholding can't reroll | **Closed by [`Hybrid`]** — past the deadline anyone finalizes from the beacon alone with a recorded `ServerMissed` fault; the seed is determined, not chooseable, so selective abort yields no reroll and no alternative outcome |
//! | 6 | `event_kind` + `draw_count` bound before the seed exists | **Closed** — both are in the `EventId`; the transcript commitment enforces them |
//!
//! Honest summary: **[`CommitReveal`] closes 3 and 6** and prevents unilateral
//! *choice* but leaves selective abort open. **[`ServerVrf`] closes 4.**
//! **[`Hybrid`] additionally closes 1 and 5** outright and closes **2** at the
//! schedule layer, with the one honest caveat that the shipped beacon is a
//! forward-secure hash chain (single operator), not a threshold drand-BLS beacon —
//! that wiring is the remaining production gap. Pseudorandomness of the LB-VRF
//! output rests on MLWE (assumed).
//!
//! ## Follow-ups (out of scope here)
//!
//! - `attested-dm` wiring of the [`Hybrid`] source into the transition-receipt
//!   verifier (its `EvidenceKind::Hybrid` dispatch arm) — a parallel lane.
//! - A real **drand-BLS** [`Beacon`] impl for [`BeaconKind::Drand`] (a BLS pairing
//!   check against the live drand group public key, plus round fetch) — the one
//!   remaining gap for escape hatch #2.
//! - Enforcing the reveal-deadline-before-beacon-maturity ordering at the receipt
//!   layer (this crate encodes the round as a future, schedule-bound round and
//!   records the `ServerMissed` fault; the wall-clock deadline is a receipt-layer
//!   obligation).

mod util;

pub mod draw;
pub mod error;
pub mod event;
pub mod request;
pub mod source;

pub use draw::{DOMAIN_DRAW, DOMAIN_TRANSCRIPT, DrawStream, Seed};
pub use error::{DrawError, VerifyError};
pub use event::{DOMAIN_EVENT_ID, EventId};
pub use request::{
    BeaconEvidence, BeaconKind, BeaconParams, BeaconSchedule, DERIVATION_VERSION,
    DOMAIN_REQUEST_COMMITMENT, EvidenceKind, Finalization, RandomnessEvidence, RandomnessRequest,
};
pub use source::{
    Beacon, CommitReveal, DOMAIN_BEACON_CHAIN, DOMAIN_COMMIT, DOMAIN_HYBRID_GENESIS,
    DOMAIN_HYBRID_MIX, DOMAIN_KEYCHAIN_LEAF, DOMAIN_KEYCHAIN_NODE, DOMAIN_LB_VRF_KEY_COMMITMENT,
    DOMAIN_SEED, Deterministic, FinalizeMode, HashChainBeacon, Hybrid, KeyChain, MockBeacon,
    RandomnessSource, ServerVrf, VrfEvalError, verify_beacon_round, verify_epoch_membership,
};
