//! Path of Angels Signal transport, finality, and replay adapter.
//!
//! This module classifies the reserved SDK event, constructs the complete
//! canonical Lean wire from a host-only context, invokes the Lean evaluator,
//! and strictly parses its canonical reply. Live evaluation remains
//! non-authoritative until the finalized-turn weld commits it. Restart audit is
//! deliberately stronger: it reloads each finalized carrier, reconstructs the
//! exact judge input, re-invokes native Lean, and derives the complete successor
//! projection without trusting the stored successor. Consequently a successful
//! [`evaluate_signal_claim`] alone is still an evaluated candidate, never a
//! finalized receipt.

use std::collections::BTreeMap;
use std::fmt;

use dregg_blocklace::finality::Payload;
use dregg_sdk::poa_signal::{
    SIGNAL_BAND_MAX, SignalClaimError, SignalClaimV1, SignalCode, SignalEventRoute,
    classify_signal_event,
};
use dregg_turn::Effect;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

const SIGNAL_INPUT_FORMAT: &str = "POA-SIGNAL-IN-1";
const SIGNAL_OUTPUT_FORMAT: &str = "POA-SIGNAL-OUT-1";
const LEAN_SIGNAL_WIRE_BYTES: usize = 16 * 1024 * 1024;
const METRIC_LIMIT: u64 = 1_000_000;
const RELIC_LIMIT: usize = 64;
const MISSION_RELIC_LIMIT: usize = 4096;
const WORLD_RELIC_LIMIT: usize = 4096;
const ARTIFACT_LIMIT: usize = 4096;
const RECEIPT_LIMIT: usize = 16_384;
const COUNTER_LIMIT: usize = 16_384;
/// One judged run plays at most `SignalTriangulation.MAX_TURNS` bursts. Taken from
/// the SDK rather than restated, because a claim longer than the judge's `replay`
/// will score must be refused at the carrier, not here.
const SIGNAL_ACTION_LIMIT: usize = dregg_sdk::poa_signal::SIGNAL_MAX_TRANSCRIPT_ROUNDS;

/// Node-side routing result.  A malformed reserved event is returned as an
/// error and can never be reconsidered as ordinary event traffic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignalEffectRoute {
    Ordinary,
    Signal(SignalClaimV1),
}

/// Classify one effect at the reserved PoA boundary.
pub fn classify_signal_effect(effect: &Effect) -> Result<SignalEffectRoute, SignalAdapterError> {
    let Effect::EmitEvent { event, .. } = effect else {
        return Ok(SignalEffectRoute::Ordinary);
    };
    match classify_signal_event(event).map_err(SignalAdapterError::Claim)? {
        SignalEventRoute::Ordinary => Ok(SignalEffectRoute::Ordinary),
        SignalEventRoute::Signal(claim) => Ok(SignalEffectRoute::Signal(claim)),
    }
}

/// Exact, parsed `POA-SIGNAL-IN-1` bytes.
#[derive(Clone, Debug)]
pub struct CanonicalSignalInput {
    bytes: String,
    dto: SignalInputDto,
}

impl CanonicalSignalInput {
    pub fn parse(bytes: &str) -> Result<Self, SignalAdapterError> {
        let dto: SignalInputDto = parse_exact(bytes, "Signal input")?;
        validate_input(&dto)?;
        Ok(Self {
            bytes: bytes.to_owned(),
            dto,
        })
    }

    pub fn as_str(&self) -> &str {
        &self.bytes
    }

    /// Drop the request entirely, retaining only the state a future finalized
    /// adapter must derive from persistence/finality.
    pub fn authority_context(&self) -> SignalAuthorityContext {
        SignalAuthorityContext {
            config: self.dto.config.clone(),
            world: self.dto.world.clone(),
            canon: self.dto.canon.clone(),
            carrier: self.dto.carrier.clone(),
            slot_state: self.dto.slot_state.clone(),
        }
    }
}

/// Exact, parsed `POA-SIGNAL-OUT-1` bytes returned by Lean.
#[derive(Clone, Debug)]
pub struct CanonicalSignalOutput {
    bytes: String,
    dto: SignalOutputDto,
}

impl CanonicalSignalOutput {
    pub fn parse(bytes: &str) -> Result<Self, SignalAdapterError> {
        let dto: SignalOutputDto = parse_exact(bytes, "Signal output")?;
        validate_output(&dto)?;
        Ok(Self {
            bytes: bytes.to_owned(),
            dto,
        })
    }

    pub fn as_str(&self) -> &str {
        &self.bytes
    }

    /// The mission id in the Lean-emitted receipt (inspection only).
    pub fn mission_id(&self) -> u64 {
        self.dto.receipt.mission.mission_id
    }
}

/// Host-only pieces used to construct a complete judge input.
///
/// The public constructor discards the request from an already strict canonical
/// input. Finality and semantic replay construct the same context from the
/// persisted head plus the exact finalized turn and receipt.
#[derive(Clone, Debug)]
pub struct SignalAuthorityContext {
    config: SignalConfigDto,
    world: WorldStateDto,
    canon: CanonStateDto,
    carrier: FinalizedCarrierDto,
    /// Curator-held, ceremony-installed slot state. Never client-supplied and
    /// never reconstructed from the request.
    slot_state: SlotStateDto,
}

/// A side-effect-free evaluated candidate.  Possession of this value is not
/// evidence that its context came from finality or that its successor committed.
#[derive(Clone, Debug)]
pub struct EvaluatedSignalCandidate {
    input: CanonicalSignalInput,
    output: CanonicalSignalOutput,
    lean_acceptance: dregg_lean_ffi::poa_ffi::AcceptedPoaSignalOutput,
}

/// Result of rebuilding one complete persisted Signal history through the
/// native Lean judge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalSemanticAuditReport {
    pub authority_id: [u8; 32],
    pub transition_count: u64,
    pub retained_genesis_digest: [u8; 32],
    pub rebuilt_head_digest: [u8; 32],
}

impl EvaluatedSignalCandidate {
    pub fn input(&self) -> &CanonicalSignalInput {
        &self.input
    }

    pub fn output(&self) -> &CanonicalSignalOutput {
        &self.output
    }
}

/// Build the canonical Lean input while deriving every authority-bearing
/// request field from the host context.  The public claim contributes exactly
/// `mission_id` and the played transcript.
///
/// # The live instance
///
/// The persisted config is a mission TEMPLATE and carries `Emit.UNBOUND_RUN_SEED`
/// — genesis has no instance, because an instance is per (slot, mission, player).
/// This function replaces the template's seed and target with the live draw for
/// THIS player before judging.
///
/// The derivation is Lean's ([`derive_live_instance`]); nothing here recomputes it.
/// The judge then re-derives it a second time from `slot_state` and refuses if the
/// two disagree, so a node that published one commitment and served a different
/// instance cannot settle the run.
pub fn prepare_signal_input(
    context: &SignalAuthorityContext,
    claim: SignalClaimV1,
) -> Result<CanonicalSignalInput, SignalAdapterError> {
    let mission_id = u64::from(claim.mission_id());
    if context.config.mission.mission_id != mission_id {
        return Err(SignalAdapterError::MissionMismatch {
            claimed: mission_id,
            active: context.config.mission.mission_id,
        });
    }
    // ⚑ THE WHOLE TRANSCRIPT, in submission order. `SignalTriangulation.judge`
    // `replay`s exactly this list from `initialState`, so a claim that named only
    // its solving guess asked the judge to score a one-round game — which is what
    // made a blind 1-in-216 settle. The judge is unchanged; what it is handed is
    // now the game that was played.
    let actions: Vec<SignalCodeDto> = claim
        .transcript()
        .iter()
        .copied()
        .map(SignalCodeDto::from)
        .collect();
    let instance = derive_live_instance(context)?;
    let mut config = context.config.clone();
    config.mission.run_seed = instance.run_seed;
    config.target = instance.target;
    let dto = SignalInputDto {
        format: SIGNAL_INPUT_FORMAT.to_owned(),
        config,
        world: context.world.clone(),
        canon: context.canon.clone(),
        carrier: context.carrier.clone(),
        slot_state: context.slot_state.clone(),
        request: SignalRequestDto {
            mission_id,
            federation_id: context.carrier.federation_id.clone(),
            content_root: context.carrier.content_root.clone(),
            activation_digest: context.carrier.activation_digest.clone(),
            content_session: context.carrier.content_session.clone(),
            content_epoch: context.carrier.content_epoch,
            slot: context.slot_state.slot,
            slot_commitment: context.slot_state.commitment.clone(),
            actor_root: context.carrier.actor_root.clone(),
            player_key: context.carrier.player_key.clone(),
            previous_player_counter: context.carrier.current_player_counter,
            expected_world_sequence: context.world.sequence,
            expected_canon_revision: context.canon.revision,
            actions,
        },
    };
    validate_input(&dto)?;
    let bytes =
        serde_json::to_string(&dto).map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    CanonicalSignalInput::parse(&bytes)
}

/// The live run seed and its puzzle target, as derived by Lean.
struct LiveInstance {
    run_seed: String,
    target: SignalCodeDto,
}

/// The `POA-SLOT-DERIVE-1` request, with the wire's key order as its FIELD order.
///
/// ⚠ THE ORDER OF THESE FIELDS IS THE WIRE. It is not style.
///
/// `SlotDeriveRuntime.decodeRequest` is `canonicalDecode parseRequestJson
/// Request.toJson`: Lean parses, re-encodes in `Request.toJson`'s pinned order, and
/// compares BYTES. A request whose keys are in any other order decodes to `none`,
/// `slotDeriveFFI` returns its `""` refusal sentinel, and every scored Signal run
/// fails as [`SignalAdapterError::LeanRejected`] — silently and totally.
///
/// This was a `serde_json::json!` literal. `json!` preserves insertion order only
/// when serde_json's `preserve_order` feature is on, and **nothing in this
/// workspace declares it** — `node/Cargo.toml` asks only for `raw_value`. It was on
/// by feature unification from a transitive dependency, so the correct wire was an
/// accident of the dependency graph, revocable by an unrelated crate dropping a
/// feature nobody would connect to Path of Angels. A derived `Serialize` emits
/// fields in declaration order unconditionally, so the wire no longer depends on
/// any feature being anything.
///
/// `slot_derive_request_is_the_exact_pinned_wire` fails if this order changes.
#[derive(Serialize)]
struct SlotDeriveRequestDto<'a> {
    format: &'static str,
    slot: u64,
    secret: &'a str,
    mission_id: u64,
    epoch: u64,
    federation_id: &'a str,
    content_session: &'a str,
    player_key: &'a str,
}

/// Build the exact canonical derivation request. Extracted from
/// [`derive_live_instance`] so a test can assert its BYTES without a Lean archive:
/// the order gate must be able to fail on a machine that cannot run the export.
fn slot_derive_request_wire(
    context: &SignalAuthorityContext,
) -> Result<String, SignalAdapterError> {
    serde_json::to_string(&SlotDeriveRequestDto {
        format: dregg_lean_ffi::poa_slot_derive_ffi::SLOT_DERIVE_INPUT_FORMAT,
        slot: context.slot_state.slot,
        secret: &context.slot_state.secret,
        mission_id: context.config.mission.mission_id,
        epoch: context.config.mission.epoch,
        federation_id: &context.config.mission.federation_id,
        content_session: &context.config.mission.content_session,
        player_key: &context.carrier.player_key,
    })
    .map_err(|error| SignalAdapterError::Json(error.to_string()))
}

/// Ask Lean for `commit`, `runSeedFor` and `targetFromSeed` of this slot state and
/// this player.
///
/// ⚠ Every branch here either returns Lean's answer or refuses. There is no Rust
/// derivation and there must never be one: `HiddenInstance` is a Poseidon2-BabyBear
/// sponge with its own padding, lane-aliasing rejection and domain tags, and a
/// second copy of it in Rust would be an unproven twin of a soundness function.
fn derive_live_instance(
    context: &SignalAuthorityContext,
) -> Result<LiveInstance, SignalAdapterError> {
    let wire = slot_derive_request_wire(context)?;
    let reply = dregg_lean_ffi::poa_slot_derive_ffi::derive_poa_slot_instance(&wire)
        .map_err(SignalAdapterError::LeanTransport)?
        .ok_or(SignalAdapterError::LeanRejected)?;

    #[derive(Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    struct DeriveReplyDto {
        format: String,
        commitment: String,
        run_seed: String,
        target: SignalCodeDto,
    }
    let reply: DeriveReplyDto = parse_exact(&reply, "Signal slot derivation")?;
    if reply.format != dregg_lean_ffi::poa_slot_derive_ffi::SLOT_DERIVE_OUTPUT_FORMAT {
        return Err(SignalAdapterError::InvalidField("slot derivation format"));
    }
    validate_digest("derived run_seed", &reply.run_seed)?;
    validate_code(&reply.target)?;
    // The commitment Lean computes from the node's secret must be the one the
    // curator published and the node installed. Equal strings, not a recomputation:
    // the derivation is Lean's on both sides.
    if reply.commitment != context.slot_state.commitment {
        return Err(SignalAdapterError::SlotCommitmentMismatch);
    }
    Ok(LiveInstance {
        run_seed: reply.run_seed,
        target: reply.target,
    })
}

/// The live instance one (authority, open slot, player) draws — THE ANSWER to
/// that run, as Lean derives it.
///
/// ⚠ **THIS VALUE IS THE PUZZLE SOLUTION.** It is produced from the curator's slot
/// secret and is only meaningful to whoever already holds that secret. Nothing that
/// renders it may reach a route, a public log, an artifact or a metric.
#[derive(Clone, Debug)]
pub struct OperatorDerivedInstance {
    /// The mission the persisted head has active.
    pub mission_id: u64,
    /// The open slot this instance belongs to.
    pub slot: u64,
    /// Lean's `runSeedFor` for this (secret, slot, player) and this content context.
    pub run_seed: String,
    /// Lean's `targetFromSeed` of that run seed — the solving code.
    pub target: SignalCode,
}

/// Derive the live instance for one player against a persisted head and an
/// INSTALLED slot, through the same Lean export the judge re-derives with.
///
/// ⚠ **OPERATOR / CURATOR ONLY. NEVER REACHABLE FROM THE HTTP ROUTER.** Publishing
/// this — as a route, a log line, a status field, an exported artifact — hands
/// every player the answer and makes the whole deduction game a formality. The
/// caller must already hold the slot secret (it is read out of the installed slot
/// record, which lives only in the node's own store), and holding the secret is
/// what knowing the instance MEANS; but a route would hand the derived answer to
/// callers who hold nothing.
/// `poa_signal_slot_instance::the_operator_derivation_is_unreachable_from_any_router`
/// fails if any HTTP surface in this crate so much as names these symbols.
///
/// There is no Rust derivation here and there must never be one: this is Lean's
/// `HiddenInstance` sponge, and the judge re-derives it independently and refuses
/// if the two disagree.
pub fn derive_operator_instance(
    head: &dregg_persist::PoaSignalHeadV1,
    slot: &dregg_persist::PoaInstalledSlotV1,
    active_federation_id: [u8; 32],
    player_key: [u8; 32],
    actor_root: [u8; 32],
) -> Result<OperatorDerivedInstance, SignalAdapterError> {
    let context = authority_context_from_persisted_head(
        head,
        slot,
        active_federation_id,
        player_key,
        actor_root,
    )?;
    let instance = derive_live_instance(&context)?;
    let target = SignalCode::new(
        instance.target.low,
        instance.target.mid,
        instance.target.high,
    )
    .map_err(SignalAdapterError::Claim)?;
    Ok(OperatorDerivedInstance {
        mission_id: context.config.mission.mission_id,
        slot: context.slot_state.slot,
        run_seed: instance.run_seed,
        target,
    })
}

/// One mid-run classification: LOCKED and DRIFT, and nothing else.
///
/// ⚠ Contrast [`OperatorDerivedInstance`], which is the ANSWER and may never reach a
/// route. This value is what a judged session serves, and it is safe to serve for a
/// structural reason rather than by filtering: there is no field here that a target
/// could occupy. Lean carries the same fact past the wire —
/// `SignalFeedbackRuntime.reply_bytes_are_a_function_of_the_feedback_alone` proves the
/// served bytes are a function of the classification alone, and
/// `served_transcript_cannot_separate_feedback_equivalent_targets` proves a whole
/// session's bytes are invariant across the feedback-consistency class of its own
/// transcript. That is "no faster than playing", stated exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SessionClassification {
    /// `SignalTriangulation.Feedback.exact` — bands in the correct position.
    pub exact: u8,
    /// `SignalTriangulation.Feedback.present` — additional multiplicity-respecting
    /// matches in the wrong position.
    pub present: u8,
}

impl SessionClassification {
    /// A run is solved exactly when all three bands lock, which
    /// `SignalTriangulation.accepted_solved_iff_target` proves is equivalent to the
    /// guess BEING the target. The node decides this on no other evidence.
    pub fn solved(self) -> bool {
        self.exact == 3
    }
}

/// The `POA-SIGNAL-FEEDBACK-1` request, with the wire's key order as its FIELD order.
///
/// ⚠ THE ORDER OF THESE FIELDS IS THE WIRE, for exactly the reason spelled out on
/// [`SlotDeriveRequestDto`]: `SignalFeedbackRuntime.decodeRequest` is
/// `canonicalDecode parseRequestJson Request.toJson`, so Lean re-encodes what it parsed
/// and compares BYTES. A derived `Serialize` emits declaration order unconditionally;
/// a `json!` map's order would be an accident of the dependency graph.
///
/// `signal_feedback_request_is_the_exact_pinned_wire` fails if this order changes.
#[derive(Serialize)]
struct SignalFeedbackRequestDto<'a> {
    format: &'static str,
    slot: u64,
    secret: &'a str,
    mission_id: u64,
    epoch: u64,
    federation_id: &'a str,
    content_session: &'a str,
    player_key: &'a str,
    commitment: &'a str,
    guess: SignalCodeDto,
}

/// Build the exact canonical classification request. Extracted from
/// [`classify_session_guess`] so a test can assert its BYTES without a Lean archive.
fn signal_feedback_request_wire(
    context: &SignalAuthorityContext,
    guess: SignalCode,
) -> Result<String, SignalAdapterError> {
    serde_json::to_string(&SignalFeedbackRequestDto {
        format: dregg_lean_ffi::poa_signal_feedback_ffi::SIGNAL_FEEDBACK_INPUT_FORMAT,
        slot: context.slot_state.slot,
        secret: &context.slot_state.secret,
        mission_id: context.config.mission.mission_id,
        epoch: context.config.mission.epoch,
        federation_id: &context.config.mission.federation_id,
        content_session: &context.config.mission.content_session,
        player_key: &context.carrier.player_key,
        commitment: &context.slot_state.commitment,
        guess: SignalCodeDto::from(guess),
    })
    .map_err(|error| SignalAdapterError::Json(error.to_string()))
}

/// The actor root a session context carries.
///
/// ⚠ A judged session has no executor receipt, so there is no `pre_state_hash` to
/// supply — and none is needed: the classification wire's ten fields (above) do not
/// include one, and the derivation the oracle performs is
/// `HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`, which does not read it
/// either. It is threaded only because [`authority_context_from_persisted_head`] is the
/// one place the head/Canon/slot bindings are checked, and that function's contract
/// covers the whole judge input. `the_feedback_wire_does_not_carry_an_actor_root` fails
/// if this value ever reaches the bytes.
const SESSION_UNREAD_ACTOR_ROOT: [u8; 32] = [0u8; 32];

/// Classify ONE mid-run guess against the judged instance, through Lean.
///
/// This is the function a judged session route calls, and it is deliberately
/// route-reachable — the one PoA derivation-adjacent path that is. What makes that
/// sound is not a filter here but the shape of what comes back: two counts.
///
/// It writes nothing and settles nothing. A session's budget is spent by the caller
/// committing the round to storage, and the caller must do that BEFORE returning this
/// value to the player (`dregg_persist::poa_signal_session`'s persist-then-reveal
/// rule); answering before committing hands a free round to anyone who can crash the
/// node.
///
/// There is no Rust classification here and there must never be one: the rule is
/// `SignalTriangulation.feedback`, the same function `step` scores a settling
/// transcript with, and a second copy of it in Rust would hand players a different game
/// than the one that settles.
pub fn classify_session_guess(
    head: &dregg_persist::PoaSignalHeadV1,
    slot: &dregg_persist::PoaInstalledSlotV1,
    active_federation_id: [u8; 32],
    player_key: [u8; 32],
    guess: SignalCode,
) -> Result<SessionClassification, SignalAdapterError> {
    let context = authority_context_from_persisted_head(
        head,
        slot,
        active_federation_id,
        player_key,
        SESSION_UNREAD_ACTOR_ROOT,
    )?;
    let wire = signal_feedback_request_wire(&context, guess)?;
    let reply = dregg_lean_ffi::poa_signal_feedback_ffi::classify_poa_signal_guess(&wire)
        .map_err(SignalAdapterError::LeanTransport)?
        .ok_or(SignalAdapterError::FeedbackRefused)?;

    #[derive(Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    struct FeedbackReplyDto {
        format: String,
        exact: u8,
        present: u8,
    }
    let reply: FeedbackReplyDto = parse_exact(&reply, "Signal feedback")?;
    if reply.format != dregg_lean_ffi::poa_signal_feedback_ffi::SIGNAL_FEEDBACK_OUTPUT_FORMAT {
        return Err(SignalAdapterError::InvalidField("feedback reply format"));
    }
    // `SignalTriangulation.feedback_match_bound` is the Lean statement; this is the
    // host-side refusal that a reply violating it is not passed on as a classification.
    if reply.exact > 3 || reply.exact.saturating_add(reply.present) > 3 {
        return Err(SignalAdapterError::InvalidField("feedback counts"));
    }
    Ok(SessionClassification {
        exact: reply.exact,
        present: reply.present,
    })
}

/// Why a submitted claim is not evidence that the game was played.
///
/// ⚠ EVERY VARIANT IS A FUNCTION OF (stored session, submitted claim) AND NOTHING
/// ELSE. It never reads the target, the run seed or the slot secret, so a refusal
/// cannot tell a submitter anything about the answer — including how close their
/// code was. `the_refusal_never_depends_on_whether_the_code_is_right` drives that
/// on both a solving and a losing code against one session and requires the same
/// refusal, which is the only way to check it that a target-reading implementation
/// could not also pass.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnplayedTranscriptV1 {
    /// ⚑ THE BLIND CLAIM. No judged session exists for this (authority, slot,
    /// player) at all: the node never classified a single one of these rounds, so
    /// whatever the code is, it was not deduced here.
    NoSession,
    /// A session exists but was opened against a different mission or a different
    /// slot commitment — a different instance, and therefore a different answer.
    InstanceMismatch,
    /// The claim names more or fewer rounds than the node served.
    LengthMismatch,
    /// A round in the claim is not the round the node classified at that index.
    RoundMismatch,
    /// The node never classified this run's last guess as locking all three bands.
    NotSolved,
}

impl UnplayedTranscriptV1 {
    /// The stable machine token recorded on the finalized rejection and returned
    /// by the ingress route.
    pub fn code(self) -> &'static str {
        match self {
            Self::NoSession => "poa-signal-transcript-no-session",
            Self::InstanceMismatch => "poa-signal-transcript-instance-mismatch",
            Self::LengthMismatch => "poa-signal-transcript-length-mismatch",
            Self::RoundMismatch => "poa-signal-transcript-round-mismatch",
            Self::NotSolved => "poa-signal-transcript-not-solved",
        }
    }
}

impl fmt::Display for UnplayedTranscriptV1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSession => write!(
                f,
                "no judged Signal session is open for this player against this slot, so this \
                 node classified none of the rounds this claim carries. Open a session and \
                 play it; a code with no game behind it settles nothing"
            ),
            Self::InstanceMismatch => write!(
                f,
                "the judged session for this player and slot was opened against a different \
                 mission or slot commitment; a transcript scored against one instance is not \
                 evidence about another"
            ),
            Self::LengthMismatch => write!(
                f,
                "the claim names a different number of rounds than this node served for this \
                 run"
            ),
            Self::RoundMismatch => write!(
                f,
                "a round in the claim is not the guess this node classified at that position"
            ),
            Self::NotSolved => write!(
                f,
                "this node never classified the last round of this run as locking all three \
                 bands, so the run is not solved here"
            ),
        }
    }
}

/// ⚑ THE GATE THAT MAKES A SETTLEMENT EVIDENCE THAT A GAME WAS PLAYED.
///
/// # What it closes
///
/// `SignalTriangulation.judge` scores whatever transcript it is handed, and it is
/// right to: it is the RULE, and a rule has no opinion about where a transcript
/// came from. Provenance is the node's job and until now the node had none. The
/// public claims route admitted a bare code, the adapter wrapped it as a one-round
/// game, the judge scored it, and a 1-in-216 blind guess settled a turn with no
/// session, no feedback and no deduction anywhere in its causal history. The
/// judged session that landed in `47cf23360` made deduction POSSIBLE; nothing made
/// it NECESSARY.
///
/// This function is the necessity. A claim must name the rounds the node ITSELF
/// classified, in the order it classified them, ending in the guess it itself
/// scored as locking — so the transcript on the chain is the transcript that was
/// served, and a judged settlement is evidence a game was played.
///
/// # What it deliberately does NOT do
///
/// It does not decide whether the transcript SOLVES. That is
/// `SignalTriangulation.replay`/`terminalOutput`, invoked through
/// [`evaluate_persisted_signal_claim`], and re-deciding it here would be a second
/// copy of the rule in Rust — the twin this repo spends its time deleting. This
/// checks only that the node issued these classifications; a transcript that
/// passes here and does not solve is refused by Lean, as before.
///
/// It also does not authenticate the player. `player_key` is the outer
/// `SignedTurn.signer`, and a session is keyed by it, so a claim signed by one key
/// cannot present another player's session.
pub fn verify_claim_transcript_was_played(
    session: Option<&dregg_persist::PoaSignalSessionV1>,
    slot: &dregg_persist::PoaInstalledSlotV1,
    claim: &SignalClaimV1,
) -> Result<(), UnplayedTranscriptV1> {
    let Some(session) = session else {
        return Err(UnplayedTranscriptV1::NoSession);
    };
    // ⚠ THE CLAIM'S MISSION IS DELIBERATELY NOT COMPARED HERE. It is compared
    // against the head's ACTIVE mission by [`prepare_signal_input`], which refuses
    // as `MissionMismatch { claimed, active }` and names both numbers — a strictly
    // better refusal than "instance mismatch" for the same fact. Repeating it here
    // would only SHADOW that one, and a check whose whole effect is to hide a more
    // specific sibling is a check that costs a diagnosis. What this compares is the
    // INSTANCE the session was played against: same slot, same published
    // commitment, and therefore the same secret and the same target.
    if session.slot() != slot.slot() || session.commitment() != slot.commitment() {
        return Err(UnplayedTranscriptV1::InstanceMismatch);
    }
    let played = session.rounds();
    let claimed = claim.transcript();
    if played.len() != claimed.len() {
        return Err(UnplayedTranscriptV1::LengthMismatch);
    }
    for (served, submitted) in played.iter().zip(claimed) {
        if served.guess != [submitted.low(), submitted.mid(), submitted.high()] {
            return Err(UnplayedTranscriptV1::RoundMismatch);
        }
    }
    // The solved bit AND the transcript it is supposed to summarize. They agree by
    // the store's own audit, and checking both costs nothing and means a record
    // that ever disagreed cannot settle on the strength of the cheaper field.
    if !session.solved() || played.last().map(|round| round.exact) != Some(3) {
        return Err(UnplayedTranscriptV1::NotSolved);
    }
    Ok(())
}

/// Invoke the existing Lean FFI and strictly parse its exact reply.
///
/// This function is intentionally pure with respect to node state: it neither
/// executes nor persists the returned successor.
pub fn evaluate_signal_claim(
    context: &SignalAuthorityContext,
    claim: SignalClaimV1,
) -> Result<EvaluatedSignalCandidate, SignalAdapterError> {
    let input = prepare_signal_input(context, claim)?;
    let verdict = dregg_lean_ffi::poa_ffi::judge_poa_signal(input.as_str())
        .map_err(SignalAdapterError::LeanTransport)?;
    let accepted = match verdict {
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(accepted) => accepted,
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Rejected => {
            return Err(SignalAdapterError::LeanRejected);
        }
    };
    let output = CanonicalSignalOutput::parse(accepted.as_str())?;
    validate_evaluation_binding(&input.dto, &output.dto)?;
    Ok(EvaluatedSignalCandidate {
        input,
        output,
        lean_acceptance: accepted,
    })
}

/// Evaluate one public claim against an exact persisted authority head and
/// produce the storage envelope consumed by the finalized-turn atomic weld.
///
/// The caller must supply `player_key` from `SignedTurn.signer` and
/// `actor_root` from the executor-produced receipt's `pre_state_hash`. Neither
/// value is accepted from the public event. This function authenticates no
/// finality by itself; that authority comes from invoking it inside the
/// finalized-turn path and committing its result with the carrying receipt.
pub fn evaluate_persisted_signal_claim(
    head: &dregg_persist::PoaSignalHeadV1,
    slot: &dregg_persist::PoaInstalledSlotV1,
    active_federation_id: [u8; 32],
    player_key: [u8; 32],
    actor_root: [u8; 32],
    claim: SignalClaimV1,
) -> Result<dregg_persist::PreparedPoaSignalTransitionV1, SignalAdapterError> {
    let context = authority_context_from_persisted_head(
        head,
        slot,
        active_federation_id,
        player_key,
        actor_root,
    )?;
    let evaluated = evaluate_signal_claim(&context, claim)?;
    let successor_canon = serde_json::to_vec(&evaluated.output.dto.successor_canon)
        .map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    dregg_persist::PreparedPoaSignalTransitionV1::from_lean_accepted(
        head.authority_id(),
        head.digest(),
        evaluated.output.dto.successor_world.sequence,
        evaluated.output.dto.successor_canon.revision,
        successor_canon,
        evaluated.input.bytes.into_bytes(),
        evaluated.lean_acceptance,
    )
    .map_err(|error| SignalAdapterError::PreparedTransition(error.to_string()))
}

/// Rebuild a finalized Signal history from its retained genesis and immutable
/// finalized carriers, invoking the native Lean judge once for every row.
///
/// The stored predecessor is checked against the previously rebuilt head. The
/// exact stored judge input must also be the byte-identical input reconstructed
/// from that head, the carrying finalized `SignedTurn`, and its durable receipt.
/// Lean then re-executes those exact bytes; its canonical output must be
/// byte-identical to the stored output. Finally the persistence projection is
/// reconstructed from the fresh Lean output and generic commit coordinates, so
/// no stored successor head participates in deriving the next step.
///
/// This is an audit-only operation: it never mutates or repairs persistence.
pub fn audit_persisted_signal_semantics(
    store: &dregg_persist::PersistentStore,
    authority_id: [u8; 32],
) -> Result<SignalSemanticAuditReport, SignalAdapterError> {
    audit_persisted_signal_semantics_against_genesis(store, authority_id, None)
}

/// Semantic replay with an optional independently re-derived genesis digest.
/// Passing `None` names the current boundary exactly: replay starts from the
/// structurally retained zero-transition genesis installed by the ceremony.
/// A future boot ceremony can pass `Some` without changing replay semantics.
pub fn audit_persisted_signal_semantics_against_genesis(
    store: &dregg_persist::PersistentStore,
    authority_id: [u8; 32],
    expected_genesis_digest: Option<[u8; 32]>,
) -> Result<SignalSemanticAuditReport, SignalAdapterError> {
    replay_persisted_signal_history(store, authority_id, expected_genesis_digest)
        .map(|replay| replay.report)
}

/// One finalized Signal transition as the Records read model needs it.
///
/// Every field is a *replayed* value, not a stored label: the coordinates come
/// from the carrying generic commit, `signer` from the finalized `SignedTurn`,
/// `actor_root` from the durable receipt's `pre_state_hash`, and the two byte
/// blobs are the exact inputs/outputs the replay above re-derived and re-judged.
/// Rust does not interpret the blobs; only Lean does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedSignalRow {
    pub sequence: u64,
    pub commit_ordinal: u64,
    pub turn_hash: [u8; 32],
    pub receipt_hash: [u8; 32],
    pub actor_root: [u8; 32],
    pub signer: [u8; 32],
    pub judge_input: String,
    pub judge_output: String,
}

/// A completed semantic replay: its verdict plus the finalized material every
/// accepted row contributed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignalSemanticReplay {
    pub report: SignalSemanticAuditReport,
    /// Exact retained genesis config bytes (the active mission).
    pub genesis_config: Vec<u8>,
    /// Exact retained genesis Canon bytes.
    pub genesis_canon: Vec<u8>,
    pub rows: Vec<FinalizedSignalRow>,
}

/// The one replay implementation.
///
/// [`audit_persisted_signal_semantics_against_genesis`] is this function with
/// its rows discarded, so an auditing caller and a reading caller cannot drift:
/// a Records read that returns rows has necessarily passed every check the
/// audit performs, in the same order.
pub fn replay_persisted_signal_history(
    store: &dregg_persist::PersistentStore,
    authority_id: [u8; 32],
    expected_genesis_digest: Option<[u8; 32]>,
) -> Result<SignalSemanticReplay, SignalAdapterError> {
    let history = store
        .load_poa_signal_history(authority_id)
        .map_err(|error| SignalAdapterError::SemanticReplay(error.to_string()))?
        .ok_or_else(|| {
            SignalAdapterError::SemanticReplay(
                "requested PoA Signal authority has no persisted genesis".to_owned(),
            )
        })?;
    if expected_genesis_digest.is_some_and(|expected| expected != history.genesis().digest()) {
        return Err(SignalAdapterError::SemanticReplay(
            "retained Signal genesis differs from the independently expected digest".to_owned(),
        ));
    }

    let blocks = load_signal_block_index(store)?;
    let receipts = load_signal_receipt_index(store)?;
    let mut rebuilt = history.genesis().clone();
    let mut rows = Vec::with_capacity(history.transitions().len());

    for stored in history.transitions() {
        let sequence = stored.sequence();
        if stored.predecessor_head().map_err(|error| {
            SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} predecessor is invalid: {error}"
            ))
        })? != rebuilt
        {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} predecessor is not the previously rebuilt head"
            )));
        }

        let commit = store
            .finalized_commit_authority_at(stored.commit_ordinal())
            .map_err(|error| SignalAdapterError::SemanticReplay(error.to_string()))?
            .ok_or_else(|| {
                SignalAdapterError::SemanticReplay(format!(
                    "Signal sequence {sequence} has no carrying generic commit"
                ))
            })?;
        let block = blocks.get(&commit.block_id()).ok_or_else(|| {
            SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} has no persisted carrying block"
            ))
        })?;
        let signed_bytes = persisted_finalized_turn_bytes(&block.payload).ok_or_else(|| {
            SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} carrying block has no SignedTurn"
            ))
        })?;
        let signed =
            crate::signed_turn_validation::decode_signed_turn(signed_bytes).map_err(|error| {
                SignalAdapterError::SemanticReplay(format!(
                    "Signal sequence {sequence} carrying SignedTurn is not exact: {error}"
                ))
            })?;
        if signed.turn.hash() != commit.turn_hash() || commit.turn_hash() != stored.turn_hash() {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} disagrees with its finalized SignedTurn"
            )));
        }
        let claim = dregg_sdk::poa_signal::claim_from_exact_signal_turn(&signed.turn).map_err(
            |error| {
                SignalAdapterError::SemanticReplay(format!(
                    "Signal sequence {sequence} carrying turn is not the exact Signal carrier: {error}"
                ))
            },
        )?;
        let receipt = receipts.get(&commit.receipt_hash()).ok_or_else(|| {
            SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} has no exact durable receipt"
            ))
        })?;
        if receipt.receipt_hash() != commit.receipt_hash()
            || commit.receipt_hash() != stored.receipt_hash()
            || receipt.turn_hash != commit.turn_hash()
            || receipt.federation_id != authority_id
            || receipt.agent != signed.turn.agent
        {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} receipt/finality coordinates disagree"
            )));
        }

        // Which slot this run was played in is read from the stored input, but the
        // SECRET and COMMITMENT are then loaded from the store, not from those
        // bytes. Taking the whole slot state from the journal would make the replay
        // agree with any slot state the journal happened to contain; loading it
        // independently is what lets the byte-identity check below detect a
        // substituted instance.
        let stored_slot = parse_exact::<SignalInputDto>(
            std::str::from_utf8(stored.judge_input()).map_err(|_| {
                SignalAdapterError::SemanticReplay(format!(
                    "Signal sequence {sequence} judge input is not UTF-8"
                ))
            })?,
            "stored Signal judge input",
        )?
        .slot_state
        .slot;
        let installed_slot = store
            .load_poa_signal_slot_v1(authority_id, stored_slot)
            .map_err(|error| {
                SignalAdapterError::SemanticReplay(format!(
                    "Signal sequence {sequence} slot load failed: {error}"
                ))
            })?
            .ok_or_else(|| {
                SignalAdapterError::SemanticReplay(format!(
                    "Signal sequence {sequence} names slot {stored_slot}, which is not installed"
                ))
            })?;
        let context = authority_context_from_persisted_head(
            &rebuilt,
            &installed_slot,
            authority_id,
            signed.signer.0,
            receipt.pre_state_hash,
        )?;
        let expected_input = prepare_signal_input(&context, claim)?;
        let exact_input = std::str::from_utf8(stored.judge_input()).map_err(|_| {
            SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} judge input is not UTF-8"
            ))
        })?;
        // Invoke native Lean on the stored bytes even when the independently
        // reconstructed authority input will subsequently expose substitution.
        // This makes the replay claim literal: every decodable journal input is
        // re-judged; authority binding and byte-identical output are separate
        // mandatory checks over that verdict.
        let replayed_verdict = dregg_lean_ffi::poa_ffi::judge_poa_signal(exact_input)
            .map_err(SignalAdapterError::LeanTransport)?;
        if expected_input.as_str().as_bytes() != stored.judge_input() {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} stored judge input is not the input derived from finalized authority"
            )));
        }
        let replayed_output = match replayed_verdict {
            dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(output) => output,
            dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Rejected => {
                return Err(SignalAdapterError::SemanticReplay(format!(
                    "Lean rejected stored Signal sequence {sequence}"
                )));
            }
        };
        if replayed_output.as_str().as_bytes() != stored.judge_output() {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} stored judge output differs from native Lean replay"
            )));
        }
        let output = CanonicalSignalOutput::parse(replayed_output.as_str())?;
        validate_evaluation_binding(&expected_input.dto, &output.dto)?;
        let successor_canon = serde_json::to_vec(&output.dto.successor_canon)
            .map_err(|error| SignalAdapterError::Json(error.to_string()))?;
        let candidate = dregg_persist::PreparedPoaSignalTransitionV1::from_lean_accepted(
            authority_id,
            rebuilt.digest(),
            output.dto.successor_world.sequence,
            output.dto.successor_canon.revision,
            successor_canon,
            expected_input.as_str().as_bytes().to_vec(),
            replayed_output,
        )
        .map_err(|error| SignalAdapterError::PreparedTransition(error.to_string()))?;
        let reconstructed =
            dregg_persist::PoaSignalTransitionV1::reconstruct_from_finalized_authority_for_audit(
                &rebuilt, &commit, &candidate,
            )
            .map_err(|error| SignalAdapterError::SemanticReplay(error.to_string()))?;
        if &reconstructed != stored {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} stored successor is not the projection of native Lean output"
            )));
        }
        // Retained only after this row has passed every check above. `signer`
        // and `actor_root` are the finalized values — never re-derived from the
        // judge input's own carrier, which is the thing they exist to bind.
        rows.push(FinalizedSignalRow {
            sequence,
            commit_ordinal: stored.commit_ordinal(),
            turn_hash: stored.turn_hash(),
            receipt_hash: stored.receipt_hash(),
            actor_root: receipt.pre_state_hash,
            signer: signed.signer.0,
            judge_input: expected_input.as_str().to_owned(),
            judge_output: output.as_str().to_owned(),
        });
        rebuilt = reconstructed.successor_head().map_err(|error| {
            SignalAdapterError::SemanticReplay(format!(
                "Signal sequence {sequence} rebuilt successor is invalid: {error}"
            ))
        })?;
    }

    if &rebuilt != history.current() {
        return Err(SignalAdapterError::SemanticReplay(
            "persisted Signal head differs from the semantically rebuilt history".to_owned(),
        ));
    }
    Ok(SignalSemanticReplay {
        report: SignalSemanticAuditReport {
            authority_id,
            transition_count: u64::try_from(history.transitions().len()).map_err(|_| {
                SignalAdapterError::SemanticReplay(
                    "persisted Signal transition count exceeds u64".to_owned(),
                )
            })?,
            retained_genesis_digest: history.genesis().digest(),
            rebuilt_head_digest: rebuilt.digest(),
        },
        genesis_config: history.genesis().config().to_vec(),
        genesis_canon: history.genesis().canon().to_vec(),
        rows,
    })
}

fn load_signal_block_index(
    store: &dregg_persist::PersistentStore,
) -> Result<BTreeMap<[u8; 32], dregg_blocklace::finality::Block>, SignalAdapterError> {
    let mut out = BTreeMap::new();
    for block in store
        .load_all_blocks()
        .map_err(|error| SignalAdapterError::SemanticReplay(error.to_string()))?
    {
        let id = block.id().0;
        if out.insert(id, block).is_some() {
            return Err(SignalAdapterError::SemanticReplay(
                "persisted blocklace contains duplicate computed block ids".to_owned(),
            ));
        }
    }
    Ok(out)
}

fn load_signal_receipt_index(
    store: &dregg_persist::PersistentStore,
) -> Result<BTreeMap<[u8; 32], dregg_turn::TurnReceipt>, SignalAdapterError> {
    let mut out = BTreeMap::new();
    for (index, bytes) in store
        .load_receipt_chain()
        .map_err(|error| SignalAdapterError::SemanticReplay(error.to_string()))?
        .into_iter()
        .enumerate()
    {
        let (receipt, remainder): (dregg_turn::TurnReceipt, &[u8]) =
            postcard::take_from_bytes(&bytes).map_err(|error| {
                SignalAdapterError::SemanticReplay(format!(
                    "durable receipt {index} is not decodable: {error}"
                ))
            })?;
        if !remainder.is_empty() {
            return Err(SignalAdapterError::SemanticReplay(format!(
                "durable receipt {index} has trailing bytes"
            )));
        }
        let hash = receipt.receipt_hash();
        if out.insert(hash, receipt).is_some() {
            return Err(SignalAdapterError::SemanticReplay(
                "durable receipt chain contains a duplicate receipt hash".to_owned(),
            ));
        }
    }
    Ok(out)
}

fn persisted_finalized_turn_bytes(payload: &Payload) -> Option<&[u8]> {
    match payload {
        Payload::Turn(bytes) => Some(bytes),
        Payload::TurnBundle(bundle) => Some(&bundle.signed_turn),
        Payload::ConsensusTimedTurnV1(bundle) => Some(bundle.signed_turn()),
        Payload::Ack
        | Payload::Checkpoint { .. }
        | Payload::MembershipVote { .. }
        | Payload::Data(_) => None,
    }
}

/// Transport-layer failures.  None authorizes ordinary-event fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignalAdapterError {
    Claim(SignalClaimError),
    WireTooLarge {
        what: &'static str,
        bytes: usize,
    },
    Json(String),
    Noncanonical(&'static str),
    InvalidField(&'static str),
    MissionMismatch {
        claimed: u64,
        active: u64,
    },
    LeanTransport(String),
    LeanRejected,
    /// The commitment Lean derives from the installed slot secret is not the one
    /// the curator published. The node holds the wrong secret for this slot and
    /// must not serve a run against it.
    SlotCommitmentMismatch,
    /// The Lean feedback oracle refused the classification wire. It is a distinct
    /// refusal from [`Self::LeanRejected`] on purpose: nothing was judged and no
    /// transition was proposed, so reporting this as "Lean rejected the transition"
    /// would name a cause that did not happen.
    FeedbackRefused,
    OutputBinding(&'static str),
    PreparedTransition(String),
    SemanticReplay(String),
}

impl fmt::Display for SignalAdapterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Claim(error) => write!(f, "{error}"),
            Self::WireTooLarge { what, bytes } => {
                write!(f, "{what} is {bytes} bytes, above the 16 MiB Lean limit")
            }
            Self::Json(error) => write!(f, "invalid Signal JSON: {error}"),
            Self::Noncanonical(what) => write!(f, "{what} is not exact canonical JSON"),
            Self::InvalidField(field) => write!(f, "invalid Signal field: {field}"),
            Self::MissionMismatch { claimed, active } => {
                write!(
                    f,
                    "claimed mission {claimed} is not active mission {active}"
                )
            }
            Self::LeanTransport(error) => write!(f, "Lean Signal transport unavailable: {error}"),
            Self::LeanRejected => write!(f, "Lean rejected the Signal transition"),
            Self::SlotCommitmentMismatch => write!(
                f,
                "the installed slot secret does not open the published slot commitment; \
                 refusing to serve a run whose instance nobody committed to"
            ),
            Self::FeedbackRefused => write!(
                f,
                "the Lean Signal feedback oracle refused this classification wire; no guess was \
                 scored"
            ),
            Self::OutputBinding(reason) => write!(f, "Lean Signal output binding failed: {reason}"),
            Self::PreparedTransition(error) => {
                write!(f, "PoA Signal persistence envelope refused: {error}")
            }
            Self::SemanticReplay(error) => write!(f, "PoA Signal semantic replay failed: {error}"),
        }
    }
}

impl std::error::Error for SignalAdapterError {}

fn parse_exact<T>(bytes: &str, what: &'static str) -> Result<T, SignalAdapterError>
where
    T: DeserializeOwned + Serialize,
{
    if bytes.len() > LEAN_SIGNAL_WIRE_BYTES {
        return Err(SignalAdapterError::WireTooLarge {
            what,
            bytes: bytes.len(),
        });
    }
    let dto: T =
        serde_json::from_str(bytes).map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    let encoded =
        serde_json::to_string(&dto).map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    if encoded != bytes {
        return Err(SignalAdapterError::Noncanonical(what));
    }
    Ok(dto)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactRefDto {
    mission_id: u64,
    artifact_id: u64,
    source_digest: String,
    content_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BudgetDto {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    relics: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct MissionDto {
    mission_id: u64,
    artifact: ArtifactRefDto,
    epoch: u64,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    run_seed: String,
    budget: BudgetDto,
    allowed_relics: Vec<u64>,
    privacy: String,
    ballot: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContributionDto {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    relics: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalCodeDto {
    low: u64,
    mid: u64,
    high: u64,
}

impl From<SignalCode> for SignalCodeDto {
    fn from(code: SignalCode) -> Self {
        Self {
            low: u64::from(code.low()),
            mid: u64::from(code.mid()),
            high: u64::from(code.high()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalConfigDto {
    target: SignalCodeDto,
    mission: MissionDto,
    reward: ContributionDto,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WorldStateDto {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    discovered_relics: Vec<u64>,
    beta_artifacts: Vec<ArtifactRefDto>,
    sequence: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReceiptKeyDto {
    federation_id: String,
    content_session: String,
    content_epoch: u64,
    player_key: String,
    player_counter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PlayerCounterRowDto {
    federation_id: String,
    content_session: String,
    content_epoch: u64,
    player_key: String,
    value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CanonStateDto {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    curator_key: String,
    world: WorldStateDto,
    known: Vec<ArtifactRefDto>,
    alpha: Vec<ArtifactRefDto>,
    superseded: Vec<ArtifactRefDto>,
    consumed_runs: Vec<ReceiptKeyDto>,
    player_counters: Vec<PlayerCounterRowDto>,
    revision: u64,
    curator_counter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FinalizedCarrierDto {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    actor_root: String,
    player_key: String,
    current_player_counter: u64,
}

/// Node-held slot state: the curator's per-slot secret, the slot it belongs to,
/// and the commitment the curator published before the slot opened.
///
/// ⚠ This is NODE state, never client state. The judge is handed the secret
/// because it RE-DERIVES the run seed rather than trusting one: `admissionChecks`
/// requires `commitment = HiddenInstance.commit secret slot` and the live
/// `run_seed` to be `HiddenInstance.runSeedFor` of that same secret, slot and
/// player. A node that published one commitment and judged against a different
/// secret is refused.
///
/// The secret must not leave the node. No output wire, descriptor or catalog
/// renders it, and `Emit` has no function that could.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SlotStateDto {
    slot: u64,
    secret: String,
    commitment: String,
}

/// ⚠ `run_seed` is GONE from the request. A client that could state the live run
/// seed could compute its own instance, which is the whole hole. What a client
/// states instead is the slot it played in and the commitment its run opening
/// showed it; the judge compares both against node state and derives the seed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalRequestDto {
    mission_id: u64,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    slot: u64,
    slot_commitment: String,
    actor_root: String,
    player_key: String,
    previous_player_counter: u64,
    expected_world_sequence: u64,
    expected_canon_revision: u64,
    actions: Vec<SignalCodeDto>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalInputDto {
    format: String,
    config: SignalConfigDto,
    world: WorldStateDto,
    canon: CanonStateDto,
    carrier: FinalizedCarrierDto,
    slot_state: SlotStateDto,
    request: SignalRequestDto,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalReceiptDto {
    mission: MissionDto,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    actor_root: String,
    player_key: String,
    previous_player_counter: u64,
    player_counter: u64,
    run_seed: String,
    pre_world: WorldStateDto,
    post_world: WorldStateDto,
    contribution: ContributionDto,
    transcript_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalOutputDto {
    format: String,
    receipt: SignalReceiptDto,
    successor_world: WorldStateDto,
    successor_canon: CanonStateDto,
}

fn validate_input(input: &SignalInputDto) -> Result<(), SignalAdapterError> {
    if input.format != SIGNAL_INPUT_FORMAT {
        return Err(SignalAdapterError::InvalidField("input format"));
    }
    validate_config(&input.config)?;
    validate_world(&input.world)?;
    validate_canon(&input.canon)?;
    validate_carrier(&input.carrier)?;
    validate_slot_state(&input.slot_state)?;
    validate_request(&input.request)?;
    // The client states the slot it played in and the commitment its opening
    // showed it; both must name the node's own slot state. The judge enforces
    // this too (`claim.slot = active.slot`, `claim.slotCommitment =
    // active.slotCommitment`); refusing here means a mismatch never reaches it.
    if input.request.slot != input.slot_state.slot
        || input.request.slot_commitment != input.slot_state.commitment
    {
        return Err(SignalAdapterError::InvalidField("request slot binding"));
    }
    Ok(())
}

fn validate_output(output: &SignalOutputDto) -> Result<(), SignalAdapterError> {
    if output.format != SIGNAL_OUTPUT_FORMAT {
        return Err(SignalAdapterError::InvalidField("output format"));
    }
    validate_mission(&output.receipt.mission)?;
    for (name, digest) in [
        ("receipt federation_id", &output.receipt.federation_id),
        ("receipt content_root", &output.receipt.content_root),
        (
            "receipt activation_digest",
            &output.receipt.activation_digest,
        ),
        ("receipt content_session", &output.receipt.content_session),
        ("receipt actor_root", &output.receipt.actor_root),
        ("receipt player_key", &output.receipt.player_key),
        ("receipt run_seed", &output.receipt.run_seed),
        (
            "receipt transcript_digest",
            &output.receipt.transcript_digest,
        ),
    ] {
        validate_digest(name, digest)?;
    }
    validate_world(&output.receipt.pre_world)?;
    validate_world(&output.receipt.post_world)?;
    validate_contribution(&output.receipt.contribution)?;
    validate_world(&output.successor_world)?;
    validate_canon(&output.successor_canon)
}

/// Transport binding only: this checks copies/equalities the Lean output is
/// required to preserve, without reimplementing its game or Canon transition.
fn validate_evaluation_binding(
    input: &SignalInputDto,
    output: &SignalOutputDto,
) -> Result<(), SignalAdapterError> {
    let request = &input.request;
    let receipt = &output.receipt;
    let bindings_hold = receipt.mission == input.config.mission
        && receipt.mission.mission_id == request.mission_id
        && receipt.federation_id == request.federation_id
        && receipt.content_root == request.content_root
        && receipt.activation_digest == request.activation_digest
        && receipt.content_session == request.content_session
        && receipt.content_epoch == request.content_epoch
        && receipt.actor_root == request.actor_root
        && receipt.player_key == request.player_key
        && receipt.previous_player_counter == request.previous_player_counter
        && receipt.player_counter.checked_sub(1) == Some(request.previous_player_counter)
        // ⚠ The request no longer states a run seed, so this can no longer be a
        // request/receipt comparison. What the receipt reveals — the run is over
        // by then — must be exactly the instance the node served, which is the
        // one in the config it judged. That the config's seed is the derivation
        // from the committed secret is `Judged.admissionChecks`, in Lean.
        && receipt.run_seed == input.config.mission.run_seed
        && receipt.pre_world == input.world
        && output.successor_world == receipt.post_world
        && output.successor_canon.world == receipt.post_world
        && output.successor_canon.federation_id == input.canon.federation_id
        && output.successor_canon.content_root == input.canon.content_root
        && output.successor_canon.activation_digest == input.canon.activation_digest
        && output.successor_canon.content_session == input.canon.content_session
        && output.successor_canon.content_epoch == input.canon.content_epoch
        && output.successor_canon.curator_key == input.canon.curator_key
        && input.world.sequence.checked_add(1) == Some(output.successor_world.sequence)
        && input.canon.revision.checked_add(1) == Some(output.successor_canon.revision);
    if !bindings_hold {
        return Err(SignalAdapterError::OutputBinding(
            "receipt/successor does not preserve the exact judged input bindings",
        ));
    }
    Ok(())
}

fn validate_config(config: &SignalConfigDto) -> Result<(), SignalAdapterError> {
    validate_code(&config.target)?;
    validate_mission(&config.mission)?;
    validate_contribution(&config.reward)
}

fn validate_mission(mission: &MissionDto) -> Result<(), SignalAdapterError> {
    validate_id("mission mission_id", mission.mission_id)?;
    validate_artifact(&mission.artifact)?;
    validate_digest("mission federation_id", &mission.federation_id)?;
    validate_digest("mission content_root", &mission.content_root)?;
    validate_digest("mission activation_digest", &mission.activation_digest)?;
    validate_digest("mission content_session", &mission.content_session)?;
    validate_digest("mission run_seed", &mission.run_seed)?;
    validate_budget(&mission.budget)?;
    validate_sorted_ids(
        "mission allowed_relics",
        &mission.allowed_relics,
        MISSION_RELIC_LIMIT,
    )?;
    if !matches!(
        mission.privacy.as_str(),
        "public"
            | "operator-visible-hiding-fri"
            | "process-separated-threshold"
            | "independent-operator-threshold"
    ) {
        return Err(SignalAdapterError::InvalidField("mission privacy"));
    }
    if !matches!(
        mission.ballot.as_str(),
        "none"
            | "one-player-one-voice"
            | "one-wallet-one-voice"
            | "capped-choir"
            | "prediction-oracle"
    ) {
        return Err(SignalAdapterError::InvalidField("mission ballot"));
    }
    Ok(())
}

fn validate_artifact(artifact: &ArtifactRefDto) -> Result<(), SignalAdapterError> {
    validate_id("artifact mission_id", artifact.mission_id)?;
    validate_id("artifact artifact_id", artifact.artifact_id)?;
    validate_digest("artifact source_digest", &artifact.source_digest)?;
    validate_digest("artifact content_digest", &artifact.content_digest)
}

fn validate_budget(budget: &BudgetDto) -> Result<(), SignalAdapterError> {
    validate_metrics(
        budget.intel,
        budget.supplies,
        budget.cohesion,
        budget.influence,
        budget.score,
    )?;
    if budget.relics > RELIC_LIMIT as u64 {
        return Err(SignalAdapterError::InvalidField("budget relics"));
    }
    Ok(())
}

fn validate_contribution(contribution: &ContributionDto) -> Result<(), SignalAdapterError> {
    validate_metrics(
        contribution.intel,
        contribution.supplies,
        contribution.cohesion,
        contribution.influence,
        contribution.score,
    )?;
    validate_sorted_ids("contribution relics", &contribution.relics, RELIC_LIMIT)
}

fn validate_world(world: &WorldStateDto) -> Result<(), SignalAdapterError> {
    validate_metrics(
        world.intel,
        world.supplies,
        world.cohesion,
        world.influence,
        world.score,
    )?;
    validate_sorted_ids(
        "world discovered_relics",
        &world.discovered_relics,
        WORLD_RELIC_LIMIT,
    )?;
    validate_sorted_artifacts(
        "world beta_artifacts",
        &world.beta_artifacts,
        ARTIFACT_LIMIT,
    )
}

fn validate_canon(canon: &CanonStateDto) -> Result<(), SignalAdapterError> {
    for (name, digest) in [
        ("canon federation_id", &canon.federation_id),
        ("canon content_root", &canon.content_root),
        ("canon activation_digest", &canon.activation_digest),
        ("canon content_session", &canon.content_session),
        ("canon curator_key", &canon.curator_key),
    ] {
        validate_digest(name, digest)?;
    }
    validate_world(&canon.world)?;
    validate_sorted_artifacts("canon known", &canon.known, ARTIFACT_LIMIT)?;
    validate_sorted_artifacts("canon alpha", &canon.alpha, ARTIFACT_LIMIT)?;
    validate_sorted_artifacts("canon superseded", &canon.superseded, ARTIFACT_LIMIT)?;
    if canon.consumed_runs.len() > RECEIPT_LIMIT
        || !canon
            .consumed_runs
            .windows(2)
            .all(|pair| receipt_key(&pair[0]) < receipt_key(&pair[1]))
    {
        return Err(SignalAdapterError::InvalidField("canon consumed_runs"));
    }
    for receipt in &canon.consumed_runs {
        validate_digest("consumed federation_id", &receipt.federation_id)?;
        validate_digest("consumed content_session", &receipt.content_session)?;
        validate_digest("consumed player_key", &receipt.player_key)?;
    }
    if canon.player_counters.len() > COUNTER_LIMIT
        || !canon
            .player_counters
            .windows(2)
            .all(|pair| counter_key(&pair[0]) < counter_key(&pair[1]))
        || canon.player_counters.iter().any(|row| row.value == 0)
    {
        return Err(SignalAdapterError::InvalidField("canon player_counters"));
    }
    for row in &canon.player_counters {
        validate_digest("counter federation_id", &row.federation_id)?;
        validate_digest("counter content_session", &row.content_session)?;
        validate_digest("counter player_key", &row.player_key)?;
    }
    Ok(())
}

fn validate_carrier(carrier: &FinalizedCarrierDto) -> Result<(), SignalAdapterError> {
    for (name, digest) in [
        ("carrier federation_id", &carrier.federation_id),
        ("carrier content_root", &carrier.content_root),
        ("carrier activation_digest", &carrier.activation_digest),
        ("carrier content_session", &carrier.content_session),
        ("carrier actor_root", &carrier.actor_root),
        ("carrier player_key", &carrier.player_key),
    ] {
        validate_digest(name, digest)?;
    }
    Ok(())
}

/// Structural validation only. That the commitment is the commitment OF the
/// secret is a Lean predicate (`HiddenInstance.commit`) and is checked by the
/// judge, not restated here — Rust holds no second copy of that derivation.
fn validate_slot_state(slot_state: &SlotStateDto) -> Result<(), SignalAdapterError> {
    for (name, digest) in [
        ("slot_state secret", &slot_state.secret),
        ("slot_state commitment", &slot_state.commitment),
    ] {
        validate_digest(name, digest)?;
    }
    Ok(())
}

fn validate_request(request: &SignalRequestDto) -> Result<(), SignalAdapterError> {
    validate_id("request mission_id", request.mission_id)?;
    for (name, digest) in [
        ("request federation_id", &request.federation_id),
        ("request content_root", &request.content_root),
        ("request activation_digest", &request.activation_digest),
        ("request content_session", &request.content_session),
        ("request slot_commitment", &request.slot_commitment),
        ("request actor_root", &request.actor_root),
        ("request player_key", &request.player_key),
    ] {
        validate_digest(name, digest)?;
    }
    if request.actions.len() > SIGNAL_ACTION_LIMIT {
        return Err(SignalAdapterError::InvalidField("request actions"));
    }
    request.actions.iter().try_for_each(validate_code)
}

fn validate_code(code: &SignalCodeDto) -> Result<(), SignalAdapterError> {
    if code.low > SIGNAL_BAND_MAX || code.mid > SIGNAL_BAND_MAX || code.high > SIGNAL_BAND_MAX {
        return Err(SignalAdapterError::InvalidField("Signal code band"));
    }
    Ok(())
}

fn authority_context_from_persisted_head(
    head: &dregg_persist::PoaSignalHeadV1,
    slot: &dregg_persist::PoaInstalledSlotV1,
    active_federation_id: [u8; 32],
    player_key: [u8; 32],
    actor_root: [u8; 32],
) -> Result<SignalAuthorityContext, SignalAdapterError> {
    if head.authority_id() != active_federation_id {
        return Err(SignalAdapterError::InvalidField(
            "persisted head authority/federation",
        ));
    }
    if slot.envelope().statement().authority_id() != active_federation_id {
        return Err(SignalAdapterError::InvalidField(
            "installed slot authority/federation",
        ));
    }
    let config_bytes = std::str::from_utf8(head.config())
        .map_err(|_| SignalAdapterError::InvalidField("persisted config UTF-8"))?;
    let canon_bytes = std::str::from_utf8(head.canon())
        .map_err(|_| SignalAdapterError::InvalidField("persisted Canon UTF-8"))?;
    let config: SignalConfigDto = parse_exact(config_bytes, "persisted Signal config")?;
    let canon: CanonStateDto = parse_exact(canon_bytes, "persisted Signal Canon")?;
    validate_config(&config)?;
    validate_canon(&canon)?;

    let federation_id = dregg_types::hex_encode(&active_federation_id);
    if config.mission.federation_id != federation_id
        || canon.federation_id != federation_id
        || config.mission.content_root != canon.content_root
        || config.mission.activation_digest != canon.activation_digest
        || config.mission.content_session != canon.content_session
        || config.mission.epoch != canon.content_epoch
        || head.world_sequence() != canon.world.sequence
        || head.canon_revision() != canon.revision
    {
        return Err(SignalAdapterError::InvalidField(
            "persisted Signal namespace/head binding",
        ));
    }

    let player_key = dregg_types::hex_encode(&player_key);
    let current_player_counter = canon
        .player_counters
        .iter()
        .find(|row| {
            row.federation_id == canon.federation_id
                && row.content_session == canon.content_session
                && row.content_epoch == canon.content_epoch
                && row.player_key == player_key
        })
        .map(|row| row.value)
        .unwrap_or(0);
    let carrier = FinalizedCarrierDto {
        federation_id: canon.federation_id.clone(),
        content_root: canon.content_root.clone(),
        activation_digest: canon.activation_digest.clone(),
        content_session: canon.content_session.clone(),
        content_epoch: canon.content_epoch,
        actor_root: dregg_types::hex_encode(&actor_root),
        player_key,
        current_player_counter,
    };
    validate_carrier(&carrier)?;
    if slot.mission_id() != config.mission.mission_id {
        return Err(SignalAdapterError::InvalidField(
            "installed slot names another mission",
        ));
    }
    let slot_state = SlotStateDto {
        slot: slot.slot(),
        secret: dregg_types::hex_encode(&slot.secret()),
        commitment: dregg_types::hex_encode(&slot.commitment()),
    };
    validate_slot_state(&slot_state)?;
    Ok(SignalAuthorityContext {
        config,
        world: canon.world.clone(),
        canon,
        carrier,
        slot_state,
    })
}

fn validate_metrics(
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
) -> Result<(), SignalAdapterError> {
    if [intel, supplies, cohesion, influence, score]
        .into_iter()
        .any(|value| value > METRIC_LIMIT)
    {
        return Err(SignalAdapterError::InvalidField("metric"));
    }
    Ok(())
}

fn validate_id(name: &'static str, id: u64) -> Result<(), SignalAdapterError> {
    if id > u64::from(u32::MAX) {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn validate_digest(name: &'static str, digest: &str) -> Result<(), SignalAdapterError> {
    if digest.len() != 64
        || !digest
            .as_bytes()
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn validate_sorted_ids(
    name: &'static str,
    ids: &[u64],
    limit: usize,
) -> Result<(), SignalAdapterError> {
    if ids.len() > limit
        || ids.iter().any(|id| *id > u64::from(u32::MAX))
        || !ids.windows(2).all(|pair| pair[0] < pair[1])
    {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn validate_sorted_artifacts(
    name: &'static str,
    artifacts: &[ArtifactRefDto],
    limit: usize,
) -> Result<(), SignalAdapterError> {
    for artifact in artifacts {
        validate_artifact(artifact)?;
    }
    if artifacts.len() > limit
        || !artifacts
            .windows(2)
            .all(|pair| artifact_key(&pair[0]) < artifact_key(&pair[1]))
    {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn artifact_key(artifact: &ArtifactRefDto) -> (u64, u64, &str, &str) {
    (
        artifact.mission_id,
        artifact.artifact_id,
        &artifact.source_digest,
        &artifact.content_digest,
    )
}

fn receipt_key(receipt: &ReceiptKeyDto) -> (&str, &str, u64, &str, u64) {
    (
        &receipt.federation_id,
        &receipt.content_session,
        receipt.content_epoch,
        &receipt.player_key,
        receipt.player_counter,
    )
}

/// Exact genesis material shared by the node finality integration tests.
/// Keeping this here makes the test exercise the same private DTO validation
/// and canonical serialization as the production persisted-head adapter.
#[cfg(test)]
/// The frozen fixture's own slot state, as an installed slot.
///
/// ⚠ Built with `new_for_test`, so it carries NO curator signature and NO Lean
/// commitment check. It reproduces the slot state the fixture was judged against so
/// finality tests can reach the adapter; it is not evidence that a slot was opened,
/// and nothing outside a test may build one this way.
pub(crate) fn fixture_signal_slot_for_finality_test(
    authority_id: [u8; 32],
) -> dregg_persist::PoaInstalledSlotV1 {
    let bytes = include_str!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json")
        .strip_suffix('\n')
        .expect("PoA Signal fixture has one trailing newline");
    let input = CanonicalSignalInput::parse(bytes).expect("canonical PoA Signal input fixture");
    let hex32 = |value: &str| {
        dregg_types::parse_hex32(value).expect("fixture digest is 32 bytes of lowercase hex")
    };
    let statement = dregg_persist::PoaSlotOpeningStatementV1::new(
        authority_id,
        input.dto.config.mission.mission_id,
        input.dto.slot_state.slot,
        hex32(&input.dto.slot_state.commitment),
    );
    dregg_persist::PoaInstalledSlotV1::new_for_test(
        dregg_persist::SignedPoaSlotOpeningEnvelopeV1::new(statement, [0u8; 32], [0u8; 64]),
        hex32(&input.dto.slot_state.secret),
    )
}

/// The claim that SOLVES the instance this exact context draws.
///
/// ⚠ There is no longer any such thing as "the answer to mission 1". The run seed
/// is `runSeedFor ⟨secret, slot, playerKey⟩ ctx`, so the target moves with the
/// federation, the content session, the slot, the secret AND the player. A test
/// that hardcodes a code can only solve the one context that code was copied from,
/// and every other context it is pointed at fails as `LeanRejected` — which reads
/// like a broken judge and is actually the split working.
///
/// So tests ask Lean what the answer is, exactly as the node does. This is not a
/// leak: the caller must already hold the slot secret to get here, and holding the
/// secret is what knowing the instance MEANS.
///
/// Requires the derivation export; panics if absent, because a test that silently
/// stopped checking the judge would be worse than one that stops.
///
/// This is [`derive_operator_instance`] with its refusals turned into panics — ONE
/// derivation, so the operator command an operator will actually run and the test
/// that proved the milestone cannot draw different answers.
///
/// ⚠ The claim it returns is a ONE-ROUND transcript, and since the transcript gate
/// landed that is not by itself settleable: the caller must also have PLAYED that
/// one round through `session/guess`, or the node refuses it as
/// [`UnplayedTranscriptV1::NoSession`]. A test that derives the answer and submits
/// it without playing is exactly the blind path, and it is now supposed to fail.
pub(crate) fn solving_claim_for_finality_test(
    head: &dregg_persist::PoaSignalHeadV1,
    slot: &dregg_persist::PoaInstalledSlotV1,
    active_federation_id: [u8; 32],
    player_key: [u8; 32],
    actor_root: [u8; 32],
) -> SignalClaimV1 {
    let instance =
        derive_operator_instance(head, slot, active_federation_id, player_key, actor_root)
            .expect("Lean must derive the fixture instance");
    SignalClaimV1::new(instance.mission_id, &[instance.target])
        .expect("a derived claim is a legal claim")
}

/// PLAY a judged session against the real store, through the real Lean oracle.
///
/// ⚠ THE CLASSIFICATIONS ARE THE NODE'S OWN. This calls
/// [`classify_session_guess`] — the same function `POST …/session/guess` calls —
/// and commits each round with [`dregg_persist::PersistentStore::record_poa_signal_session_round_v1`],
/// so a fixture built here is indistinguishable from one a player produced over
/// HTTP. It skips exactly one thing: the Ed25519 proof of possession, which is
/// transport authentication and has its own tests.
///
/// A fabricated session — rounds inserted with hand-written `exact`/`present` —
/// would let a finality fixture pass the transcript gate while disagreeing with
/// the rule, which is the one thing this gate exists to notice.
#[cfg(test)]
pub(crate) fn play_session_for_test(
    store: &dregg_persist::PersistentStore,
    head: &dregg_persist::PoaSignalHeadV1,
    slot: &dregg_persist::PoaInstalledSlotV1,
    active_federation_id: [u8; 32],
    player_key: [u8; 32],
    transcript: &[SignalCode],
) {
    store
        .open_poa_signal_session_v1(
            head.authority_id(),
            slot.slot(),
            slot.mission_id(),
            player_key,
            slot.commitment(),
        )
        .expect("a judged session opens");
    for guess in transcript {
        let classification =
            classify_session_guess(head, slot, active_federation_id, player_key, *guess)
                .expect("the Lean feedback oracle must classify a fixture guess");
        store
            .record_poa_signal_session_round_v1(
                head.authority_id(),
                slot.slot(),
                player_key,
                dregg_persist::PoaSignalSessionRoundV1 {
                    guess: [guess.low(), guess.mid(), guess.high()],
                    exact: classification.exact,
                    present: classification.present,
                },
            )
            .expect("the round commits")
            .expect("the round is within budget");
    }
}

pub(crate) fn fixture_signal_head_for_finality_test(
    authority_id: [u8; 32],
) -> dregg_persist::PoaSignalHeadV1 {
    let bytes = include_str!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json")
        .strip_suffix('\n')
        .expect("PoA Signal fixture has one trailing newline");
    let mut input = CanonicalSignalInput::parse(bytes).expect("canonical PoA Signal input fixture");
    let authority_hex = dregg_types::hex_encode(&authority_id);
    input.dto.config.mission.federation_id = authority_hex.clone();
    input.dto.canon.federation_id = authority_hex;
    dregg_persist::PoaSignalHeadV1::genesis(
        authority_id,
        [0xD3; 32],
        input.dto.canon.world.sequence,
        input.dto.canon.revision,
        serde_json::to_vec(&input.dto.config).expect("canonical fixture config"),
        serde_json::to_vec(&input.dto.canon).expect("canonical fixture Canon"),
    )
    .expect("valid fixture PoA Signal head")
}

fn counter_key(row: &PlayerCounterRowDto) -> (&str, &str, u64, &str) {
    (
        &row.federation_id,
        &row.content_session,
        row.content_epoch,
        &row.player_key,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::finality::{Block, Payload};
    use dregg_cell::{CellId, field_from_u64};
    use dregg_persist::{CommitRecord, PersistentStore, PreparedPoaSignalTransitionV1};
    use dregg_sdk::poa_signal::{SIGNAL_CLAIM_TOPIC_V1, signal_claim_event};
    use dregg_turn::action::{Event, symbol};
    use zeroize::Zeroizing;

    const INPUT_FILE: &str =
        include_str!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json");
    const OUTPUT_FILE: &str =
        include_str!("../../dregg-lean-ffi/tests/fixtures/poa-signal-output-v1.json");

    fn fixture(bytes: &'static str) -> &'static str {
        bytes.strip_suffix('\n').expect("one fixture newline")
    }

    /// The SOLVING claim for the committed fixture.
    ///
    /// ⚠ This was `(2, 4, 1)` — the old `Emit.signalTarget_literal`, back when the
    /// run seed was a published constant and every mission had one answer forever.
    /// The fixture's instance is now drawn from its slot secret, and its target is
    /// `targetFromSeed(d15ad7b7…)` = `(5, 0, 5)`: `0xd1 % 6 = 5`, `0x5a % 6 = 0`,
    /// `0xd7 % 6 = 5`.
    ///
    /// Nothing here is a leak. This is a test fixture whose secret is committed, so
    /// its answer is computable BY ANYONE HOLDING THAT SECRET — which is exactly the
    /// property the split preserves, and exactly why no real slot secret may ever be
    /// checked in.
    fn claim() -> SignalClaimV1 {
        SignalClaimV1::new(1, &[SignalCode::new(5, 0, 5).unwrap()]).unwrap()
    }

    fn hex32(value: &str) -> [u8; 32] {
        assert_eq!(value.len(), 64);
        let mut out = [0; 32];
        for (index, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
        }
        out
    }

    fn fixture_head() -> dregg_persist::PoaSignalHeadV1 {
        let input = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        fixture_signal_head_for_finality_test(hex32(&input.dto.canon.federation_id))
    }

    fn fixture_slot(authority_id: [u8; 32]) -> dregg_persist::PoaInstalledSlotV1 {
        fixture_signal_slot_for_finality_test(authority_id)
    }

    /// ⚠ THE KEY-ORDER GATE.
    ///
    /// `SlotDeriveRuntime.decodeRequest` is `canonicalDecode parseRequestJson
    /// Request.toJson`: Lean re-encodes what it parsed and compares BYTES, so a
    /// request whose keys are in any other order is refused and every scored Signal
    /// run dies as `LeanRejected`. Nothing else in the Rust test suite would notice
    /// — the value is identical, only the spelling moves — so this asserts the
    /// spelling against a LITERAL rather than against a re-serialization of itself.
    ///
    /// A pin against its own definition is decoration; the second source here is
    /// the key order written out in `SlotDeriveRuntime.lean:114-122`, transcribed
    /// by hand.
    ///
    /// This is the test that would have caught the `serde_json::json!` bomb: `json!`
    /// preserved insertion order only because `preserve_order` was on by feature
    /// unification, and NOTHING in this workspace declares it. Had an unrelated
    /// crate dropped that feature, `json!` would have serialized alphabetically —
    /// `content_session` first, `slot` last — and this assertion is what turns that
    /// into a named failure instead of a dead game.
    #[test]
    fn slot_derive_request_is_the_exact_pinned_wire() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let wire = slot_derive_request_wire(&context).unwrap();

        assert_eq!(
            wire,
            concat!(
                r#"{"format":"POA-SLOT-DERIVE-1""#,
                r#","slot":9"#,
                r#","secret":"7777777777777777777777777777777777777777777777777777777777777777""#,
                r#","mission_id":1"#,
                r#","epoch":1"#,
                r#","federation_id":"4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a""#,
                r#","content_session":"504f412d5349472d310000000000000000000000000000000000000000000000""#,
                r#","player_key":"5555555555555555555555555555555555555555555555555555555555555555"}"#,
            ),
            "the slot-derive request wire changed; Lean's canonicalDecode compares \
             BYTES against Request.toJson, so this is a total Signal outage, not a \
             formatting nit"
        );
    }

    /// The order gate above is only worth having if a reordered wire is actually
    /// refused. This asserts the CONSEQUENCE against the real export, so the gate
    /// measures a live property rather than a belief about one.
    ///
    /// ⚠ Not covered by `dregg-lean-ffi/tests/poa_slot_derive_probe.rs`'s
    /// `transposed_keys_are_refused`, despite the name: that one INSERTS a
    /// `secret_placeholder` key, so it is refused by `exactKeys` on the key SET and
    /// would still pass if `canonicalDecode`'s byte-comparison seal were deleted.
    /// This case keeps the key set identical and moves only the ORDER, which is the
    /// property the whole field-order discipline rests on.
    ///
    /// It also binds the wire this module actually BUILDS to the live export —
    /// accepted, not merely well-shaped.
    ///
    /// Skipped (not silently passed) when the archive lacks the export.
    #[test]
    fn a_reordered_slot_derive_request_is_refused_by_lean() {
        if !dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available() {
            eprintln!("skipped: dregg_poa_signal_slot_derive is not in the linked archive");
            return;
        }
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let honest = slot_derive_request_wire(&context).unwrap();
        assert!(
            dregg_lean_ffi::poa_slot_derive_ffi::derive_poa_slot_instance(&honest)
                .unwrap()
                .is_some(),
            "the pinned wire must be accepted, or this test proves nothing"
        );

        // Same values, alphabetical keys — exactly what `json!` would emit if
        // `preserve_order` were ever unified away.
        let alphabetical = concat!(
            r#"{"content_session":"504f412d5349472d310000000000000000000000000000000000000000000000""#,
            r#","epoch":1"#,
            r#","federation_id":"4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a""#,
            r#","format":"POA-SLOT-DERIVE-1""#,
            r#","mission_id":1"#,
            r#","player_key":"5555555555555555555555555555555555555555555555555555555555555555""#,
            r#","secret":"7777777777777777777777777777777777777777777777777777777777777777""#,
            r#","slot":9}"#,
        );
        assert_eq!(
            dregg_lean_ffi::poa_slot_derive_ffi::derive_poa_slot_instance(alphabetical).unwrap(),
            None,
            "Lean accepted a reordered request; the canonical seal is not order-sensitive \
             and the key-order gate above is decoration"
        );
    }

    /// The classification wire has the same order discipline and the same consequence
    /// for getting it wrong: a reordered wire is refused, which surfaces as every
    /// judged guess failing.
    #[test]
    fn signal_feedback_request_is_the_exact_pinned_wire() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let guess = SignalCode::new(0, 1, 2).unwrap();
        let wire = signal_feedback_request_wire(&context, guess).unwrap();

        assert_eq!(
            wire,
            concat!(
                r#"{"format":"POA-SIGNAL-FEEDBACK-1""#,
                r#","slot":9"#,
                r#","secret":"7777777777777777777777777777777777777777777777777777777777777777""#,
                r#","mission_id":1"#,
                r#","epoch":1"#,
                r#","federation_id":"4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a""#,
                r#","content_session":"504f412d5349472d310000000000000000000000000000000000000000000000""#,
                r#","player_key":"5555555555555555555555555555555555555555555555555555555555555555""#,
                r#","commitment":"bc7742888f4ed90ace371abf4b0be7dec5e22d47723bcfd01903a8aa2332a491""#,
                r#","guess":{"low":0,"mid":1,"high":2}}"#,
            ),
            "the Signal feedback request wire changed; Lean's canonicalDecode compares \
             BYTES against Request.toJson, so this is a total judged-session outage, not \
             a formatting nit"
        );
    }

    /// ⚑ The classification wire's first eight fields are the DERIVATION wire's, field
    /// for field and byte for byte. That is what makes a served classification a
    /// classification about the instance that will SETTLE, rather than about a second
    /// instance the session happens to agree with today. Lean proves the same weld
    /// (`SignalFeedbackRuntime.request_derives_the_judged_instance`, `rfl`); this is the
    /// host-side half, over the bytes this module actually builds.
    #[test]
    fn the_feedback_wire_is_the_derivation_wire_plus_a_commitment_and_a_guess() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let derive = slot_derive_request_wire(&context).unwrap();
        let feedback =
            signal_feedback_request_wire(&context, SignalCode::new(0, 1, 2).unwrap()).unwrap();

        let derive_body = derive
            .strip_prefix(r#"{"format":"POA-SLOT-DERIVE-1","#)
            .and_then(|rest| rest.strip_suffix('}'))
            .expect("the derivation wire shape changed");
        let feedback_body = feedback
            .strip_prefix(r#"{"format":"POA-SIGNAL-FEEDBACK-1","#)
            .expect("the feedback wire shape changed");
        assert!(
            feedback_body.starts_with(derive_body),
            "the feedback wire no longer begins with the derivation wire's exact eight \
             fields, so the two exports can be about DIFFERENT instances:\n  derive: \
             {derive_body}\n  feedback: {feedback_body}"
        );
    }

    /// ⚠ The wire carries no actor root. `SESSION_UNREAD_ACTOR_ROOT` is threaded through
    /// `authority_context_from_persisted_head` only because that is where the
    /// head/Canon/slot bindings are checked; if it ever reached the bytes it would be a
    /// zeroed field a client could mistake for a real one.
    #[test]
    fn the_feedback_wire_does_not_carry_an_actor_root() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let wire =
            signal_feedback_request_wire(&context, SignalCode::new(0, 1, 2).unwrap()).unwrap();
        assert!(!wire.contains("actor_root"));
        assert!(!wire.contains(&dregg_types::hex_encode(&SESSION_UNREAD_ACTOR_ROOT)));
    }

    /// The pinned wire is ACCEPTED by the live export and a reordered one is REFUSED,
    /// so the order gate above measures a live property rather than a belief.
    ///
    /// Skipped (not silently passed) when the archive lacks the export.
    #[test]
    fn a_reordered_feedback_request_is_refused_by_lean() {
        if !dregg_lean_ffi::poa_signal_feedback_ffi::poa_signal_feedback_available() {
            eprintln!("skipped: dregg_poa_signal_feedback is not in the linked archive");
            return;
        }
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let honest =
            signal_feedback_request_wire(&context, SignalCode::new(0, 1, 2).unwrap()).unwrap();
        assert!(
            dregg_lean_ffi::poa_signal_feedback_ffi::classify_poa_signal_guess(&honest)
                .unwrap()
                .is_some(),
            "the pinned wire must be accepted, or this test proves nothing"
        );

        let alphabetical = concat!(
            r#"{"commitment":"bc7742888f4ed90ace371abf4b0be7dec5e22d47723bcfd01903a8aa2332a491""#,
            r#","content_session":"504f412d5349472d310000000000000000000000000000000000000000000000""#,
            r#","epoch":1"#,
            r#","federation_id":"4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a""#,
            r#","format":"POA-SIGNAL-FEEDBACK-1""#,
            r#","guess":{"high":2,"low":0,"mid":1}"#,
            r#","mission_id":1"#,
            r#","player_key":"5555555555555555555555555555555555555555555555555555555555555555""#,
            r#","secret":"7777777777777777777777777777777777777777777777777777777777777777""#,
            r#","slot":9}"#,
        );
        assert_eq!(
            dregg_lean_ffi::poa_signal_feedback_ffi::classify_poa_signal_guess(alphabetical)
                .unwrap(),
            None,
            "Lean accepted a reordered feedback request; the canonical seal is not \
             order-sensitive and the key-order gate above is decoration"
        );
    }

    /// ⚑ THE ORACLE AGREES WITH THE JUDGE ON THIS FIXTURE'S INSTANCE. The solving code
    /// `evaluate_signal_claim` settles with is exactly the code the oracle answers
    /// `exact: 3` to — and the oracle's answer for a losing guess is a real
    /// classification, not a constant.
    ///
    /// This is the one place the two Lean exports are compared on the SAME context, and
    /// it is worth the fixture: a session that classified against a different instance
    /// than the judge scores would teach a player the wrong answer and then refuse it.
    ///
    /// Skipped (not silently passed) when the archive lacks either export.
    #[test]
    fn the_oracle_and_the_judge_agree_on_the_fixture_instance() {
        if !dregg_lean_ffi::poa_signal_feedback_ffi::poa_signal_feedback_available()
            || !dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available()
        {
            eprintln!("skipped: a PoA Signal export is not in the linked archive");
            return;
        }
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();

        let classify = |code: SignalCode| {
            let wire = signal_feedback_request_wire(&context, code).unwrap();
            dregg_lean_ffi::poa_signal_feedback_ffi::classify_poa_signal_guess(&wire)
                .unwrap()
                .expect("the pinned wire must be accepted")
        };

        // `solving_claim`'s code: the fixture's `targetFromSeed(d15ad7b7…)` = (5, 0, 5).
        assert_eq!(
            classify(SignalCode::new(5, 0, 5).unwrap()),
            r#"{"format":"POA-SIGNAL-FEEDBACK-OUT-1","exact":3,"present":0}"#,
            "the code the judge settles must LOCK all three bands on the oracle"
        );
        assert_ne!(
            classify(SignalCode::new(0, 1, 2).unwrap()),
            classify(SignalCode::new(5, 0, 5).unwrap()),
            "the oracle answers every guess the same; it is not classifying"
        );
    }

    #[derive(Clone, Copy)]
    enum StoredSemanticCorruption {
        None,
        Input,
        Output,
        Successor,
    }

    fn persisted_semantic_fixture(
        corruption: StoredSemanticCorruption,
    ) -> (PersistentStore, [u8; 32], [u8; 32]) {
        populate_persisted_semantic_fixture(PersistentStore::open_in_memory().unwrap(), corruption)
    }

    fn populate_persisted_semantic_fixture(
        store: PersistentStore,
        corruption: StoredSemanticCorruption,
    ) -> (PersistentStore, [u8; 32], [u8; 32]) {
        assert!(
            dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
            "semantic persistence tests require the native Lean Signal judge"
        );
        let authority = fixture_head().authority_id();
        let head = fixture_signal_head_for_finality_test(authority);
        store.initialize_poa_signal_head(&head).unwrap();
        // The replay path loads the slot from the STORE rather than trusting the
        // journal's copy, so a fixture must actually open one.
        store
            .install_poa_signal_slot_for_test(&fixture_slot(authority))
            .unwrap();

        let clerk = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0x31; 32]));
        let actor_root = [0x44; 32];
        // ⚠ Derived BEFORE the turn is built. The replay reconstructs the judge
        // input from the finalized turn's claim and compares BYTES, so the turn and
        // the stored input must carry the same code. The instance depends on the
        // PLAYER, and this fixture plays as `clerk`, not as the committed fixture's
        // `5555…`, so the answer is asked for rather than written down.
        let claim = solving_claim_for_finality_test(
            &head,
            &fixture_slot(authority),
            authority,
            clerk.public_key().0,
            actor_root,
        );
        let turn = dregg_sdk::poa_signal::signal_claim_turn(&clerk.public_key().0, 0, None, claim);
        let signed = clerk.sign_turn(&turn);
        let context = authority_context_from_persisted_head(
            &head,
            &fixture_slot(authority),
            authority,
            clerk.public_key().0,
            actor_root,
        )
        .unwrap();
        let evaluated = evaluate_signal_claim(&context, claim).unwrap();
        let mut stored_input = evaluated.input.dto.clone();
        let mut stored_output = evaluated.output.dto.clone();
        let mut successor_canon = evaluated.output.dto.successor_canon.clone();
        match corruption {
            StoredSemanticCorruption::None => {}
            StoredSemanticCorruption::Input => {
                stored_input.request.actions[0].low =
                    (stored_input.request.actions[0].low + 1) % (SIGNAL_BAND_MAX + 1);
            }
            StoredSemanticCorruption::Output => {
                stored_output.receipt.post_world.score += 1;
                stored_output.successor_world.score += 1;
                stored_output.successor_canon.world.score += 1;
                successor_canon = stored_output.successor_canon.clone();
            }
            StoredSemanticCorruption::Successor => {
                successor_canon.curator_counter += 1;
            }
        }
        let input_bytes = serde_json::to_vec(&stored_input).unwrap();
        let output_bytes = serde_json::to_vec(&stored_output).unwrap();
        let successor_bytes = serde_json::to_vec(&successor_canon).unwrap();
        let candidate = PreparedPoaSignalTransitionV1::new_for_test(
            authority,
            head.digest(),
            stored_output.successor_world.sequence,
            stored_output.successor_canon.revision,
            successor_bytes,
            input_bytes,
            output_bytes,
        )
        .unwrap();

        let receipt = dregg_turn::TurnReceipt {
            turn_hash: signed.turn.hash(),
            pre_state_hash: actor_root,
            agent: signed.turn.agent,
            federation_id: authority,
            ..Default::default()
        };
        let receipt_hash = receipt.receipt_hash();
        let signed_bytes = postcard::to_stdvec(&signed).unwrap();
        let block = Block {
            creator: [0x81; 32],
            ed25519: [0x82; 32],
            seq: 1,
            payload: Payload::Turn(signed_bytes),
            predecessors: Vec::new(),
            signature: [0; 64],
            pq_signature: Vec::new(),
        };
        let record = CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: block.id().0,
            block_executed_up_to: 1,
            turn_hash: signed.turn.hash(),
            creator: *signed.turn.agent.as_bytes(),
            receipt_hash,
            ledger_root: [0x91; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        store.persist_block(&block).unwrap();
        store
            .append_receipt_chain_entry(0, &postcard::to_stdvec(&receipt).unwrap())
            .unwrap();
        store
            .commit_finalized_turn_with_poa_signal_for_test(0, &record, &candidate)
            .unwrap();
        let genesis_digest = head.digest();
        (store, authority, genesis_digest)
    }

    #[test]
    fn reserved_route_is_exact_and_malformed_is_irrevocable() {
        let event = signal_claim_event(claim());
        let effect = Effect::EmitEvent {
            cell: CellId::from_bytes([9; 32]),
            event,
        };
        assert_eq!(
            classify_signal_effect(&effect),
            Ok(SignalEffectRoute::Signal(claim()))
        );

        let malformed = Effect::EmitEvent {
            cell: CellId::from_bytes([9; 32]),
            event: Event::new(symbol(SIGNAL_CLAIM_TOPIC_V1), vec![field_from_u64(1)]),
        };
        assert!(matches!(
            classify_signal_effect(&malformed),
            Err(SignalAdapterError::Claim(
                SignalClaimError::MalformedReserved(_)
            ))
        ));
    }

    #[test]
    fn canonical_dtos_round_trip_exactly_and_reject_reordering() {
        let input = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        assert_eq!(input.as_str(), fixture(INPUT_FILE));
        let output = CanonicalSignalOutput::parse(fixture(OUTPUT_FILE)).unwrap();
        assert_eq!(output.as_str(), fixture(OUTPUT_FILE));

        let reordered = fixture(INPUT_FILE).replacen(
            "{\"format\":\"POA-SIGNAL-IN-1\",\"config\":",
            "{\"config\":",
            1,
        );
        let reordered =
            reordered.replacen("\"world\":", "\"format\":\"POA-SIGNAL-IN-1\",\"world\":", 1);
        assert!(matches!(
            CanonicalSignalInput::parse(&reordered),
            Err(SignalAdapterError::Noncanonical(_))
        ));
    }

    #[test]
    fn public_claim_cannot_substitute_authority_fields() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let prepared = prepare_signal_input(&context, claim()).unwrap();
        let request = &prepared.dto.request;

        assert_eq!(request.federation_id, context.carrier.federation_id);
        assert_eq!(request.content_root, context.carrier.content_root);
        assert_eq!(request.activation_digest, context.carrier.activation_digest);
        assert_eq!(request.content_session, context.carrier.content_session);
        assert_eq!(request.content_epoch, context.carrier.content_epoch);
        assert_eq!(request.actor_root, context.carrier.actor_root);
        assert_eq!(request.player_key, context.carrier.player_key);
        assert_eq!(
            request.previous_player_counter,
            context.carrier.current_player_counter
        );
        // ⚠ The request no longer states a run seed — that was the hole. What it
        // states about the instance is the slot it was played in and the commitment
        // the opening showed, and both must name the node's own slot state.
        assert_eq!(request.slot, context.slot_state.slot);
        assert_eq!(request.slot_commitment, context.slot_state.commitment);
        assert_eq!(request.expected_world_sequence, context.world.sequence);
        assert_eq!(request.expected_canon_revision, context.canon.revision);
        assert_eq!(
            request.actions,
            claim()
                .transcript()
                .iter()
                .copied()
                .map(SignalCodeDto::from)
                .collect::<Vec<_>>(),
            "the judge is handed the WHOLE played transcript, not the solving code alone"
        );
        assert_eq!(prepared.as_str(), fixture(INPUT_FILE));
    }

    #[test]
    fn persisted_head_reconstructs_world_counter_and_finalized_identity_exactly() {
        let head = fixture_head();
        let context = authority_context_from_persisted_head(
            &head,
            &fixture_slot(head.authority_id()),
            head.authority_id(),
            [0x55; 32],
            [0x44; 32],
        )
        .unwrap();
        let prepared = prepare_signal_input(&context, claim()).unwrap();
        assert_eq!(prepared.as_str(), fixture(INPUT_FILE));

        let mismatched_projection = dregg_persist::PoaSignalHeadV1::genesis(
            head.authority_id(),
            head.deployment_digest(),
            head.world_sequence() + 1,
            head.canon_revision(),
            head.config().to_vec(),
            head.canon().to_vec(),
        )
        .unwrap();
        assert!(matches!(
            authority_context_from_persisted_head(
                &mismatched_projection,
                &fixture_slot(head.authority_id()),
                head.authority_id(),
                [0x55; 32],
                [0x44; 32],
            ),
            Err(SignalAdapterError::InvalidField(
                "persisted Signal namespace/head binding"
            ))
        ));
    }

    #[test]
    fn exact_output_parser_does_not_make_a_substituted_reply_acceptable() {
        let input = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let honest = CanonicalSignalOutput::parse(fixture(OUTPUT_FILE)).unwrap();
        validate_evaluation_binding(&input.dto, &honest.dto).unwrap();

        let mut substituted_dto = honest.dto.clone();
        substituted_dto.receipt.player_key = "ff".repeat(32);
        let substituted_bytes = serde_json::to_string(&substituted_dto).unwrap();
        let substituted = CanonicalSignalOutput::parse(&substituted_bytes)
            .expect("the transport parser alone is not semantic authority");
        assert!(matches!(
            validate_evaluation_binding(&input.dto, &substituted.dto),
            Err(SignalAdapterError::OutputBinding(_))
        ));
    }

    #[test]
    fn substituted_mission_refuses_before_ffi() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let other = SignalClaimV1::new(2, claim().transcript()).unwrap();
        assert!(matches!(
            prepare_signal_input(&context, other),
            Err(SignalAdapterError::MissionMismatch {
                claimed: 2,
                active: 1
            })
        ));
    }

    #[test]
    fn linked_lean_candidate_is_exact_but_not_committed() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
            "the internal PoA Signal judge export",
        ) {
            return;
        }
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let candidate = evaluate_signal_claim(&parsed.authority_context(), claim()).unwrap();
        assert_eq!(candidate.input().as_str(), fixture(INPUT_FILE));
        assert_eq!(candidate.output().as_str(), fixture(OUTPUT_FILE));

        let head = fixture_head();
        let prepared = evaluate_persisted_signal_claim(
            &head,
            &fixture_slot(head.authority_id()),
            head.authority_id(),
            [0x55; 32],
            [0x44; 32],
            claim(),
        )
        .unwrap();
        assert_ne!(prepared.judge_input_digest(), [0; 32]);
        assert_ne!(prepared.judge_output_digest(), [0; 32]);
    }

    #[test]
    fn semantic_replay_rebuilds_the_published_head_from_retained_genesis() {
        let (store, authority, genesis_digest) =
            persisted_semantic_fixture(StoredSemanticCorruption::None);
        let report = audit_persisted_signal_semantics_against_genesis(
            &store,
            authority,
            Some(genesis_digest),
        )
        .unwrap();
        assert_eq!(report.authority_id, authority);
        assert_eq!(report.transition_count, 1);
        assert_eq!(report.retained_genesis_digest, genesis_digest);
        assert_eq!(
            report.rebuilt_head_digest,
            store
                .load_poa_signal_head(authority)
                .unwrap()
                .unwrap()
                .digest()
        );
        assert!(
            audit_persisted_signal_semantics_against_genesis(&store, authority, Some([0xfe; 32]),)
                .unwrap_err()
                .to_string()
                .contains("independently expected digest")
        );
    }

    #[test]
    fn semantic_replay_survives_checkpoint_compaction_and_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("poa-signal-semantic-compaction.redb");
        let (store, authority, genesis_digest) = populate_persisted_semantic_fixture(
            PersistentStore::open(&path).unwrap(),
            StoredSemanticCorruption::None,
        );
        let survivor = CommitRecord {
            ordinal: 1,
            height: 2,
            block_id: [0xA1; 32],
            block_executed_up_to: 2,
            turn_hash: [0xA2; 32],
            creator: [0xA3; 32],
            receipt_hash: [0xA4; 32],
            ledger_root: [0x91; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        store.commit_finalized_turn(1, &survivor).unwrap();
        store
            .store_ledger_checkpoint_snapshot(&dregg_persist::LedgerCheckpoint {
                height: 2,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        crate::install_verified_pq_cores();
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(2).unwrap(), 1);
        assert!(store.commit_record_at(0).unwrap().is_none());
        drop(store);

        let reopened = PersistentStore::open_with_test_poa_compact_trust_v1(&path).unwrap();
        let report = audit_persisted_signal_semantics_against_genesis(
            &reopened,
            authority,
            Some(genesis_digest),
        )
        .unwrap();
        assert_eq!(report.transition_count, 1);
        assert_eq!(report.authority_id, authority);
        assert_eq!(report.retained_genesis_digest, genesis_digest);
    }

    /// The Records read is only as honest as the coordinates it publishes.
    /// This pins where each one comes from: the durable row for the commit
    /// coordinates, the finalized `SignedTurn` for `signer`, the durable
    /// receipt's `pre_state_hash` for `actor_root`, and the retained genesis
    /// for the blobs Lean folds from. None is re-derived from the judge input's
    /// own carrier — that carrier is what they exist to bind.
    #[test]
    fn semantic_replay_yields_the_finalized_material_the_records_read_needs() {
        let (store, authority, genesis_digest) =
            persisted_semantic_fixture(StoredSemanticCorruption::None);
        let replay =
            replay_persisted_signal_history(&store, authority, Some(genesis_digest)).unwrap();
        assert_eq!(replay.report.transition_count, 1);
        assert_eq!(replay.rows.len(), 1);

        let row = &replay.rows[0];
        assert_eq!(row.sequence, 1);
        assert_eq!(row.actor_root, [0x44; 32]);
        let clerk = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0x31; 32]));
        assert_eq!(row.signer, clerk.public_key().0);

        let stored = store
            .load_poa_signal_transition(authority, 1)
            .unwrap()
            .unwrap();
        assert_eq!(row.commit_ordinal, stored.commit_ordinal());
        assert_eq!(row.turn_hash, stored.turn_hash());
        assert_eq!(row.receipt_hash, stored.receipt_hash());
        assert_eq!(row.judge_input.as_bytes(), stored.judge_input());
        assert_eq!(row.judge_output.as_bytes(), stored.judge_output());

        let head = fixture_head();
        assert_eq!(replay.genesis_canon, head.canon().to_vec());
        assert_eq!(replay.genesis_config, head.config().to_vec());
    }

    #[test]
    fn semantic_replay_refuses_a_structurally_sealed_input_substitution() {
        let (store, authority, _) = persisted_semantic_fixture(StoredSemanticCorruption::Input);
        store
            .audit_poa_signal_state()
            .expect("structural hashes alone accept the coherently sealed row");
        let error = audit_persisted_signal_semantics(&store, authority)
            .unwrap_err()
            .to_string();
        assert!(error.contains("stored judge input"), "{error}");
    }

    #[test]
    fn semantic_replay_refuses_a_structurally_sealed_output_substitution() {
        let (store, authority, _) = persisted_semantic_fixture(StoredSemanticCorruption::Output);
        store
            .audit_poa_signal_state()
            .expect("structural hashes alone accept the coherently sealed row");
        let error = audit_persisted_signal_semantics(&store, authority)
            .unwrap_err()
            .to_string();
        assert!(error.contains("differs from native Lean replay"), "{error}");
    }

    #[test]
    fn semantic_replay_refuses_a_successor_not_derived_from_lean_output() {
        let (store, authority, _) = persisted_semantic_fixture(StoredSemanticCorruption::Successor);
        store
            .audit_poa_signal_state()
            .expect("structural hashes alone accept the coherently sealed row");
        let error = audit_persisted_signal_semantics(&store, authority)
            .unwrap_err()
            .to_string();
        assert!(error.contains("stored successor"), "{error}");
    }

    /// ⚑ THE JUDGE SCORES A MULTI-ROUND RUN, and its receipt binds the WHOLE
    /// transcript.
    ///
    /// Everything else in this module drives a one-round claim, because that is
    /// what the fixture holds and what a claim used to be able to carry. A real
    /// deduced run is two to five rounds, and until this ran there was no evidence
    /// at all that the linked judge accepts one — the whole gate would have been a
    /// door onto a wall.
    ///
    /// `SignalTriangulation.judge_receipt_binds_transcript` is the Lean statement;
    /// this is it observed on the served bytes, against the live export.
    #[test]
    fn the_linked_judge_scores_a_multi_round_transcript() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
            "the internal PoA Signal judge export",
        ) {
            return;
        }
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();

        let solving = SignalCode::new(5, 0, 5).unwrap();
        let three = [
            SignalCode::new(1, 1, 1).unwrap(),
            SignalCode::new(0, 0, 5).unwrap(),
            solving,
        ];
        let judged = evaluate_signal_claim(&context, SignalClaimV1::new(1, &three).unwrap())
            .expect("a three-round run ending in the solving guess must be judged");
        assert_eq!(judged.input().dto.request.actions.len(), 3);

        // The one-round claim of the same code is a DIFFERENT run and the receipt
        // says so: `transcriptDigest` commits to the whole list, so the two cannot
        // be confused after the fact.
        let one = evaluate_signal_claim(&context, SignalClaimV1::new(1, &[solving]).unwrap())
            .expect("the one-round run is still judged");
        assert_ne!(
            judged.output().dto.receipt.transcript_digest,
            one.output().dto.receipt.transcript_digest,
            "the receipt must bind the transcript, not only its last code"
        );

        // A run whose LAST round does not lock is refused by the rule, not by us.
        let unsolved = [three[0], three[1]];
        assert!(
            matches!(
                evaluate_signal_claim(&context, SignalClaimV1::new(1, &unsolved).unwrap()),
                Err(SignalAdapterError::LeanRejected)
            ),
            "an unsolved transcript must be refused by the judge"
        );

        // …and a run that keeps guessing AFTER it solved is refused too:
        // `SignalTriangulation.solved_refuses` says `step` returns none on a solved
        // state, so `replay` is fail-stop on the extra action.
        let past_the_end = [three[0], three[1], solving, three[0]];
        assert!(
            matches!(
                evaluate_signal_claim(&context, SignalClaimV1::new(1, &past_the_end).unwrap()),
                Err(SignalAdapterError::LeanRejected)
            ),
            "a transcript that continues past its solving round must be refused"
        );
    }

    // ── THE TRANSCRIPT-PROVENANCE GATE ──────────────────────────────────────────

    const GATE_PLAYER: [u8; 32] = [0x55; 32];

    fn code_of(bands: [u8; 3]) -> SignalCode {
        SignalCode::new(
            u64::from(bands[0]),
            u64::from(bands[1]),
            u64::from(bands[2]),
        )
        .expect("base-six bands")
    }

    /// A store holding one judged session for the fixture slot, with exactly the
    /// rounds and classifications given.
    fn gate_session(
        slot: &dregg_persist::PoaInstalledSlotV1,
        authority: [u8; 32],
        rounds: &[([u8; 3], u8, u8)],
    ) -> (tempfile::TempDir, dregg_persist::PoaSignalSessionV1) {
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("dregg.redb")).unwrap();
        let mut record = store
            .open_poa_signal_session_v1(
                authority,
                slot.slot(),
                slot.mission_id(),
                GATE_PLAYER,
                slot.commitment(),
            )
            .unwrap();
        for (guess, exact, present) in rounds {
            record = store
                .record_poa_signal_session_round_v1(
                    authority,
                    slot.slot(),
                    GATE_PLAYER,
                    dregg_persist::PoaSignalSessionRoundV1 {
                        guess: *guess,
                        exact: *exact,
                        present: *present,
                    },
                )
                .unwrap()
                .unwrap();
        }
        (dir, record)
    }

    /// ⚑ THE BLIND POLE, AT THE GATE ITSELF: a genuinely solving code with no
    /// session is refused, by name.
    ///
    /// The code here is the fixture's real answer — `(5, 0, 5)`, the same claim
    /// every settling test in this module uses — so the refusal is BECAUSE THE GAME
    /// WAS NOT PLAYED, not because the answer was wrong.
    #[test]
    fn a_solving_code_with_no_session_is_refused_by_name() {
        let authority = hex32(
            &CanonicalSignalInput::parse(fixture(INPUT_FILE))
                .unwrap()
                .dto
                .canon
                .federation_id,
        );
        let slot = fixture_slot(authority);
        let solving = claim();
        assert_eq!(
            solving.final_code(),
            SignalCode::new(5, 0, 5).unwrap(),
            "the mutation must be PRESENT: this is the fixture's genuine answer"
        );
        assert_eq!(
            verify_claim_transcript_was_played(None, &slot, &solving),
            Err(UnplayedTranscriptV1::NoSession)
        );
        assert_eq!(
            UnplayedTranscriptV1::NoSession.code(),
            "poa-signal-transcript-no-session"
        );
    }

    /// ⚑ NO REFUSAL IS AN ORACLE. Against ONE session state, a solving code and a
    /// losing code must draw the SAME refusal — otherwise the gate itself leaks
    /// whether a guess was right, faster than playing.
    ///
    /// An implementation that consulted the target could not pass this, which is
    /// what makes it a check rather than a restatement of the doc comment.
    #[test]
    fn the_refusal_never_depends_on_whether_the_code_is_right() {
        let authority = hex32(
            &CanonicalSignalInput::parse(fixture(INPUT_FILE))
                .unwrap()
                .dto
                .canon
                .federation_id,
        );
        let slot = fixture_slot(authority);
        let solving = code_of([5, 0, 5]);
        let losing = code_of([1, 1, 1]);
        assert_ne!(solving, losing);

        // No session at all.
        for code in [solving, losing] {
            let claim = SignalClaimV1::new(1, &[code]).unwrap();
            assert_eq!(
                verify_claim_transcript_was_played(None, &slot, &claim),
                Err(UnplayedTranscriptV1::NoSession)
            );
        }

        // An OPEN session with nothing played: both refuse on LENGTH, not content.
        let (_dir, empty) = gate_session(&slot, authority, &[]);
        for code in [solving, losing] {
            let claim = SignalClaimV1::new(1, &[code]).unwrap();
            assert_eq!(
                verify_claim_transcript_was_played(Some(&empty), &slot, &claim),
                Err(UnplayedTranscriptV1::LengthMismatch)
            );
        }

        // One round played, and it was neither of these codes.
        let (_dir2, one) = gate_session(&slot, authority, &[([0, 1, 2], 0, 2)]);
        for code in [solving, losing] {
            let claim = SignalClaimV1::new(1, &[code]).unwrap();
            assert_eq!(
                verify_claim_transcript_was_played(Some(&one), &slot, &claim),
                Err(UnplayedTranscriptV1::RoundMismatch)
            );
        }
    }

    /// The played pole at the gate: the exact rounds the node classified, in order,
    /// ending in the one it scored as locking, PASS — and every perturbation of that
    /// transcript refuses.
    #[test]
    fn only_the_transcript_this_node_classified_passes() {
        let authority = hex32(
            &CanonicalSignalInput::parse(fixture(INPUT_FILE))
                .unwrap()
                .dto
                .canon
                .federation_id,
        );
        let slot = fixture_slot(authority);
        let (_dir, solved) = gate_session(
            &slot,
            authority,
            &[([0, 1, 2], 0, 2), ([3, 3, 3], 1, 0), ([5, 0, 5], 3, 0)],
        );
        let played = [code_of([0, 1, 2]), code_of([3, 3, 3]), code_of([5, 0, 5])];

        verify_claim_transcript_was_played(
            Some(&solved),
            &slot,
            &SignalClaimV1::new(1, &played).unwrap(),
        )
        .expect("the transcript this node served must settle");

        // The solving code ALONE — the old carrier's whole content — refuses: the
        // node classified three rounds and this claim names one.
        assert_eq!(
            verify_claim_transcript_was_played(
                Some(&solved),
                &slot,
                &SignalClaimV1::new(1, &played[2..]).unwrap()
            ),
            Err(UnplayedTranscriptV1::LengthMismatch)
        );

        // Right rounds, wrong ORDER.
        let shuffled = [played[1], played[0], played[2]];
        assert_eq!(
            verify_claim_transcript_was_played(
                Some(&solved),
                &slot,
                &SignalClaimV1::new(1, &shuffled).unwrap()
            ),
            Err(UnplayedTranscriptV1::RoundMismatch)
        );

        // Right length, one substituted round.
        let substituted = [played[0], code_of([4, 4, 4]), played[2]];
        assert_eq!(
            verify_claim_transcript_was_played(
                Some(&solved),
                &slot,
                &SignalClaimV1::new(1, &substituted).unwrap()
            ),
            Err(UnplayedTranscriptV1::RoundMismatch)
        );

        // Another mission's claim over this session PASSES here, on purpose: the
        // mission is decided one layer down against the head's ACTIVE mission, and
        // `prepare_signal_input` names both numbers when it refuses. This assertion
        // exists so that arrangement is stated rather than assumed — if a mission
        // check is ever added back here, this goes red and the reader is sent to the
        // comment on `verify_claim_transcript_was_played` that says why not.
        verify_claim_transcript_was_played(
            Some(&solved),
            &slot,
            &SignalClaimV1::new(2, &played).unwrap(),
        )
        .expect("the mission is not this gate's question");
        assert!(matches!(
            prepare_signal_input(
                &CanonicalSignalInput::parse(fixture(INPUT_FILE))
                    .unwrap()
                    .authority_context(),
                SignalClaimV1::new(2, &played).unwrap()
            ),
            Err(SignalAdapterError::MissionMismatch {
                claimed: 2,
                active: 1
            })
        ));

        // A session the node served but never scored as locking.
        let (_dir2, unsolved) = gate_session(
            &slot,
            authority,
            &[([0, 1, 2], 0, 2), ([3, 3, 3], 1, 0), ([5, 0, 4], 2, 0)],
        );
        let unsolved_played = [played[0], played[1], code_of([5, 0, 4])];
        assert_eq!(
            verify_claim_transcript_was_played(
                Some(&unsolved),
                &slot,
                &SignalClaimV1::new(1, &unsolved_played).unwrap()
            ),
            Err(UnplayedTranscriptV1::NotSolved)
        );
    }

    /// A session opened against a DIFFERENT slot commitment is a different secret
    /// and therefore a different answer; its transcript cannot settle here.
    #[test]
    fn a_transcript_played_against_another_instance_is_refused() {
        let authority = hex32(
            &CanonicalSignalInput::parse(fixture(INPUT_FILE))
                .unwrap()
                .dto
                .canon
                .federation_id,
        );
        let slot = fixture_slot(authority);
        let dir = tempfile::tempdir().unwrap();
        let store = PersistentStore::open(&dir.path().join("dregg.redb")).unwrap();
        let record = store
            .open_poa_signal_session_v1(
                authority,
                slot.slot(),
                slot.mission_id(),
                GATE_PLAYER,
                [0xAB; 32],
            )
            .unwrap();
        assert_ne!(record.commitment(), slot.commitment());
        assert_eq!(
            verify_claim_transcript_was_played(Some(&record), &slot, &claim()),
            Err(UnplayedTranscriptV1::InstanceMismatch)
        );
    }
}
