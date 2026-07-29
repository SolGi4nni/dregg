//! `cosmos-lightclient`: the **inbound Cosmos/IBC socket** — dregg VERIFYING a
//! Cosmos chain by proof, never by trusting an RPC tag or a committee.
//!
//! This is the Cosmos analog of the ETH sync-committee verifier
//! ([`eth-lightclient`]) and the Solana Tower-BFT verifier
//! ([`dregg-bridge::solana_consensus`]). It has two accept paths, both
//! fail-closed:
//!
//! 1. [`verify_cosmos_header`] — advance a trusted Tendermint state to an
//!    untrusted [`SignedHeader`] via the audited informalsystems
//!    light-client verifier ([`tendermint_light_client_verifier`]). It enforces
//!    the whole Tendermint rule set: the validator-set hash binds the header, a
//!    stake-weighted **>= 2/3** of the voting power signed the commit (real
//!    Ed25519 verification), the header is within the trusting period, its time
//!    is monotonic and not from the future, and (for an adjacent block) the
//!    trusted `next_validators_hash` matches the untrusted validator set. On
//!    success it yields an unforgeable [`VerifiedHeader`] token — the only way to
//!    obtain one is to pass verification (its fields are private; there is no
//!    other constructor). The header's `app_hash` is the commitment the
//!    membership path opens into.
//!
//! 2. [`verify_cosmos_membership`] — verify a two-op ICS-23 proof (an `iavl`
//!    module-store exist proof + a `tendermint`/`simple` multistore exist proof)
//!    that `key -> value` is committed under a verified `app_hash`, via the
//!    audited [`ics23`] crate. This is exactly the chained verification ibc-rs
//!    performs: the iavl proof computes the module sub-root, the tendermint proof
//!    proves that sub-root under the app_hash, and the top root must equal the
//!    app_hash. Any tamper (a forged leaf, a wrong value, a swapped sub-root)
//!    breaks the chain and is refused.
//!
//! 3. [`ProvenCosmosFact`] — the bound result: `(chain_id, height, store_key,
//!    key, value)` proven at a [`VerifiedHeader`]. It is the Cosmos analog of
//!    `dregg-bridge::solana_holdings::ProvenHolding`.
//!
//! 4. [`bank`] — the holdings edge: [`foreign_holding_fields`] decodes a
//!    bank-store balance fact (`0x02 ‖ len ‖ address ‖ denom -> math.Int` /
//!    legacy `sdk.Coin`) into the plain-primitive [`ForeignHoldingFields`]
//!    `{chain_tag, holder, asset, amount, snapshot, consensus_proven}` the
//!    governance layer consumes — chain-id pinned, over-`u128` refused. The
//!    OUTBOUND direction (dregg as a CosmWasm client Cosmos verifies) remains a
//!    named followup; it waits on the wrap.
//!
//! Header advances come in both Tendermint shapes: **adjacent** (height + 1,
//! bound by `next_validators_hash`) and **non-adjacent skipping** (any higher
//! height, bound by the trust-threshold overlap rule — see
//! [`verify_cosmos_header`]).
//!
//! # Every accept path passes the VERIFIED Lean gate (2026-07-29)
//!
//! [`verify_cosmos_header`] is the ONLY constructor of a [`VerifiedHeader`], and it now decides
//! nothing on its own: it routes through [`verified_gate`] onto
//! `Dregg2.Bridge.LightClientTendermintGate`'s `@[export] dregg_tm_lc_verify` (adjacent advances)
//! or `Dregg2.Bridge.LightClientTendermintSkip`'s `@[export] dregg_tm_skip_verify` (skips), each
//! proven by `rfl` to BE the Lean decision its no-forgery theorem is stated over. Acceptance is
//! the CONJUNCTION of that gate and the audited informalsystems verifier; a missing archive makes
//! every entry point refuse with [`HeaderVerifyError::VerifiedGateUnavailable`], with no fallback.
//! `verified_gate`'s module docs carry the full argument, including what the audited verifier
//! still decides that the Lean model does not model.
//!
//! # Trust boundary (honest) — and the one thing no gate can establish
//!
//! The consensus arithmetic, the Ed25519 commit-signature verification, the
//! validator-set hashing, and the ICS-23 proof hashing are all real (delegated to
//! the audited reference libraries, not hand-rolled), and the accept/reject DECISION over their
//! results is rendered by the Lean archive.
//!
//! What no cryptography can establish is the **weak-subjectivity anchor**: the first trusted
//! `(header, next-validator-set)` pair, because nothing precedes it to verify it against. That is
//! Tendermint's analogue of the ETH light client's genesis sync committee, and it is now a
//! **named, typed** thing rather than a struct anyone can fill in:
//!
//!   * [`TrustedCosmosState::weak_subjectivity_anchor`] is the ONLY un-gated constructor. It is
//!     the operator asserting, out of band, "this is the chain". It is not gated and this crate
//!     does not pretend otherwise.
//!   * [`TrustedCosmosState::advance`] is the gated one: it takes a [`VerifiedHeader`] — which
//!     only [`verify_cosmos_header`] can mint, and only through the Lean gate — and derives the
//!     next trusted state from it.
//!   * [`TrustedCosmosState::provenance`] reports which of the two produced a given state, so
//!     "how far is this from the operator's assertion?" is answerable at runtime rather than by
//!     reading call sites.
//!
//! The struct's fields are private precisely so that the distinction cannot be bypassed. Both
//! constructors enforce the state's own self-consistency (`next_validators` must hash to
//! `next_validators_hash`) and refuse with [`HeaderVerifyError::TrustedStateCorrupt`] otherwise,
//! so a corrupt trusted state cannot be constructed at all — the check is a type invariant rather
//! than something the verify path has to remember.

pub mod bank;
pub mod verified_gate;
pub use bank::{
    cosmos_denom_asset_id, decode_bank_balance_kv, foreign_holding_fields, BankBalance,
    BankBalanceError, ForeignHoldingFields, BALANCES_PREFIX, BANK_STORE_KEY, COSMOS_CHAIN_TAG,
};

use core::time::Duration;

use ics23::commitment_proof::Proof as Ics23Proof;
use ics23::{
    calculate_existence_root, iavl_spec, tendermint_spec, CommitmentProof, ExistenceProof,
    HostFunctionsManager,
};
use tendermint::block::signed_header::SignedHeader;
use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint::validator::Set as ValidatorSet;
use tendermint::{Hash, Time};
use tendermint_light_client_verifier::options::Options;
use tendermint_light_client_verifier::types::{
    TrustThreshold, TrustedBlockState, UntrustedBlockState,
};
use tendermint_light_client_verifier::{ProdVerifier, Verdict, Verifier};

// ============================================================================
// Header verification (accept path 1)
// ============================================================================

/// Where a [`TrustedCosmosState`] came from — the distinction between "un-gated because it is
/// the anchor" and "gated".
///
/// A light client has exactly one thing cryptography cannot establish, and naming it is the point
/// of this enum. Reporting it (via [`TrustedCosmosState::provenance`]) means a caller can ask how
/// far a given state is from the operator's out-of-band assertion instead of inferring it from
/// call sites.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustProvenance {
    /// **THE WEAK-SUBJECTIVITY ANCHOR.** Asserted out of band by the operator. Nothing precedes
    /// it, so no signature, quorum or proof can establish it — a light client bootstrapped onto
    /// an attacker's anchor follows the attacker's chain with every subsequent advance perfectly
    /// verified. This is the same posture Hermes and ibc-rs have, and the same role the genesis
    /// sync committee plays for `eth-lightclient`. It is NOT gated, and this crate says so rather
    /// than gating it and pretending.
    WeakSubjectivityAnchor,
    /// Derived from a [`VerifiedHeader`] — i.e. from a header that passed the VERIFIED Lean gate
    /// and the audited verifier. Carries the height it was derived from, so a chain of advances
    /// is traceable back toward the anchor.
    VerifiedAdvance {
        /// The verified height this state was derived from.
        from_height: u64,
    },
}

/// The trusted starting point for a light-client advance: a header + validator set the caller
/// asserted out of band (the weak-subjectivity anchor), or one derived from a previously
/// [`VerifiedHeader`]. `next_validators` / `next_validators_hash` describe the validator set that
/// signs the *next* block — for an adjacent-block advance the gate binds `next_validators_hash` to
/// the untrusted validator set; for a skip it is the trust-OVERLAP tally base.
///
/// **The fields are private.** There are exactly two constructors —
/// [`TrustedCosmosState::weak_subjectivity_anchor`] (the un-gated anchor) and
/// [`TrustedCosmosState::advance`] (gated on a [`VerifiedHeader`]) — and both enforce that
/// `next_validators` hashes to `next_validators_hash`, so a self-inconsistent trusted state cannot
/// be constructed. That consistency is what makes the skipping overlap tally run over the set the
/// trusted header actually committed to rather than whatever a relayer delivered; the audited
/// verifier documents it as the caller's responsibility and this type discharges it once.
///
/// # The falsifiers, and why they were RED before 2026-07-29
///
/// Both doctests below **compiled** until this change and therefore FAILED as `compile_fail`
/// doctests — mechanically red, not argued. This type had five `pub` fields, so any caller could
/// mint a trusted anchor field-by-field with no consistency check and no record of where it came
/// from, and could mutate a verified advance back into an arbitrary assertion afterwards.
///
/// ```compile_fail
/// // A trusted anchor cannot be read apart field-by-field: the fields are private, and the
/// // anchor/advance distinction is the whole point of the type.
/// fn nope(s: cosmos_lightclient::TrustedCosmosState) {
///     let _ = s.next_validators_hash;
/// }
/// ```
///
/// ```compile_fail
/// // Nor can a trusted state be mutated after construction — that is how a doctored
/// // trust-overlap tally base used to be built.
/// fn nope(
///     s: &mut cosmos_lightclient::TrustedCosmosState,
///     other: cosmos_lightclient::TrustedCosmosState,
/// ) {
///     s.next_validators = other.next_validators;
/// }
/// ```
#[derive(Clone, Debug)]
pub struct TrustedCosmosState {
    chain_id: ChainId,
    header_time: Time,
    height: Height,
    next_validators: ValidatorSet,
    next_validators_hash: Hash,
    provenance: TrustProvenance,
}

impl TrustedCosmosState {
    /// **THE WEAK-SUBJECTIVITY ANCHOR — the one un-gated constructor in this crate.**
    ///
    /// The operator asserts, out of band, that `(chain_id, height, header_time)` is a real header
    /// of the chain it means to follow and that `next_validators_hash` is that header's
    /// commitment to the set signing `height + 1`. No cryptography available here can check that
    /// claim: there is nothing before it to check it against. Every subsequent advance is gated;
    /// this one is the axiom.
    ///
    /// `next_validators` is the relayer-supplied set. It is NOT trusted — it must hash to the
    /// operator-supplied `next_validators_hash`, or this refuses with
    /// [`HeaderVerifyError::TrustedStateCorrupt`].
    pub fn weak_subjectivity_anchor(
        chain_id: ChainId,
        header_time: Time,
        height: Height,
        next_validators: ValidatorSet,
        next_validators_hash: Hash,
    ) -> Result<Self, HeaderVerifyError> {
        Self::checked(
            chain_id,
            header_time,
            height,
            next_validators,
            next_validators_hash,
            TrustProvenance::WeakSubjectivityAnchor,
        )
    }

    /// Derive the next trusted state from a [`VerifiedHeader`] — a header that PASSED the verified
    /// gate. `next_validators` is the relayer-supplied set for `header.height + 1`; it must hash
    /// to the verified header's own `next_validators_hash` commitment, which is why that field is
    /// carried on [`VerifiedHeader`] at all.
    ///
    /// This is the gated half of the pair: it cannot be reached without a `VerifiedHeader`, and a
    /// `VerifiedHeader` cannot be reached without the Lean gate.
    pub fn advance(
        header: &VerifiedHeader,
        next_validators: ValidatorSet,
    ) -> Result<Self, HeaderVerifyError> {
        let chain_id = header.chain_id.parse::<ChainId>().map_err(|e| {
            HeaderVerifyError::TrustedStateCorrupt(format!(
                "verified header chain id {} is not a valid chain id: {e}",
                header.chain_id
            ))
        })?;
        let height = Height::try_from(header.height).map_err(|e| {
            HeaderVerifyError::TrustedStateCorrupt(format!(
                "verified header height {} is not a valid height: {e}",
                header.height
            ))
        })?;
        Self::checked(
            chain_id,
            header.time,
            height,
            next_validators,
            header.next_validators_hash,
            TrustProvenance::VerifiedAdvance {
                from_height: header.height,
            },
        )
    }

    fn checked(
        chain_id: ChainId,
        header_time: Time,
        height: Height,
        next_validators: ValidatorSet,
        next_validators_hash: Hash,
        provenance: TrustProvenance,
    ) -> Result<Self, HeaderVerifyError> {
        let actual = next_validators.hash();
        if actual != next_validators_hash {
            return Err(HeaderVerifyError::TrustedStateCorrupt(format!(
                "supplied next_validators hash {actual} != committed next_validators_hash \
                 {next_validators_hash}"
            )));
        }
        Ok(Self {
            chain_id,
            header_time,
            height,
            next_validators,
            next_validators_hash,
            provenance,
        })
    }

    /// The chain id the untrusted header must also carry (a header from another chain is refused
    /// — the cross-chain replay defense).
    pub fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }
    /// The trusted header's block time (anchors the trusting-period + monotonic-time checks).
    pub fn header_time(&self) -> Time {
        self.header_time
    }
    /// The trusted header's height.
    pub fn height(&self) -> Height {
        self.height
    }
    /// The validator set that signs `height + 1`. Guaranteed by construction to hash to
    /// [`Self::next_validators_hash`].
    pub fn next_validators(&self) -> &ValidatorSet {
        &self.next_validators
    }
    /// The trusted header's `next_validators_hash` commitment.
    pub fn next_validators_hash(&self) -> Hash {
        self.next_validators_hash
    }
    /// Whether this state is the un-gated weak-subjectivity anchor or a gated advance from one.
    pub fn provenance(&self) -> TrustProvenance {
        self.provenance
    }
}

/// Default clock-drift tolerance (the local clock may lag a blockchain timestamp
/// by at most this). Matches Hermes/ibc-rs defaults.
pub const DEFAULT_CLOCK_DRIFT: Duration = Duration::from_secs(5);

/// Why a header advance was refused. A refusal NEVER yields a [`VerifiedHeader`]
/// (fail closed).
// `PartialEq` so a refusal can be asserted BY VALUE rather than by matching its `Debug` string.
// Without it `assert_eq!(verify(..), Err(NonIncreasingHeight { .. }))` does not compile, and
// `cosmos-lightclient/tests/verified_gate_routing.rs` was left with 16 such assertions that broke
// the whole-workspace build — a test target nothing compiled because `cargo check -p` on this crate
// passes and only `--workspace --all-targets` reaches it. Every payload is `String` or an integer,
// so the derive is total and adds no semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeaderVerifyError {
    /// The signed commit did not reach the required voting-power threshold
    /// (sub-2/3, or a forged/invalid signature contributed no power). Carries the
    /// verifier's tally description.
    NotEnoughVotingPower(String),
    /// The header failed a validity check: validators-hash mismatch, a bad
    /// signature, an expired header (outside the trusting period), non-monotonic
    /// or future time, a chain-id mismatch, or a malformed commit. Carries the
    /// verifier's detail.
    Invalid(String),
    /// The caller-supplied trusted state is internally inconsistent: `next_validators` does not
    /// hash to `next_validators_hash`. Refused at CONSTRUCTION, so no such state can exist — in
    /// the non-adjacent (skipping) path that set is the trust-overlap tally base, and the
    /// underlying verifier documents that this consistency is the caller's responsibility.
    TrustedStateCorrupt(String),
    /// **THE VERIFIED GATE COULD NOT RENDER A VERDICT** — the linked Lean archive does not export
    /// `dregg_tm_lc_verify` / `dregg_tm_skip_verify` (a cold-seed, marshal-only or stale archive,
    /// or a target that cannot link it).
    ///
    /// This is DELIBERATELY distinct from every other variant: a missing archive is an
    /// ENVIRONMENT fault and must never be readable as a proved rejection. The header was not
    /// judged; it was not judgeable. There is no Rust fallback — see [`verified_gate`]'s module
    /// docs for why a light client that silently degrades to an unverified decider when its
    /// verifier is absent has the worst possible posture.
    VerifiedGateUnavailable(String),
    /// **THE VERIFIED GATE REFUSED, AND THE AUDITED VERIFIER DID NOT.** A genuine divergence
    /// between the Lean decision and the reference implementation on this header. The refusal
    /// STANDS (the conjunction refuses), and the wire is carried so the disagreement is
    /// reproducible against the export directly.
    VerifiedGateRefused {
        /// The exact bytes handed to the gate.
        wire: String,
    },
    /// A timestamp or duration has no projection into the gate's `Nat` domain (pre-epoch, or
    /// beyond `u64` nanoseconds). Refused rather than clamped — clamping would move a header
    /// across a time window.
    UnprojectableTime(String),
    /// The untrusted height is at or below the trusted height, so it is neither an adjacent
    /// advance nor a skip and reaches NEITHER gate. Refused outright rather than routed
    /// arbitrarily.
    NonIncreasingHeight {
        /// The untrusted header's height.
        untrusted: u64,
        /// The trusted state's height.
        trusted: u64,
    },
}

impl core::fmt::Display for HeaderVerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HeaderVerifyError::NotEnoughVotingPower(d) => {
                write!(f, "insufficient voting power: {d}")
            }
            HeaderVerifyError::Invalid(d) => write!(f, "invalid header: {d}"),
            HeaderVerifyError::TrustedStateCorrupt(d) => {
                write!(f, "corrupt trusted state: {d}")
            }
            HeaderVerifyError::VerifiedGateUnavailable(d) => write!(
                f,
                "VERIFIED gate unavailable (NOT a rejection — the header was not judged): {d}"
            ),
            HeaderVerifyError::VerifiedGateRefused { wire } => write!(
                f,
                "the VERIFIED gate refused a header the audited verifier accepted \
                 (divergence; refusal stands) — wire: {wire}"
            ),
            HeaderVerifyError::UnprojectableTime(d) => write!(f, "unprojectable time: {d}"),
            HeaderVerifyError::NonIncreasingHeight { untrusted, trusted } => write!(
                f,
                "untrusted height {untrusted} does not advance trusted height {trusted}"
            ),
        }
    }
}

impl std::error::Error for HeaderVerifyError {}

/// An unforgeable proof-carrying token: a Cosmos header that PASSED full
/// Tendermint light-client verification (>= 2/3 voting power signed the commit,
/// the validator-set hash bound the header, within the trusting period). Its
/// fields are private and it has no public constructor other than
/// [`verify_cosmos_header`] — you cannot fabricate one. Its `app_hash` is the
/// commitment [`verify_cosmos_membership`] opens state into.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedHeader {
    chain_id: String,
    height: u64,
    time: Time,
    app_hash: Vec<u8>,
    /// This header's own commitment to the set signing `height + 1` — what
    /// [`TrustedCosmosState::advance`] binds the relayer's next set against, so an advance off a
    /// verified header is anchored in that header rather than in the relayer.
    next_validators_hash: Hash,
}

impl VerifiedHeader {
    /// The chain id proven (bound to the trusted state's chain id).
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    /// The verified block height.
    pub fn height(&self) -> u64 {
        self.height
    }
    /// The verified block time.
    pub fn time(&self) -> Time {
        self.time
    }
    /// The verified application state root — the ICS-23 membership commitment.
    pub fn app_hash(&self) -> &[u8] {
        &self.app_hash
    }
    /// This header's commitment to the validator set signing `height + 1`.
    pub fn next_validators_hash(&self) -> Hash {
        self.next_validators_hash
    }
}

/// Verify that an untrusted [`SignedHeader`] + validator set advances a [`TrustedCosmosState`].
///
/// **This function decides nothing itself.** It routes onto the VERIFIED Lean gate and composes
/// that verdict with the audited informalsystems verifier's; a header is accepted only if BOTH
/// accept. See [`verified_gate`] for the full argument — in particular why the composition is a
/// conjunction (the audited verifier still decides things `tmVerify` does not model, and dropping
/// it would weaken checks) and why the gate has no fallback.
///
/// Two advance shapes, dispatched on the untrusted height onto two DIFFERENT gates. They are
/// different rule sets, not a rule and its relaxation, and
/// `LightClientTendermintSkip.tmSkip_height_disjoint_from_adjacent` proves they cover disjoint
/// height ranges — so every header reaches exactly one, and none reaches neither:
///
/// - **Adjacent** (`height == trusted.height + 1`) → `dregg_tm_lc_verify`. The trusted
///   `next_validators_hash` must equal the untrusted validator set's hash (the epoch binding), on
///   top of chain-id match, the time window, and the strict `2·total < 3·signed` threshold.
/// - **Non-adjacent / skipping** (`height > trusted.height + 1`) → `dregg_tm_skip_verify`. The
///   epoch binding is gone; in its place the trust-OVERLAP rule — validators from the TRUSTED
///   `next_validators` set must carry strictly more than `trust_threshold` (canonically 1/3) of
///   THAT set's voting power among the commit's verifying signatures, in addition to the full
///   strict `> 2/3` over the untrusted set. Too little overlap refuses (bisect to an intermediate
///   height to proceed); `LightClientTendermintSkip.tmSkip_zero_overlap_rejected` proves a
///   zero-overlap skip is refused with no crypto hypothesis at all.
/// - **Neither** (`height <= trusted.height`) → refused outright with
///   [`HeaderVerifyError::NonIncreasingHeight`]. A header that reaches no gate is never accepted.
///
/// The gate's REACHABILITY is checked before any cryptography runs, so a cold archive refuses
/// with [`HeaderVerifyError::VerifiedGateUnavailable`] — distinct from every rejection variant,
/// because a missing archive is an environment fault and must never read as a proved `no`.
///
/// `untrusted_next_validators` is the set that signs `height + 1`; pass `None` if unavailable (the
/// next-validators-hash cross-check is then skipped, exactly as the underlying verifier
/// documents).
///
/// On success returns a [`VerifiedHeader`] — the crate's only proof-carrying token, with no other
/// constructor.
#[allow(clippy::too_many_arguments)]
pub fn verify_cosmos_header(
    trusted: &TrustedCosmosState,
    untrusted_signed_header: &SignedHeader,
    untrusted_validators: &ValidatorSet,
    untrusted_next_validators: Option<&ValidatorSet>,
    trust_threshold: TrustThreshold,
    trusting_period: Duration,
    now: Time,
) -> Result<VerifiedHeader, HeaderVerifyError> {
    let h = &untrusted_signed_header.header;
    let untrusted_height = h.height.value();
    let trusted_height = trusted.height.value();

    // ---- Route the header onto its gate, and REFUSE if that gate cannot render a verdict. ----
    // Reachability is probed BEFORE any cryptography so the refusal is unambiguous: nothing was
    // computed, nothing was judged.
    let adjacent = untrusted_height == trusted_height + 1;
    if untrusted_height <= trusted_height {
        return Err(HeaderVerifyError::NonIncreasingHeight {
            untrusted: untrusted_height,
            trusted: trusted_height,
        });
    }
    let gate_live = if adjacent {
        verified_gate::available()
    } else {
        verified_gate::skip_available()
    };
    if !gate_live {
        return Err(HeaderVerifyError::VerifiedGateUnavailable(format!(
            "the linked archive does not export {} — this header cannot be judged, and there is \
             no Rust fallback",
            if adjacent {
                "dregg_tm_lc_verify (the ADJACENT Tendermint gate)"
            } else {
                "dregg_tm_skip_verify (the SKIPPING Tendermint gate)"
            }
        )));
    }

    // ---- The VERIFIED gate's verdict, over projections whose crypto ran in the audited crate. --
    let (gate_accepts, wire) = if adjacent {
        let p = verified_gate::project_adjacent(
            &trusted.chain_id,
            trusted.header_time,
            trusted_height,
            trusted.next_validators_hash,
            untrusted_signed_header,
            untrusted_validators,
            trusting_period,
            now,
        )?;
        (verified_gate::decide(&p)?, p.wire())
    } else {
        let p = verified_gate::project_skip(
            &trusted.chain_id,
            trusted.header_time,
            trusted_height,
            &trusted.next_validators,
            untrusted_signed_header,
            untrusted_validators,
            trust_threshold,
            trusting_period,
            now,
        )?;
        (verified_gate::decide_skip(&p)?, p.wire())
    };

    // ---- The audited verifier's verdict (the conjunction's second half). --------------------
    // It is ALSO the diagnostic source when the gate refuses: nothing in this crate re-derives a
    // refusal reason in Rust, so there is no second decision procedure to drift.
    let options = Options {
        trust_threshold,
        trusting_period,
        clock_drift: DEFAULT_CLOCK_DRIFT,
    };
    let untrusted = UntrustedBlockState {
        signed_header: untrusted_signed_header,
        validators: untrusted_validators,
        next_validators: untrusted_next_validators,
    };
    let trusted_state = TrustedBlockState {
        chain_id: &trusted.chain_id,
        header_time: trusted.header_time,
        height: trusted.height,
        next_validators: &trusted.next_validators,
        next_validators_hash: trusted.next_validators_hash,
    };
    let audited =
        ProdVerifier::default().verify_update_header(untrusted, trusted_state, &options, now);

    match (gate_accepts, audited) {
        (true, Verdict::Success) => Ok(VerifiedHeader {
            chain_id: h.chain_id.as_str().to_string(),
            height: untrusted_height,
            time: h.time,
            app_hash: h.app_hash.as_bytes().to_vec(),
            next_validators_hash: h.next_validators_hash,
        }),
        // The gate refused. The refusal STANDS either way; the audited verdict only names it.
        (false, Verdict::NotEnoughTrust(tally)) => Err(HeaderVerifyError::NotEnoughVotingPower(
            format!("{tally:?}"),
        )),
        (false, Verdict::Invalid(detail)) => Err(HeaderVerifyError::Invalid(format!("{detail:?}"))),
        // The gate refused something the audited verifier accepted: a genuine DIVERGENCE, and the
        // one outcome that must never be laundered into an ordinary rejection message.
        (false, Verdict::Success) => Err(HeaderVerifyError::VerifiedGateRefused { wire }),
        // The gate accepted and the audited verifier did not — its extra checks
        // (`header_matches_commit`, `valid_commit`, `next_validators_match`) are exactly the ones
        // `tmVerify` does not model, so this is expected, not a divergence.
        (true, Verdict::NotEnoughTrust(tally)) => Err(HeaderVerifyError::NotEnoughVotingPower(
            format!("{tally:?}"),
        )),
        (true, Verdict::Invalid(detail)) => Err(HeaderVerifyError::Invalid(format!("{detail:?}"))),
    }
}

// ============================================================================
// ICS-23 membership verification (accept path 2)
// ============================================================================

/// A Cosmos state-membership proof: the two-op ICS-23 proof an ABCI query with
/// `prove=true` returns for a `/store/<module>/key` path. `iavl_proof` proves
/// `key -> value` in the module's IAVL store (the module sub-root);
/// `store_proof` proves `store_key -> module_sub_root` in the Tendermint simple
/// multistore Merkle tree (whose root is the block `app_hash`).
#[derive(Clone, Debug)]
pub struct CosmosMembershipProof {
    /// The module store name (e.g. `b"bank"`), the key of the outer `tendermint`
    /// proof op.
    pub store_key: Vec<u8>,
    /// The inner `ics23:iavl` exist proof: `key -> value` under the module sub-root.
    pub iavl_proof: CommitmentProof,
    /// The outer `ics23:simple` (tendermint) exist proof: `store_key -> sub-root`
    /// under the `app_hash`.
    pub store_proof: CommitmentProof,
}

/// Why a membership proof was refused. A refusal NEVER counts as membership
/// (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembershipError {
    /// A proof op was not an existence proof (a non-existence / batch / compressed
    /// op cannot prove membership).
    NotExistenceProof,
    /// Could not compute the sub-root from an existence proof (malformed proof).
    RootComputationFailed,
    /// The inner IAVL exist proof did not prove `key -> value` under its sub-root
    /// (wrong key/value, tampered leaf, or spec violation).
    IavlProofInvalid,
    /// The outer tendermint exist proof did not prove `store_key -> sub-root` under
    /// its root (tampered proof, or the sub-root did not match).
    StoreProofInvalid,
    /// The proof's top root did not equal the verified `app_hash` — the proof does
    /// not open into THIS block's state.
    AppHashMismatch,
}

impl core::fmt::Display for MembershipError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            MembershipError::NotExistenceProof => "proof op is not an existence proof",
            MembershipError::RootComputationFailed => "could not compute sub-root from proof",
            MembershipError::IavlProofInvalid => "iavl membership proof invalid",
            MembershipError::StoreProofInvalid => "tendermint store proof invalid",
            MembershipError::AppHashMismatch => "proof root does not match app_hash",
        };
        f.write_str(s)
    }
}

impl std::error::Error for MembershipError {}

fn exist_proof(cp: &CommitmentProof) -> Result<&ExistenceProof, MembershipError> {
    match &cp.proof {
        Some(Ics23Proof::Exist(ex)) => Ok(ex),
        _ => Err(MembershipError::NotExistenceProof),
    }
}

/// Verify a two-op ICS-23 membership proof that `key -> value` is committed under
/// `app_hash`, via the audited [`ics23`] crate — the same chained verification
/// ibc-rs performs.
///
/// Steps (each fail-closed):
/// 1. Compute the module sub-root from the IAVL exist proof, and verify it proves
///    `key -> value` under that sub-root (the IAVL spec: leaf/inner hash ops,
///    ordering, prefixes).
/// 2. Compute the top root from the tendermint exist proof, and verify it proves
///    `store_key -> sub_root` under that top root (the tendermint spec).
/// 3. Require the top root to equal `app_hash`.
///
/// A tampered value changes the IAVL leaf hash (step 1 fails); a tampered IAVL
/// proof changes the sub-root, which then mismatches the tendermint proof's
/// committed value (step 2 fails); a tampered tendermint proof makes the top root
/// differ from `app_hash` (step 3 fails). Non-membership passed here is refused
/// in step 1 (it is not an existence proof).
pub fn verify_cosmos_membership(
    app_hash: &[u8],
    proof: &CosmosMembershipProof,
    key: &[u8],
    value: &[u8],
) -> Result<(), MembershipError> {
    // ---- Level 0: IAVL module store: key -> value under sub_root ----
    let iavl_ex = exist_proof(&proof.iavl_proof)?;
    let sub_root = calculate_existence_root::<HostFunctionsManager>(iavl_ex)
        .map_err(|_| MembershipError::RootComputationFailed)?;
    if !ics23::verify_membership::<HostFunctionsManager>(
        &proof.iavl_proof,
        &iavl_spec(),
        &sub_root,
        key,
        value,
    ) {
        return Err(MembershipError::IavlProofInvalid);
    }

    // ---- Level 1: tendermint multistore: store_key -> sub_root under top_root ----
    let store_ex = exist_proof(&proof.store_proof)?;
    let top_root = calculate_existence_root::<HostFunctionsManager>(store_ex)
        .map_err(|_| MembershipError::RootComputationFailed)?;
    if !ics23::verify_membership::<HostFunctionsManager>(
        &proof.store_proof,
        &tendermint_spec(),
        &top_root,
        &proof.store_key,
        &sub_root,
    ) {
        return Err(MembershipError::StoreProofInvalid);
    }

    // ---- Anchor: the top root MUST be the verified app_hash ----
    if top_root != app_hash {
        return Err(MembershipError::AppHashMismatch);
    }
    Ok(())
}

// ============================================================================
// ProvenCosmosFact (bound result — accept path 3)
// ============================================================================

/// A proven Cosmos state fact: at verified `(chain_id, height)`, the module store
/// `store_key` committed `key -> value`. Produced ONLY by [`prove_cosmos_fact`],
/// which requires a [`VerifiedHeader`] (an unforgeable, fully-verified header) AND
/// a valid ICS-23 membership proof under that header's `app_hash`. Its fields are
/// private with no other constructor — it cannot be fabricated. This is the
/// Cosmos analog of `ProvenHolding`; a governance/holdings binding consumes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenCosmosFact {
    chain_id: String,
    height: u64,
    store_key: Vec<u8>,
    key: Vec<u8>,
    value: Vec<u8>,
}

impl ProvenCosmosFact {
    /// The chain the fact was proven on.
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    /// The verified height the fact holds at.
    pub fn height(&self) -> u64 {
        self.height
    }
    /// The module store the key lives in (e.g. `b"bank"`).
    pub fn store_key(&self) -> &[u8] {
        &self.store_key
    }
    /// The proven key.
    pub fn key(&self) -> &[u8] {
        &self.key
    }
    /// The proven value.
    pub fn value(&self) -> &[u8] {
        &self.value
    }
}

/// Bind a [`ProvenCosmosFact`] from a [`VerifiedHeader`] + an ICS-23 membership
/// proof: verify `key -> value` under the header's verified `app_hash`, and on
/// success return the fact bound to the header's `(chain_id, height)`.
///
/// Fail-closed: a [`VerifiedHeader`] can only exist if it passed
/// [`verify_cosmos_header`], and this refuses (returns the [`MembershipError`])
/// unless the membership proof also verifies. So a `ProvenCosmosFact` is a genuine
/// end-to-end proof — a >= 2/3-signed header AND a valid state proof under it.
pub fn prove_cosmos_fact(
    header: &VerifiedHeader,
    proof: &CosmosMembershipProof,
    key: &[u8],
    value: &[u8],
) -> Result<ProvenCosmosFact, MembershipError> {
    verify_cosmos_membership(header.app_hash(), proof, key, value)?;
    Ok(ProvenCosmosFact {
        chain_id: header.chain_id().to_string(),
        height: header.height(),
        store_key: proof.store_key.clone(),
        key: key.to_vec(),
        value: value.to_vec(),
    })
}

/// Decode a raw ABCI-query proof-op payload (protobuf `CommitmentProof` bytes)
/// into an [`ics23::CommitmentProof`]. A malformed payload is refused.
pub fn decode_commitment_proof(bytes: &[u8]) -> Result<CommitmentProof, prost::DecodeError> {
    <CommitmentProof as prost::Message>::decode(bytes)
}
