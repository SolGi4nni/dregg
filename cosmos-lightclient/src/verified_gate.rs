//! `verified_gate` — the route-through that makes the **Lean gate a mandatory decider** for
//! every Cosmos/Tendermint header this crate accepts.
//!
//! # What was wrong, precisely: an ORPHAN, not a twin
//!
//! `Dregg2.Bridge.LightClientTendermintGate` proves `tmVerifyDecision_refines` (by `rfl`) — that
//! `@[export] dregg_tm_lc_verify`, fed an update's true projections, IS `tmVerify`, the decision
//! `tmNoForgery` is proven over. `dregg-lean-ffi` wrapped it (`verified_tm_lc_verify`,
//! `tm_lc_verify_wire`, `shadow_tm_lc_verify`, `tm_lc_verify_available`). The C shim bridged it.
//! `build.rs` probed the archive for it and listed it in `REQUIRED_DECISION_EXPORTS`.
//!
//! And **nothing called it.** Measured 2026-07-28: `dregg_tm_lc_verify` had no caller outside
//! `dregg-lean-ffi`, and `cosmos-lightclient/Cargo.toml` did not even depend on that crate. This
//! is not the ETH pattern (a hand-written Rust twin standing beside a proven decision, with the
//! runtime going through the unproven half) — there was no hand-written Tendermint rule set here
//! to delete. `verify_cosmos_header` delegated, correctly and deliberately, to the audited
//! informalsystems `ProdVerifier`. The Lean gate simply sat beside it, reachable from no caller,
//! reading to a maintainer as though it gated something.
//!
//! So the fix is ROUTING, not deletion — and the sibling of the ETH lane's deletion, one crate
//! over. There is no Rust twin removed here because there never was one.
//!
//! # The composition, and why it is a conjunction rather than a replacement
//!
//! Every accepted header must satisfy **both**:
//!
//!   1. the **VERIFIED Lean gate**, over the projections computed below, and
//!   2. the **audited informalsystems verifier** (`ProdVerifier::verify_update_header`).
//!
//! The Lean gate is not decoration in that pair, and the audited verifier is not redundant:
//!
//!   * The gate is **mandatory and fail-closed**. If the archive does not export it, [`decide`]
//!     returns [`crate::HeaderVerifyError::VerifiedGateUnavailable`] and `verify_cosmos_header`
//!     refuses **before running any cryptography at all**. There is deliberately no fallback and
//!     no environment variable: a light client that silently reverts to "the audited crate alone"
//!     when its verified decider is missing looks gated and is not, which is exactly the state
//!     this crate was in before this module existed.
//!   * The audited verifier is retained because it decides things `tmVerify` does **not yet
//!     model**, and dropping it would *weaken* checks: `header_matches_commit` (the commit's
//!     `block_id.hash` really is this header's hash), `valid_commit` (the commit's signature array
//!     is the right length for the validator set, with no duplicate votes), the canonical-vote
//!     sign-bytes construction itself, and `next_validators_match`. Those are named here rather
//!     than quietly inherited. It also computes the cryptography the gate consumes as results.
//!
//! Because acceptance is a conjunction, **no projection error can manufacture an accept** — it
//! can only make the pair refuse more. That is what licenses the lossy `u64` chain-id tag below.
//!
//! # The two gates, and why there are two
//!
//! Tendermint has two advance shapes and they are different rule sets, not a rule and its
//! relaxation:
//!
//!   * **Adjacent** (`height == trusted.height + 1`) → `dregg_tm_lc_verify`. Bound by the
//!     `next_validators_hash` epoch commitment.
//!   * **Non-adjacent / skipping** (`trusted.height + 1 < height`) → `dregg_tm_skip_verify`. The
//!     epoch binding is gone (a skip target's validator set was never committed by the trusted
//!     header); the **trust-overlap** threshold takes its place — strictly more than
//!     `trust_threshold` of the TRUSTED epoch's voting power signed the target, on top of the
//!     full strict `> 2/3` over the target's own set.
//!
//! `LightClientTendermintSkip.tmSkip_height_disjoint_from_adjacent` proves the two decisions
//! cover disjoint height ranges, so the height dispatch in [`crate::verify_cosmos_header`] sends
//! each header to exactly one gate and none to neither. A height at or below the trusted one
//! reaches neither gate and is refused outright.
//!
//! # The named trusted projections (stated, not hidden)
//!
//!   1. **The chain-id tag.** The gates compare chain ids as `Nat`s; a Tendermint chain id is a
//!      string. [`chain_id_tag`] projects it through SHA-256 truncated to 64 bits. This is
//!      deliberately lossy and it cannot create an accept: a collision would have to be paired
//!      with the audited verifier's `is_matching_chain_id`, which compares the actual strings,
//!      also returning success — and the two must both succeed. The gate's verdict on the tag is
//!      therefore a genuine additional refusal surface, never a weaker one.
//!   2. **The power tallies.** `total_power_of` and the `voting_power_in_sets` tallies are
//!      computed by the audited crate and supplied as `Nat`s, exactly as the `dregg_eth_lc_verify`
//!      gate trusts Rust for the participant count. The VERIFIED content is the strict
//!      multiply-form threshold DECISION over them. Note that the audited tally SHORT-CIRCUITS
//!      (`voting_power_in_impl` breaks the moment `check()` passes), so `tallied` is a lower bound
//!      — which is exactly right here, because `check()` is the same strict fraction test the gate
//!      re-decides, so a short-circuited tally clears the gate's threshold precisely when it
//!      cleared the audited one.
//!   3. **The binding booleans.** `epoch_bind_ok` / `self_bind_ok` are SHA-256 validator-set
//!      hash-and-compare results (the `CryptoLeaf.hashCR` carrier). The gate re-derives no hash.
//!
//! # One place the Lean rule is *more* permissive, and why it does not matter
//!
//! `tmVerify`'s not-from-the-future conjunct is `time ≤ now + clockDrift`; the audited
//! `is_header_from_past` is the strict `time < now + clock_drift`. At the exact boundary
//! nanosecond the gate would accept and the audited verifier refuses. Under the conjunction the
//! strict rule wins, so the deployed behaviour is the audited one. Recorded here rather than
//! papered over: it is a genuine one-nanosecond divergence between the Lean model and the
//! reference implementation, and the direction is safe.

use core::time::Duration;

use sha2::{Digest, Sha256};
use tendermint::block::signed_header::SignedHeader;
use tendermint::chain::Id as ChainId;
use tendermint::validator::Set as ValidatorSet;
use tendermint::Time;
use tendermint_light_client_verifier::operations::voting_power::ProdVotingPowerCalculator;
use tendermint_light_client_verifier::operations::VotingPowerCalculator;
use tendermint_light_client_verifier::types::TrustThreshold;

use crate::HeaderVerifyError;

/// Project a Tendermint chain id onto the `Nat` domain the gates compare: SHA-256 of the chain-id
/// string, truncated to the leading 64 bits, big-endian.
///
/// Lossy on purpose, and sound because acceptance is a conjunction — see the module docs. Both the
/// trusted and the untrusted chain id go through THIS function, so equal strings always tag equal.
pub fn chain_id_tag(id: &ChainId) -> u64 {
    let d = Sha256::digest(id.as_str().as_bytes());
    u64::from_be_bytes(d[..8].try_into().expect("sha256 yields 32 bytes"))
}

/// Project a Tendermint timestamp onto the gates' `Nat` domain: nanoseconds since the Unix epoch.
/// A pre-epoch or beyond-`u64` timestamp has no `Nat` projection, so it is REFUSED rather than
/// clamped — clamping would move a header across a time window.
fn time_nanos(t: Time) -> Option<u64> {
    u64::try_from(t.unix_timestamp_nanos()).ok()
}

/// Project a `Duration` onto the gates' `Nat` domain (nanoseconds). Refused rather than clamped,
/// for the same reason.
fn duration_nanos(d: Duration) -> Option<u64> {
    u64::try_from(d.as_nanos()).ok()
}

/// The clock/window scalars both gates share, projected once.
struct Window {
    header_time: u64,
    time: u64,
    now: u64,
    clock_drift: u64,
    trusting_period: u64,
}

fn window(
    trusted_header_time: Time,
    untrusted_time: Time,
    now: Time,
    clock_drift: Duration,
    trusting_period: Duration,
) -> Result<Window, HeaderVerifyError> {
    let bad = |what: &str| {
        HeaderVerifyError::UnprojectableTime(format!(
            "{what} has no nanosecond projection into the verified gate's Nat domain \
             (pre-epoch or beyond u64)"
        ))
    };
    Ok(Window {
        header_time: time_nanos(trusted_header_time).ok_or_else(|| bad("trusted header time"))?,
        time: time_nanos(untrusted_time).ok_or_else(|| bad("untrusted header time"))?,
        now: time_nanos(now).ok_or_else(|| bad("now"))?,
        clock_drift: duration_nanos(clock_drift).ok_or_else(|| bad("clock drift"))?,
        trusting_period: duration_nanos(trusting_period).ok_or_else(|| bad("trusting period"))?,
    })
}

/// The untrusted set's `(total, Ed25519-verified signed)` power at the `TWO_THIRDS` threshold —
/// the tally both gates share.
///
/// A tally error (a malformed commit, a duplicate validator vote) yields ZERO signed power rather
/// than propagating: zero can only make the gate refuse, and the audited verifier reports the real
/// reason in the conjunction's second half.
fn untrusted_tally(signed_header: &SignedHeader, validators: &ValidatorSet) -> (u64, u64) {
    let calc = ProdVotingPowerCalculator::default();
    let total = calc.total_power_of(validators);
    let signed = calc
        .voting_power_in(signed_header, validators, TrustThreshold::TWO_THIRDS)
        .map(|t| t.tallied)
        .unwrap_or(0);
    (total, signed)
}

/// Both tallies a SKIP needs, computed in ONE pass over the commit
/// (`voting_power_in_sets`, exactly as `check_enough_trust_and_signers` does) so no signature is
/// verified twice: the TRUSTED epoch set at the configured `trust_threshold` (the overlap) and the
/// untrusted set at `TWO_THIRDS`.
fn skip_tallies(
    signed_header: &SignedHeader,
    trusted_next_validators: &ValidatorSet,
    trust_threshold: TrustThreshold,
    untrusted_validators: &ValidatorSet,
) -> (u64, u64, u64, u64) {
    let calc = ProdVotingPowerCalculator::default();
    let trusted_total = calc.total_power_of(trusted_next_validators);
    let total = calc.total_power_of(untrusted_validators);
    match calc.voting_power_in_sets(
        signed_header,
        (trusted_next_validators, trust_threshold),
        (untrusted_validators, TrustThreshold::TWO_THIRDS),
    ) {
        Ok((t, u)) => (trusted_total, t.tallied, total, u.tallied),
        Err(_) => (trusted_total, 0, total, 0),
    }
}

// ---------------------------------------------------------------------------
// The ADJACENT gate — `dregg_tm_lc_verify`
// ---------------------------------------------------------------------------

/// The thirteen scalar/boolean projections `LightClientTendermintGate.tmProjectedDecision` is
/// stated over, in the gate's own order. Building one decides nothing; [`decide`] hands it to the
/// archive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TmProjections {
    /// The untrusted header's chain-id tag.
    pub chain_id: u64,
    /// The trusted state's chain-id tag.
    pub trusted_chain_id: u64,
    /// The untrusted header height.
    pub height: u64,
    /// The trusted state height.
    pub trusted_height: u64,
    /// The trusted header's block time, nanoseconds since epoch.
    pub header_time: u64,
    /// The untrusted header's block time, nanoseconds since epoch.
    pub time: u64,
    /// The verification clock, nanoseconds since epoch.
    pub now: u64,
    /// `DEFAULT_CLOCK_DRIFT` in nanoseconds.
    pub clock_drift: u64,
    /// `Options.trusting_period` in nanoseconds.
    pub trusting_period: u64,
    /// The SHA-256 epoch-binding RESULT: the untrusted validator set hashes to the trusted
    /// header's `next_validators_hash` (the `hashCR` carrier).
    pub epoch_bind_ok: bool,
    /// The SHA-256 self-binding RESULT: the untrusted validator set hashes to the untrusted
    /// header's own `validators_hash` (the `hashCR` carrier).
    pub self_bind_ok: bool,
    /// Total voting power of the untrusted validator set.
    pub total_power: u64,
    /// Ed25519-verified signed power in the untrusted validator set (the `sigSound` carrier).
    pub signed_power: u64,
}

impl TmProjections {
    /// The exact bytes handed to `dregg_tm_lc_verify` (`decodeTmWire`'s grammar). Exposed so a
    /// refusal can carry the wire that produced it and so tests can pin the archive's raw verdict
    /// beside this crate's rendering of it.
    pub fn wire(&self) -> String {
        dregg_lean_ffi::tm_lc_verify_wire(
            self.chain_id,
            self.trusted_chain_id,
            self.height,
            self.trusted_height,
            self.header_time,
            self.time,
            self.now,
            self.clock_drift,
            self.trusting_period,
            self.epoch_bind_ok,
            self.self_bind_ok,
            self.total_power,
            self.signed_power,
        )
    }
}

/// Whether the VERIFIED adjacent-advance gate is reachable (the archive exports
/// `dregg_tm_lc_verify` and the Lean runtime initialised). When false, every adjacent advance in
/// this crate refuses — see the module docs on why there is no fallback.
pub fn available() -> bool {
    dregg_lean_ffi::tm_lc_verify_available()
}

/// Test support: report whether BOTH Cosmos gates are reachable, in the sanctioned form — under
/// `DREGG_TEST_REQUIRE_LEAN` an absent archive FAILS the test rather than letting it pass by
/// skipping. Re-exported here so downstream crates (`dregg-interchain-gov`) get the same semantics
/// without taking a direct `dregg-lean-ffi` dependency, and so a marshal-only build cannot turn a
/// gate test into a silent green.
pub fn demand_both() -> bool {
    dregg_lean_ffi::demand_lean(
        available(),
        "dregg_tm_lc_verify Tendermint ADJACENT light-client gate",
    ) && dregg_lean_ffi::demand_lean(
        skip_available(),
        "dregg_tm_skip_verify Tendermint SKIPPING light-client gate",
    )
}

/// Hand the adjacent projections to the VERIFIED gate and return its verdict.
///
/// `Ok(true)` is the gate's `"1"`. `Ok(false)` is `"0"` **or** `"ERR"` (a malformed wire is
/// fail-closed inside the gate itself). `Err(VerifiedGateUnavailable)` means the archive did not
/// export the decision — a COLD ARCHIVE, never a proved `no`, and the caller must refuse.
pub fn decide(p: &TmProjections) -> Result<bool, HeaderVerifyError> {
    match dregg_lean_ffi::verified_tm_lc_verify(
        p.chain_id,
        p.trusted_chain_id,
        p.height,
        p.trusted_height,
        p.header_time,
        p.time,
        p.now,
        p.clock_drift,
        p.trusting_period,
        p.epoch_bind_ok,
        p.self_bind_ok,
        p.total_power,
        p.signed_power,
    ) {
        Ok(dregg_lean_ffi::TmLcVerdict::Accept) => Ok(true),
        Ok(dregg_lean_ffi::TmLcVerdict::Reject) => Ok(false),
        Err(why) => Err(HeaderVerifyError::VerifiedGateUnavailable(why)),
    }
}

/// The archive's RAW answer for these projections: `"1"` / `"0"` / `"ERR"`, exactly as
/// `dregg_tm_lc_verify` emits it — so a test can read the Lean verdict itself rather than this
/// crate's rendering of it.
pub fn raw(p: &TmProjections) -> Result<String, HeaderVerifyError> {
    dregg_lean_ffi::shadow_tm_lc_verify(&p.wire())
        .map_err(HeaderVerifyError::VerifiedGateUnavailable)
}

/// Run the adjacent gate over an ARBITRARY wire and return the archive's raw output. Exposed so a
/// test can pin the fail-closed `"ERR"` on a malformed or FOREIGN wire — the grammar-drift canary.
pub fn shadow(wire: &str) -> Result<String, HeaderVerifyError> {
    dregg_lean_ffi::shadow_tm_lc_verify(wire).map_err(HeaderVerifyError::VerifiedGateUnavailable)
}

/// Compute the adjacent projections for an update. The cryptography runs here — the SHA-256
/// validator-set hashes and, inside [`tallies`], the audited crate's per-validator Ed25519 commit
/// verification — and only its RESULTS cross into Lean.
#[allow(clippy::too_many_arguments)]
pub(crate) fn project_adjacent(
    trusted_chain_id: &ChainId,
    trusted_header_time: Time,
    trusted_height: u64,
    trusted_next_validators_hash: tendermint::Hash,
    untrusted: &SignedHeader,
    untrusted_validators: &ValidatorSet,
    trusting_period: Duration,
    now: Time,
) -> Result<TmProjections, HeaderVerifyError> {
    let h = &untrusted.header;
    let w = window(
        trusted_header_time,
        h.time,
        now,
        crate::DEFAULT_CLOCK_DRIFT,
        trusting_period,
    )?;
    let vals_hash = untrusted_validators.hash();
    let (total, signed) = untrusted_tally(untrusted, untrusted_validators);
    Ok(TmProjections {
        chain_id: chain_id_tag(&h.chain_id),
        trusted_chain_id: chain_id_tag(trusted_chain_id),
        height: h.height.value(),
        trusted_height,
        header_time: w.header_time,
        time: w.time,
        now: w.now,
        clock_drift: w.clock_drift,
        trusting_period: w.trusting_period,
        epoch_bind_ok: vals_hash == trusted_next_validators_hash,
        self_bind_ok: vals_hash == h.validators_hash,
        total_power: total,
        signed_power: signed,
    })
}

// ---------------------------------------------------------------------------
// The SKIPPING gate — `dregg_tm_skip_verify`
// ---------------------------------------------------------------------------

/// The sixteen projections `LightClientTendermintSkip.tmSkipProjectedDecision` is stated over.
/// Note what is ABSENT relative to [`TmProjections`]: there is no `epoch_bind_ok`, because a skip
/// target's validator set was never committed by the trusted header. Its place is taken by the
/// trust-threshold fraction and the TRUSTED-epoch overlap tally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TmSkipProjections {
    /// The untrusted header's chain-id tag.
    pub chain_id: u64,
    /// The trusted state's chain-id tag.
    pub trusted_chain_id: u64,
    /// The untrusted header height (must be strictly beyond the adjacent one).
    pub height: u64,
    /// The trusted state height.
    pub trusted_height: u64,
    /// The trusted header's block time, nanoseconds since epoch.
    pub header_time: u64,
    /// The untrusted header's block time, nanoseconds since epoch.
    pub time: u64,
    /// The verification clock, nanoseconds since epoch.
    pub now: u64,
    /// `DEFAULT_CLOCK_DRIFT` in nanoseconds.
    pub clock_drift: u64,
    /// `Options.trusting_period` in nanoseconds.
    pub trusting_period: u64,
    /// The SHA-256 self-binding RESULT (the `hashCR` carrier).
    pub self_bind_ok: bool,
    /// `Options.trust_threshold` numerator (canonically 1).
    pub trust_num: u64,
    /// `Options.trust_threshold` denominator (canonically 3).
    pub trust_den: u64,
    /// Total voting power of the TRUSTED next-validator set — the overlap tally base.
    pub trusted_total_power: u64,
    /// Ed25519-verified power of TRUSTED-epoch validators that signed this target (the overlap).
    pub trusted_signed_power: u64,
    /// Total voting power of the untrusted (skip-target) validator set.
    pub total_power: u64,
    /// Ed25519-verified signed power in the untrusted validator set.
    pub signed_power: u64,
}

impl TmSkipProjections {
    /// The exact bytes handed to `dregg_tm_skip_verify` (`decodeTmSkipWire`'s grammar).
    pub fn wire(&self) -> String {
        dregg_lean_ffi::tm_skip_verify_wire(
            self.chain_id,
            self.trusted_chain_id,
            self.height,
            self.trusted_height,
            self.header_time,
            self.time,
            self.now,
            self.clock_drift,
            self.trusting_period,
            self.self_bind_ok,
            self.trust_num,
            self.trust_den,
            self.trusted_total_power,
            self.trusted_signed_power,
            self.total_power,
            self.signed_power,
        )
    }
}

/// Whether the VERIFIED SKIPPING gate is reachable. Probed INDEPENDENTLY of [`available`]: an
/// archive spliced before 2026-07-29 exports the adjacent gate and not this one, and conflating
/// them would advertise a skip gate that cannot render a verdict.
pub fn skip_available() -> bool {
    dregg_lean_ffi::tm_skip_verify_available()
}

/// Hand the skipping projections to the VERIFIED gate and return its verdict. Same contract as
/// [`decide`]: `Err` means COLD ARCHIVE, never a proved `no`.
pub fn decide_skip(p: &TmSkipProjections) -> Result<bool, HeaderVerifyError> {
    match dregg_lean_ffi::verified_tm_skip_verify(
        p.chain_id,
        p.trusted_chain_id,
        p.height,
        p.trusted_height,
        p.header_time,
        p.time,
        p.now,
        p.clock_drift,
        p.trusting_period,
        p.self_bind_ok,
        p.trust_num,
        p.trust_den,
        p.trusted_total_power,
        p.trusted_signed_power,
        p.total_power,
        p.signed_power,
    ) {
        Ok(dregg_lean_ffi::TmSkipVerdict::Accept) => Ok(true),
        Ok(dregg_lean_ffi::TmSkipVerdict::Reject) => Ok(false),
        Err(why) => Err(HeaderVerifyError::VerifiedGateUnavailable(why)),
    }
}

/// The archive's RAW answer for these skipping projections.
pub fn raw_skip(p: &TmSkipProjections) -> Result<String, HeaderVerifyError> {
    dregg_lean_ffi::shadow_tm_skip_verify(&p.wire())
        .map_err(HeaderVerifyError::VerifiedGateUnavailable)
}

/// Run the skipping gate over an ARBITRARY wire and return the archive's raw output — the
/// grammar-drift canary for the sixteen-field wire.
pub fn shadow_skip(wire: &str) -> Result<String, HeaderVerifyError> {
    dregg_lean_ffi::shadow_tm_skip_verify(wire).map_err(HeaderVerifyError::VerifiedGateUnavailable)
}

/// Compute the skipping projections for an update. The cryptography runs here; only its RESULTS
/// cross into Lean. There is no epoch-binding projection by design.
#[allow(clippy::too_many_arguments)]
pub(crate) fn project_skip(
    trusted_chain_id: &ChainId,
    trusted_header_time: Time,
    trusted_height: u64,
    trusted_next_validators: &ValidatorSet,
    untrusted: &SignedHeader,
    untrusted_validators: &ValidatorSet,
    trust_threshold: TrustThreshold,
    trusting_period: Duration,
    now: Time,
) -> Result<TmSkipProjections, HeaderVerifyError> {
    let h = &untrusted.header;
    let w = window(
        trusted_header_time,
        h.time,
        now,
        crate::DEFAULT_CLOCK_DRIFT,
        trusting_period,
    )?;
    let (trusted_total, trusted_signed, total, signed) = skip_tallies(
        untrusted,
        trusted_next_validators,
        trust_threshold,
        untrusted_validators,
    );
    Ok(TmSkipProjections {
        chain_id: chain_id_tag(&h.chain_id),
        trusted_chain_id: chain_id_tag(trusted_chain_id),
        height: h.height.value(),
        trusted_height,
        header_time: w.header_time,
        time: w.time,
        now: w.now,
        clock_drift: w.clock_drift,
        trusting_period: w.trusting_period,
        self_bind_ok: untrusted_validators.hash() == h.validators_hash,
        trust_num: trust_threshold.numerator(),
        trust_den: trust_threshold.denominator(),
        trusted_total_power: trusted_total,
        trusted_signed_power: trusted_signed,
        total_power: total,
        signed_power: signed,
    })
}
