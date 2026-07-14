//! # `beacon` — the drand-beacon → daily-seed wire (the "single most valuable wire").
//!
//! [`daily_seed`](crate::daily_seed) turns a **committed epoch value** into a fresh, fair
//! dungeon seed everyone can re-derive. This module supplies that epoch value from a REAL
//! **threshold public-randomness beacon** (drand / League of Entropy), closing the gap the
//! crate docs name: with a genuine beacon output the daily seed is
//! **unpredictable-until-revealed**, **identical world-wide**, and **verifiable by
//! re-derivation** — the three properties a "today's dungeon everyone plays" needs.
//!
//! ```text
//!   drand round (round, threshold-BLS signature)
//!        │  verify_beacon_round  (BLS pairing e(sig,g2)==e(H(round),pk), output==H(sig))
//!        ▼
//!   beacon output  =  H(signature)   ── the committed epoch value ──▶  daily_seed  ──▶  CommittedSeed
//!        │                                                                                   │
//!        ▼                                                                                   ▼
//!   (unpredictable until the round matures)                                     the day's procgen dungeon
//! ```
//!
//! ## Why the three properties hold
//!
//! - **Unpredictable-until-revealed.** A drand round's output is a *threshold* BLS signature
//!   by the network's distributed key: no coalition below threshold can produce it, so the
//!   day's signature — and therefore the day's seed — does not exist until the round matures.
//!   You cannot grind a favourable dungeon: a forged signature is REFUSED by the pairing check
//!   ([`DailyBeacon::verify`]), and the round is a deterministic function of the day
//!   ([`quicknet_round_for_utc_day`]), so no favourable-round picking either.
//! - **Identical world-wide.** The seed is a pure function of the (public) beacon output, and
//!   the dungeon is a pure function of the seed. Everyone who sees the round derives the same
//!   `CommittedSeed` and re-generates the byte-identical dungeon.
//! - **Verifiable by re-derivation.** Holding only public data — the round, the signature, and
//!   the genesis-pinned drand group key — anyone runs [`DailyBeacon::verify`] then
//!   [`daily_seed`](crate::daily_seed) and re-derives the exact seed, then
//!   [`regenerate`](crate::regenerate) the byte-identical `.dungeon`.
//!
//! ## Honest scope
//!
//! - The **verification** is real drand interop (a BLS pairing check against the pinned
//!   `quicknet` group key; the crate's own tests verify a real published round). The
//!   **producer** half — *fetching* `(round, signature)` from a drand node over HTTP — is a
//!   named client seam, not embedded here (a `DailyBeacon` is built from an already-fetched
//!   round). This keeps the verifier a pure function of public data.
//! - "Unpredictable" is the drand **threshold assumption** (no sub-threshold coalition signs a
//!   future round). This wire *binds* that beacon and makes each day's binding verifiable; it
//!   does not re-prove the threshold assumption.

use dregg_dice::{
    Beacon, BeaconParams, BeaconSchedule, DrandBeacon, VerifyError, verify_beacon_round,
};

use crate::{CommittedSeed, daily_seed};

/// drand `quicknet` genesis unix time (seconds) — the chain's round-1 epoch.
/// Source: `https://api.drand.sh/52db9ba7…c84e971/info` (`genesis_time`).
pub const DRAND_QUICKNET_GENESIS_TIME: u64 = 1_692_803_367;
/// drand `quicknet` round period (seconds). Source: the same `info` endpoint (`period`).
pub const DRAND_QUICKNET_PERIOD_SECS: u64 = 3;

/// The `quicknet` round that has matured at unix time `unix_secs` (the latest round whose
/// signature exists by then). A deterministic function of the clock, so a schedule cannot be
/// nudged to a favourable already-published round.
pub fn quicknet_round_at(unix_secs: u64) -> u64 {
    if unix_secs <= DRAND_QUICKNET_GENESIS_TIME {
        return 1;
    }
    (unix_secs - DRAND_QUICKNET_GENESIS_TIME) / DRAND_QUICKNET_PERIOD_SECS + 1
}

/// The `quicknet` round bound to a UTC **day number** (days since the unix epoch) — the round
/// matured at that day's 00:00:00 UTC. "Today's dungeon" uses today's day number, so the round
/// (and therefore the seed) is a pure, un-grindable function of the date.
///
/// A different day number gives a different round — and once that round is fetched + verified,
/// a different signature, a different output, a different seed, and a different dungeon.
pub fn quicknet_round_for_utc_day(day_number: u64) -> u64 {
    quicknet_round_at(day_number.saturating_mul(86_400))
}

/// A **verifiable daily beacon opening** — one matured public-randomness round bound to a day.
/// Holds exactly the public data a re-deriver needs: the genesis-pinned beacon params (drand
/// group key + scheme, or a hash-chain anchor), the round, its output, and (for a threshold
/// [`dregg_dice::DrandBeacon`]) the round's BLS signature. [`DailyBeacon::verify`] re-checks it
/// with no network; [`DailyBeacon::seed`] turns a verified opening into the day's dungeon seed.
#[derive(Clone, Debug)]
pub struct DailyBeacon {
    /// The genesis-pinned beacon parameters (which network/scheme produced the round).
    pub params: BeaconParams,
    /// The matured round this day draws from.
    pub round: u64,
    /// The beacon output for `round` — the committed epoch value fed to [`daily_seed`].
    /// For drand this is `H(signature)`.
    pub output: [u8; 32],
    /// The round's threshold-BLS signature (drand path), re-checked by the pairing in
    /// [`verify_beacon_round`]. Empty for a hash-chain (single-operator / test) beacon.
    pub signature: Vec<u8>,
}

impl DailyBeacon {
    /// Build a daily beacon from a fetched **drand `quicknet`** round: pins the live network's
    /// group key + scheme and derives the output as drand randomness `H(signature)` (via the
    /// crate's own beacon, so no crypto is duplicated). The signature is NOT trusted here —
    /// [`DailyBeacon::verify`] re-checks it against the pinned key by pairing.
    pub fn quicknet(round: u64, signature: Vec<u8>) -> DailyBeacon {
        // The schedule is irrelevant to a single round's output; pin it to `round`.
        let schedule = BeaconSchedule {
            base_round: round,
            stride: 0,
        };
        let mut beacon = DrandBeacon::quicknet(schedule);
        beacon.insert_round(round, signature.clone());
        let output = beacon.round_output(round);
        DailyBeacon {
            params: beacon.params(),
            round,
            output,
            signature,
        }
    }

    /// Build a daily beacon from explicit parts (a general [`BeaconParams`] — e.g. a
    /// hash-chain test beacon, or a drand round assembled elsewhere). `output` must be the
    /// beacon's output for `round`; `signature` is the round signature (empty for hash-chain).
    pub fn from_parts(
        params: BeaconParams,
        round: u64,
        output: [u8; 32],
        signature: Vec<u8>,
    ) -> DailyBeacon {
        DailyBeacon {
            params,
            round,
            output,
            signature,
        }
    }

    /// **Verify the beacon opening** — the source-free check a re-deriver runs with only public
    /// data. For drand: the BLS pairing `e(sig, g2) == e(H(round), pk)` against the pinned group
    /// key, then `output == H(signature)`. A forged/mutated signature, a wrong round, or a wrong
    /// group key are each rejected — so a favourable-dungeon grind by faking the reveal fails.
    pub fn verify(&self) -> Result<(), VerifyError> {
        verify_beacon_round(&self.params, self.round, &self.output, &self.signature)
    }

    /// The committed epoch value (the verified beacon output) this day's seed derives from.
    pub fn epoch_commitment(&self) -> &[u8; 32] {
        &self.output
    }

    /// **The day's dungeon seed** — verify the opening, then fold the beacon output through
    /// [`daily_seed`]. Everyone who verifies the same round arrives at the identical
    /// [`CommittedSeed`], and thus the byte-identical dungeon. A beacon that does not verify
    /// yields no seed (fail-closed).
    pub fn seed(&self) -> Result<CommittedSeed, VerifyError> {
        self.verify()?;
        Ok(daily_seed(&self.output))
    }
}

/// **Generate today's dungeon from a verified daily beacon** — verify the opening, derive the
/// day's [`CommittedSeed`], and [`generate`](crate::generate) the procgen dungeon. The returned
/// [`GeneratedDungeon`](crate::GeneratedDungeon) re-generates byte-for-byte from the same
/// verified round, and a different day's round gives a different dungeon.
pub fn generate_daily(beacon: &DailyBeacon) -> Result<crate::GeneratedDungeon, VerifyError> {
    let seed = beacon.seed()?;
    Ok(crate::generate(&seed))
}

// ═══════════════════════════════════════════════════════════════════════════════
// The LIVE producer half — fetch today's real `quicknet` round over HTTP, verify it.
//
// The verifier above ([`DailyBeacon::verify`]) was always real drand interop; what was
// the NAMED client seam is closed here: a genuine HTTP GET of today's `quicknet` round
// from a drand node, parsed, built into a [`DailyBeacon`], and BLS-VERIFIED (the same
// pairing check) before it can seed a day. A forged / tampered round fails the pairing
// check and is refused (fail-closed) — it never becomes a dungeon seed. The pinned
// published round ([`pinned_fallback_beacon`]) stays the offline/test fallback: a real
// BLS-verifiable reveal, so an offline day is still beacon-seeded (never a fabricated
// seed), and [`todays_beacon_or_pinned`] serves live-or-pinned transparently.
// ═══════════════════════════════════════════════════════════════════════════════

/// The drand `quicknet` chain hash — the API path segment naming the network whose
/// group key [`dregg_dice`] pins. Source: the drand League-of-Entropy public API.
pub const DRAND_QUICKNET_CHAIN_HASH: &str =
    "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971";

/// The default drand HTTP API base (the public League-of-Entropy endpoint). A caller may
/// override it (a mirror / a private relay) via the `api_base` argument.
pub const DRAND_API_BASE: &str = "https://api.drand.sh";

/// A pinned, REAL published `quicknet` round — the offline/test fallback for when a live fetch is
/// unavailable (no network, a drand outage). Round 1_000_000 and its threshold-BLS signature; the
/// same vector `dregg-dice`'s interop test pins. Its pairing check holds, so the offline day is a
/// genuine beacon-seeded day (not a fabricated seed).
pub const PINNED_FALLBACK_ROUND: u64 = 1_000_000;
/// The pinned fallback round's threshold-BLS signature (hex) — re-checked by pairing on every use.
pub const PINNED_FALLBACK_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

/// Why a **live** drand fetch could not produce a verified beacon. Every variant is fail-closed:
/// nothing seeds a day unless the fetched round PASSED the pairing check.
#[derive(Debug)]
pub enum FetchError {
    /// The HTTP GET failed (unreachable node, a non-2xx status, a transport error).
    Http(String),
    /// The response body did not parse as a drand round (missing/!numeric `round`, missing/!hex
    /// `signature`), or the returned round did not match the requested one.
    Parse(String),
    /// The round was fetched + parsed but its threshold-BLS signature FAILED the pairing check
    /// against the pinned `quicknet` group key — a forged / tampered / wrong-network round.
    Verify(VerifyError),
}

impl std::fmt::Display for FetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FetchError::Http(m) => write!(f, "drand HTTP fetch failed: {m}"),
            FetchError::Parse(m) => write!(f, "drand round did not parse: {m}"),
            FetchError::Verify(e) => write!(f, "drand round failed BLS verification: {e:?}"),
        }
    }
}

impl std::error::Error for FetchError {}

/// The URL of a specific `quicknet` round on a drand HTTP API base — a pure function (no network),
/// so the request target is testable without a socket.
pub fn quicknet_round_url(api_base: &str, round: u64) -> String {
    format!(
        "{}/{}/public/{}",
        api_base.trim_end_matches('/'),
        DRAND_QUICKNET_CHAIN_HASH,
        round
    )
}

/// Parse a drand `public/{round}` JSON body into `(round, signature_bytes)` — a pure function. The
/// beacon **output** is re-derived from the signature by [`DailyBeacon::quicknet`] (as `H(sig)`),
/// so only the round number and the signature are read; the body's `randomness` is not trusted.
pub fn parse_round_json(body: &str) -> Result<(u64, Vec<u8>), FetchError> {
    let v: serde_json::Value =
        serde_json::from_str(body).map_err(|e| FetchError::Parse(e.to_string()))?;
    let round = v
        .get("round")
        .and_then(|r| r.as_u64())
        .ok_or_else(|| FetchError::Parse("missing or non-numeric `round`".to_string()))?;
    let sig_hex = v
        .get("signature")
        .and_then(|s| s.as_str())
        .ok_or_else(|| FetchError::Parse("missing or non-string `signature`".to_string()))?;
    let sig = hex::decode(sig_hex)
        .map_err(|e| FetchError::Parse(format!("`signature` is not hex: {e}")))?;
    Ok((round, sig))
}

/// Build a **verified** [`DailyBeacon`] from a fetched round body — parse, build, and BLS-verify in
/// one fail-closed step. A body whose signature does not pass the pairing check against the pinned
/// `quicknet` group key is [`FetchError::Verify`]; a `round` other than `expected_round` is
/// [`FetchError::Parse`] (the node returned the wrong round). This is the pure core the live
/// [`fetch_quicknet_round`] wraps, so the verify path is exercised without a network.
pub fn verified_beacon_from_body(
    expected_round: u64,
    body: &str,
) -> Result<DailyBeacon, FetchError> {
    let (round, signature) = parse_round_json(body)?;
    if round != expected_round {
        return Err(FetchError::Parse(format!(
            "requested round {expected_round} but the node returned round {round}"
        )));
    }
    let beacon = DailyBeacon::quicknet(round, signature);
    beacon.verify().map_err(FetchError::Verify)?;
    Ok(beacon)
}

/// One blocking HTTP GET of a URL, returning the response body text. Blocking (not async): the
/// caller drives it from a `spawn_blocking` on their own runtime, keeping this crate free of an
/// ambient tokio dependency at its API.
fn http_get(url: &str) -> Result<String, FetchError> {
    let client = reqwest::blocking::Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .user_agent("dregg-descent-beacon/1.0")
        .build()
        .map_err(|e| FetchError::Http(e.to_string()))?;
    let resp = client
        .get(url)
        .send()
        .map_err(|e| FetchError::Http(e.to_string()))?;
    if !resp.status().is_success() {
        return Err(FetchError::Http(format!(
            "drand node returned HTTP {}",
            resp.status()
        )));
    }
    resp.text().map_err(|e| FetchError::Http(e.to_string()))
}

/// **Fetch + verify a specific `quicknet` round over HTTP.** GET the round from `api_base`, parse
/// the body, build the [`DailyBeacon`], and BLS-verify it against the pinned group key before
/// returning — the returned beacon is ALWAYS verified (a forged / tampered round is refused). This
/// is a blocking call; drive it off a `spawn_blocking` on an async runtime.
pub fn fetch_quicknet_round(api_base: &str, round: u64) -> Result<DailyBeacon, FetchError> {
    let url = quicknet_round_url(api_base, round);
    let body = http_get(&url)?;
    verified_beacon_from_body(round, &body)
}

/// The current UTC **day number** (days since the unix epoch) from the system clock — the day
/// [`quicknet_round_for_utc_day`] binds today's round to.
pub fn current_utc_day() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() / 86_400)
        .unwrap_or(0)
}

/// **Fetch + verify TODAY's `quicknet` round** — the round bound to the current UTC day
/// ([`quicknet_round_for_utc_day`]), fetched live from `api_base` and BLS-verified. This is The
/// Descent's real daily beacon: unpredictable until the round matured, identical world-wide, and
/// verifiable by re-derivation. Blocking; drive it off a `spawn_blocking`.
pub fn fetch_todays_beacon(api_base: &str) -> Result<DailyBeacon, FetchError> {
    let round = quicknet_round_for_utc_day(current_utc_day());
    fetch_quicknet_round(api_base, round)
}

/// The pinned offline-fallback beacon — a real published, BLS-verifiable `quicknet` round. Always
/// verifies (a genuine reveal), so an offline / pre-fetch day is still beacon-seeded.
pub fn pinned_fallback_beacon() -> DailyBeacon {
    DailyBeacon::quicknet(
        PINNED_FALLBACK_ROUND,
        hex::decode(PINNED_FALLBACK_SIG_HEX).expect("the pinned drand signature decodes"),
    )
}

/// **Today's beacon, live-or-pinned.** Try a live drand fetch of today's UTC-day round (BLS-verified);
/// on ANY failure — no network, a drand outage, a wrong/forged round — fall back to the pinned
/// published round. Either way the returned beacon is VERIFIED: a forged live round is refused (the
/// pinned reveal stands in) and the pinned reveal is itself a genuine BLS-verifiable round, so The
/// Descent always opens on a real beacon-seeded day, never a fabricated seed.
pub fn todays_beacon_or_pinned(api_base: &str) -> DailyBeacon {
    match fetch_todays_beacon(api_base) {
        Ok(beacon) => beacon,
        Err(_) => pinned_fallback_beacon(),
    }
}

#[cfg(test)]
mod fetch_tests {
    use super::*;

    /// A drand `public/{round}` JSON body for the pinned published round — the exact shape a
    /// drand node returns (`{round, randomness, signature}`), built from a real verifiable
    /// signature so the verify path is driven WITHOUT a network.
    fn pinned_round_body() -> String {
        // randomness = H(signature); re-derived by the beacon, so any value is fine here — we set
        // the real output so the body is byte-faithful to what a node serves.
        let beacon = pinned_fallback_beacon();
        format!(
            "{{\"round\":{},\"randomness\":\"{}\",\"signature\":\"{}\"}}",
            PINNED_FALLBACK_ROUND,
            hex::encode(beacon.output),
            PINNED_FALLBACK_SIG_HEX,
        )
    }

    /// THE LIVE-FETCH VERIFY PATH, DRIVEN OFFLINE: a real published round body parses, builds, and
    /// BLS-VERIFIES, and derives the day's seed — the exact path `fetch_quicknet_round` runs after
    /// the GET, exercised without a socket.
    #[test]
    fn a_real_fetched_round_body_verifies_and_seeds_the_day() {
        let beacon = verified_beacon_from_body(PINNED_FALLBACK_ROUND, &pinned_round_body())
            .expect("a real published round body verifies");
        // The verified beacon derives a day seed (fail-closed: verify ran inside `seed`).
        let seed = beacon
            .seed()
            .expect("a verified beacon yields the day's seed");
        // Determinism: the same fetched round re-derives the identical seed.
        assert_eq!(
            seed.as_bytes(),
            pinned_fallback_beacon().seed().unwrap().as_bytes(),
            "the fetched round derives the same seed everyone re-derives"
        );
    }

    /// A FORGED / tampered round body is REFUSED by the pairing check (fail-closed) — a favourable
    /// dungeon cannot be grinded by faking the reveal. NON-VACUOUS: the honest body above verifies.
    #[test]
    fn a_forged_fetched_round_body_is_refused() {
        // Flip one nibble of the signature hex — the pairing check must reject it.
        let mut sig = hex::decode(PINNED_FALLBACK_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged_body = format!(
            "{{\"round\":{},\"randomness\":\"00\",\"signature\":\"{}\"}}",
            PINNED_FALLBACK_ROUND,
            hex::encode(&sig),
        );
        let out = verified_beacon_from_body(PINNED_FALLBACK_ROUND, &forged_body);
        assert!(
            matches!(out, Err(FetchError::Verify(_))),
            "a forged round signature fails the BLS pairing check, got {out:?}"
        );
    }

    /// A wrong-round response (the node returned a different round than requested) is refused before
    /// any verify — the schedule cannot be nudged to a favourable already-published round.
    #[test]
    fn a_wrong_round_response_is_refused() {
        let out = verified_beacon_from_body(PINNED_FALLBACK_ROUND + 1, &pinned_round_body());
        assert!(
            matches!(out, Err(FetchError::Parse(_))),
            "a round mismatch is refused, got {out:?}"
        );
    }

    /// A malformed body is a parse error (fail-closed), not a panic.
    #[test]
    fn a_malformed_body_is_a_parse_error() {
        assert!(matches!(
            verified_beacon_from_body(PINNED_FALLBACK_ROUND, "not json"),
            Err(FetchError::Parse(_))
        ));
        assert!(matches!(
            verified_beacon_from_body(PINNED_FALLBACK_ROUND, "{\"round\":1}"),
            Err(FetchError::Parse(_))
        ));
    }

    /// The request URL is the canonical drand `public/{round}` path (pure — no network).
    #[test]
    fn the_round_url_is_the_canonical_drand_path() {
        assert_eq!(
            quicknet_round_url("https://api.drand.sh", 1_000_000),
            format!("https://api.drand.sh/{DRAND_QUICKNET_CHAIN_HASH}/public/1000000")
        );
        // A trailing slash on the base is normalized.
        assert_eq!(
            quicknet_round_url("https://api.drand.sh/", 42),
            format!("https://api.drand.sh/{DRAND_QUICKNET_CHAIN_HASH}/public/42")
        );
    }

    /// THE OFFLINE FALLBACK, DRIVEN: a live fetch against an unreachable base FAILS, and
    /// `todays_beacon_or_pinned` falls back to the pinned round — which itself VERIFIES + seeds a
    /// day. So an offline day is still a genuine beacon-seeded day.
    #[test]
    fn an_unreachable_fetch_falls_back_to_the_verified_pinned_round() {
        // Port 9 (discard) on loopback: the GET fails fast (refused), no external network.
        let unreachable = "http://127.0.0.1:9/drand";
        assert!(
            fetch_todays_beacon(unreachable).is_err(),
            "an unreachable node fails the live fetch"
        );
        let beacon = todays_beacon_or_pinned(unreachable);
        // The fallback beacon is verified and seeds the day.
        assert!(
            beacon.seed().is_ok(),
            "the pinned fallback verifies + seeds a day"
        );
    }

    /// A LIVE network fetch of today's real `quicknet` round — verifies the round exists, the BLS
    /// pairing check holds, and the day seed derives. Network-gated (ignored by default so the
    /// offline suite stays green); run with `--ignored` on a networked host to validate live drand.
    #[test]
    #[ignore = "hits the live drand network; run with --ignored on a networked host"]
    fn live_drand_fetch_of_todays_round_verifies() {
        let beacon =
            fetch_todays_beacon(DRAND_API_BASE).expect("today's live drand round verifies");
        let seed = beacon.seed().expect("the live round derives today's seed");
        assert_ne!(seed.as_bytes(), &[0u8; 32], "a real seed");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// THE HYBRID DAY SEED — drand ‖ a PQ-authenticated finalized root.
//
//   daily_seed = H(domain ‖ drand_output ‖ finalized_merkle_root)
//
// The drand half above is a THRESHOLD BLS signature — unbiasable, but CLASSICAL:
// a quantum adversary who breaks BLS can forge a round and grind the day. The
// federation's finalized ledger root is the other half: it is authenticated by the
// node's HYBRID finalization quorum (`node/src/finalization_votes.rs` —
// `FinalizationVote` carries BOTH an ed25519 AND an ML-DSA-65 (FIPS 204) signature
// over `dregg-finalization-vote-v2 ‖ block_id ‖ merkle_root`, and a vote counts only
// when BOTH verify), so the root is POST-QUANTUM unforgeable — but a within-threshold
// proposer can grind block content to steer `H(root)`, so it is not on its own
// bias-resistant.
//
// Folding both closes each other's gap:
//   * PQ-UNFORGEABLE — a quantum adversary who forges the drand round still cannot
//     move the root half (that needs an ML-DSA-65 quorum forgery).
//   * UNBIASABLE IF EITHER SOURCE IS HONEST — an honest drand round is a uniform,
//     unique value the root-grinder cannot see (the ORDERING tooth below), so a
//     ground root only permutes an unknown-to-it uniform value; and an honest
//     federation root fixes an input the drand side cannot bias at all (drand rounds
//     are unique per round, and the round is a pure function of the day).
//   * NATIVE-DEGRADABLE — drand down ⇒ root-only; the federation absent (offline /
//     test) ⇒ the existing drand-only or pinned path, unchanged.
//
// THE ORDERING TOOTH. The root must be FIXED BEFORE the drand round it mixes with
// MATURES (by at least one drand period). Otherwise a proposer who has already SEEN
// the day's drand output could grind the root against it and steer the composed seed.
// [`FinalizedRootAttestation::fixed_before_round`] enforces exactly that, and the
// seed derivation is fail-closed on it.
//
// The federation types are CONSUMED, never re-implemented: the preimage is
// `dregg_types::finalization_vote_signing_message` (the same bytes the node signs and
// the persistence layer re-verifies) and the quorum rule is
// `dregg_federation::receipt::verify_hybrid_quorum_sigs` (the same `classical ∧ pq`
// check with the ENROLLED-PQ-key PIN — a signer may not bring its own ML-DSA key).
// ═══════════════════════════════════════════════════════════════════════════════

use dregg_federation::frost::MlDsaPublicKey;
use dregg_types::{HybridQuorumSig, PublicKey};

/// Domain tag for the HYBRID day seed: `H(tag ‖ drand_output ‖ finalized_merkle_root)`.
/// Distinct from [`crate::DOMAIN_DAILY_SEED`] and [`DOMAIN_ROOT_ONLY_DAY_SEED`], so a
/// hybrid day, a drand-only day, and a root-only day can never alias to the same seed.
pub const DOMAIN_HYBRID_DAY_SEED: &[u8] = b"dregg-descent-hybrid-day-seed-v1";

/// Domain tag for the DEGRADED root-only day seed (drand unavailable): the day is seeded
/// by the PQ-authenticated finalized root alone.
pub const DOMAIN_ROOT_ONLY_DAY_SEED: &[u8] = b"dregg-descent-root-only-day-seed-v1";

/// The minimum lead the finalized root must have over the drand round it is mixed with:
/// the root must be fixed at least one full drand period BEFORE that round matures. A
/// root fixed inside the maturing period could have been ground against a drand output
/// already in flight, so it is refused.
pub const MIN_ROOT_LEAD_SECS: u64 = DRAND_QUICKNET_PERIOD_SECS;

/// The unix time at which `quicknet` round `round` MATURES (its threshold signature
/// exists). Round 1 matures at genesis; round `r` at `genesis + (r-1)·period`. Inverse of
/// [`quicknet_round_at`], and the clock the [ordering tooth](FinalizedRootAttestation::fixed_before_round)
/// measures the root's fixing time against.
pub fn quicknet_round_matures_at(round: u64) -> u64 {
    DRAND_QUICKNET_GENESIS_TIME + round.saturating_sub(1) * DRAND_QUICKNET_PERIOD_SECS
}

/// The genesis-PINNED federation committee a re-deriver checks a finalized root against:
/// the ed25519 signer set and the ENROLLED ML-DSA-65 roster, aligned INDEX-FOR-INDEX
/// (member `i` of one is member `i` of the other, exactly as genesis publishes them), plus
/// the quorum threshold (`2f+1`).
///
/// The enrolled PQ roster is what makes the post-quantum half real: a quorum signature
/// carries a copy of the signer's ML-DSA key, but it is PINNED equal to the enrolled key
/// here and never trusted on its own — so an adversary who breaks ed25519 for a member
/// cannot attach its OWN ML-DSA keypair and pass the PQ half.
#[derive(Clone, Debug)]
pub struct FederationCommittee {
    ed25519: Vec<PublicKey>,
    ml_dsa: Vec<MlDsaPublicKey>,
    quorum_threshold: usize,
}

impl FederationCommittee {
    /// Pin a committee. FAIL-CLOSED: a roster misaligned in length (an EMPTY ML-DSA roster
    /// included — "hybrid not configured"), a vacuous `quorum_threshold == 0`, or a
    /// threshold larger than the committee is REFUSED here rather than silently degrading
    /// to an ed25519-only check later.
    pub fn new(
        ed25519: Vec<PublicKey>,
        ml_dsa: Vec<MlDsaPublicKey>,
        quorum_threshold: usize,
    ) -> Result<FederationCommittee, RootError> {
        if ed25519.len() != ml_dsa.len() || ed25519.is_empty() {
            return Err(RootError::MisalignedCommittee {
                ed25519: ed25519.len(),
                ml_dsa: ml_dsa.len(),
            });
        }
        if quorum_threshold == 0 {
            return Err(RootError::VacuousThreshold);
        }
        if quorum_threshold > ed25519.len() {
            return Err(RootError::ThresholdExceedsCommittee {
                threshold: quorum_threshold,
                committee: ed25519.len(),
            });
        }
        Ok(FederationCommittee {
            ed25519,
            ml_dsa,
            quorum_threshold,
        })
    }

    /// The committee size (distinct members).
    pub fn size(&self) -> usize {
        self.ed25519.len()
    }

    /// The quorum threshold (`2f+1`) a finalized root must meet.
    pub fn quorum_threshold(&self) -> usize {
        self.quorum_threshold
    }
}

/// Why a finalized root could not authenticate a day. Every variant is fail-closed: no
/// day is seeded from a root whose HYBRID quorum did not verify, or whose fixing time did
/// not precede the drand round it is mixed with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RootError {
    /// The pinned committee's ed25519 and ML-DSA rosters are not index-aligned (or are
    /// empty) — there is no well-defined enrolled PQ key to pin a signer against.
    MisalignedCommittee {
        /// The ed25519 roster length.
        ed25519: usize,
        /// The ML-DSA roster length.
        ml_dsa: usize,
    },
    /// A `0` quorum threshold — a vacuous quorum would accept anything.
    VacuousThreshold,
    /// The threshold exceeds the committee size: no quorum could ever form.
    ThresholdExceedsCommittee {
        /// The configured threshold.
        threshold: usize,
        /// The committee size.
        committee: usize,
    },
    /// The root's HYBRID quorum did not verify: too few distinct signers, a non-member
    /// signer, a bad ed25519 half, an ML-DSA key that is not the signer's ENROLLED key, or
    /// a bad / missing ML-DSA half. There is no ed25519-only downgrade.
    QuorumRefused,
    /// THE ORDERING TOOTH: the root was not fixed strictly before (by at least
    /// [`MIN_ROOT_LEAD_SECS`]) the drand round it is being mixed with matured — so its
    /// proposer could have been grinding it against an already-known drand output.
    RootFixedAfterRound {
        /// When the root was fixed (finalized) — the attestation's `fixed_at_unix`.
        fixed_at_unix: u64,
        /// The drand round it was to be mixed with.
        round: u64,
        /// When that round matured.
        round_matures_at: u64,
    },
}

impl std::fmt::Display for RootError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RootError::MisalignedCommittee { ed25519, ml_dsa } => write!(
                f,
                "the pinned committee is misaligned ({ed25519} ed25519 keys vs {ml_dsa} ML-DSA keys)"
            ),
            RootError::VacuousThreshold => write!(f, "a zero quorum threshold is vacuous"),
            RootError::ThresholdExceedsCommittee {
                threshold,
                committee,
            } => write!(
                f,
                "quorum threshold {threshold} exceeds the {committee}-member committee"
            ),
            RootError::QuorumRefused => write!(
                f,
                "the finalized root's hybrid (ed25519 ∧ ML-DSA-65) quorum did not verify"
            ),
            RootError::RootFixedAfterRound {
                fixed_at_unix,
                round,
                round_matures_at,
            } => write!(
                f,
                "the finalized root was fixed at {fixed_at_unix}, not at least {MIN_ROOT_LEAD_SECS}s \
                 before drand round {round} matured at {round_matures_at} — a root-grinder could \
                 have seen the drand output"
            ),
        }
    }
}

impl std::error::Error for RootError {}

/// A **PQ-authenticated finalized ledger root**, carried with the HYBRID-quorum evidence a
/// re-deriver re-checks against the pinned committee — the post-quantum half of the day
/// seed.
///
/// The `quorum` is exactly the record the node assembles
/// (`node/src/finalization_votes.rs::VoteCollector::assembled_quorum`) and the persistence
/// layer stores as an attested root's `finalization_quorum`: per distinct signer, the
/// ed25519 signature AND the ML-DSA-65 signature over the ONE canonical preimage
/// `dregg-finalization-vote-v2 ‖ block_id ‖ merkle_root`. Nothing is re-signed here — the
/// day seed folds the federation's own finality evidence.
///
/// `fixed_at_unix` is WHEN the root was fixed (the finalized block's time, as observed /
/// recorded by the party that pinned this root). It is the ordering witness: the root must
/// have been fixed before the drand round it is mixed with matured
/// ([`FinalizedRootAttestation::fixed_before_round`]).
#[derive(Clone, Debug)]
pub struct FinalizedRootAttestation {
    /// The finalized blocklace block id the quorum signed.
    pub block_id: [u8; 32],
    /// The finalized canonical ledger root the quorum signed — the value folded into the
    /// day seed.
    pub merkle_root: [u8; 32],
    /// When this root was FIXED (unix seconds) — the ordering witness (see the type docs).
    pub fixed_at_unix: u64,
    /// The hybrid finalization quorum over `(block_id, merkle_root)`: per distinct signer,
    /// the ed25519 half + the ML-DSA-65 half + the signer's (pinned) ML-DSA public key.
    pub quorum: Vec<HybridQuorumSig>,
}

impl FinalizedRootAttestation {
    /// The exact bytes the federation's finalization quorum signed —
    /// [`dregg_types::finalization_vote_signing_message`], the single source of truth the
    /// node's `FinalizationVote` and the persisted restart anchor both use. Re-derived here,
    /// never re-defined.
    pub fn signing_message(&self) -> Vec<u8> {
        dregg_types::finalization_vote_signing_message(&self.block_id, &self.merkle_root)
    }

    /// **Verify the PQ half.** Re-check the finalized root's HYBRID quorum against the
    /// pinned `committee`: at least `quorum_threshold` DISTINCT committee signers, each of
    /// whose ed25519 signature AND ML-DSA-65 (FIPS 204) signature verify over
    /// [`Self::signing_message`], with each signer's carried ML-DSA key PINNED equal to its
    /// ENROLLED roster key.
    ///
    /// A forged / corrupted ML-DSA half, a signer bringing its own ML-DSA key, a non-member
    /// signer, or too few distinct signers ⇒ [`RootError::QuorumRefused`]. The PQ half BITES:
    /// a perfectly valid ed25519 quorum with a bad ML-DSA half is refused, so a quantum
    /// adversary who breaks ed25519 alone cannot author the root half of a day.
    pub fn verify(&self, committee: &FederationCommittee) -> Result<(), RootError> {
        let message = self.signing_message();
        let ok = dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &self.quorum,
            &message,
            &committee.ed25519,
            &committee.ml_dsa,
            committee.quorum_threshold,
        );
        if ok {
            Ok(())
        } else {
            Err(RootError::QuorumRefused)
        }
    }

    /// **The ORDERING tooth.** The root must have been fixed at least [`MIN_ROOT_LEAD_SECS`]
    /// BEFORE `round` matured. A root fixed at-or-after the round's maturity could have been
    /// ground against a drand output its proposer already saw — refused, so the composed seed
    /// is never steerable by a proposer who knows the day's drand value.
    pub fn fixed_before_round(&self, round: u64) -> Result<(), RootError> {
        let round_matures_at = quicknet_round_matures_at(round);
        if self.fixed_at_unix + MIN_ROOT_LEAD_SECS <= round_matures_at {
            Ok(())
        } else {
            Err(RootError::RootFixedAfterRound {
                fixed_at_unix: self.fixed_at_unix,
                round,
                round_matures_at,
            })
        }
    }
}

/// **The HYBRID day seed** — `H(DOMAIN_HYBRID_DAY_SEED ‖ drand_output ‖ finalized_merkle_root)`.
/// A pure function of two public, independently-verified 32-byte values, so every player
/// re-derives the byte-identical [`CommittedSeed`] (and thus the byte-identical dungeon)
/// from the drand round + the finalized root + its quorum.
pub fn hybrid_day_seed(drand_output: &[u8; 32], finalized_root: &[u8; 32]) -> CommittedSeed {
    let mut h = crate::blake3_domain(DOMAIN_HYBRID_DAY_SEED);
    h.update(drand_output);
    h.update(finalized_root);
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// **The DEGRADED root-only day seed** — `H(DOMAIN_ROOT_ONLY_DAY_SEED ‖ finalized_merkle_root)`,
/// for a day on which drand has no liveness. Still PQ-authenticated (the root's hybrid quorum is
/// verified before this is called) and still world-identical + re-derivable; it gives up drand's
/// bias-resistance, so on such a day a within-threshold proposer could grind the root. Named,
/// not hidden: [`DaySeedSource::Root`] is a DEGRADED mode, entered only when the drand half is
/// unavailable.
pub fn root_only_day_seed(finalized_root: &[u8; 32]) -> CommittedSeed {
    let mut h = crate::blake3_domain(DOMAIN_ROOT_ONLY_DAY_SEED);
    h.update(finalized_root);
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// Why a day could not be seeded. Fail-closed in every variant: a day is seeded only from
/// sources that VERIFIED.
#[derive(Debug)]
pub enum DaySeedError {
    /// The drand round failed its BLS pairing check (forged / tampered / wrong network).
    Beacon(VerifyError),
    /// The finalized root failed its hybrid-quorum check or the ordering tooth.
    Root(RootError),
    /// A root-bearing source was offered with NO pinned committee to check it against. There
    /// is no "trust the root" path — without the committee the PQ half cannot be verified, so
    /// the day is refused (the caller may fall back to the drand-only / pinned path).
    CommitteeMissing,
}

impl std::fmt::Display for DaySeedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DaySeedError::Beacon(e) => write!(f, "the drand round failed verification: {e:?}"),
            DaySeedError::Root(e) => write!(f, "the finalized root was refused: {e}"),
            DaySeedError::CommitteeMissing => write!(
                f,
                "a finalized-root source needs a pinned committee to verify its PQ quorum"
            ),
        }
    }
}

impl std::error::Error for DaySeedError {}

/// **Where a day's seed comes from** — the hybrid source, or one of the two native
/// degradations. Every variant derives its seed ONLY after re-verifying its evidence.
#[derive(Clone, Debug)]
pub enum DaySeedSource {
    /// The EXISTING drand-only day (a live-fetched round, or the pinned published round).
    /// Byte-for-byte the seed [`DailyBeacon::seed`] already derives — nothing regresses.
    Drand(DailyBeacon),
    /// The HYBRID day: a BLS-verified drand round AND a PQ-authenticated finalized root that
    /// was fixed before the round matured. PQ-unforgeable and unbiasable if EITHER source is
    /// honest.
    Hybrid {
        /// The drand round (BLS-verified on every use).
        beacon: DailyBeacon,
        /// The finalized root + its hybrid quorum (re-verified on every use).
        root: FinalizedRootAttestation,
    },
    /// DEGRADED: drand has no liveness, so the day is seeded by the PQ-authenticated
    /// finalized root alone.
    Root(FinalizedRootAttestation),
}

impl DaySeedSource {
    /// Re-verify EVERYTHING this source rests on, with no network: the drand round's BLS
    /// pairing (where present), the finalized root's hybrid ed25519 ∧ ML-DSA-65 quorum against
    /// the pinned `committee` (where present), and — for the hybrid day — the ORDERING tooth
    /// (the root was fixed before the drand round matured).
    pub fn verify(&self, committee: Option<&FederationCommittee>) -> Result<(), DaySeedError> {
        match self {
            DaySeedSource::Drand(beacon) => beacon.verify().map_err(DaySeedError::Beacon),
            DaySeedSource::Hybrid { beacon, root } => {
                beacon.verify().map_err(DaySeedError::Beacon)?;
                let committee = committee.ok_or(DaySeedError::CommitteeMissing)?;
                root.verify(committee).map_err(DaySeedError::Root)?;
                root.fixed_before_round(beacon.round)
                    .map_err(DaySeedError::Root)
            }
            DaySeedSource::Root(root) => {
                let committee = committee.ok_or(DaySeedError::CommitteeMissing)?;
                root.verify(committee).map_err(DaySeedError::Root)
            }
        }
    }

    /// **The day's seed** — verify (above), then derive. Fail-closed: a source that does not
    /// verify yields NO seed. Pure: the same verified source re-derives the byte-identical
    /// [`CommittedSeed`] on every host.
    pub fn seed(
        &self,
        committee: Option<&FederationCommittee>,
    ) -> Result<CommittedSeed, DaySeedError> {
        self.verify(committee)?;
        Ok(match self {
            // The UNCHANGED legacy derivation — a drand-only day seeds exactly as before.
            DaySeedSource::Drand(beacon) => daily_seed(&beacon.output),
            DaySeedSource::Hybrid { beacon, root } => {
                hybrid_day_seed(&beacon.output, &root.merkle_root)
            }
            DaySeedSource::Root(root) => root_only_day_seed(&root.merkle_root),
        })
    }

    /// Generate the day's dungeon from this (verified) source.
    pub fn generate(
        &self,
        committee: Option<&FederationCommittee>,
    ) -> Result<crate::GeneratedDungeon, DaySeedError> {
        Ok(crate::generate(&self.seed(committee)?))
    }
}

/// **Today's day-seed source, resolved with NATIVE DEGRADATION.** Prefer the hybrid day; fall
/// back rather than fail:
///
/// 1. **Hybrid** — a live drand round verifies AND the offered root's hybrid quorum verifies
///    against the pinned committee AND the root was fixed before that round matured.
/// 2. **Drand-only (live)** — drand is up but the federation half is absent / unverifiable /
///    too late (an offline player, a test, a root that fails the ordering tooth): the existing
///    drand-only day, unchanged.
/// 3. **Root-only** — drand has no liveness but the federation root verifies: the day is still
///    PQ-authenticated (degraded: no drand bias-resistance).
/// 4. **Pinned** — neither is available: the pinned, genuinely BLS-verifiable published round.
///
/// The returned source is not trusted on the strength of this resolution — [`DaySeedSource::seed`]
/// re-verifies it from scratch.
pub fn todays_day_seed_source(
    api_base: &str,
    root: Option<FinalizedRootAttestation>,
    committee: Option<&FederationCommittee>,
) -> DaySeedSource {
    let live = fetch_todays_beacon(api_base).ok();
    // The root half is admissible only if its PQ quorum verifies against a pinned committee.
    let verified_root = match (root, committee) {
        (Some(r), Some(c)) if r.verify(c).is_ok() => Some(r),
        _ => None,
    };
    match (live, verified_root) {
        (Some(beacon), Some(root)) => {
            // The ORDERING tooth decides hybrid-vs-drand-only: a root that was NOT fixed before
            // today's round matured is not mixed in (it could have been ground against it).
            if root.fixed_before_round(beacon.round).is_ok() {
                DaySeedSource::Hybrid { beacon, root }
            } else {
                DaySeedSource::Drand(beacon)
            }
        }
        (Some(beacon), None) => DaySeedSource::Drand(beacon),
        (None, Some(root)) => DaySeedSource::Root(root),
        (None, None) => DaySeedSource::Drand(pinned_fallback_beacon()),
    }
}

#[cfg(test)]
mod hybrid_tests {
    use super::*;
    use dregg_federation::frost::MlDsaSigningKey;
    use ed25519_dalek::{Signer, SigningKey};

    /// A member's (ed25519, ML-DSA-65) keypair from one seed byte — the production
    /// derivation (`genesis.rs` publishes the public halves from the same node key).
    fn member(seed: u8) -> (SigningKey, MlDsaSigningKey, PublicKey, MlDsaPublicKey) {
        let sk = SigningKey::from_bytes(&[seed; 32]);
        let (pq_pk, pq_sk) = MlDsaSigningKey::from_seed(&[seed; 32]);
        let ed_pk = PublicKey(sk.verifying_key().to_bytes());
        (sk, pq_sk, ed_pk, pq_pk)
    }

    /// The pinned committee for a set of member seeds (index-aligned rosters, as genesis
    /// publishes them) at threshold `t`.
    fn committee(seeds: &[u8], t: usize) -> FederationCommittee {
        let (eds, pqs): (Vec<_>, Vec<_>) = seeds
            .iter()
            .map(|&s| {
                let (_, _, ed, pq) = member(s);
                (ed, pq)
            })
            .unzip();
        FederationCommittee::new(eds, pqs, t).expect("a well-formed pinned committee")
    }

    /// One member's REAL hybrid quorum signature over the canonical finalization preimage:
    /// a genuine ed25519 signature AND a genuine ML-DSA-65 signature over the same bytes.
    fn hybrid_sig(seed: u8, block_id: &[u8; 32], merkle_root: &[u8; 32]) -> HybridQuorumSig {
        let (sk, pq_sk, ed_pk, pq_pk) = member(seed);
        let msg = dregg_types::finalization_vote_signing_message(block_id, merkle_root);
        HybridQuorumSig {
            pubkey: ed_pk,
            signature: dregg_types::Signature(sk.sign(&msg).to_bytes()),
            ml_dsa_pubkey: pq_pk.0.to_vec(),
            pq_signature: pq_sk.sign(&msg).expect("ML-DSA hedged signing"),
        }
    }

    const BLOCK_ID: [u8; 32] = [0xB1; 32];
    const ROOT_A: [u8; 32] = [0x5A; 32];
    const ROOT_B: [u8; 32] = [0x77; 32];

    /// A root fixed comfortably before the pinned round matured (the honest ordering).
    fn attestation(seeds: &[u8], root: [u8; 32]) -> FinalizedRootAttestation {
        FinalizedRootAttestation {
            block_id: BLOCK_ID,
            merkle_root: root,
            // One hour before the pinned fallback round matured.
            fixed_at_unix: quicknet_round_matures_at(PINNED_FALLBACK_ROUND) - 3_600,
            quorum: seeds
                .iter()
                .map(|&s| hybrid_sig(s, &BLOCK_ID, &root))
                .collect(),
        }
    }

    /// THE HYBRID SEED, DRIVEN: a BLS-verified drand round + a PQ-authenticated finalized root
    /// derive the day's seed; it is a PURE re-derivable function of BOTH halves (same inputs ⇒
    /// byte-identical seed), and it genuinely DEPENDS on each half — a different root gives a
    /// different seed (so the root half is not decorative), and it differs from the drand-only
    /// seed (so the domains do not alias).
    #[test]
    fn the_hybrid_seed_derives_from_both_halves_and_re_derives_identically() {
        let com = committee(&[1, 2, 3], 3);
        let beacon = pinned_fallback_beacon();
        let src = DaySeedSource::Hybrid {
            beacon: beacon.clone(),
            root: attestation(&[1, 2, 3], ROOT_A),
        };
        let seed = src.seed(Some(&com)).expect("the hybrid day seeds");

        // PURE: an independently-rebuilt source with the same inputs re-derives byte-identically.
        let again = DaySeedSource::Hybrid {
            beacon: beacon.clone(),
            root: attestation(&[1, 2, 3], ROOT_A),
        }
        .seed(Some(&com))
        .unwrap();
        assert_eq!(
            seed.as_bytes(),
            again.as_bytes(),
            "the hybrid seed re-derives"
        );
        // And it IS the advertised derivation H(domain ‖ drand_output ‖ root).
        assert_eq!(
            seed.as_bytes(),
            hybrid_day_seed(&beacon.output, &ROOT_A).as_bytes()
        );

        // NON-VACUOUS in the root half: a DIFFERENT finalized root ⇒ a different day.
        let other = DaySeedSource::Hybrid {
            beacon: beacon.clone(),
            root: attestation(&[1, 2, 3], ROOT_B),
        }
        .seed(Some(&com))
        .unwrap();
        assert_ne!(
            seed.as_bytes(),
            other.as_bytes(),
            "a different finalized root MUST give a different seed"
        );

        // NON-VACUOUS in the drand half: a different drand output ⇒ a different day.
        assert_ne!(
            hybrid_day_seed(&beacon.output, &ROOT_A).as_bytes(),
            hybrid_day_seed(&[0x11; 32], &ROOT_A).as_bytes(),
            "a different drand output MUST give a different seed"
        );

        // The hybrid day is NOT the drand-only day (distinct domains, no aliasing).
        assert_ne!(seed.as_bytes(), daily_seed(&beacon.output).as_bytes());
    }

    /// THE PQ HALF BITES: a quorum whose ML-DSA-65 signatures are FORGED is REFUSED — even
    /// though every ed25519 half is perfectly valid. This is the property the whole hybrid
    /// exists for: an adversary who breaks the classical half alone cannot author a day's root.
    /// NON-VACUOUS: the same quorum with its honest ML-DSA halves verifies (above).
    #[test]
    fn a_root_with_a_forged_ml_dsa_half_is_refused() {
        let com = committee(&[1, 2, 3], 3);
        let mut root = attestation(&[1, 2, 3], ROOT_A);
        // Corrupt ONLY the post-quantum half of one signer's evidence.
        root.quorum[1].pq_signature[0] ^= 0xFF;

        assert_eq!(
            root.verify(&com),
            Err(RootError::QuorumRefused),
            "a forged ML-DSA half must never authenticate a day's root"
        );
        let src = DaySeedSource::Hybrid {
            beacon: pinned_fallback_beacon(),
            root,
        };
        assert!(
            matches!(
                src.seed(Some(&com)),
                Err(DaySeedError::Root(RootError::QuorumRefused))
            ),
            "the day is fail-closed on the PQ half"
        );

        // An EMPTY PQ half is equally refused (no silent ed25519-only downgrade).
        let mut stripped = attestation(&[1, 2, 3], ROOT_A);
        stripped.quorum[0].pq_signature = Vec::new();
        assert_eq!(stripped.verify(&com), Err(RootError::QuorumRefused));
    }

    /// THE ENROLLED-KEY PIN: an adversary who has broken ed25519 for member 2 attaches its OWN
    /// ML-DSA keypair and a PQ signature that is perfectly valid UNDER THAT KEY. Refused: the PQ
    /// half is checked against the member's GENESIS-ENROLLED ML-DSA key, which the adversary does
    /// not hold. Without this pin the "post-quantum" half would be self-certifying theatre.
    #[test]
    fn a_signer_may_not_bring_its_own_ml_dsa_key() {
        let com = committee(&[1, 2, 3], 3);
        let mut root = attestation(&[1, 2, 3], ROOT_A);

        // The adversary's own (unenrolled) ML-DSA keypair, signing the real message.
        let (adv_pk, adv_sk) = MlDsaSigningKey::from_seed(&[0xEE; 32]);
        let msg = dregg_types::finalization_vote_signing_message(&BLOCK_ID, &ROOT_A);
        let adv_sig = adv_sk.sign(&msg).expect("ML-DSA hedged signing");
        assert!(
            adv_pk.verify(&msg, &adv_sig),
            "precondition: the swapped PQ evidence is internally consistent"
        );
        root.quorum[1].ml_dsa_pubkey = adv_pk.0.to_vec();
        root.quorum[1].pq_signature = adv_sig;

        assert_eq!(
            root.verify(&com),
            Err(RootError::QuorumRefused),
            "a self-carried ML-DSA key that is not the enrolled one must be refused"
        );
    }

    /// INSUFFICIENT QUORUM and NON-MEMBER signers are refused — the root half needs a genuine
    /// 2f+1 of the pinned committee.
    #[test]
    fn an_insufficient_or_non_member_quorum_is_refused() {
        let com = committee(&[1, 2, 3], 3);
        // Only 2 of the required 3 distinct signers.
        assert_eq!(
            attestation(&[1, 2], ROOT_A).verify(&com),
            Err(RootError::QuorumRefused)
        );
        // A duplicate signer does not make up the numbers.
        assert_eq!(
            attestation(&[1, 2, 2], ROOT_A).verify(&com),
            Err(RootError::QuorumRefused)
        );
        // An outsider's perfectly-formed hybrid signature does not count.
        assert_eq!(
            attestation(&[1, 2, 9], ROOT_A).verify(&com),
            Err(RootError::QuorumRefused)
        );
        // The honest 3-of-3 quorum verifies (non-vacuity).
        assert_eq!(attestation(&[1, 2, 3], ROOT_A).verify(&com), Ok(()));
    }

    /// FAIL-CLOSED CONFIGURATION: an unconfigured hybrid (an empty ML-DSA roster) or a vacuous
    /// threshold cannot be pinned as a committee at all — there is no configuration under which
    /// the PQ check silently degrades to ed25519-only.
    #[test]
    fn a_misconfigured_committee_is_refused_at_construction() {
        let (_, _, ed, pq) = member(1);
        assert!(matches!(
            FederationCommittee::new(vec![ed], Vec::new(), 1),
            Err(RootError::MisalignedCommittee { .. })
        ));
        assert!(matches!(
            FederationCommittee::new(vec![ed], vec![pq.clone()], 0),
            Err(RootError::VacuousThreshold)
        ));
        assert!(matches!(
            FederationCommittee::new(vec![ed], vec![pq], 2),
            Err(RootError::ThresholdExceedsCommittee { .. })
        ));
    }

    /// THE DRAND HALF STILL BITES in the hybrid day: a forged drand round is refused by the BLS
    /// pairing check even though the finalized root is impeccable. Both halves are load-bearing.
    #[test]
    fn a_forged_drand_round_is_refused_in_the_hybrid_day() {
        let com = committee(&[1, 2, 3], 3);
        let mut sig = hex::decode(PINNED_FALLBACK_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged = DailyBeacon::quicknet(PINNED_FALLBACK_ROUND, sig);
        let src = DaySeedSource::Hybrid {
            beacon: forged,
            root: attestation(&[1, 2, 3], ROOT_A),
        };
        assert!(
            matches!(src.seed(Some(&com)), Err(DaySeedError::Beacon(_))),
            "a forged drand round never seeds a day, hybrid or not"
        );
    }

    /// THE ORDERING TOOTH, DRIVEN. A root fixed at or after the drand round it is mixed with
    /// MATURED is REFUSED — otherwise its proposer could have ground the root against a drand
    /// output it had already seen. A root fixed one full drand period before the round is
    /// accepted, so the tooth is a boundary, not a blanket refusal.
    #[test]
    fn a_root_fixed_after_the_drand_round_matured_is_refused() {
        let com = committee(&[1, 2, 3], 3);
        let beacon = pinned_fallback_beacon();
        let matured = quicknet_round_matures_at(beacon.round);

        // The tooth's exact boundary: fixed EXACTLY one period before maturity — accepted.
        let mut ok_root = attestation(&[1, 2, 3], ROOT_A);
        ok_root.fixed_at_unix = matured - MIN_ROOT_LEAD_SECS;
        assert_eq!(ok_root.fixed_before_round(beacon.round), Ok(()));
        assert!(
            DaySeedSource::Hybrid {
                beacon: beacon.clone(),
                root: ok_root,
            }
            .seed(Some(&com))
            .is_ok()
        );

        // One second INSIDE the maturing period — refused (the drand value was in flight).
        let mut late = attestation(&[1, 2, 3], ROOT_A);
        late.fixed_at_unix = matured - MIN_ROOT_LEAD_SECS + 1;
        assert!(matches!(
            late.fixed_before_round(beacon.round),
            Err(RootError::RootFixedAfterRound { .. })
        ));

        // Fixed AFTER the round matured — the grinder's dream, refused, and the day is
        // fail-closed on it (a QUORUM-VALID root is still refused: the tooth is independent
        // of the quorum check).
        let mut ground = attestation(&[1, 2, 3], ROOT_A);
        ground.fixed_at_unix = matured + 60;
        assert_eq!(ground.verify(&com), Ok(()), "the quorum itself is genuine");
        let src = DaySeedSource::Hybrid {
            beacon,
            root: ground,
        };
        assert!(
            matches!(
                src.seed(Some(&com)),
                Err(DaySeedError::Root(RootError::RootFixedAfterRound { .. }))
            ),
            "a root fixed after the drand round matured must never seed a day"
        );
    }

    /// NO SILENT DOWNGRADE: a root-bearing source offered WITHOUT a pinned committee yields no
    /// seed at all (the PQ half cannot be checked, so the root is not trusted).
    #[test]
    fn a_root_without_a_pinned_committee_seeds_nothing() {
        let src = DaySeedSource::Hybrid {
            beacon: pinned_fallback_beacon(),
            root: attestation(&[1, 2, 3], ROOT_A),
        };
        assert!(matches!(
            src.seed(None),
            Err(DaySeedError::CommitteeMissing)
        ));
        assert!(matches!(
            DaySeedSource::Root(attestation(&[1, 2, 3], ROOT_A)).seed(None),
            Err(DaySeedError::CommitteeMissing)
        ));
    }

    /// THE FALLBACKS, EACH DERIVING A VERIFIED SEED — nothing regresses and nothing is
    /// fabricated:
    ///   * drand-only (the pinned published round) seeds EXACTLY as it does today (byte-identical
    ///     to the pre-hybrid `DailyBeacon::seed`);
    ///   * root-only (drand down) seeds from the PQ-authenticated root;
    ///   * the three modes are mutually distinct (no aliasing).
    #[test]
    fn every_fallback_still_derives_a_verified_seed() {
        let com = committee(&[1, 2, 3], 3);
        let beacon = pinned_fallback_beacon();

        // Drand-only: BYTE-IDENTICAL to the existing (pre-hybrid) day seed.
        let drand_only = DaySeedSource::Drand(beacon.clone())
            .seed(None)
            .expect("the drand-only day still seeds with no committee at all");
        assert_eq!(
            drand_only.as_bytes(),
            beacon.seed().unwrap().as_bytes(),
            "the drand-only path is unchanged"
        );

        // Root-only (drand has no liveness): the PQ-authenticated root seeds the day.
        let root_only = DaySeedSource::Root(attestation(&[1, 2, 3], ROOT_A))
            .seed(Some(&com))
            .expect("the root-only day seeds");
        assert_eq!(root_only.as_bytes(), root_only_day_seed(&ROOT_A).as_bytes());
        // ...and a bad root still seeds NOTHING in the degraded mode (the PQ half bites there too).
        let mut bad = attestation(&[1, 2, 3], ROOT_A);
        bad.quorum[0].pq_signature[0] ^= 0xFF;
        assert!(DaySeedSource::Root(bad).seed(Some(&com)).is_err());

        // Hybrid, and the three modes are distinct seeds for the same day inputs.
        let hybrid = DaySeedSource::Hybrid {
            beacon,
            root: attestation(&[1, 2, 3], ROOT_A),
        }
        .seed(Some(&com))
        .unwrap();
        assert_ne!(hybrid.as_bytes(), drand_only.as_bytes());
        assert_ne!(hybrid.as_bytes(), root_only.as_bytes());
        assert_ne!(drand_only.as_bytes(), root_only.as_bytes());
    }

    /// THE RESOLVER'S NATIVE DEGRADATION, DRIVEN OFFLINE (loopback port 9 — no external
    /// network, the fetch fails fast):
    ///   * federation present  ⇒ ROOT-ONLY (drand is down, the PQ half still authenticates the day);
    ///   * federation absent   ⇒ the PINNED drand round (the pre-existing behaviour, unchanged);
    ///   * a root whose PQ quorum does NOT verify is NOT mixed in — it degrades to pinned drand
    ///     rather than seeding a day off unverified evidence.
    #[test]
    fn the_resolver_degrades_natively_when_drand_is_unreachable() {
        let unreachable = "http://127.0.0.1:9/drand";
        let com = committee(&[1, 2, 3], 3);

        // Drand down + a verified federation root ⇒ the root-only day.
        let src = todays_day_seed_source(
            unreachable,
            Some(attestation(&[1, 2, 3], ROOT_A)),
            Some(&com),
        );
        assert!(matches!(src, DaySeedSource::Root(_)));
        assert_eq!(
            src.seed(Some(&com)).unwrap().as_bytes(),
            root_only_day_seed(&ROOT_A).as_bytes()
        );

        // Drand down + no federation ⇒ the pinned published round (unchanged behaviour).
        let src = todays_day_seed_source(unreachable, None, None);
        assert!(matches!(src, DaySeedSource::Drand(_)));
        assert_eq!(
            src.seed(None).unwrap().as_bytes(),
            pinned_fallback_beacon().seed().unwrap().as_bytes()
        );

        // Drand down + a root whose PQ quorum is FORGED ⇒ the root is dropped, NOT folded in.
        let mut bad = attestation(&[1, 2, 3], ROOT_A);
        bad.quorum[2].pq_signature[0] ^= 0xFF;
        let src = todays_day_seed_source(unreachable, Some(bad), Some(&com));
        assert!(
            matches!(src, DaySeedSource::Drand(_)),
            "an unverifiable root never seeds a day; the resolver degrades to drand"
        );
        assert!(src.seed(Some(&com)).is_ok());
    }

    /// A LIVE hybrid day: today's real drand round + a PQ-authenticated root fixed before it
    /// matured. Network-gated (the offline suite stays green).
    #[test]
    #[ignore = "hits the live drand network; run with --ignored on a networked host"]
    fn live_hybrid_day_seeds() {
        let com = committee(&[1, 2, 3], 3);
        let beacon = fetch_todays_beacon(DRAND_API_BASE).expect("today's live round verifies");
        let mut root = attestation(&[1, 2, 3], ROOT_A);
        // Fixed a day before today's round matured (the honest deploy ordering).
        root.fixed_at_unix = quicknet_round_matures_at(beacon.round) - 86_400;
        let seed = DaySeedSource::Hybrid { beacon, root }
            .seed(Some(&com))
            .expect("the live hybrid day seeds");
        assert_ne!(seed.as_bytes(), &[0u8; 32]);
    }
}
