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
