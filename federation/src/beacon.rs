//! Randomness beacon — the ORGANS §6 shortcut: a committee threshold-signature
//! beacon over the BLS12-381 machinery already in this crate.
//!
//! `beacon_at(epoch, height) = blake3(BEACON_DOMAIN ‖ σ)` where
//! `σ = threshold_signature(BEACON_DOMAIN ‖ epoch ‖ height)` is the UNIQUE
//! BLS group signature: `σ = H(msg)^{f(0)}` for the Shamir-shared group secret
//! `f(0)`. Uniqueness is the unbiasability — ANY t-subset of honest shares
//! Lagrange-combines to the SAME point, so no member (and no aggregator
//! choosing among quorum subsets) can steer the output; no subset below the
//! threshold can compute it early (that would be a BLS forgery / Shamir
//! reconstruction below t).
//!
//! # Why this is NOT built on [`crate::threshold`] (`hints`) — report from the weld
//!
//! ORGANS §6 says "real BLS threshold signatures exist in the federation
//! crate" and calls the group signature deterministic. The hinTS scheme in
//! [`crate::threshold`] is real and threshold, **but its aggregate is
//! SUBSET-DEPENDENT**: `sign_aggregate` computes `(Σ_{i∈S} partial_i)/n` over
//! whichever signer set S showed up (`hints/src/lib.rs`,
//! `sign_aggregate_inner`), plus a SNARK proof over the subset bitmap.
//! Different quorums ⇒ different signatures ⇒ an aggregator could grind over
//! C(n,t) subsets to bias `hash(σ)`. That makes hinTS the right tool for
//! quorum CERTIFICATES (any quorum is as good as any other) and the wrong
//! tool for a BEACON. The executable witness is
//! `hints_aggregate_is_subset_dependent_hence_not_a_beacon` below.
//!
//! So this module is the thin signing context the task anticipated: the same
//! curve, the same RFC 9380 `hash_to_g2`, the same field — with a
//! Shamir-shared single group secret so the signature is the classical unique
//! threshold-BLS value. The dealer-based share issuance is the deliberate
//! shortcut (the dealer transiently knows `f(0)`); the VRF-grade upgrade
//! replaces the dealer with a DKG and adds per-output proofs of correct
//! evaluation — see the module-level NOTES at the bottom.
//!
//! # Domain separation
//!
//! Signed-message domain tags already in this crate (audited 2026-06-12):
//! `dregg-strand-vouch-v1`, `dregg-strand-bond-v1` (admission, Ed25519);
//! `dregg-epoch-transition-v1` (epoch certs); `dregg-reconfig-proposal-v1`
//! (node); `dregg-federation-vote-v1`, `dregg-view-change-v1` (types, the BLS
//! vote paths); `dregg-fed-id-v1` (identity, blake3 derive_key);
//! `dregg-share-mac-v1`, `dregg-threshold-tag-v1` (threshold_decrypt);
//! `dregg-nullifier-log-entry-v1` (solo); `state-roots-v1` (types). The
//! beacon signs under [`BEACON_DOMAIN`] = `dregg-randomness-beacon-v1`, which
//! collides with none of them (and is not a prefix of any, nor any of it);
//! the output and draw hashes use the distinct blake3 derive_key contexts
//! `dregg-beacon-output-v1` / `dregg-beacon-draw-v1`. Beacon shares are a
//! separately-dealt key, so cross-protocol signature reuse against the vote
//! paths is impossible at the key level too — the domain tag is defense in
//! depth.

use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{Field, UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{RngCore, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};

use hints::snark::Curve;
use hints::utils::hash_to_g2;
use hints::{F, G1, G2};

/// Domain tag for the beacon's signed message. See the module docs for the
/// audit of every other domain tag in this crate.
pub const BEACON_DOMAIN: &[u8] = b"dregg-randomness-beacon-v1";

/// blake3 derive_key context for hashing the group signature into the
/// 32-byte beacon output.
const OUTPUT_CONTEXT: &str = "dregg-beacon-output-v1";

/// blake3 derive_key context for the deterministic draw stream seeded by a
/// beacon output.
const DRAW_CONTEXT: &str = "dregg-beacon-draw-v1";

// =============================================================================
// Errors
// =============================================================================

/// Errors from the beacon layer.
#[derive(Debug, PartialEq, Eq)]
pub enum BeaconError {
    /// n == 0, t == 0, or t > n.
    InvalidParameters,
    /// Fewer than `need` VALID partials after fail-closed filtering.
    InsufficientPartials {
        /// Valid, deduplicated partials seen.
        got: usize,
        /// The committee threshold.
        need: usize,
    },
    /// The combined signature failed final verification (should be
    /// unreachable if partials verified; kept as belt and braces).
    AggregationFailed,
    /// Byte-level decode failure.
    SerializationError,
}

impl std::fmt::Display for BeaconError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BeaconError::InvalidParameters => write!(f, "invalid beacon committee parameters"),
            BeaconError::InsufficientPartials { got, need } => {
                write!(f, "insufficient valid beacon partials: {got} < {need}")
            }
            BeaconError::AggregationFailed => write!(f, "beacon aggregation failed final verify"),
            BeaconError::SerializationError => write!(f, "beacon serialization error"),
        }
    }
}

impl std::error::Error for BeaconError {}

// =============================================================================
// Message + output hashing
// =============================================================================

/// The exact byte string the committee threshold-signs for `(epoch, height)`:
/// `BEACON_DOMAIN ‖ epoch_be ‖ height_be` (fixed-width fields, so the framing
/// is unambiguous).
pub fn beacon_message(epoch: u64, height: u64) -> Vec<u8> {
    let mut msg = Vec::with_capacity(BEACON_DOMAIN.len() + 16);
    msg.extend_from_slice(BEACON_DOMAIN);
    msg.extend_from_slice(&epoch.to_be_bytes());
    msg.extend_from_slice(&height.to_be_bytes());
    msg
}

/// `blake3_derive(OUTPUT_CONTEXT, BEACON_DOMAIN ‖ σ_compressed)` — the public
/// randomness derived from the unique group signature.
fn beacon_randomness(signature: &G2) -> [u8; 32] {
    let mut sig_bytes = Vec::new();
    signature
        .serialize_compressed(&mut sig_bytes)
        .expect("G2 compression cannot fail");
    let mut h = blake3::Hasher::new_derive_key(OUTPUT_CONTEXT);
    h.update(BEACON_DOMAIN);
    h.update(&sig_bytes);
    *h.finalize().as_bytes()
}

// =============================================================================
// Committee / shares / partials / output
// =============================================================================

/// The PUBLIC side of a beacon committee: the group public key, the per-share
/// public keys (so partials are individually verifiable before aggregation),
/// and the threshold. Holding only [`BeaconCommittee::group_public`] suffices
/// to verify finished beacons via [`verify_beacon`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BeaconCommittee {
    group_public: G1,
    share_publics: Vec<G1>,
    threshold: usize,
}

/// A member's SECRET beacon share: the Shamir evaluation `f(index)` of the
/// group secret. Held by one committee member; never serialized by this
/// module.
#[derive(Clone)]
pub struct BeaconShare {
    /// 1-based Shamir evaluation point (0 is the group secret itself).
    pub index: usize,
    secret: F,
}

/// One member's partial beacon signature `H(msg)^{f(index)}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BeaconPartial {
    /// The signing member's 1-based share index.
    pub index: usize,
    point: G2,
}

/// A finished beacon: the unique group signature over
/// `beacon_message(epoch, height)` plus the derived 32-byte randomness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BeaconOutput {
    /// The epoch this beacon is bound to.
    pub epoch: u64,
    /// The height this beacon is bound to.
    pub height: u64,
    signature: G2,
    /// `blake3_derive(OUTPUT_CONTEXT, BEACON_DOMAIN ‖ σ)` — the public coin.
    pub randomness: [u8; 32],
}

impl BeaconCommittee {
    /// Deal a fresh beacon key: Shamir-split a random group secret into `n`
    /// shares with threshold `t`, using OS entropy.
    ///
    /// # Security
    /// The dealer transiently knows the group secret. This is the deliberate
    /// ORGANS §6 shortcut; the VRF-grade upgrade replaces this with a DKG.
    pub fn deal(n: usize, t: usize) -> Result<(Self, Vec<BeaconShare>), BeaconError> {
        Self::deal_with_rng(n, t, &mut ark_std::rand::rngs::OsRng)
    }

    /// Deal from a caller-supplied seed. Reproducible — for test fixtures and
    /// differentials only.
    pub fn deal_with_seed(
        n: usize,
        t: usize,
        seed: [u8; 32],
    ) -> Result<(Self, Vec<BeaconShare>), BeaconError> {
        let mut rng = StdRng::from_seed(seed);
        Self::deal_with_rng(n, t, &mut rng)
    }

    /// Deal from a caller-supplied RNG.
    pub fn deal_with_rng(
        n: usize,
        t: usize,
        rng: &mut impl RngCore,
    ) -> Result<(Self, Vec<BeaconShare>), BeaconError> {
        if n == 0 || t == 0 || t > n {
            return Err(BeaconError::InvalidParameters);
        }
        // Degree t-1 polynomial; f(0) = coeffs[0] = the group secret.
        let coeffs: Vec<F> = (0..t).map(|_| F::rand(rng)).collect();
        let eval = |x: F| {
            coeffs
                .iter()
                .rev()
                .fold(F::zero(), |acc, c| acc * x + c)
        };

        let g1 = G1::generator();
        let mut shares = Vec::with_capacity(n);
        let mut share_publics = Vec::with_capacity(n);
        for i in 1..=n {
            let secret = eval(F::from(i as u64));
            share_publics.push((g1 * secret).into_affine());
            shares.push(BeaconShare { index: i, secret });
        }
        let committee = Self {
            group_public: (g1 * coeffs[0]).into_affine(),
            share_publics,
            threshold: t,
        };
        Ok((committee, shares))
    }

    /// The group public key — all anyone needs to verify finished beacons.
    pub fn group_public(&self) -> &G1 {
        &self.group_public
    }

    /// The committee threshold t.
    pub fn threshold(&self) -> usize {
        self.threshold
    }

    /// Committee size n.
    pub fn num_members(&self) -> usize {
        self.share_publics.len()
    }

    /// Verify one member's partial against its share public key and the
    /// domain-separated message for `(epoch, height)`. Fail-closed: unknown
    /// index, identity point, or pairing mismatch all reject.
    pub fn verify_partial(&self, partial: &BeaconPartial, epoch: u64, height: u64) -> bool {
        if partial.index == 0 || partial.index > self.share_publics.len() {
            return false;
        }
        if partial.point.is_zero() || !partial.point.is_in_correct_subgroup_assuming_on_curve() {
            return false;
        }
        let share_pub = self.share_publics[partial.index - 1];
        let h_m = hash_to_g2(&beacon_message(epoch, height));
        Curve::pairing(G1::generator(), partial.point) == Curve::pairing(share_pub, h_m)
    }

    /// Aggregate partials into the beacon for `(epoch, height)`.
    ///
    /// Fail-closed: every partial is verified against its share public key
    /// (invalid or duplicate-index partials are dropped); fewer than t valid
    /// partials is an error. Any t valid partials Lagrange-combine to the
    /// SAME group signature — the subset choice cannot steer the output.
    pub fn aggregate(
        &self,
        partials: &[BeaconPartial],
        epoch: u64,
        height: u64,
    ) -> Result<BeaconOutput, BeaconError> {
        let mut seen = vec![false; self.share_publics.len()];
        let mut valid: Vec<&BeaconPartial> = Vec::new();
        for p in partials {
            if p.index == 0 || p.index > seen.len() || seen[p.index - 1] {
                continue;
            }
            if !self.verify_partial(p, epoch, height) {
                continue;
            }
            seen[p.index - 1] = true;
            valid.push(p);
        }
        if valid.len() < self.threshold {
            return Err(BeaconError::InsufficientPartials {
                got: valid.len(),
                need: self.threshold,
            });
        }
        // Any t of the valid partials suffice; uniqueness makes the choice
        // irrelevant (witnessed by `same_output_from_any_quorum_subset`).
        let chosen = &valid[..self.threshold];
        let xs: Vec<F> = chosen.iter().map(|p| F::from(p.index as u64)).collect();

        let mut sigma = <Curve as Pairing>::G2::zero();
        for (k, p) in chosen.iter().enumerate() {
            // Lagrange basis at 0: λ_k = Π_{j≠k} x_j / (x_j − x_k).
            let mut lambda = F::from(1u64);
            for (j, xj) in xs.iter().enumerate() {
                if j == k {
                    continue;
                }
                let denom = (*xj - xs[k])
                    .inverse()
                    .expect("distinct 1-based indices, nonzero denominator");
                lambda *= *xj * denom;
            }
            sigma += p.point * lambda;
        }
        let signature = sigma.into_affine();
        let out = BeaconOutput {
            epoch,
            height,
            signature,
            randomness: beacon_randomness(&signature),
        };
        if !verify_beacon(&self.group_public, &out) {
            return Err(BeaconError::AggregationFailed);
        }
        Ok(out)
    }

    /// Verify a finished beacon against this committee's group key.
    pub fn verify_beacon(&self, out: &BeaconOutput) -> bool {
        verify_beacon(&self.group_public, out)
    }

    /// Serialize the public committee (threshold, group key, share keys).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        (self.threshold as u64, self.group_public, &self.share_publics)
            .serialize_compressed(&mut buf)
            .expect("serialization cannot fail");
        buf
    }

    /// Deserialize a public committee. Validates curve points (compressed
    /// arkworks deserialization checks subgroup membership).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, BeaconError> {
        let (threshold, group_public, share_publics): (u64, G1, Vec<G1>) =
            CanonicalDeserialize::deserialize_compressed(bytes)
                .map_err(|_| BeaconError::SerializationError)?;
        let threshold = threshold as usize;
        if threshold == 0 || threshold > share_publics.len() {
            return Err(BeaconError::InvalidParameters);
        }
        Ok(Self {
            group_public,
            share_publics,
            threshold,
        })
    }
}

impl BeaconShare {
    /// Produce this member's partial beacon signature for `(epoch, height)`:
    /// `H(BEACON_DOMAIN ‖ epoch ‖ height)^{f(index)}`. Deterministic — no
    /// per-signature randomness exists to grind.
    pub fn sign(&self, epoch: u64, height: u64) -> BeaconPartial {
        let h_m = hash_to_g2(&beacon_message(epoch, height));
        BeaconPartial {
            index: self.index,
            point: (h_m * self.secret).into_affine(),
        }
    }
}

impl BeaconOutput {
    /// The group signature, compressed (96 bytes).
    pub fn signature_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.signature
            .serialize_compressed(&mut buf)
            .expect("G2 compression cannot fail");
        buf
    }

    /// Serialize: epoch ‖ height ‖ σ ‖ randomness.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        (self.epoch, self.height, self.signature, self.randomness)
            .serialize_compressed(&mut buf)
            .expect("serialization cannot fail");
        buf
    }

    /// Deserialize (validates the curve point). The result still must pass
    /// [`verify_beacon`] before being trusted.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, BeaconError> {
        let (epoch, height, signature, randomness): (u64, u64, G2, [u8; 32]) =
            CanonicalDeserialize::deserialize_compressed(bytes)
                .map_err(|_| BeaconError::SerializationError)?;
        Ok(Self {
            epoch,
            height,
            signature,
            randomness,
        })
    }
}

impl Serialize for BeaconOutput {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

impl<'de> Deserialize<'de> for BeaconOutput {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Deserialize::deserialize(deserializer)?;
        Self::from_bytes(&bytes).map_err(serde::de::Error::custom)
    }
}

/// Verify a beacon with ONLY the group public key, fail-closed on everything:
/// identity/out-of-subgroup points reject; a signature over any other epoch,
/// height, or domain fails the pairing (the message is recomputed HERE from
/// the claimed `(epoch, height)` under [`BEACON_DOMAIN`], so a verifier can
/// never be talked into checking a foreign message); a tampered `randomness`
/// fails the recomputation.
pub fn verify_beacon(group_public: &G1, out: &BeaconOutput) -> bool {
    if group_public.is_zero() || !group_public.is_in_correct_subgroup_assuming_on_curve() {
        return false;
    }
    if out.signature.is_zero() || !out.signature.is_in_correct_subgroup_assuming_on_curve() {
        return false;
    }
    let h_m = hash_to_g2(&beacon_message(out.epoch, out.height));
    if Curve::pairing(G1::generator(), out.signature) != Curve::pairing(*group_public, h_m) {
        return false;
    }
    beacon_randomness(&out.signature) == out.randomness
}

/// Convenience orchestration (the single-machine collapse of the committee
/// round): sign with the given shares and aggregate. In a distributed
/// deployment each member runs [`BeaconShare::sign`] and any node aggregates.
pub fn beacon_at(
    committee: &BeaconCommittee,
    shares: &[BeaconShare],
    epoch: u64,
    height: u64,
) -> Result<BeaconOutput, BeaconError> {
    let partials: Vec<BeaconPartial> = shares.iter().map(|s| s.sign(epoch, height)).collect();
    committee.aggregate(&partials, epoch, height)
}

// =============================================================================
// Consumer surface: deterministic draws (jury selection wants this)
// =============================================================================

/// A deterministic, unbiased draw stream seeded by a beacon output
/// (blake3 XOF under [`DRAW_CONTEXT`]). Everyone holding the same beacon
/// derives the same draws.
pub struct BeaconDraw {
    reader: blake3::OutputReader,
}

impl BeaconDraw {
    /// Seed a draw stream from beacon randomness.
    pub fn new(randomness: &[u8; 32]) -> Self {
        let mut h = blake3::Hasher::new_derive_key(DRAW_CONTEXT);
        h.update(randomness);
        Self {
            reader: h.finalize_xof(),
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut buf = [0u8; 8];
        self.reader.fill(&mut buf);
        u64::from_be_bytes(buf)
    }

    /// Draw uniformly from `0..range` (rejection sampling — no modulo bias).
    /// `None` iff `range == 0`.
    pub fn draw(&mut self, range: u64) -> Option<u64> {
        if range == 0 {
            return None;
        }
        // Largest multiple of `range` that fits in 2^64; accept below it.
        let zone: u128 = (1u128 << 64) - ((1u128 << 64) % range as u128);
        loop {
            let x = self.next_u64();
            if (x as u128) < zone {
                return Some(x % range);
            }
        }
    }

    /// Draw `k` DISTINCT indices from `0..pool` (partial Fisher–Yates).
    /// `None` iff `k > pool`.
    pub fn select_distinct(&mut self, pool: usize, k: usize) -> Option<Vec<usize>> {
        if k > pool {
            return None;
        }
        let mut idx: Vec<usize> = (0..pool).collect();
        for i in 0..k {
            let j = i + self.draw((pool - i) as u64)? as usize;
            idx.swap(i, j);
        }
        idx.truncate(k);
        Some(idx)
    }
}

/// One uniform draw from `0..range`, deterministic given the beacon
/// randomness. `None` iff `range == 0`.
pub fn deterministic_draw(randomness: &[u8; 32], range: u64) -> Option<u64> {
    BeaconDraw::new(randomness).draw(range)
}

/// Jury selection: `k` distinct indices from a pool of `pool` candidates,
/// deterministic given the beacon randomness. `None` iff `k > pool`.
pub fn select_jury(randomness: &[u8; 32], pool: usize, k: usize) -> Option<Vec<usize>> {
    BeaconDraw::new(randomness).select_distinct(pool, k)
}

// =============================================================================
// NOTES — the VRF-grade upgrade (what would change later)
// =============================================================================
//
// 1. DKG instead of a dealer: Pedersen/Gennaro-style distributed key
//    generation so NO party ever holds f(0). The signing/verify surface here
//    (BeaconShare::sign, aggregate, verify_beacon) is unchanged — only share
//    issuance moves.
// 2. Proactive resharing + committee handoff across epochs (reshare f under
//    a new polynomial; group_public is preserved or re-anchored in the epoch
//    transition cert under its own domain tag).
// 3. Per-partial DLEQ proofs (or pairing checks, as here) are already enough
//    for robustness; a drand-style chain (prev_randomness folded into the
//    message) adds bias-resistance across reorgs — one line in
//    beacon_message once heights can fork.
// 4. If beacon keys should be the SAME keys as the hinTS vote keys, the
//    upgrade is a deterministic-threshold-BLS mode in `hints` (interpolate at
//    a FIXED canonical signer set) — until then the dealt key keeps the two
//    signature streams unconfusable by construction.

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(n: usize, t: usize, seed: u8) -> (BeaconCommittee, Vec<BeaconShare>) {
        BeaconCommittee::deal_with_seed(n, t, [seed; 32]).unwrap()
    }

    // ── The uniqueness tooth: unbiasability ───────────────────────────────

    /// THE beacon property: every quorum subset of honest shares produces
    /// the IDENTICAL output — there is nothing for an aggregator to grind.
    #[test]
    fn same_output_from_any_quorum_subset() {
        let (committee, shares) = fixture(5, 3, 7);
        let (epoch, height) = (4, 1042);

        let subsets: &[&[usize]] = &[&[0, 1, 2], &[2, 3, 4], &[0, 2, 4], &[1, 3, 4]];
        let mut outputs = Vec::new();
        for subset in subsets {
            let picked: Vec<BeaconShare> = subset.iter().map(|&i| shares[i].clone()).collect();
            outputs.push(beacon_at(&committee, &picked, epoch, height).unwrap());
        }
        // All five shares at once too (aggregate uses any t of them).
        outputs.push(beacon_at(&committee, &shares, epoch, height).unwrap());

        for out in &outputs[1..] {
            assert_eq!(
                outputs[0], *out,
                "different honest quorum subsets must produce THE SAME beacon"
            );
            assert_eq!(outputs[0].signature_bytes(), out.signature_bytes());
            assert_eq!(outputs[0].randomness, out.randomness);
        }
        assert!(committee.verify_beacon(&outputs[0]));
    }

    /// Running the whole pipeline twice is byte-identical (no hidden
    /// per-signature randomness).
    #[test]
    fn beacon_is_deterministic_end_to_end() {
        let (committee, shares) = fixture(4, 3, 9);
        let a = beacon_at(&committee, &shares[0..3], 1, 1).unwrap();
        let b = beacon_at(&committee, &shares[0..3], 1, 1).unwrap();
        assert_eq!(a.to_bytes(), b.to_bytes());
    }

    // ── Below threshold cannot produce the beacon ─────────────────────────

    #[test]
    fn below_threshold_cannot_produce_beacon() {
        let (committee, shares) = fixture(5, 3, 11);
        let err = beacon_at(&committee, &shares[0..2], 0, 5).unwrap_err();
        assert_eq!(err, BeaconError::InsufficientPartials { got: 2, need: 3 });
    }

    #[test]
    fn invalid_and_duplicate_partials_do_not_count_toward_threshold() {
        let (committee, shares) = fixture(5, 3, 13);
        let (epoch, height) = (2, 77);

        // A partial signed over the WRONG height does not verify and is
        // dropped (fail-closed), so 2 good + 1 bad < t.
        let mut partials = vec![
            shares[0].sign(epoch, height),
            shares[1].sign(epoch, height),
            shares[2].sign(epoch, height + 1),
        ];
        assert_eq!(
            committee.aggregate(&partials, epoch, height).unwrap_err(),
            BeaconError::InsufficientPartials { got: 2, need: 3 }
        );

        // Duplicating an index does not double-count.
        partials[2] = shares[0].sign(epoch, height);
        assert_eq!(
            committee.aggregate(&partials, epoch, height).unwrap_err(),
            BeaconError::InsufficientPartials { got: 2, need: 3 }
        );

        // And the same set WITH the third honest partial succeeds.
        partials[2] = shares[2].sign(epoch, height);
        assert!(committee.aggregate(&partials, epoch, height).is_ok());
    }

    // ── Verification: fail-closed on tampering / wrong binding ───────────

    #[test]
    fn verify_with_group_key_only() {
        let (committee, shares) = fixture(4, 3, 17);
        let out = beacon_at(&committee, &shares[1..4], 3, 9).unwrap();
        // A light verifier holds just the group public key.
        assert!(verify_beacon(committee.group_public(), &out));
        // Round-trips through bytes/serde and still verifies.
        let out2 = BeaconOutput::from_bytes(&out.to_bytes()).unwrap();
        assert!(verify_beacon(committee.group_public(), &out2));
    }

    #[test]
    fn tampered_randomness_fails_verify() {
        let (committee, shares) = fixture(4, 3, 19);
        let mut out = beacon_at(&committee, &shares[0..3], 1, 2).unwrap();
        out.randomness[0] ^= 0x01;
        assert!(!verify_beacon(committee.group_public(), &out));
    }

    #[test]
    fn wrong_epoch_or_height_claim_fails_verify() {
        let (committee, shares) = fixture(4, 3, 23);
        let out = beacon_at(&committee, &shares[0..3], 6, 100).unwrap();

        let mut wrong_height = out.clone();
        wrong_height.height = 101;
        assert!(!verify_beacon(committee.group_public(), &wrong_height));

        let mut wrong_epoch = out.clone();
        wrong_epoch.epoch = 7;
        assert!(!verify_beacon(committee.group_public(), &wrong_epoch));
    }

    #[test]
    fn signature_from_another_height_fails_verify() {
        let (committee, shares) = fixture(4, 3, 29);
        let at_100 = beacon_at(&committee, &shares[0..3], 1, 100).unwrap();
        let at_101 = beacon_at(&committee, &shares[0..3], 1, 101).unwrap();
        // Graft height-101's signature+randomness onto a height-100 claim.
        let grafted = BeaconOutput {
            epoch: 1,
            height: 100,
            signature: at_101.signature,
            randomness: at_101.randomness,
        };
        assert!(!verify_beacon(committee.group_public(), &grafted));
        assert!(verify_beacon(committee.group_public(), &at_100));
    }

    #[test]
    fn foreign_domain_signature_is_rejected() {
        // Partials signed under another crate domain (the vote domain) must
        // not aggregate into a beacon: verify_partial recomputes the message
        // under BEACON_DOMAIN, so foreign-domain partials are dropped.
        let (committee, shares) = fixture(4, 3, 31);
        let mut foreign = b"dregg-federation-vote-v1".to_vec();
        foreign.extend_from_slice(&5u64.to_be_bytes());
        foreign.extend_from_slice(&10u64.to_be_bytes());
        let h_foreign = hash_to_g2(&foreign);
        let partials: Vec<BeaconPartial> = shares[0..3]
            .iter()
            .map(|s| BeaconPartial {
                index: s.index,
                point: (h_foreign * s.secret).into_affine(),
            })
            .collect();
        assert_eq!(
            committee.aggregate(&partials, 5, 10).unwrap_err(),
            BeaconError::InsufficientPartials { got: 0, need: 3 }
        );
    }

    #[test]
    fn wrong_committee_key_fails_verify() {
        let (committee_a, shares_a) = fixture(4, 3, 37);
        let (committee_b, _) = fixture(4, 3, 41);
        let out = beacon_at(&committee_a, &shares_a[0..3], 0, 1).unwrap();
        assert!(verify_beacon(committee_a.group_public(), &out));
        assert!(!verify_beacon(committee_b.group_public(), &out));
    }

    // ── Distinctness across coordinates ──────────────────────────────────

    #[test]
    fn beacons_differ_across_heights_and_epochs() {
        let (committee, shares) = fixture(4, 3, 43);
        let base = beacon_at(&committee, &shares[0..3], 2, 50).unwrap();
        let next_height = beacon_at(&committee, &shares[0..3], 2, 51).unwrap();
        let next_epoch = beacon_at(&committee, &shares[0..3], 3, 50).unwrap();
        assert_ne!(base.randomness, next_height.randomness);
        assert_ne!(base.randomness, next_epoch.randomness);
        assert_ne!(next_height.randomness, next_epoch.randomness);
    }

    // ── The consumer: deterministic draws / jury selection ───────────────

    #[test]
    fn deterministic_draw_is_deterministic_in_range_and_beacon_bound() {
        let (committee, shares) = fixture(4, 3, 47);
        let out_a = beacon_at(&committee, &shares[0..3], 1, 7).unwrap();
        let out_b = beacon_at(&committee, &shares[0..3], 1, 8).unwrap();

        let a1 = deterministic_draw(&out_a.randomness, 1000).unwrap();
        let a2 = deterministic_draw(&out_a.randomness, 1000).unwrap();
        assert_eq!(a1, a2, "same beacon, same range ⇒ same draw");
        assert!(a1 < 1000);

        let b1 = deterministic_draw(&out_b.randomness, 1000).unwrap();
        assert_ne!(
            (out_a.randomness, a1),
            (out_b.randomness, b1),
            "different beacons must not share both randomness and draw"
        );

        assert_eq!(deterministic_draw(&out_a.randomness, 0), None);
        assert_eq!(deterministic_draw(&out_a.randomness, 1), Some(0));
    }

    /// Loose uniformity sanity (chi-square-shaped): 4096 draws from one
    /// beacon stream into 8 buckets; expected 512 per bucket. The bound
    /// (±25%) is ~6+ sigma for a binomial(4096, 1/8) — deterministic, no
    /// flake, but a constant or badly-skewed stream fails hard.
    #[test]
    fn draw_stream_bucket_uniformity() {
        let (committee, shares) = fixture(4, 3, 53);
        let out = beacon_at(&committee, &shares[0..3], 9, 9).unwrap();
        let mut stream = BeaconDraw::new(&out.randomness);
        let mut buckets = [0usize; 8];
        for _ in 0..4096 {
            buckets[stream.draw(8).unwrap() as usize] += 1;
        }
        for (i, &count) in buckets.iter().enumerate() {
            assert!(
                (384..=640).contains(&count),
                "bucket {i} count {count} outside loose uniformity band [384, 640]: {buckets:?}"
            );
        }
    }

    #[test]
    fn jury_selection_is_deterministic_and_distinct() {
        let (committee, shares) = fixture(5, 3, 59);
        let out = beacon_at(&committee, &shares[2..5], 3, 33).unwrap();

        let jury = select_jury(&out.randomness, 100, 12).unwrap();
        assert_eq!(jury.len(), 12);
        let mut sorted = jury.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), 12, "jurors must be distinct");
        assert!(jury.iter().all(|&j| j < 100));

        // Everyone holding the beacon computes the same jury.
        assert_eq!(select_jury(&out.randomness, 100, 12).unwrap(), jury);

        // Edges: full pool is a permutation; over-asking is refused.
        assert_eq!(
            select_jury(&out.randomness, 5, 5).unwrap().len(),
            5
        );
        assert_eq!(select_jury(&out.randomness, 5, 6), None);
    }

    // ── Committee serialization ───────────────────────────────────────────

    #[test]
    fn committee_roundtrips_through_bytes() {
        let (committee, shares) = fixture(4, 3, 61);
        let committee2 = BeaconCommittee::from_bytes(&committee.to_bytes()).unwrap();
        assert_eq!(committee, committee2);
        let out = beacon_at(&committee, &shares[0..3], 1, 1).unwrap();
        assert!(committee2.verify_beacon(&out));
    }

    #[test]
    fn deal_rejects_degenerate_parameters() {
        assert!(BeaconCommittee::deal_with_seed(0, 0, [1; 32]).is_err());
        assert!(BeaconCommittee::deal_with_seed(3, 0, [1; 32]).is_err());
        assert!(BeaconCommittee::deal_with_seed(3, 4, [1; 32]).is_err());
        assert!(BeaconCommittee::deal_with_seed(1, 1, [1; 32]).is_ok());
    }

    // ── The loud report, executable: why hinTS is NOT the beacon ─────────

    /// ORGANS §6 calls the existing threshold signature "deterministic …
    /// uniqueness of BLS". For the hinTS aggregate in `crate::threshold`
    /// that is FALSE across signer subsets: two different honest quorums
    /// produce two DIFFERENT (both verifying) aggregate signatures, so
    /// hash(aggregate) would be grindable over subsets — which is exactly
    /// why this module deals a Shamir-shared key instead.
    #[test]
    fn hints_aggregate_is_subset_dependent_hence_not_a_beacon() {
        use crate::threshold::generate_test_committee;
        use hints::PartialSignature;

        let (committee, members) = generate_test_committee(4, 2).unwrap();
        let msg = beacon_message(0, 0);

        let quorum_a: Vec<(usize, PartialSignature)> = members[0..2]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &msg)))
            .collect();
        let quorum_b: Vec<(usize, PartialSignature)> = members[2..4]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &msg)))
            .collect();

        let qc_a = committee.aggregate(&quorum_a, &msg).unwrap();
        let qc_b = committee.aggregate(&quorum_b, &msg).unwrap();
        assert!(committee.verify(&qc_a, &msg).is_ok());
        assert!(committee.verify(&qc_b, &msg).is_ok());
        assert_ne!(
            qc_a.to_bytes(),
            qc_b.to_bytes(),
            "if this ever becomes equal, hinTS gained uniqueness and the \
             beacon could unify onto crate::threshold"
        );
    }
}
