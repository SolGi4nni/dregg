//! Protocol binding substrate for a genuinely shielded exact-spend apex.
//!
//! This module is deliberately a **v4 boundary**, not a compatibility wrapper around exact
//! FNSP-v3.  V3 cannot honestly be reused for a dark-value spend:
//!
//! - its 76-lane statement publishes `value` and `asset_type`; and
//! - its `FNI2` linked leaf commits the clear four-limb `u64` value.
//!
//! The v4 shape replaces that clear leaf payload with the existing sixteen-felt, blinded,
//! full-`u64` value/asset binding.  It also commits the fixed Dark-AMM + shielded-ring public
//! surfaces and the output-note root into one consequence digest.  The exact statement shares the
//! same full nullifier, value/asset binding, consequence digest, output-note root, accumulator
//! transition, and outer state endpoints without publishing a clear value or asset.
//!
//! ## Honest scope
//!
//! These are binding and wire primitives, **not proof acceptance authority**.  In particular, the
//! current ring public surface still carries a one-felt legacy nullifier and value binding.  A live
//! v4 descriptor must prove inside one code-owned relation that:
//!
//! 1. the faithful note opening produces the full 256-bit nullifier below;
//! 2. the same hidden `(value, asset)` opening produces the sixteen-lane binding below;
//! 3. the ring/conservation proof consumes that same opening and creates exactly the committed
//!    output notes; and
//! 4. the `FNI4`/`FNS4` transition and outer state endpoints advance atomically.
//!
//! Until that descriptor is Lean-authored, emitted, assigned a pinned verifier identity, and its
//! output notes land in the same durable transaction as the exact frame, callers must treat
//! [`PreparedShieldedConsequenceV4`] and [`ShieldedExactApexV4Public`] as inputs to that future
//! verifier, never as evidence that it already accepted.
//!
//! ## Cryptographic posture of the sixteen-lane carrier
//!
//! `shielded::wide_value_binding` computes two domain-separated, full-output Poseidon2 `node8`
//! images over canonical `u64` value/asset limbs and seven hidden BabyBear blinding lanes.  Thus the
//! pre-hash encoding is faithful and the carrier is hiding/binding only under the deployed
//! Poseidon2 collision/preimage assumptions.  It is plausibly post-quantum in the hash-based sense;
//! this module does not claim a reduction or more security than the HidingFRI/Poseidon floor.
//! Crucially, it is **not** the Ristretto Pedersen commitment used by today's classical
//! conservation proof.  A v4 relation must prove same-opening between the wide carrier and its
//! conservation representation (or replace the latter with a native PQ conserving relation).

use core::fmt;

use dregg_circuit::exact_nullifier_aafi::{Digest8, ExactTaggedKey, TaggedKeyWire};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_many_8;

use crate::dark_amm_private::{PUBLIC_INPUT_COUNT as DARK_AMM_PUBLIC_INPUT_COUNT, PublicStatement};
pub use crate::shielded::WIDE_VALUE_BINDING_LANES;
use crate::shielded::{WideValueBindingProof, verify_wide_value_binding};
use crate::shielded_ring_clearing_air::{RING_ENDPOINT_PUBLIC_LEN, RING_LEG_CLAIM_LEN, RING_LEGS};

/// ASCII `FNI4`: linked exact-nullifier leaf carrying a shielded value/asset binding.
pub const SHIELDED_EXACT_LEAF_DOMAIN: u32 = 0x464e_4934;
/// ASCII `FNS4`: exact accumulator state whose leaves use [`SHIELDED_EXACT_LEAF_DOMAIN`].
pub const SHIELDED_EXACT_STATE_DOMAIN: u32 = 0x464e_5334;
/// ASCII `FXC4`: fixed Dark-AMM + shielded-ring + output-note consequence binding.
pub const SHIELDED_CONSEQUENCE_DOMAIN: u32 = 0x4658_4334;
/// ASCII `FXA4`: compact binding of the complete v4 verifier-facing statement.
pub const SHIELDED_EXACT_APEX_DOMAIN: u32 = 0x4658_4134;

/// The v4 public statement has no clear-value or clear-asset slot.
pub const SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT: usize = 100;
/// Canonical fixed-width public wire: 100 little-endian BabyBear representatives.
pub const SHIELDED_EXACT_APEX_V4_PUBLIC_WIRE_BYTES: usize =
    SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT * size_of::<u32>();
/// Exact canonical FXC4 transcript width: domain/selectors, complete ledger/exact endpoints,
/// 19 Dark-AMM lanes, 27 ring lanes, and the exact output count/root.
pub const SHIELDED_CONSEQUENCE_PREIMAGE_LANES: usize = 146;

const PI_HEIGHT: usize = 0;
const PI_HISTORICAL_NOTE_ROOT: usize = 4;
const PI_NULLIFIER: usize = 12;
const PI_VALUE_ASSET_BINDING: usize = 28;
const PI_SUCCESSOR_EXACT_ROOT: usize = 44;
const PI_PRIOR_EXACT_ROOT: usize = 52;
const PI_PRE_COUNT: usize = 60;
const PI_POST_COUNT: usize = 64;
const PI_CONSEQUENCE_ROOT: usize = 68;
const PI_OUTPUT_NOTES_ROOT: usize = 76;
const PI_BEFORE_OUTER_COMMIT: usize = 84;
const PI_AFTER_OUTER_COMMIT: usize = 92;
const PI_END: usize = 100;

const _: () = {
    assert!(SHIELDED_EXACT_LEAF_DOMAIN < BABYBEAR_P);
    assert!(SHIELDED_EXACT_STATE_DOMAIN < BABYBEAR_P);
    assert!(SHIELDED_CONSEQUENCE_DOMAIN < BABYBEAR_P);
    assert!(SHIELDED_EXACT_APEX_DOMAIN < BABYBEAR_P);
    assert!(RING_LEGS == 2);
    assert!(RING_LEG_CLAIM_LEN == 3);
    assert!(DARK_AMM_PUBLIC_INPUT_COUNT == 19);
    assert!(RING_ENDPOINT_PUBLIC_LEN == 27);
    assert!(PI_END == SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT);
};

/// Human-readable v4 ABI.  The absence of clear `value` / `asset_type` slots is intentional and
/// tested against v3's public ABI.
pub const PUBLIC_ABI: &[(&str, usize, usize, &str)] = &[
    ("historical_height", PI_HEIGHT, 4, "u64-le-u16x4"),
    (
        "historical_note_root",
        PI_HISTORICAL_NOTE_ROOT,
        8,
        "babybear-root8",
    ),
    ("nullifier", PI_NULLIFIER, 16, "bytes32-le-u16x16"),
    (
        "hidden_value_asset_binding",
        PI_VALUE_ASSET_BINDING,
        16,
        "babybear-digest16",
    ),
    (
        "successor_exact_root",
        PI_SUCCESSOR_EXACT_ROOT,
        8,
        "babybear-root8-fni4",
    ),
    (
        "prior_exact_root",
        PI_PRIOR_EXACT_ROOT,
        8,
        "babybear-root8-fni4",
    ),
    ("pre_count", PI_PRE_COUNT, 4, "u64-le-u16x4"),
    ("post_count", PI_POST_COUNT, 4, "u64-le-u16x4"),
    (
        "shielded_consequence_root",
        PI_CONSEQUENCE_ROOT,
        8,
        "babybear-digest8-fxc4",
    ),
    (
        "output_notes_root",
        PI_OUTPUT_NOTES_ROOT,
        8,
        "babybear-root8",
    ),
    (
        "before_outer_commit",
        PI_BEFORE_OUTER_COMMIT,
        8,
        "babybear-digest8",
    ),
    (
        "after_outer_commit",
        PI_AFTER_OUTER_COMMIT,
        8,
        "babybear-digest8",
    ),
];

/// Canonical `FNI4` linked leaf.  The clear four-limb value from `FNI2` is intentionally absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedExactLinkedLeafV4 {
    addr: ExactTaggedKey,
    value_asset_binding: [BabyBear; WIDE_VALUE_BINDING_LANES],
    next_addr: ExactTaggedKey,
}

impl ShieldedExactLinkedLeafV4 {
    /// Validate an untrusted leaf before it can enter the v4 hash domain.
    pub fn try_new(
        addr: TaggedKeyWire,
        value_asset_binding: [u32; WIDE_VALUE_BINDING_LANES],
        next_addr: TaggedKeyWire,
    ) -> Result<Self, ShieldedExactApexV4Error> {
        let addr = addr
            .decode()
            .map_err(|error| ShieldedExactApexV4Error::TaggedKey(error.to_string()))?;
        let next_addr = next_addr
            .decode()
            .map_err(|error| ShieldedExactApexV4Error::TaggedKey(error.to_string()))?;
        if matches!(addr, ExactTaggedKey::Top) {
            return Err(ShieldedExactApexV4Error::InvalidLeafAddress);
        }
        if matches!(next_addr, ExactTaggedKey::Bot) {
            return Err(ShieldedExactApexV4Error::InvalidLeafSuccessor);
        }
        validate_canonical_lanes("hidden value/asset binding", &value_asset_binding)?;
        Ok(Self {
            addr,
            value_asset_binding: value_asset_binding.map(BabyBear::new),
            next_addr,
        })
    }

    pub fn addr(&self) -> ExactTaggedKey {
        self.addr
    }

    pub fn next_addr(&self) -> ExactTaggedKey {
        self.next_addr
    }

    pub fn value_asset_binding(&self) -> [u32; WIDE_VALUE_BINDING_LANES] {
        self.value_asset_binding.map(BabyBear::as_u32)
    }
}

fn append_tagged_key(out: &mut Vec<BabyBear>, key: ExactTaggedKey) {
    let wire = key.wire();
    out.push(BabyBear::new(u32::from(wire.tag)));
    out.extend(
        wire.raw_u16_le
            .into_iter()
            .map(|limb| BabyBear::new(u32::from(limb))),
    );
}

/// Exact 51-felt `FNI4 || addr17 || hidden_binding16 || next17` preimage.
pub fn shielded_exact_leaf_preimage(leaf: ShieldedExactLinkedLeafV4) -> Vec<BabyBear> {
    let mut input = Vec::with_capacity(51);
    input.push(BabyBear::new(SHIELDED_EXACT_LEAF_DOMAIN));
    append_tagged_key(&mut input, leaf.addr);
    input.extend(leaf.value_asset_binding);
    append_tagged_key(&mut input, leaf.next_addr);
    debug_assert_eq!(input.len(), 51);
    input
}

/// Full eight-lane commitment of one v4 linked leaf.
pub fn shielded_exact_leaf_digest(leaf: ShieldedExactLinkedLeafV4) -> Digest8 {
    hash_many_8(&shielded_exact_leaf_preimage(leaf))
}

/// Exact `FNS4 || root8 || count_u16_le[4]` state preimage.
pub fn shielded_exact_state_preimage(root: Digest8, count: u64) -> Vec<BabyBear> {
    let mut input = Vec::with_capacity(13);
    input.push(BabyBear::new(SHIELDED_EXACT_STATE_DOMAIN));
    input.extend(root);
    input.extend(u64_u16_lanes(count).map(BabyBear::new));
    debug_assert_eq!(input.len(), 13);
    input
}

/// State commitment for an accumulator whose leaves use `FNI4`.
pub fn shielded_exact_state_commit(root: Digest8, count: u64) -> Digest8 {
    hash_many_8(&shielded_exact_state_preimage(root, count))
}

/// Code-owned verification of the existing full-u64 sidecar against one expected compatibility
/// digest.
///
/// The type is intentionally non-`Clone` with private fields.  It proves that the sixteen-lane
/// carrier has a canonical hidden `(u64 value, u64 asset)` opening whose reduction produces the
/// expected one-BabyBear legacy digest.  It does **not** prove that a separate ring proof used the
/// same opening: two full-width openings separated by the BabyBear modulus can share that legacy
/// digest.  True v4 authority therefore still requires a shared-witness/full-width join in one
/// relation.
#[derive(Debug, PartialEq, Eq)]
pub struct VerifiedWideBindingCompatibilityV4 {
    legacy_value_binding: u32,
    value_asset_binding: [u32; WIDE_VALUE_BINDING_LANES],
}

/// Verify the existing HidingFRI sidecar with its fixed, code-owned verifier and retain only its
/// public compatibility/wide carriers.
pub fn verify_wide_binding_compatibility_v4(
    proof: &WideValueBindingProof,
    expected_legacy_value_binding: u32,
) -> Result<VerifiedWideBindingCompatibilityV4, ShieldedExactApexV4Error> {
    validate_canonical_lane(
        "expected legacy value binding",
        expected_legacy_value_binding,
    )?;
    let expected = BabyBear::new(expected_legacy_value_binding);
    verify_wide_value_binding(proof, expected)
        .map_err(|error| ShieldedExactApexV4Error::WideBindingCompatibility(error.to_string()))?;
    Ok(VerifiedWideBindingCompatibilityV4 {
        legacy_value_binding: expected_legacy_value_binding,
        value_asset_binding: proof.claim.wide_binding.map(BabyBear::as_u32),
    })
}

/// The complete canonical ledger/exact transition absorbed by FXC4.
///
/// Construction validates every BabyBear root lane and the exact `count + 1` law once.  Keeping
/// these fields in one non-forgeable value prevents the FXC4 transcript and the 100-lane apex public
/// statement from being assembled from divergent endpoint arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedExactApexV4LedgerTransition {
    historical_root_height: u64,
    historical_note_root: [u32; 8],
    successor_exact_root: [u32; 8],
    prior_exact_root: [u32; 8],
    pre_count: u64,
    post_count: u64,
    before_outer_commit: [u32; 8],
    after_outer_commit: [u32; 8],
}

impl ShieldedExactApexV4LedgerTransition {
    #[allow(clippy::too_many_arguments)]
    pub fn try_new(
        historical_root_height: u64,
        historical_note_root: [u32; 8],
        successor_exact_root: [u32; 8],
        prior_exact_root: [u32; 8],
        pre_count: u64,
        post_count: u64,
        before_outer_commit: [u32; 8],
        after_outer_commit: [u32; 8],
    ) -> Result<Self, ShieldedExactApexV4Error> {
        validate_count_transition(pre_count, post_count)?;
        for (name, lanes) in [
            ("historical note root", historical_note_root),
            ("successor exact root", successor_exact_root),
            ("prior exact root", prior_exact_root),
            ("before outer commit", before_outer_commit),
            ("after outer commit", after_outer_commit),
        ] {
            validate_canonical_lanes(name, &lanes)?;
        }
        Ok(Self {
            historical_root_height,
            historical_note_root,
            successor_exact_root,
            prior_exact_root,
            pre_count,
            post_count,
            before_outer_commit,
            after_outer_commit,
        })
    }
}

/// A prepared commitment to the fixed current private-AMM and two-leg ring public surfaces.
///
/// This type is non-`Clone` and its fields are private to avoid accidentally treating raw arrays
/// as an already verified consequence.  Preparation checks canonical encodings and exact shared
/// legacy lanes, then binds the full nullifier and wide value/asset carrier as the migration target.
/// It does **not** verify the Dark-AMM proof or recursively pin/verify the ring apex.
#[derive(Debug, PartialEq, Eq)]
pub struct PreparedShieldedConsequenceV4 {
    ledger: ShieldedExactApexV4LedgerTransition,
    dark_amm: PublicStatement,
    ring_public: [u32; RING_ENDPOINT_PUBLIC_LEN],
    ring_leg: u8,
    nullifier: [u8; 32],
    value_asset_binding: [u32; WIDE_VALUE_BINDING_LANES],
    output_note_count: u64,
    output_notes_root: [u32; 8],
    root: [u32; 8],
}

impl PreparedShieldedConsequenceV4 {
    /// Commit the fixed Dark-AMM and current two-leg ring public surfaces to the exact v4 fields.
    ///
    /// `ring_leg` selects the spent leg being promoted to full-width exact authority.  The scalar
    /// nullifier and compatibility value binding must equal that leg's ring claim.  The complete
    /// 256-bit nullifier and sixteen-lane value/asset binding are additionally absorbed so a v4 AIR
    /// can prove the missing same-opening/full-nullifier bridges without changing this ABI.
    #[allow(clippy::too_many_arguments)]
    pub fn from_current_dark_amm_and_ring_publics(
        ledger: ShieldedExactApexV4LedgerTransition,
        dark_amm: PublicStatement,
        ring_public: [u32; RING_ENDPOINT_PUBLIC_LEN],
        ring_leg: usize,
        legacy_nullifier: u32,
        nullifier: [u8; 32],
        value_binding: VerifiedWideBindingCompatibilityV4,
        output_note_count: u64,
        output_notes_root: [u32; 8],
    ) -> Result<Self, ShieldedExactApexV4Error> {
        dark_amm
            .validate()
            .map_err(ShieldedExactApexV4Error::DarkAmmStatement)?;
        if ring_leg >= RING_LEGS {
            return Err(ShieldedExactApexV4Error::RingLegOutOfRange(ring_leg));
        }
        validate_canonical_lanes("ring public", &ring_public)?;
        validate_canonical_lane("legacy nullifier", legacy_nullifier)?;
        validate_canonical_lanes("output notes root", &output_notes_root)?;
        if output_note_count == 0 {
            return Err(ShieldedExactApexV4Error::EmptyOutputNotes);
        }

        let leg_base = ring_leg * RING_LEG_CLAIM_LEN;
        if ring_public[leg_base] != legacy_nullifier {
            return Err(ShieldedExactApexV4Error::LegacyNullifierMismatch);
        }
        if ring_public[leg_base + 2] != value_binding.legacy_value_binding {
            return Err(ShieldedExactApexV4Error::LegacyValueBindingMismatch);
        }
        let value_asset_binding = value_binding.value_asset_binding;

        let ring_leg = u8::try_from(ring_leg).expect("validated two-leg selector");
        let preimage = canonical_fxc4_preimage(
            ledger,
            dark_amm,
            ring_public,
            ring_leg,
            nullifier,
            value_asset_binding,
            output_note_count,
            output_notes_root,
        );
        let root = hash_many_8(&preimage).map(BabyBear::as_u32);

        Ok(Self {
            ledger,
            dark_amm,
            ring_public,
            ring_leg,
            nullifier,
            value_asset_binding,
            output_note_count,
            output_notes_root,
            root,
        })
    }

    pub fn root(&self) -> [u32; 8] {
        self.root
    }

    /// Exact 146-lane canonical FXC4 preimage.  This is transcript data, never proof authority.
    pub fn canonical_preimage(&self) -> [u32; SHIELDED_CONSEQUENCE_PREIMAGE_LANES] {
        canonical_fxc4_preimage(
            self.ledger,
            self.dark_amm,
            self.ring_public,
            self.ring_leg,
            self.nullifier,
            self.value_asset_binding,
            self.output_note_count,
            self.output_notes_root,
        )
        .map(BabyBear::as_u32)
    }
}

#[allow(clippy::too_many_arguments)]
fn canonical_fxc4_preimage(
    ledger: ShieldedExactApexV4LedgerTransition,
    dark_amm: PublicStatement,
    ring_public: [u32; RING_ENDPOINT_PUBLIC_LEN],
    ring_leg: u8,
    nullifier: [u8; 32],
    value_asset_binding: [u32; WIDE_VALUE_BINDING_LANES],
    output_note_count: u64,
    output_notes_root: [u32; 8],
) -> [BabyBear; SHIELDED_CONSEQUENCE_PREIMAGE_LANES] {
    let mut preimage = Vec::with_capacity(SHIELDED_CONSEQUENCE_PREIMAGE_LANES);
    preimage.push(BabyBear::new(SHIELDED_CONSEQUENCE_DOMAIN));
    // Code-owned relation selectors.  They are not caller-supplied verifier identifiers.
    preimage.push(BabyBear::new(crate::dark_amm_private::RULE_ID));
    preimage.push(BabyBear::new(RING_ENDPOINT_PUBLIC_LEN as u32));
    preimage.push(BabyBear::new(u32::from(ring_leg)));
    preimage.extend(u64_u16_lanes(ledger.historical_root_height).map(BabyBear::new));
    preimage.extend(ledger.historical_note_root.map(BabyBear::new));
    preimage.extend(bytes32_u16_lanes(&nullifier).map(BabyBear::new));
    preimage.extend(value_asset_binding.map(BabyBear::new));
    preimage.extend(ledger.successor_exact_root.map(BabyBear::new));
    preimage.extend(ledger.prior_exact_root.map(BabyBear::new));
    preimage.extend(u64_u16_lanes(ledger.pre_count).map(BabyBear::new));
    preimage.extend(u64_u16_lanes(ledger.post_count).map(BabyBear::new));
    preimage.extend(ledger.before_outer_commit.map(BabyBear::new));
    preimage.extend(ledger.after_outer_commit.map(BabyBear::new));
    preimage.extend(dark_amm.as_u32_array().map(BabyBear::new));
    preimage.extend(ring_public.map(BabyBear::new));
    preimage.extend(u64_u16_lanes(output_note_count).map(BabyBear::new));
    preimage.extend(output_notes_root.map(BabyBear::new));
    preimage
        .try_into()
        .expect("FXC4 canonical preimage has compile-time audited width")
}

/// Canonical 100-lane v4 statement.  Construction from a prepared consequence makes the shared
/// nullifier, hidden value/asset binding, consequence root, and output-note root non-divergent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedExactApexV4Public {
    lanes: [u32; SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT],
}

impl ShieldedExactApexV4Public {
    /// Construct the public statement from the same already-validated ledger transition absorbed
    /// by FXC4.  There is intentionally no constructor taking a second set of endpoint arguments.
    pub fn from_prepared(consequence: PreparedShieldedConsequenceV4) -> Self {
        let ledger = consequence.ledger;
        let mut lanes = [0u32; SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT];
        lanes[PI_HEIGHT..PI_HISTORICAL_NOTE_ROOT]
            .copy_from_slice(&u64_u16_lanes(ledger.historical_root_height));
        lanes[PI_HISTORICAL_NOTE_ROOT..PI_NULLIFIER].copy_from_slice(&ledger.historical_note_root);
        lanes[PI_NULLIFIER..PI_VALUE_ASSET_BINDING]
            .copy_from_slice(&bytes32_u16_lanes(&consequence.nullifier));
        lanes[PI_VALUE_ASSET_BINDING..PI_SUCCESSOR_EXACT_ROOT]
            .copy_from_slice(&consequence.value_asset_binding);
        lanes[PI_SUCCESSOR_EXACT_ROOT..PI_PRIOR_EXACT_ROOT]
            .copy_from_slice(&ledger.successor_exact_root);
        lanes[PI_PRIOR_EXACT_ROOT..PI_PRE_COUNT].copy_from_slice(&ledger.prior_exact_root);
        lanes[PI_PRE_COUNT..PI_POST_COUNT].copy_from_slice(&u64_u16_lanes(ledger.pre_count));
        lanes[PI_POST_COUNT..PI_CONSEQUENCE_ROOT]
            .copy_from_slice(&u64_u16_lanes(ledger.post_count));
        lanes[PI_CONSEQUENCE_ROOT..PI_OUTPUT_NOTES_ROOT].copy_from_slice(&consequence.root);
        lanes[PI_OUTPUT_NOTES_ROOT..PI_BEFORE_OUTER_COMMIT]
            .copy_from_slice(&consequence.output_notes_root);
        lanes[PI_BEFORE_OUTER_COMMIT..PI_AFTER_OUTER_COMMIT]
            .copy_from_slice(&ledger.before_outer_commit);
        lanes[PI_AFTER_OUTER_COMMIT..PI_END].copy_from_slice(&ledger.after_outer_commit);
        Self { lanes }
    }

    /// Strict verifier-wire decoder.  This mints no proof authority.
    pub fn try_from_u32s(lanes: &[u32]) -> Result<Self, ShieldedExactApexV4Error> {
        if lanes.len() != SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT {
            return Err(ShieldedExactApexV4Error::PublicLaneCount {
                expected: SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT,
                actual: lanes.len(),
            });
        }
        let mut exact = [0u32; SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT];
        exact.copy_from_slice(lanes);
        for (index, value) in exact.iter().copied().enumerate() {
            if value >= BABYBEAR_P {
                return Err(ShieldedExactApexV4Error::NonCanonicalLane { index, value });
            }
            if is_u16_public_lane(index) && value > u16::MAX as u32 {
                return Err(ShieldedExactApexV4Error::NonCanonicalU16Lane { index, value });
            }
        }
        validate_count_transition(
            read_u64_u16(&exact[PI_PRE_COUNT..PI_POST_COUNT]),
            read_u64_u16(&exact[PI_POST_COUNT..PI_CONSEQUENCE_ROOT]),
        )?;
        Ok(Self { lanes: exact })
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Result<Self, ShieldedExactApexV4Error> {
        if bytes.len() != SHIELDED_EXACT_APEX_V4_PUBLIC_WIRE_BYTES {
            return Err(ShieldedExactApexV4Error::PublicWireLength {
                expected: SHIELDED_EXACT_APEX_V4_PUBLIC_WIRE_BYTES,
                actual: bytes.len(),
            });
        }
        let mut lanes = [0u32; SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT];
        for (index, chunk) in bytes.chunks_exact(4).enumerate() {
            lanes[index] = u32::from_le_bytes(chunk.try_into().expect("four-byte public lane"));
        }
        Self::try_from_u32s(&lanes)
    }

    pub const fn as_u32_array(&self) -> &[u32; SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT] {
        &self.lanes
    }

    pub fn to_le_bytes(self) -> [u8; SHIELDED_EXACT_APEX_V4_PUBLIC_WIRE_BYTES] {
        let mut out = [0u8; SHIELDED_EXACT_APEX_V4_PUBLIC_WIRE_BYTES];
        for (index, value) in self.lanes.into_iter().enumerate() {
            out[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        out
    }

    /// Compact full-width binding for durable receipt/frame transport.
    pub fn apex_binding_digest(&self) -> [u32; 8] {
        let mut preimage = Vec::with_capacity(1 + self.lanes.len());
        preimage.push(BabyBear::new(SHIELDED_EXACT_APEX_DOMAIN));
        preimage.extend(self.lanes.map(BabyBear::new));
        hash_many_8(&preimage).map(BabyBear::as_u32)
    }

    pub fn nullifier(&self) -> [u8; 32] {
        bytes32_from_u16_lanes(&self.lanes[PI_NULLIFIER..PI_VALUE_ASSET_BINDING])
    }

    pub fn value_asset_binding(&self) -> [u32; WIDE_VALUE_BINDING_LANES] {
        self.lanes[PI_VALUE_ASSET_BINDING..PI_SUCCESSOR_EXACT_ROOT]
            .try_into()
            .expect("fixed v4 binding width")
    }

    pub fn consequence_root(&self) -> [u32; 8] {
        self.lanes[PI_CONSEQUENCE_ROOT..PI_OUTPUT_NOTES_ROOT]
            .try_into()
            .expect("fixed v4 consequence width")
    }

    pub fn output_notes_root(&self) -> [u32; 8] {
        self.lanes[PI_OUTPUT_NOTES_ROOT..PI_BEFORE_OUTER_COMMIT]
            .try_into()
            .expect("fixed v4 output-notes width")
    }
}

fn validate_count_transition(
    pre_count: u64,
    post_count: u64,
) -> Result<(), ShieldedExactApexV4Error> {
    if pre_count.checked_add(1) != Some(post_count) {
        return Err(ShieldedExactApexV4Error::CountTransition {
            pre: pre_count,
            post: post_count,
        });
    }
    Ok(())
}

fn validate_canonical_lane(name: &'static str, value: u32) -> Result<(), ShieldedExactApexV4Error> {
    if value >= BABYBEAR_P {
        return Err(ShieldedExactApexV4Error::NonCanonicalNamedLane { name, value });
    }
    Ok(())
}

fn validate_canonical_lanes(
    name: &'static str,
    values: &[u32],
) -> Result<(), ShieldedExactApexV4Error> {
    for value in values.iter().copied() {
        validate_canonical_lane(name, value)?;
    }
    Ok(())
}

fn is_u16_public_lane(index: usize) -> bool {
    (PI_HEIGHT..PI_HISTORICAL_NOTE_ROOT).contains(&index)
        || (PI_NULLIFIER..PI_VALUE_ASSET_BINDING).contains(&index)
        || (PI_PRE_COUNT..PI_CONSEQUENCE_ROOT).contains(&index)
}

fn u64_u16_lanes(value: u64) -> [u32; 4] {
    core::array::from_fn(|index| ((value >> (16 * index)) & 0xffff) as u32)
}

fn read_u64_u16(values: &[u32]) -> u64 {
    debug_assert_eq!(values.len(), 4);
    values
        .iter()
        .copied()
        .enumerate()
        .fold(0, |acc, (index, limb)| {
            acc | u64::from(limb) << (16 * index)
        })
}

fn bytes32_u16_lanes(bytes: &[u8; 32]) -> [u32; 16] {
    core::array::from_fn(|index| {
        u32::from(u16::from_le_bytes([bytes[index * 2], bytes[index * 2 + 1]]))
    })
}

fn bytes32_from_u16_lanes(lanes: &[u32]) -> [u8; 32] {
    debug_assert_eq!(lanes.len(), 16);
    let mut out = [0u8; 32];
    for (index, lane) in lanes.iter().copied().enumerate() {
        let bytes = u16::try_from(lane)
            .expect("strict v4 public decoder accepted only u16 lanes")
            .to_le_bytes();
        out[index * 2..index * 2 + 2].copy_from_slice(&bytes);
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedExactApexV4Error {
    TaggedKey(String),
    InvalidLeafAddress,
    InvalidLeafSuccessor,
    DarkAmmStatement(String),
    RingLegOutOfRange(usize),
    LegacyNullifierMismatch,
    LegacyValueBindingMismatch,
    WideBindingCompatibility(String),
    EmptyOutputNotes,
    NonCanonicalNamedLane { name: &'static str, value: u32 },
    NonCanonicalLane { index: usize, value: u32 },
    NonCanonicalU16Lane { index: usize, value: u32 },
    CountTransition { pre: u64, post: u64 },
    PublicLaneCount { expected: usize, actual: usize },
    PublicWireLength { expected: usize, actual: usize },
}

impl fmt::Display for ShieldedExactApexV4Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TaggedKey(error) => write!(f, "invalid exact tagged key: {error}"),
            Self::InvalidLeafAddress => f.write_str("v4 exact leaf address cannot be TOP"),
            Self::InvalidLeafSuccessor => f.write_str("v4 exact leaf successor cannot be BOT"),
            Self::DarkAmmStatement(error) => write!(f, "fixed Dark-AMM statement refused: {error}"),
            Self::RingLegOutOfRange(index) => {
                write!(f, "shielded ring leg {index} is out of range")
            }
            Self::LegacyNullifierMismatch => {
                f.write_str("selected ring leg has a different legacy nullifier")
            }
            Self::LegacyValueBindingMismatch => {
                f.write_str("selected ring leg has a different legacy value binding")
            }
            Self::WideBindingCompatibility(error) => {
                write!(f, "wide value/asset compatibility proof refused: {error}")
            }
            Self::EmptyOutputNotes => f.write_str("shielded consequence creates no output notes"),
            Self::NonCanonicalNamedLane { name, value } => {
                write!(f, "{name} lane {value} is noncanonical for BabyBear")
            }
            Self::NonCanonicalLane { index, value } => write!(
                f,
                "v4 public lane {index}={value} is noncanonical for BabyBear"
            ),
            Self::NonCanonicalU16Lane { index, value } => {
                write!(f, "v4 public lane {index}={value} is not a canonical u16")
            }
            Self::CountTransition { pre, post } => {
                write!(f, "v4 exact count transition {pre}->{post} is not +1")
            }
            Self::PublicLaneCount { expected, actual } => write!(
                f,
                "v4 public statement expects {expected} lanes, got {actual}"
            ),
            Self::PublicWireLength { expected, actual } => {
                write!(f, "v4 public wire expects {expected} bytes, got {actual}")
            }
        }
    }
}

impl std::error::Error for ShieldedExactApexV4Error {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shielded::{BINDING_BLIND_LANES, WideValueBindingWitness, prove_wide_value_binding};
    use crate::shielded_ring_clearing_air::endpoint_pi;
    use dregg_circuit::exact_nullifier_aafi::{ExactTaggedKey, TaggedKeyWire, exact_state_commit};

    fn root(seed: u32) -> [u32; 8] {
        core::array::from_fn(|index| seed + index as u32)
    }

    fn dark_amm() -> PublicStatement {
        PublicStatement {
            session: 7,
            rule: crate::dark_amm_private::RULE_ID,
            k: 9,
            old_root: root(100),
            new_root: root(200),
        }
    }

    fn ledger() -> ShieldedExactApexV4LedgerTransition {
        ShieldedExactApexV4LedgerTransition::try_new(
            77,
            root(10),
            root(20),
            root(30),
            8,
            9,
            root(40),
            root(50),
        )
        .expect("canonical v4 ledger transition")
    }

    fn ring_public(legacy_nf: u32, legacy_vb: u32) -> [u32; RING_ENDPOINT_PUBLIC_LEN] {
        let mut ring = [0u32; RING_ENDPOINT_PUBLIC_LEN];
        ring[0] = legacy_nf;
        ring[1] = 31;
        ring[2] = legacy_vb;
        ring[3] = legacy_nf + 1;
        ring[4] = 31;
        ring[5] = legacy_vb + 1;
        for (index, lane) in ring.iter_mut().enumerate().skip(6) {
            *lane = 300 + index as u32;
        }
        ring
    }

    fn consequence(
        nullifier: [u8; 32],
        binding: [u32; WIDE_VALUE_BINDING_LANES],
    ) -> PreparedShieldedConsequenceV4 {
        consequence_with_ledger(ledger(), nullifier, binding)
    }

    fn consequence_with_ledger(
        ledger: ShieldedExactApexV4LedgerTransition,
        nullifier: [u8; 32],
        binding: [u32; WIDE_VALUE_BINDING_LANES],
    ) -> PreparedShieldedConsequenceV4 {
        PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
            ledger,
            dark_amm(),
            ring_public(17, 23),
            0,
            17,
            nullifier,
            compatibility(23, binding),
            2,
            root(500),
        )
        .expect("canonical prepared consequence")
    }

    fn compatibility(
        legacy_value_binding: u32,
        value_asset_binding: [u32; WIDE_VALUE_BINDING_LANES],
    ) -> VerifiedWideBindingCompatibilityV4 {
        VerifiedWideBindingCompatibilityV4 {
            legacy_value_binding,
            value_asset_binding,
        }
    }

    fn public(
        nullifier: [u8; 32],
        binding: [u32; WIDE_VALUE_BINDING_LANES],
    ) -> ShieldedExactApexV4Public {
        ShieldedExactApexV4Public::from_prepared(consequence(nullifier, binding))
    }

    #[test]
    fn v4_public_abi_has_no_clear_value_or_asset_slot() {
        assert_eq!(PUBLIC_ABI.iter().map(|slot| slot.2).sum::<usize>(), 100);
        assert!(!PUBLIC_ABI.iter().any(|slot| slot.0 == "value"));
        assert!(!PUBLIC_ABI.iter().any(|slot| slot.0 == "asset_type"));
        assert!(
            crate::faithful_note_spend_exact_v3_identity::PUBLIC_ABI
                .iter()
                .any(|slot| slot.name == "value")
        );
        assert!(
            crate::faithful_note_spend_exact_v3_identity::PUBLIC_ABI
                .iter()
                .any(|slot| slot.name == "asset_type")
        );
        assert!(matches!(
            ShieldedExactApexV4Public::from_le_bytes(&[0u8; 76 * 4]),
            Err(ShieldedExactApexV4Error::PublicWireLength { .. })
        ));
        let public = public([0x42; 32], core::array::from_fn(|index| 700 + index as u32));
        let debug = format!("{public:?}");
        assert!(!debug.contains("value:"));
        assert!(!debug.contains("asset_type:"));
    }

    #[test]
    fn code_owned_wide_compatibility_verifier_mints_only_the_narrowly_named_token() {
        let witness = WideValueBindingWitness {
            value: 37,
            asset_type: 11,
            legacy_randomness: BabyBear::new(19),
            binding_blind: core::array::from_fn(|index| BabyBear::new(100 + index as u32)),
        };
        let proof = prove_wide_value_binding(&witness).expect("wide HidingFRI proof");
        let legacy = proof.claim.legacy_binding.as_u32();
        let token = verify_wide_binding_compatibility_v4(&proof, legacy)
            .expect("fixed wide verifier accepts its exact compatibility claim");
        assert_eq!(token.legacy_value_binding, legacy);
        assert_eq!(
            token.value_asset_binding,
            proof.claim.wide_binding.map(BabyBear::as_u32)
        );
        assert!(verify_wide_binding_compatibility_v4(&proof, (legacy + 1) % BABYBEAR_P).is_err());
    }

    #[test]
    fn legacy_mod_p_alias_is_not_same_opening_and_fxc4_keeps_value_and_asset_distinct() {
        let base = WideValueBindingWitness {
            value: 5,
            asset_type: 7,
            legacy_randomness: BabyBear::new(9),
            binding_blind: [BabyBear::new(13); BINDING_BLIND_LANES],
        };
        let value_alias = WideValueBindingWitness {
            value: base.value + u64::from(BABYBEAR_P),
            ..base.clone()
        };
        let asset_alias = WideValueBindingWitness {
            asset_type: base.asset_type + u64::from(BABYBEAR_P),
            ..base.clone()
        };
        assert_eq!(base.legacy_binding(), value_alias.legacy_binding());
        assert_eq!(base.legacy_binding(), asset_alias.legacy_binding());
        assert_ne!(base.wide_binding(), value_alias.wide_binding());
        assert_ne!(base.wide_binding(), asset_alias.wide_binding());

        let nullifier = [0x42; 32];
        let legacy = base.legacy_binding().as_u32();
        let ring = ring_public(17, legacy);
        let prepare = |wide: [BabyBear; WIDE_VALUE_BINDING_LANES]| {
            PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
                ledger(),
                dark_amm(),
                ring,
                0,
                17,
                nullifier,
                compatibility(legacy, wide.map(BabyBear::as_u32)),
                2,
                root(500),
            )
            .unwrap()
            .root()
        };
        let base_root = prepare(base.wide_binding());
        assert_ne!(base_root, prepare(value_alias.wide_binding()));
        assert_ne!(base_root, prepare(asset_alias.wide_binding()));
    }

    #[test]
    fn fni4_binds_all_wide_lanes_and_is_domain_separate_from_fni2_fns3() {
        let addr = TaggedKeyWire::real([0x11; 32]);
        let next = ExactTaggedKey::Top.wire();
        let binding = core::array::from_fn(|index| 1000 + index as u32);
        let leaf = ShieldedExactLinkedLeafV4::try_new(addr, binding, next).unwrap();
        let digest = shielded_exact_leaf_digest(leaf);
        for lane in 0..WIDE_VALUE_BINDING_LANES {
            let mut changed = binding;
            changed[lane] += 1;
            let changed = ShieldedExactLinkedLeafV4::try_new(addr, changed, next).unwrap();
            assert_ne!(
                shielded_exact_leaf_digest(changed),
                digest,
                "wide lane {lane}"
            );
        }

        let tree_root = digest;
        let mut changed_tree_root = tree_root;
        changed_tree_root[7] += BabyBear::ONE;
        assert_ne!(
            shielded_exact_state_commit(tree_root, 1),
            exact_state_commit(tree_root, 1),
            "FNS4 must never alias v3's FNS3 domain on the same root/count"
        );
        assert_ne!(
            shielded_exact_state_commit(tree_root, 1),
            shielded_exact_state_commit(changed_tree_root, 1),
            "the complete FNI4 root must bind into FNS4"
        );
        assert_ne!(
            shielded_exact_state_commit(tree_root, 1),
            shielded_exact_state_commit(tree_root, 2),
            "the terminal count must bind into FNS4"
        );
    }

    #[test]
    fn consequence_binds_full_nullifier_wide_commitment_market_ring_and_outputs() {
        let nullifier = [0x42; 32];
        let binding = core::array::from_fn(|index| 700 + index as u32);
        let baseline_prepared = consequence(nullifier, binding);
        let transcript = baseline_prepared.canonical_preimage();
        assert_eq!(transcript[0], SHIELDED_CONSEQUENCE_DOMAIN);
        assert_eq!(transcript[1], crate::dark_amm_private::RULE_ID);
        assert_eq!(transcript[2], RING_ENDPOINT_PUBLIC_LEN as u32);
        assert_eq!(transcript[3], 0);
        let baseline = baseline_prepared.root();

        let mut changed_ledger = ledger();
        changed_ledger.historical_root_height += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );
        let mut changed_ledger = ledger();
        changed_ledger.historical_note_root[7] += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );
        let mut changed_ledger = ledger();
        changed_ledger.successor_exact_root[7] += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );
        let mut changed_ledger = ledger();
        changed_ledger.prior_exact_root[7] += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );
        let mut changed_ledger = ledger();
        changed_ledger.pre_count += 1;
        changed_ledger.post_count += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );
        let mut changed_ledger = ledger();
        changed_ledger.before_outer_commit[7] += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );
        let mut changed_ledger = ledger();
        changed_ledger.after_outer_commit[7] += 1;
        assert_ne!(
            consequence_with_ledger(changed_ledger, nullifier, binding).root(),
            baseline
        );

        let mut changed_nullifier = nullifier;
        changed_nullifier[31] ^= 0x80;
        assert_ne!(consequence(changed_nullifier, binding).root(), baseline);

        let mut changed_binding = binding;
        changed_binding[15] += 1;
        assert_ne!(consequence(nullifier, changed_binding).root(), baseline);

        let mut changed_amm = dark_amm();
        changed_amm.new_root[7] += 1;
        let changed = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
            ledger(),
            changed_amm,
            ring_public(17, 23),
            0,
            17,
            nullifier,
            compatibility(23, binding),
            2,
            root(500),
        )
        .unwrap();
        assert_ne!(changed.root(), baseline);

        let dark_lanes = dark_amm().as_u32_array();
        for lane in 0..DARK_AMM_PUBLIC_INPUT_COUNT {
            let mut mutated = dark_lanes;
            mutated[lane] = (mutated[lane] + 1) % BABYBEAR_P;
            let parsed = PublicStatement::try_from_u32s(&mutated);
            if lane == 1 {
                assert!(parsed.is_err(), "fixed Dark-AMM rule selector must refuse");
                continue;
            }
            let changed = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
                ledger(),
                parsed.expect("canonical mutated Dark-AMM statement"),
                ring_public(17, 23),
                0,
                17,
                nullifier,
                compatibility(23, binding),
                2,
                root(500),
            )
            .unwrap();
            assert_ne!(changed.root(), baseline, "Dark-AMM lane {lane}");
        }

        let mut changed_ring = ring_public(17, 23);
        changed_ring[endpoint_pi::POST_COMMIT_8] += 1;
        let changed = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
            ledger(),
            dark_amm(),
            changed_ring,
            0,
            17,
            nullifier,
            compatibility(23, binding),
            2,
            root(500),
        )
        .unwrap();
        assert_ne!(changed.root(), baseline);

        for lane in 0..RING_ENDPOINT_PUBLIC_LEN {
            let mut changed_ring = ring_public(17, 23);
            changed_ring[lane] = (changed_ring[lane] + 1) % BABYBEAR_P;
            let changed = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
                ledger(),
                dark_amm(),
                changed_ring,
                0,
                17,
                nullifier,
                compatibility(23, binding),
                2,
                root(500),
            );
            if lane == 0 || lane == 2 {
                assert!(
                    changed.is_err(),
                    "selected ring weld lane {lane} must refuse"
                );
            } else {
                assert_ne!(changed.unwrap().root(), baseline, "ring lane {lane}");
            }
        }

        let changed_leg = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
            ledger(),
            dark_amm(),
            ring_public(17, 23),
            1,
            18,
            nullifier,
            compatibility(24, binding),
            2,
            root(500),
        )
        .unwrap();
        assert_ne!(changed_leg.root(), baseline, "selected ring leg selector");

        let changed = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
            ledger(),
            dark_amm(),
            ring_public(17, 23),
            0,
            17,
            nullifier,
            compatibility(23, binding),
            3,
            root(500),
        )
        .unwrap();
        assert_ne!(changed.root(), baseline);

        let changed = PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
            ledger(),
            dark_amm(),
            ring_public(17, 23),
            0,
            17,
            nullifier,
            compatibility(23, binding),
            2,
            root(501),
        )
        .unwrap();
        assert_ne!(changed.root(), baseline);
    }

    #[test]
    fn same_fields_are_shared_and_every_apex_component_bites() {
        let nullifier = [0x42; 32];
        let binding = core::array::from_fn(|index| 700 + index as u32);
        let statement = public(nullifier, binding);
        assert_eq!(statement.nullifier(), nullifier);
        assert_eq!(statement.value_asset_binding(), binding);
        assert_eq!(statement.output_notes_root(), root(500));
        assert_eq!(
            statement,
            ShieldedExactApexV4Public::from_le_bytes(&statement.to_le_bytes()).unwrap()
        );

        let baseline = statement.apex_binding_digest();
        for index in 0..SHIELDED_EXACT_APEX_V4_PUBLIC_INPUT_COUNT {
            let mut lanes = *statement.as_u32_array();
            // Keep the exact +1 count law while exercising those fields.
            if (PI_PRE_COUNT..PI_CONSEQUENCE_ROOT).contains(&index) {
                continue;
            }
            lanes[index] = (lanes[index] + 1) % BABYBEAR_P;
            let changed = ShieldedExactApexV4Public::try_from_u32s(&lanes).unwrap();
            assert_ne!(
                changed.apex_binding_digest(),
                baseline,
                "public lane {index}"
            );
        }
    }

    #[test]
    fn hostile_mismatches_noncanonical_lanes_and_count_aliases_refuse() {
        let nullifier = [0x42; 32];
        let binding = core::array::from_fn(|index| 700 + index as u32);
        let mut wrong_ring = ring_public(17, 23);
        wrong_ring[2] = 24;
        assert!(matches!(
            PreparedShieldedConsequenceV4::from_current_dark_amm_and_ring_publics(
                ledger(),
                dark_amm(),
                wrong_ring,
                0,
                17,
                nullifier,
                compatibility(23, binding),
                2,
                root(500),
            ),
            Err(ShieldedExactApexV4Error::LegacyValueBindingMismatch)
        ));

        let statement = public(nullifier, binding);
        let mut lanes = *statement.as_u32_array();
        lanes[PI_VALUE_ASSET_BINDING] = BABYBEAR_P;
        assert!(matches!(
            ShieldedExactApexV4Public::try_from_u32s(&lanes),
            Err(ShieldedExactApexV4Error::NonCanonicalLane { .. })
        ));

        let mut lanes = *statement.as_u32_array();
        lanes[PI_NULLIFIER] = u16::MAX as u32 + 1;
        assert!(matches!(
            ShieldedExactApexV4Public::try_from_u32s(&lanes),
            Err(ShieldedExactApexV4Error::NonCanonicalU16Lane { .. })
        ));

        let mut lanes = *statement.as_u32_array();
        lanes[PI_POST_COUNT] += 1;
        assert!(matches!(
            ShieldedExactApexV4Public::try_from_u32s(&lanes),
            Err(ShieldedExactApexV4Error::CountTransition { .. })
        ));

        assert!(ShieldedExactApexV4Public::from_le_bytes(&statement.to_le_bytes()[..399]).is_err());
    }
}
