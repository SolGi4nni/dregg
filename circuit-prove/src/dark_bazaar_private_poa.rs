//! Receipt-bound Path of Angels Dark Bazaar proof family.
//!
//! This is a separately versioned extension of [`crate::dark_bazaar_private`].
//! It proves the same Lean-authored fixed N=4/K=4 private clearing relation and
//! publishes one additional value: the canonical PoA transition receipt digest
//! as eight independent BabyBear lanes. The verifier requires the exact 32
//! bytes returned by the Lean judge and compares every lane before checking the
//! proof. No 256-to-31-bit fold or modulo-reducing decoder exists here.
//!
//! Receipt binding is not transition semantics. The caller must actually run
//! the Lean public-transition judge and supply its canonical receipt digest;
//! this module neither computes nor substitutes a Rust state-machine twin.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};

use crate::dark_bazaar_private::{
    DIGEST_WIDTH, MAX_QTY, ORDER_COUNT, PRICE_COUNT, PrivateBookWitness,
    PublicStatement as PrivatePublicStatement, RULE_ID,
};

/// Exact Lean-emitted v2 descriptor artifact.
pub const DARK_BAZAAR_PRIVATE_POA_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/dark-bazaar-private-poa-n4k4-v2.json");

pub const TRACE_WIDTH: usize = 189;
pub const PUBLIC_INPUT_COUNT: usize = 20;
pub const POA_RECEIPT_BASE: usize = 181;
pub const POA_RECEIPT_PI_BASE: usize = 12;

/// Canonical eight-lane representation of Lean's `Digest32` receipt output.
///
/// Lean's Dark Bazaar wire uses `V1.digestOfRoot`: eight canonical BabyBear
/// representatives, each serialized as one little-endian `u32`. The inner
/// array is private so construction always checks all eight representatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoaReceiptDigest([u32; DIGEST_WIDTH]);

impl PoaReceiptDigest {
    /// Decode the exact 32-byte Lean wire. Values at or above the BabyBear
    /// modulus refuse; silently applying `% p` would create aliases.
    pub fn try_from_lean_bytes(bytes: [u8; 32]) -> Result<Self, String> {
        let mut lanes = [0u32; DIGEST_WIDTH];
        for (lane, chunk) in bytes.chunks_exact(4).enumerate() {
            let value = u32::from_le_bytes(
                chunk
                    .try_into()
                    .expect("chunks_exact(4) always yields four bytes"),
            );
            if value >= BABYBEAR_P {
                return Err(format!(
                    "PoA receipt lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
            lanes[lane] = value;
        }
        Ok(Self(lanes))
    }

    pub const fn lanes(self) -> [u32; DIGEST_WIDTH] {
        self.0
    }

    pub fn to_lean_bytes(self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (lane, value) in self.0.into_iter().enumerate() {
            bytes[4 * lane..4 * lane + 4].copy_from_slice(&value.to_le_bytes());
        }
        bytes
    }
}

/// The exact twenty public felts verified by this family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub private: PrivatePublicStatement,
    pub poa_receipt_digest: PoaReceiptDigest,
}

impl PublicStatement {
    /// Refuse every host integer which would be silently reduced before it
    /// reaches the proof verifier.  This mirrors the v1 wire-shape checks while
    /// keeping the v2 verifier independently fail-closed.
    fn validate_shape(self) -> Result<(), String> {
        if self.private.session >= BABYBEAR_P {
            return Err(format!(
                "session {} is noncanonical for BabyBear modulus {BABYBEAR_P}",
                self.private.session
            ));
        }
        if self.private.rule != RULE_ID {
            return Err(format!(
                "rule {} is not fixed Dark Bazaar rule {RULE_ID}",
                self.private.rule
            ));
        }
        if self.private.p_star as usize >= PRICE_COUNT {
            return Err(format!(
                "p* {} is outside fixed K={PRICE_COUNT} family",
                self.private.p_star
            ));
        }
        if self.private.v_star > (ORDER_COUNT as u32) * (MAX_QTY as u32) {
            return Err(format!(
                "V* {} exceeds fixed family volume bound {}",
                self.private.v_star,
                ORDER_COUNT as u32 * MAX_QTY as u32
            ));
        }
        for (lane, root) in self.private.order_root.into_iter().enumerate() {
            if root >= BABYBEAR_P {
                return Err(format!(
                    "order-root lane {lane}={root} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        Ok(())
    }

    fn as_felts(self) -> [BabyBear; PUBLIC_INPUT_COUNT] {
        let mut public = [BabyBear::ZERO; PUBLIC_INPUT_COUNT];
        public[0] = BabyBear::new(self.private.session);
        public[1] = BabyBear::new(self.private.rule);
        for (lane, root) in self.private.order_root.into_iter().enumerate() {
            public[2 + lane] = BabyBear::new(root);
        }
        public[10] = BabyBear::new(self.private.p_star);
        public[11] = BabyBear::new(self.private.v_star);
        for (lane, receipt) in self.poa_receipt_digest.lanes().into_iter().enumerate() {
            public[POA_RECEIPT_PI_BASE + lane] = BabyBear::new(receipt);
        }
        public
    }
}

/// Opaque HidingFRI proof for the receipt-bound v2 statement.
pub struct DarkBazaarPrivatePoaZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl DarkBazaarPrivatePoaZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private PoA Dark Bazaar proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private PoA Dark Bazaar proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DARK_BAZAAR_PRIVATE_POA_DESCRIPTOR_JSON)?;
    if descriptor.name != "dark-bazaar-private-poa-n4k4::receipt8-v2"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("PoA Dark Bazaar emitted descriptor shape drifted".to_owned());
    }
    Ok(descriptor)
}

fn trace_and_public(
    session: u32,
    witness: &PrivateBookWitness,
    poa_receipt_digest: PoaReceiptDigest,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (mut row, private) = crate::dark_bazaar_private::build_row(session, witness)?;
    debug_assert_eq!(row.len(), POA_RECEIPT_BASE);
    row.extend(poa_receipt_digest.lanes().into_iter().map(BabyBear::new));
    if row.len() != TRACE_WIDTH {
        return Err("PoA receipt lanes did not extend the private trace exactly".to_owned());
    }
    let public = PublicStatement {
        private,
        poa_receipt_digest,
    };
    let descriptor = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((descriptor, trace, public))
}

/// Produce a proof bound to the exact canonical receipt bytes emitted by Lean.
pub fn prove_zk(
    session: u32,
    witness: &PrivateBookWitness,
    lean_receipt_digest: [u8; 32],
) -> Result<(DarkBazaarPrivatePoaZkProof, PublicStatement), String> {
    let receipt = PoaReceiptDigest::try_from_lean_bytes(lean_receipt_digest)?;
    let (descriptor, trace, public) = trace_and_public(session, witness, receipt)?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((DarkBazaarPrivatePoaZkProof { proof }, public))
}

/// Verify the real proof only after exact comparison with the receipt digest
/// independently returned by the Lean transition judge.
///
/// Requiring this argument at the sole verifier entry point prevents a caller
/// from checking the proof while forgetting the PoA transition join. It does
/// not attest where the bytes came from; the network ingress must invoke Lean.
pub fn verify_zk(
    proof: &DarkBazaarPrivatePoaZkProof,
    public: PublicStatement,
    expected_lean_receipt_digest: [u8; 32],
) -> Result<(), String> {
    public.validate_shape()?;
    let expected = PoaReceiptDigest::try_from_lean_bytes(expected_lean_receipt_digest)?;
    if public.poa_receipt_digest != expected {
        return Err("proof statement names another PoA receipt digest".to_owned());
    }
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dark_bazaar_private::PrivateOrder;
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    fn witness() -> PrivateBookWitness {
        PrivateBookWitness::try_from_orders_with_blinding(
            &[
                PrivateOrder::bid(10, 2),
                PrivateOrder::bid(6, 1),
                PrivateOrder::ask(5, 0),
                PrivateOrder::ask(8, 1),
            ],
            core::array::from_fn(|lane| 777 + lane as u32),
        )
        .expect("fixed private book")
    }

    fn digest(seed: u32) -> [u8; 32] {
        let lanes = core::array::from_fn::<u32, DIGEST_WIDTH, _>(|lane| seed + lane as u32);
        PoaReceiptDigest(lanes).to_lean_bytes()
    }

    #[test]
    fn receipt_wire_is_exact_little_endian_and_refuses_reduction_aliases() {
        let bytes = digest(0x1020_3040);
        let receipt = PoaReceiptDigest::try_from_lean_bytes(bytes).expect("canonical receipt");
        assert_eq!(receipt.to_lean_bytes(), bytes);
        assert_eq!(receipt.lanes()[0], 0x1020_3040);

        let mut alias = bytes;
        alias[..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(PoaReceiptDigest::try_from_lean_bytes(alias).is_err());
    }

    #[test]
    fn verifier_refuses_noncanonical_v1_public_lanes_before_field_reduction() {
        let honest_digest = digest(1000);
        let (proof, mut public) =
            prove_zk(99, &witness(), honest_digest).expect("receipt-bound proof");
        public.private.order_root[0] = BABYBEAR_P;
        assert!(verify_zk(&proof, public, honest_digest).is_err());
    }

    #[test]
    fn descriptor_publishes_all_eight_receipt_lanes_without_moving_v1_pis() {
        let descriptor = descriptor().expect("Lean-emitted descriptor decodes");
        let mut pins = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
                    Some((*row, *col, *pi_index))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        pins.sort_by_key(|(_, _, pi)| *pi);
        assert_eq!(pins.len(), PUBLIC_INPUT_COUNT);
        assert_eq!(pins[0], (VmRow::First, 0, 0));
        assert_eq!(pins[1], (VmRow::First, 1, 1));
        assert_eq!(pins[10], (VmRow::First, 10, 10));
        assert_eq!(pins[11], (VmRow::First, 11, 11));
        for lane in 0..DIGEST_WIDTH {
            assert_eq!(
                pins[POA_RECEIPT_PI_BASE + lane],
                (
                    VmRow::First,
                    POA_RECEIPT_BASE + lane,
                    POA_RECEIPT_PI_BASE + lane,
                )
            );
        }
    }

    #[test]
    fn proof_refuses_substituted_receipt_source_and_successor_identities() {
        let honest_digest = digest(1000);
        let (proof, public) = prove_zk(99, &witness(), honest_digest).expect("receipt-bound proof");
        assert_eq!(public.private.rule, RULE_ID);
        verify_zk(&proof, public, honest_digest).expect("honest exact receipt verifies");

        let substituted_receipt = digest(2000);
        assert!(
            verify_zk(&proof, public, substituted_receipt).is_err(),
            "an expected receipt substitution must fail before proof verification"
        );

        let mut substituted_source = public;
        substituted_source.poa_receipt_digest =
            PoaReceiptDigest::try_from_lean_bytes(digest(3000)).expect("canonical substitution");
        assert!(
            verify_zk(&proof, substituted_source, digest(3000)).is_err(),
            "changing the receipt digest to one induced by another source must break the transcript"
        );

        let mut substituted_successor = public;
        substituted_successor.poa_receipt_digest =
            PoaReceiptDigest::try_from_lean_bytes(digest(4000)).expect("canonical substitution");
        assert!(
            verify_zk(&proof, substituted_successor, digest(4000)).is_err(),
            "changing the receipt digest to one induced by another successor must break the transcript"
        );
    }
}
