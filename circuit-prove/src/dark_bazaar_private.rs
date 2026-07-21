//! Fixed `N=4,K=4` private-order Dark Bazaar proof producer.
//!
//! The relation and descriptor are authored in Lean at
//! `Market/DarkBazaarPrivateDescriptor.lean`; this module only validates inputs,
//! fills its fixed witness columns, and consumes the emitted JSON. Public inputs
//! are `(session, rule, order_root, p_star, v_star)`. Order side/limit/quantity
//! and the root blinding never enter the public vector. [`prove_zk`] is the
//! shielded entry point; [`prove_non_hiding`] exists only as an explicit
//! compatibility/debug lane and makes no witness-hiding claim. `HidingFriPcs`
//! hides the witness from proof consumers, not from the process constructing
//! this trace: this is a Tier-1/operator-visible receipt, not Tier-0 house-blind
//! clearing. A no-single-viewer FHE/MPC producer remains a separate composition.

use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};

/// The exact Lean-emitted descriptor artifact.
pub const DARK_BAZAAR_PRIVATE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/dark-bazaar-private-n4k4.json");

pub const ORDER_COUNT: usize = 4;
pub const PRICE_COUNT: usize = 4;
pub const MAX_QTY: u8 = 15;
pub const RULE_ID: u32 = 1_430_520_836;
pub const ROOT_DOMAIN_TAG: u32 = 1_145_194_322;
pub const DIGEST_WIDTH: usize = 8;

const TRACE_WIDTH: usize = 181;
const SESSION: usize = 0;
const RULE: usize = 1;
const ROOT_BASE: usize = 2;
const PSTAR: usize = 10;
const VSTAR: usize = 11;
const BLINDING_BASE: usize = 12;
const PACKED_BOOK: usize = 20;
const ORDER_BASE: usize = 21;
const ORDER_STRIDE: usize = 14;
const DEMAND_BASE: usize = 77;
const SUPPLY_BASE: usize = 81;
const VOLUME_BASE: usize = 85;
const MIN_CHOOSE_BASE: usize = 89;
const MIN_DIFF_BASE: usize = 93;
const MIN_DIFF_BITS_BASE: usize = 97;
const SELECT_BASE: usize = 121;
const MAX_DIFF_BASE: usize = 125;
const MAX_DIFF_BITS_BASE: usize = 129;
const LOW_SLACK_BASE: usize = 153;
const LOW_SLACK_BITS_BASE: usize = 157;
const DIFF_BITS: usize = 6;

#[inline]
const fn kind_col(i: usize, t: usize) -> usize {
    ORDER_BASE + ORDER_STRIDE * i + t
}
#[inline]
const fn qty_col(i: usize) -> usize {
    ORDER_BASE + ORDER_STRIDE * i + 8
}
#[inline]
const fn qty_bit_col(i: usize, bit: usize) -> usize {
    ORDER_BASE + ORDER_STRIDE * i + 9 + bit
}
#[inline]
const fn order_pack_col(i: usize) -> usize {
    ORDER_BASE + ORDER_STRIDE * i + 13
}
#[inline]
const fn min_diff_bit_col(p: usize, bit: usize) -> usize {
    MIN_DIFF_BITS_BASE + DIFF_BITS * p + bit
}
#[inline]
const fn max_diff_bit_col(p: usize, bit: usize) -> usize {
    MAX_DIFF_BITS_BASE + DIFF_BITS * p + bit
}
#[inline]
const fn low_slack_bit_col(p: usize, bit: usize) -> usize {
    LOW_SLACK_BITS_BASE + DIFF_BITS * p + bit
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Bid,
    Ask,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateOrder {
    pub side: Side,
    pub qty: u8,
    pub limit: u8,
}

impl PrivateOrder {
    pub const fn bid(qty: u8, limit: u8) -> Self {
        Self {
            side: Side::Bid,
            qty,
            limit,
        }
    }

    pub const fn ask(qty: u8, limit: u8) -> Self {
        Self {
            side: Side::Ask,
            qty,
            limit,
        }
    }

    fn validate(self) -> Result<(), String> {
        if self.qty > MAX_QTY {
            return Err(format!(
                "quantity {} is outside fixed 4-bit family [0,{MAX_QTY}]",
                self.qty
            ));
        }
        if self.limit as usize >= PRICE_COUNT {
            return Err(format!(
                "limit {} is outside fixed K={PRICE_COUNT} family",
                self.limit
            ));
        }
        Ok(())
    }

    #[inline]
    fn kind(self) -> u32 {
        self.limit as u32
            + match self.side {
                Side::Bid => 0,
                Side::Ask => PRICE_COUNT as u32,
            }
    }

    #[inline]
    fn code(self) -> u32 {
        self.kind() + 8 * self.qty as u32
    }
}

/// Exactly four committed slots. Fewer product orders are padded with the
/// canonical zero-quantity bid; more than four fail closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBookWitness {
    pub orders: [PrivateOrder; ORDER_COUNT],
    /// Eight fresh canonical BabyBear elements. The caller must draw these from
    /// a cryptographically secure RNG for a hiding commitment; this constructor
    /// deliberately refuses host integers that would alias after field reduction.
    pub blinding: [u32; DIGEST_WIDTH],
}

impl PrivateBookWitness {
    /// Build from caller-owned blinding (for deterministic fixtures or a
    /// distributed source that already jointly sampled the commitment blind).
    pub fn try_from_orders_with_blinding(
        orders: &[PrivateOrder],
        blinding: [u32; DIGEST_WIDTH],
    ) -> Result<Self, String> {
        if orders.len() > ORDER_COUNT {
            return Err(format!(
                "{} orders exceed fixed N={ORDER_COUNT} family",
                orders.len()
            ));
        }
        let pad = PrivateOrder::bid(0, 0);
        let mut fixed = [pad; ORDER_COUNT];
        for (i, &order) in orders.iter().enumerate() {
            order.validate()?;
            fixed[i] = order;
        }
        for (lane, &blind) in blinding.iter().enumerate() {
            if blind >= BABYBEAR_P {
                return Err(format!(
                    "blinding lane {lane}={blind} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        Ok(Self {
            orders: fixed,
            blinding,
        })
    }

    /// Build with eight independently rejection-sampled BabyBear elements from
    /// OS entropy. Distributed/no-viewer producers should instead supply
    /// jointly generated limbs through [`Self::try_from_orders_with_blinding`].
    pub fn try_from_orders_fresh(orders: &[PrivateOrder]) -> Result<Self, String> {
        let modulus = BABYBEAR_P as u64;
        let accept_below = ((u32::MAX as u64 + 1) / modulus) * modulus;
        let mut blinding = [0u32; DIGEST_WIDTH];
        for blind in &mut blinding {
            loop {
                let mut bytes = [0u8; 4];
                getrandom::fill(&mut bytes)
                    .map_err(|e| format!("OS randomness failed for Dark Bazaar blinding: {e}"))?;
                let candidate = u32::from_le_bytes(bytes) as u64;
                if candidate < accept_below {
                    *blind = (candidate % modulus) as u32;
                    break;
                }
            }
        }
        Self::try_from_orders_with_blinding(orders, blinding)
    }

    fn validate(&self) -> Result<(), String> {
        for order in self.orders {
            order.validate()?;
        }
        for (lane, &blind) in self.blinding.iter().enumerate() {
            if blind >= BABYBEAR_P {
                return Err(format!(
                    "blinding lane {lane}={blind} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        Ok(())
    }
}

/// The only twelve felts revealed by this fixed family: session, rule, the
/// faithful eight-felt source root, and the exact clearing `(p*,V*)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub session: u32,
    pub rule: u32,
    pub order_root: [u32; DIGEST_WIDTH],
    pub p_star: u32,
    pub v_star: u32,
}

impl PublicStatement {
    fn as_felts(self) -> [BabyBear; 12] {
        let mut public = [BabyBear::ZERO; 12];
        public[0] = BabyBear::new(self.session);
        public[1] = BabyBear::new(self.rule);
        for (lane, root) in self.order_root.into_iter().enumerate() {
            public[2 + lane] = BabyBear::new(root);
        }
        public[10] = BabyBear::new(self.p_star);
        public[11] = BabyBear::new(self.v_star);
        public
    }

    fn validate_shape(self) -> Result<(), String> {
        if self.session >= BABYBEAR_P {
            return Err(format!(
                "session {} is noncanonical for BabyBear modulus {BABYBEAR_P}",
                self.session
            ));
        }
        if self.rule != RULE_ID {
            return Err(format!(
                "rule {} is not fixed Dark Bazaar rule {RULE_ID}",
                self.rule
            ));
        }
        if self.p_star as usize >= PRICE_COUNT {
            return Err(format!(
                "p* {} is outside fixed K={PRICE_COUNT} family",
                self.p_star
            ));
        }
        if self.v_star > (ORDER_COUNT as u32) * (MAX_QTY as u32) {
            return Err(format!(
                "V* {} exceeds fixed family volume bound {}",
                self.v_star,
                ORDER_COUNT as u32 * MAX_QTY as u32
            ));
        }
        for (lane, root) in self.order_root.into_iter().enumerate() {
            if root >= BABYBEAR_P {
                return Err(format!(
                    "order-root lane {lane}={root} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        Ok(())
    }
}

/// A binding, explicitly non-hiding proof. Do not use this type for a Dark
/// Bazaar privacy claim; use [`DarkBazaarPrivateZkProof`] instead.
pub struct DarkBazaarPrivateNonHidingProof {
    proof: Ir2BatchProof<DreggStarkConfig>,
}

/// A private-order proof produced through `HidingFriPcs` with fresh OS-seeded
/// salted leaves, random trace rows, and random FRI codewords.
pub struct DarkBazaarPrivateZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl DarkBazaarPrivateZkProof {
    /// Canonical opaque proof body for worker, receipt, and file transport.
    /// The public statement is deliberately transported separately and must be
    /// supplied independently to [`verify_zk`].
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private Dark Bazaar proof encode failed: {error}"))
    }

    /// Decode an opaque proof body. This performs no verification and trusts no
    /// public values from the body; callers must still invoke [`verify_zk`].
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private Dark Bazaar proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(DARK_BAZAAR_PRIVATE_DESCRIPTOR_JSON)?;
    if desc.name != "dark-bazaar-private-n4k4::wide-poseidon2-v2"
        || desc.trace_width != TRACE_WIDTH
        || desc.public_input_count != 12
    {
        return Err("Dark Bazaar emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

#[inline]
fn set_bits(row: &mut [BabyBear], value: u32, bits: usize, col: impl Fn(usize) -> usize) {
    for bit in 0..bits {
        row[col(bit)] = BabyBear::new((value >> bit) & 1);
    }
}

fn build_row(
    session: u32,
    witness: &PrivateBookWitness,
) -> Result<(Vec<BabyBear>, PublicStatement), String> {
    witness.validate()?;
    if session >= BABYBEAR_P {
        return Err(format!(
            "session {session} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[SESSION] = BabyBear::new(session);
    row[RULE] = BabyBear::new(RULE_ID);
    for (lane, blind) in witness.blinding.into_iter().enumerate() {
        row[BLINDING_BASE + lane] = BabyBear::new(blind);
    }

    let mut packed_book = 0u32;
    for (i, order) in witness.orders.iter().copied().enumerate() {
        let kind = order.kind() as usize;
        row[kind_col(i, kind)] = BabyBear::ONE;
        row[qty_col(i)] = BabyBear::new(order.qty as u32);
        set_bits(&mut row, order.qty as u32, 4, |b| qty_bit_col(i, b));
        let code = order.code();
        row[order_pack_col(i)] = BabyBear::new(code);
        packed_book += code * 128u32.pow(i as u32);
    }
    debug_assert!(packed_book < (1 << 28));
    row[PACKED_BOOK] = BabyBear::new(packed_book);

    // Full arity-16 is load-bearing: the deployed chip's arity selector seeds
    // all 16 state lanes in this mode. Arity 12 would replace input lanes 4..6
    // with its tag and silently drop three blind limbs.
    let mut root_preimage = Vec::with_capacity(16);
    root_preimage.extend([
        BabyBear::new(ROOT_DOMAIN_TAG),
        row[SESSION],
        row[RULE],
        row[PACKED_BOOK],
    ]);
    root_preimage.extend(witness.blinding.map(BabyBear::new));
    root_preimage.extend([BabyBear::ZERO; 4]);
    let root = chip_absorb_all_lanes(root_preimage.len(), &root_preimage);
    row[ROOT_BASE..ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&root);

    let mut volume = [0u32; PRICE_COUNT];
    for p in 0..PRICE_COUNT {
        let mut demand = 0u32;
        let mut supply = 0u32;
        for order in witness.orders {
            match order.side {
                Side::Bid if p <= order.limit as usize => demand += order.qty as u32,
                Side::Ask if order.limit as usize <= p => supply += order.qty as u32,
                _ => {}
            }
        }
        let choose_demand = demand <= supply;
        let v = demand.min(supply);
        let diff = demand.abs_diff(supply);
        volume[p] = v;
        row[DEMAND_BASE + p] = BabyBear::new(demand);
        row[SUPPLY_BASE + p] = BabyBear::new(supply);
        row[VOLUME_BASE + p] = BabyBear::new(v);
        row[MIN_CHOOSE_BASE + p] = BabyBear::new(choose_demand as u32);
        row[MIN_DIFF_BASE + p] = BabyBear::new(diff);
        set_bits(&mut row, diff, DIFF_BITS, |b| min_diff_bit_col(p, b));
    }

    let mut p_star = 0usize;
    for p in 1..PRICE_COUNT {
        if volume[p] > volume[p_star] {
            p_star = p;
        }
    }
    let v_star = volume[p_star];
    row[PSTAR] = BabyBear::new(p_star as u32);
    row[VSTAR] = BabyBear::new(v_star);
    row[SELECT_BASE + p_star] = BabyBear::ONE;

    for p in 0..PRICE_COUNT {
        let max_diff = v_star - volume[p];
        let later_selected = u32::from(p < p_star);
        let low_slack = max_diff.checked_sub(later_selected).ok_or_else(|| {
            "internal lowest-price tie witness failed: earlier bucket ties selected output"
                .to_string()
        })?;
        row[MAX_DIFF_BASE + p] = BabyBear::new(max_diff);
        set_bits(&mut row, max_diff, DIFF_BITS, |b| max_diff_bit_col(p, b));
        row[LOW_SLACK_BASE + p] = BabyBear::new(low_slack);
        set_bits(&mut row, low_slack, DIFF_BITS, |b| low_slack_bit_col(p, b));
    }

    let statement = PublicStatement {
        session,
        rule: RULE_ID,
        order_root: root.map(BabyBear::as_u32),
        p_star: p_star as u32,
        v_star,
    };
    Ok((row, statement))
}

/// Commit and compute the exact public statement without proving it.
pub fn statement(session: u32, witness: &PrivateBookWitness) -> Result<PublicStatement, String> {
    build_row(session, witness).map(|(_, public)| public)
}

fn trace_and_public(
    session: u32,
    witness: &PrivateBookWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (row, public) = build_row(session, witness)?;
    let desc = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((desc, trace, public))
}

/// Prove the exact statement through the binding, **non-hiding** compatibility
/// configuration. The witness is absent from public inputs, but raw FRI query
/// openings are not hidden. Privacy-sensitive callers must use [`prove_zk`].
pub fn prove_non_hiding(
    session: u32,
    witness: &PrivateBookWitness,
) -> Result<(DarkBazaarPrivateNonHidingProof, PublicStatement), String> {
    let (desc, trace, public) = trace_and_public(session, witness)?;
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
    )?;
    Ok((DarkBazaarPrivateNonHidingProof { proof }, public))
}

/// Verify an explicitly non-hiding proof against caller-supplied public values.
pub fn verify_non_hiding(
    proof: &DarkBazaarPrivateNonHidingProof,
    public: PublicStatement,
) -> Result<(), String> {
    public.validate_shape()?;
    verify_vm_descriptor2(&descriptor()?, &proof.proof, &public.as_felts())
}

/// Prove the exact private-order statement through `DreggZkStarkConfig` and
/// Plonky3's `HidingFriPcs`. Each invocation creates a fresh OS-seeded config,
/// which supplies independent Merkle salts, random trace rows, and random FRI
/// codewords. The verifier learns only `(session,rule,root[0..8),p*,V*)`.
/// The process building this trace still sees the book; this is shielded from
/// verifier/public, not a no-single-viewer FHE/MPC clearing service.
pub fn prove_zk(
    session: u32,
    witness: &PrivateBookWitness,
) -> Result<(DarkBazaarPrivateZkProof, PublicStatement), String> {
    let (desc, trace, public) = trace_and_public(session, witness)?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((DarkBazaarPrivateZkProof { proof }, public))
}

/// CSPRNG-backed convenience entry point: sample a fresh canonical 8-felt
/// commitment blind, construct the fixed book, and mint its hiding proof.
pub fn prove_orders_zk(
    session: u32,
    orders: &[PrivateOrder],
) -> Result<(DarkBazaarPrivateZkProof, PublicStatement), String> {
    let witness = PrivateBookWitness::try_from_orders_fresh(orders)?;
    prove_zk(session, &witness)
}

/// Verify a hiding proof without the private orders or prover randomness.
pub fn verify_zk(proof: &DarkBazaarPrivateZkProof, public: PublicStatement) -> Result<(), String> {
    public.validate_shape()?;
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    fn blind() -> [u32; DIGEST_WIDTH] {
        core::array::from_fn(|lane| 777 + lane as u32)
    }

    fn fixture() -> PrivateBookWitness {
        PrivateBookWitness::try_from_orders_with_blinding(
            &[
                PrivateOrder::bid(10, 2),
                PrivateOrder::bid(6, 1),
                PrivateOrder::ask(5, 0),
                PrivateOrder::ask(8, 1),
            ],
            blind(),
        )
        .expect("fixed book")
    }

    #[test]
    fn dark_bazaar_private_fixed_shape_fails_closed() {
        assert!(
            PrivateBookWitness::try_from_orders_with_blinding(
                &[PrivateOrder::bid(1, 0); 5],
                blind()
            )
            .is_err()
        );
        assert!(
            PrivateBookWitness::try_from_orders_with_blinding(&[PrivateOrder::bid(16, 0)], blind())
                .is_err()
        );
        assert!(
            PrivateBookWitness::try_from_orders_with_blinding(&[PrivateOrder::ask(1, 4)], blind())
                .is_err()
        );
        let mut noncanonical = blind();
        noncanonical[3] = BABYBEAR_P;
        assert!(
            PrivateBookWitness::try_from_orders_with_blinding(
                &[PrivateOrder::bid(1, 0)],
                noncanonical
            )
            .is_err(),
            "a blind limb must refuse before field reduction can alias it"
        );
        assert!(
            statement(BABYBEAR_P, &fixture()).is_err(),
            "a noncanonical public session must also refuse before field reduction"
        );
        let fresh_a = PrivateBookWitness::try_from_orders_fresh(&[PrivateOrder::bid(1, 0)])
            .expect("OS-seeded blind");
        let fresh_b = PrivateBookWitness::try_from_orders_fresh(&[PrivateOrder::bid(1, 0)])
            .expect("second OS-seeded blind");
        assert!(fresh_a.blinding.into_iter().all(|blind| blind < BABYBEAR_P));
        assert!(fresh_b.blinding.into_iter().all(|blind| blind < BABYBEAR_P));
        assert_ne!(fresh_a.blinding, fresh_b.blinding);
        assert_ne!(
            statement(99, &fresh_a).expect("fresh statement").order_root,
            statement(99, &fresh_b).expect("fresh statement").order_root,
            "fresh commitment blinds produce distinct wide roots"
        );
        let desc = descriptor().expect("emitted descriptor decodes");
        assert_eq!(desc.public_input_count, 12);
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        let mut pins = desc
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
        assert_eq!(
            pins,
            vec![
                (VmRow::First, SESSION, 0),
                (VmRow::First, RULE, 1),
                (VmRow::First, ROOT_BASE, 2),
                (VmRow::First, ROOT_BASE + 1, 3),
                (VmRow::First, ROOT_BASE + 2, 4),
                (VmRow::First, ROOT_BASE + 3, 5),
                (VmRow::First, ROOT_BASE + 4, 6),
                (VmRow::First, ROOT_BASE + 5, 7),
                (VmRow::First, ROOT_BASE + 6, 8),
                (VmRow::First, ROOT_BASE + 7, 9),
                (VmRow::First, PSTAR, 10),
                (VmRow::First, VSTAR, 11),
            ],
            "the descriptor publishes exactly session/rule/root8/p*/V*; no order column is a PI"
        );
    }

    #[test]
    fn dark_bazaar_private_statement_is_exact_lowest_argmax_and_bound() {
        let witness = fixture();
        let public = statement(99, &witness).expect("statement");
        assert_eq!((public.p_star, public.v_star), (1, 13));
        assert_eq!(public.rule, RULE_ID);

        let mut changed = witness.clone();
        changed.orders[0].qty = 11;
        assert_ne!(
            statement(99, &changed)
                .expect("changed statement")
                .order_root,
            public.order_root,
            "a private order mutation changes the committed source root"
        );
        assert_ne!(
            statement(100, &witness).expect("new session").order_root,
            public.order_root,
            "the public session is inside the committed root"
        );
        let mut reblinded = witness.clone();
        reblinded.blinding[0] += 1;
        assert_ne!(
            statement(99, &reblinded).expect("fresh blind").order_root,
            public.order_root,
            "all eight private blinding lanes are inside the wide commitment"
        );
    }

    #[test]
    fn dark_bazaar_private_hiding_proves_randomizes_and_public_tampers_refuse() {
        let (proof, public) = prove_zk(99, &fixture()).expect("honest private book proves hiding");
        verify_zk(&proof, public).expect("honest hiding proof verifies");
        let proof_wire = proof.to_postcard().expect("proof transport encodes");
        let transported =
            DarkBazaarPrivateZkProof::from_postcard(&proof_wire).expect("proof transport decodes");
        assert_eq!(
            transported.to_postcard().expect("proof re-encodes"),
            proof_wire,
            "the accepted proof wire has one canonical postcard encoding"
        );
        verify_zk(&transported, public).expect("transported proof verifies");
        assert!(
            proof.proof.commitments.random.is_some(),
            "the batch proof must carry the ZK random-polynomial commitment"
        );
        assert!(
            proof
                .proof
                .opened_values
                .instances
                .iter()
                .all(|instance| instance.base_opened_values.random.is_some()),
            "every present AIR instance must carry its ZK random opening"
        );

        let (rerun, rerun_public) =
            prove_zk(99, &fixture()).expect("a second hiding proof also mints");
        assert_eq!(rerun_public, public);
        assert_ne!(
            format!("{:?}", proof.proof.commitments.random),
            format!("{:?}", rerun.proof.commitments.random),
            "fresh OS-seeded randomness must change the random commitment"
        );
        verify_zk(&rerun, rerun_public).expect("second hiding proof verifies");

        let mut changed_witness = fixture();
        changed_witness.orders[0].qty = 11;
        let (changed_proof, changed_public) =
            prove_zk(99, &changed_witness).expect("changed private book also proves hiding");
        verify_zk(&changed_proof, changed_public).expect("changed proof verifies for its own root");
        assert_eq!(
            (changed_public.p_star, changed_public.v_star),
            (public.p_star, public.v_star),
            "the mutation isolates source binding rather than changing the public clearing"
        );
        assert_ne!(changed_public.order_root, public.order_root);
        assert!(
            verify_zk(&changed_proof, public).is_err(),
            "a proof for a mutated private order refuses the original committed root"
        );

        let mut forged_root = public;
        forged_root.order_root[0] = (forged_root.order_root[0] + 1) % BABYBEAR_P;
        assert!(
            verify_zk(&proof, forged_root).is_err(),
            "forged order root refuses"
        );

        let mut forged_price = public;
        forged_price.p_star = 2;
        assert!(
            verify_zk(&proof, forged_price).is_err(),
            "forged p* refuses"
        );

        let mut forged_volume = public;
        forged_volume.v_star -= 1;
        assert!(
            verify_zk(&proof, forged_volume).is_err(),
            "forged V* refuses"
        );
    }
}
