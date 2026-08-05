//! Anchored Path of Angels Dark Bazaar settlement proof family (v4).
//!
//! V4 consumes the independently returned Lean Dark Bazaar judge output and
//! publishes the exact public escrow and custody transition together with an
//! eight-lane settlement anchor. The Lean-emitted AIR enforces exact debit,
//! exact credit, authored quote calculation, and per-asset conservation
//! consequences, and forces the anchor to be the Poseidon2 image of the book
//! root, the clearing, the ten settlement scalars and the visibility grade.
//!
//! ⚑ **What v3 published and v4 does not.** V3's public vector carried
//! fifty-five felts, thirty-two of which were the lanes of the judge's input,
//! successor, public-view and receipt digests — pinned to trace columns that no
//! gate body, boundary body or lookup tuple ever named. Its docblock said it
//! "binds" them. It did not: a prover could publish any thirty-two field
//! elements beside a completely honest settlement and every constraint still
//! held. Those digests hash canonical JSON strings, so no AIR over this
//! four-row fixed-width trace can derive them — publishing them was a statement
//! this circuit could not make. They are still checked, host-side, in
//! [`verify_zk`], against a judge the verifier runs itself.
//!
//! The private book is hidden from the verifier by HidingFRI, but the process
//! building the trace receives it. The public statement therefore carries the
//! typed [`ProverVisibilityGrade::VerifierShieldedProducerVisible`] grade. This
//! module does not claim house-blind or no-single-viewer production.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};
use dregg_lean_ffi::poa_dark_bazaar_ffi::{
    PoaDarkBazaarVerdict, judge_poa_dark_bazaar, poa_dark_bazaar_judge_available,
};
use serde::Deserialize;

use crate::dark_bazaar_private::{
    DIGEST_WIDTH, MAX_QTY, ORDER_COUNT, PRICE_COUNT, PrivateBookWitness,
    PublicStatement as PrivatePublicStatement, RULE_ID,
};
use crate::dark_bazaar_private_poa::PoaReceiptDigest;

/// Exact Lean-emitted v4 descriptor artifact.
pub const DARK_BAZAAR_PRIVATE_POA_SETTLEMENT_DESCRIPTOR_JSON: &str = include_str!(
    "../../circuit/descriptors/by-name/dark-bazaar-private-poa-settlement-n4k4-v4.json"
);

pub const TRACE_WIDTH: usize = 480;
pub const PUBLIC_INPUT_COUNT: usize = 31;
pub const V1_TRACE_WIDTH: usize = 181;

/// The two staged settlement-anchor absorbs. `HALF` is the intermediate stage
/// and is NOT published; `ANCHOR` is the eight published lanes.
///
/// These mirror `Market.DarkBazaarPrivatePoaSettlementDescriptor` exactly. The
/// AIR is authored there; this module only reproduces the preimages so the
/// producer writes the same values the Lean-emitted chip lookups force.
pub const HALF_BASE: usize = V1_TRACE_WIDTH;
pub const ANCHOR_BASE: usize = HALF_BASE + DIGEST_WIDTH;
pub const VISIBILITY_COL: usize = ANCHOR_BASE + DIGEST_WIDTH;
pub const SCALAR_BASE: usize = VISIBILITY_COL + 1;
pub const SCALAR_COUNT: usize = 10;
pub const RANGE_BIT_BASE: usize = SCALAR_BASE + SCALAR_COUNT;
pub const STATE_VALUE_BITS: usize = 28;
pub const QUOTE_TICK_BITS: usize = 20;
pub const STATE_VALUE_LIMIT: u64 = 1 << STATE_VALUE_BITS;
pub const QUOTE_TICK_LIMIT: u64 = 1 << QUOTE_TICK_BITS;
pub const LEAN_DESCRIPTOR_SESSION: u32 = 1_347_371_569;

/// Stage-1 domain tag, ASCII `DBH1`; stage-2, ASCII `DBA1`. Both distinct from
/// the v1 book root's `DBGR`.
pub const HALF_DOMAIN_TAG: u32 = 1_145_194_545;
pub const ANCHOR_DOMAIN_TAG: u32 = 1_145_192_753;

/// Public-input layout. The four judge digests are NOT here: they are not
/// derivable in this AIR (they hash canonical JSON strings), so v4 refuses to
/// publish them as though the circuit had attested them. They are checked
/// host-side in [`verify_zk`] against a judge the verifier runs itself.
pub const ANCHOR_PI_BASE: usize = 12;
pub const VISIBILITY_PI: usize = ANCHOR_PI_BASE + DIGEST_WIDTH;
pub const SCALAR_PI_BASE: usize = VISIBILITY_PI + 1;

/// What the proof establishes about who sees the private book.
///
/// The second variant is intentionally representable so substitution tests can
/// prove that the v4 family refuses it. No producer in this module emits it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum ProverVisibilityGrade {
    VerifierShieldedProducerVisible = 1,
    NoSingleViewer = 2,
}

/// Exact public settlement scalars extracted from a Lean judge successor.
/// Every state value is strictly below `2^28`; `quote_tick` is below `2^20`.
/// Those explicit family bounds keep all five integer equations below the
/// BabyBear modulus, so field wraparound cannot masquerade as settlement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SettlementTransition {
    pub before_base_escrow: u32,
    pub after_base_escrow: u32,
    pub before_buyer_base_custody: u32,
    pub after_buyer_base_custody: u32,
    pub before_quote_escrow: u32,
    pub after_quote_escrow: u32,
    pub before_seller_quote_custody: u32,
    pub after_seller_quote_custody: u32,
    pub quote_tick: u32,
    pub quote_amount: u32,
}

impl SettlementTransition {
    const fn fields(self) -> [u32; SCALAR_COUNT] {
        [
            self.before_base_escrow,
            self.after_base_escrow,
            self.before_buyer_base_custody,
            self.after_buyer_base_custody,
            self.before_quote_escrow,
            self.after_quote_escrow,
            self.before_seller_quote_custody,
            self.after_seller_quote_custody,
            self.quote_tick,
            self.quote_amount,
        ]
    }

    fn validate(self, p_star: u32, v_star: u32) -> Result<(), String> {
        for (field, value) in self.fields().into_iter().enumerate() {
            if field != 8 && u64::from(value) >= STATE_VALUE_LIMIT {
                return Err(format!(
                    "settlement field {field}={value} exceeds v4 28-bit exact-integer family"
                ));
            }
        }
        if u64::from(self.quote_tick) >= QUOTE_TICK_LIMIT {
            return Err(format!(
                "quote tick {} exceeds v4 20-bit exact-integer family",
                self.quote_tick
            ));
        }
        let quote_amount = u64::from(self.quote_tick)
            .checked_mul(u64::from(p_star) + 1)
            .and_then(|value| value.checked_mul(u64::from(v_star)))
            .ok_or_else(|| "quote calculation overflowed u64".to_owned())?;
        if quote_amount != u64::from(self.quote_amount) {
            return Err("Lean judge settlement quote amount is internally inconsistent".to_owned());
        }
        if u64::from(self.after_base_escrow) + u64::from(v_star)
            != u64::from(self.before_base_escrow)
            || u64::from(self.before_buyer_base_custody) + u64::from(v_star)
                != u64::from(self.after_buyer_base_custody)
            || u64::from(self.after_quote_escrow) + quote_amount
                != u64::from(self.before_quote_escrow)
            || u64::from(self.before_seller_quote_custody) + quote_amount
                != u64::from(self.after_seller_quote_custody)
        {
            return Err("Lean judge settlement scalars violate the exact v4 transition".to_owned());
        }
        Ok(())
    }
}

/// Exact public statement verified by v4.
///
/// ⚑ The four judge digests are carried here and compared in [`verify_zk`]
/// against a judge the verifier runs itself. They are deliberately NOT part of
/// the proof's public input vector — see [`PublicStatement::as_felts`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub private: PrivatePublicStatement,
    pub input_digest: PoaReceiptDigest,
    pub successor_digest: PoaReceiptDigest,
    pub public_view_digest: PoaReceiptDigest,
    pub receipt_digest: PoaReceiptDigest,
    pub visibility: ProverVisibilityGrade,
    pub transition: SettlementTransition,
}

impl PublicStatement {
    fn validate_shape(self) -> Result<(), String> {
        if self.private.session != LEAN_DESCRIPTOR_SESSION {
            return Err(format!(
                "session {} is not Lean Dark Bazaar descriptor session {LEAN_DESCRIPTOR_SESSION}",
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
        if self.visibility != ProverVisibilityGrade::VerifierShieldedProducerVisible {
            return Err("v4 does not establish a no-single-viewer producer".to_owned());
        }
        self.transition
            .validate(self.private.p_star, self.private.v_star)
    }

    /// The two staged settlement-anchor absorbs, reproduced exactly as the
    /// Lean-emitted chip lookups force them.
    ///
    /// * stage 1, arity 16: `[HALF_DOMAIN_TAG, root₀..₇, scalar₀..₅, 0]`
    /// * stage 2, arity 16: `[ANCHOR_DOMAIN_TAG, half₀..₇, scalar₆..₉,
    ///   visibility, p*, V*]`
    ///
    /// ⚑ Full arity 16 is load-bearing twice over. The deployed chip's arity
    /// selector seeds all sixteen state lanes only at arity ∈ {7, 11, 16}, and
    /// the natural arity here — 12 — is not admitted by the chip AIR at all, so
    /// a site at that arity would have no satisfying assignment. The explicit
    /// zero pad in stage 1 is what makes the arity 16 rather than 15.
    fn anchor_lanes(self) -> ([BabyBear; DIGEST_WIDTH], [BabyBear; DIGEST_WIDTH]) {
        let fields = self.transition.fields();

        let mut half_preimage = Vec::with_capacity(16);
        half_preimage.push(BabyBear::new(HALF_DOMAIN_TAG));
        half_preimage.extend(self.private.order_root.map(BabyBear::new));
        half_preimage.extend(fields[..6].iter().copied().map(BabyBear::new));
        half_preimage.push(BabyBear::ZERO);
        let half = chip_absorb_all_lanes(half_preimage.len(), &half_preimage);

        let mut anchor_preimage = Vec::with_capacity(16);
        anchor_preimage.push(BabyBear::new(ANCHOR_DOMAIN_TAG));
        anchor_preimage.extend(half);
        anchor_preimage.extend(fields[6..].iter().copied().map(BabyBear::new));
        anchor_preimage.push(BabyBear::new(self.visibility as u32));
        anchor_preimage.push(BabyBear::new(self.private.p_star));
        anchor_preimage.push(BabyBear::new(self.private.v_star));
        let anchor = chip_absorb_all_lanes(anchor_preimage.len(), &anchor_preimage);

        (half, anchor)
    }

    /// The proof's public input vector: 31 felts.
    ///
    /// ⚑ **The four judge digests are not here, and that is the v4 repair.**
    /// V3 published all thirty-two of their lanes and no constraint of any kind
    /// named the columns they were pinned to — a verifier checking the STARK
    /// against those public inputs learned nothing whatsoever about them. They
    /// are hashes of canonical JSON strings
    /// (`DarkBazaarJudgeWire.digestString`), so no AIR over this four-row
    /// fixed-width trace can derive them; publishing them here would be a
    /// statement this circuit cannot make. What v4 publishes instead is the
    /// eight-lane settlement anchor, which the Lean-emitted chip lookups force
    /// to be the image of the book root, the clearing, the ten settlement
    /// scalars and the visibility grade.
    fn as_felts(self) -> [BabyBear; PUBLIC_INPUT_COUNT] {
        let mut public = [BabyBear::ZERO; PUBLIC_INPUT_COUNT];
        public[0] = BabyBear::new(self.private.session);
        public[1] = BabyBear::new(self.private.rule);
        for (lane, root) in self.private.order_root.into_iter().enumerate() {
            public[2 + lane] = BabyBear::new(root);
        }
        public[10] = BabyBear::new(self.private.p_star);
        public[11] = BabyBear::new(self.private.v_star);

        let (_half, anchor) = self.anchor_lanes();
        for (lane, value) in anchor.into_iter().enumerate() {
            public[ANCHOR_PI_BASE + lane] = value;
        }
        public[VISIBILITY_PI] = BabyBear::new(self.visibility as u32);
        for (field, value) in self.transition.fields().into_iter().enumerate() {
            public[SCALAR_PI_BASE + field] = BabyBear::new(value);
        }
        public
    }
}

/// Parsed projection of bytes returned by the Lean judge.
///
/// This type and its parser are deliberately private. A caller-authored JSON
/// string is data, not authorization; the only public route to one of these is
/// [`LeanJudgedSettlement::judge`], which invokes the linked Lean evaluator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LeanJudgeBinding {
    input_digest: PoaReceiptDigest,
    successor_digest: PoaReceiptDigest,
    public_view_digest: PoaReceiptDigest,
    receipt_digest: PoaReceiptDigest,
    private_book_commitment: PoaReceiptDigest,
    p_star: u32,
    v_star: u32,
    transition: SettlementTransition,
}

#[derive(Deserialize)]
struct JudgeOutputJson {
    format: String,
    input_digest: String,
    successor_digest: String,
    public_view_digest: String,
    receipt_digest: String,
    successor: SuccessorJson,
    public_view: PublicViewJson,
    receipt: ReceiptJson,
}

#[derive(Deserialize)]
struct SuccessorJson {
    policy: PublicPolicyJson,
    base_notes: Vec<NoteJson>,
    quote_notes: Vec<NoteJson>,
    buyer_base_custody: u64,
    seller_quote_custody: u64,
}

#[derive(Deserialize)]
struct NoteJson {
    amount: u64,
}

#[derive(Deserialize)]
struct PublicViewJson {
    spec: PublicSpecJson,
    private_book_commitment: String,
    output: ClearingJson,
    base_inputs: Vec<NoteJson>,
    quote_inputs: Vec<NoteJson>,
}

#[derive(Deserialize)]
struct PublicSpecJson {
    policy: PublicPolicyJson,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
struct PublicPolicyJson {
    quote_tick: u64,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
struct ClearingJson {
    bucket: u64,
    volume: u64,
}

#[derive(Deserialize)]
struct ReceiptJson {
    authorization: String,
    commitment: String,
    clearing: ClearingJson,
    buyer_base_custody: u64,
    seller_quote_custody: u64,
}

fn decode_lower_hex_digest(value: &str, label: &str) -> Result<PoaReceiptDigest, String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!(
            "{label} must be exactly 64 lowercase hexadecimal digits"
        ));
    }
    let mut bytes = [0u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let nibble = |byte: u8| -> u8 {
            if byte.is_ascii_digit() {
                byte - b'0'
            } else {
                byte - b'a' + 10
            }
        };
        bytes[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    PoaReceiptDigest::try_from_lean_bytes(bytes)
}

fn checked_sum_notes(notes: &[NoteJson], label: &str) -> Result<u64, String> {
    notes.iter().try_fold(0u64, |total, note| {
        total
            .checked_add(note.amount)
            .ok_or_else(|| format!("{label} note sum overflowed u64"))
    })
}

fn checked_u32(value: u64, label: &str) -> Result<u32, String> {
    u32::try_from(value).map_err(|_| format!("{label}={value} does not fit the v4 host integer"))
}

impl LeanJudgeBinding {
    fn parse(bytes: &str) -> Result<Self, String> {
        let output: JudgeOutputJson = serde_json::from_str(bytes)
            .map_err(|error| format!("Lean Dark Bazaar judge output decode failed: {error}"))?;
        if output.format != "POA-DARK-BAZAAR-OUT-1" {
            return Err("wrong Lean Dark Bazaar output format".to_owned());
        }
        if output.receipt.authorization != "DREGG-DARK-BAZAAR-N4-K4-POSEIDON2-V1" {
            return Err("wrong Lean Dark Bazaar receipt authorization".to_owned());
        }
        if output.receipt.clearing != output.public_view.output {
            return Err("Lean judge receipt and public-view clearing disagree".to_owned());
        }
        if output.receipt.commitment != output.public_view.private_book_commitment {
            return Err("Lean judge receipt and public-view commitment disagree".to_owned());
        }
        if output.successor.policy != output.public_view.spec.policy {
            return Err("Lean judge successor and public-view policy disagree".to_owned());
        }
        if output.receipt.buyer_base_custody != output.successor.buyer_base_custody
            || output.receipt.seller_quote_custody != output.successor.seller_quote_custody
        {
            return Err("Lean judge receipt and successor custody disagree".to_owned());
        }

        let after_base = checked_sum_notes(&output.successor.base_notes, "base escrow")?;
        let after_quote = checked_sum_notes(&output.successor.quote_notes, "quote escrow")?;
        let consumed_base = checked_sum_notes(&output.public_view.base_inputs, "base input")?;
        let consumed_quote = checked_sum_notes(&output.public_view.quote_inputs, "quote input")?;
        let v_star = output.public_view.output.volume;
        let p_star = output.public_view.output.bucket;
        let quote_amount = output
            .public_view
            .spec
            .policy
            .quote_tick
            .checked_mul(
                p_star
                    .checked_add(1)
                    .ok_or_else(|| "bucket overflow".to_owned())?,
            )
            .and_then(|value| value.checked_mul(v_star))
            .ok_or_else(|| "Lean judge quote calculation overflowed u64".to_owned())?;
        if consumed_base != v_star || consumed_quote != quote_amount {
            return Err(
                "Lean judge public asset inputs do not exactly fund the clearing".to_owned(),
            );
        }
        let before_base = after_base
            .checked_add(consumed_base)
            .ok_or_else(|| "base escrow predecessor overflowed u64".to_owned())?;
        let before_quote = after_quote
            .checked_add(consumed_quote)
            .ok_or_else(|| "quote escrow predecessor overflowed u64".to_owned())?;
        let before_buyer = output
            .successor
            .buyer_base_custody
            .checked_sub(v_star)
            .ok_or_else(|| "buyer custody successor is below the cleared base amount".to_owned())?;
        let before_seller = output
            .successor
            .seller_quote_custody
            .checked_sub(quote_amount)
            .ok_or_else(|| {
                "seller custody successor is below the cleared quote amount".to_owned()
            })?;

        let transition = SettlementTransition {
            before_base_escrow: checked_u32(before_base, "before base escrow")?,
            after_base_escrow: checked_u32(after_base, "after base escrow")?,
            before_buyer_base_custody: checked_u32(before_buyer, "before buyer custody")?,
            after_buyer_base_custody: checked_u32(
                output.successor.buyer_base_custody,
                "after buyer custody",
            )?,
            before_quote_escrow: checked_u32(before_quote, "before quote escrow")?,
            after_quote_escrow: checked_u32(after_quote, "after quote escrow")?,
            before_seller_quote_custody: checked_u32(before_seller, "before seller custody")?,
            after_seller_quote_custody: checked_u32(
                output.successor.seller_quote_custody,
                "after seller custody",
            )?,
            quote_tick: checked_u32(output.public_view.spec.policy.quote_tick, "quote tick")?,
            quote_amount: checked_u32(quote_amount, "quote amount")?,
        };
        let p_star = checked_u32(p_star, "p*")?;
        let v_star = checked_u32(v_star, "V*")?;
        transition.validate(p_star, v_star)?;

        Ok(Self {
            input_digest: decode_lower_hex_digest(&output.input_digest, "input digest")?,
            successor_digest: decode_lower_hex_digest(
                &output.successor_digest,
                "successor digest",
            )?,
            public_view_digest: decode_lower_hex_digest(
                &output.public_view_digest,
                "public-view digest",
            )?,
            receipt_digest: decode_lower_hex_digest(&output.receipt_digest, "receipt digest")?,
            private_book_commitment: decode_lower_hex_digest(
                &output.public_view.private_book_commitment,
                "private-book commitment",
            )?,
            p_star,
            v_star,
            transition,
        })
    }

    fn statement(self, private: PrivatePublicStatement) -> Result<PublicStatement, String> {
        let commitment = PoaReceiptDigest::try_from_lean_bytes(lanes_to_bytes(private.order_root))?;
        if commitment != self.private_book_commitment {
            return Err("private proof root differs from Lean judge public view".to_owned());
        }
        if private.p_star != self.p_star || private.v_star != self.v_star {
            return Err("private proof clearing differs from Lean judge public view".to_owned());
        }
        let statement = PublicStatement {
            private,
            input_digest: self.input_digest,
            successor_digest: self.successor_digest,
            public_view_digest: self.public_view_digest,
            receipt_digest: self.receipt_digest,
            visibility: ProverVisibilityGrade::VerifierShieldedProducerVisible,
            transition: self.transition,
        };
        statement.validate_shape()?;
        Ok(statement)
    }
}

/// Opaque evidence that the linked Lean evaluator accepted one canonical Dark
/// Bazaar input and returned the settlement projection held here.
///
/// The field is private, the type has no decoding or raw-output constructor,
/// and neither proving nor verification accepts judge-output text. Validators
/// mint their own value by running Lean over the canonical input they received.
pub struct LeanJudgedSettlement {
    binding: LeanJudgeBinding,
}

impl LeanJudgedSettlement {
    /// Run the linked Lean judge. Semantic refusal is distinct from a missing
    /// evaluator/export, but both fail closed before the proof system is called.
    pub fn judge(canonical_input: &str) -> Result<Self, String> {
        if !poa_dark_bazaar_judge_available() {
            return Err("linked Lean Dark Bazaar judge is unavailable; settlement refuses".into());
        }
        match judge_poa_dark_bazaar(canonical_input)? {
            PoaDarkBazaarVerdict::Accepted(output) => Ok(Self {
                binding: LeanJudgeBinding::parse(&output)?,
            }),
            PoaDarkBazaarVerdict::Rejected => {
                Err("Lean Dark Bazaar judge rejected the canonical input".into())
            }
        }
    }
}

fn lanes_to_bytes(lanes: [u32; DIGEST_WIDTH]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (lane, value) in lanes.into_iter().enumerate() {
        bytes[4 * lane..4 * lane + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

pub struct DarkBazaarPrivatePoaSettlementZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl DarkBazaarPrivatePoaSettlementZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private PoA settlement proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private PoA settlement proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DARK_BAZAAR_PRIVATE_POA_SETTLEMENT_DESCRIPTOR_JSON)?;
    if descriptor.name != "dark-bazaar-private-poa-settlement-n4k4::anchored-v4"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("PoA Dark Bazaar v4 emitted descriptor shape drifted".to_owned());
    }
    Ok(descriptor)
}

fn set_bits(row: &mut [BabyBear], value: u32, bits: usize, base: usize) {
    for bit in 0..bits {
        row[base + bit] = BabyBear::new((value >> bit) & 1);
    }
}

/// Extend a complete v1 row with the v4 settlement columns: the two staged
/// anchor absorbs, the visibility grade, the ten scalars and their range bits.
///
/// Split out from [`trace_and_public`] so the trace can be built from a
/// statement alone. The AIR-level falsifier is a claim about the descriptor and
/// must not need the Lean judge FFI to make it.
fn extend_row_with_settlement(
    row: &mut Vec<BabyBear>,
    public: PublicStatement,
) -> Result<(), String> {
    if row.len() != V1_TRACE_WIDTH {
        return Err("v1 row width drifted before v4 extension".to_owned());
    }

    let (half, anchor) = public.anchor_lanes();
    row.extend(half);
    row.extend(anchor);
    row.push(BabyBear::new(public.visibility as u32));
    let fields = public.transition.fields();
    row.extend(fields.into_iter().map(BabyBear::new));
    row.resize(TRACE_WIDTH, BabyBear::ZERO);

    // Nine 28-bit targets: the eight before/after state values, then quote amount.
    for (target, field) in fields[..8]
        .iter()
        .copied()
        .chain(core::iter::once(fields[9]))
        .enumerate()
    {
        set_bits(
            row,
            field,
            STATE_VALUE_BITS,
            RANGE_BIT_BASE + target * STATE_VALUE_BITS,
        );
    }
    set_bits(
        row,
        fields[8],
        QUOTE_TICK_BITS,
        RANGE_BIT_BASE + 9 * STATE_VALUE_BITS,
    );
    if row.len() != TRACE_WIDTH {
        return Err("v4 settlement columns did not extend the trace exactly".to_owned());
    }
    Ok(())
}

fn trace_and_public(
    witness: &PrivateBookWitness,
    judged: &LeanJudgedSettlement,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (mut row, private) =
        crate::dark_bazaar_private::build_row(LEAN_DESCRIPTOR_SESSION, witness)?;
    let public = judged.binding.statement(private)?;
    extend_row_with_settlement(&mut row, public)?;

    let descriptor = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((descriptor, trace, public))
}

/// The trace for a statement the caller already holds, without consulting the
/// Lean judge. The `private` projection is re-derived from the witness and must
/// agree, so this cannot mint a trace for a book the witness does not open.
#[cfg(test)]
fn trace_for_statement(
    witness: &PrivateBookWitness,
    public: PublicStatement,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>), String> {
    let (mut row, private) =
        crate::dark_bazaar_private::build_row(LEAN_DESCRIPTOR_SESSION, witness)?;
    if private != public.private {
        return Err("witness does not open this statement's v1 public projection".to_owned());
    }
    public.validate_shape()?;
    extend_row_with_settlement(&mut row, public)?;
    let descriptor = descriptor()?;
    Ok((descriptor, vec![row.clone(), row.clone(), row.clone(), row]))
}

/// Produce v4 only from an opaque Lean-accepted settlement joined to the exact
/// hidden-book root and clearing result.
pub fn prove_zk(
    witness: &PrivateBookWitness,
    judged: &LeanJudgedSettlement,
) -> Result<(DarkBazaarPrivatePoaSettlementZkProof, PublicStatement), String> {
    let (descriptor, trace, public) = trace_and_public(witness, judged)?;
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
    Ok((DarkBazaarPrivatePoaSettlementZkProof { proof }, public))
}

/// Verify against an independently minted Lean judgement. All four judge
/// digests, the private-book commitment, clearing output, exact public scalar
/// transition, and typed visibility grade are compared before proof checking.
///
/// ⚑ The digest comparison here is the ONLY thing that ties this proof to a
/// specific judge output, and it is a HOST check against a judge this caller
/// ran — not something the proof attests. That was true under v3 as well; the
/// difference is that v3 also published the digests as public inputs, so a
/// reader of the proof alone could believe the circuit had checked them.
pub fn verify_zk(
    proof: &DarkBazaarPrivatePoaSettlementZkProof,
    public: PublicStatement,
    expected: &LeanJudgedSettlement,
) -> Result<(), String> {
    public.validate_shape()?;
    let expected_statement = expected.binding.statement(public.private)?;
    if public != expected_statement {
        return Err(
            "proof statement differs from independently executed Lean judgement".to_owned(),
        );
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

    const LEAN_INPUT_WITH_NEWLINE: &str =
        include_str!("../../dregg-lean-ffi/tests/fixtures/poa-dark-bazaar-input-v1.json");
    const LEAN_OUTPUT_WITH_NEWLINE: &str =
        include_str!("../../dregg-lean-ffi/tests/fixtures/poa-dark-bazaar-output-v1.json");

    fn lean_input() -> &'static str {
        LEAN_INPUT_WITH_NEWLINE
            .strip_suffix('\n')
            .expect("fixture has one trailing newline")
    }

    fn lean_output() -> &'static str {
        LEAN_OUTPUT_WITH_NEWLINE
            .strip_suffix('\n')
            .expect("fixture has one trailing newline")
    }

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

    fn judged() -> LeanJudgedSettlement {
        LeanJudgedSettlement::judge(lean_input()).expect("linked Lean judge accepts fixture")
    }

    #[test]
    fn emitted_descriptor_pins_the_complete_v4_public_surface() {
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
        for (pi, (row, _col, actual_pi)) in pins.into_iter().enumerate() {
            assert_eq!(row, VmRow::First);
            assert_eq!(actual_pi, pi);
        }
    }

    #[test]
    fn lean_judge_binding_derives_exact_custody_and_conservation() {
        let binding = LeanJudgeBinding::parse(lean_output()).expect("Lean fixture parses");
        assert_eq!(binding.p_star, 1);
        assert_eq!(binding.v_star, 13);
        assert_eq!(binding.transition.quote_tick, 2);
        assert_eq!(binding.transition.quote_amount, 52);
        assert_eq!(binding.transition.before_base_escrow, 13);
        assert_eq!(binding.transition.after_base_escrow, 0);
        assert_eq!(binding.transition.before_quote_escrow, 52);
        assert_eq!(binding.transition.after_quote_escrow, 0);
        assert_eq!(
            binding.transition.after_base_escrow + binding.transition.after_buyer_base_custody,
            binding.transition.before_base_escrow + binding.transition.before_buyer_base_custody
        );
        assert_eq!(
            binding.transition.after_quote_escrow + binding.transition.after_seller_quote_custody,
            binding.transition.before_quote_escrow + binding.transition.before_seller_quote_custody
        );
    }

    /// ⚠ The four digest substitutions below are refused by the HOST comparison
    /// in `verify_zk`, not by the AIR — they are not public inputs in v4. That
    /// was already the only thing refusing them in v3; v3 merely also published
    /// them. Read this test as covering the host check, and read
    /// `a_forged_settlement_anchor_that_satisfies_every_gate_is_refused` for
    /// what the circuit itself now refuses.
    #[test]
    fn v4_proves_and_refuses_every_public_settlement_substitution() {
        let judged = judged();
        let (proof, public) = prove_zk(&witness(), &judged).expect("v4 proof mints");
        verify_zk(&proof, public, &judged).expect("exact Lean settlement verifies");

        let zero_digest = PoaReceiptDigest::try_from_lean_bytes([0; 32]).unwrap();
        for substituted in [
            PublicStatement {
                input_digest: zero_digest,
                ..public
            },
            PublicStatement {
                successor_digest: zero_digest,
                ..public
            },
            PublicStatement {
                public_view_digest: zero_digest,
                ..public
            },
            PublicStatement {
                receipt_digest: zero_digest,
                ..public
            },
        ] {
            assert!(verify_zk(&proof, substituted, &judged).is_err());
        }

        let mut claimed_house_blind = public;
        claimed_house_blind.visibility = ProverVisibilityGrade::NoSingleViewer;
        assert!(verify_zk(&proof, claimed_house_blind, &judged).is_err());

        for field in 0..SCALAR_COUNT {
            let mut caller_authored = public;
            match field {
                0 => caller_authored.transition.before_base_escrow += 1,
                1 => caller_authored.transition.after_base_escrow += 1,
                2 => caller_authored.transition.before_buyer_base_custody += 1,
                3 => caller_authored.transition.after_buyer_base_custody += 1,
                4 => caller_authored.transition.before_quote_escrow += 1,
                5 => caller_authored.transition.after_quote_escrow += 1,
                6 => caller_authored.transition.before_seller_quote_custody += 1,
                7 => caller_authored.transition.after_seller_quote_custody += 1,
                8 => caller_authored.transition.quote_tick += 1,
                9 => caller_authored.transition.quote_amount += 1,
                _ => unreachable!(),
            }
            assert!(verify_zk(&proof, caller_authored, &judged).is_err());
        }
    }

    #[test]
    fn public_ingress_runs_lean_and_has_no_output_text_constructor() {
        LeanJudgedSettlement::judge(lean_input()).expect("canonical input is authorized by Lean");
        let forged = lean_input().replacen(
            "\"output\":{\"bucket\":1,\"volume\":13}",
            "\"output\":{\"bucket\":2,\"volume\":13}",
            1,
        );
        assert!(LeanJudgedSettlement::judge(&forged).is_err());
        assert!(LeanJudgedSettlement::judge(&format!("{}\n", lean_input())).is_err());
    }

    /// A complete, self-consistent v4 statement built from the witness alone.
    ///
    /// ⚑ No Lean judge is consulted, and it does not need to be: the four judge
    /// digests are no longer public inputs, so they cannot reach the proof. That
    /// is exactly the v4 property under test, and it makes the falsifier below a
    /// claim about the AIR rather than about the FFI. Everything the AIR does
    /// constrain is derived here from the witness's own clearing.
    fn statement_from_witness(witness: &PrivateBookWitness) -> PublicStatement {
        let (_row, private) =
            crate::dark_bazaar_private::build_row(LEAN_DESCRIPTOR_SESSION, witness)
                .expect("the fixed private book builds its v1 row");
        let quote_tick = 2u32;
        let quote_amount = quote_tick * (private.p_star + 1) * private.v_star;
        let unused = PoaReceiptDigest::try_from_lean_bytes([0; 32]).expect("canonical zero digest");
        PublicStatement {
            private,
            input_digest: unused,
            successor_digest: unused,
            public_view_digest: unused,
            receipt_digest: unused,
            visibility: ProverVisibilityGrade::VerifierShieldedProducerVisible,
            transition: SettlementTransition {
                before_base_escrow: private.v_star,
                after_base_escrow: 0,
                before_buyer_base_custody: 0,
                after_buyer_base_custody: private.v_star,
                before_quote_escrow: quote_amount,
                after_quote_escrow: 0,
                before_seller_quote_custody: 0,
                after_seller_quote_custody: quote_amount,
                quote_tick,
                quote_amount,
            },
        }
    }

    /// ⚑⚑ **THE FORGERY V3 COULD NOT REFUSE, REPLAYED AGAINST V4'S ANCHOR.**
    ///
    /// Under v3 this attack succeeded outright. A prover kept every v1 book
    /// column, every settlement scalar, every range bit and the visibility
    /// grade — so every gate body, every boundary body and every lookup in the
    /// descriptor was satisfied — wrote arbitrary values into the thirty-two
    /// judge-digest columns, published them, and the STARK verified. The proof
    /// then read as a settlement "about" a judge output that never existed.
    ///
    /// V4 publishes the settlement anchor instead, and the anchor is a chip
    /// lookup output. This test replays the identical attack shape: satisfy
    /// every gate, keep the `pi_binding` honest by publishing exactly what the
    /// column holds, and move only the published value. It must be REFUSED —
    /// the prover re-derives the chip table row from the genuine permutation
    /// over the tuple's INPUT block, so a forged output column makes the LogUp
    /// bus fail to balance.
    ///
    /// ⚠ The forgery targets ANCHOR lane 0 on purpose. `fill_chip_lanes`
    /// rewrites lanes 1..7 of every chip output from the descriptor before
    /// proving, so a forgery there would be silently corrected and this test
    /// would go green for the wrong reason. Lane 0 is producer-owned. The
    /// `assert_ne!` is there because a tamper that moves a value onto itself
    /// proves nothing at all.
    #[test]
    fn a_forged_settlement_anchor_that_satisfies_every_gate_is_refused() {
        let witness = witness();
        let public = statement_from_witness(&witness);
        let (descriptor, honest_trace) =
            trace_for_statement(&witness, public).expect("v4 honest trace builds");
        let honest_public = public.as_felts();
        let config = create_zk_config();

        let honest_proof = prove_vm_descriptor2_for_config(
            &descriptor,
            &honest_trace,
            &honest_public,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &config,
        )
        .expect("the honest v4 settlement proves");
        verify_vm_descriptor2_with_config(&descriptor, &honest_proof, &honest_public, &config)
            .expect("the honest v4 settlement verifies");

        let honest_lane = honest_public[ANCHOR_PI_BASE];
        let forged_lane = BabyBear::new(honest_lane.as_u32() ^ 1);
        assert_ne!(
            forged_lane, honest_lane,
            "the tamper must actually move the published anchor, or this test proves nothing"
        );

        let mut forged_trace = honest_trace.clone();
        for row in forged_trace.iter_mut() {
            row[ANCHOR_BASE] = forged_lane;
        }
        let mut forged_public = honest_public;
        forged_public[ANCHOR_PI_BASE] = forged_lane;

        let refusal = match prove_vm_descriptor2_for_config(
            &descriptor,
            &forged_trace,
            &forged_public,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &config,
        ) {
            Err(why) => why,
            Ok(forged_proof) => match verify_vm_descriptor2_with_config(
                &descriptor,
                &forged_proof,
                &forged_public,
                &config,
            ) {
                Err(why) => why,
                Ok(()) => panic!(
                    "a forged settlement anchor VERIFIED — the published anchor is not bound, \
                     which is the v3 defect this family was rebuilt to close"
                ),
            },
        };

        // ⚑ NAME THE MECHANISM, do not merely observe a refusal. Measured:
        // `IR v2 batch self-verify failed: LookupError("GlobalCumulativeMismatch(None): ir2_p2")`
        // — the Poseidon2 chip bus. The prover re-derives every chip table row's
        // output lanes from the genuine permutation over the tuple's input block,
        // so the forged output column is sent on the bus and matched by no row.
        // Asserting the mechanism means a future change that refuses this for
        // some UNRELATED reason cannot keep the test green while the binding
        // silently rots.
        assert!(
            refusal.contains("ir2_p2") || refusal.contains("Lookup"),
            "the forged anchor must be refused BY THE CHIP BUS that derives it, \
             not incidentally; got: {refusal}"
        );
    }

    /// The anchor is a function of the settlement, not a label beside it:
    /// moving any one of the ten scalars moves the published anchor.
    #[test]
    fn every_settlement_scalar_moves_the_published_anchor() {
        let public = statement_from_witness(&witness());
        let (_half, honest_anchor) = public.anchor_lanes();

        for field in 0..SCALAR_COUNT {
            let mut moved = public;
            match field {
                0 => moved.transition.before_base_escrow += 1,
                1 => moved.transition.after_base_escrow += 1,
                2 => moved.transition.before_buyer_base_custody += 1,
                3 => moved.transition.after_buyer_base_custody += 1,
                4 => moved.transition.before_quote_escrow += 1,
                5 => moved.transition.after_quote_escrow += 1,
                6 => moved.transition.before_seller_quote_custody += 1,
                7 => moved.transition.after_seller_quote_custody += 1,
                8 => moved.transition.quote_tick += 1,
                9 => moved.transition.quote_amount += 1,
                _ => unreachable!(),
            }
            let (_half, moved_anchor) = moved.anchor_lanes();
            assert_ne!(
                moved_anchor, honest_anchor,
                "settlement scalar {field} does not reach the published anchor"
            );
        }

        let mut regraded = public;
        regraded.visibility = ProverVisibilityGrade::NoSingleViewer;
        let (_half, regraded_anchor) = regraded.anchor_lanes();
        assert_ne!(
            regraded_anchor, honest_anchor,
            "the visibility grade does not reach the published anchor"
        );
    }

    #[test]
    fn prover_refuses_another_book_for_the_same_lean_settlement() {
        let judged = judged();
        let mut another = witness();
        another.orders[0] = PrivateOrder::bid(11, 2);
        let error = match prove_zk(&another, &judged) {
            Ok(_) => panic!("another private book must not authorize the Lean settlement"),
            Err(error) => error,
        };
        assert!(error.contains("root differs") || error.contains("clearing differs"));
    }
}
