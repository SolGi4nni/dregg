//! `mina_pickles`: **the byte-exact decoder for a Mina block's Pickles Wrap proof**
//! (`Mina_base.Proof.Stable.V2`, the `protocolStateProof` GraphQL serves as base64url
//! binprot), and the SHAPE projection the verified gate decides over.
//!
//! # Why this exists
//!
//! Until 2026-07-29 [`crate::mina_observer`] passed a compile-time constant
//! `NEUTRAL_PICKLES_OK = true` for the Pickles conjunct of the Mina light-client
//! gate, because `bestChain` did not fetch `protocolStateProof` and nothing here
//! could look at a proof. That constant is retired. The observer now fetches every
//! block's proof and drives it through this decoder before the gate runs.
//!
//! # ⚑ WHAT THIS MODULE IS, AND WHAT IT DELIBERATELY IS NOT
//!
//! **It is a CODEC.** It decodes the binprot object, refuses every deviation, and
//! projects the LENGTHS/COUNTS the Kimchi verifier's preamble asserts on. It does
//! **no field arithmetic and no group arithmetic**, and that is a house law, not an
//! omission: the on-curve predicate `y² = x³ + 5`, the sponge, the linearization and
//! the IPA relation are AIR/constraint content and are authored in Lean
//! (`Dregg2.Circuit.Emit.MinaWrapGroupGate`, `…MinaWrapOpeningGate`, `…PastaIpaFold`).
//! Rust hand-writing a Pasta field would be exactly the drift those modules exist to
//! prevent. The single arithmetic-shaped thing done here is a 32-byte **comparison**
//! against the field modulus — the same canonicality check
//! [`crate::mina_observer::decode_state_hash`] already does on a state hash, and for
//! the same reason: a coordinate `x + p` is a different byte string denoting the same
//! field element, so admitting it would make the decode non-injective.
//!
//! # What a successful decode establishes about the bytes
//!
//! * they are valid **base64url** (no padding) — GraphQL's transport form;
//! * they are a **total, exact-fit** `Mina_base.Proof.Stable.V2`: every nested
//!   `PaddedSeq` terminator is present, every `Option` tag is `0x00`/`0x01`, every
//!   `bool` is `0`/`1`, every bounded `ArrayN16` is within its cap, and the decoder
//!   consumes **every** byte — a single trailing byte is a REFUSAL;
//! * every binprot integer is in its **canonical** encoding (`0x00..0x7f` inline,
//!   `0xfe`/`0xfd`/`0xfc` only when the value needs the width). The reference reader
//!   (`binprot-rs`) accepts non-canonical widths; this one does not, because two byte
//!   strings for one proof is a malleability an endpoint chooses;
//! * every field element is **canonical** for the field it lives in — Pallas
//!   coordinates and the Wrap scalars against the two Pasta moduli.
//!
//! None of that is "the proof verifies". It is the preamble, and the preamble is the
//! part a light client can run per block without the verifier index, the SRS, or an
//! hour of kernel time. See `mina_observer`'s per-step table for where the line is.

/// The Pallas BASE field modulus `p` — the coordinate field of every commitment in a
/// **Wrap** proof (`0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001`).
/// Big-endian, for comparison against a big-endian rendering of the decoded element.
const PALLAS_BASE_MODULUS_BE: [u8; 32] = [
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x22, 0x46, 0x98, 0xfc, 0x09, 0x4c, 0xf9, 0x1b, 0x99, 0x2d, 0x30, 0xed, 0x00, 0x00, 0x00, 0x01,
];

/// The Pallas SCALAR field modulus `q` (= the Vesta base field) — the field the Wrap
/// proof's evaluations and IPA scalars live in, and the coordinate field of the
/// Step-side accumulator commitment the statement carries
/// (`0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001`).
const PALLAS_SCALAR_MODULUS_BE: [u8; 32] = [
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x22, 0x46, 0x98, 0xfc, 0x09, 0x94, 0xa8, 0xdd, 0x8c, 0x46, 0xeb, 0x21, 0x00, 0x00, 0x00, 0x01,
];

/// Why a `protocolStateProof` was refused. Every variant is a REFUSAL — this type has
/// no "probably fine" arm, and the observer maps all of them to a settlement refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrapProofError {
    /// Byte offset into the binprot stream where the refusal happened (`0` for a
    /// base64 failure).
    pub at: usize,
    /// What was wrong.
    pub reason: String,
}

impl std::fmt::Display for WrapProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "at binprot offset {}: {}", self.at, self.reason)
    }
}

/// **The shape of a decoded Wrap proof** — the counts `to_batch`'s preamble asserts on
/// (`verifier.rs:173-177, 259-266, 810-830`), which is exactly the argument list of the
/// Lean-authored decision `Dregg2.Circuit.Emit.KimchiVerify.shapeOkRec`.
///
/// ⚑ `public_len` is NOT here, and its absence is the finding, not an oversight: the
/// wire proof does not carry the public input. `messages_for_next_step_proof.app_state`
/// is `()` on the wire — the verifier reconstructs the 40-element public input from the
/// BLOCK, using the verification key's `dlog_plonk_index`. So the public length is a
/// property of the pinned verifier index, and the observer supplies it from
/// [`MinaWrapIndexParams`], where it is visibly TRUSTED CONFIG.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WrapProofShape {
    /// `messages_for_next_step_proof.challenge_polynomial_commitments.len()` — the
    /// number of previous proofs this Wrap proof carries accumulators for. This is the
    /// `prev_challenges` `verifier.rs:810-813` compares against the verifier index.
    /// **Two** on a real Mina block; the old `shapeOk` froze it at zero and therefore
    /// REFUSED Mina (`PicklesRecursion.wrap_prev_challenges_admitted`).
    pub prev_challenges: usize,
    /// `messages_for_next_step_proof.old_bulletproof_challenges.len()` — must agree
    /// with `prev_challenges`; a proof exhibiting commitments without the matching
    /// challenge vectors (or vice versa) is malformed.
    pub prev_challenge_vectors: usize,
    /// `commitments.w_comm.len()` — the 15 witness-column commitments.
    pub w_comm: usize,
    /// `commitments.t_comm.len()` — the quotient chunks, `≤ 7 · chunk_size`.
    pub t_comm: usize,
    /// `evaluations.s.len()` — the `PERMUTS - 1 = 6` σ evaluations.
    pub s_evals: usize,
    /// `evaluations.coefficients.len()` — the 15 coefficient columns.
    pub coefficients: usize,
    /// `bulletproof.lr.len()` — the IPA round count `k = log₂ max_poly_size`, **15**
    /// for the devnet blockchain Wrap index (`SideShape.rounds`).
    pub ipa_rounds: usize,
    /// `statement.proof_state.deferred_values.branch_data.proofs_verified` (0/1/2).
    /// ⚑ This describes the **Step** side, not the Wrap index — the real devnet block
    /// carries `{proofs_verified: N2, domain_log2: 16}` while the Wrap VK's own domain
    /// is `2^14`. Kept separate from `prev_challenges` on purpose; conflating them is
    /// the error `docs/MINA-REAL-BLOCK-GATE.md` §4.2 records.
    pub branch_proofs_verified: u8,
    /// `…branch_data.domain_log2` — the Step domain, `16` on the real devnet block.
    pub branch_domain_log2: u8,
    /// How many field elements were canonicality-checked while decoding. Reported so a
    /// caller can assert the check was not vacuous: a decoder that silently checked
    /// nothing would report `0` here and the observer's tests refuse that.
    pub field_elements_checked: usize,

    // ── the CHAIN projection: what this proof SAYS ABOUT ITS PARENT'S PROOF ──────────
    //
    // ⚑ This is the proof↔proof binding, and it is the reason the four fields below are
    // extracted rather than merely walked past. See `WrapProofShape`'s note above about
    // `public_len`: the block is NOT in the proof, so a Wrap proof cannot be tied to its own
    // header from its bytes. But it IS tied to its PARENT'S PROOF, because Pickles recursion
    // makes block N's Step proof verify block N−1's Wrap proof, and the accumulator it carries
    // for that verification is literally block N−1's own IPA commitment.
    //
    // MEASURED on 40 consecutive real Mina devnet blocks (539761…539800, fetched
    // 2026-07-29 from `api.minascan.io`, 39 adjacent pairs): `acc0 == parent.sg` on 39/39 and
    // `acc0_challenges == parent.bp_challenges` on 39/39, with 40 distinct `sg` values, zero
    // self-references (`acc0 != sg` on every block), and zero NON-adjacent coincidences.
    /// `bulletproof.challenge_polynomial_commitment` — **this proof's own IPA accumulator**
    /// `sg`, in Pallas's base field. The value the NEXT block's proof must name.
    pub sg: Point,
    /// `statement.messages_for_next_step_proof.challenge_polynomial_commitments[0]` — **the
    /// accumulator of the proof this one's Step recursion verified**, i.e. the parent block's
    /// `sg`. All-zero when the proof carries no accumulator at all (`prev_challenges = 0`),
    /// which the verified chain gate refuses: `(0, 0)` is not on `y² = x³ + 5`.
    ///
    /// Index `[1]` is deliberately NOT projected — it is the transaction-SNARK accumulator, and
    /// it is stable across many blocks (4 distinct values over the measured 40), so it carries
    /// no positional information.
    pub acc0: Point,
    /// `statement.proof_state.deferred_values.bulletproof_challenges` — **this proof's own** 16
    /// IPA challenges, the second half of what the next block's proof must name.
    pub bp_challenges: [u128; 16],
    /// `statement.messages_for_next_step_proof.old_bulletproof_challenges[0]` — the 16
    /// challenges of the proof this one's Step recursion verified. All-zero when absent.
    pub acc0_challenges: [u128; 16],
}

/// **The pinned Wrap verifier-index parameters** the decoded shape is compared against.
///
/// ⚑ TRUSTED CONFIG, and named as such. Nothing in this crate derives these from the
/// chain; they are the declared counts of openmina's embedded devnet **blockchain**
/// verifier index, which `metatheory/fixtures/pickles-extractors` loads and prints
/// (`public=40 prev_challenges=2 domain=2^14 max_poly_size=2^15 zk_rows=3`). Modelling
/// the Wrap VK itself is P8/P9 and is not started.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MinaWrapIndexParams {
    /// `verifier_index.prev_challenges` — **2** for a Pickles Wrap index.
    pub prev_challenges: usize,
    /// The public-input length the index declares — **40**. Not on the wire; see
    /// [`WrapProofShape`].
    pub public_len: usize,
    /// `chunk_size` — **1**, because the Wrap domain `2^14` is below the SRS `2^15`.
    pub chunk_size: usize,
    /// The IPA round count `log₂ max_poly_size` — **15**.
    pub ipa_rounds: usize,
}

impl MinaWrapIndexParams {
    /// The devnet blockchain Wrap index as openmina's `BlockVerifier::make()` reports
    /// it. Mainnet is deliberately absent: openmina at HEAD cannot load the mainnet
    /// verifier index at all (stale serde format — `BlockVerifier::make()` panics), so
    /// there is no measured mainnet parameter set to pin and inventing one would be a
    /// guess wearing a constant's clothes.
    pub const DEVNET_BLOCKCHAIN: Self = Self {
        prev_challenges: 2,
        public_len: 40,
        chunk_size: 1,
        ipa_rounds: 15,
    };
}

// ===========================================================================
// binprot reader — total, canonical, exact-fit
// ===========================================================================

struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn err<T>(&self, reason: impl Into<String>) -> Result<T, WrapProofError> {
        Err(WrapProofError {
            at: self.i,
            reason: reason.into(),
        })
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], WrapProofError> {
        if self.i + n > self.b.len() {
            return self.err(format!(
                "truncated: need {n} more bytes, {} remain",
                self.b.len() - self.i
            ));
        }
        let s = &self.b[self.i..self.i + n];
        self.i += n;
        Ok(s)
    }

    fn u8(&mut self) -> Result<u8, WrapProofError> {
        Ok(self.take(1)?[0])
    }

    /// binprot `Nat0` (list/array lengths), CANONICAL only.
    fn nat0(&mut self) -> Result<u64, WrapProofError> {
        let c = self.u8()?;
        match c {
            0x00..=0x7f => Ok(u64::from(c)),
            0xfe => {
                let v = u64::from(u16::from_le_bytes(self.take(2)?.try_into().unwrap()));
                if v < 0x80 {
                    return self.err("non-canonical Nat0: 16-bit width for a 7-bit value");
                }
                Ok(v)
            }
            0xfd => {
                let v = u64::from(u32::from_le_bytes(self.take(4)?.try_into().unwrap()));
                if v < 0x1_0000 {
                    return self.err("non-canonical Nat0: 32-bit width for a 16-bit value");
                }
                Ok(v)
            }
            0xfc => {
                let v = u64::from_le_bytes(self.take(8)?.try_into().unwrap());
                if v < 0x1_0000_0000 {
                    return self.err("non-canonical Nat0: 64-bit width for a 32-bit value");
                }
                Ok(v)
            }
            other => self.err(format!("invalid Nat0 code 0x{other:02x}")),
        }
    }

    /// binprot signed integer, CANONICAL only. `Hex64` limbs are written through this
    /// (`Number<u64>` writes `self.0 as i64`), so a limb with the top bit set arrives
    /// as `0xfc` + 8 bytes and a small limb as a single byte.
    fn int(&mut self) -> Result<i64, WrapProofError> {
        let c = self.u8()?;
        match c {
            0x00..=0x7f => Ok(i64::from(c)),
            0xff => {
                let v = i64::from(self.take(1)?[0] as i8);
                if v >= 0 {
                    return self.err("non-canonical int: NEG_INT8 encoding a non-negative value");
                }
                Ok(v)
            }
            0xfe => {
                let v = i64::from(i16::from_le_bytes(self.take(2)?.try_into().unwrap()));
                // Canonical only when the value does NOT fit either 1-byte form
                // (`0x00..=0x7f` inline, or `NEG_INT8` for `-0x80..=-1`).
                if (0..0x80).contains(&v) || (-0x80..0).contains(&v) {
                    return self.err("non-canonical int: 16-bit width for an 8-bit value");
                }
                Ok(v)
            }
            0xfd => {
                let v = i64::from(i32::from_le_bytes(self.take(4)?.try_into().unwrap()));
                if (-0x8000..0x8000).contains(&v) {
                    return self.err("non-canonical int: 32-bit width for a 16-bit value");
                }
                Ok(v)
            }
            0xfc => {
                let v = i64::from_le_bytes(self.take(8)?.try_into().unwrap());
                if (-0x8000_0000..0x8000_0000).contains(&v) {
                    return self.err("non-canonical int: 64-bit width for a 32-bit value");
                }
                Ok(v)
            }
            other => self.err(format!("invalid int code 0x{other:02x}")),
        }
    }

    /// binprot `unit` — one `0x00` byte. This is what terminates every OCaml
    /// fixed-length `Vector.t` (`PaddedSeq`), so it is load-bearing structure, not
    /// padding: it is what makes a 15-vector distinguishable from a 16-vector.
    fn unit(&mut self) -> Result<(), WrapProofError> {
        match self.u8()? {
            0 => Ok(()),
            other => self.err(format!("expected unit 0x00, got 0x{other:02x}")),
        }
    }

    fn bool(&mut self) -> Result<bool, WrapProofError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            other => self.err(format!("expected bool 0x00/0x01, got 0x{other:02x}")),
        }
    }

    /// A 32-byte little-endian field element, CHECKED canonical against `modulus_be`, and
    /// RETURNED. Returning the bytes is what lets the chain projection
    /// ([`WrapProofShape::sg`] / [`WrapProofShape::acc0`]) be read out of the same single walk
    /// that already checks them; callers that only need the check discard with `?;`.
    fn field(&mut self, modulus_be: &[u8; 32], what: &str) -> Result<[u8; 32], WrapProofError> {
        let at = self.i;
        let le: [u8; 32] = self.take(32)?.try_into().unwrap();
        // Big-endian compare, most significant byte first. No arithmetic.
        for k in 0..32 {
            let a = le[31 - k];
            let m = modulus_be[k];
            if a < m {
                return Ok(le);
            }
            if a > m {
                return Err(WrapProofError {
                    at,
                    reason: format!(
                        "{what}: field element is NON-CANONICAL (>= the field modulus); `x` and \
                         `x + p` are the same element and must not have two encodings"
                    ),
                });
            }
        }
        Err(WrapProofError {
            at,
            reason: format!("{what}: field element equals the modulus (not canonical)"),
        })
    }

    /// A curve point as two coordinates in `modulus_be`'s field. Curve MEMBERSHIP is
    /// not checked here and must not be: `y² = x³ + 5` is Lean-authored
    /// (`MinaWrapGroupGate` / `MinaWrapSgCore.srs_g_on_curve`).
    fn point(&mut self, modulus_be: &[u8; 32], what: &str) -> Result<Point, WrapProofError> {
        let x = self.field(modulus_be, what)?;
        let y = self.field(modulus_be, what)?;
        Ok([x, y])
    }

    /// `PaddedSeq<T, N>`: exactly `N` elements followed by the unit terminator.
    fn pseq<T>(
        &mut self,
        n: usize,
        mut f: impl FnMut(&mut Self) -> Result<T, WrapProofError>,
    ) -> Result<(), WrapProofError> {
        for _ in 0..n {
            f(self)?;
        }
        self.unit()
    }

    /// `PaddedSeq<T, N>`, KEEPING the elements. Same walk as [`Self::pseq`] — the
    /// terminator is still required — but the values survive, which is what the chain
    /// projection reads.
    fn pseq_v<T>(
        &mut self,
        n: usize,
        mut f: impl FnMut(&mut Self) -> Result<T, WrapProofError>,
    ) -> Result<Vec<T>, WrapProofError> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(f(self)?);
        }
        self.unit()?;
        Ok(out)
    }

    /// `Option<T>`.
    fn opt<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, WrapProofError>,
    ) -> Result<bool, WrapProofError> {
        match self.u8()? {
            0 => Ok(false),
            1 => {
                f(self)?;
                Ok(true)
            }
            other => self.err(format!("expected Option tag 0x00/0x01, got 0x{other:02x}")),
        }
    }

    /// `ArrayN<T, CAP>`: a `Nat0` length that must not exceed `cap`, then that many
    /// elements.
    fn arrayn<T>(
        &mut self,
        cap: u64,
        mut f: impl FnMut(&mut Self) -> Result<T, WrapProofError>,
    ) -> Result<u64, WrapProofError> {
        let n = self.nat0()?;
        if n > cap {
            return self.err(format!("ArrayN length {n} exceeds its bound {cap}"));
        }
        for _ in 0..n {
            f(self)?;
        }
        Ok(n)
    }
}

/// A 128-bit Pickles challenge: `PaddedSeq<Hex64, 2>`.
fn challenge(r: &mut Reader<'_>) -> Result<(), WrapProofError> {
    r.pseq(2, |r| r.int())
}

/// The same challenge, KEEPING its value. The two `Hex64` limbs are written through binprot's
/// signed-int encoder (`Number<u64>` writes `self.0 as i64`), so the limb is reinterpreted back
/// to `u64` and the pair assembled little-endian into the 128-bit challenge.
///
/// ⚑ No arithmetic and no field reduction: this is the wire value, and the chain check is an
/// EQUALITY between two wire values. `two_u64_to_field` (which is what openmina applies before
/// hashing) is injective on these, so comparing the pre-image is the same test as comparing the
/// field elements — and it keeps every Pasta operation on the Lean side.
fn challenge_v(r: &mut Reader<'_>) -> Result<u128, WrapProofError> {
    let limbs = r.pseq_v(2, |r| r.int())?;
    Ok(u128::from(limbs[0] as u64) | (u128::from(limbs[1] as u64) << 64))
}

/// A curve point as its two 32-byte little-endian coordinates, in wire order `(x, y)`.
pub type Point = [[u8; 32]; 2];

/// Render a 32-byte LITTLE-ENDIAN field element as a decimal string — the form every Lean-side
/// Pasta constant in this tree is written in, and therefore the form the gate wires carry.
///
/// Schoolbook repeated division by 10 over 32-bit limbs. It is a base conversion, not field
/// arithmetic: no modulus is involved and nothing here depends on which Pasta field the element
/// came from.
pub fn decimal_of_le32(le: &[u8; 32]) -> String {
    let mut limbs = [0u32; 8];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let mut b = [0u8; 4];
        b.copy_from_slice(&le[i * 4..i * 4 + 4]);
        *limb = u32::from_le_bytes(b);
    }
    let mut digits: Vec<u8> = Vec::new();
    while !limbs.iter().all(|&l| l == 0) {
        let mut rem: u64 = 0;
        for limb in limbs.iter_mut().rev() {
            let cur = (rem << 32) | u64::from(*limb);
            *limb = (cur / 10) as u32;
            rem = cur % 10;
        }
        digits.push(b'0' + rem as u8);
    }
    if digits.is_empty() {
        return "0".to_string();
    }
    digits.reverse();
    String::from_utf8(digits).expect("ASCII digits")
}

/// **Decode a `protocolStateProof`** — base64url (unpadded) of the binprot
/// `Mina_base.Proof.Stable.V2` — and project its [`WrapProofShape`].
///
/// Every deviation is an `Err`. There is no lenient mode and no "unknown fields
/// ignored": the decoder walks the exact OCaml type and must land on the last byte.
pub fn decode_protocol_state_proof(b64url: &str) -> Result<WrapProofShape, WrapProofError> {
    use base64::Engine as _;
    let trimmed = b64url.trim_end_matches('=');
    let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(trimmed)
        .map_err(|e| WrapProofError {
            at: 0,
            reason: format!("protocolStateProof is not base64url: {e}"),
        })?;
    decode_proof_bytes(&bytes)
}

/// The binprot half of [`decode_protocol_state_proof`], on already-decoded bytes.
pub fn decode_proof_bytes(bytes: &[u8]) -> Result<WrapProofShape, WrapProofError> {
    const FP: &[u8; 32] = &PALLAS_BASE_MODULUS_BE;
    const FQ: &[u8; 32] = &PALLAS_SCALAR_MODULUS_BE;

    let r = &mut Reader { b: bytes, i: 0 };
    let mut checked = 0usize;

    // ── statement.proof_state.deferred_values.plonk ────────────────────────────
    challenge(r)?; // alpha
    r.pseq(2, |r| r.int())?; // beta
    r.pseq(2, |r| r.int())?; // gamma
    challenge(r)?; // zeta
    if r.opt(challenge)? {
        // The devnet blockchain Wrap index has no lookups, so `joint_combiner` is
        // `None` on every real block. A `Some` here is a proof for a DIFFERENT index
        // and the shape decision below would have to be told about it; refuse rather
        // than decode a feature nothing in this stack models.
        return r.err("joint_combiner is Some: a lookup-enabled Wrap index is not modelled here");
    }
    for _ in 0..8 {
        // feature_flags: range_check0/1, foreign_field_add/mul, xor, rot, lookup,
        // runtime_tables. All false on the devnet blockchain index.
        if r.bool()? {
            return r.err(
                "a Kimchi feature flag is SET: this proof is for an index whose gates \
                          are not modelled here",
            );
        }
    }
    // deferred_values.bulletproof_challenges — KEPT: this proof's own 16 IPA challenges are
    // half of what its CHILD block's proof must exhibit.
    let bp_challenges: [u128; 16] = r
        .pseq_v(16, challenge_v)?
        .try_into()
        .expect("pseq_v(16) yields 16");
    let branch_proofs_verified = r.u8()?;
    if branch_proofs_verified > 2 {
        return r.err(format!(
            "branch_data.proofs_verified tag {branch_proofs_verified} is not one of N0/N1/N2"
        ));
    }
    let branch_domain_log2 = r.u8()?;

    // ── statement.proof_state (rest) ───────────────────────────────────────────
    r.pseq(4, |r| r.int())?; // sponge_digest_before_evaluations
    // messages_for_next_wrap_proof.challenge_polynomial_commitment is the STEP-side
    // accumulator, so its coordinates are in the OTHER Pasta field.
    r.point(
        FQ,
        "messages_for_next_wrap_proof.challenge_polynomial_commitment",
    )?;
    checked += 2;
    r.pseq(2, |r| r.pseq(15, challenge))?; // old_bulletproof_challenges: 2 × 15

    // ── statement.messages_for_next_step_proof ─────────────────────────────────
    r.unit()?; // app_state : () — ⚑ the block is NOT in the proof; see WrapProofShape.
    let mut acc0: Point = [[0u8; 32]; 2];
    let prev_challenges = {
        let n = r.nat0()?;
        if n > 2 {
            return r.err(format!(
                "challenge_polynomial_commitments length {n} exceeds Pickles' max_proofs_verified 2"
            ));
        }
        for k in 0..n {
            let p = r.point(
                FP,
                "messages_for_next_step_proof.challenge_polynomial_commitments",
            )?;
            // Index 0 is the PARENT BLOCK's accumulator; index 1 is the transaction SNARK's.
            if k == 0 {
                acc0 = p;
            }
            checked += 2;
        }
        n as usize
    };
    let mut acc0_challenges = [0u128; 16];
    let prev_challenge_vectors = {
        let n = r.nat0()?;
        if n > 2 {
            return r.err(format!("old_bulletproof_challenges length {n} exceeds 2"));
        }
        for k in 0..n {
            let v = r.pseq_v(16, challenge_v)?;
            if k == 0 {
                acc0_challenges = v.try_into().expect("pseq_v(16) yields 16");
            }
        }
        n as usize
    };

    // ── prev_evals ─────────────────────────────────────────────────────────────
    // The previous proof's evaluations, in the Wrap proof's SCALAR field.
    let ev = |r: &mut Reader<'_>| -> Result<u64, WrapProofError> {
        let a = r.arrayn(16, |r| r.field(FQ, "prev_evals"))?;
        let b = r.arrayn(16, |r| r.field(FQ, "prev_evals"))?;
        Ok(a + b)
    };
    let mut prev_ev_checked = 0u64;
    r.field(FQ, "prev_evals.public_input.0")?;
    r.field(FQ, "prev_evals.public_input.1")?;
    checked += 2;
    {
        let mut go = |r: &mut Reader<'_>| -> Result<(), WrapProofError> {
            prev_ev_checked += ev(r)?;
            Ok(())
        };
        r.pseq(15, &mut go)?; // w
        r.pseq(15, &mut go)?; // coefficients
        go(r)?; // z
        r.pseq(6, &mut go)?; // s
        for _ in 0..6 {
            // generic / poseidon / complete_add / mul / emul / endomul_scalar selectors
            go(r)?;
        }
        for _ in 0..8 {
            // range_check0/1, foreign_field_add/mul, xor, rot, lookup_aggregation,
            // lookup_table — all `None` on a no-lookup index.
            if r.opt(&mut go)? {
                return r
                    .err("an optional lookup/foreign-field evaluation is present: not modelled");
            }
        }
        r.pseq(5, |r| r.opt(&mut go))?; // lookup_sorted
        for _ in 0..5 {
            // runtime_lookup_table, runtime_lookup_table_selector, xor_lookup_selector,
            // lookup_gate_lookup_selector, range_check_lookup_selector
            if r.opt(&mut go)? {
                return r.err("an optional lookup evaluation is present: not modelled");
            }
        }
        if r.opt(&mut go)? {
            return r.err("foreign_field_mul_lookup_selector is present: not modelled");
        }
    }
    checked += prev_ev_checked as usize;
    r.field(FQ, "prev_evals.ft_eval1")?;
    checked += 1;

    // ── proof: Pickles__Wrap_wire_proof.Stable.V1 ──────────────────────────────
    let mut w_comm = 0usize;
    r.pseq(15, |r| {
        w_comm += 1;
        r.point(FP, "commitments.w_comm")
    })?;
    checked += 2 * w_comm;
    r.point(FP, "commitments.z_comm")?;
    checked += 2;
    let mut t_comm = 0usize;
    r.pseq(7, |r| {
        t_comm += 1;
        r.point(FP, "commitments.t_comm")
    })?;
    checked += 2 * t_comm;

    // evaluations: each entry is the (ζ, ζω) PAIR of scalars, not a point.
    let mut sc = 0usize;
    let mut scalar_pair = |r: &mut Reader<'_>| -> Result<(), WrapProofError> {
        r.field(FQ, "evaluations")?;
        r.field(FQ, "evaluations")?;
        sc += 2;
        Ok(())
    };
    let mut coefficients = 0usize;
    r.pseq(15, &mut scalar_pair)?; // w
    r.pseq(15, |r| {
        coefficients += 1;
        scalar_pair(r)
    })?;
    scalar_pair(r)?; // z
    let mut s_evals = 0usize;
    r.pseq(6, |r| {
        s_evals += 1;
        scalar_pair(r)
    })?;
    for _ in 0..6 {
        scalar_pair(r)?; // the six selectors
    }
    checked += sc;
    r.field(FQ, "ft_eval1")?;
    checked += 1;

    // bulletproof
    let mut ipa_rounds = 0usize;
    let n = r.nat0()?;
    if n > 16 {
        return r.err(format!(
            "bulletproof.lr length {n} exceeds its ArrayN16 bound"
        ));
    }
    for _ in 0..n {
        r.point(FP, "bulletproof.lr.L")?;
        r.point(FP, "bulletproof.lr.R")?;
        ipa_rounds += 1;
        checked += 4;
    }
    r.field(FQ, "bulletproof.z_1")?;
    r.field(FQ, "bulletproof.z_2")?;
    checked += 2;
    r.point(FP, "bulletproof.delta")?;
    // ⚑ `sg` — this proof's own IPA accumulator, the value the CHILD block's proof must carry
    // as its `messages_for_next_step_proof.challenge_polynomial_commitments[0]`.
    let sg = r.point(FP, "bulletproof.challenge_polynomial_commitment")?;
    checked += 4;

    if r.i != bytes.len() {
        return Err(WrapProofError {
            at: r.i,
            reason: format!(
                "{} trailing byte(s) after a complete Mina_base.Proof.Stable.V2",
                bytes.len() - r.i
            ),
        });
    }

    Ok(WrapProofShape {
        prev_challenges,
        prev_challenge_vectors,
        w_comm,
        t_comm,
        s_evals,
        coefficients,
        ipa_rounds,
        branch_proofs_verified,
        branch_domain_log2,
        field_elements_checked: checked,
        sg,
        acc0,
        bp_challenges,
        acc0_challenges,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The REAL Mina devnet block 539508 as `metatheory/fixtures/pickles-extractors`
    /// pinned it — the same object o1-labs' own `kimchi::verifier::verify` accepted
    /// (`docs/MINA-REAL-BLOCK-GATE.md` §2, ground truth 3) and the Lean gate renders
    /// (`MinaRealBlockGate`). Sharing the fixture is the point: if this decoder and
    /// that extractor ever disagree about what a Mina proof IS, a test goes red.
    const DEVNET_BLOCK_JSON: &str =
        include_str!("../../metatheory/fixtures/pickles-extractors/mina_devnet_block.json");

    /// Pull `protocol_state_proof_base64_urlsafe` out of the fixture without a JSON
    /// dependency ordering concern — `serde_json` is a normal dep of this crate.
    pub(super) fn real_block_proof_b64() -> String {
        let v: serde_json::Value = serde_json::from_str(DEVNET_BLOCK_JSON).expect("fixture JSON");
        v.get("protocol_state_proof_base64_urlsafe")
            .and_then(|x| x.as_str())
            .expect("fixture carries the base64url proof")
            .to_string()
    }

    /// ⚑ THE ACCEPT. The real devnet block's Pickles Wrap proof decodes, exactly, and
    /// its shape is the shape `MinaRealBlockGate` names: `prev_challenges = 2`,
    /// `w = 15`, `t = 7`, `s = 6`, `coefficients = 15`, `k = 15` IPA rounds, and the
    /// Step-side `branch_data = {N2, 2^16}`.
    #[test]
    fn real_devnet_block_proof_decodes_to_the_pinned_shape() {
        let shape = decode_protocol_state_proof(&real_block_proof_b64())
            .expect("the real devnet block's proof decodes");
        assert_eq!(
            shape.prev_challenges, 2,
            "the real block carries 2 — the `prevLen = 0` freeze REJECTED Mina"
        );
        assert_eq!(shape.prev_challenge_vectors, 2);
        assert_eq!(shape.w_comm, 15);
        assert_eq!(shape.t_comm, 7);
        assert_eq!(shape.s_evals, 6);
        assert_eq!(shape.coefficients, 15);
        assert_eq!(shape.ipa_rounds, 15, "k = log2(max_poly_size = 2^15)");
        assert_eq!(shape.branch_proofs_verified, 2);
        assert_eq!(
            shape.branch_domain_log2, 16,
            "the STEP domain, not the Wrap 2^14"
        );
        // Non-vacuity, pinned exactly: 294 field elements of the real object were
        // canonicality-checked — 116 group coordinates, 86 Wrap evaluations, 86
        // previous-proof evaluations, both `ft_eval1`s, `z_1`/`z_2` and the two
        // `public_input` evaluations. A decoder that quietly checked nothing would
        // report 0 and this line would go red.
        assert_eq!(
            shape.field_elements_checked, 294,
            "the canonicality check must actually run on every field element"
        );

        // ⚑ THE CHAIN PROJECTION IS NOT VACUOUS. A decoder that quietly left these at their
        // zero initialisers would still satisfy every assertion above, and the proof-chain gate
        // would then compare `(0,0)` against `(0,0)` — which is exactly why the gate refuses the
        // degenerate accumulator, and exactly why this assertion exists on the Rust side too.
        assert_ne!(shape.sg, [[0u8; 32]; 2], "sg must be extracted");
        assert_ne!(shape.acc0, [[0u8; 32]; 2], "acc0 must be extracted");
        assert_ne!(shape.acc0, shape.sg, "block 539508 is not self-naming");
        assert!(
            shape.bp_challenges.iter().any(|&c| c != 0),
            "the proof's own IPA challenges must be extracted"
        );
        assert!(
            shape.acc0_challenges.iter().any(|&c| c != 0),
            "the parent's claimed IPA challenges must be extracted"
        );
        assert_ne!(
            shape.bp_challenges, shape.acc0_challenges,
            "a block's own challenges are not its parent's"
        );
    }

    /// The whole 11138-byte object is consumed — the decode is exact-fit, so an
    /// endpoint cannot append anything to a genuine proof.
    #[test]
    fn real_block_proof_is_exactly_11138_bytes_and_all_are_consumed() {
        use base64::Engine as _;
        let raw = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(real_block_proof_b64().trim_end_matches('='))
            .unwrap();
        assert_eq!(raw.len(), 11138);
        assert!(decode_proof_bytes(&raw).is_ok());
        let mut extended = raw.clone();
        extended.push(0);
        let err = decode_proof_bytes(&extended).unwrap_err();
        assert!(err.reason.contains("trailing"), "got {err}");
    }

    /// ⚑ THE FALSIFIER, on real bytes. Truncating the proof anywhere is a REFUSAL,
    /// and so is flipping the structural bytes that make a 15-vector a 15-vector.
    #[test]
    fn tampered_real_proof_is_refused() {
        use base64::Engine as _;
        let raw = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(real_block_proof_b64().trim_end_matches('='))
            .unwrap();

        // (a) truncation at a spread of offsets.
        for cut in [1usize, 100, 1000, 5000, 11137] {
            assert!(
                decode_proof_bytes(&raw[..cut]).is_err(),
                "a {cut}-byte prefix of a proof must be refused"
            );
        }

        // (b) every PaddedSeq terminator is load-bearing: corrupt one and the object
        //     stops being the OCaml type it claims to be. Offset 18 closes `alpha`'s
        //     2-limb challenge vector; the assertion on the message is what proves the
        //     offset landed where the comment says.
        let mut t = raw.clone();
        t[18] = 1;
        let err = decode_proof_bytes(&t).unwrap_err();
        assert!(err.reason.contains("expected unit"), "got {err}");

        // (c) a set feature flag (offset 77, the first of the eight) is refused, not
        //     ignored: it means the proof is for a gate set this stack does not model,
        //     and silently proceeding is how a verifier ends up checking a different
        //     circuit than the one it was handed.
        let mut t = raw.clone();
        t[77] = 1;
        let err = decode_proof_bytes(&t).unwrap_err();
        assert!(err.reason.contains("feature flag"), "got {err}");

        // (c2) and so is a `Some` joint_combiner (offset 76).
        let mut t = raw.clone();
        t[76] = 1;
        assert!(decode_proof_bytes(&t).is_err());

        // (d) the empty string and garbage.
        assert!(decode_protocol_state_proof("").is_err());
        assert!(decode_protocol_state_proof("not base64!!!").is_err());
        assert!(decode_protocol_state_proof("AAAA").is_err());
    }

    /// ⚑ A coordinate pushed out of its field is REFUSED. This is the `x + p` alias
    /// family at the proof's group elements, and it is the same wound
    /// `decode_state_hash` refuses at a state hash: two byte strings for one element.
    #[test]
    fn non_canonical_field_element_is_refused() {
        use base64::Engine as _;
        let mut raw = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(real_block_proof_b64().trim_end_matches('='))
            .unwrap();
        assert_eq!(raw.len(), 11138);
        // `messages_for_next_wrap_proof.challenge_polynomial_commitment.x` occupies
        // bytes 429..461 little-endian, so 460 is its most significant byte. Setting it
        // to 0xff puts the element well past the `0x40…` Pasta modulus. The assertion
        // on the message names the field, so the offset cannot silently drift onto
        // something else and still pass.
        raw[460] = 0xff;
        let err = decode_proof_bytes(&raw).unwrap_err();
        assert!(err.reason.contains("NON-CANONICAL"), "got {err}");
        assert!(
            err.reason
                .contains("messages_for_next_wrap_proof.challenge_polynomial_commitment"),
            "got {err}"
        );
    }

    /// Non-canonical binprot integer widths are refused: one proof, one encoding.
    #[test]
    fn non_canonical_binprot_integer_width_is_refused() {
        // A `PaddedSeq<Hex64,2>` whose first limb is `0xfe 0x01 0x00` — the 16-bit
        // width for the value 1, which `write_i64` would have written as `0x01`.
        let bytes = [0xfeu8, 0x01, 0x00];
        let r = &mut Reader { b: &bytes, i: 0 };
        let err = r.int().unwrap_err();
        assert!(err.reason.contains("non-canonical"), "got {err}");
    }
}
