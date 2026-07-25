//! Lean-first BFV — STONE 1, Rust side: a FROM-SCRATCH RNS homomorphic
//! fold-add that interoperates with `fhe.rs` ciphertexts at the BYTE level,
//! differentially anchored to `fhe.rs` as the ORACLE.
//!
//! What this module is: our own arithmetic + our own codec for the exact
//! objects `fhe.rs` produces. A BFV ciphertext is a pair `(c0, c1)` of
//! polynomials in `R_q = Z_q[X]/(X^n + 1)` with `q = q0·q1·q2` an RNS basis of
//! NTT-friendly primes; homomorphic ADDITION is coefficient-wise addition of
//! the residue rows mod each prime — no carry, no PBS, no key material. This
//! module parses a serialized `fhe.rs` ciphertext into raw RNS residue rows,
//! performs that addition with its OWN modular arithmetic (no `fhe.rs` code on
//! the add path), and re-serializes bytes that `fhe.rs` accepts and decrypts.
//!
//! The ANCHOR (what stops this being a mirror): the oracle tests in
//! `tests/bfv_lean_oracle.rs` encrypt real bucket-increment vectors with
//! `fhe.rs` (degree-4096, moduli {0xffffee001, 0xffffc4001, 0x1ffffe0001},
//! t ≈ 2^20), add them HERE, and decrypt with `fhe.rs`. If this add is wrong
//! in any way, `fhe.rs` decrypts the wrong sum and the test is RED — agreement
//! with a real BFV library cannot be faked. A second differential pins BYTE
//! equality against `fhe.rs`'s own `&ct1 + &ct2`.
//!
//! Wire-format ground truth (read from `fhe` 0.1.1 / `fhe-math` 0.1.1 SOURCE,
//! not docs — registry copies under `fhe-0.1.1/src/bfv/ciphertext.rs`,
//! `fhe-math-0.1.1/src/rq/{serialize,convert}.rs`, `fhe-util-0.1.1/src/lib.rs`):
//!
//! * `Ciphertext` proto3: `repeated bytes c = 1` (one `Rq` message per poly),
//!   `bytes seed = 2` (present only for secret-key-encrypted ciphertexts),
//!   `uint32 level = 3`.
//! * `Rq` proto3: `Representation representation = 1` (Ntt = 2 for ciphertext
//!   polys), `uint32 degree = 2`, `bytes coefficients = 3`,
//!   `bool allow_variable_time = 4`.
//! * `coefficients` are the POWER-BASIS rows (the serializer converts NTT →
//!   power basis before packing, `rq/convert.rs:19-26`), one row per RNS
//!   modulus in order, each coefficient bit-packed LSB-first at
//!   `nbits(q_i) = 64 - (q_i - 1).leading_zeros()` bits
//!   (`zq/mod.rs::serialize_vec` → `fhe-util::transcode_to_bytes`).
//!   Addition commutes with the (I)NTT, so adding power-basis rows is exact.
//! * Public-key encryption yields `seed: None` and both polys
//!   `allow_variable_time = true` (`bfv/keys/public_key.rs`); ciphertext
//!   addition ORs the flag and drops the seed (`bfv/ops/mod.rs`,
//!   `rq/ops.rs:27`).
//!
//! Scope of THIS stone (the fold path only): parse + RNS fold-add + wrap
//! refusal + re-serialize. NAMED NEXT STONES, not attempted here:
//! * from-scratch encode/encrypt/decrypt/keygen (this stone borrows them from
//!   `fhe.rs`; the Lean-first rebuild replaces them one stone at a time);
//! * seeded (secret-key) ciphertexts — the parser REFUSES them loudly rather
//!   than reimplementing ChaCha8 seed expansion (`SeededCiphertext`);
//! * multiplication / relinearization / rotations — never ride the fold path
//!   (see `TESTQALOG.md` 4swarm/bfv-sizing: that is WHY the surface is ~1/3);
//! * n-of-n threshold decrypt with PROPER exponential smudging (fhe.rs's own
//!   mbfv smudging is the known-wrong fresh-noise TODO);
//! * the noise-MARGIN meter + Lean-emitted noise bound (sizing memo item (A));
//! * the Lean model itself and the Rust↔Lean equality gate.
//!
//! Wrap discipline (sizing-memo class (C)): bucket sums ≥ t wrap SILENTLY in
//! BFV — the oracle test proves it ((t-1) + 2 decrypts to 1). Ciphertext slots
//! are opaque, so wrap cannot be detected post-hoc; it must be REFUSED at
//! ingest. Every [`LeanCiphertext`] carries `plain_bound`, a caller-declared
//! inclusive upper bound on every plaintext slot; [`fold_add`] refuses when
//! the bounds could sum to ≥ t. The bound is DECLARED, not proven — binding
//! the declaration cryptographically (range proof at ingest) is a named later
//! stone; the deployed ingest rule is `N_max · q_max < t` with q: u16, so the
//! declaration is enforceable at the boundary today.

use std::fmt;

/// The fold parameter set this stone is anchored to (asserted, not assumed, in
/// the oracle tests): degree-4096, 128-bit-secure HE-standard moduli, t ≈ 2^20.
pub const FOLD_DEGREE: usize = 4096;
/// The three RNS primes of the degree-4096 `fhe.rs` default 128-bit set.
pub const FOLD_MODULI: [u64; 3] = [0xffff_ee001, 0xffff_c4001, 0x1_ffff_e0001];

/// Errors — every refusal is loud and NAMES what was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BfvLeanError {
    /// The ciphertext carries a c1-seed (secret-key encryption). Expanding it
    /// requires ChaCha8 seed expansion — a NAMED later stone, refused here.
    SeededCiphertext,
    /// Structurally invalid / unknown wire bytes. The parser is STRICT: an
    /// unknown proto field is refused, not skipped.
    Malformed(&'static str),
    /// A parsed coefficient was ≥ its RNS modulus (non-canonical residue).
    NonCanonical { modulus_index: usize },
    /// The two operands disagree on moduli/degree/level/poly-count.
    Incompatible(&'static str),
    /// Class-(C) wrap refusal: the declared plaintext bounds could sum past
    /// t-1, so the slot sums could wrap mod t SILENTLY. Refused at ingest.
    WrapRefused {
        bound_sum: u128,
        plaintext_modulus: u64,
    },
    /// Folding an empty list has no ciphertext to return.
    EmptyFold,
    /// GPU fold: no wgpu adapter (headless CI / no device). The caller should fall back to the CPU `fold`.
    GpuUnavailable,
    /// GPU fold: this first stone only handles the fresh-fold shape (3 RNS moduli); other shapes go to CPU.
    GpuUnsupportedShape,
    /// GPU resident fold: one ciphertext does not fit in a storage-buffer binding on this adapter.
    /// Larger *batches* are streamed in bounded chunks; this is only the irreducible one-ct case.
    GpuCiphertextExceedsCapacity {
        ciphertext_bytes: u64,
        max_storage_bytes: u64,
    },
    /// GPU resident fold: one ciphertext fits, but the adapter cannot bind even a pair for the final
    /// resident reduction. Falling back here could mask an adapter-dependent correctness cliff.
    GpuReductionExceedsCapacity {
        pair_bytes: u64,
        max_storage_bytes: u64,
    },
}

impl fmt::Display for BfvLeanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SeededCiphertext => write!(
                f,
                "seeded (secret-key) ciphertext: seed expansion is a named later stone; \
                 encrypt with the public key for the fold path"
            ),
            Self::Malformed(what) => write!(f, "malformed ciphertext bytes: {what}"),
            Self::NonCanonical { modulus_index } => write!(
                f,
                "non-canonical residue: coefficient >= modulus q_{modulus_index}"
            ),
            Self::Incompatible(what) => write!(f, "incompatible operands: {what}"),
            Self::WrapRefused {
                bound_sum,
                plaintext_modulus,
            } => write!(
                f,
                "plaintext wrap refused: declared slot bounds sum to {bound_sum} >= t = \
                 {plaintext_modulus}; a slot sum could wrap mod t silently"
            ),
            Self::EmptyFold => write!(f, "cannot fold zero ciphertexts"),
            Self::GpuUnavailable => write!(f, "no wgpu adapter; fall back to the CPU fold"),
            Self::GpuUnsupportedShape => {
                write!(f, "gpu fold handles the 3-modulus fresh-fold shape only")
            }
            Self::GpuCiphertextExceedsCapacity {
                ciphertext_bytes,
                max_storage_bytes,
            } => write!(
                f,
                "one GPU-resident ciphertext is {ciphertext_bytes} bytes, larger than this adapter's \
                 {max_storage_bytes}-byte storage-buffer binding limit"
            ),
            Self::GpuReductionExceedsCapacity {
                pair_bytes,
                max_storage_bytes,
            } => write!(
                f,
                "a two-ciphertext GPU-resident reduction needs {pair_bytes} bytes, larger than this \
                 adapter's {max_storage_bytes}-byte storage-buffer binding limit"
            ),
        }
    }
}

impl std::error::Error for BfvLeanError {}

type Result<T> = std::result::Result<T, BfvLeanError>;

/// One ring element as raw RNS residue rows: `rows[i][j]` = coefficient `j`
/// (POWER-BASIS order, exactly as serialized) mod `moduli[i]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RnsPoly {
    pub rows: Vec<Vec<u64>>,
}

/// A parsed `fhe.rs` BFV ciphertext as raw RNS data, plus the declared
/// plaintext budget that makes wrap refusable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanCiphertext {
    /// RNS moduli, in serialization order.
    pub moduli: Vec<u64>,
    /// Ring degree n.
    pub degree: usize,
    /// Modulus-switch level (0 for fresh fold ciphertexts).
    pub level: u64,
    /// OR of the operands' variable-time flags (mirrors `fhe.rs` semantics).
    pub variable_time: bool,
    /// The ciphertext polys c0, c1.
    pub polys: Vec<RnsPoly>,
    /// Declared INCLUSIVE upper bound on every plaintext slot value. The wrap
    /// gate refuses an add whose bounds could sum to ≥ t.
    pub plain_bound: u64,
}

// ---------------------------------------------------------------------------
// minimal proto3 wire codec (from scratch; only what the Ciphertext/Rq
// messages use: varint + length-delimited)
// ---------------------------------------------------------------------------

struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn new(b: &'a [u8]) -> Self {
        Self { b, i: 0 }
    }

    fn done(&self) -> bool {
        self.i >= self.b.len()
    }

    fn varint(&mut self) -> Result<u64> {
        let mut v: u64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = *self
                .b
                .get(self.i)
                .ok_or(BfvLeanError::Malformed("truncated varint"))?;
            self.i += 1;
            if shift >= 64 {
                return Err(BfvLeanError::Malformed("varint overflow"));
            }
            v |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(v);
            }
            shift += 7;
        }
    }

    fn bytes(&mut self) -> Result<&'a [u8]> {
        let len = self.varint()? as usize;
        let end = self
            .i
            .checked_add(len)
            .filter(|&e| e <= self.b.len())
            .ok_or(BfvLeanError::Malformed("truncated length-delimited field"))?;
        let out = &self.b[self.i..end];
        self.i = end;
        Ok(out)
    }
}

fn push_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

// ---------------------------------------------------------------------------
// coefficient bit-packing (from scratch, matching fhe-util's LSB-first layout)
// ---------------------------------------------------------------------------

/// Bits needed for residues mod `q`: `64 - (q-1).leading_zeros()`.
fn modulus_nbits(q: u64) -> usize {
    64 - (q - 1).leading_zeros() as usize
}

/// Unpack `count` coefficients of `nbits` bits each, LSB-first, from `b`.
/// `b.len() * 8` must equal `count * nbits` exactly (degree is a multiple of 8).
fn unpack_coeffs(b: &[u8], nbits: usize, count: usize) -> Result<Vec<u64>> {
    debug_assert!(nbits > 0 && nbits <= 64);
    if b.len() * 8 != count * nbits {
        return Err(BfvLeanError::Malformed("coefficient row length mismatch"));
    }
    let mask = if nbits == 64 {
        u128::from(u64::MAX)
    } else {
        (1u128 << nbits) - 1
    };
    let mut out = Vec::with_capacity(count);
    let mut acc: u128 = 0;
    let mut acc_bits = 0usize;
    let mut idx = 0usize;
    while out.len() < count {
        while acc_bits < nbits {
            acc |= u128::from(b[idx]) << acc_bits;
            acc_bits += 8;
            idx += 1;
        }
        out.push((acc & mask) as u64);
        acc >>= nbits;
        acc_bits -= nbits;
    }
    Ok(out)
}

/// Pack coefficients of `nbits` bits each, LSB-first. Inverse of
/// [`unpack_coeffs`]; byte-identical to `fhe-util::transcode_to_bytes`.
fn pack_coeffs(a: &[u64], nbits: usize) -> Vec<u8> {
    debug_assert!(nbits > 0 && nbits <= 64);
    let nbytes = (a.len() * nbits).div_ceil(8);
    let mut out = Vec::with_capacity(nbytes);
    let mut acc: u128 = 0;
    let mut acc_bits = 0usize;
    for &c in a {
        debug_assert!(nbits == 64 || c < (1u64 << nbits));
        acc |= u128::from(c) << acc_bits;
        acc_bits += nbits;
        while acc_bits >= 8 {
            out.push(acc as u8);
            acc >>= 8;
            acc_bits -= 8;
        }
    }
    if acc_bits > 0 {
        out.push(acc as u8);
    }
    out
}

// ---------------------------------------------------------------------------
// parse / serialize
// ---------------------------------------------------------------------------

/// Representation tag for NTT in the `Rq` proto enum.
const REPR_NTT: u64 = 2;

#[derive(Debug)]
struct ParsedPoly {
    rows: Vec<Vec<u64>>,
    variable_time: bool,
}

fn parse_poly(bytes: &[u8], moduli: &[u64], degree: usize) -> Result<ParsedPoly> {
    let mut r = Reader::new(bytes);
    let mut repr: Option<u64> = None;
    let mut wire_degree: Option<u64> = None;
    let mut coeff_bytes: Option<&[u8]> = None;
    let mut variable_time = false;
    while !r.done() {
        let tag = r.varint()?;
        match (tag >> 3, tag & 7) {
            (1, 0) => repr = Some(r.varint()?),
            (2, 0) => wire_degree = Some(r.varint()?),
            (3, 2) => coeff_bytes = Some(r.bytes()?),
            (4, 0) => variable_time = r.varint()? != 0,
            _ => return Err(BfvLeanError::Malformed("unknown Rq field")),
        }
    }
    // proto3 omits zero/false/empty fields; representation and degree are
    // nonzero for real ciphertext polys, so their absence is malformed.
    if repr != Some(REPR_NTT) {
        return Err(BfvLeanError::Malformed(
            "ciphertext poly representation is not Ntt",
        ));
    }
    if wire_degree != Some(degree as u64) {
        return Err(BfvLeanError::Malformed("degree mismatch"));
    }
    let coeff_bytes = coeff_bytes.ok_or(BfvLeanError::Malformed("missing coefficients"))?;

    let total: usize = moduli.iter().map(|&q| modulus_nbits(q) * degree / 8).sum();
    if coeff_bytes.len() != total {
        return Err(BfvLeanError::Malformed("coefficient payload length"));
    }
    let mut rows = Vec::with_capacity(moduli.len());
    let mut off = 0usize;
    for (qi, &q) in moduli.iter().enumerate() {
        let nbits = modulus_nbits(q);
        let len = nbits * degree / 8;
        let row = unpack_coeffs(&coeff_bytes[off..off + len], nbits, degree)?;
        off += len;
        // STRICT canonicity: the bit-packing can express values in [q, 2^nbits);
        // fhe.rs would accept them, we refuse (a residue must be < q).
        if row.iter().any(|&c| c >= q) {
            return Err(BfvLeanError::NonCanonical { modulus_index: qi });
        }
        rows.push(row);
    }
    Ok(ParsedPoly {
        rows,
        variable_time,
    })
}

impl LeanCiphertext {
    /// Parse a serialized `fhe.rs` `Ciphertext` (its `to_bytes()`), given the
    /// parameter facts (RNS moduli in order, ring degree) and the caller's
    /// DECLARED inclusive per-slot plaintext bound (see module docs; the wrap
    /// gate refuses adds whose bounds could reach t).
    ///
    /// Refuses: seeded ciphertexts, unknown fields, non-canonical residues,
    /// wrong degree/lengths, poly count ≠ 2 (fold-path ciphertexts are always
    /// 2 polys; 3-poly cts only arise from multiplication, which never rides
    /// this path).
    pub fn from_fhe_bytes(
        bytes: &[u8],
        moduli: &[u64],
        degree: usize,
        plain_bound: u64,
    ) -> Result<Self> {
        let mut r = Reader::new(bytes);
        let mut poly_bytes: Vec<&[u8]> = Vec::new();
        let mut level = 0u64;
        while !r.done() {
            let tag = r.varint()?;
            match (tag >> 3, tag & 7) {
                (1, 2) => poly_bytes.push(r.bytes()?),
                (2, 2) => {
                    if !r.bytes()?.is_empty() {
                        return Err(BfvLeanError::SeededCiphertext);
                    }
                }
                (3, 0) => level = r.varint()?,
                _ => return Err(BfvLeanError::Malformed("unknown Ciphertext field")),
            }
        }
        if poly_bytes.len() != 2 {
            return Err(BfvLeanError::Malformed(
                "fold-path ciphertext must have exactly 2 polys",
            ));
        }
        let mut polys = Vec::with_capacity(2);
        let mut variable_time = false;
        for pb in poly_bytes {
            let p = parse_poly(pb, moduli, degree)?;
            variable_time |= p.variable_time;
            polys.push(RnsPoly { rows: p.rows });
        }
        Ok(Self {
            moduli: moduli.to_vec(),
            degree,
            level,
            variable_time,
            polys,
            plain_bound,
        })
    }

    /// Serialize back to the exact bytes `fhe.rs`'s `Ciphertext::from_bytes`
    /// accepts — byte-identical to what `fhe.rs` itself would emit for the
    /// same ciphertext (prost field order, zero-default omission).
    pub fn to_fhe_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for poly in &self.polys {
            let mut pb = Vec::new();
            // field 1 varint: representation = Ntt
            pb.push(0x08);
            push_varint(&mut pb, REPR_NTT);
            // field 2 varint: degree
            pb.push(0x10);
            push_varint(&mut pb, self.degree as u64);
            // field 3 bytes: packed rows, moduli order
            let mut coeffs = Vec::new();
            for (row, &q) in poly.rows.iter().zip(self.moduli.iter()) {
                coeffs.extend_from_slice(&pack_coeffs(row, modulus_nbits(q)));
            }
            pb.push(0x1a);
            push_varint(&mut pb, coeffs.len() as u64);
            pb.extend_from_slice(&coeffs);
            // field 4 bool: emitted only when true (proto3 default omission)
            if self.variable_time {
                pb.push(0x20);
                pb.push(0x01);
            }
            // ciphertext field 1: this poly
            out.push(0x0a);
            push_varint(&mut out, pb.len() as u64);
            out.extend_from_slice(&pb);
        }
        // seed (field 2): never present — we refuse seeded inputs.
        if self.level != 0 {
            out.push(0x18);
            push_varint(&mut out, self.level);
        }
        out
    }
}

// ---------------------------------------------------------------------------
// the RNS fold-add
// ---------------------------------------------------------------------------

fn check_compatible(a: &LeanCiphertext, b: &LeanCiphertext) -> Result<()> {
    if a.moduli != b.moduli {
        return Err(BfvLeanError::Incompatible("RNS moduli differ"));
    }
    if a.degree != b.degree {
        return Err(BfvLeanError::Incompatible("degree differs"));
    }
    if a.level != b.level {
        return Err(BfvLeanError::Incompatible("level differs"));
    }
    if a.polys.len() != 2 || b.polys.len() != 2 {
        return Err(BfvLeanError::Incompatible("poly count is not 2"));
    }
    Ok(())
}

/// Coefficient-wise residue add: both inputs canonical (< q), so one
/// conditional subtract restores canonicity. q < 2^38 « 2^64: no overflow.
fn add_row(x: &[u64], y: &[u64], q: u64) -> Vec<u64> {
    x.iter()
        .zip(y.iter())
        .map(|(&a, &b)| {
            let s = a + b;
            if s >= q {
                s - q
            } else {
                s
            }
        })
        .collect()
}

fn rns_add_raw(a: &LeanCiphertext, b: &LeanCiphertext, bound: u64) -> LeanCiphertext {
    let polys = a
        .polys
        .iter()
        .zip(b.polys.iter())
        .map(|(pa, pb)| RnsPoly {
            rows: pa
                .rows
                .iter()
                .zip(pb.rows.iter())
                .zip(a.moduli.iter())
                .map(|((ra, rb), &q)| add_row(ra, rb, q))
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli: a.moduli.clone(),
        degree: a.degree,
        level: a.level,
        variable_time: a.variable_time | b.variable_time,
        polys,
        plain_bound: bound,
    }
}

/// THE FOLD-ADD: homomorphic addition of two parsed BFV ciphertexts, with the
/// class-(C) wrap gate. Refuses (never silently wraps) when the declared
/// plaintext bounds could sum to ≥ t.
pub fn fold_add(
    a: &LeanCiphertext,
    b: &LeanCiphertext,
    plaintext_modulus: u64,
) -> Result<LeanCiphertext> {
    check_compatible(a, b)?;
    let bound_sum = u128::from(a.plain_bound) + u128::from(b.plain_bound);
    if bound_sum >= u128::from(plaintext_modulus) {
        return Err(BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus,
        });
    }
    Ok(rns_add_raw(a, b, bound_sum as u64))
}

/// Left-fold of many ciphertexts under [`fold_add`] (the budget accumulates,
/// so an N-deep fold that could reach t is refused at the exact add that
/// crosses the line). Refuses an empty fold.
pub fn fold(cts: &[LeanCiphertext], plaintext_modulus: u64) -> Result<LeanCiphertext> {
    let (first, rest) = cts.split_first().ok_or(BfvLeanError::EmptyFold)?;
    let mut acc = first.clone();
    for ct in rest {
        acc = fold_add(&acc, ct, plaintext_modulus)?;
    }
    Ok(acc)
}

/// TEST-CONTROL ONLY: the same RNS add WITHOUT the wrap gate, existing solely
/// so the oracle test can PROVE the wrap it refuses is real and silent
/// ((t-1) + 2 decrypts to 1 under `fhe.rs`). Production callers use
/// [`fold_add`]; using this on real data silently corrupts sums ≥ t.
pub fn rns_add_wrap_control(a: &LeanCiphertext, b: &LeanCiphertext) -> Result<LeanCiphertext> {
    check_compatible(a, b)?;
    Ok(rns_add_raw(a, b, u64::MAX))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_unpack_roundtrip_all_fold_moduli() {
        for &q in FOLD_MODULI.iter() {
            let nbits = modulus_nbits(q);
            // deterministic pseudo-random residues incl. the extremes
            let mut v: Vec<u64> = (0u64..4096)
                .map(|i| (i.wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(17)) % q)
                .collect();
            v[0] = 0;
            v[1] = q - 1;
            let packed = pack_coeffs(&v, nbits);
            assert_eq!(packed.len(), nbits * v.len() / 8);
            let un = unpack_coeffs(&packed, nbits, v.len()).unwrap();
            assert_eq!(v, un);
        }
    }

    #[test]
    fn varint_roundtrip() {
        for v in [0u64, 1, 127, 128, 300, u32::MAX as u64, u64::MAX] {
            let mut b = Vec::new();
            push_varint(&mut b, v);
            let mut r = Reader::new(&b);
            assert_eq!(r.varint().unwrap(), v);
            assert!(r.done());
        }
    }

    #[test]
    fn add_row_reduces_canonically() {
        let q = FOLD_MODULI[0];
        assert_eq!(add_row(&[q - 1], &[1], q), vec![0]);
        assert_eq!(add_row(&[q - 1], &[q - 1], q), vec![q - 2]);
        assert_eq!(add_row(&[0], &[5], q), vec![5]);
    }

    #[test]
    fn non_canonical_residue_refused() {
        // A row whose first coefficient is exactly q0 (>= q0, still fits in
        // nbits): the strict parser must refuse.
        let q = FOLD_MODULI[0];
        let nbits = modulus_nbits(q);
        let row = vec![q; 8]; // degree 8, all == q (non-canonical)
        let packed = pack_coeffs(&row, nbits);
        let un = unpack_coeffs(&packed, nbits, 8).unwrap();
        assert_eq!(un, row); // the packing itself carries it fine…
                             // …but parse_poly refuses it:
        let mut pb = Vec::new();
        pb.push(0x08);
        push_varint(&mut pb, REPR_NTT);
        pb.push(0x10);
        push_varint(&mut pb, 8);
        pb.push(0x1a);
        push_varint(&mut pb, packed.len() as u64);
        pb.extend_from_slice(&packed);
        let err = parse_poly(&pb, &[q], 8).unwrap_err();
        assert_eq!(err, BfvLeanError::NonCanonical { modulus_index: 0 });
    }
}
