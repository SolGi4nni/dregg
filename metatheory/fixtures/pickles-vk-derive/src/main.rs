// pickles-vk-derive — DERIVE a Mina `VerificationKey` from a LEAN-ASSEMBLED circuit.
//
// ⚑ THE SEAM THIS CLOSES. Every Mina VK in this repo up to now came from o1js `.compile()` on a
// TypeScript circuit. `metatheory/` had no `derive_vk`/`wrap_vk` path of any kind: the only VK-shaped
// object it produced was a kimchi `VerifierIndex` inside a test harness, which is not the object a
// node parses. This crate is the missing edge — Lean-emitted gates in, a Mina-encoded
// `Side_loaded_verification_key.Stable.V2.t` out.
//
// HOUSE LAW #1. Lean AUTHORS the circuit; Rust DERIVES and RUNS. Nothing here writes a constraint.
// The gate list, the coefficients and the cross-gate placement come from
// `Dregg2.Circuit.Emit.KimchiWrapMain` via `EmitWrapMainJson.lean`; the only rows this crate adds are
// trailing `Zero` rows wired to themselves, which are a DOMAIN choice (they add no constraint and
// touch no witness cell), and they are counted and reported separately from the Lean rows.
//
// ⚑ WHY THE WRAP SIDE. A zkApp account stores the **wrap** VK
// (mina/src/lib/pickles/side_loaded_verification_key.mli, ported at
// mina-rust/crates/ledger/src/proofs/verifiers.rs:396-477). `wrap_main_inputs.ml:4,6` sets
// `Me = Tock`, so a wrap circuit's native field is `Fq` and its commitments are **Pallas** points
// whose coordinates live in **Fp**. `KimchiStepMain` is the STEP side — Vesta/Fp — and its
// commitments are the wrong group for this object. `KimchiWrapMain` is the right one, and is what
// this crate reads.
//
// ---------------------------------------------------------------------------------------------
// THE OBJECT, ESTABLISHED AT SOURCE (and re-derived from o1js's own bytes; see `t1`/`t2`).
//
// o1js `VerificationKey` is `Struct({ data: String, hash: Field })`
// (o1js@2.15.0 dist/node/lib/proof-system/verification-key.js:8-13). `data` is STANDARD base64, with
// padding and NO version-tag byte, of the binprot encoding of
// `Pickles.Side_loaded.Verification_key.Stable.V2.t` — ported as
// `MinaBaseVerificationKeyWireStableV1` in mina-rust/crates/p2p-messages/src/v2/generated.rs:986,
// with `to_base64`/`from_base64` at mina-rust/crates/p2p-messages/src/v2/manual.rs:1166-1180.
//
//   off  len   field
//   0    1     max_proofs_verified      Proofs_verified variant tag: N0=0, N1=1, N2=2
//   1    1     actual_wrap_domain_size  same encoding; N0->2^13, N1->2^14, N2->2^15
//                                       (`wrap_domains`, verifiers.rs:382-393)
//   2    448   sigma_comm[0..7]         7 points
//   450  1     0x00                     binprot `()` — the Pickles_types.Vector nil
//                                       (PaddedSeq, mina-rust/crates/p2p-messages/src/pseq.rs:96)
//   451  960   coefficients_comm[0..15] 15 points
//   1411 1     0x00                     the second Vector nil
//   1412 384   generic, psm, complete_add, mul, emul, endomul_scalar
//   total 1796
//
// A point is 64 bytes: `x` then `y`, each a 32-byte LITTLE-ENDIAN canonical (non-Montgomery) Fp
// element. NO compression, NO parity byte, NO Finite/Infinity tag — the identity is representable
// only as (0,0) (`make_group`, mina-rust/crates/ledger/src/proofs/transaction.rs:147). 28
// commitments, in exactly the order `make_zkapp_verifier_index` reads them back out
// (verifiers.rs:452-459).
//
// THE HASH stored beside the key is
//     Poseidon_Fp( update( update([0;3], [prefix]), fields ) )[0]
// with `prefix = "MinaSideLoadedVk****"` read as 32 little-endian bytes into Fp
// (o1js dist/node/bindings/crypto/constants.js:18 + binable.js:224-229; mina-rust
// poseidon/src/hash.rs:188-196,280) and
//     fields = [x,y of all 28 commitments in the order above]  ++  [one packed word]
// where the packed word is the SIX one-hot bits of (max_proofs_verified, actual_wrap_domain_size),
// first bit most significant (mina-rust crates/ledger/src/account/account.rs:386-400,472-490;
// the bit-packed items land AFTER the full field elements because `Inputs::to_fields` appends them,
// poseidon/src/hash.rs:150). `t2` checks this against o1js on three real keys — mina-rust has no
// such cross-implementation pin.
//
// ---------------------------------------------------------------------------------------------
// THE SRS IS MINA'S. `SRS::create(depth)` is the deterministic Blake2b-to-curve construction
// (poly-commitment/src/ipa.rs:353-380), and it is what openmina builds a zkApp *verifier* index with
// (`SRS::<Pallas>::create(1 << BACKEND_TOCK_ROUNDS_N)`, verifiers.rs:405-410). kimchi's
// `new_index_for_test_with_lookups` would instead hand back the serialized TEST srs for log2 <= 16
// (prover_index.rs:225-231), which is a DIFFERENT set of points — so this crate passes its own
// `get_srs` closure and never touches the test SRS. `max_poly_size` is pinned to 2^15, Mina's Tock
// value, which is also what the devnet wrap VKs in bridge/mina-zkapp/fixtures carry.
//
// ---------------------------------------------------------------------------------------------
// ⚑ BOTH CURVES, AND `--curve` IS NOT OPTIONAL.
//
// This crate was Pallas/Fq ONLY, and not by a type parameter it happened to instantiate — by
// `build_gates -> Vec<CircuitGate<Fq>>`, hardcoded, reading a hardcoded pair of rung names through
// `load_wrapmain`. A STEP-side circuit could not go through it, and the way it could not was the
// dangerous way: `Fq::from_str` on an Fp coefficient is `BigInt::from_str(s) % q` (ark-ff 0.5,
// `fields/models/fp/mod.rs:651-666`), and every step-side value is below p < q, so it would have
// parsed SILENTLY and derived a key for a circuit nobody authored.
//
// Three refusals replace that comment:
//
//   1. **`--curve {pallas|vesta}` is REQUIRED.** Nothing in an emitted artifact says which field it
//      was authored over — the renderer emits decimal strings and both primes accept the same
//      literals below p — so the field is a DECLARATION, and this crate refuses to guess it. There
//      is no default; running without it exits non-zero.
//   2. **A non-canonical literal is refused, not reduced.** `pickles-circuit-driver`'s
//      `parse_field` errors on `|value| >= modulus` instead of wrapping. That catches the Fq-into-Fp
//      direction outright (the window `[p, q)` is exactly the wrap-side values `Fp::from_str` would
//      have silently reduced) and it is the half of the hazard the bytes CAN see.
//   3. **A Vesta-committed circuit cannot be written as a Mina `Side_loaded_verification_key`.**
//      That object holds Pallas points; a zkApp account stores the WRAP key. The step derivation
//      reports its 28 commitments and its domain and REFUSES the binprot encoding, rather than
//      emitting 1796 bytes that decode as a key for the wrong group.
//
// USAGE
//   cargo run --release -- <out-dir> --curve pallas [--log2-domain 14]
//   cargo run --release -- <out-dir> --curve vesta --circuit /path/to/stepmain_smoke_r7.json
//   cargo test --release
//
// SCOPE — read this before quoting anything. This derives and encodes a KEY. It does not produce a
// proof, it does not claim the assembled `wrap_main` is complete (`KimchiWrapMain` §13 names by
// sub-circuit what is absent), and "a node parses it" is NOT "a node verifies a proof against it".

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use std::time::Instant;

use ark_ec::AffineRepr;
use ark_ff::{BigInt, BigInteger, Field as _, PrimeField, Zero};
use ark_poly::EvaluationDomain;
use mina_curves::pasta::{Fp, Fq};
use mina_poseidon::{
    constants::{PlonkSpongeConstantsKimchi, SpongeConstants},
    pasta::{fp_kimchi, FULL_ROUNDS},
    poseidon::{ArithmeticSponge, Sponge as _},
};
use poly_commitment::PolyComm;

use kimchi::circuits::{constraints::ConstraintSystem, gate::CircuitGate};

// ⚑ THE ONE DRIVER. `build_gates` and the index construction are `pickles-circuit-driver`'s, shared
// with the four prove-and-bind harnesses and generic over the curve — which is what makes this
// crate's second curve a type argument rather than a second copy.
use pickles_circuit_driver::{
    load, BaseOf, CircuitJson, Idx, IndexOpts, Lane, ScalarOf, Srs, Step, StepBaseSponge, Wrap,
    WrapBaseSponge,
};

/// Mina's Tock `max_poly_size`: `BACKEND_TOCK_ROUNDS_N = 15`
/// (mina-rust/crates/ledger/src/proofs/constants.rs; used at verifiers.rs:406,448).
const TOCK_MAX_POLY_SIZE: usize = 1 << 15;

/// Mina's Tick `max_poly_size`: `BACKEND_TICK_ROUNDS_N = 16` — the STEP side's. ⚠ It is NOT
/// interchangeable with the Tock one: `max_poly_size` decides how many chunks a commitment splits
/// into, so deriving a step key at the wrap value would produce a differently-chunked object.
const TICK_MAX_POLY_SIZE: usize = 1 << 16;

/// The wire length of a `Side_loaded_verification_key.Stable.V2.t`.
const VK_WIRE_LEN: usize = 1796;

/// The 28 commitments, in binprot / `make_zkapp_verifier_index` order.
const COMM_NAMES: [&str; 28] = [
    "sigma[0]",
    "sigma[1]",
    "sigma[2]",
    "sigma[3]",
    "sigma[4]",
    "sigma[5]",
    "sigma[6]",
    "coeff[0]",
    "coeff[1]",
    "coeff[2]",
    "coeff[3]",
    "coeff[4]",
    "coeff[5]",
    "coeff[6]",
    "coeff[7]",
    "coeff[8]",
    "coeff[9]",
    "coeff[10]",
    "coeff[11]",
    "coeff[12]",
    "coeff[13]",
    "coeff[14]",
    "generic",
    "psm",
    "complete_add",
    "mul",
    "emul",
    "endomul_scalar",
];

// =================================================================================================
// the wire object
// =================================================================================================

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WrapVk {
    /// `Proofs_verified.t` tag, 0..=2.
    pub max_proofs_verified: u8,
    /// `Proofs_verified.t` tag, 0..=2; N0 -> 2^13, N1 -> 2^14, N2 -> 2^15.
    pub actual_wrap_domain_size: u8,
    /// 28 Pallas points as (x, y) in Fp, in `COMM_NAMES` order.
    pub comms: [(Fp, Fp); 28],
}

fn fp_le(f: &Fp) -> [u8; 32] {
    let mut out = [0u8; 32];
    let b = f.into_bigint().to_bytes_le();
    out[..b.len()].copy_from_slice(&b);
    out
}

/// Is (x, y) on Pallas, `y^2 = x^3 + 5`? The identity (0,0) is NOT — Mina has no other encoding
/// for it, so a VK carrying a zero commitment is a VK carrying an off-curve point.
fn on_pallas(x: Fp, y: Fp) -> bool {
    y.square() == x.square() * x + Fp::from(5u64)
}

impl WrapVk {
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(VK_WIRE_LEN);
        out.push(self.max_proofs_verified);
        out.push(self.actual_wrap_domain_size);
        fn push(out: &mut Vec<u8>, p: (Fp, Fp)) {
            out.extend_from_slice(&fp_le(&p.0));
            out.extend_from_slice(&fp_le(&p.1));
        }
        for i in 0..7 {
            push(&mut out, self.comms[i]);
        }
        out.push(0x00); // Vector nil after sigma_comm
        for i in 7..22 {
            push(&mut out, self.comms[i]);
        }
        out.push(0x00); // Vector nil after coefficients_comm
        for i in 22..28 {
            push(&mut out, self.comms[i]);
        }
        debug_assert_eq!(out.len(), VK_WIRE_LEN);
        out
    }

    /// Strict binprot reader. Every refusal below is one a Mina reader also makes; `t6` proves each
    /// one goes red, and `bridge/mina-zkapp/scripts/mina-vk-parse-gate.mjs` re-runs the same four
    /// mutations through o1js's OCaml reader.
    pub fn decode(b: &[u8]) -> Result<Self, String> {
        if b.len() != VK_WIRE_LEN {
            return Err(format!("length {} != {VK_WIRE_LEN}", b.len()));
        }
        let tag = |i: usize| -> Result<u8, String> {
            match b[i] {
                t @ 0..=2 => Ok(t),
                t => Err(format!("byte {i}: Proofs_verified tag {t} is not N0/N1/N2")),
            }
        };
        let mut off = 2usize;
        let mut comms = [(Fp::zero(), Fp::zero()); 28];
        let mut rd = |off: &mut usize, i: usize| -> Result<(), String> {
            let f = |s: &[u8]| -> Result<Fp, String> {
                // `from_bigint` returns None for a >= p representative: a non-canonical limb is a
                // refusal, not a reduction.
                fp_from_le(s)
                    .ok_or_else(|| format!("{}: limb is not a canonical Fp element", COMM_NAMES[i]))
            };
            let x = f(&b[*off..*off + 32])?;
            let y = f(&b[*off + 32..*off + 64])?;
            if !on_pallas(x, y) {
                return Err(format!("{}: (x,y) is not on Pallas", COMM_NAMES[i]));
            }
            comms[i] = (x, y);
            *off += 64;
            Ok(())
        };
        for i in 0..7 {
            rd(&mut off, i)?;
        }
        if b[off] != 0 {
            return Err(format!(
                "byte {off}: Vector nil after sigma_comm is {:#04x}, not 0x00",
                b[off]
            ));
        }
        off += 1;
        for i in 7..22 {
            rd(&mut off, i)?;
        }
        if b[off] != 0 {
            return Err(format!(
                "byte {off}: Vector nil after coefficients_comm is {:#04x}, not 0x00",
                b[off]
            ));
        }
        off += 1;
        for i in 22..28 {
            rd(&mut off, i)?;
        }
        assert_eq!(off, VK_WIRE_LEN);
        Ok(WrapVk {
            max_proofs_verified: tag(0)?,
            actual_wrap_domain_size: tag(1)?,
            comms,
        })
    }

    pub fn to_base64(&self) -> String {
        b64_encode(&self.encode())
    }

    pub fn from_base64(s: &str) -> Result<Self, String> {
        Self::decode(&b64_decode(s)?)
    }

    /// The field element a zkApp account stores beside the key. See the header for the layout and
    /// its citations; `t2` pins this against o1js on three independently produced keys.
    pub fn hash(&self) -> Fp {
        let params = fp_kimchi::static_params();
        let rate = PlonkSpongeConstantsKimchi::SPONGE_RATE;
        let mut sponge =
            ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
        assert!(
            sponge.state.iter().all(|s: &Fp| s.is_zero()),
            "sponge starts at [0;3]"
        );

        // `Random_oracle.update ~state input`: add each rate-sized block (zero-padded) into the
        // state and permute. This is NOT `Sponge::absorb`, which does not permute a partial block.
        let update =
            |sponge: &mut ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>,
             input: &[Fp]| {
                for block in input.chunks(rate) {
                    for (i, x) in block.iter().enumerate() {
                        sponge.state[i] += x;
                    }
                    sponge.poseidon_block_cipher();
                }
            };

        update(&mut sponge, &[sideloaded_vk_prefix_field()]);

        let mut fields: Vec<Fp> = Vec::with_capacity(57);
        for (x, y) in self.comms.iter() {
            fields.push(*x);
            fields.push(*y);
        }
        // The two `Proofs_verified` values are appended as SIX one-hot bits, packed MSB-first into
        // one field, and land after the full field elements.
        let one_hot = |t: u8| -> [bool; 3] { [t == 0, t == 1, t == 2] };
        let mut packed = 0u64;
        for b in one_hot(self.max_proofs_verified)
            .into_iter()
            .chain(one_hot(self.actual_wrap_domain_size))
        {
            packed = (packed << 1) | (b as u64);
        }
        fields.push(Fp::from(packed));

        update(&mut sponge, &fields);
        sponge.state[0]
    }
}

/// `prefixToField("MinaSideLoadedVk****")`: the ASCII bytes, zero-padded to 32, read little-endian.
fn sideloaded_vk_prefix_field() -> Fp {
    const PREFIX: &str = "MinaSideLoadedVk****";
    let mut le = [0u8; 32];
    le[..PREFIX.len()].copy_from_slice(PREFIX.as_bytes());
    fp_from_le(&le).expect("prefix < p")
}

/// 32 little-endian bytes -> Fp, REFUSING a non-canonical representative (>= p). That refusal is the
/// reason this is not `from_le_bytes_mod_order`: silently reducing would accept a key Mina rejects.
fn fp_from_le(s: &[u8]) -> Option<Fp> {
    if s.len() != 32 {
        return None;
    }
    let mut limbs = [0u64; 4];
    for (i, l) in limbs.iter_mut().enumerate() {
        *l = u64::from_le_bytes(s[i * 8..i * 8 + 8].try_into().unwrap());
    }
    Fp::from_bigint(BigInt::new(limbs))
}

// -- base64, standard alphabet with padding (no dependency worth taking for 40 lines) -------------

const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn b64_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for c in bytes.chunks(3) {
        let b = [c[0], *c.get(1).unwrap_or(&0), *c.get(2).unwrap_or(&0)];
        let n = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | b[2] as u32;
        s.push(B64[(n >> 18) as usize & 63] as char);
        s.push(B64[(n >> 12) as usize & 63] as char);
        s.push(if c.len() > 1 {
            B64[(n >> 6) as usize & 63] as char
        } else {
            '='
        });
        s.push(if c.len() > 2 {
            B64[n as usize & 63] as char
        } else {
            '='
        });
    }
    s
}

fn b64_decode(s: &str) -> Result<Vec<u8>, String> {
    let mut rev = [255u8; 256];
    for (i, c) in B64.iter().enumerate() {
        rev[*c as usize] = i as u8;
    }
    let raw: Vec<u8> = s
        .bytes()
        .filter(|c| !c.is_ascii_whitespace() && *c != b'=')
        .collect();
    let mut out = Vec::with_capacity(raw.len() * 3 / 4);
    let mut acc: u32 = 0;
    let mut nbits = 0u32;
    for c in raw {
        let v = rev[c as usize];
        if v == 255 {
            return Err(format!("byte {c:#04x} is not base64"));
        }
        acc = (acc << 6) | v as u32;
        nbits += 6;
        if nbits >= 8 {
            nbits -= 8;
            out.push((acc >> nbits) as u8);
        }
    }
    Ok(out)
}

// =================================================================================================
// the Lean-emitted circuit
// =================================================================================================

/// ⚑ **THE LANE IS DECLARED, NOT INFERRED.** An emitted circuit is a list of decimal strings; both
/// pasta primes accept every literal below `p`, so no amount of reading the artifact says which
/// field it was authored over. This enum is the declaration, it comes from `--curve`, and there is
/// no default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Curve {
    /// The WRAP side. Pallas-committed, Fq-scalar, coordinates in Fp. `wrap_main_inputs.ml:4,6`
    /// sets `Me = Tock`. This is the object a zkApp account stores.
    Pallas,
    /// The STEP side. Vesta-committed, Fp-scalar, coordinates in Fq. ⚠ A Vesta-committed key is NOT
    /// a Mina `Side_loaded_verification_key` — see [`Derived::mina_vk`].
    Vesta,
}

impl Curve {
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "pallas" | "wrap" => Ok(Curve::Pallas),
            "vesta" | "step" => Ok(Curve::Vesta),
            other => Err(format!(
                "--curve {other:?} is not one of pallas|wrap (the wrap side, Fq) or \
                 vesta|step (the step side, Fp)"
            )),
        }
    }
    pub fn max_poly_size(self) -> usize {
        match self {
            Curve::Pallas => TOCK_MAX_POLY_SIZE,
            Curve::Vesta => TICK_MAX_POLY_SIZE,
        }
    }
}

/// Trailing `Zero` rows, each cell wired to itself. A `Zero` gate constrains nothing and a
/// self-wire puts the cell in a singleton permutation class, so this changes the DOMAIN and nothing
/// else. It is how a circuit smaller than Mina's wrap domain is placed in that domain.
fn pad_to_rows<F: PrimeField>(gates: &mut Vec<CircuitGate<F>>, target_rows: usize) {
    while gates.len() < target_rows {
        let row = gates.len();
        let w: kimchi::circuits::wires::GateWires =
            std::array::from_fn(|col| kimchi::circuits::wires::Wire { row, col });
        gates.push(CircuitGate::new(
            kimchi::circuits::gate::GateType::Zero,
            w,
            vec![],
        ));
    }
}

/// The constraint system on its own — no SRS, no commitments. Used to ask kimchi what domain a row
/// count lands in without paying for an SRS.
fn constraint_system<F: PrimeField>(
    gates: Vec<CircuitGate<F>>,
    public: usize,
    max_poly_size: usize,
) -> ConstraintSystem<F> {
    ConstraintSystem::<F>::create(gates)
        .public(public)
        .prev_challenges(2)
        .disable_gates_checks(true)
        .max_poly_size(Some(max_poly_size))
        .build()
        .expect("the Lean-emitted gate list builds a constraint system")
}

fn one_chunk<G: AffineRepr>(c: &PolyComm<G>, name: &str) -> (G::BaseField, G::BaseField) {
    assert_eq!(
        c.chunks.len(),
        1,
        "{name}: a side-loaded VK holds ONE chunk per commitment; domain must be <= max_poly_size"
    );
    let p = c.chunks[0];
    p.xy()
        .unwrap_or((G::BaseField::zero(), G::BaseField::zero()))
}

/// A derivation, on whichever curve was DECLARED. The 28 commitments live in the curve's BASE
/// field, which is why this is generic and why the Mina wire encoding is not.
pub struct Derived<L: Lane> {
    pub comms: [(BaseOf<L>, BaseOf<L>); 28],
    pub lean_rows: usize,
    pub padded_rows: usize,
    pub log2_domain: u32,
    /// `Some(tag)` when the derived domain is one `actual_wrap_domain_size` can NAME (2^13/2^14/2^15),
    /// `None` otherwise. A `None` key is still a well-formed object and o1js still parses it, but its
    /// declared domain would be a LIE, so `write_vk` refuses to emit one.
    pub wrap_domain_tag: Option<u8>,
    pub public: usize,
    pub circuit: String,
    pub curve: Curve,
}

/// Pad `gates` until the constraint system's domain IS `2^k`, or refuse.
fn pad_to_domain<F: PrimeField>(
    gates: &mut Vec<CircuitGate<F>>,
    name: &str,
    public: usize,
    max_poly_size: usize,
    k: u32,
) {
    // kimchi sizes d1 as the next power of two at or above `gates.len() + zk_rows`. Rather than
    // re-derive zk_rows, walk down from the target until the built domain IS the target — and
    // refuse if no padding reaches it.
    let target = 1usize << k;
    let lean_rows = gates.len();
    assert!(
        lean_rows < target,
        "{name} has {lean_rows} rows, which does not fit domain 2^{k}"
    );
    for slack in 1..64usize {
        let mut g = gates.clone();
        pad_to_rows(&mut g, target - slack);
        // The constraint system alone decides the domain; building it needs no SRS, so the search
        // is cheap and the answer is kimchi's, not a re-derived zk_rows formula.
        if constraint_system(g.clone(), public, max_poly_size)
            .domain
            .d1
            .size()
            == target
        {
            *gates = g;
            return;
        }
    }
    panic!("no padding length reaches domain 2^{k}");
}

/// Lean-emitted gates -> constraint system -> Mina's SRS -> the 28 commitments. This function is the
/// whole derivation, and it is the SAME function on both curves.
pub fn derive_on<L: Lane, EFq>(
    c: &CircuitJson,
    curve: Curve,
    log2_domain: Option<u32>,
) -> Derived<L>
where
    BaseOf<L>: PrimeField,
    pickles_circuit_driver::Map<L>: Sync,
    EFq: Clone
        + mina_poseidon::FqSponge<BaseOf<L>, L::G, ScalarOf<L>, { pickles_circuit_driver::ROUNDS }>,
{
    let mps = curve.max_poly_size();
    // ⚑ The gate list comes from the SHARED reader, whose `parse_field` REFUSES a literal that is
    // not canonical for `ScalarOf<L>` rather than reducing it into range.
    let mut gates = pickles_circuit_driver::build_gates::<ScalarOf<L>>(c);
    let lean_rows = gates.len();
    if let Some(k) = log2_domain {
        pad_to_domain(&mut gates, &c.name, c.public_input_size, mps, k);
    }
    let padded_rows = gates.len();
    let index: Idx<L> = pickles_circuit_driver::index_from_gates::<L, EFq>(
        gates,
        IndexOpts::test(c.public_input_size)
            .prev_challenges(2) // Mina's wrap VK carries prev_challenges = 2 (verifiers.rs:451)
            .srs(Srs::MinaParallel)
            .max_poly_size(Some(mps)),
    );
    let vi = index.verifier_index.as_ref().expect("verifier index");
    assert_eq!(vi.max_poly_size, mps);
    assert_eq!(vi.prev_challenges, 2);

    let mut comms = [(BaseOf::<L>::zero(), BaseOf::<L>::zero()); 28];
    for i in 0..7 {
        comms[i] = one_chunk::<L::G>(&vi.sigma_comm[i], COMM_NAMES[i]);
    }
    for i in 0..15 {
        comms[7 + i] = one_chunk::<L::G>(&vi.coefficients_comm[i], COMM_NAMES[7 + i]);
    }
    for (j, cm) in [
        &vi.generic_comm,
        &vi.psm_comm,
        &vi.complete_add_comm,
        &vi.mul_comm,
        &vi.emul_comm,
        &vi.endomul_scalar_comm,
    ]
    .into_iter()
    .enumerate()
    {
        comms[22 + j] = one_chunk::<L::G>(cm, COMM_NAMES[22 + j]);
    }

    let log2 = vi.domain.log_size_of_group;
    // `wrap_domains` (mina/src/lib/pickles/common.ml:27-31): proofs_verified 0/1/2 -> 2^13/2^14/2^15,
    // and `actual_wrap_domain_size` is the INVERSE of that map (common.ml:33-45). It can therefore
    // name only those three domains. Declare the truth when the derived domain is one of them, and
    // carry `None` — which `write_vk` refuses to emit — when it is not.
    // ⚠ On VESTA there is no `actual_wrap_domain_size` at all; the tag is meaningless there and is
    // held at `None` so nothing downstream can read a wrap declaration off a step key.
    let wrap_domain_tag = match (curve, log2) {
        (Curve::Pallas, 13) => Some(0u8),
        (Curve::Pallas, 14) => Some(1u8),
        (Curve::Pallas, 15) => Some(2u8),
        _ => None,
    };
    Derived {
        comms,
        lean_rows,
        padded_rows,
        log2_domain: log2,
        wrap_domain_tag,
        public: c.public_input_size,
        circuit: c.name.clone(),
        curve,
    }
}

/// The wrap derivation: Pallas, Fq scalars, Fp coordinates.
pub fn derive(c: &CircuitJson, log2_domain: Option<u32>) -> Derived<Wrap> {
    derive_on::<Wrap, WrapBaseSponge>(c, Curve::Pallas, log2_domain)
}

/// The step derivation: Vesta, Fp scalars, Fq coordinates. ⚠ Its commitments are on the WRONG GROUP
/// for a Mina side-loaded VK, and [`Derived::<Step>`] carries no `mina_vk`.
pub fn derive_step(c: &CircuitJson, log2_domain: Option<u32>) -> Derived<Step> {
    derive_on::<Step, StepBaseSponge>(c, Curve::Vesta, log2_domain)
}

impl Derived<Wrap> {
    /// ⚑ The Mina wire object. Pallas-only, and that is not an accident of this impl block: the
    /// binprot layout stores 32-byte little-endian **Fp** coordinates, which is what a Pallas point
    /// has. There is no `impl Derived<Step>` counterpart, so a step key cannot be written as one by
    /// construction rather than by a check somebody could forget.
    pub fn mina_vk(&self) -> WrapVk {
        WrapVk {
            // ⚑ `max_proofs_verified` is a property of the STEP branch this wrap wraps, and NOTHING in
            // a wrap gate list determines it — it is DECLARED here, not derived. The only declaration
            // that is not immediately self-contradictory is the one `wrap_domains` inverts to: a key
            // whose wrap domain is 2^14 and whose `max_proofs_verified` says N2 asserts a domain of
            // 2^15 in the same object. So both fields carry the derived domain's tag, and when the
            // step side lands this becomes a real input rather than a consistency choice.
            max_proofs_verified: self.wrap_domain_tag.unwrap_or(0),
            actual_wrap_domain_size: self.wrap_domain_tag.unwrap_or(0),
            comms: self.comms,
        }
    }
}

// =================================================================================================
// fixtures + CLI
// =================================================================================================

fn own_fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures")
}

/// ⚑ THIS CRATE CARRIES ITS OWN COPY of the Lean emission, exactly as every other harness in the
/// pickles ratchet does. It does NOT reach into `pickles-wrapmain-harness/fixtures`: a gate whose
/// inputs live in a sibling crate is a gate that cannot run from a clean checkout of HEAD unless the
/// sibling landed first, and that is how a committed gate silently stops being runnable.
/// `scripts/mina-vk-derivation-gate.sh` diffs this copy against the wrapmain harness's byte-for-byte
/// and goes RED on any drift, so the copy cannot quietly diverge from the emission it claims to be.
///
/// REGENERATE (only when the Lean assembly changes):
///   cd metatheory && lake build Dregg2.Circuit.Emit.KimchiWrapMain \
///     && DREGG_WM=smoke lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean \
///     && cp /tmp/pickles-wrapmain/wrapmain_smoke_w{3_branch,4_bind}.json \
///           fixtures/pickles-vk-derive/fixtures/
fn load_wrapmain(rung: &str) -> CircuitJson {
    load(&own_fixtures_dir().join(format!("wrapmain_smoke_{rung}.json")))
}

/// Write a derived WRAP key. ⚑ There is no step-side counterpart, by construction: `mina_vk` exists
/// only on `Derived<Wrap>`, so "write a Mina side-loaded VK from a Vesta-committed circuit" is not a
/// call this file can express.
fn write_vk(dir: &Path, stem: &str, d: &Derived<Wrap>) -> PathBuf {
    let vk = d.mina_vk();
    // ⚠ NO FALLBACK. A key whose circuit does not sit in 2^13/2^14/2^15 cannot state its own wrap
    // domain, and emitting one with a made-up tag would ship a field that says something false about
    // the object it travels with. Pad the circuit to a nameable domain or do not write the file.
    assert!(
        d.wrap_domain_tag.is_some(),
        "{}: domain 2^{} is not one `actual_wrap_domain_size` can name (2^13/2^14/2^15); \
         re-derive with --log2-domain rather than declaring a domain the key does not have",
        d.circuit,
        d.log2_domain
    );
    let p = dir.join(format!("{stem}.json"));
    let v = serde_json::json!({
        "data": vk.to_base64(),
        "hash": vk.hash().to_string(),
        "derivedFrom": {
            "lean_module": "Dregg2.Circuit.Emit.KimchiWrapMain",
            "circuit": d.circuit,
            "lean_rows": d.lean_rows,
            "padded_rows": d.padded_rows,
            "zero_padding_rows": d.padded_rows - d.lean_rows,
            "public_input_size": d.public,
        },
        "wire": {
            "bytes": VK_WIRE_LEN,
            "max_proofs_verified": vk.max_proofs_verified,
            "actual_wrap_domain_size": vk.actual_wrap_domain_size,
            "log2_domain": d.log2_domain,
            "max_poly_size": TOCK_MAX_POLY_SIZE,
            "prev_challenges": 2,
            "srs": "SRS::<Pallas>::create_parallel — Mina's deterministic Blake2b-to-curve SRS",
        },
        "commitments": vk.comms.iter().enumerate()
            .map(|(i,(x,y))| (COMM_NAMES[i].to_string(), serde_json::json!({"x": x.to_string(), "y": y.to_string()})))
            .collect::<BTreeMap<_,_>>(),
    });
    std::fs::write(&p, serde_json::to_string_pretty(&v).unwrap() + "\n").unwrap();
    p
}

/// One coefficient of one Lean-emitted gate, plus one. Everything downstream must move.
#[cfg_attr(not(test), allow(dead_code))]
fn perturb_coefficient(c: &CircuitJson, row: usize, coeff: usize) -> CircuitJson {
    let mut out = c.clone();
    let g = &mut out.gates[row];
    assert!(
        coeff < g.coeffs.len(),
        "row {row} has {} coefficients",
        g.coeffs.len()
    );
    let v = pickles_circuit_driver::parse_field::<Fq>(&g.coeffs[coeff]) + Fq::from(1u64);
    g.coeffs[coeff] = v.to_string();
    out.name = format!("{}_perturbed_r{row}c{coeff}", c.name);
    out
}

/// Re-point ONE wire of ONE Lean-emitted row at itself, breaking it out of its permutation class.
/// The copy-permutation is what `sigma_comm` commits to, so this must move sigma and nothing else.
#[cfg_attr(not(test), allow(dead_code))]
fn perturb_wire(c: &CircuitJson, row: usize, col: usize) -> CircuitJson {
    let mut out = c.clone();
    out.gates[row].wires[col] = [row, col];
    out.name = format!("{}_wire_r{row}c{col}", c.name);
    out
}

/// Retype ONE Lean-emitted row. Selector polynomials are a function of the gate TYPE column alone.
#[cfg_attr(not(test), allow(dead_code))]
fn perturb_gate_type(c: &CircuitJson, row: usize, typ: u64) -> CircuitJson {
    let mut out = c.clone();
    out.gates[row].typ = typ;
    out.name = format!("{}_retyped_r{row}", c.name);
    out
}

/// The lines a derivation prints, on either curve. `Derived<L>` is generic and so is this.
fn report<L: Lane>(tag: &str, d: &Derived<L>)
where
    BaseOf<L>: PrimeField,
{
    println!(
        "\n{tag}: {} Lean rows (+{} Zero pad) -> domain 2^{}, public {} [{}]",
        d.lean_rows,
        d.padded_rows - d.lean_rows,
        d.log2_domain,
        d.public,
        L::NAME
    );
}

fn usage() -> ! {
    eprintln!(
        "usage: derive-vk <out-dir> --curve <pallas|vesta> [--circuit <path>] [--log2-domain N]\n\
         \n\
         ⚠ --curve is REQUIRED and has no default. An emitted circuit is decimal strings; both\n\
         pasta primes accept every literal below p, so NOTHING in the artifact says which field it\n\
         was authored over. Deriving a key on the wrong curve is silent — the coefficients parse\n\
         and a well-formed key for a circuit nobody authored comes out. Declare the lane."
    );
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out = PathBuf::from(
        args.iter()
            .find(|a| !a.starts_with("--"))
            .cloned()
            .unwrap_or_else(|| "/tmp/pickles-vk-derive".into()),
    );

    // ⚑ REFUSAL #1 — the lane is declared or the run stops.
    let curve = match args.iter().position(|a| a == "--curve") {
        Some(i) => match args.get(i + 1).map(|s| Curve::parse(s)) {
            Some(Ok(c)) => c,
            Some(Err(e)) => {
                eprintln!("{e}");
                usage()
            }
            None => usage(),
        },
        None => {
            eprintln!("REFUSED: --curve is required.");
            usage()
        }
    };

    let log2: Option<u32> = match args.iter().position(|a| a == "--log2-domain") {
        Some(i) => Some(args[i + 1].parse().expect("--log2-domain wants an integer")),
        None => Some(14),
    };
    std::fs::create_dir_all(&out).unwrap();

    println!("pickles-vk-derive — a Lean-assembled circuit -> a derived verification key");
    println!(
        "  declared lane: {}",
        match curve {
            Curve::Pallas => "pallas/Fq — the WRAP side (Dregg2.Circuit.Emit.KimchiWrapMain)",
            Curve::Vesta => "vesta/Fp — the STEP side (Dregg2.Circuit.Emit.KimchiStepMain)",
        }
    );
    println!(
        "  target domain: {}",
        log2.map(|k| format!("2^{k}")).unwrap_or("natural".into())
    );

    // ⚑ **AN EXPLICIT CIRCUIT PATH — so a key can be derived for a rung this crate does not CARRY.**
    // The two carried fixtures (`w3_branch`, `w4_bind`) exist for `mina-vk-derivation-gate.sh`'s
    // drift `cmp`, and they are the two smallest. Every other rung lives in the emitter's own output
    // directory, and copying a 4 MB fixture in here to derive one key would be a second copy with
    // nothing keeping it fresh — the exact shape of the drift the gate exists to catch.
    //
    // ⚠ This derives and writes ONE key and returns; the movement gate below is deliberately not
    // run, because its perturbation is defined against `w4_bind`.
    if let Some(i) = args.iter().position(|a| a == "--circuit") {
        let p = PathBuf::from(args.get(i + 1).unwrap_or_else(|| usage()));
        let c = load(&p);
        match curve {
            Curve::Pallas => {
                let d = derive(&c, log2);
                report("--circuit", &d);
                println!("  hash {}", d.mina_vk().hash());
                let path = write_vk(&out, &format!("vk-{}", c.name), &d);
                println!("  wrote {}", path.display());
            }
            Curve::Vesta => {
                let d = derive_step(&c, log2);
                report("--circuit", &d);
                // ⚑ REFUSAL #3 — a Vesta-committed key is NOT a Mina side-loaded VK. The wire object
                // holds Fp coordinates, i.e. PALLAS points, and a zkApp account stores the WRAP key.
                // The commitments are real and are reported; the 1796-byte encoding is refused
                // rather than emitted for the wrong group.
                let p = out.join(format!("commitments-{}.json", c.name));
                let v = serde_json::json!({
                    "curve": "vesta",
                    "note": "STEP-side commitments. NOT a Mina Side_loaded_verification_key: that                              object encodes Pallas points (Fp coordinates) and a zkApp account                              stores the WRAP key. No base64 `data` field is emitted, deliberately.",
                    "derivedFrom": {
                        "lean_module": "Dregg2.Circuit.Emit.KimchiStepMain",
                        "circuit": d.circuit,
                        "lean_rows": d.lean_rows,
                        "padded_rows": d.padded_rows,
                        "public_input_size": d.public,
                        "log2_domain": d.log2_domain,
                        "max_poly_size": TICK_MAX_POLY_SIZE,
                    },
                    "commitments": d.comms.iter().enumerate()
                        .map(|(i,(x,y))| (COMM_NAMES[i].to_string(),
                            serde_json::json!({"x": x.to_string(), "y": y.to_string()})))
                        .collect::<BTreeMap<_,_>>(),
                });
                std::fs::write(&p, serde_json::to_string_pretty(&v).unwrap() + "\n").unwrap();
                println!(
                    "  wrote {} (commitments only — see the note in the file)",
                    p.display()
                );
            }
        }
        return;
    }

    if curve == Curve::Vesta {
        eprintln!(
            "REFUSED: the carried fixtures are WRAP rungs (Pallas/Fq). Pass --circuit <path> to a \
             step-side emission rather than deriving a Vesta key from a wrap gate list."
        );
        std::process::exit(2);
    }

    let mut written = Vec::new();
    let mut derivations: Vec<(String, Derived<Wrap>)> = Vec::new();

    for rung in ["w3_branch", "w4_bind"] {
        let c = load_wrapmain(rung);
        let t = Instant::now();
        let d = derive(&c, log2);
        report(rung, &d);
        println!("  hash {}  — {:?}", d.mina_vk().hash(), t.elapsed());
        written.push(write_vk(&out, &format!("vk-wrapmain-{rung}"), &d));
        derivations.push((rung.to_string(), d));
    }

    // The movement gate: one coefficient of one Lean-emitted gate, +1.
    let base = load_wrapmain("w4_bind");
    let row = base
        .gates
        .iter()
        .position(|g| g.typ == 2)
        .expect("w4_bind has Poseidon rows");
    let pert = perturb_coefficient(&base, row, 0);
    let dp = derive(&pert, log2);
    println!("\nperturbed w4_bind gate row {row} coefficient 0 (+1):");
    let d4 = &derivations.iter().find(|(k, _)| k == "w4_bind").unwrap().1;
    let moved: Vec<&str> = (0..28)
        .filter(|i| d4.comms[*i] != dp.comms[*i])
        .map(|i| COMM_NAMES[i])
        .collect();
    println!(
        "  commitments that MOVED ({}/28): {}",
        moved.len(),
        moved.join(" ")
    );
    println!(
        "  commitments that held ({}/28): {}",
        28 - moved.len(),
        (0..28)
            .filter(|i| d4.comms[*i] == dp.comms[*i])
            .map(|i| COMM_NAMES[i])
            .collect::<Vec<_>>()
            .join(" ")
    );
    println!("  hash {} -> {}", d4.mina_vk().hash(), dp.mina_vk().hash());
    written.push(write_vk(&out, "vk-wrapmain-w4_bind-perturbed", &dp));

    println!("\nwrote:");
    for p in &written {
        println!("  {}", p.display());
    }
    println!("\nNEXT: node bridge/mina-zkapp/scripts/mina-vk-parse-gate.mjs \\");
    for p in &written {
        println!("        --vk {} \\", p.display());
    }
    println!("        --self-test");
}

// =================================================================================================
// tests — green or bust
// =================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(serde::Deserialize)]
    struct RefVk {
        data: String,
        hash: String,
    }

    /// Three verification keys produced by o1js 2.15.0 itself: two from `.compile()` on ZkPrograms
    /// that differ by one constraint, and `VerificationKey.dummySync()`. Regenerate with
    ///   node bridge/mina-zkapp/scripts/mina-vk-parse-gate.mjs --reference-dump <this file>
    fn reference_vks() -> BTreeMap<String, RefVk> {
        // `PICKLES_VK_REF_FIXTURE` exists ONLY so the gate's `--self-test` can point at a corrupted
        // COPY in a temp dir and watch these tests go red. It must never rewrite the tracked fixture:
        // the working tree is shared with other lanes.
        let p = match std::env::var_os("PICKLES_VK_REF_FIXTURE") {
            Some(v) => PathBuf::from(v),
            None => own_fixtures_dir().join("o1js-reference-vks.json"),
        };
        serde_json::from_str(&std::fs::read_to_string(&p).unwrap()).unwrap()
    }

    /// t1 — the wire layout is REPRODUCED, not described. Decode three keys o1js emitted, re-encode,
    /// and require byte identity. This is a diff against an INDEPENDENT source: o1js's OCaml binprot
    /// writer wrote those bytes and this file never saw them until now.
    #[test]
    fn t1_o1js_reference_vks_round_trip_byte_identically() {
        for (name, r) in reference_vks() {
            let raw = b64_decode(&r.data).unwrap();
            assert_eq!(
                raw.len(),
                VK_WIRE_LEN,
                "{name}: o1js vk.data is not {VK_WIRE_LEN} bytes"
            );
            let vk = WrapVk::decode(&raw).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert_eq!(vk.encode(), raw, "{name}: re-encode is not byte-identical");
            assert_eq!(vk.to_base64(), r.data, "{name}: base64 round-trip differs");
            for (i, (x, y)) in vk.comms.iter().enumerate() {
                assert!(on_pallas(*x, *y), "{name}: {} is off Pallas", COMM_NAMES[i]);
            }
        }
    }

    /// t2 — the HASH is reproduced from an independent implementation. o1js computes
    /// `inCircuitVkHash` through its OCaml bindings; this crate computes it from `mina-poseidon`
    /// and the layout in the header. They must agree on all three keys.
    /// mina-rust has no equivalent cross-implementation pin (its hash path is only self-consistent).
    #[test]
    fn t2_rust_hash_reproduces_the_o1js_vk_hash() {
        for (name, r) in reference_vks() {
            let vk = WrapVk::from_base64(&r.data).unwrap();
            assert_eq!(
                vk.hash().to_string(),
                r.hash,
                "{name}: VK hash disagrees with o1js"
            );
        }
    }

    /// t3 — a VK DERIVED from Lean-emitted gates is well-formed on the wire.
    #[test]
    fn t3_derived_vk_is_wellformed() {
        let d = derive(&load_wrapmain("w4_bind"), None);
        assert_eq!(d.lean_rows, d.padded_rows, "no padding was asked for");
        let raw = d.mina_vk().encode();
        assert_eq!(raw.len(), VK_WIRE_LEN);
        let back = WrapVk::decode(&raw).expect("the derived key decodes under the strict reader");
        assert_eq!(back, d.mina_vk());
        for (i, (x, y)) in d.comms.iter().enumerate() {
            assert!(on_pallas(*x, *y), "{} is off Pallas", COMM_NAMES[i]);
            assert!(
                !(x.is_zero() && y.is_zero()),
                "{} is the identity",
                COMM_NAMES[i]
            );
        }
    }

    /// t4 — THE DERIVATION IS REAL. Perturb ONE coefficient of ONE Lean-emitted gate and the key
    /// must move; and it must move in the RIGHT places — a coefficient column commitment is a
    /// function of the coefficients, the permutation commitments are not.
    #[test]
    fn t4_perturbing_one_gate_coefficient_moves_the_vk() {
        let c = load_wrapmain("w4_bind");
        let base = derive(&c, None);
        let row = c.gates.iter().position(|g| g.typ == 2).unwrap();
        let pert = derive(&perturb_coefficient(&c, row, 0), None);

        assert_ne!(
            base.mina_vk(),
            pert.mina_vk(),
            "one coefficient moved and the VK did not"
        );
        assert_ne!(
            base.mina_vk().hash(),
            pert.mina_vk().hash(),
            "the VK hash did not move"
        );

        let moved: Vec<usize> = (0..28)
            .filter(|i| base.comms[*i] != pert.comms[*i])
            .collect();
        // Exactly coefficients_comm[0] moves: the gate's other coefficient columns, all selector
        // polynomials and the whole permutation are untouched by a change to coefficient 0.
        assert_eq!(
            moved.iter().map(|i| COMM_NAMES[*i]).collect::<Vec<_>>(),
            vec!["coeff[0]"],
            "a change to coefficient 0 of one row moved the wrong set of commitments"
        );
        // and it must move by exactly the Lagrange basis element of that row, scaled by 1.
        // (Left as the weaker statement: the point simply differs. The exact-delta check would
        // require re-deriving the Lagrange basis here, which would be a pin against our own SRS.)
    }

    /// t10 — a WIRE moved, not a coefficient. The copy-permutation is a different lever on the key
    /// than the coefficients are, and it must move the sigma commitments and leave every selector
    /// commitment alone. A derivation that moved on coefficients but not on wiring would be reading
    /// half the circuit.
    #[test]
    fn t10_perturbing_one_wire_moves_the_sigma_commitments() {
        let c = load_wrapmain("w4_bind");
        let base = derive(&c, None);
        // Find a row/col whose wire actually points somewhere else, so the edit is a real change.
        let (row, col) = c
            .gates
            .iter()
            .enumerate()
            .find_map(|(r, g)| (0..7).find(|cc| g.wires[*cc] != [r, *cc]).map(|cc| (r, cc)))
            .expect("w4_bind has at least one non-self wire");
        let pert = derive(&perturb_wire(&c, row, col), None);
        assert_ne!(
            base.mina_vk(),
            pert.mina_vk(),
            "a wire moved and the VK did not"
        );

        let moved: Vec<&str> = (0..28)
            .filter(|i| base.comms[*i] != pert.comms[*i])
            .map(|i| COMM_NAMES[i])
            .collect();
        assert!(!moved.is_empty(), "no commitment moved");
        assert!(
            moved.iter().all(|n| n.starts_with("sigma[")),
            "a wire edit moved something other than sigma: {moved:?}"
        );
        // and it must be sigma[col] specifically: `sigma_comm[i]` commits to the permutation of
        // COLUMN i, and the edited cell is in column `col`. (Whether any OTHER sigma also moves
        // depends on which column the cell that used to point here lives in, so nothing stronger
        // than this is derivable — an earlier draft of this test asserted `moved.len() >= 2` from
        // intuition and it was false: a class entirely inside column 0 moves sigma[0] alone.)
        assert!(
            moved.contains(&COMM_NAMES[col]),
            "editing a wire in column {col} did not move sigma[{col}]: {moved:?}"
        );
    }

    /// t11 — a GATE TYPE retyped. Selector commitments are a function of the type column alone, so
    /// this must move selectors and leave every coefficient and permutation commitment alone.
    #[test]
    fn t11_retyping_one_gate_moves_the_selector_commitments() {
        let c = load_wrapmain("w4_bind");
        let base = derive(&c, None);
        // A Generic row -> Zero: `generic` loses a row, and no other selector gains one.
        let row = c
            .gates
            .iter()
            .position(|g| g.typ == 1)
            .expect("w4_bind has Generic rows");
        let pert = derive(&perturb_gate_type(&c, row, 0), None);
        assert_ne!(
            base.mina_vk(),
            pert.mina_vk(),
            "a gate type changed and the VK did not"
        );

        let moved: Vec<&str> = (0..28)
            .filter(|i| base.comms[*i] != pert.comms[*i])
            .map(|i| COMM_NAMES[i])
            .collect();
        assert!(
            moved.contains(&"generic"),
            "retyping a Generic row did not move generic_comm: {moved:?}"
        );
        assert!(
            moved.iter().all(|n| !n.starts_with("sigma[")),
            "retyping a gate moved the permutation: {moved:?}"
        );
    }

    /// t5 — two DIFFERENT Lean circuits give two different keys, and the domain is HELD FIXED so
    /// the difference is entirely the circuit.
    ///
    /// ⚠ ⚑ **THIS TEST WAS RED AT HEAD AND THE REASON IS THE INTERESTING PART.** It used to derive
    /// both rungs at their NATURAL domain and assert the two domains were EQUAL, over a comment
    /// reading "w3 is 483 rows and w4 is 492; both land in the 2^9 domain". `9413a4bd3` re-emitted
    /// the fixtures — w3 is 489 rows and w4 is **532** — and 532 does not fit 2^9. The assertion was
    /// never about the derivation; it was a note about two fixture sizes, and a re-emission
    /// invalidated it silently. Holding the domain with `Some(14)` states the intended fact
    /// (same SRS, same domain, different circuit) instead of hoping two row counts stay on the same
    /// side of a power of two.
    #[test]
    fn t5_different_lean_circuits_give_different_vks() {
        let a = derive(&load_wrapmain("w3_branch"), Some(14));
        let b = derive(&load_wrapmain("w4_bind"), Some(14));
        assert_eq!(a.log2_domain, 14, "w3 was not padded into 2^14");
        assert_eq!(b.log2_domain, 14, "w4 was not padded into 2^14");
        assert_ne!(a.mina_vk(), b.mina_vk());
        assert_ne!(a.mina_vk().hash(), b.mina_vk().hash());
        // …and the natural domains DO differ, which is what made the old form of this test fall
        // over. Recorded rather than assumed.
        assert_eq!(derive(&load_wrapmain("w3_branch"), None).log2_domain, 9);
        assert_eq!(derive(&load_wrapmain("w4_bind"), None).log2_domain, 10);
    }

    /// ⚑ t12 — **THE LANE IS DECLARED, AND THE PARSER REFUSES THE WRONG ONE.** The two pasta primes
    /// differ above bit 128 and `p < q`, so the window `[p, q)` holds exactly the wrap-side values a
    /// step-side reader would have silently reduced. A coefficient in that window is refused by the
    /// shared reader rather than wrapped; below it, NOTHING in the artifact distinguishes the two
    /// fields, which is why `--curve` exists and has no default.
    #[test]
    fn t12_a_wrong_field_coefficient_is_refused_not_reduced() {
        use ark_ff::BigInteger as _;
        let p: num_bigint::BigUint =
            num_bigint::BigUint::from_bytes_le(&<Fp as PrimeField>::MODULUS.to_bytes_le());
        let q: num_bigint::BigUint =
            num_bigint::BigUint::from_bytes_le(&<Fq as PrimeField>::MODULUS.to_bytes_le());
        assert!(p < q, "Fp's modulus is the smaller pasta prime");
        let in_window = ((&p + &q) / 2u32).to_string();

        // The wrap lane (Fq) takes it; the step lane (Fp) REFUSES it.
        assert!(pickles_circuit_driver::try_parse_field::<Fq>(&in_window).is_ok());
        assert!(pickles_circuit_driver::try_parse_field::<Fp>(&in_window).is_err());

        // …and it is refused THROUGH the derivation, not merely in a helper: a wrap circuit whose
        // coefficient lands in the window cannot be derived on the step lane.
        let mut c = load_wrapmain("w4_bind");
        let row = c.gates.iter().position(|g| !g.coeffs.is_empty()).unwrap();
        c.gates[row].coeffs[0] = in_window;
        assert!(
            std::panic::catch_unwind(move || { pickles_circuit_driver::build_gates::<Fp>(&c) })
                .is_err(),
            "an Fq-window coefficient was accepted on the step lane — it would have been REDUCED"
        );
    }

    /// ⚑ t13 — **`--curve` IS PARSED, NOT GUESSED**, and a step key is not a Mina side-loaded VK.
    /// `Derived<Step>` has no `mina_vk`, so the 1796-byte encoding cannot be produced for a
    /// Vesta-committed circuit at all — this asserts the runtime half (the tag a wrap key would
    /// declare is held at `None` on the step lane) since the wire half is a type error.
    #[test]
    fn t13_the_curve_is_declared_and_a_step_key_is_not_a_mina_vk() {
        assert_eq!(Curve::parse("pallas"), Ok(Curve::Pallas));
        assert_eq!(Curve::parse("wrap"), Ok(Curve::Pallas));
        assert_eq!(Curve::parse("vesta"), Ok(Curve::Vesta));
        assert_eq!(Curve::parse("step"), Ok(Curve::Vesta));
        assert!(Curve::parse("").is_err());
        assert!(Curve::parse("bn254").is_err());
        assert_eq!(Curve::Pallas.max_poly_size(), TOCK_MAX_POLY_SIZE);
        assert_eq!(Curve::Vesta.max_poly_size(), TICK_MAX_POLY_SIZE);
        assert_ne!(
            TOCK_MAX_POLY_SIZE, TICK_MAX_POLY_SIZE,
            "Tick and Tock max_poly_size are not interchangeable"
        );

        // ⚑ THE STEP LANE RUNS. A circuit whose coefficients are all canonical for BOTH primes
        // derives on either, which is precisely the ambiguity `--curve` resolves — and the step
        // derivation produces Fq coordinates, on the wrong group for a side-loaded VK.
        let c = load_wrapmain("w3_branch"); // coeff-free rung: canonical in both fields
        let d = derive_step(&c, None);
        assert_eq!(
            d.wrap_domain_tag, None,
            "a Vesta derivation must never declare an actual_wrap_domain_size"
        );
        assert_eq!(d.curve, Curve::Vesta);
        assert_eq!(d.lean_rows, c.num_rows);
        let w = derive(&c, None);
        assert_eq!(
            w.log2_domain, d.log2_domain,
            "the same gate list lands in the same domain on either curve"
        );
        // The two derivations are DIFFERENT objects: the commitments live in different fields and
        // are computed over different SRSs. `x.to_string()` is the only comparison the types allow,
        // which is itself the point — nothing can accidentally treat one as the other.
        assert_ne!(
            d.comms[0].0.to_string(),
            w.comms[0].0.to_string(),
            "the step and wrap derivations of the same gate list must not coincide"
        );
    }

    /// t6 — the strict reader REFUSES what a Mina reader refuses. Each mutation below is re-run
    /// through o1js's own reader by `bridge/mina-zkapp/scripts/mina-vk-parse-gate.mjs`.
    #[test]
    fn t6_reader_refuses_malformed_keys() {
        let good = derive(&load_wrapmain("w3_branch"), None).mina_vk().encode();
        assert!(WrapVk::decode(&good).is_ok());

        let mut off_curve = good.clone();
        off_curve[2] = off_curve[2].wrapping_add(1);
        assert!(
            WrapVk::decode(&off_curve).is_err(),
            "an off-curve sigma[0] was accepted"
        );

        assert!(
            WrapVk::decode(&good[..good.len() - 1]).is_err(),
            "a truncated key was accepted"
        );

        let mut bad_nil = good.clone();
        bad_nil[2 + 7 * 64] = 1;
        assert!(
            WrapVk::decode(&bad_nil).is_err(),
            "a non-zero Vector nil was accepted"
        );

        let mut bad_nil2 = good.clone();
        bad_nil2[2 + 7 * 64 + 1 + 15 * 64] = 1;
        assert!(
            WrapVk::decode(&bad_nil2).is_err(),
            "a non-zero second Vector nil was accepted"
        );

        // x = p, the modulus itself: a non-canonical limb.
        let mut noncanon = good.clone();
        let p = <Fp as PrimeField>::MODULUS.to_bytes_le();
        noncanon[2..34].copy_from_slice(&p[..32]);
        assert!(
            WrapVk::decode(&noncanon).is_err(),
            "a limb equal to p was accepted"
        );

        let mut bad_tag = good.clone();
        bad_tag[0] = 3;
        assert!(
            WrapVk::decode(&bad_tag).is_err(),
            "Proofs_verified tag 3 was accepted"
        );
    }

    /// t7 — the derivation is a function of the circuit alone.
    #[test]
    fn t7_derivation_is_deterministic() {
        let c = load_wrapmain("w3_branch");
        assert_eq!(derive(&c, None).mina_vk(), derive(&c, None).mina_vk());
    }

    /// t9 — the key never declares a wrap domain it does not have. The declared tag is the INVERSE
    /// of `wrap_domains` applied to the domain the constraint system actually landed in, and a
    /// circuit padded to 2^14 must say N1 — not the N2 that Mina's own transaction wrap says.
    #[test]
    fn t9_declared_wrap_domain_is_the_derived_one() {
        let d = derive(&load_wrapmain("w3_branch"), Some(14));
        assert_eq!(
            d.log2_domain, 14,
            "padding did not land the circuit in 2^14"
        );
        assert_eq!(
            d.wrap_domain_tag,
            Some(1),
            "2^14 inverts to N1 under wrap_domains"
        );
        assert_eq!(d.mina_vk().actual_wrap_domain_size, 1);
        assert_eq!(
            d.mina_vk().max_proofs_verified,
            1,
            "the two tags must not contradict each other"
        );
        // The unpadded circuit lands in a domain no tag can name, and that must be REFUSED, not
        // rounded to something plausible.
        let nat = derive(&load_wrapmain("w3_branch"), None);
        assert_eq!(
            nat.wrap_domain_tag, None,
            "2^{} is not nameable",
            nat.log2_domain
        );
        // ...and padding is not free: it changes the committed columns, so the key moves.
        assert_ne!(
            nat.comms, d.comms,
            "padding to a different domain left the key unchanged"
        );
    }

    /// t8 — the prefix field is the one o1js uses. Pinned against o1js's own constant, which is the
    /// STRING; this recomputes the field element from it rather than transcribing a number.
    #[test]
    fn t8_sideloaded_prefix_is_the_o1js_constant() {
        // "MinaSideLoadedVk****" little-endian, zero padded — the first limb is the ASCII.
        let f = sideloaded_vk_prefix_field();
        let le = fp_le(&f);
        assert_eq!(&le[..20], b"MinaSideLoadedVk****");
        assert!(le[20..].iter().all(|b| *b == 0));
    }
}
