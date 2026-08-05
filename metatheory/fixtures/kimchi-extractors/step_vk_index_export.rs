//! W-KEY index-commitment export, from **MINA'S OWN STEP CIRCUIT**.
//!
//! ⚑ WHY THIS EXISTS, AND WHAT IT REPLACES. `wrap_key_index_export.rs` (its sibling) dumps the 28
//! index commitments of kimchi's **own generic-gate test circuit** — `create_circuit(0, 5)` through
//! `new_index_for_test_with_lookups`. That circuit has no Poseidon, no CompleteAdd, no VarBaseMul,
//! no EndoMul and no EndoMulScalar row, and it writes only 8 of the 15 coefficient columns. Seven of
//! its `coefficients_comm` are therefore commitments to the ZERO polynomial, and
//! `verifier_index.rs:230-238` commits `sigma_comm` and `coefficients_comm` with
//! `commit_evaluations_non_hiding` — UNMASKED — so a zero column lands on the POINT AT INFINITY.
//! (The six selector commitments below them go through `mask_fixed`, blinder 1, so a zero selector
//! lands on the SRS blinding base `h` instead, which is why five of them are the same point.)
//!
//! `Pickles_base.Side_loaded_verification_key.index_to_field_elements` flattens the identity as the
//! FAKE POINT `(0, 0)` — `DefaultFqSponge::absorb_g` does — and the wrap circuit's W-COMBINE folds
//! those 28 points with `Ops.add_fast`, the INCOMPLETE add. A chord through `(0, 0)` leaves the
//! curve, so at that key `combined_polynomial` is an off-curve pair, and everything downstream of it
//! — `p_prime`, `q`, `cq`, `lhs` — inherits it. `wrap_main.ml:419`'s
//! `Boolean.Assert.is_true bulletproof_success` then has no satisfying witness, because the honest
//! `G := z_1^{-1}(lhs - z_2 H) - b u` solve needs an ON-CURVE `lhs` to land on.
//!
//! THE FIX IS THE FIXTURE, NOT THE GADGET: use Mina's real step circuit. This binary reads o1-labs'
//! released `circuit-blobs` gate list for `step-transaction` (branch 0 of the transaction SNARK),
//! runs it through the SAME kimchi index builder, and dumps the same 56 coordinates. That circuit is
//! 17,806 rows with 4,851 Poseidon gates, so every coefficient column and every selector is live and
//! NO commitment is the identity.
//!
//! ## The three things that make this Mina's key and not a lookalike
//!
//! 1. **The gate list is o1-labs', not ours.** `*_gates.json` in the `circuit-blobs` releases is
//!    exactly kimchi's `Circuit { public_input_size, gates }` serde form — the bytes
//!    `caml_pasta_fp_plonk_circuit_serialize` emits — and mina-rust reads them with a five-line
//!    `serde_json::from_reader` (`ledger/src/proofs/provers.rs:38-49`). The md5 in the release
//!    filename IS the OCaml constraint-system digest, so the file names its own hash.
//! 2. **The SRS is Mina's.** `SRS::<G>::create(n)` is deterministic —
//!    `g[i] = point_of_random_bytes(Blake2b512(i_be))` — and it is the same code path
//!    `Kimchi_bindings.Protocol.SRS.Fp.create` runs inside Mina. kimchi's serialized *test* SRS is
//!    that same object: `precomputed_srs.rs`'s `heavy_test_srs_serialization` asserts
//!    `SRS::<Vesta>::create(1 << 16) == get_srs_test::<Vesta>()`. We pass
//!    `override_srs_size = Some(1 << 16)` — `Common.Max_degree.step` — so the commitments are taken
//!    against the STEP URS, at the size `wrap_main`'s `~srs` has.
//! 3. **It cross-checks against two values this file does not own.** The SRS blinding base `h` is
//!    asserted equal to `MinaStepSrsLagrange.URS_H_XY`, which a DIFFERENT binary
//!    (`pickles-wrapmain-harness/src/bin/xhat_lagrange_export.rs`) dumped on a different day. And
//!    — the sharp one — **all 56 derived coordinates are asserted to occur as gate coefficients of
//!    the `wrap-transaction` blob**, because `choose_key` (`wrap_verifier.ml:189-204`) holds the
//!    step keys as `Inner_curve.constant`, so Mina's own wrap circuit BAKES THIS KEY IN. Measured:
//!    56/56 against `wrap-transaction`'s 995 distinct coefficients, and **0/56 against
//!    `wrap-blockchain`'s 584** — which is the discrimination that makes it a check rather than a
//!    birthday coincidence, since the blockchain wrap wraps the blockchain step rules and not this
//!    one. The old test-circuit key scores **0/42 against both**.
//!
//! ⚠ WHAT THIS IS NOT. There is no independently published Mina STEP verification key to diff
//! against — openmina ships wrap verifier indices only (`devnet_{transaction,blockchain}_
//! verifier_index.json`). What validates the derivation is (a) the wrap-coefficient tie above and
//! (b) that the SAME pipeline, run on the two released WRAP gate blobs, reproduces openmina's
//! shipped wrap VKs' 28 commitments byte-for-byte. So: the gate list is Mina's, the SRS is Mina's,
//! the index builder is kimchi's, and Mina's own wrap circuit contains the answer. It is not a
//! byte-diff against a published step key, because none is published.
//!
//! Run (blob dir defaults to mina-rust's own resolution order):
//!   cargo run --release --bin step_vk_index_export -p kimchi-reality-gate-extractors \
//!     > metatheory/kimchi_step_key_index.json

use std::path::PathBuf;

use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::{GateWires, Wire, COLUMNS, PERMUTS},
    },
    curve::KimchiCurve,
    prover_index::testing::new_index_for_test_with_lookups,
};
use mina_curves::pasta::{Fp, Fq, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, sponge::DefaultFqSponge,
    FqSponge as _,
};
use num_bigint::BigUint;
use poly_commitment::commitment::PolyComm;

type SpongeParams = PlonkSpongeConstantsKimchi;
type BaseSponge = DefaultFqSponge<VestaParameters, SpongeParams, FULL_ROUNDS>;

/// `Common.Max_degree.step = 1 lsl Backend.Tick.Rounds.n`, `Rounds.n = 16` (`common.ml:6-9`).
/// `wrap_main`'s `~srs` is `Backend.Tick.Keypair.load_urs ()`, an SRS of exactly this size.
const TICK_MAX_POLY_SIZE: usize = 1 << 16;

/// `Pickles_types.Nat.N2` — every Mina step rule carries two previous proofs.
const PREV_CHALLENGES: usize = 2;

/// The release asset. The md5 is the OCaml `Md5.digest_bytes` of kimchi's `CryptoDigest`, i.e. the
/// file names its own constraint-system hash (`PICKLES-SYNTHESIS-EPOCH-SCOPE.md` §13.2).
const STEP_BLOB: &str =
    "step-step-proving-key-transaction-snark-transaction-0-c33ec5211c07928c87e850a63c6a2079_gates.json";
const STEP_BLOB_MD5: &str = "c33ec5211c07928c87e850a63c6a2079";
/// The wrap circuit that VERIFIES the step rule above — and therefore holds its key as constants.
const WRAP_T_BLOB: &str =
    "wrap-wrap-proving-key-transaction-snark-b9a01295c8cc9bda6d12142a581cd305_gates.json";
/// The OTHER wrap. Its step rules are the blockchain ones, so it must hold NONE of these constants;
/// without this leg the 56/56 above would be an unfalsifiable coincidence.
const WRAP_B_BLOB: &str =
    "wrap-wrap-proving-key-blockchain-snark-bbecaf158ca543ec8ac9e7144400e669_gates.json";
/// `StepTransactionProof` (`ledger/src/proofs/constants.rs:81-107`) — openmina's independently
/// transcribed constants for this very circuit.
const STEP_ROWS: usize = 17806;
const STEP_PUBLIC: usize = 67;

/// `MinaStepSrsLagrange.URS_H_XY` — `Generators.h`, dumped by a different binary on a different day.
const URS_H_XY: [&str; 2] = [
    "4128018831155263258921677689761735101256426860488784731125497417640507220481",
    "22304269070532896717707344537995120070212833580943367087267197592645043797542",
];

fn fq_dec(x: Fq) -> String {
    BigUint::from(x.into_bigint()).to_string()
}

/// `~g z = List.to_array (Inner_curve.to_field_elements z)` — the affine `(x, y)`.
/// ⚠ `DefaultFqSponge::absorb_g` absorbs the FAKE POINT `(0, 0)` for the point at infinity, so an
/// identity commitment still contributes two coordinates. Counting them is the whole point here.
fn point_xy(c: &PolyComm<Vesta>, n_inf: &mut usize) -> Vec<Fq> {
    assert_eq!(c.chunks.len(), 1, "index commitments are single-chunk");
    match c.chunks[0].xy() {
        Some((x, y)) => vec![x, y],
        None => {
            *n_inf += 1;
            vec![Fq::from(0u8), Fq::from(0u8)]
        }
    }
}

// ── o1-labs' released gate blob ──────────────────────────────────────────────────────────────────

#[derive(serde::Deserialize)]
struct BlobJson {
    public_input_size: usize,
    gates: Vec<BlobGate>,
}
#[derive(serde::Deserialize)]
struct BlobGate {
    typ: String,
    wires: Vec<BlobWire>,
    coeffs: Vec<String>,
}
#[derive(serde::Deserialize)]
struct BlobWire {
    row: usize,
    col: usize,
}

fn gate_type_named(s: &str) -> GateType {
    match s {
        "Zero" => GateType::Zero,
        "Generic" => GateType::Generic,
        "Poseidon" => GateType::Poseidon,
        "CompleteAdd" => GateType::CompleteAdd,
        "VarBaseMul" => GateType::VarBaseMul,
        "EndoMul" => GateType::EndoMul,
        "EndoMulScalar" => GateType::EndoMulScalar,
        other => panic!("Mina's step circuit uses seven gate types; got {other:?}"),
    }
}

/// 32-byte LITTLE-ENDIAN canonical hex -> Fp. ⚑ `Fp`, not `Fq`: a step circuit's native field is
/// `Tick.Field = Fp`. Its COMMITMENTS are Vesta points whose coordinates are Fq, which is why the
/// wrap circuit — whose own field is Fq — can hold them as constants without any foreign-field
/// arithmetic.
fn fp_from_le_hex(s: &str) -> Fp {
    let raw: Vec<u8> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex digit"))
        .collect();
    assert_eq!(raw.len(), 32, "coefficient is not 32 bytes");
    let mut limbs = [0u64; 4];
    for (i, l) in limbs.iter_mut().enumerate() {
        *l = u64::from_le_bytes(raw[i * 8..i * 8 + 8].try_into().unwrap());
    }
    Fp::from_bigint(ark_ff::BigInt::new(limbs)).expect("canonical Fp element")
}

fn blob_path(name: &str) -> PathBuf {
    // mina-rust's own resolution order (`circuit_blobs.rs:126-152`), minus the network fetch: this
    // binary refuses rather than downloading, so the input is always a file someone can point at.
    if let Ok(dir) = std::env::var("MINA_CIRCUIT_BLOBS_BASE_DIR") {
        return PathBuf::from(dir).join(name);
    }
    let home = std::env::var("HOME").expect("HOME");
    PathBuf::from(home)
        .join(".mina/circuit-blobs/berkeley-devnet")
        .join(name)
}

fn read_blob(name: &str) -> BlobJson {
    let path = blob_path(name);
    serde_json::from_reader(std::io::BufReader::new(
        std::fs::File::open(&path).unwrap_or_else(|e| {
            panic!(
                "open {}: {e}\nFetch it from \
                 https://github.com/o1-labs/circuit-blobs/releases/download/berkeley-devnet/ \
                 or set MINA_CIRCUIT_BLOBS_BASE_DIR.",
                path.display()
            )
        }),
    ))
    .expect("the release asset is kimchi's Circuit serde form")
}

/// Every distinct gate coefficient of a blob, as an Fq element. ⚑ The blob's coefficients are the
/// STEP circuit's own field (Fp) in the step blob, but a WRAP blob's are Fq — and a step key's
/// coordinates ARE Fq, which is the whole reason `choose_key` can hold them as constants. So this
/// reads a wrap blob's coefficients in the field they already live in; no reduction happens.
fn wrap_coefficient_set(name: &str) -> std::collections::HashSet<Fq> {
    read_blob(name)
        .gates
        .iter()
        .flat_map(|g| g.coeffs.iter())
        .map(|s| {
            let raw: Vec<u8> = (0..s.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex digit"))
                .collect();
            let mut limbs = [0u64; 4];
            for (i, l) in limbs.iter_mut().enumerate() {
                *l = u64::from_le_bytes(raw[i * 8..i * 8 + 8].try_into().unwrap());
            }
            Fq::from_bigint(ark_ff::BigInt::new(limbs)).expect("canonical Fq element")
        })
        .collect()
}

fn main() {
    let blob = read_blob(STEP_BLOB);

    // ---- the blob IS the circuit openmina independently transcribed ----
    assert_eq!(
        blob.public_input_size, STEP_PUBLIC,
        "not step-transaction: PRIMARY_LEN"
    );
    assert_eq!(blob.gates.len(), STEP_ROWS, "not step-transaction: ROWS");

    let gates: Vec<CircuitGate<Fp>> = blob
        .gates
        .iter()
        .enumerate()
        .map(|(row, g)| {
            assert_eq!(g.wires.len(), PERMUTS, "row {row}: 7 permutable columns");
            let mut w: GateWires = std::array::from_fn(|_| Wire { row: 0, col: 0 });
            for (i, rc) in g.wires.iter().enumerate() {
                w[i] = Wire {
                    row: rc.row,
                    col: rc.col,
                };
            }
            let coeffs: Vec<Fp> = g.coeffs.iter().map(|s| fp_from_le_hex(s)).collect();
            CircuitGate::new(gate_type_named(&g.typ), w, coeffs)
        })
        .collect();

    // ---- the index. `disable_gates_checks` because we hold a circuit and no witness; it is a
    // witness-time flag and does not enter a single commitment.
    let index = new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
        gates,
        blob.public_input_size,
        PREV_CHALLENGES,
        vec![],
        None,
        /* disable_gates_checks */ true,
        Some(TICK_MAX_POLY_SIZE),
        /* lazy_mode */ false,
    );
    let vi = index.verifier_index();

    assert_eq!(vi.max_poly_size, TICK_MAX_POLY_SIZE);
    assert_eq!(vi.prev_challenges, PREV_CHALLENGES);
    assert_eq!(vi.public, STEP_PUBLIC);

    // ---- the SRS is the one `MinaStepSrsLagrange` already grounds the x_hat MSM against ----
    let (hx, hy) = index.srs.h.xy().expect("the blinding base is not infinity");
    assert_eq!(
        [fq_dec(hx), fq_dec(hy)],
        [URS_H_XY[0].to_string(), URS_H_XY[1].to_string()],
        "this index was NOT committed against the step URS MinaStepSrsLagrange dumped"
    );

    // ---- the 28 points ARE the whole absorb list: no optional gate, no lookup index ----
    assert!(
        vi.range_check0_comm.is_none()
            && vi.range_check1_comm.is_none()
            && vi.foreign_field_add_comm.is_none()
            && vi.foreign_field_mul_comm.is_none()
            && vi.xor_comm.is_none()
            && vi.rot_comm.is_none()
            && vi.lookup_index.is_none(),
        "digest would absorb more than the 28 Pickles index points"
    );
    assert_eq!(vi.sigma_comm.len(), PERMUTS);
    assert_eq!(vi.coefficients_comm.len(), COLUMNS);

    // ---- index_to_field_elements order (side_loaded_verification_key.ml:159-183) ----
    let mut coords: Vec<Fq> = vec![];
    let mut n_inf: usize = 0;
    for c in vi.sigma_comm.iter() {
        coords.extend(point_xy(c, &mut n_inf));
    }
    for c in vi.coefficients_comm.iter() {
        coords.extend(point_xy(c, &mut n_inf));
    }
    for c in [
        &vi.generic_comm,
        &vi.psm_comm,
        &vi.complete_add_comm,
        &vi.mul_comm,
        &vi.emul_comm,
        &vi.endomul_scalar_comm,
    ] {
        coords.extend(point_xy(c, &mut n_inf));
    }
    assert_eq!(coords.len(), 2 * (PERMUTS + COLUMNS + 6));

    // ---- ⚑ THE WHOLE REASON THIS BINARY EXISTS ----
    assert_eq!(
        n_inf, 0,
        "a step key with an identity commitment poisons W-COMBINE's add_fast fold — see the header"
    );

    // ---- ⚑ AND THE TIE THAT MAKES IT MINA'S: the wrap circuit that verifies this rule holds these
    // 56 numbers as `Inner_curve.constant` coefficients, and the OTHER wrap holds none of them.
    let wt = wrap_coefficient_set(WRAP_T_BLOB);
    let wb = wrap_coefficient_set(WRAP_B_BLOB);
    let in_wt = coords.iter().filter(|c| wt.contains(c)).count();
    let in_wb = coords.iter().filter(|c| wb.contains(c)).count();
    assert_eq!(
        in_wt,
        coords.len(),
        "wrap-transaction does not bake in this key: only {in_wt}/{} coordinates occur among its \
         {} distinct coefficients",
        coords.len(),
        wt.len()
    );
    assert_eq!(
        in_wb, 0,
        "wrap-blockchain bakes in {in_wb} of these coordinates — the tie above does not discriminate"
    );

    // ---- the digest, and an INDEPENDENT replay over exactly those 56 coordinates ----
    let vk_digest: Fq = vi.digest::<BaseSponge>();
    let mut replay = BaseSponge::new(Vesta::other_curve_sponge_params());
    replay.absorb_fq(&coords);
    assert_eq!(
        fq_dec(replay.digest_fq()),
        fq_dec(vk_digest),
        "absorbing the 56 index_to_field_elements coordinates is NOT the index digest"
    );

    eprintln!(
        "[ground truth] {} rows, {} public, domain 2^{}, {n_inf} of 28 points at infinity; \
         wrap-transaction bakes in {in_wt}/{} of the coordinates ({} distinct coefficients), \
         wrap-blockchain {in_wb}/{} ({} distinct)",
        STEP_ROWS,
        STEP_PUBLIC,
        vi.domain.log_size_of_group,
        coords.len(),
        wt.len(),
        coords.len(),
        wb.len()
    );

    println!("{{");
    println!("  \"source\": \"o1-labs/circuit-blobs berkeley-devnet {STEP_BLOB}\",");
    println!("  \"source_md5\": \"{STEP_BLOB_MD5}\",");
    println!("  \"circuit\": \"step-transaction (branch 0 of the transaction SNARK)\",");
    println!("  \"rows\": {STEP_ROWS},");
    println!("  \"public_input_size\": {STEP_PUBLIC},");
    println!("  \"prev_challenges\": {PREV_CHALLENGES},");
    println!("  \"max_poly_size\": {TICK_MAX_POLY_SIZE},");
    println!("  \"domain_log2\": {},", vi.domain.log_size_of_group);
    println!("  \"zk_rows\": {},", vi.zk_rows);
    println!("  \"optional_gate_and_lookup_comms_absent\": true,");
    println!("  \"n_points\": {},", PERMUTS + COLUMNS + 6);
    println!("  \"n_points_at_infinity\": {n_inf},");
    println!("  \"srs_h_is_the_step_urs_h\": true,");
    println!("  \"coords_in_wrap_transaction_coefficients\": {in_wt},");
    println!("  \"coords_in_wrap_blockchain_coefficients\": {in_wb},");
    println!("  \"vk_digest\": \"{}\",", fq_dec(vk_digest));
    println!("  \"replay_of_56_coords_matches_digest\": true,");
    println!("  \"index_comm_xy\": [");
    for (i, c) in coords.iter().enumerate() {
        let comma = if i + 1 == coords.len() { "" } else { "," };
        println!("    \"{}\"{}", fq_dec(*c), comma);
    }
    println!("  ]");
    println!("}}");
}
