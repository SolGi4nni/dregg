//! W-KEY index-commitment export for breadstuffs `metatheory/Dregg2/Circuit/Emit/`.
//!
//! `wrap_verifier.ml:521-530` computes the wrap transcript's FIRST absorbed word as
//!
//!     index_digest = squeeze (absorb_all (index_to_field_elements step_plonk_index))
//!
//! and `Pickles_base.Side_loaded_verification_key.index_to_field_elements`
//! (`side_loaded_verification_key.ml:159-183`) flattens a `Plonk_verification_key_evals.t` as
//!
//!     sigma_comm[0..7) ++ coefficients_comm[0..15) ++
//!     [generic_comm; psm_comm; complete_add_comm; mul_comm; emul_comm; endomul_scalar_comm]
//!
//! with `~g z = [x; y]`. That is 28 points = 56 Fq coordinates.
//!
//! Rust kimchi's `VerifierIndex::digest` (`kimchi/src/verifier_index.rs:407-530`) absorbs the very
//! same eight fields in the very same order via `absorb_commitment` = `absorb_g(&chunks)`, plus the
//! OPTIONAL gate commitments and the lookup index WHEN PRESENT. This example rebuilds the index the
//! `pickles_p6_fq_export` fixture was taken from, ASSERTS that every optional commitment and the
//! lookup index are absent (so the 28 points ARE the whole absorb list), dumps the 56 coordinates in
//! `index_to_field_elements` order, and ASSERTS that `verifier_index.digest::<BaseSponge>()` equals
//! the `VKDIGEST` already recorded in `PastaPoseidonFq.lean` — which is what makes the dumped
//! coordinates the preimage of THAT digest and not of some other index.
//!
//! Run: cargo run --release --example wrap_key_index_export -p kimchi

use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use kimchi::{
    circuits::{
        polynomials::generic::testing::create_circuit,
        wires::{COLUMNS, PERMUTS},
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

/// `PastaPoseidonFq.VKDIGEST`, the value the Lean side already carries as the transcript's first
/// absorbed item. This example is only meaningful if the index it rebuilds is THAT index.
const VKDIGEST_DEC: &str =
    "23940398070405067193324749695039666845380036036761315381145161659442448704671";

fn fq_dec(x: Fq) -> String {
    BigUint::from(x.into_bigint()).to_string()
}

/// `~g z = List.to_array (Inner_curve.to_field_elements z)` — the affine `(x, y)`.
/// ⚠ `DefaultFqSponge::absorb_g` (`poseidon/src/sponge.rs:332-345`) absorbs the FAKE POINT `(0, 0)`
/// for the point at infinity, so an identity commitment still contributes two coordinates.
fn point_xy(c: &PolyComm<Vesta>, n_inf: &mut usize) -> Vec<Fq> {
    assert_eq!(c.chunks.len(), 1, "index commitments are single-chunk");
    let a = c.chunks[0];
    match a.xy() {
        Some((x, y)) => vec![x, y],
        None => {
            *n_inf += 1;
            vec![Fq::from(0u8), Fq::from(0u8)]
        }
    }
}

fn main() {
    // The SAME index `pickles_p6_fq_export.rs:158-174` builds.
    let public: Vec<Fp> = vec![Fp::from(3u8); 5];
    let gates = create_circuit(0, public.len());
    const NPREV: usize = 2;
    let index = new_index_for_test_with_lookups::<FULL_ROUNDS, Vesta>(
        gates,
        public.len(),
        NPREV,
        vec![],
        None,
        false,
        None,
        false,
    );
    let vi = index.verifier_index();

    // ---- the 28 points ARE the whole absorb list: no optional gate, no lookup index ----
    let optional_absent = vi.range_check0_comm.is_none()
        && vi.range_check1_comm.is_none()
        && vi.foreign_field_add_comm.is_none()
        && vi.foreign_field_mul_comm.is_none()
        && vi.xor_comm.is_none()
        && vi.rot_comm.is_none()
        && vi.lookup_index.is_none();
    assert!(
        optional_absent,
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

    // ---- GROUND TRUTH: this index's digest is the recorded VKDIGEST ----
    let vk_digest: Fq = vi.digest::<BaseSponge>();
    assert_eq!(
        fq_dec(vk_digest),
        VKDIGEST_DEC,
        "rebuilt index is NOT the index the PastaPoseidonFq fixture was taken from"
    );

    // ---- and an INDEPENDENT replay over exactly those 56 coordinates reproduces it ----
    let mut replay = BaseSponge::new(Vesta::other_curve_sponge_params());
    replay.absorb_fq(&coords);
    let replayed = replay.digest_fq();
    assert_eq!(
        fq_dec(replayed),
        VKDIGEST_DEC,
        "absorbing the 56 index_to_field_elements coordinates does NOT give the index digest"
    );

    eprintln!("[ground truth] 56 index coordinates absorb to the recorded VKDIGEST ({n_inf} of 28 points are the identity)");

    println!("{{");
    println!("  \"source\": \"o1-labs/proof-systems; create_circuit generic, 5 public inputs, prev_challenges = 2; new_index_for_test_with_lookups\",");
    println!("  \"optional_gate_and_lookup_comms_absent\": true,");
    println!("  \"n_points\": {},", PERMUTS + COLUMNS + 6);
    println!("  \"n_points_at_infinity\": {},", n_inf);
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
