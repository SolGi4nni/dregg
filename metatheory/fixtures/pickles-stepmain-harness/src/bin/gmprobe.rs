//! One-shot value probe: `Generators.h` (the Pallas URS blinder) and the Bw19 group-map
//! parameters, printed as decimal field elements for the Lean side to pin.
//!
//! `Generators.h` is `Kimchi_bindings.Protocol.SRS.Fq.urs_h (Backend.Tock.Keypair.load_urs ())`
//! (`step_main_inputs.ml:306-311`), i.e. the `h` blinder of the Pallas SRS — derived from
//! `Blake2b512(b"srs_misc" ++ 0u32)` through `point_of_random_bytes`
//! (`poly-commitment/src/ipa.rs:751-775`) and independent of the SRS depth.

use ark_ff::PrimeField;
use groupmap::{BWParameters, GroupMap};
use mina_curves::pasta::{Fp, Pallas, PallasParameters};
use poly_commitment::{ipa::SRS, SRS as _};

fn d<F: PrimeField>(x: F) -> String {
    x.into_bigint().to_string()
}

fn main() {
    let srs: SRS<Pallas> = SRS::create(1);
    let h: Pallas = srs.h;
    println!("GENERATORS_H_X = {}", d(h.x));
    println!("GENERATORS_H_Y = {}", d(h.y));

    let m = <BWParameters<PallasParameters> as GroupMap<Fp>>::setup();
    println!("BW_U           = {}", d(m.u));
    println!("BW_FU          = {}", d(m.fu));
    println!(
        "BW_SQRT3U2_MU2 = {}",
        d(m.sqrt_neg_three_u_squared_minus_u_over_2)
    );
    println!("BW_SQRT3U2     = {}", d(m.sqrt_neg_three_u_squared));
    println!("BW_INV3U2      = {}", d(m.inv_three_u_squared));

    // A few (t, group_map t) pairs, so the Lean evaluator has a cross-implementation oracle.
    for t in [1u64, 2, 7, 12345, 999_999_937] {
        let (x, y) = m.to_group(Fp::from(t));
        println!("GM {t} -> ({}, {})", d(x), d(y));
    }
}
