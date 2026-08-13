//! Measures the linear (opening) route against the AIR route at real batch sizes.
//!
//! Three questions, each answered by a different kind of evidence and labelled as such:
//!
//! 1. **[measured]** What does the linear route's prover actually cost, in wall-clock,
//!    on deployed-shape ciphertexts? (limb map + `B+1` MLE evaluations + commitments)
//! 2. **[measured]** What does the FHE fold itself cost — reduced (deployed) versus
//!    lazily accumulated (what the linear route requires)? This is the side-condition
//!    price, and `notes/h2-verdict.md` says it is negative, i.e. a speedup.
//! 3. **[derived]** How many field elements does each route commit? There is no AIR for
//!    `fold_add` in the tree to measure, so this prices the AIR that *would* be written,
//!    with named columns, deliberately conservative to the AIR.
//!
//! Run: `cargo run --release -p fold-opening --bin fold_opening_bench`

use std::hint::black_box;
use std::time::{Duration, Instant};

use fold_opening::{
    CostModel, EF, F, LimbAccumulator, RangeLeg, Shape, account, commit, fixture, flatten,
    lazy_fold, max_unit_batch, mle,
};
use p3_field::PrimeCharacteristicRing;
use p3_multilinear_util::point::Point;

const DEPLOYED_BATCH: usize = 4;

fn min_of<T>(reps: usize, mut f: impl FnMut() -> T) -> Duration {
    (0..reps)
        .map(|_| {
            let t = Instant::now();
            black_box(f());
            t.elapsed()
        })
        .min()
        .expect("at least one rep")
}

fn point(mu: usize) -> Point<EF> {
    // A fixed point: this measures evaluation cost, not the transcript.
    Point::new(
        (0..mu)
            .map(|i| EF::from(F::from_u64(0x9E37_79B9 + i as u64)))
            .collect(),
    )
}

fn main() {
    let shape = Shape::deployed();
    let mu = shape.num_variables();

    println!("# fold-as-opening — measured + derived");
    println!();
    println!("Shape (read from fhegg-core, not assumed):");
    println!(
        "  P={} polys, L={} RNS moduli, N={} degree",
        shape.polys, shape.moduli, shape.degree
    );
    println!(
        "  M = P*L*N = {} residues; limbs = M*{} = {}; mu = {}; padded 2^{} = {}",
        shape.residues(),
        fold_opening::LIMBS,
        shape.limbs(),
        mu,
        mu,
        1usize << mu
    );
    println!(
        "  batch ceiling before the accumulator wraps BabyBear: B <= {}",
        max_unit_batch()
    );
    println!();

    // -----------------------------------------------------------------
    // 2. the side condition's price on the FHE side  [measured]
    // -----------------------------------------------------------------
    println!("## The side condition: reduced vs lazy fold  [measured, min-of-N]");
    println!();
    println!(
        "FHE side only — `lazy_fold_residues` is `bfv_lean::add_row` MINUS the conditional\n\
         subtract, and carries no limb map. The limb map is proof-side and is priced below."
    );
    println!();
    println!("| B | bfv_lean::fold (reduced, deployed) | lazy residues (no reduction) | ratio |");
    println!("|---|---|---|---|");
    for &b in &[4usize, 16, 64, 256] {
        let cts: Vec<_> = (0..b).map(|k| fixture(shape, 0xF01D + k as u64)).collect();
        let coeffs = vec![1u64; b];
        let reps = if b > 64 { 40 } else { 400 };
        let reduced = min_of(reps, || {
            fhegg_core::bfv_lean::fold(&cts, u64::MAX).expect("fold")
        });
        let lazy = min_of(reps, || {
            fold_opening::lazy_fold_residues(&cts, &coeffs).expect("lazy residues")
        });
        println!(
            "| {b} | {:.3} ms | {:.3} ms | **{:.3}x** |",
            reduced.as_secs_f64() * 1e3,
            lazy.as_secs_f64() * 1e3,
            lazy.as_secs_f64() / reduced.as_secs_f64()
        );
    }
    println!();

    // -----------------------------------------------------------------
    // 1. the linear route's prover cost  [measured]
    // -----------------------------------------------------------------
    println!("## Linear-route prover cost  [measured, min-of-N]");
    println!();
    println!(
        "The whole protocol: flatten each input, evaluate B+1 multilinears at ONE point,\n\
         commit the result. Zero sumcheck rounds."
    );
    println!();
    println!(
        "| B | limb map (B x) | accumulate | MLE evals (B+1 x) | commit out | TOTAL | vs deployed fold |"
    );
    println!("|---|---|---|---|---|---|---|");
    for &b in &[4usize, 16, 64, 256] {
        let cts: Vec<_> = (0..b).map(|k| fixture(shape, 0xF01D + k as u64)).collect();
        let coeffs = vec![1u64; b];
        let acc: LimbAccumulator = lazy_fold(&cts, &coeffs).expect("lazy fold");
        let r = point(mu);
        let reps = if b > 64 { 3 } else { 10 };

        let t_flat = min_of(reps, || {
            cts.iter().map(|c| flatten(c).unwrap()).collect::<Vec<_>>()
        });
        // `lazy_fold` = limb map + accumulate, so the accumulate half is the difference.
        let t_lazy = min_of(reps, || lazy_fold(&cts, &coeffs).expect("lazy fold"));
        let t_acc = t_lazy.saturating_sub(t_flat);
        let flats: Vec<Vec<F>> = cts.iter().map(|c| flatten(c).unwrap()).collect();
        let out_flat = acc.to_field();
        let t_eval = min_of(reps, || {
            let mut s = EF::ZERO;
            for f in &flats {
                s += mle(f).eval_base(&r);
            }
            s + mle(&out_flat).eval_base(&r)
        });
        let t_commit = min_of(reps, || commit(&out_flat));
        let total = t_flat + t_acc + t_eval + t_commit;
        let fhe = min_of(reps, || {
            fhegg_core::bfv_lean::fold(&cts, u64::MAX).expect("fold")
        });
        println!(
            "| {b} | {:.2} ms | {:.2} ms | {:.2} ms | {:.2} ms | **{:.2} ms** | {:.1}x |",
            t_flat.as_secs_f64() * 1e3,
            t_acc.as_secs_f64() * 1e3,
            t_eval.as_secs_f64() * 1e3,
            t_commit.as_secs_f64() * 1e3,
            total.as_secs_f64() * 1e3,
            total.as_secs_f64() / fhe.as_secs_f64()
        );
    }
    println!();
    println!(
        "⚑ The `vs deployed fold` column is the number to compare against\n\
         `notes/h2-verdict.md`'s \"proving one FHE op costs >=618x (packed) / 1639x (scalar)\n\
         performing it\" for the AIR route. It is missing the PCS opening (see STUB), so it\n\
         is a LOWER BOUND on the linear route's real cost, not the whole of it."
    );
    println!();
    println!(
        "⚠ `commit out` is a Poseidon2 sponge in the SCALAR challenger path, not the packed\n\
         Merkle path a real PCS uses, and it is B-independent. It DOMINATES at the deployed\n\
         batch — which is `notes/prover-floor.md`'s finding arriving again: even the route\n\
         that deletes the sumcheck entirely is hash-bound."
    );
    println!();

    // -----------------------------------------------------------------
    // 3. committed elements  [derived]
    // -----------------------------------------------------------------
    let model = CostModel::default();
    println!("## Committed field elements  [DERIVED — no AIR for fold_add exists to measure]");
    println!();
    println!(
        "Columns per modular-add site: {} base + {} lookup felts + {} carry.\n\
         Deliberately conservative to the AIR (the repo measures 34 elements/site at real\n\
         circuit sites; if the ratio holds at {} it holds a fortiori at 34).",
        model.add_columns,
        model.lookup_felts,
        model.carry_columns,
        model.add_columns + model.lookup_felts + model.carry_columns
    );
    println!();
    println!(
        "| B | AIR marginal | linear marginal | **marginal ratio** | AIR total | linear total | total ratio |"
    );
    println!("|---|---|---|---|---|---|---|");
    for &b in &[DEPLOYED_BATCH, 16, 64, 512, 3840] {
        let a = account(shape, b, model);
        let tag = if b == DEPLOYED_BATCH {
            " (DEPLOYED)"
        } else {
            ""
        };
        println!(
            "| {b}{tag} | {:.3e} | {:.3e} | **{:.1}x** | {:.3e} | {:.3e} | {:.2}x |",
            a.air_marginal as f64,
            a.linear_marginal as f64,
            a.marginal_ratio(),
            a.air_total as f64,
            a.linear_total as f64,
            a.total_ratio()
        );
    }
    println!();
    println!(
        "- **marginal** = inputs already committed. They ARE: the attested clearing receipt\n\
         already binds every ordered input ciphertext. This is the accounting in which\n\
         \"ratio = B\" is true; it is exactly 7*(B-1)/5 here.\n\
         - **total** = every input commitment charged to the comparison. Saturates at\n\
         (8B-7)/(B+5) -> 8x. The B-linear win is real but it is a MARGINAL win."
    );
    println!();
    println!(
        "Range-check sites in the linear route: {} — independent of B.\n\
         That is the whole mechanism: the reduction is amortised to once, not deleted.",
        RangeLeg::sites(shape)
    );
}
