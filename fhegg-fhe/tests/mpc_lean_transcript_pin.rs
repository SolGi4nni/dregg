//! Pin the DEPLOYED `mpc_crossing` transcript geometry against the Lean model.
//!
//! `metatheory/Market/MpcClearingSecurity.lean` proves the reveal-only statement
//! over transcript sizes it DERIVES from the public circuit shape `(K, b)`
//! (`idxBits` / `andGates` / `maskedOpens` / `crossingRounds`, transcribed from
//! `mpc.rs`). Those definitions are only worth anything if they describe the
//! circuit that actually runs.
//!
//! So the constants below are written out as literals on BOTH sides:
//!
//!   * Lean derives them by kernel computation in `deployed_transcript_pins`;
//!   * this test MEASURES them off a real `cross_curves` run.
//!
//! The two sources are independent — an arithmetic model versus the circuit's
//! observed behaviour — so a disagreement is a red gate. A pin of the Rust
//! formula against its own `simulate` (which `mpc.rs`'s own unit tests already
//! do) could not catch a shared mistake; this can.
//!
//! ⚠ If you change the gate schedule of `mpc_crossing`, these numbers move and
//! BOTH sides must move together. Do not "fix" one side to match the other
//! without deciding which one is right.

use fhegg_fhe::mpc::{cross_curves, crossing_rounds, index_bits, Crossing};
use rand::rngs::StdRng;
use rand::SeedableRng;

/// One pinned shape: `(K, b)` and every transcript size the Lean model derives.
struct ShapePin {
    k: usize,
    b: usize,
    idx_bits: usize,
    and_gates: usize,
    masked_len: usize,
    rounds: usize,
}

/// EXACTLY the triples Lean proves in
/// `Market.MpcClearingSecurity.deployed_transcript_pins`.
const LEAN_PINS: &[ShapePin] = &[
    ShapePin {
        k: 3,
        b: 8,
        idx_bits: 2,
        and_gates: 164,
        masked_len: 328,
        rounds: 27,
    },
    ShapePin {
        k: 4,
        b: 16,
        idx_bits: 2,
        and_gates: 454,
        masked_len: 908,
        rounds: 51,
    },
    ShapePin {
        k: 8,
        b: 32,
        idx_bits: 3,
        and_gates: 1941,
        masked_len: 3882,
        rounds: 132,
    },
];

/// A book at `k` buckets whose coefficients comfortably fit `b` bits.
fn curves(k: usize, seed: u64) -> (Vec<u64>, Vec<u64>) {
    let demand: Vec<u64> = (0..k)
        .map(|p| ((seed * 7 + p as u64 * 3) % 97) + 1)
        .collect();
    let supply: Vec<u64> = (0..k)
        .map(|p| ((seed * 11 + p as u64 * 5) % 89) + 1)
        .collect();
    (demand, supply)
}

#[test]
fn measured_transcript_geometry_matches_the_lean_pins() {
    let mut rng = StdRng::seed_from_u64(0x1EA4_9111);
    for pin in LEAN_PINS {
        let (demand, supply) = curves(pin.k, 3);
        let (_, tr, used) = cross_curves(&demand, &supply, pin.b, 3, &mut rng);

        assert_eq!(
            index_bits(pin.k),
            pin.idx_bits,
            "K={} index width drifted from the Lean `idxBits`",
            pin.k
        );
        assert_eq!(
            tr.and_gates, pin.and_gates,
            "K={}, b={}: measured AND gates disagree with Lean `andGates`",
            pin.k, pin.b
        );
        assert_eq!(
            used, pin.and_gates,
            "K={}, b={}: triples consumed disagree with Lean `andGates`",
            pin.k, pin.b
        );
        assert_eq!(
            tr.masked.len(),
            pin.masked_len,
            "K={}, b={}: measured masked openings disagree with Lean `maskedOpens`",
            pin.k,
            pin.b
        );
        assert_eq!(
            tr.rounds, pin.rounds,
            "K={}, b={}: measured rounds disagree with Lean `crossingRounds`",
            pin.k, pin.b
        );
        assert_eq!(crossing_rounds(pin.k, pin.b), pin.rounds);

        // The two opened output fields are exactly the widths the Lean view
        // records as `pStarBits` / `vStarBits`.
        assert_eq!(tr.revealed_pstar.len(), pin.idx_bits);
        assert_eq!(tr.revealed_vstar.len(), pin.b);
        assert!(tr.is_reveal_only(pin.k, pin.b));
    }
}

/// The fact Lean now proves as `transcript_sizes_depend_only_on_shape` (and which
/// used to be the HYPOTHESIS `hm`): at a fixed public shape, the private book
/// moves no transcript size at all.
#[test]
fn transcript_sizes_are_independent_of_the_private_book() {
    let mut rng = StdRng::seed_from_u64(0xB00C_5142);
    for pin in LEAN_PINS {
        let mut seen: Option<(usize, usize, usize, usize, usize)> = None;
        // Wildly different books at the same shape: a flat zero book, a ramp, a
        // spike, and two pseudorandom ones.
        let books: Vec<(Vec<u64>, Vec<u64>)> = vec![
            (vec![0; pin.k], vec![0; pin.k]),
            (
                (0..pin.k).map(|p| p as u64).collect(),
                (0..pin.k).map(|p| p as u64).collect(),
            ),
            (
                (0..pin.k).map(|p| if p == 0 { 250 } else { 0 }).collect(),
                (0..pin.k)
                    .map(|p| if p + 1 == pin.k { 250 } else { 0 })
                    .collect(),
            ),
            curves(pin.k, 1),
            curves(pin.k, 29),
        ];
        for (demand, supply) in books {
            let (_, tr, used) = cross_curves(&demand, &supply, pin.b, 3, &mut rng);
            let shape = (
                tr.and_gates,
                used,
                tr.masked.len(),
                tr.rounds,
                tr.revealed_pstar.len(),
            );
            match seen {
                None => seen = Some(shape),
                Some(first) => assert_eq!(
                    shape, first,
                    "K={}, b={}: a different book moved a transcript SIZE — \
                     data-obliviousness is broken and the Lean reveal-only \
                     statement no longer describes this circuit",
                    pin.k, pin.b
                ),
            }
            // And it is the pinned shape, not merely a self-consistent one.
            assert_eq!(shape.2, pin.masked_len);
        }
    }
}

/// RED: `144` is not a masked-opening count the deployed circuit can produce at
/// `K = 3` for ANY bit width — the measured lengths step by 40 per bit and skip
/// it. Lean proves the general fact as `maskedOpens_three_never_144`; this is the
/// deployed-side witness that the retired Dark-Bazaar Tier-1 constant was
/// unreachable rather than merely unexplained.
#[test]
fn the_retired_hand_picked_length_144_is_unreachable_at_k3() {
    let mut rng = StdRng::seed_from_u64(0x144_144);
    let mut lengths = Vec::new();
    for b in 1..=12usize {
        let (demand, supply) = curves(3, 2);
        // Keep every coefficient inside the b-bit ring.
        let cap = if b >= 63 { u64::MAX } else { (1u64 << b) - 1 };
        let demand: Vec<u64> = demand.iter().map(|&v| v.min(cap)).collect();
        let supply: Vec<u64> = supply.iter().map(|&v| v.min(cap)).collect();
        let (_, tr, _) = cross_curves(&demand, &supply, b, 3, &mut rng);
        assert_ne!(
            tr.masked.len(),
            144,
            "b={b} produced the retired hand-picked length 144"
        );
        lengths.push(tr.masked.len());
    }
    // The measured sequence is the Lean `maskedOpens 3 b = 40b + 8`.
    let expected: Vec<usize> = (1..=12usize).map(|b| 40 * b + 8).collect();
    assert_eq!(lengths, expected);
    assert!(!lengths.contains(&144));
}

/// The simulator's transcript geometry is reproducible from the PUBLIC shape and
/// output alone — the property the Lean `mpcSim` now models by taking `(K, b)`
/// and the leakage, and nothing else.
#[test]
fn simulator_geometry_needs_only_shape_and_output() {
    let mut rng = StdRng::seed_from_u64(0x5124_0000);
    for pin in LEAN_PINS {
        let (demand, supply) = curves(pin.k, 5);
        let (cross, tr, _) = cross_curves(&demand, &supply, pin.b, 3, &mut rng);
        let simulated = fhegg_fhe::mpc::simulate(&cross, pin.k, pin.b, &mut rng);
        assert_eq!(simulated.masked.len(), tr.masked.len());
        assert_eq!(simulated.and_gates, tr.and_gates);
        assert_eq!(simulated.rounds, tr.rounds);
        assert_eq!(simulated.revealed_pstar, tr.revealed_pstar);
        assert_eq!(simulated.revealed_vstar, tr.revealed_vstar);
        assert_eq!(simulated.masked.len(), pin.masked_len);

        // The simulator is a function of `(p*, V*, K, b)`: rebuilding it from a
        // reconstructed output reproduces the same geometry.
        let restated = Crossing {
            p_star: cross.p_star,
            v_star: cross.v_star,
        };
        let again = fhegg_fhe::mpc::simulate(&restated, pin.k, pin.b, &mut rng);
        assert_eq!(again.masked.len(), simulated.masked.len());
        assert_eq!(again.revealed_pstar, simulated.revealed_pstar);
        assert_eq!(again.revealed_vstar, simulated.revealed_vstar);
    }
}
