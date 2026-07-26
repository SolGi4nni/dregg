//! Rust witness builder for the emitted **attested-fact-membership** descriptor
//! (`dregg-attested-fact-membership::v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/AttestedFactMembershipEmit.lean` as `attestedFactMembershipDesc`).
//!
//! ## What this closes — the THIRD-PARTY rung of the predicate stack
//!
//! The predicate family ([`crate::predicate_arith_witness`] and its comparison twins) proves, at
//! `pi = [threshold, fact_commitment]`, that the value covered by `fact_commitment` satisfies the
//! bound. That is the value↔fact WELD, and it is real. What it cannot say is that the fact is a fact
//! of the PRESENTED TOKEN: `FACT_HASH` is a hidden column with nothing above it, so a prover invents
//! `(pred_sym, value, t1, t2)`, hashes it, blinds it, proves a TRUE statement about it, and publishes
//! the resulting commitment as `pi[1]`.
//!
//! A verifier holding TRUSTED STATE closes that by deriving `pi[1]` itself
//! (`dregg_sdk::verify::verify_disclosure_presentation_against_state`). A THIRD PARTY cannot: it does
//! not know the value, so it has no sound source for the expected commitment, and
//! `verify_disclosure_presentation` therefore FAILS CLOSED on every predicate proof.
//!
//! This descriptor is the missing rung. It proves, at `pi = [fact_commitment, facts_root, state_root]`:
//!
//! > "∃ fact_hash, blinding, path: `fact_hash ∈ tree(facts_root)` (a 4-ary Poseidon2 Merkle path),
//! >  and `fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])`."
//!
//! `fact_commitment` is a PI of BOTH descriptors, and both compute it by the IDENTICAL arity-4
//! absorb of `[fact_hash, state_root, blinding, 0]` — this builder's [`attested_fact_commitment`] is
//! byte-equal to [`crate::predicate_arith_witness::FactBinding::commitment_of`] (pinned by a test
//! below). So the two proofs JOIN on that felt, and their conjunction is exactly what a third party
//! needs: **some fact of the token committed at `facts_root` has a value satisfying the threshold.**
//!
//! ## Why MEMBERSHIP and not RE-DERIVE (the brute-force leak, closed)
//!
//! Re-derive needs the `blinding` to travel as a DECOMMITMENT so the verifier can recompute the
//! commitment for a value it trusts — and a proof-holder then BRUTE-FORCES a low-entropy value
//! (guess `v`, hash, compare; a driven falsifier recovers `age = 37` in 130 tries). Membership needs
//! no decommitment: `BLINDING` stays a hidden witness column and never becomes a PI. Nothing travels
//! to grind against. The same hiddenness is what keeps two showings of one fact unlinkable.
//!
//! ## The trace layout (a single logical row, repeated to a power-of-two height)
//!
//! | col     | name             | meaning                                                          |
//! |---------|------------------|------------------------------------------------------------------|
//! | 0       | `FACT_HASH`      | the hidden member (Merkle input 0 AND commitment in0)            |
//! | 1..3    | `SIB0A/B/C`      | level-0 siblings (HIDDEN)                                        |
//! | 4       | `PARENT0`        | `hash_4_to_1(fact_hash, sib0…)` = level-0 chip out0 (HIDDEN)     |
//! | 5       | `CUR1`           | level-1 path input; the continuity gate pins `CUR1 = PARENT0`    |
//! | 6..8    | `SIB1A/B/C`      | level-1 siblings (HIDDEN)                                        |
//! | 9       | `PARENT1`        | the `facts_root` (chip out0); PI-pinned                          |
//! | 10      | `BLINDING`       | the fresh blinding (HIDDEN — unlinkability + no decommitment)    |
//! | 11      | `FACT_COMMITMENT`| `hash_4_to_1([fact_hash, state_root, blinding, 0])`; PI-pinned   |
//! | 12      | `STATE_ROOT`     | the token state root; PI-pinned (PUBLIC)                         |
//! | 13..19  | `LEVEL0_LANES`   | the 7 witnessed level-0 permutation lanes 1..7                   |
//! | 20..26  | `LEVEL1_LANES`   | the 7 witnessed level-1 permutation lanes 1..7                   |
//! | 27..33  | `COMMIT_LANES`   | the 7 witnessed commitment-tooth permutation lanes 1..7          |
//!
//! Every chip lane is GENUINE Poseidon2 permutation output ([`chip_absorb_all_lanes`]), so each of
//! the three `TID_P2` chip lookups is SERVED — a forged digest, lane, blinding, or member has no
//! serving chip row → UNSAT.
//!
//! ## The leftmost-child convention
//!
//! Like [`crate::blinded_membership_witness`], the emitted descriptor hashes the member as the
//! slot-0 (leftmost) input at each level, at depth 2. `positions` is accepted to mirror the
//! production signature but each entry must be `0`; position-general / depth-general trees need the
//! generalized emitted family, not a change here.
//!
//! ## Honest scope
//!
//! `facts_root`'s own binding to the issuer's derivation is the SAME named leaf the rest of the
//! presentation rides (fold-chain continuity + derivation-root binding = recursion `ProofBind`;
//! issuer Merkle membership = a STARK sub-proof). This descriptor does not lift that leaf — it makes
//! the predicate leg REACH it, where before the leg dangled below every other leg of the presentation.

use crate::descriptor_ir2::{CHIP_OUT_LANES, chip_absorb_all_lanes};
use crate::field::BabyBear;

// ---- Column layout (mirror `AttestedFactMembershipEmit.lean` §1). ----
/// Level-0 path element = the hidden `fact_hash` (also the commitment tooth's input 0).
pub const FACT_HASH: usize = 0;
/// Level-0 siblings (HIDDEN).
pub const SIB0A: usize = 1;
pub const SIB0B: usize = 2;
pub const SIB0C: usize = 3;
/// Level-0 parent digest = `hash_4_to_1(fact_hash, sib0a, sib0b, sib0c)` (chip out0; HIDDEN).
pub const PARENT0: usize = 4;
/// Level-1 path element (the continuity gate forces `CUR1 = PARENT0`; HIDDEN).
pub const CUR1: usize = 5;
/// Level-1 siblings (HIDDEN).
pub const SIB1A: usize = 6;
pub const SIB1B: usize = 7;
pub const SIB1C: usize = 8;
/// Level-1 parent digest = the `facts_root`; pinned to [`ROOT_PI`].
pub const PARENT1: usize = 9;
/// The fresh blinding — HIDDEN, never a PI. This is what makes the commitment unlinkable AND what
/// means no decommitment travels for a brute-forcer to grind against.
pub const BLINDING: usize = 10;
/// The published `fact_commitment` — THE JOIN with the predicate proof's `pi[1]`; pinned to
/// [`FACT_COMMITMENT_PI`].
pub const FACT_COMMITMENT: usize = 11;
/// The token state root; pinned to [`STATE_ROOT_PI`] (PUBLIC).
pub const STATE_ROOT: usize = 12;
/// First of the 7 witnessed level-0 permutation lanes 1..7.
pub const LEVEL0_LANE_BASE: usize = 13;
/// First of the 7 witnessed level-1 permutation lanes 1..7.
pub const LEVEL1_LANE_BASE: usize = 20;
/// First of the 7 witnessed commitment-tooth permutation lanes 1..7.
pub const COMMIT_LANE_BASE: usize = 27;
/// Total base-trace width: 13 base columns + 7·3 chip lane blocks.
pub const ATTESTED_WIDTH: usize = 34;

/// PI slot 0: the published `fact_commitment` (THE JOIN).
pub const FACT_COMMITMENT_PI: usize = 0;
/// PI slot 1: the public `facts_root`.
pub const ROOT_PI: usize = 1;
/// PI slot 2: the public token `state_root`.
pub const STATE_ROOT_PI: usize = 2;
/// Public-input count: `[fact_commitment, facts_root, state_root]`.
pub const ATTESTED_PI_COUNT: usize = 3;

/// The emitted descriptor's depth (the leftmost-child, depth-2 path).
pub const ATTESTED_DEPTH: usize = 2;
/// The trace height (a power of two ≥ 2; the row is logically uniform).
pub const ATTESTED_HEIGHT: usize = 4;

/// The emitted descriptor's dispatch key (`descriptor_by_name`).
pub const ATTESTED_FACT_MEMBERSHIP_NAME: &str = "dregg-attested-fact-membership::v1";

/// The 4-ary Merkle parent of a member and its three co-path siblings — the genuine `hash_4_to_1`
/// the descriptor's per-level chip lookup enforces (member in the leftmost slot).
pub fn attested_merkle_parent(cur: BabyBear, siblings: [BabyBear; 3]) -> BabyBear {
    chip_absorb_all_lanes(4, &[cur, siblings[0], siblings[1], siblings[2]])[0]
}

/// The `facts_root` a depth-2 leftmost path from `fact_hash` authenticates. This is the value a
/// presentation must attest for a membership proof over `fact_hash` to verify against it.
pub fn attested_facts_root(
    fact_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
) -> Result<BabyBear, String> {
    if siblings.len() != ATTESTED_DEPTH {
        return Err(format!(
            "attested-fact-membership expects {ATTESTED_DEPTH} sibling levels (the emitted depth-2 \
             descriptor), got {}",
            siblings.len()
        ));
    }
    let parent0 = attested_merkle_parent(fact_hash, siblings[0]);
    Ok(attested_merkle_parent(parent0, siblings[1]))
}

/// **THE JOIN** — `fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])`, the arity-4
/// absorb the descriptor's `commitLookup` enforces.
///
/// This is byte-identical to the predicate family's leg-2 construction
/// ([`crate::predicate_arith_witness::FactBinding::commitment_of`], which absorbs the same four
/// inputs at the same arity). A test below pins that equality: if it ever drifts, the two proofs
/// silently stop speaking about the same fact and the third-party chain unjoins.
pub fn attested_fact_commitment(
    fact_hash: BabyBear,
    state_root: BabyBear,
    blinding: BabyBear,
) -> BabyBear {
    chip_absorb_all_lanes(4, &[fact_hash, state_root, blinding, BabyBear::ZERO])[0]
}

/// Build the **attested-fact-membership** base trace + public inputs
/// `[fact_commitment, facts_root, state_root]` for the emitted
/// `dregg-attested-fact-membership::v1` descriptor.
///
/// `siblings` is the per-level co-path triple (depth [`ATTESTED_DEPTH`] = 2); `positions` mirrors the
/// production signature but — the emitted descriptor pins the member to the leftmost child slot —
/// each entry must be `0`.
///
/// The two Merkle parents and the fact commitment are genuine chip out0 values with their 7
/// permutation lanes witnessed alongside, so all three `TID_P2` lookups are SERVED.
///
/// The three PIs are `[fact_commitment, facts_root, state_root]`. **`fact_hash` and `blinding` are
/// deliberately absent**: the member never leaves the witness (unlinkability) and no decommitment
/// travels (nothing to brute-force).
pub fn attested_fact_membership_witness(
    fact_hash: BabyBear,
    state_root: BabyBear,
    blinding: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if siblings.len() != ATTESTED_DEPTH {
        return Err(format!(
            "attested-fact-membership expects {ATTESTED_DEPTH} sibling levels (the emitted depth-2 \
             descriptor), got {}",
            siblings.len()
        ));
    }
    if positions.len() != ATTESTED_DEPTH {
        return Err(format!(
            "attested-fact-membership expects {ATTESTED_DEPTH} positions, got {}",
            positions.len()
        ));
    }
    if let Some((lvl, &p)) = positions.iter().enumerate().find(|&(_, &p)| p != 0) {
        return Err(format!(
            "attested-fact-membership position[{lvl}] = {p}: the emitted \
             `attestedFactMembershipDesc` pins the member to the leftmost child slot (slot 0) — a \
             non-leftmost position needs a position-generalized emitted descriptor, not this builder"
        ));
    }

    // Level-0 child → parent (genuine arity-4 chip absorb): out0 = parent0, lanes 1..7 witnessed.
    let level0 = chip_absorb_all_lanes(
        4,
        &[fact_hash, siblings[0][0], siblings[0][1], siblings[0][2]],
    );
    let parent0 = level0[0];
    // Level-1 child → parent: CUR1 = PARENT0 (the continuity chain), out0 = the facts_root.
    let level1 = chip_absorb_all_lanes(
        4,
        &[parent0, siblings[1][0], siblings[1][1], siblings[1][2]],
    );
    let facts_root = level1[0];
    // The commitment tooth (genuine arity-4 absorb of the SAME four inputs the predicate's leg 2
    // absorbs): out0 = the published fact_commitment, lanes 1..7 witnessed.
    let commit = chip_absorb_all_lanes(4, &[fact_hash, state_root, blinding, BabyBear::ZERO]);
    let fact_commitment = commit[0];

    let mut row = vec![BabyBear::ZERO; ATTESTED_WIDTH];
    row[FACT_HASH] = fact_hash;
    row[SIB0A] = siblings[0][0];
    row[SIB0B] = siblings[0][1];
    row[SIB0C] = siblings[0][2];
    row[PARENT0] = parent0;
    row[CUR1] = parent0; // the continuity gate: CUR1 == PARENT0
    row[SIB1A] = siblings[1][0];
    row[SIB1B] = siblings[1][1];
    row[SIB1C] = siblings[1][2];
    row[PARENT1] = facts_root;
    row[BLINDING] = blinding;
    row[FACT_COMMITMENT] = fact_commitment;
    row[STATE_ROOT] = state_root;
    for j in 0..(CHIP_OUT_LANES - 1) {
        row[LEVEL0_LANE_BASE + j] = level0[j + 1];
        row[LEVEL1_LANE_BASE + j] = level1[j + 1];
        row[COMMIT_LANE_BASE + j] = commit[j + 1];
    }

    let trace: Vec<Vec<BabyBear>> = (0..ATTESTED_HEIGHT).map(|_| row.clone()).collect();

    let mut pis = vec![BabyBear::ZERO; ATTESTED_PI_COUNT];
    pis[FACT_COMMITMENT_PI] = fact_commitment;
    pis[ROOT_PI] = facts_root;
    pis[STATE_ROOT_PI] = state_root;

    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::predicate_arith_witness::{Blinding, FactBinding};

    fn sibs() -> Vec<[BabyBear; 3]> {
        vec![
            [BabyBear::new(11), BabyBear::new(12), BabyBear::new(13)],
            [BabyBear::new(21), BabyBear::new(22), BabyBear::new(23)],
        ]
    }

    /// The dispatched artifact decodes and carries the shape this builder writes.
    ///
    /// The byte pin is Lean's: `AttestedFactMembershipEmit.lean` `#guard`s `emitVmJson2
    /// attestedFactMembershipDesc` against the exact wire string, so the artifact has one author
    /// and a drift breaks `lake build`. What is checkable HERE is the other join — that the width
    /// and PI count this Rust builder lays its trace out for are the ones the artifact declares.
    #[test]
    fn lean_bytes_parse_dispatch_and_shape() {
        let parsed = descriptor_by_name(ATTESTED_FACT_MEMBERSHIP_NAME)
            .expect("the attested-fact-membership descriptor dispatches by name");
        assert_eq!(parsed.name, ATTESTED_FACT_MEMBERSHIP_NAME);
        assert_eq!(parsed.trace_width, ATTESTED_WIDTH);
        assert_eq!(parsed.public_input_count, ATTESTED_PI_COUNT);
    }

    /// ⚑ **THE JOIN, PINNED.** This builder's commitment must be BYTE-EQUAL to the predicate
    /// family's — they are the same absorb of the same four inputs, and the third-party chain is
    /// exactly the claim that the two proofs' `fact_commitment` PIs are the same object. If this
    /// drifts, the membership proof attests one felt while the predicate proof pins another, and
    /// the conjunction silently stops meaning anything.
    #[test]
    fn the_commitment_is_byte_equal_to_the_predicate_familys() {
        let state_root = BabyBear::new(0x57A7E);
        for (value, blinding) in [(300u32, 7u32), (0, 0), (999, 0xDEAD_BEEF)] {
            let binding = FactBinding {
                predicate_sym: BabyBear::new(42),
                term1: BabyBear::new(1),
                term2: BabyBear::new(2),
                state_root,
            };
            let fact_hash = binding.fact_hash_of(BabyBear::new(value));
            let b = Blinding(BabyBear::new(blinding));

            assert_eq!(
                attested_fact_commitment(fact_hash, state_root, b.as_field()),
                binding.commitment_of(BabyBear::new(value), b),
                "the attested-membership commitment and the predicate weld's leg-2 commitment must \
                 be the SAME felt — they are the join the third-party chain rests on"
            );
        }
    }

    /// The witness is internally consistent: PIs match the recomputed root/commitment, and the
    /// continuity chain holds.
    #[test]
    fn witness_pis_are_the_genuine_root_and_commitment() {
        let fact_hash = BabyBear::new(1234);
        let state_root = BabyBear::new(0x57A7E);
        let blinding = BabyBear::new(99);
        let s = sibs();
        let (trace, pis) =
            attested_fact_membership_witness(fact_hash, state_root, blinding, &s, &[0, 0])
                .expect("the honest witness builds");

        assert_eq!(trace.len(), ATTESTED_HEIGHT);
        assert_eq!(trace[0].len(), ATTESTED_WIDTH);
        assert_eq!(
            pis[ROOT_PI],
            attested_facts_root(fact_hash, &s).expect("root"),
            "the root PI must be the genuine depth-2 path root"
        );
        assert_eq!(
            pis[FACT_COMMITMENT_PI],
            attested_fact_commitment(fact_hash, state_root, blinding),
            "the commitment PI must be the genuine arity-4 absorb"
        );
        assert_eq!(pis[STATE_ROOT_PI], state_root);
        assert_eq!(
            trace[0][CUR1], trace[0][PARENT0],
            "the continuity chain ties"
        );

        // The member and the blinding are NOT among the PIs — nothing to link or brute-force.
        for pi in &pis {
            assert_ne!(*pi, fact_hash, "the member must never be published");
            assert_ne!(*pi, blinding, "the blinding must never be published");
        }
    }

    /// UNLINKABILITY at the witness level: two fresh blindings over one fact publish two different
    /// commitments under the SAME root.
    #[test]
    fn two_blindings_of_one_fact_publish_different_commitments_under_one_root() {
        let fact_hash = BabyBear::new(1234);
        let state_root = BabyBear::new(0x57A7E);
        let s = sibs();
        let (_, a) =
            attested_fact_membership_witness(fact_hash, state_root, BabyBear::new(5), &s, &[0, 0])
                .expect("witness a");
        let (_, b) =
            attested_fact_membership_witness(fact_hash, state_root, BabyBear::new(6), &s, &[0, 0])
                .expect("witness b");
        assert_ne!(
            a[FACT_COMMITMENT_PI], b[FACT_COMMITMENT_PI],
            "two showings of one fact must publish different commitments"
        );
        assert_eq!(
            a[ROOT_PI], b[ROOT_PI],
            "…while proving membership under the same attested root"
        );
    }

    /// A non-leftmost position is REFUSED, not silently mis-arranged.
    #[test]
    fn non_leftmost_positions_fail_loud() {
        let s = sibs();
        assert!(
            attested_fact_membership_witness(
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(3),
                &s,
                &[1, 0]
            )
            .is_err(),
            "a non-leftmost position must fail loud"
        );
        assert!(
            attested_fact_membership_witness(
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(3),
                &s[..1],
                &[0]
            )
            .is_err(),
            "a wrong-depth path must fail loud"
        );
    }
}
