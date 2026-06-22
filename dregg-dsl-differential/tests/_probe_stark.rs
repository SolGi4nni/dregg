//! Forge detector for the macro-emitted `{Name}Circuit` (emit_stark backend).
//!
//! Confirms the compile-time-baked AIR distinguishes valid from invalid inputs
//! for the inequality / equality / non-equality predicates. The inequality case
//! is the one that mattered: before the bit-decomposition fix in
//! `dregg-dsl/src/emit_stark_impl.rs`, an honestly-generated trace for a
//! VIOLATION (`a <= b` with `a > b`) was ACCEPTED because nothing tied the sign
//! bit to the decomposition of the difference. This test pins both poles:
//! the honest witness is accepted, the violation's honest trace is rejected.

use dregg_circuit::field::BabyBear;
use dregg_circuit::stark::StarkAir;
use dregg_dsl::dregg_caveat;

#[dregg_caveat]
fn probe_le(a: u64, b: u64) {
    require!(a <= b);
}

#[dregg_caveat]
fn probe_eq(a: u64, b: u64) {
    require!(a == b);
}

#[dregg_caveat]
fn probe_ne(a: u64, b: u64) {
    require!(a != b);
}

fn z() -> BabyBear {
    BabyBear::ZERO
}

#[test]
fn probe_stark_accept_reject() {
    // Two independent alpha challenges: a sound sub-constraint must vanish under
    // every alpha; a single nonzero sub-constraint shows up for almost all alpha.
    for alpha in [BabyBear::new(7), BabyBear::new(31)] {
        // LessEqual: 3 <= 5 holds; 5 <= 3 violates. generate_trace honestly
        // decomposes the difference, so the violation's reconstruction needs
        // bits above the allowed range (forced zero) => nonzero constraint.
        let c = ProbeLeCircuit;
        let valid = c.generate_trace(3, 5);
        let invalid = c.generate_trace(5, 3);
        let rv = c.eval_constraints(&valid[0], &valid[1], &[], alpha);
        let ri = c.eval_constraints(&invalid[0], &invalid[1], &[], alpha);
        assert_eq!(rv, z(), "LE valid (3 <= 5) must be accepted (alpha={alpha:?})");
        assert_ne!(ri, z(), "LE violation (5 <= 3) must be REJECTED (alpha={alpha:?})");

        // Equal: 4 == 4 holds; 4 == 9 violates.
        let c = ProbeEqCircuit;
        let valid = c.generate_trace(4, 4);
        let invalid = c.generate_trace(4, 9);
        let rv = c.eval_constraints(&valid[0], &valid[1], &[], alpha);
        let ri = c.eval_constraints(&invalid[0], &invalid[1], &[], alpha);
        assert_eq!(rv, z(), "EQ valid (4 == 4) must be accepted (alpha={alpha:?})");
        assert_ne!(ri, z(), "EQ violation (4 == 9) must be REJECTED (alpha={alpha:?})");

        // NotEqual: 4 != 9 holds; 4 != 4 violates.
        let c = ProbeNeCircuit;
        let valid = c.generate_trace(4, 9);
        let invalid = c.generate_trace(4, 4);
        let rv = c.eval_constraints(&valid[0], &valid[1], &[], alpha);
        let ri = c.eval_constraints(&invalid[0], &invalid[1], &[], alpha);
        assert_eq!(rv, z(), "NE valid (4 != 9) must be accepted (alpha={alpha:?})");
        assert_ne!(ri, z(), "NE violation (4 != 4) must be REJECTED (alpha={alpha:?})");
    }
}
