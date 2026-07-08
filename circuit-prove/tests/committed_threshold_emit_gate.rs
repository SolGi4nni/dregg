//! # The emit-from-Lean EQUALITY GATE — the committed-threshold predicate family.
//!
//! Validates the `emit-from-Lean` pattern for `committed_threshold` end-to-end. The descriptor is
//! AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/CommittedThresholdEmit.lean`,
//! `committedThresholdDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This
//! test embeds that EXACT string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. KATs the arity-2 chip mapping: `chip_absorb_all_lanes(2, [thr, blind])[0] == hash_2_to_1`
//!      (the `TID_P2` lookup with arity tag 2 IS the threshold commitment `Poseidon2(thr, blind)`);
//!   3. proves an HONEST witness (`value >= threshold`, genuine commitment) through
//!      [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof against the two
//!      commitment public inputs;
//!   4. the MUTATION CANARIES — each tampers ONE tooth and asserts the prove-or-verify REFUSES
//!      (real UNSAT), non-vacuously (the honest witness is asserted to prove first):
//!        * `forged_threshold_commitment_pi` — the `threshold_commitment == pi[0]` pin (c1);
//!        * `forged_fact_commitment_pi` — the `fact_commitment == pi[1]` pin (c2);
//!        * `value_below_threshold_refuses` — the 30-bit RANGE gadget (out-of-range `diff` → the
//!           recomposition + high-bit gates are UNSAT: `value >= threshold` is load-bearing);
//!        * `forged_poseidon2_result_refuses` — THE SOUNDNESS FIX: the arity-2 chip lookup FORCES
//!           `poseidon2_result = hash_2_to_1(thr, blind)` (a binding the hand
//!           `CommittedThresholdAir::eval_constraints` OMITS); a forged digest names a row no
//!           genuine chip permutation serves → UNSAT, even with the pins/`c3` kept consistent;
//!        * `tampered_private_value_refuses` — the `diff == value - threshold` gate (c4), isolated;
//!        * `nonbinary_bit_refuses` — the per-bit `bit*(bit-1) == 0` gate (the range gadget's
//!           binary tooth).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_fact};

/// The fixed fact context the honest witness commits (the credential's predicate symbol + trailing
/// terms + token state root). The honest fact's VALUE is the proven `value`.
const FIXED_PRED: u32 = 42;
const FIXED_STATE_ROOT: u32 = 99_999;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 committedThresholdDesc` emits (pinned by the
/// `#guard` in `CommittedThresholdEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if
/// this literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-committed-threshold::poseidon2-v2","ir":2,"trace_width":63,"public_input_count":2,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":1},{"t":"var","v":2},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":36},{"t":"var","v":37},{"t":"var","v":38},{"t":"var","v":39},{"t":"var","v":40},{"t":"var","v":41},{"t":"var","v":42},{"t":"var","v":43}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":44},{"t":"var","v":0},{"t":"var","v":45},{"t":"var","v":46},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":48},{"t":"var","v":49},{"t":"var","v":50},{"t":"var","v":51},{"t":"var","v":52},{"t":"var","v":53},{"t":"var","v":54},{"t":"var","v":55}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":48},{"t":"var","v":47},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":35},{"t":"var","v":56},{"t":"var","v":57},{"t":"var","v":58},{"t":"var","v":59},{"t":"var","v":60},{"t":"var","v":61},{"t":"var","v":62}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"var","v":1}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":4}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"var","v":5}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4},"r":{"t":"var","v":6}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8},"r":{"t":"var","v":7}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":64},"r":{"t":"var","v":10}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":128},"r":{"t":"var","v":11}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":256},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":512},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1024},"r":{"t":"var","v":14}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2048},"r":{"t":"var","v":15}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4096},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8192},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16384},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":20}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":131072},"r":{"t":"var","v":21}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":262144},"r":{"t":"var","v":22}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":524288},"r":{"t":"var","v":23}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1048576},"r":{"t":"var","v":24}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2097152},"r":{"t":"var","v":25}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4194304},"r":{"t":"var","v":26}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8388608},"r":{"t":"var","v":27}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16777216},"r":{"t":"var","v":28}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":33554432},"r":{"t":"var","v":29}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":67108864},"r":{"t":"var","v":30}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":134217728},"r":{"t":"var","v":31}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":268435456},"r":{"t":"var","v":32}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":536870912},"r":{"t":"var","v":33}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"var","v":18},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"var","v":22},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":33},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"const","v":-1}}}},{"t":"pi_binding","row":"first","col":34,"pi_index":0},{"t":"pi_binding","row":"first","col":35,"pi_index":1},{"t":"gate","body":{"t":"var","v":33}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"var","v":1}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":4}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"var","v":5}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4},"r":{"t":"var","v":6}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8},"r":{"t":"var","v":7}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":64},"r":{"t":"var","v":10}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":128},"r":{"t":"var","v":11}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":256},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":512},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1024},"r":{"t":"var","v":14}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2048},"r":{"t":"var","v":15}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4096},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8192},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16384},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":20}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":131072},"r":{"t":"var","v":21}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":262144},"r":{"t":"var","v":22}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":524288},"r":{"t":"var","v":23}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1048576},"r":{"t":"var","v":24}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2097152},"r":{"t":"var","v":25}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4194304},"r":{"t":"var","v":26}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8388608},"r":{"t":"var","v":27}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16777216},"r":{"t":"var","v":28}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":33554432},"r":{"t":"var","v":29}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":67108864},"r":{"t":"var","v":30}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":134217728},"r":{"t":"var","v":31}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":268435456},"r":{"t":"var","v":32}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":536870912},"r":{"t":"var","v":33}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"var","v":18},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"var","v":22},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":33},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"var","v":33}}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `CommittedThresholdEmit.lean` §1). ---
const PRIVATE_VALUE: usize = 0;
const THRESHOLD: usize = 1;
const BLINDING: usize = 2;
const DIFF: usize = 3;
const DIFF_BITS_START: usize = 4;
const COMMITTED_DIFF_BITS: usize = 30;
const THRESHOLD_COMMITMENT: usize = DIFF_BITS_START + COMMITTED_DIFF_BITS; // 34
const FACT_COMMITMENT: usize = THRESHOLD_COMMITMENT + 1; // 35
const POSEIDON2_RESULT: usize = FACT_COMMITMENT + 1; // 36
const CHIP_LANE_BASE: usize = 37; // threshold-commitment out-lanes 1..7 at 37..43
// value<->fact weld columns
const PREDICATE_SYM: usize = 44;
const TERM1: usize = 45;
const TERM2: usize = 46;
const STATE_ROOT: usize = 47;
const FACT_HASH: usize = 48;
const FH_LANE_BASE: usize = 49; // fact-hash out-lanes 1..7 at 49..55
const FC_LANE_BASE: usize = 56; // fact-commitment out-lanes 1..7 at 56..62
const FACT_MARK: u32 = 0xFACF;
const CT_WIDTH: usize = 63;

#[inline]
fn diff_bit(i: usize) -> usize {
    DIFF_BITS_START + i
}

/// An arity-2 `TID_P2` chip lookup absorbing `[thr_col, blind_col]`, binding out0 to `out_col` (the
/// commitment digest) and out-lanes 1..7 to `CHIP_LANE_BASE..+7`. Built EXACTLY as Lean's
/// `chipLookupTuple` (arity tag = ins.length = 2, `CHIP_RATE` zero-padded inputs, out0 :: 7 lanes).
fn chip2_lookup(input_cols: [usize; 2], out_col: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag (= ins.length in Lean's chipLookupTuple)
    for i in 0..CHIP_RATE {
        tuple.push(match input_cols.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the commitment digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(CHIP_LANE_BASE + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// A generic `TID_P2` chip lookup with arity `inputs.len()` — built EXACTLY as Lean's
/// `chipLookupTuple ins out_col lanes` (arity tag = ins.len(), `CHIP_RATE` zero-padded input exprs,
/// out0 :: 7 lane vars). Used for the value↔fact weld's arity-7 fact-hash and arity-2
/// fact-commitment lookups.
fn chip_lookup(inputs: &[LeanExpr], out_col: usize, lane_base: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(inputs.len() as i64));
    for i in 0..CHIP_RATE {
        tuple.push(inputs.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    tuple.push(LeanExpr::Var(out_col));
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The value↔fact weld's two lookups, in descriptor order (right after the threshold-commitment
/// lookup): the arity-7 fact-hash absorb of `[pred, private_value, term1, term2, 0, FACT_MARK, 1]`
/// binding out0 to `FACT_HASH`, then the arity-2 fact-commitment absorb of `[fact_hash, state_root]`
/// binding out0 to `FACT_COMMITMENT`.
fn fact_hash_lookup() -> VmConstraint2 {
    chip_lookup(
        &[
            LeanExpr::Var(PREDICATE_SYM),
            LeanExpr::Var(PRIVATE_VALUE),
            LeanExpr::Var(TERM1),
            LeanExpr::Var(TERM2),
            LeanExpr::Const(0),
            LeanExpr::Const(FACT_MARK as i64),
            LeanExpr::Const(1),
        ],
        FACT_HASH,
        FH_LANE_BASE,
    )
}
fn fact_commit_lookup() -> VmConstraint2 {
    chip_lookup(
        &[LeanExpr::Var(FACT_HASH), LeanExpr::Var(STATE_ROOT)],
        FACT_COMMITMENT,
        FC_LANE_BASE,
    )
}

/// The independently-hand-built twin of the Lean `committedThresholdDesc`: the hash-binding chip
/// lookup, the equality/diff/recomposition gates, the 30 per-bit binary gates, the two commitment
/// PI pins, and the high-bit-zero gate — in the SAME order the Lean descriptor lists them.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();

    // 1. hash binding: poseidon2_result = hash_2_to_1(threshold, blinding).
    constraints.push(chip2_lookup([THRESHOLD, BLINDING], POSEIDON2_RESULT));

    // 1b/1c. THE VALUE<->FACT WELD: fact_hash = hash_fact(pred, [private_value, term1, term2]) and
    // fact_commitment = hash_2_to_1(fact_hash, state_root) — feeding the SAME private_value column.
    constraints.push(fact_hash_lookup());
    constraints.push(fact_commit_lookup());

    // 2. c3: poseidon2_result - threshold_commitment.
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::Var(POSEIDON2_RESULT),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(THRESHOLD_COMMITMENT)),
    ))));

    // 3. c4: diff - private_value + threshold.
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::Var(DIFF),
        LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(PRIVATE_VALUE)),
            LeanExpr::Var(THRESHOLD),
        ),
    ))));

    // 4. c5: Sum_{i<30} 2^i * bit_i - diff  (right fold, -diff innermost — matches Lean foldr).
    let mut recomp = LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(DIFF));
    for i in (0..COMMITTED_DIFF_BITS).rev() {
        recomp = LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(1i64 << i), LeanExpr::Var(diff_bit(i))),
            recomp,
        );
    }
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(recomp)));

    // 5. the 30 per-bit binary gates: bit_i * (bit_i - 1).
    for i in 0..COMMITTED_DIFF_BITS {
        constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::mul(
            LeanExpr::Var(diff_bit(i)),
            LeanExpr::add(LeanExpr::Var(diff_bit(i)), LeanExpr::Const(-1)),
        ))));
    }

    // 6. the two commitment PI pins.
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: THRESHOLD_COMMITMENT,
        pi_index: 0,
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: FACT_COMMITMENT,
        pi_index: 1,
    }));

    // 7. c7: high bit (diff_bit 29) is zero.
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Var(
        diff_bit(COMMITTED_DIFF_BITS - 1),
    ))));

    // 8. THE LAST-ROW SEMANTIC FIX (`ctLastGateFix`): the same semantic bodies (c3, c4, recomp, the
    // 30 binary gates, the high-bit-zero gate) re-lowered as `.boundary VmRow::Last` so each fires on
    // the LAST row too — where the transition-only `.gate` mapping makes it vacuous. Matches the
    // deployed `CommittedThresholdAir::eval_constraints` (every-row, `is_transition = false`) and
    // closes the height-1 forge (row 0 IS last → the whole range/diff/binding chain would drop).
    let last_boundary = |body: LeanExpr| -> VmConstraint2 {
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body,
        })
    };
    // c3.
    constraints.push(last_boundary(LeanExpr::add(
        LeanExpr::Var(POSEIDON2_RESULT),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(THRESHOLD_COMMITMENT)),
    )));
    // c4.
    constraints.push(last_boundary(LeanExpr::add(
        LeanExpr::Var(DIFF),
        LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(PRIVATE_VALUE)),
            LeanExpr::Var(THRESHOLD),
        ),
    )));
    // recomp.
    let mut recomp_b = LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(DIFF));
    for i in (0..COMMITTED_DIFF_BITS).rev() {
        recomp_b = LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(1i64 << i), LeanExpr::Var(diff_bit(i))),
            recomp_b,
        );
    }
    constraints.push(last_boundary(recomp_b));
    // the 30 per-bit binary gates.
    for i in 0..COMMITTED_DIFF_BITS {
        constraints.push(last_boundary(LeanExpr::mul(
            LeanExpr::Var(diff_bit(i)),
            LeanExpr::add(LeanExpr::Var(diff_bit(i)), LeanExpr::Const(-1)),
        )));
    }
    // the high-bit-zero gate.
    constraints.push(last_boundary(LeanExpr::Var(diff_bit(
        COMMITTED_DIFF_BITS - 1,
    ))));

    EffectVmDescriptor2 {
        name: "dregg-committed-threshold::poseidon2-v2".to_string(),
        trace_width: CT_WIDTH,
        public_input_count: 2,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// One honest committed-threshold row: `value >= threshold`, the genuine `hash_2_to_1(threshold,
/// blinding)` in the commitment + poseidon2_result columns, the bit decomposition of `diff` filled,
/// AND the value↔fact weld columns filled for a fact whose VALUE is exactly `value` — so
/// `fact_hash = hash_fact(pred, [value, 0, 0])` (out0 of the arity-7 lookup, over the SAME
/// `private_value` column) and `fact_commitment = hash_2_to_1(fact_hash, state_root)` (out0 of the
/// arity-2 lookup). The chip LANE columns are left zero — the prover fills them from the genuine
/// permutation. The 4th arg is IGNORED (the honest fact commitment is derived); it is retained so the
/// existing canaries' call sites stay unchanged. Returns `(row, [threshold_commitment,
/// fact_commitment])`.
fn honest_row(
    value: BabyBear,
    threshold: BabyBear,
    blinding: BabyBear,
    _ignored_fact_commitment: BabyBear,
) -> (Vec<BabyBear>, [BabyBear; 2]) {
    let diff = value - threshold;
    let commitment = hash_2_to_1(threshold, blinding);
    let pred = BabyBear::new(FIXED_PRED);
    let sr = BabyBear::new(FIXED_STATE_ROOT);
    // The fact hash the arity-7 lookup recomputes from the `private_value` COLUMN (== `value` here).
    let fact_hash = chip_absorb_all_lanes(
        7,
        &[
            pred,
            value,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(FACT_MARK),
            BabyBear::ONE,
        ],
    )[0];
    debug_assert_eq!(
        fact_hash,
        hash_fact(pred, &[value, BabyBear::ZERO, BabyBear::ZERO])
    );
    let fact_commitment = hash_2_to_1(fact_hash, sr);
    let mut row = vec![BabyBear::ZERO; CT_WIDTH];
    row[PRIVATE_VALUE] = value;
    row[THRESHOLD] = threshold;
    row[BLINDING] = blinding;
    row[DIFF] = diff;
    let dv = diff.as_u32();
    for i in 0..COMMITTED_DIFF_BITS {
        row[diff_bit(i)] = BabyBear::new((dv >> i) & 1);
    }
    row[THRESHOLD_COMMITMENT] = commitment;
    row[FACT_COMMITMENT] = fact_commitment;
    row[POSEIDON2_RESULT] = commitment; // out0 of the arity-2 threshold-commitment absorb
    // weld columns
    row[PREDICATE_SYM] = pred;
    row[TERM1] = BabyBear::ZERO;
    row[TERM2] = BabyBear::ZERO;
    row[STATE_ROOT] = sr;
    row[FACT_HASH] = fact_hash; // out0 of the arity-7 fact-hash absorb
    (row, [commitment, fact_commitment])
}

/// A 4-row (power-of-two) base trace of identical honest rows.
fn honest_trace(
    value: BabyBear,
    threshold: BabyBear,
    blinding: BabyBear,
    fact_commitment: BabyBear,
) -> (Vec<Vec<BabyBear>>, [BabyBear; 2]) {
    let (row, pis) = honest_row(value, threshold, blinding, fact_commitment);
    (vec![row.clone(), row.clone(), row.clone(), row], pis)
}

/// The witness fixture: value 750 >= threshold 700 (diff 50, high bit clear).
fn fixture() -> (BabyBear, BabyBear, BabyBear, BabyBear) {
    (
        BabyBear::new(750),       // value
        BabyBear::new(700),       // threshold
        BabyBear::new(12345),     // blinding
        BabyBear::new(9_999_991), // fact_commitment (arbitrary; pinned to pi[1])
    )
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. Prove-THEN-verify is the
/// faithful gate: `prove_vm_descriptor2` self-verifies only under `cfg!(debug_assertions)`, so in a
/// `--release` test the CONSUMER's `verify_vm_descriptor2` is the real check.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,      // panicked anywhere -> rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err -> rejected
        Ok(Ok(())) => false, // proved AND verified -> ACCEPTED
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), with exactly the expected shape.
#[test]
fn committed_threshold_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, CT_WIDTH);
    assert_eq!(decoded.public_input_count, 2);
    // three arity chip lookups: threshold-commitment (arity 2), fact-hash (arity 7), fact-commitment
    // (arity 2) — the last two are THE VALUE<->FACT WELD.
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        chip_lookups, 3,
        "threshold-commitment + fact-hash + fact-commitment chip lookups"
    );
    // two PI pins (the two commitments).
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 2, "the two commitment PI pins");
    // 6 (3 lookups + 3 gates) + 30 binary + 3 (2 pins + high-bit) = 39 transition-domain constraints,
    // PLUS the last-row fix `ctLastGateFix` = 3 (c3/c4/recomp) + 30 binary + 1 high-bit = 34 boundary
    // constraints, so every semantic tooth fires on the last row too.
    assert_eq!(
        decoded.constraints.len(),
        (6 + COMMITTED_DIFF_BITS + 3) + (3 + COMMITTED_DIFF_BITS + 1)
    );
    // the 34 last-row boundary constraints the fix adds.
    let last_boundaries = decoded
        .constraints
        .iter()
        .filter(|c| {
            matches!(
                c,
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::Last,
                    ..
                })
            )
        })
        .count();
    assert_eq!(last_boundaries, 3 + COMMITTED_DIFF_BITS + 1);
}

/// STEP 2 — the chip mapping: an arity-2 `TID_P2` absorb IS `hash_2_to_1`, and BOTH inputs are
/// load-bearing (perturbing either changes the digest AND every lane).
#[test]
fn arity2_chip_lookup_is_hash_2_to_1() {
    let thr = BabyBear::new(700);
    let blind = BabyBear::new(12345);
    let lanes = chip_absorb_all_lanes(2, &[thr, blind]);
    assert_eq!(
        lanes[0],
        hash_2_to_1(thr, blind),
        "arity-2 chip out0 must equal hash_2_to_1 (the threshold commitment)"
    );
    for j in 0..2 {
        let mut alt = [thr, blind];
        alt[j] += BabyBear::ONE;
        let lanes_alt = chip_absorb_all_lanes(2, &alt);
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                lanes[i], lanes_alt[i],
                "chip lane {i} unchanged after perturbing input {j} — that input is dead"
            );
        }
    }
}

/// STEP 3 — THE POSITIVE POLE: an honest witness (`value >= threshold`, genuine commitment) proves
/// through the emitted descriptor and re-verifies against the two commitment public inputs.
#[test]
fn honest_committed_threshold_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    let (trace, pis) = honest_trace(value, threshold, blinding, fc);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest committed-threshold witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the two commitments");
}

/// STEP 4a — CANARY (c1): honest trace, but a FORGED `threshold_commitment` public input. The pin
/// `threshold_commitment == pi[0]` is violated at verify → UNSAT.
#[test]
fn forged_threshold_commitment_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    let (trace, pis) = honest_trace(value, threshold, blinding, fc);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let forged = [pis[0] + BabyBear::ONE, pis[1]];
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged threshold-commitment PI must be REJECTED (c1 pin)"
    );
}

/// STEP 4b — CANARY (c2): honest trace, but a FORGED `fact_commitment` public input. The pin
/// `fact_commitment == pi[1]` is violated → UNSAT.
#[test]
fn forged_fact_commitment_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    let (trace, pis) = honest_trace(value, threshold, blinding, fc);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest must accept (non-vacuity)"
    );
    let forged = [pis[0], pis[1] + BabyBear::ONE];
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged fact-commitment PI must be REJECTED (c2 pin)"
    );
}

/// STEP 4c — CANARY (RANGE): a witness with `value < threshold`. `diff = value - threshold` wraps to
/// a huge field element out of `[0, 2^29)`; the honest bit fill can neither recompose to `diff` nor
/// keep the high bit clear → the recomposition + high-bit gates are UNSAT. `value >= threshold` is
/// load-bearing (the 30-bit range gadget genuinely gates). The commitment pins + `c3` + `c4` stay
/// satisfied, so the refusal is SPECIFICALLY the range gadget.
#[test]
fn value_below_threshold_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    // honest (value >= threshold) accepts — non-vacuity.
    let (ok_trace, ok_pis) = honest_trace(value, threshold, blinding, fc);
    assert!(!rejects(&desc, &ok_trace, &ok_pis), "honest must accept");
    // value 650 < threshold 700: diff wraps out of range.
    let below = BabyBear::new(650);
    assert!(
        below.as_u32() < threshold.as_u32(),
        "fixture must be below threshold"
    );
    let (bad_trace, bad_pis) = honest_trace(below, threshold, blinding, fc);
    assert!(
        rejects(&desc, &bad_trace, &bad_pis),
        "value < threshold (out-of-range diff) must be REJECTED (range gadget)"
    );
}

/// STEP 4d — CANARY (THE SOUNDNESS FIX / hash binding): honest trace, but the `poseidon2_result`
/// digest column is FORGED off by one — AND the `threshold_commitment` column + `pi[0]` are moved to
/// the same forged value, so the commitment pin (c1) AND `c3` (`poseidon2_result == threshold_commitment`)
/// stay satisfied. The ONLY thing that breaks is the arity-2 chip lookup: `out0` is not the genuine
/// `hash_2_to_1(threshold, blinding)`, so the sent tuple names a chip row no permutation serves →
/// LogUp UNSAT. This is EXACTLY the binding the hand `eval_constraints` omitted.
#[test]
fn forged_poseidon2_result_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    let (ok_trace, ok_pis) = honest_trace(value, threshold, blinding, fc);
    assert!(!rejects(&desc, &ok_trace, &ok_pis), "honest must accept");
    let genuine = hash_2_to_1(threshold, blinding);
    let forged = genuine + BabyBear::ONE;
    let (mut trace, _) = honest_trace(value, threshold, blinding, fc);
    for row in &mut trace {
        row[POSEIDON2_RESULT] = forged; // fabricate the digest (out0)
        row[THRESHOLD_COMMITMENT] = forged; // keep c3 + the pin consistent with the forgery
    }
    let forged_pis = [forged, fc]; // keep the c1 pin satisfied against the forged commitment
    assert!(
        rejects(&desc, &trace, &forged_pis),
        "a forged poseidon2_result (no serving chip row) must be REJECTED — the hash-binding tooth"
    );
}

/// STEP 4e — CANARY (c4 + weld): honest trace, but `private_value` is bumped by one (DIFF left as
/// the old value). `private_value` now feeds `c4` (`diff == value - threshold`) AND the arity-7
/// fact-hash lookup; both break → UNSAT. (Pre-weld this isolated `c4`; the weld makes `private_value`
/// additionally load-bearing for the fact opening — which is the whole point.)
#[test]
fn tampered_private_value_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    let (ok_trace, ok_pis) = honest_trace(value, threshold, blinding, fc);
    assert!(!rejects(&desc, &ok_trace, &ok_pis), "honest must accept");
    let (mut trace, pis) = honest_trace(value, threshold, blinding, fc);
    for row in &mut trace {
        row[PRIVATE_VALUE] += BabyBear::ONE; // diff no longer = value - threshold
    }
    assert!(
        rejects(&desc, &trace, &pis),
        "a private_value inconsistent with diff must be REJECTED (c4)"
    );
}

/// STEP 4f — CANARY (binary): honest trace, but one `diff_bit` column is set to 2. The per-bit gate
/// `bit*(bit-1) == 0` is violated → UNSAT. The range gadget's binary tooth (a non-binary "bit" could
/// otherwise forge the weighted recomposition).
#[test]
fn nonbinary_bit_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (value, threshold, blinding, fc) = fixture();
    let (ok_trace, ok_pis) = honest_trace(value, threshold, blinding, fc);
    assert!(!rejects(&desc, &ok_trace, &ok_pis), "honest must accept");
    let (mut trace, pis) = honest_trace(value, threshold, blinding, fc);
    for row in &mut trace {
        row[diff_bit(7)] = BabyBear::new(2); // non-binary
    }
    assert!(
        rejects(&desc, &trace, &pis),
        "a non-binary diff bit must be REJECTED (binary gate)"
    );
}

/// STEP 4g — CANARY (THE VALUE↔FACT WELD / held forgery #2): the prover proves `value 750 >=
/// threshold 700` but the `fact_commitment` public input names a DIFFERENT real fact whose value is
/// `300` (a fact they hold that FAILS the threshold). Before the weld, `fact_commitment` was a free
/// PI, so this passed. Now the two in-circuit chip lookups force `fact_commitment =
/// hash_2_to_1(hash_fact(pred, [private_value, 0, 0]), state_root)` over the SAME `private_value`
/// column: with `private_value = 750`, `fact_commitment` MUST open to the value-750 fact, so pinning
/// it to the value-300 fact's commitment names a chip row (`hash_2_to_1(fact_hash_750, sr) = fc_300`)
/// no genuine permutation serves → LogUp UNSAT. Honest (value == committed value) ACCEPTS.
#[test]
fn forge_committed_value_neq_fact_rejects() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let threshold = BabyBear::new(700);
    let blinding = BabyBear::new(12345);
    let pred = BabyBear::new(FIXED_PRED);
    let sr = BabyBear::new(FIXED_STATE_ROOT);
    let tc = hash_2_to_1(threshold, blinding);

    // Non-vacuity: the honest witness (value 750 == committed fact value 750) ACCEPTS.
    let (ok_trace, ok_pis) = honest_trace(BabyBear::new(750), threshold, blinding, BabyBear::ZERO);
    assert!(
        !rejects(&desc, &ok_trace, &ok_pis),
        "honest value==fact must ACCEPT"
    );

    // Forge: prove value 750 >= 700, but commit to the value-300 fact the prover actually holds.
    let fc_300 = hash_2_to_1(
        hash_fact(pred, &[BabyBear::new(300), BabyBear::ZERO, BabyBear::ZERO]),
        sr,
    );
    // Fill the row honestly for private_value=750 (so c4/range/fact-hash lookup are internally
    // consistent), then override FACT_COMMITMENT + pi[1] to the value-300 fact to keep the c2 pin
    // satisfied — the strongest forgery. Only the arity-2 fact-commitment lookup can then break.
    let (mut trace, _) = honest_trace(BabyBear::new(750), threshold, blinding, BabyBear::ZERO);
    for row in &mut trace {
        row[FACT_COMMITMENT] = fc_300;
    }
    let forged_pis = [tc, fc_300];
    assert!(
        rejects(&desc, &trace, &forged_pis),
        "proving a value (750) different from the committed fact's value (300) must be REJECTED — \
         the value↔fact weld (held forgery #2)"
    );
}
