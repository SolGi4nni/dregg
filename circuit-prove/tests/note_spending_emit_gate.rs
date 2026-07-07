//! # The emit-from-Lean EQUALITY GATE — the note-spend recursion leaf.
//!
//! Validates the `emit-from-Lean` pattern on the `note_spending` family: the descriptor whose
//! constraint SEMANTICS are now authored in `metatheory/Dregg2/Circuit/Emit/NoteSpendingLeafEmit.lean`
//! (`noteSpendLeafDesc`) and byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT
//! string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode EQUALS the PRODUCTION Rust
//!      lowering [`note_spend_to_descriptor2`] — the independently-built descriptor `circuit-prove`
//!      ships. A byte drift on either side breaks this OR the Lean `#guard`. (Every constraint the
//!      hand AIR enforces — the 7-site full-width commitment chain, the two-step nullifier, position
//!      validity, the position-aware Merkle membership + chain continuity, the boundary pins, and the
//!      in-AIR mint-hash recompute — is carried; this asserts the Lean emit reproduces them ALL.)
//!   2. proves an HONEST note-spend witness (real spending key + 28-limb commitment + Merkle path)
//!      through the REAL [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies with
//!      [`verify_vm_descriptor2`];
//!   3. the MUTATION CANARY — a forged nullifier / merkle-root / mint-hash public input, and a
//!      tampered Merkle co-path in the trace, each asserts the prove-or-verify REFUSES (real UNSAT),
//!      biting a specific descriptor tooth (PiBinding pins and the C6 Poseidon2 membership lookup).
//!
//! The canaries are NON-VACUOUS: the honest witness proves (step 2) and each negative first re-asserts
//! that the honest statement is ACCEPTED before asserting the tampered one is REFUSED.
//!
//! Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies only under
//! `cfg!(debug_assertions)` (`descriptor_ir2.rs`), so in a `--release` run the eager replay alone does
//! not check the first-row `PiBinding` against the public inputs — the CONSUMER's
//! `verify_vm_descriptor2` is the real check (the production posture).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TID_P2, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::note_spending::generate_note_spending_trace;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_circuit::note_spending_air::{
    NOTE_SPENDING_WIDTH, NoteSpendingWitness, merkle_col, pi, test_spending_key,
};
use dregg_circuit::poseidon2::{hash_fact, hash_many};
use dregg_circuit_prove::note_spend_leaf_adapter::{
    note_spend_leaf_public_inputs, note_spend_to_descriptor2,
};

/// The BYTE-IDENTICAL wire string `emitVmJson2 noteSpendLeafDesc` emits (pinned by the `#guard` in
/// `NoteSpendingLeafEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this literal
/// drifts, the `decoded == note_spend_to_descriptor2()` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"note-spend-leaf::dregg-note-spending-dsl-v3","ir":2,"trace_width":149,"public_input_count":7,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":20}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":21}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":22}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":23}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":24}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":48}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":65},{"t":"var","v":66},{"t":"var","v":67},{"t":"var","v":68},{"t":"var","v":69},{"t":"var","v":70},{"t":"var","v":71}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":48}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":25}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":26}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":27}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":28}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":49}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":72},{"t":"var","v":73},{"t":"var","v":74},{"t":"var","v":75},{"t":"var","v":76},{"t":"var","v":77},{"t":"var","v":78}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":49}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":29}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":30}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":31}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":32}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":50}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":79},{"t":"var","v":80},{"t":"var","v":81},{"t":"var","v":82},{"t":"var","v":83},{"t":"var","v":84},{"t":"var","v":85}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":50}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":33}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":34}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":35}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":36}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":51}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":86},{"t":"var","v":87},{"t":"var","v":88},{"t":"var","v":89},{"t":"var","v":90},{"t":"var","v":91},{"t":"var","v":92}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":51}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":37}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":38}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":39}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":40}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":52}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":93},{"t":"var","v":94},{"t":"var","v":95},{"t":"var","v":96},{"t":"var","v":97},{"t":"var","v":98},{"t":"var","v":99}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":52}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":41}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":42}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":43}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":44}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":53}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":100},{"t":"var","v":101},{"t":"var","v":102},{"t":"var","v":103},{"t":"var","v":104},{"t":"var","v":105},{"t":"var","v":106}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":53}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":45}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":46}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":47}},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":54}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":107},{"t":"var","v":108},{"t":"var","v":109},{"t":"var","v":110},{"t":"var","v":111},{"t":"var","v":112},{"t":"var","v":113}]},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":54}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":28}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":29}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":30}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":5}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":6}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":7}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":8}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":9}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":17}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":114},{"t":"var","v":115},{"t":"var","v":116},{"t":"var","v":117},{"t":"var","v":118},{"t":"var","v":119},{"t":"var","v":120}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":17}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":10}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":11}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":12}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":13}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":14}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":121},{"t":"var","v":122},{"t":"var","v":123},{"t":"var","v":124},{"t":"var","v":125},{"t":"var","v":126},{"t":"var","v":127}]},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"mul","l":{"t":"mul","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":4}},"r":{"t":"var","v":4}},"r":{"t":"var","v":4}},"r":{"t":"var","v":4}},"r":{"t":"mul","l":{"t":"mul","l":{"t":"mul","l":{"t":"const","v":2013265915},"r":{"t":"var","v":4}},"r":{"t":"var","v":4}},"r":{"t":"var","v":4}}},"r":{"t":"mul","l":{"t":"mul","l":{"t":"const","v":11},"r":{"t":"var","v":4}},"r":{"t":"var","v":4}}},"r":{"t":"mul","l":{"t":"const","v":2013265915},"r":{"t":"var","v":4}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"var","v":16},"r":{"t":"var","v":0}},{"t":"mul","l":{"t":"var","v":16},"r":{"t":"var","v":1}},{"t":"mul","l":{"t":"var","v":16},"r":{"t":"var","v":2}},{"t":"mul","l":{"t":"var","v":16},"r":{"t":"var","v":3}},{"t":"mul","l":{"t":"var","v":16},"r":{"t":"var","v":4}},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"var","v":5}},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"const","v":657167757}}},{"t":"var","v":128},{"t":"var","v":129},{"t":"var","v":130},{"t":"var","v":131},{"t":"var","v":132},{"t":"var","v":133},{"t":"var","v":134}]},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"pi_binding","row":"first","col":14,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":2},{"t":"pi_binding","row":"first","col":2,"pi_index":3},{"t":"pi_binding","row":"last","col":0,"pi_index":1},{"t":"pi_binding","row":"first","col":18,"pi_index":4},{"t":"pi_binding","row":"first","col":19,"pi_index":5},{"t":"pi_binding","row":"first","col":62,"pi_index":1},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":14}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":62}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":18}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":2}},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":63}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":135},{"t":"var","v":136},{"t":"var","v":137},{"t":"var","v":138},{"t":"var","v":139},{"t":"var","v":140},{"t":"var","v":141}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":63}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":1}},{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":19}},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"var","v":64}},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":657167757}}},{"t":"var","v":142},{"t":"var","v":143},{"t":"var","v":144},{"t":"var","v":145},{"t":"var","v":146},{"t":"var","v":147},{"t":"var","v":148}]},{"t":"pi_binding","row":"first","col":64,"pi_index":6}],"hash_sites":[],"ranges":[]}"#;

// Mint-extension columns (from `note_spend_leaf_adapter`): the 3 columns appended past the source
// width, then the per-site chip lanes.
const MINT_ROOT_COL: usize = NOTE_SPENDING_WIDTH; // 62
const MINT_M1_COL: usize = NOTE_SPENDING_WIDTH + 1; // 63
const MINT_HASH_COL: usize = NOTE_SPENDING_WIDTH + 2; // 64
const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3; // 65

/// A REAL full-width witness (raw 32-byte fields + a > 2^30 u64 value so the high limb is live).
/// Depth 2 → 4 trace rows (1 commitment + 2 Merkle + 1 pad), the deployed DSL circuit's own shape.
/// Byte-identical to `note_spend_leaf_adapter`'s `make_witness`.
fn make_witness(tag: u8) -> NoteSpendingWitness {
    let owner = [tag; 32];
    let nonce = [tag ^ 0x5A; 32];
    let rand = [tag ^ 0xA5; 32];
    let key = test_spending_key(tag as u32 + 0x77);
    let depth = 2;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        siblings.push([
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
        ]);
        positions.push((i % 4) as u8);
    }
    NoteSpendingWitness::from_note_limbs(
        &owner,
        0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
        3,
        &nonce,
        &rand,
        key,
        siblings,
        positions,
    )
}

/// The HONEST base trace (source trace + the 3 mint columns filled on row 0) and its 7-slot claim
/// tuple — a faithful reconstruction of `note_spend_leaf_adapter::note_spend_leaf_base_trace` from
/// PUBLIC APIs. The chip lane columns (65..149) are left to the prover's `trace_with_chip_lanes`.
fn honest_base_trace(w: &NoteSpendingWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (mut trace, pis) = generate_note_spending_trace(w);
    for row in &mut trace {
        row.resize(EXT_BASE_WIDTH, BabyBear::ZERO);
    }
    let m1 = hash_fact(
        pis[pi::NULLIFIER],
        &[
            pis[pi::MERKLE_ROOT],
            pis[pi::DESTINATION_FEDERATION],
            pis[pi::ASSET_TYPE],
        ],
    );
    let mint = hash_fact(m1, &[pis[pi::VALUE], pis[pi::VALUE_HI]]);
    trace[0][MINT_ROOT_COL] = pis[pi::MERKLE_ROOT];
    trace[0][MINT_M1_COL] = m1;
    trace[0][MINT_HASH_COL] = mint;

    let full_pis = note_spend_leaf_public_inputs(w);
    assert_eq!(
        full_pis[pi::VALUE_HI + 1],
        mint,
        "the mint identity is the appended 7th PI slot"
    );
    (trace, full_pis)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies (an accepted spend).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,      // panicked anywhere → rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err → rejected
        Ok(Ok(())) => false, // proved AND verified → ACCEPTED
    }
}

/// STEP 1 — the Lean-emitted descriptor decodes and EQUALS the production `note_spend_to_descriptor2`
/// lowering (Lean emit ≡ Rust semantics), with the expected shape.
#[test]
fn note_spend_emit_decodes_to_production_lowering() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let production =
        note_spend_to_descriptor2().expect("the production note-spend lowering builds");
    assert_eq!(
        decoded, production,
        "the Lean-emitted descriptor must equal the production note_spend_to_descriptor2() lowering"
    );

    // Shape pins (mirror the Lean `#guard`s): width 149, 7 PIs, 12 chip lookups, 8 pins, 1 window.
    assert_eq!(decoded.trace_width, 149);
    assert_eq!(decoded.public_input_count, 7);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        chip_lookups, 12,
        "7 commitment-chain + 2 nullifier + 1 Merkle + 2 mint fact sites"
    );
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 8, "6 source boundary pins + MINT_ROOT + MINT_HASH");
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(windows, 1, "the C7 Merkle-chain continuity");
}

/// STEP 2 — THE POSITIVE POLE: an honest note-spend witness proves through the emitted descriptor
/// and re-verifies against its 7-slot claim tuple.
#[test]
fn honest_note_spend_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x10);
    let (trace, pis) = honest_base_trace(&w);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest note-spend witness must prove through the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the claim tuple");
}

/// STEP 3a — MUTATION CANARY (nullifier PI): a forged nullifier slot. The boundary pin
/// `PiBinding{First, col::NULLIFIER, pi0}` is violated → UNSAT. The nullifier is bound to the spend.
#[test]
fn forged_nullifier_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x21);
    let (trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pis.clone();
    forged[pi::NULLIFIER] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged nullifier PI must be REJECTED (nullifier binding tooth)"
    );
}

/// STEP 3b — MUTATION CANARY (merkle-root PI): a forged root slot. The last-row root pin
/// `PiBinding{Last, CURRENT, pi1}` (and the MINT_ROOT pin at pi1) is violated → UNSAT.
#[test]
fn forged_merkle_root_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x32);
    let (trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest accepted"
    );
    let mut forged = pis.clone();
    forged[pi::MERKLE_ROOT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged merkle-root PI must be REJECTED (membership root binding)"
    );
}

/// STEP 3c — MUTATION CANARY (mint-hash PI): a forged mint identity slot. The pin
/// `PiBinding{First, MINT_HASH_COL, pi6}` over the in-AIR-recomputed identity is violated → UNSAT.
#[test]
fn forged_mint_hash_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x43);
    let (trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest accepted"
    );
    let mut forged = pis.clone();
    let mint_pi = pi::VALUE_HI + 1; // the appended 7th slot
    forged[mint_pi] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged mint-hash PI must be REJECTED (mint identity weld tooth)"
    );
}

/// STEP 3d — MUTATION CANARY (Merkle co-path): a tampered sibling on a Merkle row, claim tuple
/// honest. The C6 `Poseidon2Chip` membership lookup names a parent digest no genuine permutation of
/// the tampered inputs serves → UNSAT. A forged co-path is refused (the membership tooth).
#[test]
fn tampered_merkle_sibling_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x54);
    let (mut trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest accepted"
    );
    // Row 1 is the first Merkle row (is_merkle = 1). Tamper its SIB0 without recomputing PARENT:
    // the C6 lookup's out0 (PARENT) no longer matches the genuine hash of the tampered inputs.
    trace[1][merkle_col::SIB0] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged Merkle sibling (wrong co-path) must be REJECTED (C6 chip membership lookup)"
    );
}
