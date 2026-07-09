//! **`descriptor_by_name`** — the descriptor-world analog of
//! [`crate::dsl::descriptors::circuit_for_air_name`] (Foundation 1).
//!
//! The StarkProof→descriptor-prover migration replaces the runtime AIR-name → `DslCircuit`
//! dispatch (`circuit_for_air_name`, a match over v1 `CircuitDescriptor` circuits) with a
//! dispatch into the IR-v2 descriptor world: each predicate kind's proof is re-expressed as an
//! [`EffectVmDescriptor2`] proven through [`crate::descriptor_ir2::prove_vm_descriptor2`] and
//! checked by [`crate::descriptor_ir2::verify_vm_descriptor2`]. This module is the production
//! dispatch table for that world.
//!
//! ## The #1 migration danger this closes
//!
//! A wrong or MISSING dispatch arm is a SILENT verify failure: the consumer that cannot find a
//! descriptor for a predicate must NEVER fall through to "accept". So [`descriptor_by_name`]
//! returns [`Option::None`] on a miss — never a stand-in descriptor, never a silent accept — and
//! every mapped name is covered by the round-trip test below (name → descriptor → decode →
//! well-formedness; and, for the membership family, real prove → verify).
//!
//! ## The predicate-kind → descriptor map (ground-truthed from the migration scout)
//!
//! | [`PredicateKind`] | descriptor(s) ([`descriptor_names_for_kind`])                          |
//! |-------------------|------------------------------------------------------------------------|
//! | `Dfa`             | `dfa-routing-toggle-2state::poseidon2-v1` (DfaRouting)                  |
//! | `Temporal`        | `dregg-temporal-predicate-gte::dsl-v1` (TemporalPredicate)             |
//! | `MerkleMembership`| `merkle-membership-depth2-4ary::poseidon2-v1` + the depth-GENERAL builder |
//! | `NonMembership`   | `dregg-membership-adjacency::poseidon2-v1` + `quantified-absence-…`     |
//! | `BlindedSet`      | `dregg-non-revocation-sorted-tree::poseidon2-v1` + `dregg-accumulator-nonrev-emit-v2` |
//! | `BridgePredicate` | `bridge-action-leaf::bridge_action_air_v1` + `dregg-predicate-arith-ge::threshold-v1` |
//! | `Custom`          | `dregg-effectvm-custom-v1` (customVmDescriptor2)                        |
//! | `PedersenEquality`| NONE — off-STARK Schnorr, no descriptor (returns `&[]` / `None`)        |
//!
//! ## Where the descriptors come from (byte-pinned)
//!
//! Each predicate descriptor is emitted from Lean (`metatheory/Dregg2/Circuit/Emit/*Emit.lean`)
//! and byte-pinned there by an `emitVmJson2` `#guard`; the identical string is proven+verified
//! by its `circuit-prove/tests/*_emit_gate.rs`. The consts below embed those exact byte-pinned
//! goldens (`circuit/descriptors/by-name/*.json`, extracted verbatim) and decode them via
//! [`crate::descriptor_ir2::parse_vm_descriptor2`] — the same decode the emit-gate tests use, so
//! a byte drift on either side breaks the Lean `#guard`, the emit-gate `assert_eq!`, or this
//! module's `dispatch_names_decode_and_check` test. The depth-general Merkle membership is built
//! by [`membership_descriptor_of_depth`] (Foundation 2), not parsed.

use std::collections::HashMap;
use std::sync::LazyLock;

use crate::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};

/// Parse-once cache for the byte-pinned static goldens. `descriptor_by_name` sits on the
/// per-verify path (`bridge/src/verifier.rs`), and `parse_vm_descriptor2` walks the JSON into
/// fresh `Vec`s at 15–57 µs/call — pure waste on an immutable constant. We parse each golden ONCE
/// here and clone from the cache on dispatch (clone ≪ parse), preserving the exact owned-return
/// signature (zero caller change) AND the legible byte-pin (the `*_JSON` strings remain the source
/// of truth — this only memoizes the deterministic decode). A golden that fails to decode is simply
/// absent from the map, so dispatch still falls through to the fail-closed `None`.
static GOLDEN_CACHE: LazyLock<HashMap<&'static str, EffectVmDescriptor2>> = LazyLock::new(|| {
    STATIC_GOLDENS
        .iter()
        .filter_map(|(name, json)| parse_vm_descriptor2(json).ok().map(|d| (*name, d)))
        .collect()
});

/// Singleton caches for the two BUILT (not parsed) descriptors — each is a parameterless, immutable
/// construction, so we build once and clone on dispatch. Note-spend is the single most expensive
/// entry (~56 µs to lower the deployed DSL circuit); delegate is cheaper but likewise wasteful to
/// rebuild per verify.
static NOTE_SPEND_CACHE: LazyLock<Option<EffectVmDescriptor2>> =
    LazyLock::new(|| note_spend_leaf_descriptor().ok());
static DELEGATE_CACHE: LazyLock<EffectVmDescriptor2> = LazyLock::new(delegate_binding_descriptor);

/// The (name → byte-pinned golden JSON) table — the single source of truth shared by the cache and
/// the round-trip test, so no name can drift between dispatch and validation.
const STATIC_GOLDENS: &[(&str, &str)] = &[
    ("dfa-routing-toggle-2state::poseidon2-v1", DFA_ROUTING_JSON),
    (
        "dregg-temporal-predicate-gte::dsl-v1",
        TEMPORAL_PREDICATE_JSON,
    ),
    (
        "merkle-membership-depth2-4ary::poseidon2-v1",
        MERKLE_MEMBERSHIP_DEPTH2_JSON,
    ),
    (
        "dregg-membership-adjacency::poseidon2-v1",
        ADJACENCY_MEMBERSHIP_JSON,
    ),
    (
        "quantified-absence-quotient-accumulator::babybear4-v1",
        QUANTIFIED_ABSENCE_JSON,
    ),
    (
        "dregg-non-revocation-sorted-tree::poseidon2-v1",
        NON_REVOCATION_JSON,
    ),
    ("dregg-accumulator-nonrev-emit-v2", ACCUMULATOR_NONREV_JSON),
    (
        "bridge-action-leaf::bridge_action_air_v1",
        BRIDGE_ACTION_JSON,
    ),
    (
        "dregg-predicate-arith-ge::threshold-v1",
        PREDICATE_ARITH_JSON,
    ),
    (
        "dregg-presentation-freshness::summary-v1",
        PRESENTATION_FRESHNESS_JSON,
    ),
    ("dregg-bound-presentation::v1", BOUND_PRESENTATION_JSON),
    (
        "dregg-effectvm-custom-v1",
        crate::effect_vm_descriptors::DREGG_EFFECTVM_CUSTOM_IR2_JSON,
    ),
];

pub use crate::delegate_descriptor::{DELEGATE_V2_NAME, delegate_binding_descriptor};
pub use crate::membership_descriptor_4ary::{
    MEMBERSHIP_4ARY_NAME_PREFIX, membership_descriptor_of_depth_4ary,
};
pub use crate::membership_descriptor_general::membership_descriptor_of_depth;
pub use crate::note_spend_witness::{NOTE_SPEND_LEAF_NAME, note_spend_leaf_descriptor};

// ---- The byte-pinned emitted predicate-descriptor goldens (verbatim from the Lean #guards). ----
const DFA_ROUTING_JSON: &str = include_str!("../descriptors/by-name/dfa-routing.json");
const TEMPORAL_PREDICATE_JSON: &str =
    include_str!("../descriptors/by-name/temporal-predicate.json");
const MERKLE_MEMBERSHIP_DEPTH2_JSON: &str =
    include_str!("../descriptors/by-name/merkle-membership-depth2.json");
const ADJACENCY_MEMBERSHIP_JSON: &str =
    include_str!("../descriptors/by-name/adjacency-membership.json");
const QUANTIFIED_ABSENCE_JSON: &str =
    include_str!("../descriptors/by-name/quantified-absence.json");
const NON_REVOCATION_JSON: &str = include_str!("../descriptors/by-name/non-revocation.json");
const ACCUMULATOR_NONREV_JSON: &str =
    include_str!("../descriptors/by-name/accumulator-nonrev.json");
const BRIDGE_ACTION_JSON: &str = include_str!("../descriptors/by-name/bridge-action.json");
const PREDICATE_ARITH_JSON: &str = include_str!("../descriptors/by-name/predicate-arith.json");
/// The `presentation` family (token-presentation summary AIR + internalized FRESHNESS binding),
/// authored in `metatheory/Dregg2/Circuit/Emit/PresentationEmit.lean` (`presentationFreshnessDesc`)
/// and byte-pinned there by an `emitVmJson2` `#guard`. The blinded-presentation path
/// (`sdk::verify_anonymous_presentation`, `bridge` issuer path) reduces to this descriptor for the
/// summary + freshness tooth; the blinded issuer Merkle membership itself rides as a NAMED STARK leaf
/// (the `FITS_WITH_NAMED_GATE` verdict), so it is not internalized here.
const PRESENTATION_FRESHNESS_JSON: &str =
    include_str!("../descriptors/by-name/presentation-freshness.json");
/// The **bound-presentation** family (`dregg-bound-presentation::v1`), authored in
/// `metatheory/Dregg2/Circuit/Emit/BoundPresentationEmit.lean` (`boundPresentationDesc`) and
/// byte-pinned there by an `emitVmJson2` `#guard`. This is the Golden-Lift-stage-1 successor to the
/// freshness summary: the `presentation_tag` PI is CONSTRAINED in-circuit to its arity-4 Poseidon2
/// chip image (the tag-binding tooth `presentationFreshnessDesc` left to a named STARK leaf), so a
/// light client / the recursion fold re-verifies the tag binding from the descriptor alone. Its Rust
/// witness builder is [`crate::bound_presentation_witness::bound_presentation_witness`].
const BOUND_PRESENTATION_JSON: &str =
    include_str!("../descriptors/by-name/bound-presentation.json");

/// The prefix of the depth-GENERAL Merkle-membership descriptor name
/// ([`membership_descriptor_of_depth`] pins `depth{N}` after it).
pub const MEMBERSHIP_GENERAL_NAME_PREFIX: &str =
    "merkle-membership::poseidon2-binary-general-depth";

/// The predicate KINDS the migration dispatches (the scout's map keys).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateKind {
    /// DFA routing (finite-automaton transition predicate).
    Dfa,
    /// Temporal (`≥`/counter) predicate.
    Temporal,
    /// Poseidon2 Merkle set membership (fixed depth-2 4-ary + the depth-general builder).
    MerkleMembership,
    /// Set NON-membership (sorted-neighbor adjacency + quantified absence).
    NonMembership,
    /// Blinded-set / non-revocation membership (sorted tree + accumulator).
    BlindedSet,
    /// Bridge-action / arithmetic-threshold bridge predicate.
    BridgePredicate,
    /// Custom cell-program predicate (`customVmDescriptor2`).
    Custom,
    /// Pedersen-equality — off-STARK Schnorr; NO STARK descriptor.
    PedersenEquality,
}

/// The descriptor AIR-name(s) a predicate kind dispatches to (the scout map). `PedersenEquality`
/// returns `&[]` — it has no STARK descriptor (an off-STARK Schnorr equality). `MerkleMembership`
/// lists the fixed depth-2 name; the depth-general family is reached via
/// [`membership_descriptor_of_depth`] / the [`MEMBERSHIP_GENERAL_NAME_PREFIX`] name form.
pub fn descriptor_names_for_kind(kind: PredicateKind) -> &'static [&'static str] {
    match kind {
        PredicateKind::Dfa => &["dfa-routing-toggle-2state::poseidon2-v1"],
        PredicateKind::Temporal => &["dregg-temporal-predicate-gte::dsl-v1"],
        PredicateKind::MerkleMembership => &["merkle-membership-depth2-4ary::poseidon2-v1"],
        PredicateKind::NonMembership => &[
            "dregg-membership-adjacency::poseidon2-v1",
            "quantified-absence-quotient-accumulator::babybear4-v1",
        ],
        PredicateKind::BlindedSet => &[
            "dregg-non-revocation-sorted-tree::poseidon2-v1",
            "dregg-accumulator-nonrev-emit-v2",
        ],
        PredicateKind::BridgePredicate => &[
            "bridge-action-leaf::bridge_action_air_v1",
            "dregg-predicate-arith-ge::threshold-v1",
        ],
        PredicateKind::Custom => &["dregg-effectvm-custom-v1"],
        PredicateKind::PedersenEquality => &[],
    }
}

/// **`descriptor_by_name`** — map a predicate-descriptor AIR-name to its [`EffectVmDescriptor2`],
/// or [`None`] on an unrecognized name. The production analog of
/// [`crate::dsl::descriptors::circuit_for_air_name`], in the IR-v2 descriptor world.
///
/// A miss is `None` (fail-closed) — NEVER a stand-in descriptor. A known name whose byte-pinned
/// golden fails to decode is also `None` (fail-closed, not a silent accept); the round-trip test
/// guarantees every known golden decodes, so a `None` here always means an unknown predicate.
///
/// The depth-GENERAL Merkle-membership family is dispatched by the `merkle-membership::poseidon2-
/// binary-general-depth{N}` name form (parsed to a depth and built by
/// [`membership_descriptor_of_depth`]); every other name maps to a byte-pinned emitted golden.
pub fn descriptor_by_name(name: &str) -> Option<EffectVmDescriptor2> {
    // The depth-general BINARY membership family (built, not parsed).
    if let Some(depth_str) = name.strip_prefix(MEMBERSHIP_GENERAL_NAME_PREFIX) {
        return depth_str
            .parse::<usize>()
            .ok()
            .map(membership_descriptor_of_depth);
    }
    // The depth-general 4-ARY membership family (built, not parsed) — byte-faithful to the deployed
    // `hash_4_to_1`-chained root (`MEMBERSHIP_GENERAL_NAME_PREFIX` is `…-binary-…`, disjoint).
    if let Some(depth_str) = name.strip_prefix(MEMBERSHIP_4ARY_NAME_PREFIX) {
        return depth_str
            .parse::<usize>()
            .ok()
            .map(membership_descriptor_of_depth_4ary);
    }
    // The IR-v2 delegation scope-binding descriptor (built once, then cloned — it is a singleton).
    if name == DELEGATE_V2_NAME {
        return Some(DELEGATE_CACHE.clone());
    }
    // The note-spend recursion-leaf descriptor (built by lowering the deployed DSL note-spending
    // circuit — the most expensive build, ~56 µs; memoized as a singleton, cloned on dispatch).
    // Fail-closed on a lowering refusal (absent from the cache → `None`).
    if name == NOTE_SPEND_LEAF_NAME {
        return NOTE_SPEND_CACHE.clone();
    }

    // Static byte-pinned goldens: served from the parse-once cache (clone ≪ re-parse). A miss is
    // fail-closed `None`; a golden that failed to decode is absent from the cache → also `None`.
    GOLDEN_CACHE.get(name).cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::{
        CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, LookupSpec, MemBoundaryWitness, TID_P2,
        VmConstraint2, check_descriptor2_wellformed, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::field::BabyBear;
    use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
    use crate::poseidon2::{hash_2_to_1, hash_4_to_1};
    use std::panic::AssertUnwindSafe;

    /// Every predicate kind's every name.
    const ALL_KINDS: &[PredicateKind] = &[
        PredicateKind::Dfa,
        PredicateKind::Temporal,
        PredicateKind::MerkleMembership,
        PredicateKind::NonMembership,
        PredicateKind::BlindedSet,
        PredicateKind::BridgePredicate,
        PredicateKind::Custom,
        PredicateKind::PedersenEquality,
    ];

    /// DISPATCH SOUNDNESS: every AIR-name every kind lists resolves to a descriptor that decodes,
    /// carries that exact `name`, and passes the structural well-formedness gate
    /// (`check_descriptor2` — the same check prove/verify run first). A wrong/missing arm would
    /// fail HERE, not silently at verify time.
    #[test]
    fn dispatch_names_decode_and_check() {
        for &kind in ALL_KINDS {
            for &name in descriptor_names_for_kind(kind) {
                let desc = descriptor_by_name(name)
                    .unwrap_or_else(|| panic!("{kind:?} name {name:?} must dispatch to Some"));
                assert_eq!(
                    desc.name, name,
                    "{kind:?}: dispatched descriptor name must equal the dispatch key"
                );
                check_descriptor2_wellformed(&desc).unwrap_or_else(|e| {
                    panic!("{kind:?} descriptor {name:?} must be well-formed: {e}")
                });
            }
        }
    }

    /// PedersenEquality has NO descriptor (off-STARK) — its name list is empty and no
    /// pedersen-shaped name silently resolves.
    #[test]
    fn pedersen_equality_has_no_descriptor() {
        assert!(descriptor_names_for_kind(PredicateKind::PedersenEquality).is_empty());
        assert!(descriptor_by_name("pedersen-equality").is_none());
        assert!(descriptor_by_name("schnorr-equality").is_none());
    }

    /// A MISS is `None` — never a stand-in, never a silent accept.
    #[test]
    fn unknown_name_is_none() {
        assert!(descriptor_by_name("no-such-air").is_none());
        assert!(descriptor_by_name("").is_none());
        assert!(descriptor_by_name("merkle-membership").is_none()); // prefix-only, no depth
        // a wrong depth suffix on the general family is a miss, not a panic.
        assert!(
            descriptor_by_name("merkle-membership::poseidon2-binary-general-depthNaN").is_none()
        );
    }

    /// The depth-GENERAL name form dispatches to exactly [`membership_descriptor_of_depth`].
    #[test]
    fn depth_general_membership_dispatches() {
        for depth in [2usize, 4, 8] {
            let name = format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}{depth}");
            let via_dispatch = descriptor_by_name(&name).expect("general membership dispatches");
            assert_eq!(via_dispatch, membership_descriptor_of_depth(depth));
            assert_eq!(via_dispatch.name, name);
        }
    }

    // ---- The depth-2 4-ary Merkle-membership golden witness (mirrors merkle_membership_emit_gate). ----
    const LEAF: usize = 0;
    const SIB0A: usize = 1;
    const SIB0B: usize = 2;
    const SIB0C: usize = 3;
    const PARENT0: usize = 4;
    const CUR1: usize = 5;
    const SIB1A: usize = 6;
    const SIB1B: usize = 7;
    const SIB1C: usize = 8;
    const PARENT1: usize = 9;
    const MEMBERSHIP_WIDTH: usize = 24;

    fn honest_merkle_row(
        leaf: BabyBear,
        s0: [BabyBear; 3],
        s1: [BabyBear; 3],
    ) -> (Vec<BabyBear>, BabyBear) {
        let parent0 = hash_4_to_1(&[leaf, s0[0], s0[1], s0[2]]);
        let root = hash_4_to_1(&[parent0, s1[0], s1[1], s1[2]]);
        let mut row = vec![BabyBear::ZERO; MEMBERSHIP_WIDTH];
        row[LEAF] = leaf;
        row[SIB0A] = s0[0];
        row[SIB0B] = s0[1];
        row[SIB0C] = s0[2];
        row[PARENT0] = parent0;
        row[CUR1] = parent0;
        row[SIB1A] = s1[0];
        row[SIB1B] = s1[1];
        row[SIB1C] = s1[2];
        row[PARENT1] = root;
        (row, root)
    }

    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        matches!(r, Err(_) | Ok(Err(_)))
    }

    /// REAL PROVE → VERIFY through the dispatched depth-2 Merkle-membership descriptor
    /// (honest accept), plus a forged-root REJECT (non-vacuous: the honest witness is accepted).
    #[test]
    fn merkle_membership_dispatch_proves_and_verifies() {
        let name = "merkle-membership-depth2-4ary::poseidon2-v1";
        let desc = descriptor_by_name(name).expect("dispatch");
        let leaf = BabyBear::new(1001);
        let s0 = [
            BabyBear::new(2002),
            BabyBear::new(3003),
            BabyBear::new(4004),
        ];
        let s1 = [
            BabyBear::new(5005),
            BabyBear::new(6006),
            BabyBear::new(7007),
        ];
        let (row, root) = honest_merkle_row(leaf, s0, s1);
        let trace = vec![row.clone(), row.clone(), row.clone(), row];

        let proof =
            prove_vm_descriptor2(&desc, &trace, &[root], &MemBoundaryWitness::default(), &[])
                .expect("honest membership must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &[root]).expect("honest proof must verify");

        // forged root → the root pin is UNSAT.
        assert!(
            rejects(&desc, &trace, &[root + BabyBear::ONE]),
            "a forged claimed root must be REJECTED"
        );
    }

    /// CROSS-DESCRIPTOR REJECT: a proof minted for the depth-2 Merkle golden does NOT verify
    /// against a DIFFERENT dispatched descriptor (the DFA one) — a wrong dispatch arm cannot
    /// launder a proof.
    #[test]
    fn proof_does_not_verify_against_wrong_descriptor() {
        let merkle = descriptor_by_name("merkle-membership-depth2-4ary::poseidon2-v1").unwrap();
        let dfa = descriptor_by_name("dfa-routing-toggle-2state::poseidon2-v1").unwrap();
        let leaf = BabyBear::new(1001);
        let s0 = [
            BabyBear::new(2002),
            BabyBear::new(3003),
            BabyBear::new(4004),
        ];
        let s1 = [
            BabyBear::new(5005),
            BabyBear::new(6006),
            BabyBear::new(7007),
        ];
        let (row, root) = honest_merkle_row(leaf, s0, s1);
        let trace = vec![row.clone(), row.clone(), row.clone(), row];
        let proof = prove_vm_descriptor2(
            &merkle,
            &trace,
            &[root],
            &MemBoundaryWitness::default(),
            &[],
        )
        .expect("prove");
        // Verifying the merkle proof under the DFA descriptor must fail (different AIR set / PIs).
        assert!(
            verify_vm_descriptor2(&dfa, &proof, &[root]).is_err(),
            "a merkle proof must NOT verify against the DFA descriptor"
        );
    }

    /// TAMPERED GOLDEN: a byte-mutated descriptor JSON either fails to decode OR decodes to a
    /// descriptor that rejects the honest proof — a drifted golden never silently accepts.
    #[test]
    fn tampered_golden_does_not_silently_accept() {
        // Mutate the merkle golden's root-pin `pi_index` (0 → 9, out of range) — decode-or-check fails.
        let bad = MERKLE_MEMBERSHIP_DEPTH2_JSON.replace(
            "\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":0",
            "\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9",
        );
        assert_ne!(
            bad, MERKLE_MEMBERSHIP_DEPTH2_JSON,
            "the mutation must change the golden"
        );
        let decoded = parse_vm_descriptor2(&bad);
        if let Ok(d) = decoded {
            // decoded — but pi_index 9 exceeds public_input_count 1, so well-formedness fails.
            assert!(
                check_descriptor2_wellformed(&d).is_err(),
                "a golden with an out-of-range pi_index must fail the well-formedness gate"
            );
        }
    }

    /// Keep the hand-built shape aligned with the golden decode: the chip4 tuple helper the emit
    /// gate uses produces the exact `CHIP_TUPLE_LEN` shape (a guard against a silent chip-arity
    /// drift in the dispatched membership descriptor).
    #[test]
    fn merkle_golden_has_two_arity4_chip_lookups() {
        let d = descriptor_by_name("merkle-membership-depth2-4ary::poseidon2-v1").unwrap();
        let chip: Vec<&LookupSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chip.len(), 2, "depth-2 = two child→parent chip lookups");
        for l in chip {
            assert_eq!(l.tuple.len(), CHIP_TUPLE_LEN);
            assert_eq!(l.tuple[0], LeanExpr::Const(4), "arity-4 tag");
            // out lanes are the last CHIP_OUT_LANES entries; the input block is CHIP_RATE wide.
            assert_eq!(l.tuple.len(), 1 + CHIP_RATE + CHIP_OUT_LANES);
        }
        // the single root pin.
        let pins = d
            .constraints
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::PiBinding {
                        row: VmRow::First,
                        ..
                    })
                )
            })
            .count();
        assert_eq!(pins, 1);
    }

    // ---- A second, NON-membership predicate kind proven end-to-end through the dispatch: the
    //      toggle-DFA routing golden (mirrors dfa_routing_emit_gate's honest witness). ----
    const DFA_CURRENT: usize = 0;
    const DFA_SYMBOL: usize = 1;
    const DFA_NEXT: usize = 2;
    const DFA_ENTRY_HASH: usize = 3;
    const DFA_RUNNING_HASH: usize = 4;
    const DFA_IS_FIRST: usize = 5;
    const DFA_ACC: usize = 7;
    const DFA_WIDTH: usize = 22;

    /// Build the honest 4-row toggle-DFA routing witness (`step(s,y) = s XOR y`): start state, a
    /// symbol at row 0, self-loops after, with the genuine `hash_4_to_1` entry hashes and the
    /// `hash_2_to_1` running-hash chain. Returns `(trace, pis = [initial, final, seed, route])`.
    fn dfa_honest(start: u32, sym0: u32, seed: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let symbols = [sym0, 0, 0, 0];
        let mut cur = start;
        let mut running = seed;
        let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
        for (i, &sym) in symbols.iter().enumerate() {
            let nxt = cur ^ sym;
            let entry = hash_4_to_1(&[
                BabyBear::new(cur),
                BabyBear::new(sym),
                BabyBear::new(nxt),
                BabyBear::ZERO,
            ]);
            let acc = running;
            running = hash_2_to_1(acc, entry);
            let mut row = vec![BabyBear::ZERO; DFA_WIDTH];
            row[DFA_CURRENT] = BabyBear::new(cur);
            row[DFA_SYMBOL] = BabyBear::new(sym);
            row[DFA_NEXT] = BabyBear::new(nxt);
            row[DFA_ENTRY_HASH] = entry;
            row[DFA_RUNNING_HASH] = running;
            row[DFA_IS_FIRST] = if i == 0 {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[DFA_ACC] = acc;
            rows.push(row);
            cur = nxt;
        }
        let pis = vec![
            BabyBear::new(start),
            BabyBear::new(cur),
            seed,
            rows[3][DFA_RUNNING_HASH],
        ];
        (rows, pis)
    }

    /// REAL PROVE → VERIFY through the dispatched DFA-routing descriptor (a DISTINCT, non-membership
    /// predicate kind). Honest accept + a FORBIDDEN-edge reject (`0 --sym1--> 0`, violating
    /// `step(0,1)=1`) — non-vacuous: the honest route is accepted.
    #[test]
    fn dfa_routing_dispatch_proves_and_verifies() {
        let desc = descriptor_by_name("dfa-routing-toggle-2state::poseidon2-v1").expect("dispatch");
        let (trace, pis) = dfa_honest(0, 1, BabyBear::new(0x51D5));
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest DFA route must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("honest DFA proof must verify");

        // Forbidden edge: force NEXT = 0 at row 0 where step(0,1) = 1 → the transition Gate is UNSAT.
        let (mut bad, bad_pis) = dfa_honest(0, 1, BabyBear::new(0x51D5));
        bad[0][DFA_NEXT] = BabyBear::ZERO;
        assert!(
            rejects(&desc, &bad, &bad_pis),
            "a forbidden DFA edge (step(0,1)=1 routed to 0) must be REJECTED"
        );
    }
}
