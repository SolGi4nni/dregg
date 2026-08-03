//! The shadow executor's durable NULLIFIER accumulator (VK-epoch stage E2, Path B).
//!
//! # What this is
//!
//! The cumulative double-spend frontier, held as the DEPLOYED Poseidon2 sorted-Merkle indexed tree
//! ([`dregg_circuit::heap_root::CanonicalHeapTree8`]) rather than the legacy BLAKE3
//! `dregg_cell::nullifier_set::NullifierSet`. On a committed `NoteSpend` the shadow executor
//! advances the deployed `nullifier_root` (circuit limb 26) — the sorted-compacted
//! [`CanonicalHeapTree8::root8`] (byte-identical to the producer's
//! [`dregg_circuit::heap_root::compute_canonical_heap_root_8`]). The insert itself is the DEPLOYED
//! IMT insert [`CanonicalHeapTree8::insert_witness_aafi`] — the proven `imtInsert` lineage: it
//! brackets the fresh key by the low leaf's pointer gap (`low.addr < k < low.next_addr`), so a
//! present key (or a sentinel / out-of-bracket collision) yields `None` — a FAIL-CLOSED
//! double-spend: the root does NOT advance and the spend is refused.
//!
//! # Adapting to main's IMT shape (why `insert_witness_aafi`, not `insert_witness`)
//!
//! Main evolved `HeapLeaf` to the arity-3 indexed-Merkle-tree leaf `(addr, value, next_addr)` (the
//! gap-#5 IMT closure, mirror of the proven Lean `Dregg2.Circuit.IndexedMerkleTree.imtInsert`) and
//! DROPPED the separate MAX-sentinel leaf — MAX survives only as the terminal `next_addr` pointer.
//! As a consequence the sorted-compacted [`CanonicalHeapTree8::insert_witness`] cannot append a
//! NEW-MAXIMUM key (it needs a strict successor leaf, which no longer exists), and a nullifier
//! accumulator appends new maximums constantly. The pointer-bracketing
//! [`CanonicalHeapTree8::insert_witness_aafi`] handles every fresh in-range key (MIN's pointer is
//! MAX, so the first insert brackets), and it is the PROVEN `imtInsert` path — the more faithful
//! primitive. Main keeps TWO parallel commitment lineages pre-cutover: the sorted-compacted
//! `root8` (what the producer currently commits at limb 26) and the append-ordered AAFI root
//! ([`AafiInsertWitness8::new_root`], the layout the eventual atomic AIR cutover will commit). This
//! accumulator advances the DEPLOYED sorted-compacted `root8` and ALSO surfaces the AAFI witness.
//!
//! # Why Path B (the soundness story)
//!
//! The advance runs in RUST here for speed. Its soundness is banked by the VERIFIED Lean spec, not
//! re-derived at runtime:
//!
//!   * `Dregg2.Circuit.SortedTreeNonMembershipHeap8` (`nonMembership_sound8` / `update_sound8`) and
//!     the IMT `imtInsert_preserves` / `imtLowUpdate_binds` are the proven insert + non-membership; and
//!   * `Dregg2.Exec.NullifierAccumulator.present_no_witness` is the proven fail-closed gate — an
//!     adversary CANNOT supply an insert/gap witness for an already-present key.
//!     (Both LANDED on main: `metatheory/Dregg2/Exec/NullifierAccumulator.lean` +
//!     `NullifierAccumulatorKernelBridge.lean`, and `Circuit/SortedTreeNonMembershipHeap8`.)
//!
//! The Rust face of the low-leaf opening (`imtLowUpdate_binds`) is checked inline via
//! [`recompose_membership_8`] over the AAFI witness's low-leaf membership path. The full
//! `dregg_nullifier_advance` FFI KAT (Lean `advanceRoot8Exec` = the deployed recompose) is the
//! GATED wire-codec tail (it rebuilds the Lean seed) — it lands with the ember-gated VK-epoch flip.
//!
//! # Scope (stage E2, items 1+2 — NOT the wire-codec fork)
//!
//! This holds + advances the deployed `nullifier_root` in the shadow executor state ONLY. It does
//! NOT yet thread the root into the published commitment / `WireState` / VK — that is item 3 (the
//! wire-codec fork: a `WireState.nullifier_root` field, the faithful 8-felt commitment feed, and the
//! VK regen). Until then the accumulator is observed + held; it does not gate the commit decision.

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    AafiInsertWitness8, CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf,
    compute_canonical_heap_root_8, recompose_membership_8,
};
use dregg_circuit::poseidon2::hash_bytes;

/// The leaf VALUE felt marking a nullifier as SPENT. The accumulator's tree stores presence, so any
/// fixed non-zero marker binds the leaf; `1` matches the FFI KAT's spent-marker convention.
const NF_SPENT_VALUE: u32 = 1;

/// A refused advance: the nullifier is ALREADY in the accumulator (a double-spend), so
/// [`CanonicalHeapTree8::insert_witness_aafi`] returned `None`. Fail-closed — the root did NOT
/// advance. The proven face is `Dregg2.Exec.NullifierAccumulator.present_no_witness`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NullifierDoubleSpend {
    /// The low field-image of the refused nullifier (for logging / the anomaly signal).
    pub addr: u32,
}

/// The durable Poseidon2 nullifier accumulator — the shadow executor's cumulative double-spend
/// frontier. Held across turns (see [`crate::LeanShadowObserver`]); advanced on every committed
/// `NoteSpend`.
#[derive(Clone, Debug)]
pub struct ShadowNullifierAccumulator {
    /// The spent nullifier leaves (the source of truth the sorted tree is rebuilt from). Each is
    /// an unlinked `(addr = field-image of the nullifier, value = spent marker)` entry; the tree
    /// builder relinks the IMT `next_addr` pointers.
    leaves: Vec<HeapLeaf>,
    /// The canonical 8-felt sorted-Merkle IMT over `leaves` (+ MIN sentinel). Rebuilt after each
    /// accepted spend so the next insert brackets against the grown frontier.
    tree: CanonicalHeapTree8,
    /// The current advanced deployed `nullifier_root` (8-felt; the circuit limb-26 sorted-compacted
    /// root = [`compute_canonical_heap_root_8`] over the frontier).
    root: [BabyBear; 8],
}

impl Default for ShadowNullifierAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ShadowNullifierAccumulator {
    /// A fresh accumulator over the empty frontier: the tree holds only the MIN sentinel and `root`
    /// is the deterministic empty-tree root ([`dregg_circuit::heap_root::empty_heap_root_8`]).
    pub fn new() -> Self {
        let tree = CanonicalHeapTree8::new(Vec::new(), HEAP_TREE_DEPTH);
        let root = tree.root8().limbs();
        Self {
            leaves: Vec::new(),
            tree,
            root,
        }
    }

    /// The current advanced 8-felt nullifier root (the deployed limb-26 sorted-compacted root).
    pub fn nullifier_root(&self) -> [BabyBear; 8] {
        self.root
    }

    /// The current nullifier root as a [`Faithful8`] — the NATIVE `CanonicalHeapTree8` sorted-
    /// compacted node8 root the rotated commitment's limb-26 group carries (the value threaded into
    /// `V9RotationContext.nullifier_root` / `rotation_witness::produce`). This is the accumulator's
    /// own tree root (faithful by construction), so the producer fill binds the LIVE-advanced
    /// frontier. Empty-accumulator equals `dregg_circuit::heap_root::empty_heap_root_8`, so the
    /// empty default and a live root ride the SAME lanes.
    ///
    /// [`Faithful8`]: dregg_circuit::Faithful8
    pub fn nullifier_root_faithful(&self) -> dregg_circuit::Faithful8 {
        self.tree.root8()
    }

    /// The number of nullifiers in the frontier (excluding sentinels).
    pub fn num_spent(&self) -> usize {
        self.leaves.len()
    }

    /// The canonical field-image ADDRESS of a 32-byte nullifier: the deployed `hash_bytes` image
    /// (the same lift `rotation_witness::root_felt` uses to carry byte roots into the field). This
    /// is the PROVISIONAL leaf key for stage E2 items 1+2; item 3 (the wire-codec fork) pins the
    /// canonical limb-26 nullifier encoding.
    ///
    /// # ⚑ CLASS (A) — AND THE ONLY ONE IN THE SWEEP THAT IS GENUINELY **LEAN/EMIT WORK**
    ///
    /// Classified 2026-08-01. This is a KEY, not a hash node, and it is the wrong primitive
    /// twice over: a key needs INJECTIVITY over the 256 bits of a nullifier, and one BabyBear
    /// lane carries 30.906891 of them. (Eight lanes would still lose — 247.26 < 256, pigeonhole;
    /// the key answer in this tree is `Digest9Key` / the base-2^29 nonet, `76cc8a4a7`. The
    /// 2^123.63 hash-NODE figure does not transfer to a key and must not be quoted here.)
    ///
    /// **What a collision buys.** The accumulator refuses a key already present, so the gain is
    /// not a double-spend — it is a targeted, permanent FREEZE: grind a note whose nullifier
    /// shares this felt with a victim's future nullifier, spend yours first, and the victim's
    /// note is refused forever as an already-spent double-spend. Against a chosen victim that is
    /// a second preimage, `2^30.91 ≈ 1.5e9` evaluations — hours on one core. Un-targeted it is
    /// worse than a cost: with `N` spent notes the chance an HONEST new spend collides is
    /// `N^2 / 2p`, i.e. ~50% at `N ≈ 2^15.45 ≈ 44,900` notes — the accumulator spontaneously
    /// bricks a random honest note somewhere around its 45,000th spend, with no attacker at all.
    ///
    /// **Why it is NOT migrated in the Rust sweep.** Unlike every other (A) in this sweep, the
    /// sink here is not a producer-side encoding this crate owns. It is `HeapLeaf::addr` — ONE
    /// felt — and, downstream, `MA_KEY` / `MA_LO_ADDR` / `MA_LO_NEXT` in the DEPLOYED
    /// `Ir2Air::MapAbsent` IMT bracket reached through `noteSpendVmDescriptor2R24`
    /// (`circuit/src/descriptor_ir2.rs`): one felt each, while the roots, leaf digests and node
    /// folds around them are already `node8`. Widening the Rust lift alone would desynchronise
    /// the producer from that emitted gate. **This is the Lean/emit item**, and its emitters are
    /// already proved and unlanded on disk: `metatheory/Dregg2/Circuit/Emit/LexCompare8Emit.lean`,
    /// `Emit/HeapLeafWideEmit.lean`, `Circuit/MapAbsentImtGateWide.lean`. Landing them is a VK
    /// rotation + a `CANONICAL_STATE_SCHEMA_EPOCH` bump; landing the Rust half is not a step
    /// toward it, it is a desynchronisation. Same finding, same words, at
    /// `persist/src/lib.rs`'s epoch-19 "WHAT THIS EPOCH DOES *NOT* CLOSE".
    ///
    /// ⓘ Not currently consensus-bearing: per this module's scope note, the accumulator is
    /// observed + held in the shadow executor and does NOT yet gate the commit decision (item 3
    /// threads it into `WireState` / the VK). The freeze above becomes live when item 3 lands,
    /// which is the reason to land the emitters WITH it rather than after.
    pub fn addr_of(nf: &[u8; 32]) -> BabyBear {
        hash_bytes(nf)
    }

    /// Advance the frontier by the nullifier at field-address `addr`. On success returns the
    /// [`AafiInsertWitness8`] (the proven `imtInsert` lineage) and advances the deployed
    /// sorted-compacted `nullifier_root`; on a present / sentinel / out-of-bracket key returns
    /// [`NullifierDoubleSpend`] (fail-closed — the root is unchanged).
    pub fn spend_felt(
        &mut self,
        addr: BabyBear,
    ) -> Result<AafiInsertWitness8, NullifierDoubleSpend> {
        // The UNLINKED entry `(addr, value)` — the builder / IMT insert relink the `next_addr`
        // pointer (main's arity-3 indexed-Merkle leaf; the caller supplies `(addr, value)`).
        let leaf = HeapLeaf::entry(addr, BabyBear::new(NF_SPENT_VALUE));
        // The DEPLOYED IMT insert (the proven `imtInsert` gate): `None` for a present key, a
        // sentinel collision, or an out-of-bracket key — the fail-closed `present_no_witness` face.
        let Some(witness) = self.tree.insert_witness_aafi(leaf) else {
            return Err(NullifierDoubleSpend {
                addr: addr.as_u32(),
            });
        };
        // Spec-tie #1 (`imtLowUpdate_binds`, the Rust face): the AAFI witness's low leaf really
        // opens against the accumulator's CURRENT (pre-insert) sorted-compacted root via the
        // deployed `recompose_membership_8`. A mismatch would be a corruption of the deployed heap
        // machinery, not a reachable input, so assert.
        debug_assert_eq!(
            witness.old_root, self.root,
            "the witness must open the current root"
        );
        debug_assert_eq!(
            recompose_membership_8(
                witness.low_leaf_old.digest8(),
                &witness.low_siblings,
                &witness.low_directions,
            ),
            witness.old_root,
            "the low leaf must open (recompose) to the pre-insert root (imtLowUpdate_binds)"
        );
        // Persist the grown frontier: push the leaf and rebuild the sorted IMT so the next spend
        // brackets against the advanced root, and advance the deployed sorted-compacted limb-26
        // root. Spec-tie #2: the rebuilt tree root equals the producer's
        // `compute_canonical_heap_root_8` over the same set.
        self.leaves.push(leaf);
        self.tree = CanonicalHeapTree8::new(self.leaves.clone(), HEAP_TREE_DEPTH);
        debug_assert_eq!(
            self.tree.root8().limbs(),
            compute_canonical_heap_root_8(self.leaves.clone()).limbs(),
            "the held root must equal the deployed producer compute_canonical_heap_root_8"
        );
        self.root = self.tree.root8().limbs();
        Ok(witness)
    }

    /// Advance the frontier by a 32-byte nullifier (addresses it via [`Self::addr_of`]). The
    /// committed-`NoteSpend` entry point.
    pub fn spend(&mut self, nf: &[u8; 32]) -> Result<AafiInsertWitness8, NullifierDoubleSpend> {
        self.spend_felt(Self::addr_of(nf))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// (a) A fresh spend ADVANCES the deployed root: `nullifier_root` changes, equals the producer's
    /// `compute_canonical_heap_root_8` over the frontier, and the AAFI witness opens the pre-insert root.
    #[test]
    fn fresh_spend_advances_root() {
        let mut acc = ShadowNullifierAccumulator::new();
        let before = acc.nullifier_root();
        assert_eq!(acc.num_spent(), 0);

        let witness = acc
            .spend_felt(BabyBear::new(1_500_000_000))
            .expect("a fresh nullifier advances");

        let after = acc.nullifier_root();
        assert_ne!(before, after, "a fresh spend must move the nullifier root");
        assert_eq!(
            witness.old_root, before,
            "the AAFI witness must open the pre-insert root"
        );
        assert_eq!(
            after,
            compute_canonical_heap_root_8(vec![HeapLeaf::entry(
                BabyBear::new(1_500_000_000),
                BabyBear::new(NF_SPENT_VALUE)
            )])
            .limbs(),
            "the advanced root must equal the deployed producer root over the frontier"
        );
        assert_eq!(acc.num_spent(), 1);
    }

    /// (a2) The FAITHFUL root feed (the producer fill): a fresh accumulator's `nullifier_root_faithful`
    /// equals the native empty-heap root the producers default to, and after a spend its completion
    /// lanes 1..7 become NON-ZERO (closing the vacuous zero-fill of the rotated nullifier limbs).
    #[test]
    fn faithful_root_matches_empty_default_and_grows_nonzero() {
        let acc = ShadowNullifierAccumulator::new();
        assert_eq!(
            acc.nullifier_root_faithful(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "the empty accumulator's faithful root must equal the producers' empty default \
             (dregg_turn::rotation_witness::empty_nullifier_root_8) — the empty and live roots \
             ride the SAME lanes"
        );
        // Lane 0 must equal the held scalar root's lane 0 (the historical welded limb-26 position).
        assert_eq!(acc.nullifier_root_faithful().limbs(), acc.nullifier_root());

        let mut acc = acc;
        acc.spend_felt(BabyBear::new(1_500_000_000))
            .expect("a fresh nullifier advances");
        let faithful = acc.nullifier_root_faithful();
        assert_eq!(
            faithful.limbs(),
            acc.nullifier_root(),
            "the faithful root must equal the advanced scalar root lane-for-lane"
        );
        // The completion lanes (1..7, the rotated nullifier limbs) are NON-ZERO for a non-empty
        // accumulator — the whole point of the faithful fill (a genuine node8 root fills all 8).
        assert!(
            faithful.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty accumulator's completion lanes must be NON-ZERO"
        );
    }

    /// (b) A double-spend (the SAME nullifier again) is REJECTED fail-closed: `insert_witness_aafi`
    /// returns `None`, the accumulator errs, and the root does NOT advance.
    #[test]
    fn double_spend_is_rejected_fail_closed() {
        let mut acc = ShadowNullifierAccumulator::new();
        let nf = BabyBear::new(1_269_785_000);
        acc.spend_felt(nf).expect("first spend accepted");
        let root_after_first = acc.nullifier_root();

        let err = acc
            .spend_felt(nf)
            .expect_err("re-spending the same nullifier must be refused");
        assert_eq!(err.addr, nf.as_u32());
        assert_eq!(
            acc.nullifier_root(),
            root_after_first,
            "a refused double-spend must NOT advance the root"
        );
        assert_eq!(
            acc.num_spent(),
            1,
            "the frontier must not grow on a refusal"
        );
    }

    /// (c) The advanced root EQUALS the producer's `compute_canonical_heap_root_8` over the grown
    /// frontier, and the AAFI witness's low leaf recomposes to the pre-insert root — for a spend
    /// onto a NON-empty frontier (real bracketing neighbors).
    #[test]
    fn advanced_root_equals_producer_and_witness_opens_preroot() {
        let mut acc = ShadowNullifierAccumulator::new();
        // Seed a small frontier so the fresh insert brackets against real neighbors.
        let seeds = [1_162_445_946u32, 1_771_067_041, 10, 20, 30];
        for a in seeds {
            acc.spend_felt(BabyBear::new(a)).expect("seed spend");
        }
        let pre_root = acc.nullifier_root();

        let fresh = BabyBear::new(900_000_000);
        let witness = acc
            .spend_felt(fresh)
            .expect("fresh spend onto the frontier");

        // The witness opens the pre-insert root (imtLowUpdate_binds, the deployed recompose).
        assert_eq!(witness.old_root, pre_root);
        assert_eq!(
            recompose_membership_8(
                witness.low_leaf_old.digest8(),
                &witness.low_siblings,
                &witness.low_directions,
            ),
            pre_root,
            "the low leaf must recompose to the pre-insert sorted-compacted root"
        );

        // The advanced deployed root equals the producer over the full frontier (all seeds + fresh).
        let mut all: Vec<HeapLeaf> = seeds
            .iter()
            .map(|a| HeapLeaf::entry(BabyBear::new(*a), BabyBear::new(NF_SPENT_VALUE)))
            .collect();
        all.push(HeapLeaf::entry(fresh, BabyBear::new(NF_SPENT_VALUE)));
        assert_eq!(
            acc.nullifier_root(),
            compute_canonical_heap_root_8(all).limbs(),
            "the held nullifier root must equal the deployed producer root over the frontier"
        );
    }

    /// The 32-byte `spend` entry point advances and rejects the byte-identical replay (the
    /// committed-`NoteSpend` path).
    #[test]
    fn byte_nullifier_spend_and_replay() {
        let mut acc = ShadowNullifierAccumulator::new();
        let nf = [7u8; 32];
        let before = acc.nullifier_root();
        acc.spend(&nf).expect("fresh byte nullifier accepted");
        assert_ne!(before, acc.nullifier_root());

        let err = acc.spend(&nf).expect_err("byte-identical replay refused");
        assert_eq!(err.addr, ShadowNullifierAccumulator::addr_of(&nf).as_u32());
    }
}
