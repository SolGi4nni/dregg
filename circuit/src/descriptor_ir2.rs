//! Descriptor IR v2 — the EPOCH multi-table interpreter (`docs/EPOCH-DESIGN.md`).
//!
//! `lean_descriptor_air.rs` PART 6 interprets the SINGLE-table v1 EffectVM descriptor
//! (`emitVmJson`): per-row hash sites cost a 352-column Poseidon2 aux block each, and range
//! teeth cost one boolean column per bit. This module interprets the VERSIONED v2 wire
//! (`Dregg2.Circuit.DescriptorIR2.emitVmJson2`, `"ir":2`), whose grammar makes hashing a
//! BOUNDARY phenomenon: the descriptor declares TABLES and RELATIONS, and the Rust side
//! assembles a MULTI-TABLE batch STARK (`p3-batch-stark` + the `p3-lookup` LogUp argument)
//! whose instances are
//!
//!   * **main** — one trace row per effect row; interprets the embedded v1 constraint forms
//!     (`gate`/`transition`/`boundary`/`pi_binding`) on the same domains the v1 AIR used, and
//!     realizes every declared `lookup`/`mem_op`/`map_op` as a bus interaction;
//!   * **poseidon2 chip** — one row per permutation `(arity, inputs padded to rate 8, output)`,
//!     each row pinned to the REAL Poseidon2 round constraints (`poseidon2_permute_expr`) so
//!     the table is sound in exactly the sense of Lean's `ChipTableSound`; hash-site lookups
//!     ride the `ir2_p2` bus (the measured 85% lever — one aux block per UNIQUE permutation,
//!     not per row × site);
//!   * **range** — the shared `[0,256)` byte table; a declared `lookup` into the range table
//!     (`rangeLimb bits`) is realized by byte-limb decomposition + LogUp byte queries + a
//!     tight top-limb bit bound (the proven `lean_lookup_air` shape; the realized relation is
//!     exactly `v ∈ [0, 2^bits)` = Lean's `range_row_mem_iff`);
//!   * **memory** — one row per state access, in log order: the offline-memory-checking
//!     instrumentation. The main AIR SENDS each guarded `(addr, value, prev_value,
//!     prev_serial, kind)` op on a permutation-check bus and the memory table RECEIVES it
//!     (exact multiset equality = Lean's `memTableFaithful`); the table's own AIR enforces the
//!     Blum discipline (positional serials, `prev_serial < serial` by range, read ⇒
//!     `value = prev_value`) and runs the read/write multiset argument
//!     (`init + writes = reads + final`, Lean `MemCheck`) on a second permutation bus against
//!     a boundary instance (declared addresses, strictly increasing ⇒ `Nodup`; address
//!     closure by lookup). Soundness of balance ⇒ consistency is the PROVED
//!     `Dregg2.Crypto.MemoryChecking.memcheck_sound`;
//!   * **map-ops** — one row per boundary reconciliation `(root, key, value, op) → new_root`,
//!     each row verifying a REAL sorted-Poseidon2-Merkle opening (leaf `hash[key, value]`,
//!     nodes `hash_fact(l, [r])`, depth 16 — byte-identical to
//!     `heap_root::CanonicalHeapTree`): `read` authenticates the leaf under `root` and pins
//!     `new_root = root`; `write` is the in-place sorted-tree leaf UPDATE (old leaf under
//!     `root`, new leaf over the SAME siblings to `new_root` — `HeapUpdateWitness`'s shape).
//!     Every permutation of the opening RIDES THE CHIP BUS (the leaf hashes as arity-2
//!     `ir2_p2` lookups, the node hashes as `ir2_fact` lookups into fact-marked chip rows) —
//!     the map row carries only the opening's spine (key/value/sibs/dirs + the 32 chain
//!     digests), never an in-row aux block. Main sends each guarded op; the table receives
//!     it (`mapTableFaithful`).
//!
//! **Descriptor-empty tables are NOT committed.** The batch is assembled over only the
//! tables the descriptor actually uses (a function of the constraint list alone, so prover
//! and verifier agree): the chip table iff any chip lookup or map op, the byte table iff any
//! range lookup or mem op, memory+boundary iff any mem op, map-ops iff any map op. FRI
//! opening cost is per-query × the row width of every committed matrix, so committing a
//! padded empty table is pure regression (`docs/PROOF-ECONOMICS.md` §2b measured the empty
//! map-ops table alone at ~1.7 MiB per transfer proof).
//!
//! **The law: Rust authors NO constraints.** Every enforced relation here is the realization
//! of a DECLARED descriptor element (a v1 form, a lookup into a declared table, a mem op, a
//! map op); the per-table AIRs discharge the per-table faithfulness obligations Lean names
//! (`ChipTableSound`, the faithful range table, `memTableFaithful`+`MemCheck`+`Disciplined`,
//! `mapTableFaithful`+`opensTo`/`writesTo`). Which wires are constrained is entirely the
//! descriptor's (= Lean's) choice.
//!
//! Two ADDITIVE table families ride the same batch, recursion-gated like everything here,
//! committed only when a descriptor uses them (`docs/UNIVERSAL-MEMORY.md` /
//! `docs/UNIVERSAL-MAP-ROTATION.md` §2.2):
//!
//!   * **map-absent** — one row per `map_op` kind `absent`: the bracketed sorted-gap
//!     NON-MEMBERSHIP opening (Lean `opensTo … none` via `opensTo_none_of_gap`): two
//!     membership paths at ADJACENT leaf positions under the same root, with
//!     `lo_addr < key < hi_addr` enforced by canonical-BabyBear-decomposition lexicographic
//!     comparators (`key = hi4·2^27 + lo27`, unique by the `is15·lo27 = 0` tooth since
//!     `p − 1 = 15·2^27` — full-felt hash-image keys order soundly). This is the
//!     once-per-touched-address boundary leg of `nullifier_fresh_binds_root`.
//!   * **umemory + umem-boundary** — the UNIVERSAL memory: `umem_op` constraints address the
//!     `Domain × κ` space as a literal `(domain, key)` pair with `Option`-valued cells
//!     `(present, value)`; ONE Blum multiset covers every domain
//!     (`UniversalMemory.universal_memory_sound`), with ZERO intra-proof hashing — a
//!     umem-only descriptor commits NO chip table (measured: a write+read-back is 67.6 KiB
//!     against 128.7 KiB for the same write as a boundary map op). Nullifier freshness is
//!     ONE read row with `present = 0` (`nullifier_fresh_sound` — no Merkle path, no gap
//!     opening); the nullifier domain's INSERT-ONLY discipline is an in-table tooth. The
//!     boundary table's declared `(domain, key)` list is Nodup by domain-major
//!     lexicographic strict increase over the canonical decomposition.
//!
//! ## Honest boundary notes (named, with their closure lanes)
//!
//!   * `map_op` kind `write` is realized as the in-place leaf UPDATE at an existing key
//!     (exactly `Heap.set` when the key is present — the cap-crown phase-B shape). A
//!     fresh-key sorted INSERT shifts leaf positions; its bracketed-insert witness can now
//!     reuse the map-absent adjacency/gap machinery and rides the nullifier-insert lane.
//!   * The universal-memory tables are the INTERIOR argument only: map roots remain derived
//!     boundary views reconciled by map ops at the proof's edge (today's map-ops machinery,
//!     once per touched key per proof — `boundary_root_from_memcheck` is the Lean anchor
//!     that both regimes commit to the same object). The full table-collapse (per-map tables
//!     subsumed for ALL live descriptors) is flag-day work by the spec's §3 ordering: it
//!     rides THE ONE ROTATION with the 3-verb executor, never before it.
//!   * The universal boundary image (`uinit`/`ufin`/declared `(domain, key)` list) is
//!     witness-supplied (`UMemBoundaryWitness`), exactly like the flat memory boundary. The
//!     INIT image is BOUND to committed PRE-state per-cell by a `MapOp::Read` opening each
//!     declared init cell against a committed-root PUBLIC INPUT (the PI-v3 ride-along; Lean
//!     anchor `UniversalMemory.boundary_init_root_derived` + the injectivity tooth
//!     `boundary_init_root_bound`, lifted to the IR as `DescriptorIR2.satisfied2U_init_root`).
//!     This is exactly `boundary_root_derived`'s `hsem` realized per address: the opened cell
//!     genuinely lives in the committed map whose root is published — a forged peer root has no
//!     membership path, a forged value opens to the genuine leaf. It is the WITNESSED
//!     CROSS-CELL-READ primitive (the circuit twin of the executor-only
//!     `StateConstraint::ObservedFieldEquals`); see `tests/effect_vm_umem_real_turn.rs`. The
//!     whole-IMAGE equality (the no-extra-cells direction) is now ASSEMBLED IN LEAN against the
//!     DEPLOYED binary-Merkle peer-root leg — `UniversalBridge.crossCellRead_whole_image`
//!     (+ `_sem` / `cross_cell_read_no_extra_cell` / `_teeth`), the binary-`mapRoot_injective`
//!     companion of the per-cell `crossCellRead_refines_observedField`, exactly as the flat-sponge
//!     `UniversalMemory.boundary_whole_image_sem` (lifted to the IR as
//!     `DescriptorIR2.satisfied2U_init_whole_image`) carries it over `Heap.root_injective`: pin the
//!     published peer root to the binary fold of the ENTIRE declared whole-boundary view and, under
//!     the CR floor, the committed peer heap agrees with the declared image at EVERY address
//!     INCLUDING absence off the declared list (no extra cells — a hidden cell cannot survive the
//!     pin). The Lean theorem's `hpin` hypothesis — an AIR that COMPUTES the whole-boundary binary
//!     fold (`mapRoot hash d boundaryHeap`, the sorted-leaf fold to the `2^d`-leaf root) and pins
//!     it to the published-root public input — is now REALIZED in `crate::whole_image_fold` (the
//!     WHOLE-IMAGE FOLD CHIP): a sorted-`MapKind::Insert` chain from the empty root reconstructs the
//!     deployed binary fold over the ENTIRE declared boundary view and `PiBinding`s the delivered
//!     fold to the published root, so a peer heap with one undeclared/altered cell folds elsewhere
//!     and cannot be pinned (the `mapRoot_injective` no-extra-cells tooth biting in-circuit;
//!     `tests/effect_vm_umem_real_turn.rs::cross_cell_read_whole_image_*`). The cross-table wiring
//!     binding the chip's insert-chain `(key, value)` rows to THIS universal boundary table's
//!     per-domain `(domain, key)` cells is REALIZED (`whole_image_fold::whole_image_fold_bound_*`):
//!     each fold link drives a `UMemOp::Read` against the boundary table, so the deployed
//!     address-closure lookup (`BUS_UMEM_ADDRS`) forces every folded cell DECLARED and the Blum
//!     balance (`BUS_UMEM_CHECK`) forces its folded value to equal the declared cell's value — the
//!     chip folds EXACTLY the declared boundary, no new bus/column/AIR
//!     (`tests/effect_vm_umem_real_turn.rs::whole_image_fold_bound_*`).
//!   * The custom table id 5 (Lean `SUBMASK_TID = 0`) is realized as the bitwise-submask
//!     relation at 30 bits (`subsetTable_mem_iff`: both elements in `[0, 2^30)` and
//!     `keep & held = keep`), enforced by per-bit decomposition — the custom-table CONTENTS
//!     manifest is the named small IR follow-up on the Lean side; until it lands the id ↦
//!     relation binding lives here, in one place.
//!   * The FLAT memory boundary image (`minit`/`mfin`/declared addresses) is witness-supplied
//!     (the `MemBoundaryWitness` instance). The flat boundary is the carrier
//!     `setFieldDynVmDescriptor2` (the post-flag-day dynamic field write) uses to hold a cell's
//!     eight user fields in FLAT MEMORY at addresses `0..7` (`EffectVmEmitV2.lean:51`) — the ONLY
//!     flat-`mem_op` carrier in the wide+umem welded registry (every other member uses anchored
//!     umem or hash-absorbed state), and STILL STAGED (the live per-slot `setfield-v1` is
//!     hash-absorption-bound, `memops=0`).
//!     SOUNDNESS ANCHOR — CLOSED (the flat twin of the umem anchor). The Lean denotation gained the
//!     flat init/fin root legs + the forge tooth, `#assert_axioms`-clean, mirroring the universal
//!     `satisfied2U_init_root` family EXACTLY (`DescriptorIR2.lean`, the §6a' block after
//!     `satisfied2_mem_consistent`):
//!       - `satisfied2_init_root` / `satisfied2_fin_root` — if the committed pre/post-state heap has
//!         the declared `minit`/`mfin` lookup semantics over the declared sorted addresses, its
//!         sorted-Poseidon2 root EQUALS the boundary fold `Heap.root (boundaryCells (some ∘ minit)
//!         maddrs)` (the universal `boundary_init_root_derived`, the flat image saturated to `some`);
//!       - `satisfied2_init_root_bound` — the forge tooth: `Heap.root_injective` under
//!         `Poseidon2SpongeCR`, so a declared image differing from the committed pre-state CANNOT
//!         keep the published root;
//!       - `satisfied2_init_whole_image` — `boundary_whole_image_sem`: pinning the committed root to
//!         the WHOLE-boundary fold forces the committed heap to BE the declared image at every
//!         address (declared cells open to `minit a`, every address off the list ABSENT) — the
//!         no-extra-cells direction that rejects a forged `minit[a]` at an untouched declared field.
//!     IN-CIRCUIT REALIZATION — REALIZED as the flat-bound whole-image fold companion (the exact
//!     twin of the umem `whole_image_fold_bound`, `crate::whole_image_fold::*_bound_mem`): the fold
//!     recomputes the sorted-Poseidon2 root of the declared flat boundary image and pins it to the
//!     published (committed-pre-state) root, each fold link cross-bound to the `MemBoundary` table
//!     via a `MemOp::Read`. The two deployed teeth bite in `verify_batch` (no new bus/column/AIR):
//!     the `BUS_MEM_ADDRS` address-closure refuses a folded cell the boundary never declared, and
//!     the `BUS_MEM_CHECK` Blum balance refuses a folded value differing from the declared
//!     `minit[addr]` — so a forged `minit` folds to a different root and the published-root pin
//!     REFUSES (`tests/effect_vm_umem_real_turn.rs::whole_image_fold_bound_mem_forged_minit_refuses`
//!     + honest-accept/undeclared/smuggled-start companions).
//!     RESIDUAL — the per-EFFECT VK weld. Like the umem boundary (still "witness-supplied" at its
//!     effect descriptors, the anchor realized as the `whole_image_fold` companion), the flat fold
//!     is realized as a companion, NOT yet welded into `setFieldDynVmDescriptor2` itself. Welding it
//!     — `setFieldDynVmDescriptor2` publishes `minit_root`/`mfin_root` PIs pinned to the turn's
//!     committed pre/post-state root, with the fold (running-root columns in `Ir2Air::MemBoundary` +
//!     the boundary producer, or an in-batch fold AIR) proving the pin, then `emit-descriptors.sh`
//!     re-emit so its VK MOVES (`check-descriptor-drift.sh`) — is what makes a forged-`minit` proof
//!     of setFieldDyn ITSELF refuse in `verify_batch` (today the companion is a separate proof).
//!     Two known weld details: (a) the field addresses `0..7` include addr 0, which the binary
//!     Merkle sorted-insert rejects as a sentinel collision (an address offset, or sentinel-handling
//!     adjustment, is needed for the fold over the real `0..7` plane — the companion test uses
//!     non-zero addresses, as the umem tests do); (b) the cross-binding `MemOp::Read` links join the
//!     effect's memory log, so the fin-side fold + `setFieldDyn_memLog` need the joined-log
//!     accounting worked through. The carrier stays STAGED until this weld lands; the soundness
//!     anchor + the biting forge tooth are in place.
//!   * v1 descriptors (no `"ir"` key) keep proving through `lean_descriptor_air::
//!     prove_vm_descriptor` untouched — both registries live until the flag-day.

// Prover-only (the trace-assembly histograms): `recursion`.
use std::collections::BTreeMap;

use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_lookup::InteractionBuilder;
use p3_lookup::bus::{LookupBus, PermutationCheckBus};
// Prover-only (`to_matrix` builds the LDE input matrix): `recursion`.
use p3_matrix::dense::RowMajorMatrix;

// VERIFY surface (compiles under the prover-free `verifier` feature): `verify_batch`
// is prover-free, and `ProverData::from_airs_and_degrees(..).common` builds only the
// symbolic `Lookups` + (empty, for the IR-v2 AIRs) preprocessed commitment — no DFT,
// no `prove_batch`. The PROVE surface (`prove_batch` + `StarkInstance` trace assembly)
// is `recursion`-only.
use p3_batch_stark::{BatchProof, ProverData, verify_batch};
use p3_batch_stark::{StarkInstance, prove_batch};
// Generic-config (SIDESTEP) prove/verify surface: lets the rotated leaf-wrap mint/verify an
// IR-v2 batch under an arbitrary `SC` (e.g. the recursion config with retargeted FRI knobs)
// rather than only `DreggStarkConfig`. The bounds mirror `prove_batch`/`verify_batch`'s own.
// On both the prover (`recursion`) and verify (`verifier`) surfaces, like `verify_batch`.
use p3_commit::PolynomialSpace;
use p3_field::Algebra;
use p3_uni_stark::{Domain, StarkGenericConfig, SymbolicExpressionExt, Val};

/// Re-export the IR-v2 wire proof type + its STARK config so external crates (the sdk's
/// rotated route, measurement tests) can name the `prove_vm_descriptor2` return type without
/// depending on `p3-batch-stark` / `crate::plonky3_prover` directly.
pub use crate::plonky3_prover::DreggStarkConfig;
pub use p3_batch_stark::BatchProof as Ir2BatchProof;

use crate::field::{BABYBEAR_P, BabyBear};
// `HEAP_TREE_DEPTH` indexes the map-absent AIR column layout (verify-needed); the tree
// type / leaf / sentinels are prover-only (the witness map openings live in `build_traces`).
use crate::heap_root::HEAP_TREE_DEPTH;
use crate::heap_root::{CanonicalHeapTree, HeapLeaf, SENTINEL_MAX, SENTINEL_MIN};
use crate::lean_descriptor_air::{
    EFFECTVM_STATE_AFTER_BASE, EFFECTVM_STATE_BEFORE_BASE, JsonCursor, LeanExpr, VmConstraint,
    VmHashSite, VmRow, const_to_expr, parse_expr, parse_hash_site, parse_range,
    parse_vm_constraint_body,
};
// `i64_to_babybear` is the concrete-eval constant lowering (prover-only, `eval_c`).
use crate::lean_descriptor_air::i64_to_babybear;
use crate::lean_descriptor_air::{EffectVmDescriptor, RangeSpec};
use crate::plonky3_prover::{
    POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, create_config_with_fri, poseidon2_permute_expr_lanes,
    to_p3,
};
// The concrete permutation aux-witness fill is prover-only (`perm_aux`).
use crate::plonky3_prover::poseidon2_permute_aux_witness;

// ============================================================================
// Wire constants (the Rust mirror of `DescriptorIR2` §1/§7)
// ============================================================================

/// Stable wire id of the main table.
pub const TID_MAIN: usize = 0;
/// Stable wire id of the Poseidon2 chip table.
pub const TID_P2: usize = 1;
/// Stable wire id of the range (limb) table.
pub const TID_RANGE: usize = 2;
/// Stable wire id of the memory table.
pub const TID_MEMORY: usize = 3;
/// Stable wire id of the map-ops table.
pub const TID_MAP_OPS: usize = 4;
/// Wire id of `custom 0` = the bitwise-submask table (`DescriptorIR2.SUBMASK_TID`).
pub const TID_CUSTOM_SUBMASK: usize = 5;
/// Wire id of `custom 1` = the UNIVERSAL memory table (`DescriptorIR2.UMEM_TID`,
/// `docs/UNIVERSAL-MEMORY.md` — one Blum multiset over the `Domain × κ` address space).
pub const TID_UMEMORY: usize = 6;
/// Wire id of `custom 2` = the universal boundary table (declared `(domain, key)` addresses
/// with their init/final `Option` images).
pub const TID_UMEM_BOUNDARY: usize = 7;

/// The nullifier domain's wire code (`DescriptorIR2.domainCode .nullifiers`). The universal
/// memory table enforces the INSERT-ONLY discipline on this domain in-circuit (a write
/// installing `none` is refused), which is what turns a `none` read into the proved
/// freshness fact (`UniversalMemory.nullifier_fresh_sound`).
pub const NULLIFIER_DOMAIN: u32 = 3;
/// Domains are nibble-bounded on the wire (codes 0..4 deployed; new state components get new
/// codes, never new tables).
pub const DOMAIN_BOUND: u32 = 16;

/// The chip's INPUT-LANE COUNT: how many base-field input felts one chip row (= ONE Poseidon2
/// permutation) seeds. A chip tuple is `1 (arity) + CHIP_RATE (padded inputs) + 8 (output lanes)
/// = 20` wide. This is DISTINCT from the Poseidon2 sponge `rate` (8 = `babyBearD4W16.rate`,
/// pinned separately in [`POSEIDON2_SPONGE_RATE`] and the chip-param check): one permutation can
/// SEED up to `WIDTH − capacity` lanes regardless of the multi-block sponge rate. Phase
/// B-GATE-INPUT widened it `8 → 11` so a single permutation can absorb an 8-felt carrier + 3 new
/// limbs (the wide Merkle–Damgård step of the faithful 8-felt commitment, Phase B-ROTATION).
/// Phase H3 (native-8-felt Merkle root weld) widened it `11 → 16` = full `WIDTH`: the `node8`
/// arity-16 row compresses two 8-felt child digests `L8 ‖ R8` in ONE permutation (no capacity —
/// fixed-length compression domain-separated by the arity tag), reading lanes `0..8` for the
/// 8-felt node digest. Every per-node Merkle step (cap/heap/fields) routes through this lane.
pub const CHIP_RATE: usize = 16;
/// The Poseidon2 sponge rate in base-field elements (`babyBearD4W16.rate = rate_ext · d = 8`).
/// This is the REAL multi-block-sponge absorb width of the permutation — a cryptographic
/// parameter pinned in `circuit/src/poseidon2.rs` and the chip `params` JSON. It is NOT the
/// chip's input-lane count ([`CHIP_RATE`], the single-permutation seed width); the chip's
/// arity-11 wide row seeds 11 lanes of ONE permutation, which is well below `WIDTH = 16`.
pub const POSEIDON2_SPONGE_RATE: usize = 8;
/// The chip tuple arity on the wire: `1 (arity) + CHIP_RATE (inputs) + 8 (output lanes)`.
pub const CHIP_TUPLE_LEN: usize = CHIP_RATE + 1 + 8;
/// The wide single-permutation absorb arity (Phase B-GATE-INPUT): the 8-felt commitment carrier
/// `d8` (8 lanes) + `WIDE_K` new limbs/step. The wide Merkle–Damgård step `d8 ← perm(d8 ‖
/// new_limbs)[0..8]` of the faithful commitment (Phase B-ROTATION). `≤ CHIP_RATE ≤ WIDTH`.
pub const CHIP_WIDE_ARITY: usize = 11;
/// New limbs absorbed per wide commitment step (`CHIP_WIDE_ARITY − 8` carrier felts). The
/// deployed chain folds `[d, limb, limb, limb]` (1 carrier + 3 limbs); the wide step folds
/// `[d0..d7, limb, limb, limb]` (8 carrier + 3 limbs).
pub const WIDE_K: usize = CHIP_WIDE_ARITY - 8;
/// The `node8` Merkle-compression arity (Phase H3): two 8-felt child digests `L8 ‖ R8` seed
/// ALL 16 lanes of ONE permutation; lanes `0..8` are read as the node's 8-felt digest. This is
/// the COLLISION-FLOOR fix — a node whose children are 1-felt collides at ~2^15.5 regardless of
/// root width, so EVERY node must absorb full 8-felt children and emit a full 8-felt digest.
/// `= WIDTH = 16`: no capacity lane is reserved (fixed-length compression is domain-separated by
/// the arity tag itself — only a genuine 16-seed row answers an `arity == 16` lookup).
pub const CHIP_NODE8_ARITY: usize = 16;

/// The effect-mask width of the submask custom table (`EffectVmEmitV2.MASK_BITS`).
pub const SUBMASK_BITS: usize = 30;
/// Bit width of the memory serial-gap / boundary address range checks.
const MEM_GAP_BITS: usize = 30;

/// Bits per range-table limb: 4-bit nibble chunks against a `[0,16)` table.
///
/// MEASURED better than 8-bit byte limbs at every FRI grid point
/// (docs/PROOF-ECONOMICS.md §2c): the table's degree_bits drop 8 → 4, which shortens
/// the whole batch's FRI commit phase and the table's per-query Merkle paths
/// (transfer at the production `ir2_config` [DATED measurement, approximate]: 124.1 → 120.4 KiB, prove ~330 → ~55 ms —
/// the 2¹⁴-point byte-table LDE was the high-blowup prover's dominant cost), while
/// the doubled limb count adds only a few opened main columns per query.
pub const LIMB_BITS: usize = 4;
/// The range-table height. PINNED, prove- AND verify-side: the table AIR forces
/// `value = row index`, so its committed HEIGHT is its value range — a taller table
/// would silently widen every limb's admissible range. `verify_vm_descriptor2`
/// refuses any other height (`ir2_oversized_byte_table_refuses`).
pub const BYTE_TABLE_HEIGHT: usize = 1 << LIMB_BITS;

/// Minimum height for the auxiliary tables (chip / memory / boundary / map-ops).
/// Prover-only: it floors the witness table heights in `next_pow2` / `build_traces`.
const MIN_TABLE_HEIGHT: usize = 8;

// The shared bus names (namespaced so sibling modules' buses never collide).
const BUS_P2: &str = "ir2_p2";
const BUS_BYTE: &str = "ir2_byte";
const BUS_MEM_LOG: &str = "ir2_mem_log";
const BUS_MEM_CHECK: &str = "ir2_mem_check";
const BUS_MEM_ADDRS: &str = "ir2_mem_addrs";
const BUS_MAP_LOG: &str = "ir2_map_log";
const BUS_FACT: &str = "ir2_fact";
const BUS_UMEM_LOG: &str = "ir2_umem_log";
const BUS_UMEM_CHECK: &str = "ir2_umem_check";
const BUS_UMEM_ADDRS: &str = "ir2_umem_addrs";

/// The low-limb width of the CANONICAL BabyBear key decomposition
/// `key = hi4 · 2^27 + lo27` (BabyBear `p = 2^31 − 2^27 + 1 = 15 · 2^27 + 1`, so the canonical
/// range `[0, p)` is exactly `hi4 < 15 ∨ (hi4 = 15 ∧ lo27 = 0)` — the `is15 · lo27 = 0` tooth
/// makes the decomposition UNIQUE, which is what lets full-felt keys (hash images) be compared
/// as integers, lexicographically over `(hi4, lo27)`). The flat 30-bit address regime of the
/// EPOCH memory boundary cannot order hash-image keys; this one can.
const KEY_LO_BITS: usize = 27;
/// `2^27` as a field constant base for the canonical decomposition.
const KEY_HI_BASE: u64 = 1 << KEY_LO_BITS;
/// The top nibble value excluded from carrying a nonzero low limb (`p − 1 = 15 · 2^27`).
const KEY_HI_MAX: u64 = 15;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]).
const FACT_MARK: u32 = 0xFACF;

// ============================================================================
// The v2 descriptor mirror (Lean `EffectVmDescriptor2`, decoded from `emitVmJson2`)
// ============================================================================

/// Row semantics of a declared table (Lean `RowSemantics`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TableSem {
    /// One row per effect (the descriptor's own main trace).
    Main,
    /// One row per Poseidon2 permutation (params validated against the deployed pins).
    Poseidon2Chip,
    /// The limb table: rows `[v]` for `v ∈ [0, 2^bits)`.
    Range {
        /// The declared limb width.
        bits: usize,
    },
    /// One row per state access (offline memory checking).
    Memory,
    /// One row per boundary reconciliation (sorted-map opening).
    MapOps,
    /// One row per UNIVERSAL state access (the domain-tagged `Option`-valued Blum multiset).
    UMemory,
    /// One row per declared universal `(domain, key)` address (init/final `Option` images).
    UMemBoundary,
    /// The COHORT single-row specialization of [`TableSem::UMemBoundary`]: at most one declared
    /// `(domain, key)` address, so the inter-row lexicographic comparator + key decomposition the
    /// general boundary uses to establish `Nodup` are dropped (`Nodup` is `nodup_singleton`). The
    /// single-row discipline is enforced in-circuit; a multi-row witness is refused. Selected by
    /// the welded single-domain leg ([`crate::effect_vm_descriptors::weld_umem_into_rotated_descriptor`]).
    UMemBoundaryCohort,
}

/// A declared table (Lean `TableDef`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableDef2 {
    /// Stable wire id.
    pub id: usize,
    /// Display name.
    pub name: String,
    /// Column arity.
    pub arity: usize,
    /// Row semantics.
    pub sem: TableSem,
}

/// A lookup: the tuple of expressions is asserted to be a row of the named table
/// (Lean `Lookup`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupSpec {
    /// Target table wire id.
    pub table: usize,
    /// The tuple of column expressions.
    pub tuple: Vec<LeanExpr>,
}

/// Memory access kind (Lean `MemoryChecking.Kind`; wire codes 0 = read, 1 = write).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemKind {
    /// A read: returns its claimed previous value.
    Read,
    /// A write: installs `value` over the claimed previous tuple.
    Write,
}

impl MemKind {
    /// The memory-table `kind` column value.
    pub fn code(self) -> u32 {
        match self {
            MemKind::Read => 0,
            MemKind::Write => 1,
        }
    }
}

/// A read/write multiset row (Lean `MemOp`): the offline-memory-checking instrumentation
/// as expressions over the emitting main row. `guard` gates the contribution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemOpSpec {
    /// Selector guard (active iff it evaluates to 1).
    pub guard: LeanExpr,
    /// Address expression.
    pub addr: LeanExpr,
    /// Value returned (read) / installed (write).
    pub value: LeanExpr,
    /// Claimed latest prior value at the address.
    pub prev_value: LeanExpr,
    /// Claimed latest prior serial at the address.
    pub prev_serial: LeanExpr,
    /// Access kind.
    pub kind: MemKind,
}

/// A UNIVERSAL memory access row (Lean `UMemOp`): the offline-checking instrumentation against
/// the `Domain × κ` address space, with `Option`-valued cells as `(present, value)` pairs
/// (canonical encoding: `none ↦ (0, 0)`, `some v ↦ (1, v)`). The address is the literal PAIR
/// `(domain, key)` — the domain tag is its own bus coordinate, so the abstract injectivity
/// `(d, a) = (d, b) ↔ a = b` is wire-literal: NO hashing, not even at the boundary. This is
/// what makes nullifier freshness ONE read row returning `none`
/// (`UniversalMemory.nullifier_fresh_sound`) — Merkle-path-free, gap-opening-free.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UMemOpSpec {
    /// Selector guard (active iff it evaluates to 1).
    pub guard: LeanExpr,
    /// The STATIC domain code (Lean `domainCode`; the emission fixes the domain per op).
    pub domain: u32,
    /// The in-domain key expression (full-felt: hash images welcome).
    pub key: LeanExpr,
    /// Present bit of the returned (read) / installed (write) cell.
    pub present: LeanExpr,
    /// Payload of the returned / installed cell (0 when absent).
    pub value: LeanExpr,
    /// Present bit of the claimed latest prior cell.
    pub prev_present: LeanExpr,
    /// Payload of the claimed latest prior cell.
    pub prev_value: LeanExpr,
    /// Claimed latest prior serial.
    pub prev_serial: LeanExpr,
    /// Access kind.
    pub kind: MemKind,
}

/// Map reconciliation kind (Lean `MapOpKind`; wire codes 0/1/2/3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapKind {
    /// Membership read (root unchanged).
    Read,
    /// In-place value UPDATE at an existing key (root advances; the old and new
    /// leaves share the SAME sibling path).
    Write,
    /// Non-membership / bracketed-gap read (realized and tested; see `ir2_absent_*` tests
    /// and the map-absent table assembly). The `value` field is pinned to `const 0`
    /// and `new_root` is pinned to `root`.
    Absent,
    /// Sorted INSERT at a fresh key (root advances; the new leaf's membership path
    /// is against the NEW tree). Freshness must be established separately, e.g. by a
    /// paired `MapKind::Absent` opening against the same pre-root.
    Insert,
}

impl MapKind {
    /// The map-ops table `op` column value.
    pub fn code(self) -> u32 {
        match self {
            MapKind::Read => 0,
            MapKind::Write => 1,
            MapKind::Absent => 2,
            MapKind::Insert => 3,
        }
    }
}

/// A boundary reconciliation `(root, key, value, op) → new_root` (Lean `MapOp`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapOpSpec {
    /// Selector guard (active iff it evaluates to 1).
    pub guard: LeanExpr,
    /// The pre-root expression.
    pub root: LeanExpr,
    /// The map key expression.
    pub key: LeanExpr,
    /// The read/written value expression.
    pub value: LeanExpr,
    /// The post-root expression.
    pub new_root: LeanExpr,
    /// Reconciliation kind.
    pub op: MapKind,
}

/// An accumulator / recursive-proof-binding op (Lean `DescriptorIR2.ProofBind`): the Custom
/// row's `custom_proof_commitment` column (`commit`) and `custom_program_vk_hash` column (`vk`),
/// gated by `guard`. The denotation binds them to a VERIFYING external sub-proof of the
/// recursion engine — the row commits to the VERIFICATION of the external proof, rather than
/// trusting it. This is the constraint kind the four ROW-LOCAL kinds (lookup/mem/map/umem)
/// could not express: none folds in another STARK proof; this one rides the named recursion
/// argument (`joint_turn_recursive.rs` leaf verifier / `ivc_turn_chain.rs` aggregate prover),
/// exactly as `MemOp`/`UMemOp` ride the offline-memory argument rather than a row-local poly.
/// The binding is enforced at the per-turn FOLD, not by an in-AIR row gate: the rotated Custom
/// member PUBLISHES these columns as descriptor public inputs (Lean
/// `EffectVmEmitRotationV3.customPiExposure`, eight `.piBinding .first` pins), and the fold
/// connects those PIs to the custom sub-proof leaf's PI-commitment. The per-row `proof_bind`
/// denotation therefore stays a declaration (`True`, like `MemOp`/`UMemOp`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofBindSpec {
    /// Selector guard (active iff it evaluates to 1).
    pub guard: LeanExpr,
    /// The `custom_proof_commitment` column (bound to a verifying sub-proof's PI commitment).
    pub commit: LeanExpr,
    /// The `custom_program_vk_hash` column (bound to that sub-proof's program VK).
    pub vk: LeanExpr,
}

/// A two-row arithmetic expression (Lean `DescriptorIR2.WindowExpr`): a polynomial over BOTH
/// the current row (`Loc c`) and the next row (`Nxt c`). The base `LeanExpr` reads only the
/// current row, so a cross-row relation (the aggregation AIR's cumulative
/// `next[cum] = local[cum] + next[contribution]`) is inexpressible in it; `WindowExpr` adds the
/// `Nxt` leaf. `Loc c` is the faithful twin of `LeanExpr::Var c`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WindowExpr {
    /// Current-row column `c`.
    Loc(usize),
    /// Next-row column `c`.
    Nxt(usize),
    /// A signed integer constant.
    Const(i64),
    /// Field addition.
    Add(Box<WindowExpr>, Box<WindowExpr>),
    /// Field multiplication.
    Mul(Box<WindowExpr>, Box<WindowExpr>),
}

impl WindowExpr {
    /// Evaluate as an `AB::Expr` polynomial over the current (`local`) + next (`next`) rows.
    /// Mirrors Lean `WindowExpr.eval` reading `env.loc`/`env.nxt`, and the Rust hand-AIR's
    /// `local[..]` / `next[..]` reads inside a `builder.when_transition()` arm.
    pub(crate) fn eval_expr<AB>(&self, local: &[AB::Var], next: &[AB::Var]) -> AB::Expr
    where
        AB: AirBuilder,
        AB::F: PrimeField32,
    {
        match self {
            WindowExpr::Loc(i) => local[*i].into(),
            WindowExpr::Nxt(i) => next[*i].into(),
            WindowExpr::Const(c) => const_to_expr::<AB>(*c),
            WindowExpr::Add(a, b) => {
                a.eval_expr::<AB>(local, next) + b.eval_expr::<AB>(local, next)
            }
            WindowExpr::Mul(a, b) => {
                a.eval_expr::<AB>(local, next) * b.eval_expr::<AB>(local, next)
            }
        }
    }

    /// The maximum column index referenced (over both row tags), if any. The descriptor's
    /// `windowGate` bounds check uses this; degree is left to the batch prover's symbolic
    /// analysis (the cumulative-sum bodies are linear).
    fn max_var(&self) -> Option<usize> {
        match self {
            WindowExpr::Loc(i) | WindowExpr::Nxt(i) => Some(*i),
            WindowExpr::Const(_) => None,
            WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => match (a.max_var(), b.max_var()) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            },
        }
    }
}

/// A windowed constraint (Lean `DescriptorIR2.WindowConstraint`): the polynomial `body` (over
/// the current+next row) must vanish. `on_transition = true` ⇒ asserted only on the transition
/// (every row but the last — the Rust `builder.when_transition()` arm); `false` ⇒ asserted on
/// every row (including the last, where `Nxt` is the wrap row).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowGateSpec {
    /// The two-row polynomial body.
    pub body: WindowExpr,
    /// Assert only on the transition (`true`) vs. every row (`false`).
    pub on_transition: bool,
}

/// One v2 constraint: a v1 form embedded whole, or one of the new kinds
/// (Lean `VmConstraint2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmConstraint2 {
    /// An embedded v1 constraint form.
    Base(VmConstraint),
    /// A lookup into a declared table.
    Lookup(LookupSpec),
    /// A memory-table access row.
    MemOp(MemOpSpec),
    /// A map-ops-table reconciliation row.
    MapOp(MapOpSpec),
    /// A UNIVERSAL memory-table access row (the one-Blum-multiset leg).
    UMemOp(UMemOpSpec),
    /// An accumulator / recursive-proof-binding row (the Custom leg — rides the recursion
    /// argument, not a committed table).
    ProofBind(ProofBindSpec),
    /// A two-row windowed gate (the cumulative-sum primitive: a polynomial over the current
    /// AND next rows, asserted on the transition or every row). The aggregation AIR's two
    /// running cumulatives are this kind.
    WindowGate(WindowGateSpec),
}

/// The Rust mirror of Lean's `EffectVmDescriptor2` (decoded from `emitVmJson2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectVmDescriptor2 {
    /// AIR identity string.
    pub name: String,
    /// The main-trace base width.
    pub trace_width: usize,
    /// Number of public-input slots.
    pub public_input_count: usize,
    /// The declared tables.
    pub tables: Vec<TableDef2>,
    /// The constraint list (v2 grammar).
    pub constraints: Vec<VmConstraint2>,
    /// Legacy v1 hash-site carrier (must be EMPTY for the v2 assembly; graduated
    /// descriptors carry their sites as chip lookups).
    pub hash_sites: Vec<VmHashSite>,
    /// Legacy v1 range carrier (must be EMPTY for the v2 assembly).
    pub ranges: Vec<RangeSpec>,
}

/// Either wire shape, dispatched on the `"ir"` key (`parse_vm_descriptor_any`).
#[derive(Clone, Debug)]
pub enum AnyVmDescriptor {
    /// A v1 descriptor (no `"ir"` key): proves through `lean_descriptor_air`.
    V1(EffectVmDescriptor),
    /// A v2 descriptor (`"ir":2`): proves through this module.
    V2(EffectVmDescriptor2),
}

// ============================================================================
// JSON decode (the v2 grammar; byte-pinned by the Lean `#guard` golden)
// ============================================================================

fn parse_array<T>(
    c: &mut JsonCursor,
    mut item: impl FnMut(&mut JsonCursor) -> Result<T, String>,
) -> Result<Vec<T>, String> {
    c.expect(b'[')?;
    let mut v = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
        return Ok(v);
    }
    loop {
        v.push(item(c)?);
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b']') => {
                c.expect(b']')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or ']' in array, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }
    Ok(v)
}

fn parse_usize(c: &mut JsonCursor, what: &str) -> Result<usize, String> {
    let n = c.parse_int()?;
    if n < 0 {
        return Err(format!("negative {what} {n}"));
    }
    Ok(n as usize)
}

/// Validate the chip `params` object against the DEPLOYED Poseidon2 pins
/// (`babyBearD4W16` ↔ `circuit/src/poseidon2.rs`). A mismatch is a refusal, not a warning:
/// the chip table's row semantics is "the real permutation" and these are its parameters.
fn parse_chip_params(c: &mut JsonCursor) -> Result<(), String> {
    c.expect(b'{')?;
    let expected_num: &[(&str, i64)] = &[
        ("field_modulus", BABYBEAR_P as i64),
        ("d", 4),
        ("width", POSEIDON2_WIDTH as i64),
        ("sbox_degree", 7),
        ("sbox_registers", 1),
        ("half_full_rounds", 4),
        ("partial_rounds", 13),
        // The REAL Poseidon2 sponge rate (8), NOT the chip input-lane count (`CHIP_RATE` = 11).
        ("rate", POSEIDON2_SPONGE_RATE as i64),
    ];
    loop {
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "rc_source" => {
                let s = c.parse_string()?;
                if s != "BABYBEAR_POSEIDON2_RC_16" {
                    return Err(format!("chip params rc_source \"{s}\" != deployed source"));
                }
            }
            "internal_diag_source" => {
                let s = c.parse_string()?;
                if s != "BABYBEAR_POSEIDON2_INTERNAL_DIAG_16" {
                    return Err(format!(
                        "chip params internal_diag_source \"{s}\" != deployed source"
                    ));
                }
            }
            other => {
                let v = c.parse_int()?;
                let Some(&(_, want)) = expected_num.iter().find(|(k, _)| *k == other) else {
                    return Err(format!("unknown chip param \"{other}\""));
                };
                if v != want {
                    return Err(format!("chip param {other} = {v}, deployed pin is {want}"));
                }
            }
        }
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in chip params, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }
    Ok(())
}

fn parse_table_def(c: &mut JsonCursor) -> Result<TableDef2, String> {
    c.expect(b'{')?;
    let mut id: Option<usize> = None;
    let mut name: Option<String> = None;
    let mut arity: Option<usize> = None;
    let mut sem_tag: Option<String> = None;
    let mut bits: Option<usize> = None;
    loop {
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "id" => id = Some(parse_usize(c, "table id")?),
            "name" => name = Some(c.parse_string()?),
            "arity" => arity = Some(parse_usize(c, "table arity")?),
            "sem" => sem_tag = Some(c.parse_string()?),
            "bits" => bits = Some(parse_usize(c, "range bits")?),
            "params" => parse_chip_params(c)?,
            other => return Err(format!("unknown table-def key \"{other}\"")),
        }
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in table def, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }
    let sem = match sem_tag.as_deref() {
        Some("main") => TableSem::Main,
        Some("poseidon2_chip") => TableSem::Poseidon2Chip,
        Some("range") => TableSem::Range {
            bits: bits.ok_or("range table def missing \"bits\"")?,
        },
        Some("memory") => TableSem::Memory,
        Some("map_ops") => TableSem::MapOps,
        Some("umemory") => TableSem::UMemory,
        Some("umem_boundary") => TableSem::UMemBoundary,
        Some("umem_boundary_cohort") => TableSem::UMemBoundaryCohort,
        Some(other) => return Err(format!("unknown table sem \"{other}\"")),
        None => return Err("table def missing \"sem\"".to_string()),
    };
    Ok(TableDef2 {
        id: id.ok_or("table def missing \"id\"")?,
        name: name.ok_or("table def missing \"name\"")?,
        arity: arity.ok_or("table def missing \"arity\"")?,
        sem,
    })
}

/// Parse one `<window_expr>` object: `{"t":"loc"|"nxt"|"const"|"add"|"mul", …}` (Lean
/// `WindowExpr.toJson`). `loc`/`nxt` carry a column index `c`; the arithmetic nodes reuse the
/// `l`/`r` shape of `LeanExpr`.
fn parse_window_expr(c: &mut JsonCursor) -> Result<WindowExpr, String> {
    c.expect(b'{')?;
    c.expect_key("t")?;
    let tag = c.parse_string()?;
    let expr = match tag.as_str() {
        "loc" => {
            c.expect(b',')?;
            c.expect_key("c")?;
            WindowExpr::Loc(parse_usize(c, "window loc col")?)
        }
        "nxt" => {
            c.expect(b',')?;
            c.expect_key("c")?;
            WindowExpr::Nxt(parse_usize(c, "window nxt col")?)
        }
        "const" => {
            c.expect(b',')?;
            c.expect_key("v")?;
            WindowExpr::Const(c.parse_int()?)
        }
        "add" | "mul" => {
            c.expect(b',')?;
            c.expect_key("l")?;
            let l = parse_window_expr(c)?;
            c.expect(b',')?;
            c.expect_key("r")?;
            let r = parse_window_expr(c)?;
            if tag == "add" {
                WindowExpr::Add(Box::new(l), Box::new(r))
            } else {
                WindowExpr::Mul(Box::new(l), Box::new(r))
            }
        }
        other => return Err(format!("unknown window expr tag \"{other}\"")),
    };
    c.expect(b'}')?;
    Ok(expr)
}

fn parse_constraint2(c: &mut JsonCursor) -> Result<VmConstraint2, String> {
    c.expect(b'{')?;
    c.expect_key("t")?;
    let tag = c.parse_string()?;
    let out = match tag.as_str() {
        "lookup" => {
            c.expect(b',')?;
            c.expect_key("table")?;
            let table = parse_usize(c, "lookup table id")?;
            c.expect(b',')?;
            c.expect_key("tuple")?;
            let tuple = parse_array(c, parse_expr)?;
            VmConstraint2::Lookup(LookupSpec { table, tuple })
        }
        "mem_op" => {
            c.expect(b',')?;
            c.expect_key("kind")?;
            let kind = match c.parse_string()?.as_str() {
                "read" => MemKind::Read,
                "write" => MemKind::Write,
                other => return Err(format!("unknown mem_op kind \"{other}\"")),
            };
            c.expect(b',')?;
            c.expect_key("guard")?;
            let guard = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("addr")?;
            let addr = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("value")?;
            let value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_value")?;
            let prev_value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_serial")?;
            let prev_serial = parse_expr(c)?;
            VmConstraint2::MemOp(MemOpSpec {
                guard,
                addr,
                value,
                prev_value,
                prev_serial,
                kind,
            })
        }
        "umem_op" => {
            c.expect(b',')?;
            c.expect_key("kind")?;
            let kind = match c.parse_string()?.as_str() {
                "read" => MemKind::Read,
                "write" => MemKind::Write,
                other => return Err(format!("unknown umem_op kind \"{other}\"")),
            };
            c.expect(b',')?;
            c.expect_key("domain")?;
            let domain = parse_usize(c, "umem_op domain")? as u32;
            c.expect(b',')?;
            c.expect_key("guard")?;
            let guard = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("key")?;
            let key = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("present")?;
            let present = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("value")?;
            let value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_present")?;
            let prev_present = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_value")?;
            let prev_value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_serial")?;
            let prev_serial = parse_expr(c)?;
            VmConstraint2::UMemOp(UMemOpSpec {
                guard,
                domain,
                key,
                present,
                value,
                prev_present,
                prev_value,
                prev_serial,
                kind,
            })
        }
        "map_op" => {
            c.expect(b',')?;
            c.expect_key("op")?;
            let op = match c.parse_string()?.as_str() {
                "read" => MapKind::Read,
                "write" => MapKind::Write,
                "absent" => MapKind::Absent,
                "insert" => MapKind::Insert,
                other => return Err(format!("unknown map_op kind \"{other}\"")),
            };
            c.expect(b',')?;
            c.expect_key("guard")?;
            let guard = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("root")?;
            let root = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("key")?;
            let key = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("value")?;
            let value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("new_root")?;
            let new_root = parse_expr(c)?;
            VmConstraint2::MapOp(MapOpSpec {
                guard,
                root,
                key,
                value,
                new_root,
                op,
            })
        }
        "proof_bind" => {
            c.expect(b',')?;
            c.expect_key("guard")?;
            let guard = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("commit")?;
            let commit = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("vk")?;
            let vk = parse_expr(c)?;
            VmConstraint2::ProofBind(ProofBindSpec { guard, commit, vk })
        }
        "window_gate" => {
            c.expect(b',')?;
            c.expect_key("on_transition")?;
            let on_transition = c.parse_bool()?;
            c.expect(b',')?;
            c.expect_key("body")?;
            let body = parse_window_expr(c)?;
            VmConstraint2::WindowGate(WindowGateSpec {
                body,
                on_transition,
            })
        }
        v1tag => VmConstraint2::Base(parse_vm_constraint_body(c, v1tag)?),
    };
    c.expect(b'}')?;
    Ok(out)
}

/// **`parse_vm_descriptor2`** — decode a Lean `emitVmJson2` string (`"ir":2`).
pub fn parse_vm_descriptor2(json: &str) -> Result<EffectVmDescriptor2, String> {
    match parse_vm_descriptor_any(json)? {
        AnyVmDescriptor::V2(d) => Ok(d),
        AnyVmDescriptor::V1(_) => {
            Err("descriptor has no \"ir\" key (v1 wire); use parse_vm_descriptor".to_string())
        }
    }
}

/// **`parse_vm_descriptor_any`** — the versioned dispatcher: a missing `"ir"` key is wire
/// version 1 (the untouched `emitVmJson` grammar, re-encoded as `AnyVmDescriptor::V1`);
/// `"ir":2` is the multi-table grammar. Both registries live until the flag-day.
pub fn parse_vm_descriptor_any(json: &str) -> Result<AnyVmDescriptor, String> {
    let mut c = JsonCursor::new(json);
    c.expect(b'{')?;

    let mut name: Option<String> = None;
    let mut ir: Option<usize> = None;
    let mut trace_width: Option<usize> = None;
    let mut public_input_count: Option<usize> = None;
    let mut tables: Vec<TableDef2> = Vec::new();
    let mut constraints: Option<Vec<VmConstraint2>> = None;
    let mut hash_sites: Vec<VmHashSite> = Vec::new();
    let mut ranges: Vec<RangeSpec> = Vec::new();

    loop {
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "name" => name = Some(c.parse_string()?),
            "ir" => ir = Some(parse_usize(&mut c, "ir version")?),
            "trace_width" => trace_width = Some(parse_usize(&mut c, "trace_width")?),
            "public_input_count" => {
                public_input_count = Some(parse_usize(&mut c, "public_input_count")?)
            }
            "tables" => tables = parse_array(&mut c, parse_table_def)?,
            "constraints" => constraints = Some(parse_array(&mut c, parse_constraint2)?),
            "hash_sites" => hash_sites = parse_array(&mut c, parse_hash_site)?,
            "ranges" => ranges = parse_array(&mut c, parse_range)?,
            other => return Err(format!("unknown top-level key \"{other}\"")),
        }
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in descriptor, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }

    let name = name.ok_or("descriptor missing \"name\"")?;
    let trace_width = trace_width.ok_or("descriptor missing \"trace_width\"")?;
    let public_input_count =
        public_input_count.ok_or("descriptor missing \"public_input_count\"")?;
    let constraints = constraints.ok_or("descriptor missing \"constraints\"")?;

    match ir {
        None => {
            // v1 wire: no tables, no v2-only constraint kinds.
            if !tables.is_empty() {
                return Err("v1 descriptor (no \"ir\") declares tables".to_string());
            }
            let mut v1 = Vec::with_capacity(constraints.len());
            for k in constraints {
                match k {
                    VmConstraint2::Base(b) => v1.push(b),
                    other => {
                        return Err(format!(
                            "v1 descriptor (no \"ir\") carries a v2-only constraint: {other:?}"
                        ));
                    }
                }
            }
            Ok(AnyVmDescriptor::V1(EffectVmDescriptor {
                name,
                trace_width,
                public_input_count,
                constraints: v1,
                hash_sites,
                ranges,
            }))
        }
        Some(2) => Ok(AnyVmDescriptor::V2(EffectVmDescriptor2 {
            name,
            trace_width,
            public_input_count,
            tables,
            constraints,
            hash_sites,
            ranges,
        })),
        Some(v) => Err(format!("unsupported descriptor ir version {v}")),
    }
}

// ============================================================================
// Layout: byte-limb decomposition geometry + the main-trace aux blocks
// ============================================================================

/// Limb geometry of a `bits`-wide byte decomposition: `(num_limbs, top_bits)`.
/// The top limb is bit-bound when `top_bits < 8` (the tight bound); full limbs are
/// byte-bus lookups.
const fn limb_geom(bits: usize) -> (usize, usize) {
    let n = bits.div_ceil(LIMB_BITS);
    (n, bits - (n - 1) * LIMB_BITS)
}

/// Aux columns one `bits`-wide decomposition adds (limbs + top bits when partial).
const fn decomp_cols(bits: usize) -> usize {
    let (n, top) = limb_geom(bits);
    n + if top < LIMB_BITS { top } else { 0 }
}

/// One declared range lookup, resolved to its aux block in the extended main trace.
#[derive(Clone, Debug)]
struct RangeBlock {
    /// The range-checked base wire (the lookup tuple's single `Var`).
    wire: usize,
    /// Declared bit width (from the range table def).
    bits: usize,
    /// First limb column (extended-trace index).
    limb0: usize,
}

/// One declared submask lookup, resolved to its bit blocks.
#[derive(Clone, Debug)]
struct SubmaskBlock {
    /// The kept (must-be-subset) mask expression — lookup tuple\[0\].
    keep: LeanExpr,
    /// The held (superset) mask expression — lookup tuple\[1\].
    held: LeanExpr,
    /// First bit column of the keep decomposition.
    keep0: usize,
    /// First bit column of the held decomposition.
    held0: usize,
}

/// The resolved main-instance layout: base wires, then per-range limb blocks, then
/// per-submask bit blocks.
#[derive(Clone, Debug)]
struct MainLayout {
    width: usize,
    ranges: Vec<RangeBlock>,
    submasks: Vec<SubmaskBlock>,
}

impl MainLayout {
    fn build(desc: &EffectVmDescriptor2) -> Result<Self, String> {
        let range_bits = desc.tables.iter().find_map(|t| match t.sem {
            TableSem::Range { bits } => Some(bits),
            _ => None,
        });
        let mut next = desc.trace_width;
        let mut ranges = Vec::new();
        let mut submasks = Vec::new();
        for (ci, k) in desc.constraints.iter().enumerate() {
            let VmConstraint2::Lookup(l) = k else {
                continue;
            };
            match l.table {
                TID_RANGE => {
                    let bits = range_bits.ok_or_else(|| {
                        format!("constraint {ci}: range lookup but no range table declared")
                    })?;
                    if l.tuple.len() != 1 {
                        return Err(format!(
                            "constraint {ci}: range lookup tuple arity {} != 1",
                            l.tuple.len()
                        ));
                    }
                    let LeanExpr::Var(wire) = l.tuple[0] else {
                        return Err(format!(
                            "constraint {ci}: range lookup tuple must be a bare column \
                             (graduateV1 emits `.var wire`)"
                        ));
                    };
                    ranges.push(RangeBlock {
                        wire,
                        bits,
                        limb0: next,
                    });
                    next += decomp_cols(bits);
                }
                TID_CUSTOM_SUBMASK => {
                    if l.tuple.len() != 2 {
                        return Err(format!(
                            "constraint {ci}: submask lookup tuple arity {} != 2",
                            l.tuple.len()
                        ));
                    }
                    let keep0 = next;
                    let held0 = next + SUBMASK_BITS;
                    next += 2 * SUBMASK_BITS;
                    submasks.push(SubmaskBlock {
                        keep: l.tuple[0].clone(),
                        held: l.tuple[1].clone(),
                        keep0,
                        held0,
                    });
                }
                TID_P2 => {
                    if l.tuple.len() != CHIP_TUPLE_LEN {
                        return Err(format!(
                            "constraint {ci}: chip lookup tuple arity {} != {CHIP_TUPLE_LEN}",
                            l.tuple.len()
                        ));
                    }
                }
                TID_MAIN | TID_MEMORY | TID_MAP_OPS | TID_UMEMORY | TID_UMEM_BOUNDARY => {
                    return Err(format!(
                        "constraint {ci}: lookups into table {} are not part of the graduated \
                         grammar (state accesses are mem_op / map_op / umem_op constraints)",
                        l.table
                    ));
                }
                other => {
                    return Err(format!(
                        "constraint {ci}: custom table id {other} has no realized relation \
                         (only the submask table, id {TID_CUSTOM_SUBMASK}, is bound; the \
                         custom-table contents manifest is the named IR follow-up)"
                    ));
                }
            }
        }
        Ok(MainLayout {
            width: next,
            ranges,
            submasks,
        })
    }
}

/// Bounds- and shape-check a v2 descriptor for assembly. Returns the resolved layout.
fn check_descriptor2(desc: &EffectVmDescriptor2) -> Result<MainLayout, String> {
    if !desc.hash_sites.is_empty() || !desc.ranges.is_empty() {
        return Err(
            "v2 assembly requires a GRADUATED descriptor (empty hash_sites/ranges carriers); \
             embedV1-shaped descriptors keep the v1 path during the epoch"
                .to_string(),
        );
    }
    let w = desc.trace_width;
    let chk = |e: &LeanExpr, what: &str, ci: usize| -> Result<(), String> {
        if let Some(m) = e.max_var()
            && m >= w
        {
            return Err(format!(
                "constraint {ci}: {what} references column {m} >= trace_width {w}"
            ));
        }
        Ok(())
    };
    for (ci, k) in desc.constraints.iter().enumerate() {
        match k {
            VmConstraint2::Base(VmConstraint::Gate(body))
            | VmConstraint2::Base(VmConstraint::Boundary { body, .. }) => {
                chk(body, "gate/boundary body", ci)?
            }
            VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
                if EFFECTVM_STATE_BEFORE_BASE + hi >= w || EFFECTVM_STATE_AFTER_BASE + lo >= w {
                    return Err(format!("constraint {ci}: transition out of bounds"));
                }
            }
            VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                if *col >= w {
                    return Err(format!("constraint {ci}: pi_binding col out of bounds"));
                }
                if *pi_index >= desc.public_input_count {
                    return Err(format!(
                        "constraint {ci}: pi_binding pi_index out of bounds"
                    ));
                }
            }
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    chk(e, "lookup tuple element", ci)?;
                }
            }
            VmConstraint2::MemOp(m) => {
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    chk(e, "mem_op field", ci)?;
                }
            }
            VmConstraint2::MapOp(m) => {
                if m.op == MapKind::Absent && m.value != LeanExpr::Const(0) {
                    // The absent denotation ignores the value; the wire convention pins it to
                    // the literal 0 so the map-log bus tuple is canonical (the MapAbsent
                    // table receives the 0 coordinate).
                    return Err(format!(
                        "constraint {ci}: map_op kind `absent` must carry value `const 0` \
                         (the non-membership read has no value; the wire pins the canonical 0)"
                    ));
                }
                for e in [&m.guard, &m.root, &m.key, &m.value, &m.new_root] {
                    chk(e, "map_op field", ci)?;
                }
            }
            VmConstraint2::UMemOp(m) => {
                if m.domain >= DOMAIN_BOUND {
                    return Err(format!(
                        "constraint {ci}: umem_op domain {} out of the nibble bound {}",
                        m.domain, DOMAIN_BOUND
                    ));
                }
                if m.domain == NULLIFIER_DOMAIN
                    && m.kind == MemKind::Write
                    && m.present == LeanExpr::Const(0)
                {
                    // The INSERT-ONLY discipline, statically-violating shape: a nullifier
                    // write installing a definitely-absent cell (Lean
                    // `umemNullifierInsertOnly` — nobody un-spends). Dynamic `present`
                    // expressions pass here and meet the in-circuit tooth
                    // (`is_null·kind·(1−present)`) row-by-row.
                    return Err(format!(
                        "constraint {ci}: nullifier-domain umem_op write installs a \
                         definitely-absent cell (insert-only: nobody un-spends; \
                         UniversalMemory.InsertOnlyAt)"
                    ));
                }
                for e in [
                    &m.guard,
                    &m.key,
                    &m.present,
                    &m.value,
                    &m.prev_present,
                    &m.prev_value,
                    &m.prev_serial,
                ] {
                    chk(e, "umem_op field", ci)?;
                }
            }
            VmConstraint2::ProofBind(m) => {
                // The proof-binding op declares the recursion binding; its columns must be in
                // bounds. They are PUBLISHED as descriptor PIs (the rotated Custom member's eight
                // `customPiExposure` pins) and bound to the verifying sub-proof's PI commitment /
                // VK at the per-turn FOLD via the recursion argument — not by a row-local poly here.
                for e in [&m.guard, &m.commit, &m.vk] {
                    chk(e, "proof_bind field", ci)?;
                }
            }
            VmConstraint2::WindowGate(g) => {
                // The window body reads BOTH rows; every referenced column (`loc`/`nxt`) must
                // lie inside the main width.
                if let Some(m) = g.body.max_var()
                    && m >= w
                {
                    return Err(format!(
                        "constraint {ci}: window_gate body references column {m} >= \
                             trace_width {w}"
                    ));
                }
            }
        }
    }
    MainLayout::build(desc)
}

// ============================================================================
// The REAL-evaluator row-local accept oracle (the faithfulness-differential leg)
// ============================================================================

/// A row window over a borrowed `(local, next)` pair, replaying the deployed
/// `Ir2Air::Main::eval` ROW-LOCALLY against a real witness so a differential can call the
/// ACTUAL deployed evaluator (not a hand transcription) for the row-local constraint arms.
///
/// `assert_zero` checks the constraint vanishes (recording a failure if not); the cross-table
/// LogUp bus pushes (`InteractionBuilder::push_interaction` / `push_local_interaction`) are
/// SWALLOWED — exactly the semantics of the deployed debug constraint check, which evaluates a
/// single AIR's row-local algebra and leaves the multiset balance to the batch assembly. The
/// pattern mirrors p3-lookup's own `MiniLookupBuilder`/`DebugConstraintBuilder`: those swallow
/// the bus sends too. So `ir2_eval_accepts` is FAITHFUL on the row-local arms (Gate /
/// Transition / WindowGate / range-recomposition / submask bit gates) and SILENT on the bus
/// arms (chip/byte lookups, mem/map/umem log sends) — the precise split a caller must respect.
struct Ir2RowLocalBuilder<'a> {
    local: &'a [P3BabyBear],
    next: &'a [P3BabyBear],
    public_values: &'a [P3BabyBear],
    /// An empty preprocessed window (the IR-v2 Main AIR carries no preprocessed columns); held
    /// here so `preprocessed()` can return a reference into it.
    empty_prep: p3_air::RowWindow<'a, P3BabyBear>,
    row: usize,
    height: usize,
    /// Set once any row-local `assert_zero` body is non-zero.
    failed: bool,
}

impl<'a> p3_air::AirBuilder for Ir2RowLocalBuilder<'a> {
    type F = P3BabyBear;
    type Expr = P3BabyBear;
    type Var = P3BabyBear;
    type PreprocessedWindow = p3_air::RowWindow<'a, P3BabyBear>;
    type MainWindow = p3_air::RowWindow<'a, P3BabyBear>;
    type PublicVar = P3BabyBear;
    type PeriodicVar = P3BabyBear;

    fn main(&self) -> Self::MainWindow {
        p3_air::RowWindow::from_two_rows(self.local, self.next)
    }

    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        // The IR-v2 Main AIR carries no preprocessed columns; an empty window suffices.
        &self.empty_prep
    }

    fn is_first_row(&self) -> Self::Expr {
        P3BabyBear::from_bool(self.row == 0)
    }

    fn is_last_row(&self) -> Self::Expr {
        P3BabyBear::from_bool(self.row + 1 == self.height)
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        assert!(size <= 2, "only two-row windows are supported, got {size}");
        P3BabyBear::from_bool(self.row + 1 < self.height)
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        // The DebugConstraintBuilder semantics: under a `when_*` filter, the selector has been
        // folded into the expression already (FilteredAirBuilder multiplies the body by the
        // condition before delegating here), so a vanishing selector makes the body zero and
        // this passes — exactly the `when_transition`/`when_first_row`/`when_last_row` domains.
        if !x.into().is_zero() {
            self.failed = true;
        }
    }

    fn public_values(&self) -> &[Self::PublicVar] {
        self.public_values
    }
}

impl<'a> p3_air::ExtensionBuilder for Ir2RowLocalBuilder<'a> {
    type EF = P3BabyBear;
    type ExprEF = P3BabyBear;
    type VarEF = P3BabyBear;

    fn assert_zero_ext<I: Into<Self::ExprEF>>(&mut self, x: I) {
        if !x.into().is_zero() {
            self.failed = true;
        }
    }
}

impl<'a> PermutationAirBuilder for Ir2RowLocalBuilder<'a> {
    type MP = p3_air::RowWindow<'a, P3BabyBear>;
    type RandomVar = P3BabyBear;
    type PermutationVar = P3BabyBear;

    fn permutation(&self) -> Self::MP {
        p3_air::RowWindow::from_two_rows(&[], &[])
    }

    fn permutation_randomness(&self) -> &[Self::RandomVar] {
        &[]
    }

    fn permutation_values(&self) -> &[Self::PermutationVar] {
        &[]
    }
}

impl<'a> InteractionBuilder for Ir2RowLocalBuilder<'a> {
    fn push_interaction<E: Into<Self::Expr>>(
        &mut self,
        _bus_name: &str,
        fields: impl IntoIterator<Item = E>,
        _count: impl Into<Self::Expr>,
        _count_weight: u32,
    ) {
        // Bus sends/receives are the cross-table multiset leg — not row-local algebra. Drain
        // the iterator (matching the deployed debug builder) and otherwise ignore.
        fields.into_iter().for_each(drop);
    }

    fn push_local_interaction(
        &mut self,
        tuples: impl IntoIterator<Item = (Vec<Self::Expr>, Self::Expr)>,
    ) {
        tuples.into_iter().for_each(drop);
    }
}

/// **THE REAL-EVALUATOR ROW-LOCAL ACCEPT ORACLE.** Build the DEPLOYED `Ir2Air::Main` AIR for
/// `desc`, fill the per-table layout columns over `base_rows`, and run the ACTUAL
/// `Ir2Air::eval` (the deployed verifier's constraint evaluator) ROW-BY-ROW. Returns `true` iff
/// every ROW-LOCAL constraint vanishes on every row.
///
/// This is the v2 analog of [`crate::lean_descriptor_air::descriptor_air_accepts`] — but where
/// the v1 helper drives the WHOLE single AIR through `check_all_constraints`, the v2 Main AIR
/// also emits cross-table LogUp bus messages (`PermutationCheckBus` / `LookupBus` sends for the
/// chip / byte / memory / map-ops tables) that no single-AIR row-local check can evaluate. Those
/// bus pushes are SWALLOWED (see [`Ir2RowLocalBuilder`]); the multiset balance is the batch
/// assembly's job (`prove_batch`/`verify_batch`). So this oracle is FAITHFUL on the row-local
/// arms — `Base(Gate)`, `Base(Transition)`, `WindowGate{on_transition}`, the every-row
/// `WindowGate`, plus the range-recomposition + submask bit gates — and SILENT on the bus arms.
///
/// `base_rows` are the `desc.trace_width`-column main rows. The layout columns (range limbs,
/// submask bits) appended past `trace_width` are NOT filled here: callers that exercise the
/// row-local arms use descriptors with NO range/submask lookups (so `MainLayout` adds no
/// columns and the recomposition gates are absent). A descriptor that DOES declare such lookups
/// will see those gates fire over zero-filled limb columns; that path is out of this oracle's
/// row-local-faithful scope and the caller must not rely on it.
pub fn ir2_eval_accepts(
    desc: &EffectVmDescriptor2,
    base_rows: &[Vec<P3BabyBear>],
    public_inputs: &[P3BabyBear],
) -> bool {
    let layout = match check_descriptor2(desc) {
        Ok(l) => l,
        Err(_) => return false,
    };
    if base_rows.is_empty() || public_inputs.len() != desc.public_input_count {
        return false;
    }
    let air = Ir2Air::Main {
        desc: desc.clone(),
        layout: MainLayoutPub(layout),
    };
    let width = match &air {
        Ir2Air::Main { layout, .. } => layout.0.width,
        _ => unreachable!(),
    };
    // Materialize the full-width rows (base columns + zero-filled layout columns).
    let height = base_rows.len();
    let mut rows: Vec<Vec<P3BabyBear>> = Vec::with_capacity(height);
    for r in base_rows {
        if r.len() > width {
            return false;
        }
        let mut row = r.clone();
        row.resize(width, P3BabyBear::ZERO);
        rows.push(row);
    }
    for row_index in 0..height {
        let next_index = (row_index + 1) % height;
        let mut builder = Ir2RowLocalBuilder {
            local: &rows[row_index],
            next: &rows[next_index],
            public_values: public_inputs,
            empty_prep: p3_air::RowWindow::from_two_rows(&[], &[]),
            row: row_index,
            height,
            failed: false,
        };
        air.eval(&mut builder);
        if builder.failed {
            return false;
        }
    }
    true
}

/// `i64`-valued convenience wrapper over [`ir2_eval_accepts`] so callers (the faithfulness
/// differential) need not depend on `p3-baby-bear` directly: the `(row, pi)` integers are lifted
/// to canonical BabyBear felts (the same `i64_to_babybear` lowering the descriptor evaluator
/// uses for its constants) and the REAL `Ir2Air::Main` row-local evaluator is run.
pub fn ir2_eval_accepts_i64(
    desc: &EffectVmDescriptor2,
    base_rows: &[Vec<i64>],
    public_inputs: &[i64],
) -> bool {
    let rows: Vec<Vec<P3BabyBear>> = base_rows
        .iter()
        .map(|r| r.iter().map(|&x| to_p3(i64_to_babybear(x))).collect())
        .collect();
    let pis: Vec<P3BabyBear> = public_inputs
        .iter()
        .map(|&x| to_p3(i64_to_babybear(x)))
        .collect();
    ir2_eval_accepts(desc, &rows, &pis)
}

// ============================================================================
// The multi-table AIR (one enum type: prove_batch is monomorphic in the AIR)
// ============================================================================

// -- Memory table layout (one row per access, log order). --
const MEM_ADDR: usize = 0;
const MEM_VALUE: usize = 1;
const MEM_PREV_VALUE: usize = 2;
const MEM_PREV_SERIAL: usize = 3;
const MEM_KIND: usize = 4;
const MEM_SERIAL: usize = 5;
const MEM_IS_REAL: usize = 6;
const MEM_GAP: usize = 7;
const MEM_GAP_LIMB0: usize = 8;
const MEM_WIDTH: usize = MEM_GAP_LIMB0 + decomp_cols(MEM_GAP_BITS); // 8 + 10 = 18

// -- Memory boundary layout (one row per declared address, strictly increasing). --
const MB_ADDR: usize = 0;
const MB_INIT_VAL: usize = 1;
const MB_FIN_VAL: usize = 2;
const MB_FIN_SERIAL: usize = 3;
const MB_IS_REAL: usize = 4;
const MB_ADDR_MULT: usize = 5;
const MB_AGAP: usize = 6;
const MB_AGAP_LIMB0: usize = 7;
const MB_ACHK: usize = MB_AGAP_LIMB0 + decomp_cols(MEM_GAP_BITS); // 17
const MB_ACHK_LIMB0: usize = MB_ACHK + 1; // 18
const MB_WIDTH: usize = MB_ACHK_LIMB0 + decomp_cols(MEM_GAP_BITS); // 28

// -- UNIVERSAL memory table layout (one row per access, log order): the ONE Blum multiset over
//    the `(domain, key)` address space with `Option`-valued cells. Identical Blum discipline to
//    the flat memory table, plus: the domain coordinate (nibble-bounded), the present bits
//    (boolean, `none ↦ value = 0` canonical), and the nullifier INSERT-ONLY tooth (a
//    nullifier-domain write installing `none` is UNSAT — `UniversalMemory.InsertOnlyAt`,
//    in-circuit). NO hashing rides this table at all: freshness of a nullifier is one read row
//    with `present = 0` (`nullifier_fresh_sound`), and the map roots are reconciled at the
//    boundary by map ops, never per access. --
const UM_DOMAIN: usize = 0;
const UM_KEY: usize = 1;
const UM_PRESENT: usize = 2;
const UM_VALUE: usize = 3;
const UM_PREV_PRESENT: usize = 4;
const UM_PREV_VALUE: usize = 5;
const UM_PREV_SERIAL: usize = 6;
const UM_KIND: usize = 7;
const UM_SERIAL: usize = 8;
const UM_IS_REAL: usize = 9;
const UM_GAP: usize = 10;
const UM_GAP_LIMB0: usize = 11;
const UM_IS_NULL: usize = UM_GAP_LIMB0 + decomp_cols(MEM_GAP_BITS); // 21
const UM_NULL_INV: usize = UM_IS_NULL + 1; // 22
const UM_WIDTH: usize = UM_NULL_INV + 1; // 23

// -- Universal boundary layout (one row per declared `(domain, key)` address, domain-major
//    lexicographically increasing). Nodup of the declared addresses — the hypothesis
//    `memcheck_sound` stands on — is enforced for FULL-FELT keys via the canonical BabyBear
//    decomposition `key = hi4·2^27 + lo27` (unique by the `is15·lo27 = 0` tooth, since
//    `p − 1 = 15·2^27`) and a lexicographic strict-increase over `(domain, hi4, lo27)`.
//    The flat memory boundary's 30-bit address pin cannot carry hash-image keys; this can. --
const UB_DOMAIN: usize = 0;
const UB_KEY: usize = 1;
const UB_INIT_PRESENT: usize = 2;
const UB_INIT_VALUE: usize = 3;
const UB_FIN_PRESENT: usize = 4;
const UB_FIN_VALUE: usize = 5;
const UB_FIN_SERIAL: usize = 6;
const UB_IS_REAL: usize = 7;
const UB_ADDR_MULT: usize = 8;
const UB_KEY_HI4: usize = 9;
const UB_KEY_LIMB0: usize = 10;
const UB_KEY_IS15: usize = UB_KEY_LIMB0 + decomp_cols(KEY_LO_BITS); // 20
const UB_KEY_INV15: usize = UB_KEY_IS15 + 1; // 21
const UB_DGAP: usize = UB_KEY_INV15 + 1; // 22
const UB_SAME_DOM: usize = UB_DGAP + 1; // 23
const UB_SAMEDOM_INV: usize = UB_SAME_DOM + 1; // 24
const UB_KCMP_S: usize = UB_SAMEDOM_INV + 1; // 25
const UB_KCMP_DHI: usize = UB_KCMP_S + 1; // 26
const UB_KCMP_DLO: usize = UB_KCMP_DHI + 1; // 27
const UB_KCMP_DLO_LIMB0: usize = UB_KCMP_DLO + 1; // 28
const UB_WIDTH: usize = UB_KCMP_DLO_LIMB0 + decomp_cols(KEY_LO_BITS); // 38

// -- COHORT universal boundary layout (the single-row specialization). The general boundary
//    (above) spends columns 9..38 — the canonical key decomposition (`UB_KEY_HI4..`) plus the
//    domain-major lexicographic strict-increase comparator (`UB_DGAP`/`UB_SAME_DOM*`/`UB_KCMP_*`)
//    — SOLELY to establish that the declared `(domain, key)` address list is `Nodup`, the
//    hypothesis `memcheck_sound` stands on. For the single-domain cohort / welded leg the boundary
//    has AT MOST ONE real row, so `Nodup` is `List.nodup_singleton` (Lean
//    `UniversalMemory.universal_memory_sound_single` / `MemoryChecking.memcheck_sound_single`,
//    `#assert_axioms`-clean): the entire comparator + key decomposition is VACUOUS and dropped.
//    The single-row discipline is enforced IN-CIRCUIT by `(next.is_real = 0)` on every transition
//    (`UB` row 0 may be real; rows 1.. are forced pads) — a multi-row witness is REFUSED, never
//    silently accepted, so the specialization can never be used unsoundly. Width 9 vs 38: the heavy
//    instance the IVC fold re-pays up the aggregation tree is cut to a quarter of its FRI columns. --
const UBC_DOMAIN: usize = 0;
const UBC_KEY: usize = 1;
const UBC_INIT_PRESENT: usize = 2;
const UBC_INIT_VALUE: usize = 3;
const UBC_FIN_PRESENT: usize = 4;
const UBC_FIN_VALUE: usize = 5;
const UBC_FIN_SERIAL: usize = 6;
const UBC_IS_REAL: usize = 7;
const UBC_ADDR_MULT: usize = 8;
const UBC_WIDTH: usize = UBC_ADDR_MULT + 1; // 9

// -- Map-ABSENT table layout (one row per non-membership reconciliation): the realization of
//    `map_op` kind `absent` (Lean `opensTo … none`, constructible by `opensTo_none_of_gap`) —
//    the sorted-gap bracketing, IN-CIRCUIT: two membership paths at ADJACENT leaf positions
//    (position = Σ dirᵢ·2ⁱ; adjacency is one linear constraint) under the SAME root, with
//    `lo_addr < key < hi_addr` enforced by the canonical-decomposition lexicographic
//    comparators. The sentinel bracketing (MIN/MAX, `heap_root.rs`) guarantees every
//    non-reserved absent key has a real adjacent pair. This is THE boundary leg of
//    `nullifier_fresh_binds_root`: the gap machinery survives exactly here — once per touched
//    address per proof, never per access. Committed ONLY when a descriptor declares an
//    `absent` op (presence-elided like every other table). --
const MA_ROOT: usize = 0;
const MA_KEY: usize = 1;
const MA_NEW_ROOT: usize = 2;
const MA_IS_REAL: usize = 3;
const MA_LO_ADDR: usize = 4;
const MA_LO_VALUE: usize = 5;
const MA_HI_ADDR: usize = 6;
const MA_HI_VALUE: usize = 7;
const MA_LO_LEAF: usize = 8;
const MA_HI_LEAF: usize = 9;
const MA_LO_SIB0: usize = 10;
const MA_LO_DIR0: usize = MA_LO_SIB0 + HEAP_TREE_DEPTH; // 26
const MA_LO_CHAIN0: usize = MA_LO_DIR0 + HEAP_TREE_DEPTH; // 42
const MA_HI_SIB0: usize = MA_LO_CHAIN0 + (HEAP_TREE_DEPTH - 1); // 57
const MA_HI_DIR0: usize = MA_HI_SIB0 + HEAP_TREE_DEPTH; // 73
const MA_HI_CHAIN0: usize = MA_HI_DIR0 + HEAP_TREE_DEPTH; // 89
// Canonical decompositions (hi4 · 2^27 + lo27, unique) of lo_addr / key / hi_addr:
// each block = [hi4, lo27 limbs (10), is15, inv15] = 13 columns.
const MA_DECOMP_COLS: usize = 1 + decomp_cols(KEY_LO_BITS) + 2; // 13
const MA_A_DEC0: usize = MA_HI_CHAIN0 + (HEAP_TREE_DEPTH - 1); // 104 (lo_addr)
const MA_K_DEC0: usize = MA_A_DEC0 + MA_DECOMP_COLS; // 117 (key)
const MA_B_DEC0: usize = MA_K_DEC0 + MA_DECOMP_COLS; // 130 (hi_addr)
// Lexicographic strict-lt comparator blocks: [s, dhi, dlo, dlo limbs (10)] = 13 columns.
const MA_CMP_COLS: usize = 3 + decomp_cols(KEY_LO_BITS); // 13
const MA_CMP_LO0: usize = MA_B_DEC0 + MA_DECOMP_COLS; // 143 (lo_addr < key)
const MA_CMP_HI0: usize = MA_CMP_LO0 + MA_CMP_COLS; // 156 (key < hi_addr)
// Phase B-GATE: the two leaf absorbs now ride the 17-wide chip bus, so each carries 7
// extra output lanes (out1..out7) appended at the tail (the digest itself stays at
// MA_LO_LEAF/MA_HI_LEAF = lane0). Appending avoids re-deriving the decomposition offsets.
const MA_LO_LEAF1: usize = MA_CMP_HI0 + MA_CMP_COLS; // 169 (lanes 1..7 of the lo leaf)
const MA_HI_LEAF1: usize = MA_LO_LEAF1 + (CHIP_OUT_LANES - 1); // 176 (lanes 1..7 of the hi leaf)
const MA_WIDTH: usize = MA_HI_LEAF1 + (CHIP_OUT_LANES - 1); // 183

// -- Map-ops table layout (one row per reconciliation, log order). Every permutation of
//    the opening rides the chip bus: the row carries the two leaf digests and the two
//    sibling-sharing chains' intermediate digests (the final links ARE root / new_root),
//    NEVER an in-row aux block (the EPOCH's row-width cure, applied to its own boundary
//    table — previously 39 + 34·352 = 12,007 cols, the measured §2b disease). --
const MAP_ROOT: usize = 0;
const MAP_KEY: usize = 1;
const MAP_VALUE: usize = 2;
const MAP_OP: usize = 3;
const MAP_NEW_ROOT: usize = 4;
const MAP_IS_REAL: usize = 5;
const MAP_OLD_VALUE: usize = 6;
const MAP_SIB0: usize = 7;
const MAP_DIR0: usize = MAP_SIB0 + HEAP_TREE_DEPTH; // 23
const MAP_OLD_LEAF: usize = MAP_DIR0 + HEAP_TREE_DEPTH; // 39
const MAP_NEW_LEAF: usize = MAP_OLD_LEAF + 1; // 40
const MAP_OLD_CHAIN0: usize = MAP_NEW_LEAF + 1; // 41 (levels 0..14; level 15 = MAP_ROOT)
const MAP_NEW_CHAIN0: usize = MAP_OLD_CHAIN0 + (HEAP_TREE_DEPTH - 1); // 56
// Phase B-GATE: the old/new leaf absorbs ride the 17-wide chip bus. Lane0 stays at
// MAP_OLD_LEAF/MAP_NEW_LEAF (the chained digest); lanes 1..7 are appended at the tail.
const MAP_OLD_LEAF1: usize = MAP_NEW_CHAIN0 + (HEAP_TREE_DEPTH - 1); // 71 (lanes 1..7 old leaf)
const MAP_NEW_LEAF1: usize = MAP_OLD_LEAF1 + (CHIP_OUT_LANES - 1); // 78 (lanes 1..7 new leaf)
const MAP_WIDTH: usize = MAP_NEW_LEAF1 + (CHIP_OUT_LANES - 1); // 85

/// The DECLARED leaf-input column list for a `MapOp` absorb, parametric in the value
/// column (`MAP_VALUE` for the new leaf, `MAP_OLD_VALUE` for the committed old leaf).
///
/// LAW#1: the leaf-absorb arity is DATA, not a hardcoded `2`. Both the AIR (`chip_absorb_tuple`)
/// and the trace assembly (`absorb_tuple` in `assemble`) read the SAME list, so prover and
/// verifier agree on the leaf shape by construction. Today the `MapOp` leaf is the 2-field sorted-
/// `Heap` leaf `hash[key, value]` (Lean `Substrate.Heap.leafOf hash e = hash[e.1, e.2]`, the
/// denotation `MapOp.holdsAt` opens against); the function is the single seam a wider declared map
/// leaf would extend (the absorb code paths are already arity-generic). The 7-field cap leaf is a
/// SEPARATE object (a binary-Merkle opening via generic chip `Lookup`s — Lean `DeployedCapOpen`),
/// not a `MapOp` leaf; see the module-level note and the returned ledger.
#[inline]
fn map_leaf_input_cols(value_col: usize) -> [usize; 2] {
    [MAP_KEY, value_col]
}

// -- Chip table layout. A row is EITHER a sponge-absorb permutation (`is_fact = 0`:
//    state = (in0..in3, arity tag) — the hash_many shape every hash-site lookup queries)
//    OR a Merkle-node permutation (`is_fact = 1`, arity pinned 0: state = fact_state
//    (in0, in1) — `poseidon2::hash_fact`'s marker shape, provided on the `ir2_fact` bus
//    for the map-ops chains). One aux block per UNIQUE permutation, either way.
//
//    PROVENANCE (#175): the permutation constraints are `poseidon2_permute_expr`
//    (`plonky3_prover.rs`) — the in-repo round-by-round arithmetization (every round's
//    full 16-lane output committed and equality-constrained; no shortcut columns), the
//    SAME gadget the v1 hash sites and `effect_vm_p3_full_air.rs` discharge
//    `Poseidon2SpongeCR` with. Its round constants / internal diagonal are the audited
//    p3-baby-bear `BABYBEAR_POSEIDON2_RC_16` / `..INTERNAL_DIAG_16` tables (descriptor
//    `params` pin those source names; `parse_chip_params` refuses a mismatch), and the
//    permutation FUNCTION is conformance-KAT'd against the pinned-rev plonky3
//    `default_babybear_poseidon2_16()` (`poseidon2::tests::poseidon2_plonky3_cross_check_kat`).
//    The audited `p3-poseidon2-circuit-air` is used where its layout is forced on us —
//    the recursion verifier circuit (`plonky3_recursion_impl.rs`). NOTE: the descriptor
//    param `sbox_registers: 1` describes the p3-air REGISTERED layout, which this chip
//    deliberately does NOT use (measured net-negative, see `max_constraint_degree` +
//    docs/PROOF-ECONOMICS.md §2c); the parameter is a frozen descriptor pin (no regen
//    off-cycle), and the permutation function is unaffected by arithmetization shape.
//
//    AMORTIZATION (#175): ONE chip table per batch proof serves ALL hash facts — the
//    main table's hash-site lookups and the map-ops leaf absorbs ride `BUS_P2`, the
//    map-ops Merkle-chain facts ride `BUS_FACT`, both LogUp-served by this single
//    table. Cross-EFFECT amortization (one chip table for a whole turn) needs the
//    IR-v2 turn assembly, which does not exist yet (this path is per-effect,
//    recursion-gated, pre-cutover); it lands with the recursion aggregation. --
const CHIP_ARITY: usize = 0;
const CHIP_IN0: usize = 1;
const CHIP_OUT: usize = CHIP_IN0 + CHIP_RATE; // 9 (= out0, the squeezed digest lane)
/// The number of permutation-output lanes the chip exposes on the bus. Widened
/// 1 → 8 (Phase B-GATE): the chip's bus tuple now carries `state[0..8]` of the
/// SAME already-fully-constrained final permutation. Single-output sites bind
/// only `out0` (`CHIP_OUT`) — lanes 1..8 are made AVAILABLE for the 8-felt
/// commitment sponge (Phase B-ROTATION) but the deployed commitment is STILL
/// 1-felt after this phase.
pub const CHIP_OUT_LANES: usize = 8;
const CHIP_MULT: usize = CHIP_OUT + CHIP_OUT_LANES; // 17
const CHIP_IS_FACT: usize = CHIP_MULT + 1; // 18
/// `big = [arity == 7]`: selects the rate-8 absorb seeding (inputs in lanes 0..6,
/// length tag absent from lanes 4..6) from the rate-4 seeding (tag at lane 4).
const CHIP_BIG: usize = CHIP_IS_FACT + 1; // 12
/// Dedicated seed-source columns for the three AMBIGUOUS state lanes 4/5/6 (input
/// vs tag/fact). Each is read DIRECTLY into the permuted state (degree 1), while
/// its VALUE is pinned by a degree-≤3 SIDE constraint (never through the x⁷ S-box) —
/// the only degree-safe way to serve two seedings from one fixed state array.
const CHIP_S4: usize = CHIP_BIG + 1; // 13
const CHIP_S5: usize = CHIP_S4 + 1; // 14
const CHIP_S6: usize = CHIP_S5 + 1; // 15
/// `wide = [arity == 11]` (Phase B-GATE-INPUT): high EXACTLY on the wide single-permutation
/// absorb (8-felt carrier ‖ 3 limbs). Lifts the narrow `in7..in10 = 0` pins (the wide row
/// genuinely seeds state lanes 7..10) and, with `big`, drives lanes 4/5/6 from the inputs.
const CHIP_WIDE: usize = CHIP_S6 + 1;
/// `node8 = [arity == 16]` (Phase H3): high EXACTLY on the full-width `node8` compression row
/// (`L8 ‖ R8` → 8-felt digest). Like `wide` it drives lanes 4..6 from the inputs (`seed456`) and
/// lifts the narrow `in7..` zero-pins; additionally it lifts the `in11..in15 = 0` pins so the
/// second 8-felt child genuinely seeds lanes 11..15.
const CHIP_NODE8: usize = CHIP_WIDE + 1;
const CHIP_AUX0: usize = CHIP_NODE8 + 1;
const CHIP_WIDTH: usize = CHIP_AUX0 + POSEIDON2_PERM_AUX_COLS;

/// The five-table interpreter AIR. One Rust type covering every instance of the batch
/// (the batch prover is monomorphic in the AIR type), entirely descriptor-driven.
#[derive(Clone)]
pub enum Ir2Air {
    /// The main instance: the descriptor's own constraints + bus interactions.
    Main {
        /// The interpreted descriptor.
        desc: EffectVmDescriptor2,
        /// Resolved aux layout.
        layout: MainLayoutPub,
    },
    /// The Poseidon2 chip table (every row a REAL permutation; `ChipTableSound`).
    Chip,
    /// The `[0,256)` byte table (value column pinned to the row index).
    ByteTable,
    /// The memory access table (Blum discipline + the read/write multiset legs).
    Memory,
    /// The memory boundary (init/final image over the declared, strictly increasing
    /// address list).
    MemBoundary,
    /// The map-ops table (in-row sorted-Poseidon2 openings).
    MapOps,
    /// The map-ABSENT table (bracketed sorted-gap non-membership openings).
    MapAbsent,
    /// The UNIVERSAL memory table (the one Blum multiset over `Domain × κ`).
    UMemory,
    /// The universal boundary (init/final `Option` images over the declared,
    /// domain-major lexicographically increasing `(domain, key)` list).
    UMemBoundary,
    /// The COHORT single-row specialization of [`Ir2Air::UMemBoundary`] (width 9): at most one
    /// real declared address, so the inter-row lexicographic comparator + key decomposition are
    /// dropped (`Nodup` is `nodup_singleton`, Lean `universal_memory_sound_single`). Refuses a
    /// multi-row witness in-circuit via `(next.is_real = 0)` on every transition.
    UMemBoundaryCohort,
}

/// Public re-export wrapper of the resolved main layout (kept opaque; constructed by
/// `check_descriptor2` via the prove/verify entry points).
#[derive(Clone, Debug)]
pub struct MainLayoutPub(MainLayout);

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for Ir2Air {
    fn width(&self) -> usize {
        match self {
            Ir2Air::Main { layout, .. } => layout.0.width,
            Ir2Air::Chip => CHIP_WIDTH,
            Ir2Air::ByteTable => 2,
            Ir2Air::Memory => MEM_WIDTH,
            Ir2Air::MemBoundary => MB_WIDTH,
            Ir2Air::MapOps => MAP_WIDTH,
            Ir2Air::MapAbsent => MA_WIDTH,
            Ir2Air::UMemory => UM_WIDTH,
            Ir2Air::UMemBoundary => UB_WIDTH,
            Ir2Air::UMemBoundaryCohort => UBC_WIDTH,
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Ir2Air::Main { desc, .. } => desc.public_input_count,
            _ => 0,
        }
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        match self {
            // The inline Poseidon2 S-box (x⁷ between committed round-state blocks).
            // A 1-register (committed-cube, degree-3) variant was built and MEASURED
            // worse at every security-parity FRI point: +141 aux columns ⇒ +25.8 KiB
            // on transfer at (lb=3, q=38), and the low blowup it would enable loses
            // to high-blowup/few-queries anyway (docs/PROOF-ECONOMICS.md §2c).
            // Guarded by `ir2_degree_budget`.
            Ir2Air::Chip => Some(7),
            // Let the symbolic analysis infer the rest (map-ops is lookup-spine only now;
            // descriptor gates vary on main).
            _ => None,
        }
    }
}

/// Emit one byte-limb decomposition: `value_expr = Σ limbᵢ·256ⁱ`, full limbs queried on the
/// byte bus, a partial top limb bit-bound tightly. The realization of "∈ [0, 2^bits)".
fn eval_decomp<AB>(builder: &mut AB, value_expr: AB::Expr, limbs: &[AB::Var], bits: usize)
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: PrimeField32,
{
    let bus = LookupBus::new(BUS_BYTE);
    let (n, top_bits) = limb_geom(bits);
    let partial = top_bits < LIMB_BITS;
    let limb_base = AB::Expr::from_u64(1 << LIMB_BITS);
    let mut recomposed = AB::Expr::ZERO;
    let mut weight = AB::Expr::ONE;
    for i in 0..n {
        let limb: AB::Expr = limbs[i].into();
        recomposed += limb.clone() * weight.clone();
        weight = weight.clone() * limb_base.clone();
        if i == n - 1 && partial {
            // Tight top-limb bound: bit-decompose into `top_bits` booleans.
            let mut top_recomp = AB::Expr::ZERO;
            let mut bw = AB::Expr::ONE;
            for b in 0..top_bits {
                let bit: AB::Expr = limbs[n + b].into();
                builder.assert_zero(bit.clone() * (bit.clone() - AB::Expr::ONE));
                top_recomp += bit * bw.clone();
                bw = bw.clone() + bw;
            }
            builder.assert_zero(top_recomp - limb);
        } else {
            bus.lookup_key(builder, [limb], AB::Expr::ONE);
        }
    }
    builder.assert_zero(recomposed - value_expr);
}

/// Emit one CANONICAL BabyBear decomposition `value = hi4 · 2^27 + lo27` over a 13-column
/// block `[hi4, lo27 limbs (10), is15, inv15]`. Uniqueness (and hence integer-faithfulness of
/// the lexicographic comparators) is the `is15 · lo27 = 0` tooth: `p − 1 = 15 · 2^27`, so the
/// only admissible composite with `hi4 = 15` is `p − 1` itself — the non-canonical alias
/// `value + p` of any small value is UNSAT. `gate` activates the is15-forcing leg (pad rows
/// stay all-zero). Returns `(hi4, lo27)` as expressions for the comparators.
fn eval_canon_decomp<AB>(
    builder: &mut AB,
    value_expr: AB::Expr,
    block: &[AB::Var],
    gate: AB::Expr,
) -> (AB::Expr, AB::Expr)
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: PrimeField32,
{
    let hi4: AB::Expr = block[0].into();
    let limbs: Vec<AB::Var> = block[1..1 + decomp_cols(KEY_LO_BITS)].to_vec();
    let is15: AB::Expr = block[1 + decomp_cols(KEY_LO_BITS)].into();
    let inv15: AB::Expr = block[2 + decomp_cols(KEY_LO_BITS)].into();
    let fifteen = AB::Expr::from_u64(KEY_HI_MAX);
    // hi4 is a nibble (the shared limb table is exactly [0, 16)).
    let bus = LookupBus::new(BUS_BYTE);
    bus.lookup_key(builder, [hi4.clone()], AB::Expr::ONE);
    // lo27 = value − hi4·2^27, decomposed to 27 bits.
    let lo27 = value_expr - hi4.clone() * AB::Expr::from_u64(KEY_HI_BASE);
    eval_decomp(builder, lo27.clone(), &limbs, KEY_LO_BITS);
    // is15 forced: boolean; (hi4 − 15)·is15 = 0; (hi4 − 15)·inv15 = gate − is15.
    builder.assert_zero(is15.clone() * (is15.clone() - AB::Expr::ONE));
    builder.assert_zero((hi4.clone() - fifteen.clone()) * is15.clone());
    builder.assert_zero((hi4.clone() - fifteen) * inv15 - (gate - is15.clone()));
    // THE UNIQUENESS TOOTH: hi4 = 15 admits only lo27 = 0 (the value p − 1).
    builder.assert_zero(is15 * lo27.clone());
    (hi4, lo27)
}

/// Emit one lexicographic STRICT-LT comparator `a < b` over canonical `(hi4, lo27)`
/// decompositions, on a 13-column block `[s, dhi, dlo, dlo limbs (10)]`, gated by `gate`
/// (degree ≤ 1). When the gate fires: `s = 1` ⇒ `b.hi4 ≥ a.hi4 + 1` (dhi a nibble);
/// `s = 0` ⇒ `b.hi4 = a.hi4` and `b.lo27 ≥ a.lo27 + 1` (dlo 27-bit). Since the
/// decompositions are unique-canonical, this is integer `<` on the felts — full-felt keys
/// (hash images) compare soundly, which the 30-bit flat-address regime could never do.
#[allow(clippy::too_many_arguments)]
fn eval_lex_lt<AB>(
    builder: &mut AB,
    a_hi4: AB::Expr,
    a_lo27: AB::Expr,
    b_hi4: AB::Expr,
    b_lo27: AB::Expr,
    block: &[AB::Var],
    gate: AB::Expr,
    transition_only: bool,
) where
    AB: AirBuilder + InteractionBuilder,
    AB::F: PrimeField32,
{
    let s: AB::Expr = block[0].into();
    let dhi: AB::Var = block[1];
    let dlo: AB::Var = block[2];
    let dlo_limbs: Vec<AB::Var> = block[3..3 + decomp_cols(KEY_LO_BITS)].to_vec();
    builder.assert_zero(s.clone() * (s.clone() - AB::Expr::ONE));
    // dhi/dlo are committed columns, range-bound unconditionally (pads carry 0); their
    // VALUES are pinned by the gated branch equations.
    let bus = LookupBus::new(BUS_BYTE);
    bus.lookup_key(builder, [dhi.into()], AB::Expr::ONE);
    eval_decomp(builder, dlo.into(), &dlo_limbs, KEY_LO_BITS);
    let one = AB::Expr::ONE;
    let c_dhi =
        dhi.into() - gate.clone() * s.clone() * (b_hi4.clone() - a_hi4.clone() - one.clone());
    let c_eq = gate.clone() * (one.clone() - s.clone()) * (b_hi4 - a_hi4);
    let c_dlo = dlo.into() - gate * (one.clone() - s) * (b_lo27 - a_lo27 - one);
    if transition_only {
        let mut tb = builder.when_transition();
        tb.assert_zero(c_dhi);
        tb.assert_zero(c_eq);
        tb.assert_zero(c_dlo);
    } else {
        builder.assert_zero(c_dhi);
        builder.assert_zero(c_eq);
        builder.assert_zero(c_dlo);
    }
}

impl<AB> Air<AB> for Ir2Air
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let (local, next): (Vec<AB::Var>, Vec<AB::Var>) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        match self {
            // ----------------------------------------------------------------
            Ir2Air::Main { desc, layout } => {
                let pv: Vec<AB::Expr> = builder.public_values().iter().map(|&v| v.into()).collect();

                // -- The embedded v1 forms, on the v1 domains. --
                {
                    let mut fb = builder.when_first_row();
                    for k in &desc.constraints {
                        if let VmConstraint2::Base(c) = k {
                            match c {
                                VmConstraint::PiBinding {
                                    row: VmRow::First,
                                    col,
                                    pi_index,
                                } => fb.assert_zero(local[*col].into() - pv[*pi_index].clone()),
                                VmConstraint::Boundary {
                                    row: VmRow::First,
                                    body,
                                } => fb.assert_zero(body.eval_expr::<AB>(&local)),
                                _ => {}
                            }
                        }
                    }
                }
                {
                    let mut lb = builder.when_last_row();
                    for k in &desc.constraints {
                        if let VmConstraint2::Base(c) = k {
                            match c {
                                VmConstraint::PiBinding {
                                    row: VmRow::Last,
                                    col,
                                    pi_index,
                                } => lb.assert_zero(local[*col].into() - pv[*pi_index].clone()),
                                VmConstraint::Boundary {
                                    row: VmRow::Last,
                                    body,
                                } => lb.assert_zero(body.eval_expr::<AB>(&local)),
                                _ => {}
                            }
                        }
                    }
                }
                {
                    let mut tb = builder.when_transition();
                    for k in &desc.constraints {
                        match k {
                            VmConstraint2::Base(VmConstraint::Gate(body)) => {
                                tb.assert_zero(body.eval_expr::<AB>(&local))
                            }
                            VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
                                let n: AB::Expr = next[EFFECTVM_STATE_BEFORE_BASE + hi].into();
                                let l: AB::Expr = local[EFFECTVM_STATE_AFTER_BASE + lo].into();
                                tb.assert_zero(n - l);
                            }
                            // The two-row windowed gate (Lean `windowGate`): an `on_transition`
                            // body reads BOTH rows and fires only on the transition — exactly
                            // the Rust hand-AIR's `builder.when_transition().assert_zero(..)`
                            // cumulative-sum arm.
                            VmConstraint2::WindowGate(w) if w.on_transition => {
                                tb.assert_zero(w.body.eval_expr::<AB>(&local, &next))
                            }
                            _ => {}
                        }
                    }
                }
                // -- Every-row windowed gates (Lean `windowGate` with `on_transition = false`):
                //    the body vanishes on every row (the wrap row included). None of the shipped
                //    descriptors emit this form today; it is carried for grammar completeness. --
                for k in &desc.constraints {
                    if let VmConstraint2::WindowGate(w) = k
                        && !w.on_transition
                    {
                        builder.assert_zero(w.body.eval_expr::<AB>(&local, &next));
                    }
                }

                // -- Chip lookups: each declared tuple queried on the chip bus, every row. --
                let p2 = LookupBus::new(BUS_P2);
                for k in &desc.constraints {
                    if let VmConstraint2::Lookup(l) = k
                        && l.table == TID_P2
                    {
                        let tuple: Vec<AB::Expr> =
                            l.tuple.iter().map(|e| e.eval_expr::<AB>(&local)).collect();
                        p2.lookup_key(builder, tuple, AB::Expr::ONE);
                    }
                }

                // -- Range lookups: the byte-limb realization, every row. --
                for rb in &layout.0.ranges {
                    let cols = decomp_cols(rb.bits);
                    let limbs: Vec<AB::Var> = local[rb.limb0..rb.limb0 + cols].to_vec();
                    eval_decomp(builder, local[rb.wire].into(), &limbs, rb.bits);
                }

                // -- Submask lookups: the bitwise a&b=a relation at SUBMASK_BITS. --
                for sb in &layout.0.submasks {
                    let mut keep_recomp = AB::Expr::ZERO;
                    let mut held_recomp = AB::Expr::ZERO;
                    let mut w = AB::Expr::ONE;
                    for i in 0..SUBMASK_BITS {
                        let kb: AB::Expr = local[sb.keep0 + i].into();
                        let hb: AB::Expr = local[sb.held0 + i].into();
                        builder.assert_zero(kb.clone() * (kb.clone() - AB::Expr::ONE));
                        builder.assert_zero(hb.clone() * (hb.clone() - AB::Expr::ONE));
                        // Non-amplification, bitwise: keep ⇒ held.
                        builder.assert_zero(kb.clone() * (AB::Expr::ONE - hb.clone()));
                        keep_recomp += kb * w.clone();
                        held_recomp += hb * w.clone();
                        w = w.clone() + w;
                    }
                    builder.assert_zero(keep_recomp - sb.keep.eval_expr::<AB>(&local));
                    builder.assert_zero(held_recomp - sb.held.eval_expr::<AB>(&local));
                }

                // -- Mem ops: send the instrumented row on the memory log bus. --
                let mem_log = PermutationCheckBus::new(BUS_MEM_LOG);
                for k in &desc.constraints {
                    if let VmConstraint2::MemOp(m) = k {
                        let fields = [
                            m.addr.eval_expr::<AB>(&local),
                            m.value.eval_expr::<AB>(&local),
                            m.prev_value.eval_expr::<AB>(&local),
                            m.prev_serial.eval_expr::<AB>(&local),
                            AB::Expr::from_u64(m.kind.code() as u64),
                        ];
                        mem_log.send(builder, fields, m.guard.eval_expr::<AB>(&local));
                    }
                }

                // -- Map ops: send the reconciliation row on the map log bus (read/write rows
                //    are received by the map-ops table; `absent` rows by the map-absent
                //    table — the op code partitions the one multiset). --
                let map_log = PermutationCheckBus::new(BUS_MAP_LOG);
                for k in &desc.constraints {
                    if let VmConstraint2::MapOp(m) = k {
                        let fields = [
                            m.root.eval_expr::<AB>(&local),
                            m.key.eval_expr::<AB>(&local),
                            m.value.eval_expr::<AB>(&local),
                            AB::Expr::from_u64(m.op.code() as u64),
                            m.new_root.eval_expr::<AB>(&local),
                        ];
                        map_log.send(builder, fields, m.guard.eval_expr::<AB>(&local));
                    }
                }

                // -- Universal mem ops: send the instrumented row on the umem log bus. --
                let umem_log = PermutationCheckBus::new(BUS_UMEM_LOG);
                for k in &desc.constraints {
                    if let VmConstraint2::UMemOp(m) = k {
                        let fields = [
                            AB::Expr::from_u64(m.domain as u64),
                            m.key.eval_expr::<AB>(&local),
                            m.present.eval_expr::<AB>(&local),
                            m.value.eval_expr::<AB>(&local),
                            m.prev_present.eval_expr::<AB>(&local),
                            m.prev_value.eval_expr::<AB>(&local),
                            m.prev_serial.eval_expr::<AB>(&local),
                            AB::Expr::from_u64(m.kind.code() as u64),
                        ];
                        umem_log.send(builder, fields, m.guard.eval_expr::<AB>(&local));
                    }
                }
            }

            // ----------------------------------------------------------------
            Ir2Air::Chip => {
                let arity: AB::Expr = local[CHIP_ARITY].into();
                let is_fact: AB::Expr = local[CHIP_IS_FACT].into();
                let big: AB::Expr = local[CHIP_BIG].into();
                let wide: AB::Expr = local[CHIP_WIDE].into();
                let node8: AB::Expr = local[CHIP_NODE8].into();
                let two = AB::Expr::from_u64(2);
                let three = AB::Expr::from_u64(3);
                let four = AB::Expr::from_u64(4);
                let seven = AB::Expr::from_u64(7);
                let eleven = AB::Expr::from_u64(CHIP_WIDE_ARITY as u64);
                let sixteen = AB::Expr::from_u64(CHIP_NODE8_ARITY as u64);
                builder.assert_zero(is_fact.clone() * (is_fact.clone() - AB::Expr::ONE));
                // arity ∈ {0 (pad/fact), 2, 3 (cap node [FACT_MARK,l,r]), 4, 7 (cap leaf), 11
                // (Phase B-GATE-INPUT wide MD step: 8-felt carrier + 3 limbs), 16 (Phase H3 node8:
                // L8 ‖ R8 full-width Merkle compression)}. Degree 7 (= the S-box budget).
                builder.assert_zero(
                    arity.clone()
                        * (arity.clone() - two.clone())
                        * (arity.clone() - three.clone())
                        * (arity.clone() - four.clone())
                        * (arity.clone() - seven.clone())
                        * (arity.clone() - eleven.clone())
                        * (arity.clone() - sixteen.clone()),
                );
                // A fact row carries arity 0 (so the genuine fact state's zero tag is
                // expressible — no hybrid absorb/fact state is).
                builder.assert_zero(is_fact.clone() * arity.clone());
                // `big = [arity == 7]`: boolean, high EXACTLY on arity 7. Selects the rate-8 leaf
                // seeding (lanes 4..6 = genuine in4..in6) from the rate-4 seeding (lane 4 = arity
                // tag, 5/6 = fact marker/flag). `big` stays LOW on the wide arity 11 — there the
                // `wide` selector drives lanes 4..6 (and 7..10) from inputs instead.
                builder.assert_zero(big.clone() * (big.clone() - AB::Expr::ONE));
                builder.assert_zero(big.clone() * (arity.clone() - seven.clone()));
                // p7 ≠ 0 ⇔ arity ∈ {0,2,3,4,11,16} (= 0 exactly at arity 7); p7·(1−big) forces big
                // HIGH on the arity-7 branch. (`(a−11)`/`(a−16)` adjoined so p7 also vanishes the
                // wide + node8 rows — big is LOW there. Degree 7 — a SIDE constraint, not S-boxed.)
                let p7 = arity.clone()
                    * (arity.clone() - two.clone())
                    * (arity.clone() - three.clone())
                    * (arity.clone() - four.clone())
                    * (arity.clone() - eleven.clone())
                    * (arity.clone() - sixteen.clone());
                builder.assert_zero(p7 * (AB::Expr::ONE - big.clone()));
                // `wide = [arity == 11]`: boolean, high EXACTLY on the wide arity. Lifts the narrow
                // input-zeroing pins (in7..in10) and selects the input-seeded lanes 4..6.
                builder.assert_zero(wide.clone() * (wide.clone() - AB::Expr::ONE));
                builder.assert_zero(wide.clone() * (arity.clone() - eleven.clone()));
                // p11 ≠ 0 ⇔ arity ∈ {0,2,3,4,7,16} (= 0 exactly at arity 11); p11·(1−wide) forces
                // wide HIGH on the arity-11 branch. (Degree 7 — a SIDE constraint, not S-boxed.)
                let p11 = arity.clone()
                    * (arity.clone() - two.clone())
                    * (arity.clone() - three.clone())
                    * (arity.clone() - four.clone())
                    * (arity.clone() - seven.clone())
                    * (arity.clone() - sixteen.clone());
                builder.assert_zero(p11 * (AB::Expr::ONE - wide.clone()));
                // `node8 = [arity == 16]` (Phase H3): boolean, high EXACTLY on the full-width L8‖R8
                // compression row. Lifts the narrow input-zeroing pins (in7..in15) and selects the
                // input-seeded lanes 4..6.
                builder.assert_zero(node8.clone() * (node8.clone() - AB::Expr::ONE));
                builder.assert_zero(node8.clone() * (arity.clone() - sixteen.clone()));
                // p16 ≠ 0 ⇔ arity ∈ {0,2,3,4,7,11} (= 0 exactly at arity 16); p16·(1−node8) forces
                // node8 HIGH on the arity-16 branch. (Degree 7 — a SIDE constraint, not S-boxed.)
                let p16 = arity.clone()
                    * (arity.clone() - two.clone())
                    * (arity.clone() - three.clone())
                    * (arity.clone() - four.clone())
                    * (arity.clone() - seven.clone())
                    * (arity.clone() - eleven.clone());
                builder.assert_zero(p16 * (AB::Expr::ONE - node8.clone()));
                // `seed456 = big + wide + node8` (∈ {0,1}: at most one flag is high — the membership
                // gate forces distinct arity values 7/11/16). When high, lanes 4/5/6 carry genuine
                // in4/in5/in6 (rate-8 leaf, wide step, OR node8); when low, lane 4 = arity tag.
                let seed456 = big.clone() + wide.clone() + node8.clone();
                // Inputs beyond the arity are ZERO (the padTo discipline — a junk-padded row is
                // not a genuine chipRow). The input lanes a row genuinely uses are exactly
                // `i < arity`; the gates below vanish each lane on the arity classes that do
                // NOT reach it. (None routed through the S-box.)
                //
                // in0/in1: used by every absorb arity {2,3,4,7,11,16} AND fact rows; pinned only on
                // the bare pad row (arity 0, non-fact). q01 = (a−2)(a−3)(a−4)(a−7)(a−11)(a−16) is 0
                // on arity∈{2,3,4,7,11,16} and +29568 on the pad/fact row (arity 0, SIX negative
                // factors ⇒ positive). Subtracting 29568·is_fact cancels it on fact rows.
                let q01 = (arity.clone() - two.clone())
                    * (arity.clone() - three.clone())
                    * (arity.clone() - four.clone())
                    * (arity.clone() - seven.clone())
                    * (arity.clone() - eleven.clone())
                    * (arity.clone() - sixteen.clone());
                // q01 on the pad row (arity 0): (−2)(−3)(−4)(−7)(−11)(−16) = +29568.
                let q01_pad = AB::Expr::from_u64(1848 * CHIP_NODE8_ARITY as u64);
                for i in 0..2 {
                    let inp: AB::Expr = local[CHIP_IN0 + i].into();
                    builder.assert_zero(inp * (q01.clone() - q01_pad.clone() * is_fact.clone()));
                }
                // in2: genuine for arity ∈ {3,4,7,11,16}; pinned on {0,2} and fact.
                builder.assert_zero(
                    local[CHIP_IN0 + 2].into()
                        * (arity.clone() - three.clone())
                        * (arity.clone() - four.clone())
                        * (arity.clone() - seven.clone())
                        * (arity.clone() - eleven.clone())
                        * (arity.clone() - sixteen.clone()),
                );
                // in3: genuine only for arity ∈ {4,7,11,16}; pinned on {0,2,3} and fact.
                builder.assert_zero(
                    local[CHIP_IN0 + 3].into()
                        * (arity.clone() - four.clone())
                        * (arity.clone() - seven.clone())
                        * (arity.clone() - eleven.clone())
                        * (arity.clone() - sixteen.clone()),
                );
                // in4/in5/in6: genuine for arity ∈ {7 (rate-8 leaf), 11 (wide), 16 (node8)}; pinned
                // else.
                for i in 4..7 {
                    builder.assert_zero(
                        local[CHIP_IN0 + i].into()
                            * (arity.clone() - seven.clone())
                            * (arity.clone() - eleven.clone())
                            * (arity.clone() - sixteen.clone()),
                    );
                }
                // in7..in10: genuine for the wide arity 11 AND node8 arity 16 (the second 8-felt
                // child's first 4 lanes ride here); pinned on every narrow arity ≤ 7.
                for i in 7..CHIP_WIDE_ARITY {
                    builder.assert_zero(
                        local[CHIP_IN0 + i].into()
                            * (arity.clone() - eleven.clone())
                            * (arity.clone() - sixteen.clone()),
                    );
                }
                // in11..in15: genuine ONLY for node8 arity 16 (the tail of the second 8-felt child);
                // pinned on EVERY other arity (incl. the wide arity 11, which uses lanes 0..10).
                for i in CHIP_WIDE_ARITY..CHIP_NODE8_ARITY {
                    builder.assert_zero(
                        local[CHIP_IN0 + i].into() * (arity.clone() - sixteen.clone()),
                    );
                }
                // The three AMBIGUOUS seed-source columns S4/S5/S6, pinned by SIDE constraints
                // (off the S-box path). When `seed456 = 0` (rate-4 / fact): S4 = arity tag,
                // S5 = is_fact·FACT_MARK, S6 = is_fact — byte-identical to the deployed seeding.
                // When `seed456 = 1` (arity 7 leaf OR arity 11 wide): S4/S5/S6 = genuine in4/in5/in6.
                builder.assert_zero(
                    local[CHIP_S4].into()
                        - (seed456.clone() * local[CHIP_IN0 + 4].into()
                            + (AB::Expr::ONE - seed456.clone()) * arity.clone()),
                );
                builder.assert_zero(
                    local[CHIP_S5].into()
                        - (seed456.clone() * local[CHIP_IN0 + 5].into()
                            + (AB::Expr::ONE - seed456.clone())
                                * is_fact.clone()
                                * AB::Expr::from_u64(FACT_MARK as u64)),
                );
                builder.assert_zero(
                    local[CHIP_S6].into()
                        - (seed456.clone() * local[CHIP_IN0 + 6].into()
                            + (AB::Expr::ONE - seed456.clone()) * is_fact.clone()),
                );
                // The REAL permutation, output pinned. Every seeded lane reads ONE column
                // (degree 1) so the first x⁷ S-box stays at the degree-7 budget. Rate-4 rows
                // (is_fact = 0): state = (in0..in3, arity tag) — `hash_many`'s shape. Rate-8 leaf
                // (arity 7): state = (in0..in6, 0…). Fact rows (is_fact = 1, arity 0): state =
                // (l, r, 0, 0, 0, FACT_MARK, 1, 0…) — `hash_fact`'s marker shape via S5/S6. Wide
                // (arity 11): state = (in0..in10, 0…) — the 8-felt carrier ‖ 3 limbs, lanes 7..10
                // read directly (pinned 0 on every narrow arity, so reading them is safe there).
                let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| AB::Expr::ZERO);
                for i in 0..4 {
                    st[i] = local[CHIP_IN0 + i].into();
                }
                st[4] = local[CHIP_S4].into();
                st[5] = local[CHIP_S5].into();
                st[6] = local[CHIP_S6].into();
                // Lanes 7..15: the wide carrier/limb tail (7..10) AND the node8 second-child tail
                // (11..15). On every arity that does not reach a lane it is pinned 0 above, so
                // seeding them directly preserves the narrow/wide state shapes. arity 16 seeds all
                // 16 lanes = WIDTH (full-width compression, no capacity).
                for i in 7..CHIP_NODE8_ARITY {
                    st[i] = local[CHIP_IN0 + i].into();
                }
                let aux: Vec<AB::Var> =
                    local[CHIP_AUX0..CHIP_AUX0 + POSEIDON2_PERM_AUX_COLS].to_vec();
                // Expose the first 8 lanes `state[0..8]` of the SAME already-fully-constrained
                // final permutation. Lane 0 is the squeezed digest the single-output sites bind;
                // lanes 1..8 are the genuine distinct lanes the 8-felt commitment sponge will use
                // (Phase B-GATE makes them AVAILABLE; the deployed commitment is still 1-felt).
                let lanes = poseidon2_permute_expr_lanes::<AB>(builder, st, &aux);
                // out0 == lane0 (the existing digest binding — UNCHANGED meaning).
                builder.assert_zero(local[CHIP_OUT].into() - lanes[0].clone());
                // out1..out7 == lanes 1..8: the 7 NEW constraints. These EQUALITY-bind the
                // genuine distinct permutation lanes (out[i] is NOT a free column and NOT a copy
                // of out[0]) — a witness with a forged out[i] is UNSAT (the anti-laundering crux).
                for i in 1..CHIP_OUT_LANES {
                    builder.assert_zero(local[CHIP_OUT + i].into() - lanes[i].clone());
                }

                // Provide the (arity, ins, out0..out7) tuple on the absorb bus, consumed `mult`
                // times — fact rows provide ZERO here (no fact digest can serve a
                // hash-site lookup) and vice versa.
                let bus = LookupBus::new(BUS_P2);
                let mut tuple: Vec<AB::Expr> = Vec::with_capacity(CHIP_TUPLE_LEN);
                tuple.push(local[CHIP_ARITY].into());
                for i in 0..CHIP_RATE {
                    tuple.push(local[CHIP_IN0 + i].into());
                }
                for i in 0..CHIP_OUT_LANES {
                    tuple.push(local[CHIP_OUT + i].into());
                }
                bus.table_entry(
                    builder,
                    tuple,
                    local[CHIP_MULT].into() * (AB::Expr::ONE - is_fact.clone()),
                );
                // Provide (l, r, out) on the fact bus for fact rows only.
                let fact_bus = LookupBus::new(BUS_FACT);
                fact_bus.table_entry(
                    builder,
                    [
                        local[CHIP_IN0].into(),
                        local[CHIP_IN0 + 1].into(),
                        local[CHIP_OUT].into(),
                    ],
                    local[CHIP_MULT].into() * is_fact,
                );
            }

            // ----------------------------------------------------------------
            Ir2Air::ByteTable => {
                // value = row index (first row 0, increment 1): the table cannot lie.
                builder.when_first_row().assert_zero(local[0].into());
                builder
                    .when_transition()
                    .assert_zero(next[0].into() - local[0].into() - AB::Expr::ONE);
                let bus = LookupBus::new(BUS_BYTE);
                bus.table_entry(builder, [local[0].into()], local[1].into());
            }

            // ----------------------------------------------------------------
            Ir2Air::Memory => {
                let is_real: AB::Expr = local[MEM_IS_REAL].into();
                let kind: AB::Expr = local[MEM_KIND].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                builder.assert_zero(kind.clone() * (kind.clone() - AB::Expr::ONE));
                // Real rows form a prefix.
                builder.when_transition().assert_zero(
                    (AB::Expr::ONE - local[MEM_IS_REAL].into()) * next[MEM_IS_REAL].into(),
                );
                // Positional serials: 1, 2, 3, … (Lean: op i carries serial i+1).
                builder
                    .when_first_row()
                    .assert_zero(local[MEM_SERIAL].into() - AB::Expr::ONE);
                builder.when_transition().assert_zero(
                    next[MEM_SERIAL].into() - local[MEM_SERIAL].into() - AB::Expr::ONE,
                );
                // Read discipline: a read returns exactly its claimed previous value.
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - kind)
                        * (local[MEM_VALUE].into() - local[MEM_PREV_VALUE].into()),
                );
                // prev_serial < serial (Disciplined): gap = is_real·(serial − 1 − prev_serial)
                // and gap ∈ [0, 2^30) by byte decomposition.
                builder.assert_zero(
                    local[MEM_GAP].into()
                        - is_real.clone()
                            * (local[MEM_SERIAL].into()
                                - AB::Expr::ONE
                                - local[MEM_PREV_SERIAL].into()),
                );
                let limbs: Vec<AB::Var> =
                    local[MEM_GAP_LIMB0..MEM_GAP_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[MEM_GAP].into(), &limbs, MEM_GAP_BITS);

                // The table carries EXACTLY the gathered log (memTableFaithful).
                let mem_log = PermutationCheckBus::new(BUS_MEM_LOG);
                mem_log.receive(
                    builder,
                    [
                        local[MEM_ADDR].into(),
                        local[MEM_VALUE].into(),
                        local[MEM_PREV_VALUE].into(),
                        local[MEM_PREV_SERIAL].into(),
                        local[MEM_KIND].into(),
                    ],
                    is_real.clone(),
                );
                // The Blum multiset legs: every op consumes its claimed prior tuple and
                // publishes its own (reads republish their value — Lean writeSetFrom).
                let mem_check = PermutationCheckBus::new(BUS_MEM_CHECK);
                mem_check.send(
                    builder,
                    [
                        local[MEM_ADDR].into(),
                        local[MEM_VALUE].into(),
                        local[MEM_SERIAL].into(),
                    ],
                    is_real.clone(),
                );
                mem_check.receive(
                    builder,
                    [
                        local[MEM_ADDR].into(),
                        local[MEM_PREV_VALUE].into(),
                        local[MEM_PREV_SERIAL].into(),
                    ],
                    is_real.clone(),
                );
                // Address closure: every op address is a declared boundary address.
                let addrs = LookupBus::new(BUS_MEM_ADDRS);
                addrs.lookup_key(builder, [local[MEM_ADDR].into()], is_real);
            }

            // ----------------------------------------------------------------
            Ir2Air::MemBoundary => {
                let is_real: AB::Expr = local[MB_IS_REAL].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                builder.when_transition().assert_zero(
                    (AB::Expr::ONE - local[MB_IS_REAL].into()) * next[MB_IS_REAL].into(),
                );
                // Strictly increasing declared addresses (⇒ Nodup): on a real→real step the
                // gap (next.addr − addr − 1) is bound and range-checked.
                builder.when_transition().assert_zero(
                    local[MB_AGAP].into()
                        - next[MB_IS_REAL].into()
                            * (next[MB_ADDR].into() - local[MB_ADDR].into() - AB::Expr::ONE),
                );
                let agap_limbs: Vec<AB::Var> =
                    local[MB_AGAP_LIMB0..MB_AGAP_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[MB_AGAP].into(), &agap_limbs, MEM_GAP_BITS);
                // Address magnitude bound (so the increasing chain cannot wrap the field):
                // addr_chk = is_real·addr ∈ [0, 2^30).
                builder
                    .assert_zero(local[MB_ACHK].into() - is_real.clone() * local[MB_ADDR].into());
                let achk_limbs: Vec<AB::Var> =
                    local[MB_ACHK_LIMB0..MB_ACHK_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[MB_ACHK].into(), &achk_limbs, MEM_GAP_BITS);

                // Init entries produced at serial 0; final entries consumed.
                let mem_check = PermutationCheckBus::new(BUS_MEM_CHECK);
                mem_check.send(
                    builder,
                    [
                        local[MB_ADDR].into(),
                        local[MB_INIT_VAL].into(),
                        AB::Expr::ZERO,
                    ],
                    is_real.clone(),
                );
                mem_check.receive(
                    builder,
                    [
                        local[MB_ADDR].into(),
                        local[MB_FIN_VAL].into(),
                        local[MB_FIN_SERIAL].into(),
                    ],
                    is_real,
                );
                // The declared-address table for closure lookups.
                let addrs = LookupBus::new(BUS_MEM_ADDRS);
                addrs.table_entry(builder, [local[MB_ADDR].into()], local[MB_ADDR_MULT].into());
            }

            // ----------------------------------------------------------------
            Ir2Air::MapOps => {
                let is_real: AB::Expr = local[MAP_IS_REAL].into();
                let op: AB::Expr = local[MAP_OP].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                // op ∈ {0 (read), 1 (write), 3 (insert)}. Absent (2) is received by the
                // map-absent table; the map-log multiset partitions by op code.
                builder.assert_zero(
                    op.clone()
                        * (op.clone() - AB::Expr::ONE)
                        * (op.clone() - AB::Expr::from_u64(3)),
                );
                // A read returns the committed value: old_value = value on read rows.
                // The `(op - 3)` factor disables this leg for insert (op = 3), where there
                // is no committed old leaf.
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - op.clone())
                        * (op.clone() - AB::Expr::from_u64(3))
                        * (local[MAP_OLD_VALUE].into() - local[MAP_VALUE].into()),
                );
                for lvl in 0..HEAP_TREE_DEPTH {
                    let dir: AB::Expr = local[MAP_DIR0 + lvl].into();
                    builder.assert_zero(dir.clone() * (dir - AB::Expr::ONE));
                }

                // Selector: the old-leaf/old-path legs apply to read/write (op ∈ {0,1})
                // but are vacuous for insert (op = 3). `not_insert` is the unique degree-2
                // polynomial that is 1 at op = 0 and op = 1, and 0 at op = 3.
                let inv6 =
                    AB::Expr::from_u64(BabyBear::new(6).inverse().expect("6 != 0").as_u32() as u64);
                let not_insert: AB::Expr =
                    AB::Expr::ONE - inv6 * op.clone() * (op.clone() - AB::Expr::ONE);

                // Leaf digests ride the chip bus as absorb lookups (gated by is_real — pad rows
                // query nothing). The old-leaf lookup is suppressed on insert rows.
                //
                // LAW#1 / parametric leaf: the absorb arity is NOT a hardcoded `2`. The map-op
                // declares its leaf as a list of INPUT COLUMNS (`map_leaf_input_cols`), and the
                // absorb tuple is built generically from that list by `chip_absorb_tuple` — the
                // Rust twin of the Lean `chipLookupTuple` (`arity :: padTo CHIP_RATE ins ++
                // [digest]`). Today the declared list is the 2-field `[key, value]` shape (the
                // sorted-`Heap` leaf `hash[addr, value]` the `MapOp` denotation pins); a wider
                // leaf would extend the column list with ZERO new branches here. The 7-field cap
                // leaf does NOT ride this op — it is a binary-Merkle membership opening realized
                // as generic chip `Lookup`s (Lean `DeployedCapOpen.leafLookup`, arity 7), the
                // SAME `chip_absorb_tuple` primitive at a different arity. See the module note.
                let p2 = LookupBus::new(BUS_P2);
                // Phase B-GATE: the 17-wide tuple is `[arity, padTo CHIP_RATE inputs, out0..out7]`.
                // `digest_col` is out0 (the chained leaf digest); `lane1_base..+6` are the 7
                // exposed lanes 1..7 (witnessed in the appended leaf-lane columns). The map-op
                // CONSTRAINS only out0 via the fact-chain seed below — lanes 1..7 are carried so
                // the lookup matches the 17-wide chip row, then ignored.
                let chip_absorb_tuple =
                    |inputs: &[usize], digest_col: usize, lane1_base: usize| -> Vec<AB::Expr> {
                        debug_assert!(
                            inputs.len() <= CHIP_RATE,
                            "map-op leaf arity {} exceeds CHIP_RATE {CHIP_RATE}",
                            inputs.len()
                        );
                        let mut t: Vec<AB::Expr> = Vec::with_capacity(CHIP_TUPLE_LEN);
                        t.push(AB::Expr::from_u64(inputs.len() as u64));
                        for &c in inputs {
                            t.push(local[c].into());
                        }
                        for _ in inputs.len()..CHIP_RATE {
                            t.push(AB::Expr::ZERO);
                        }
                        t.push(local[digest_col].into());
                        for i in 0..CHIP_OUT_LANES - 1 {
                            t.push(local[lane1_base + i].into());
                        }
                        t
                    };
                // The declared leaf input columns for read/write/insert: `[key, value-col]`. The
                // old leaf reads the committed `MAP_OLD_VALUE`, the new leaf the written
                // `MAP_VALUE` — same declared key column, the value column distinguishes them.
                let old_leaf_cols = map_leaf_input_cols(MAP_OLD_VALUE);
                let new_leaf_cols = map_leaf_input_cols(MAP_VALUE);
                p2.lookup_key(
                    builder,
                    chip_absorb_tuple(&old_leaf_cols, MAP_OLD_LEAF, MAP_OLD_LEAF1),
                    is_real.clone() * not_insert.clone(),
                );
                p2.lookup_key(
                    builder,
                    chip_absorb_tuple(&new_leaf_cols, MAP_NEW_LEAF, MAP_NEW_LEAF1),
                    is_real.clone(),
                );

                // The sibling-sharing chains ride the fact bus. Write/read share one path;
                // insert uses the SAME columns for a membership opening of the NEW leaf
                // against the NEW root (no old leaf exists at a fresh key). The old-path
                // lookups are gated by `not_insert`; the new-path lookup is always active.
                let fact_bus = LookupBus::new(BUS_FACT);
                let mut cur_old: AB::Expr = local[MAP_OLD_LEAF].into();
                let mut cur_new: AB::Expr = local[MAP_NEW_LEAF].into();
                for lvl in 0..HEAP_TREE_DEPTH {
                    let sib: AB::Expr = local[MAP_SIB0 + lvl].into();
                    let dir: AB::Expr = local[MAP_DIR0 + lvl].into();
                    let mix = |cur: AB::Expr| -> (AB::Expr, AB::Expr) {
                        let left =
                            (AB::Expr::ONE - dir.clone()) * cur.clone() + dir.clone() * sib.clone();
                        let right = (AB::Expr::ONE - dir.clone()) * sib.clone() + dir.clone() * cur;
                        (left, right)
                    };
                    let last = lvl + 1 == HEAP_TREE_DEPTH;
                    let out_old: AB::Expr = if last {
                        local[MAP_ROOT].into()
                    } else {
                        local[MAP_OLD_CHAIN0 + lvl].into()
                    };
                    let (lo, ro) = mix(cur_old.clone());
                    fact_bus.lookup_key(
                        builder,
                        [lo, ro, out_old.clone()],
                        is_real.clone() * not_insert.clone(),
                    );
                    cur_old = out_old;
                    let out_new: AB::Expr = if last {
                        local[MAP_NEW_ROOT].into()
                    } else {
                        local[MAP_NEW_CHAIN0 + lvl].into()
                    };
                    let (ln, rn) = mix(cur_new.clone());
                    fact_bus.lookup_key(builder, [ln, rn, out_new.clone()], is_real.clone());
                    cur_new = out_new;
                }

                // The table carries EXACTLY the gathered log (mapTableFaithful).
                let map_log = PermutationCheckBus::new(BUS_MAP_LOG);
                map_log.receive(
                    builder,
                    [
                        local[MAP_ROOT].into(),
                        local[MAP_KEY].into(),
                        local[MAP_VALUE].into(),
                        local[MAP_OP].into(),
                        local[MAP_NEW_ROOT].into(),
                    ],
                    is_real,
                );
            }

            // ----------------------------------------------------------------
            Ir2Air::MapAbsent => {
                let is_real: AB::Expr = local[MA_IS_REAL].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                for lvl in 0..HEAP_TREE_DEPTH {
                    for dir0 in [MA_LO_DIR0, MA_HI_DIR0] {
                        let dir: AB::Expr = local[dir0 + lvl].into();
                        builder.assert_zero(dir.clone() * (dir - AB::Expr::ONE));
                    }
                }
                // A non-membership read preserves the root.
                builder.assert_zero(
                    is_real.clone() * (local[MA_NEW_ROOT].into() - local[MA_ROOT].into()),
                );

                // ADJACENCY: the two opened leaves sit at consecutive positions
                // (position = Σ dirᵢ·2ⁱ): hi_pos − lo_pos = 1. With the sentinel
                // bracketing this pins the pair as sorted-neighbours of the gap.
                {
                    let mut diff = AB::Expr::ZERO;
                    let mut w = AB::Expr::ONE;
                    for lvl in 0..HEAP_TREE_DEPTH {
                        diff += (local[MA_HI_DIR0 + lvl].into() - local[MA_LO_DIR0 + lvl].into())
                            * w.clone();
                        w = w.clone() + w;
                    }
                    builder.assert_zero(is_real.clone() * (diff - AB::Expr::ONE));
                }

                // THE GAP: lo_addr < key < hi_addr as INTEGERS, via the unique canonical
                // decompositions + lexicographic strict-lt comparators (the in-circuit face
                // of `Crypto.NonMembership.sorted_gap_excludes` / `Heap.get_none_of_gap`).
                let (a_hi4, a_lo27) = eval_canon_decomp(
                    builder,
                    local[MA_LO_ADDR].into(),
                    &local[MA_A_DEC0..MA_A_DEC0 + MA_DECOMP_COLS],
                    is_real.clone(),
                );
                let (k_hi4, k_lo27) = eval_canon_decomp(
                    builder,
                    local[MA_KEY].into(),
                    &local[MA_K_DEC0..MA_K_DEC0 + MA_DECOMP_COLS],
                    is_real.clone(),
                );
                let (b_hi4, b_lo27) = eval_canon_decomp(
                    builder,
                    local[MA_HI_ADDR].into(),
                    &local[MA_B_DEC0..MA_B_DEC0 + MA_DECOMP_COLS],
                    is_real.clone(),
                );
                eval_lex_lt(
                    builder,
                    a_hi4,
                    a_lo27,
                    k_hi4.clone(),
                    k_lo27.clone(),
                    &local[MA_CMP_LO0..MA_CMP_LO0 + MA_CMP_COLS],
                    is_real.clone(),
                    false,
                );
                eval_lex_lt(
                    builder,
                    k_hi4,
                    k_lo27,
                    b_hi4,
                    b_lo27,
                    &local[MA_CMP_HI0..MA_CMP_HI0 + MA_CMP_COLS],
                    is_real.clone(),
                    false,
                );

                // Both bracketing leaves are GENUINE members under the SAME root: leaf
                // digests ride the chip bus (arity-2 absorbs), node hashes ride the fact
                // bus, both final links ARE the root column — the map-ops chain shape, twice.
                let p2 = LookupBus::new(BUS_P2);
                // Phase B-GATE: 17-wide tuple; `leaf_col` is out0, `lane1_base..+6` the lanes 1..7.
                let leaf_tuple =
                    |addr_col: usize, val_col: usize, leaf_col: usize, lane1_base: usize| {
                        let mut t: Vec<AB::Expr> = Vec::with_capacity(CHIP_TUPLE_LEN);
                        t.push(AB::Expr::from_u64(2));
                        t.push(local[addr_col].into());
                        t.push(local[val_col].into());
                        for _ in 2..CHIP_RATE {
                            t.push(AB::Expr::ZERO);
                        }
                        t.push(local[leaf_col].into());
                        for i in 0..CHIP_OUT_LANES - 1 {
                            t.push(local[lane1_base + i].into());
                        }
                        t
                    };
                p2.lookup_key(
                    builder,
                    leaf_tuple(MA_LO_ADDR, MA_LO_VALUE, MA_LO_LEAF, MA_LO_LEAF1),
                    is_real.clone(),
                );
                p2.lookup_key(
                    builder,
                    leaf_tuple(MA_HI_ADDR, MA_HI_VALUE, MA_HI_LEAF, MA_HI_LEAF1),
                    is_real.clone(),
                );
                let fact_bus = LookupBus::new(BUS_FACT);
                for (leaf_col, sib0, dir0, chain0) in [
                    (MA_LO_LEAF, MA_LO_SIB0, MA_LO_DIR0, MA_LO_CHAIN0),
                    (MA_HI_LEAF, MA_HI_SIB0, MA_HI_DIR0, MA_HI_CHAIN0),
                ] {
                    let mut cur: AB::Expr = local[leaf_col].into();
                    for lvl in 0..HEAP_TREE_DEPTH {
                        let sib: AB::Expr = local[sib0 + lvl].into();
                        let dir: AB::Expr = local[dir0 + lvl].into();
                        let left =
                            (AB::Expr::ONE - dir.clone()) * cur.clone() + dir.clone() * sib.clone();
                        let right = (AB::Expr::ONE - dir.clone()) * sib + dir * cur;
                        let out: AB::Expr = if lvl + 1 == HEAP_TREE_DEPTH {
                            local[MA_ROOT].into()
                        } else {
                            local[chain0 + lvl].into()
                        };
                        fact_bus.lookup_key(builder, [left, right, out.clone()], is_real.clone());
                        cur = out;
                    }
                }

                // The table carries EXACTLY the gathered absent sub-log (op code 2, the
                // canonical value 0 — the map-log multiset partitions by op).
                let map_log = PermutationCheckBus::new(BUS_MAP_LOG);
                map_log.receive(
                    builder,
                    [
                        local[MA_ROOT].into(),
                        local[MA_KEY].into(),
                        AB::Expr::ZERO,
                        AB::Expr::from_u64(MapKind::Absent.code() as u64),
                        local[MA_NEW_ROOT].into(),
                    ],
                    is_real,
                );
            }

            // ----------------------------------------------------------------
            Ir2Air::UMemory => {
                let is_real: AB::Expr = local[UM_IS_REAL].into();
                let kind: AB::Expr = local[UM_KIND].into();
                let present: AB::Expr = local[UM_PRESENT].into();
                let prev_present: AB::Expr = local[UM_PREV_PRESENT].into();
                let is_null: AB::Expr = local[UM_IS_NULL].into();
                for b in [&is_real, &kind, &present, &prev_present, &is_null] {
                    builder.assert_zero(b.clone() * (b.clone() - AB::Expr::ONE));
                }
                // Real rows form a prefix.
                builder.when_transition().assert_zero(
                    (AB::Expr::ONE - local[UM_IS_REAL].into()) * next[UM_IS_REAL].into(),
                );
                // Positional serials.
                builder
                    .when_first_row()
                    .assert_zero(local[UM_SERIAL].into() - AB::Expr::ONE);
                builder
                    .when_transition()
                    .assert_zero(next[UM_SERIAL].into() - local[UM_SERIAL].into() - AB::Expr::ONE);
                // Read discipline on the Option cell: a read returns its claimed prior cell.
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - kind.clone())
                        * (local[UM_PRESENT].into() - local[UM_PREV_PRESENT].into()),
                );
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - kind.clone())
                        * (local[UM_VALUE].into() - local[UM_PREV_VALUE].into()),
                );
                // Canonical `none`: an absent cell carries payload 0 (the (present, value)
                // pair is then a faithful encoding of `Option` — Lean `optOf`).
                builder.assert_zero(
                    is_real.clone() * (AB::Expr::ONE - present.clone()) * local[UM_VALUE].into(),
                );
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - prev_present.clone())
                        * local[UM_PREV_VALUE].into(),
                );
                // prev_serial < serial (Disciplined), exactly the flat memory's gap shape.
                builder.assert_zero(
                    local[UM_GAP].into()
                        - is_real.clone()
                            * (local[UM_SERIAL].into()
                                - AB::Expr::ONE
                                - local[UM_PREV_SERIAL].into()),
                );
                let limbs: Vec<AB::Var> =
                    local[UM_GAP_LIMB0..UM_GAP_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[UM_GAP].into(), &limbs, MEM_GAP_BITS);
                // Domain is a nibble (new state components are new codes, never new tables).
                let bus = LookupBus::new(BUS_BYTE);
                bus.lookup_key(builder, [local[UM_DOMAIN].into()], AB::Expr::ONE);
                // THE INSERT-ONLY TOOTH (nullifiers): is_null is FORCED to the domain
                // indicator, and a nullifier-domain write installing `none` is UNSAT —
                // `UniversalMemory.InsertOnlyAt`, in-circuit. This is what upgrades a
                // `present = 0` read into the PROVED freshness fact.
                let dom_m3 = local[UM_DOMAIN].into() - AB::Expr::from_u64(NULLIFIER_DOMAIN as u64);
                builder.assert_zero(dom_m3.clone() * is_null.clone());
                builder.assert_zero(
                    dom_m3 * local[UM_NULL_INV].into() - (is_real.clone() - is_null.clone()),
                );
                builder.assert_zero(is_null * kind * (AB::Expr::ONE - present));

                // The table carries EXACTLY the gathered log (umemTableFaithful).
                let umem_log = PermutationCheckBus::new(BUS_UMEM_LOG);
                umem_log.receive(
                    builder,
                    [
                        local[UM_DOMAIN].into(),
                        local[UM_KEY].into(),
                        local[UM_PRESENT].into(),
                        local[UM_VALUE].into(),
                        local[UM_PREV_PRESENT].into(),
                        local[UM_PREV_VALUE].into(),
                        local[UM_PREV_SERIAL].into(),
                        local[UM_KIND].into(),
                    ],
                    is_real.clone(),
                );
                // The ONE Blum multiset (Lean `MemCheck` over `Domain × κ` with `Option`
                // cells): every op consumes its claimed prior cell and publishes its own.
                let umem_check = PermutationCheckBus::new(BUS_UMEM_CHECK);
                umem_check.send(
                    builder,
                    [
                        local[UM_DOMAIN].into(),
                        local[UM_KEY].into(),
                        local[UM_PRESENT].into(),
                        local[UM_VALUE].into(),
                        local[UM_SERIAL].into(),
                    ],
                    is_real.clone(),
                );
                umem_check.receive(
                    builder,
                    [
                        local[UM_DOMAIN].into(),
                        local[UM_KEY].into(),
                        local[UM_PREV_PRESENT].into(),
                        local[UM_PREV_VALUE].into(),
                        local[UM_PREV_SERIAL].into(),
                    ],
                    is_real.clone(),
                );
                // Address closure over the declared universal boundary.
                let addrs = LookupBus::new(BUS_UMEM_ADDRS);
                addrs.lookup_key(
                    builder,
                    [local[UM_DOMAIN].into(), local[UM_KEY].into()],
                    is_real,
                );
            }

            // ----------------------------------------------------------------
            Ir2Air::UMemBoundary => {
                let is_real: AB::Expr = local[UB_IS_REAL].into();
                let init_present: AB::Expr = local[UB_INIT_PRESENT].into();
                let fin_present: AB::Expr = local[UB_FIN_PRESENT].into();
                let same_dom: AB::Expr = local[UB_SAME_DOM].into();
                for b in [&is_real, &init_present, &fin_present, &same_dom] {
                    builder.assert_zero(b.clone() * (b.clone() - AB::Expr::ONE));
                }
                builder.when_transition().assert_zero(
                    (AB::Expr::ONE - local[UB_IS_REAL].into()) * next[UB_IS_REAL].into(),
                );
                // Canonical `none` images.
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - init_present.clone())
                        * local[UB_INIT_VALUE].into(),
                );
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - fin_present.clone())
                        * local[UB_FIN_VALUE].into(),
                );
                // Domain nibble + the unique canonical key decomposition (full-felt keys).
                let bus = LookupBus::new(BUS_BYTE);
                bus.lookup_key(builder, [local[UB_DOMAIN].into()], AB::Expr::ONE);
                let (hi4, lo27) = eval_canon_decomp(
                    builder,
                    local[UB_KEY].into(),
                    &local[UB_KEY_HI4..UB_KEY_HI4 + MA_DECOMP_COLS],
                    is_real.clone(),
                );
                // DOMAIN-MAJOR LEXICOGRAPHIC strict increase ⇒ the declared addresses are
                // Nodup — the hypothesis `memcheck_sound` stands on, enforced for full-felt
                // keys. dgap = next.domain − domain is a nibble; same_dom is FORCED to the
                // dgap-zero indicator (against next-real); equal domains compare keys.
                bus.lookup_key(builder, [local[UB_DGAP].into()], AB::Expr::ONE);
                {
                    let mut tb = builder.when_transition();
                    tb.assert_zero(
                        local[UB_DGAP].into()
                            - next[UB_IS_REAL].into()
                                * (next[UB_DOMAIN].into() - local[UB_DOMAIN].into()),
                    );
                    tb.assert_zero(
                        local[UB_DGAP].into() * local[UB_SAMEDOM_INV].into()
                            - (next[UB_IS_REAL].into() - local[UB_SAME_DOM].into()),
                    );
                }
                builder.assert_zero(local[UB_DGAP].into() * local[UB_SAME_DOM].into());
                let next_hi4: AB::Expr = next[UB_KEY_HI4].into();
                let next_lo27 =
                    next[UB_KEY].into() - next[UB_KEY_HI4].into() * AB::Expr::from_u64(KEY_HI_BASE);
                eval_lex_lt(
                    builder,
                    hi4,
                    lo27,
                    next_hi4,
                    next_lo27,
                    &local[UB_KCMP_S..UB_KCMP_S + MA_CMP_COLS],
                    same_dom,
                    true,
                );

                // Init cells produced at serial 0; final cells consumed (the ONE balance).
                let umem_check = PermutationCheckBus::new(BUS_UMEM_CHECK);
                umem_check.send(
                    builder,
                    [
                        local[UB_DOMAIN].into(),
                        local[UB_KEY].into(),
                        local[UB_INIT_PRESENT].into(),
                        local[UB_INIT_VALUE].into(),
                        AB::Expr::ZERO,
                    ],
                    is_real.clone(),
                );
                umem_check.receive(
                    builder,
                    [
                        local[UB_DOMAIN].into(),
                        local[UB_KEY].into(),
                        local[UB_FIN_PRESENT].into(),
                        local[UB_FIN_VALUE].into(),
                        local[UB_FIN_SERIAL].into(),
                    ],
                    is_real,
                );
                // The declared-address table for closure lookups.
                let addrs = LookupBus::new(BUS_UMEM_ADDRS);
                addrs.table_entry(
                    builder,
                    [local[UB_DOMAIN].into(), local[UB_KEY].into()],
                    local[UB_ADDR_MULT].into(),
                );
            }
            // ----------------------------------------------------------------
            // The COHORT single-row boundary: the same Blum legs + address table as
            // `UMemBoundary`, but the inter-row lexicographic comparator + key decomposition (the
            // general boundary's `Nodup`-establishing machinery) are GONE. `Nodup` instead follows
            // from there being at most ONE real row, which is forced here: every transition pins
            // `next.is_real = 0`, so row 0 may be real and rows 1.. are pads — a multi-row witness
            // is UNSAT. The soundness of dropping the comparator under this discipline is Lean
            // `UniversalMemory.universal_memory_sound_single` (`[a].Nodup` via `nodup_singleton`,
            // `#assert_axioms`-clean): with ≤1 declared address the dropped columns prove nothing.
            Ir2Air::UMemBoundaryCohort => {
                let is_real: AB::Expr = local[UBC_IS_REAL].into();
                let init_present: AB::Expr = local[UBC_INIT_PRESENT].into();
                let fin_present: AB::Expr = local[UBC_FIN_PRESENT].into();
                for b in [&is_real, &init_present, &fin_present] {
                    builder.assert_zero(b.clone() * (b.clone() - AB::Expr::ONE));
                }
                // THE SINGLE-ROW TOOTH: at most one real row (row 0). Every transition forces the
                // NEXT row to be a pad, so the declared address list has length ≤ 1 ⇒ `Nodup` is
                // free. This is what licenses dropping the lexicographic comparator: there is never
                // a second row to compare against.
                builder
                    .when_transition()
                    .assert_zero(next[UBC_IS_REAL].into());
                // Canonical `none` images (the present bit gates the value to 0 for an absent cell).
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - init_present.clone())
                        * local[UBC_INIT_VALUE].into(),
                );
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - fin_present.clone())
                        * local[UBC_FIN_VALUE].into(),
                );
                // The domain coordinate is a nibble (the shared byte table is exactly [0, 16)).
                let bus = LookupBus::new(BUS_BYTE);
                bus.lookup_key(builder, [local[UBC_DOMAIN].into()], AB::Expr::ONE);
                // Init cells produced at serial 0; final cells consumed — the ONE Blum balance,
                // identical to the general boundary's send/receive (the cohort drops only the
                // ordering machinery, never the multiset legs).
                let umem_check = PermutationCheckBus::new(BUS_UMEM_CHECK);
                umem_check.send(
                    builder,
                    [
                        local[UBC_DOMAIN].into(),
                        local[UBC_KEY].into(),
                        local[UBC_INIT_PRESENT].into(),
                        local[UBC_INIT_VALUE].into(),
                        AB::Expr::ZERO,
                    ],
                    is_real.clone(),
                );
                umem_check.receive(
                    builder,
                    [
                        local[UBC_DOMAIN].into(),
                        local[UBC_KEY].into(),
                        local[UBC_FIN_PRESENT].into(),
                        local[UBC_FIN_VALUE].into(),
                        local[UBC_FIN_SERIAL].into(),
                    ],
                    is_real,
                );
                // The declared-address table for closure lookups (the `umemClosed` tooth).
                let addrs = LookupBus::new(BUS_UMEM_ADDRS);
                addrs.table_entry(
                    builder,
                    [local[UBC_DOMAIN].into(), local[UBC_KEY].into()],
                    local[UBC_ADDR_MULT].into(),
                );
            }
        }
    }
}

// ============================================================================
// Witness generation (the restructure: chip rows + lookup tuples from hash sites,
// memory rows from state accesses, map-op rows from boundary reconciliations)
// ============================================================================

/// Concrete evaluation of a `LeanExpr` over one main row (diagnostic/producer helper).
pub fn eval_lean_expr(e: &LeanExpr, row: &[BabyBear]) -> BabyBear {
    eval_c(e, row)
}

/// Concrete evaluation of a `LeanExpr` over one main row.
fn eval_c(e: &LeanExpr, row: &[BabyBear]) -> BabyBear {
    match e {
        LeanExpr::Var(i) => row[*i],
        LeanExpr::Const(c) => i64_to_babybear(*c),
        LeanExpr::Add(a, b) => eval_c(a, row) + eval_c(b, row),
        LeanExpr::Mul(a, b) => eval_c(a, row) * eval_c(b, row),
    }
}

/// Concrete permutation: full aux block (`poseidon2_permute_expr`'s committed
/// round-state layout) + the squeezed digest (`state[0]` of the last round block).
fn perm_aux(st: [BabyBear; POSEIDON2_WIDTH]) -> (Vec<BabyBear>, BabyBear) {
    let aux = poseidon2_permute_aux_witness(st);
    let digest = aux[aux.len() - POSEIDON2_WIDTH];
    (aux, digest)
}

/// The 8 exposed output lanes `state[0..8]` of the final permutation block — the
/// genuine distinct lanes the chip's widened bus tuple carries (Phase B-GATE).
/// `perm_lanes(st)[0]` equals `perm_aux(st).1` (the squeezed digest).
fn perm_lanes(st: [BabyBear; POSEIDON2_WIDTH]) -> [BabyBear; CHIP_OUT_LANES] {
    let aux = poseidon2_permute_aux_witness(st);
    let base = aux.len() - POSEIDON2_WIDTH;
    core::array::from_fn(|i| aux[base + i])
}

/// **Phase B-GATE producer helper: the 7 exposed chip lanes 1..7 of an absorb.** Seeds the
/// permutation EXACTLY as the chip witness-gen (`build_traces`): the rate-8 inputs, with
/// `state[4..7]` carrying the arity-blend (`big = arity == 7`, else `state[4] = arity`), and
/// returns `perm_lanes(seed)[1..8]` — `state[1..8]` of the SINGLE final permutation. This is the
/// fill every chip-bearing producer writes into a hash site's lane columns so the 17-wide chip
/// lookup matches (`out[i] == lane[i]`); a forged lane is UNSAT. `arity ≤ CHIP_RATE`.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub(crate) fn chip_absorb_lanes(
    arity: usize,
    inputs: &[BabyBear],
) -> [BabyBear; CHIP_OUT_LANES - 1] {
    debug_assert!(arity <= CHIP_RATE && inputs.len() >= arity.min(CHIP_RATE));
    let big = arity == 7;
    let wide = arity == CHIP_WIDE_ARITY;
    let node8 = arity == CHIP_NODE8_ARITY;
    let seed456 = big || wide || node8;
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    for i in 0..4 {
        st[i] = inputs.get(i).copied().unwrap_or(BabyBear::ZERO);
    }
    if seed456 {
        st[4] = inputs.get(4).copied().unwrap_or(BabyBear::ZERO);
        st[5] = inputs.get(5).copied().unwrap_or(BabyBear::ZERO);
        st[6] = inputs.get(6).copied().unwrap_or(BabyBear::ZERO);
    } else {
        st[4] = BabyBear::new(arity as u32);
    }
    // The wide carrier/limb tail (lanes 7..10) AND the node8 second-child tail (lanes 11..15):
    // seeded from the genuine (zero-padded) inputs on EVERY arity — BYTE-IDENTICAL to the chip-row
    // gather (`for i in 7..CHIP_NODE8_ARITY { st[i] = in_i }`, no flag guard). Narrow live arities
    // (≤ 7) zero-pad in7.., so this is a no-op for them; the wide commitment's arity-9 final
    // (`prev8 ‖ iroot`, 9 real inputs) seeds in7/in8; node8's 16 real inputs seed all 16 lanes.
    let _ = (wide, node8);
    for i in 7..CHIP_NODE8_ARITY {
        st[i] = inputs.get(i).copied().unwrap_or(BabyBear::ZERO);
    }
    let lanes = perm_lanes(st);
    core::array::from_fn(|j| lanes[j + 1])
}

/// **THE chip-faithful 8-lane absorb (Phase B-ROTATION wide carriers).** Returns ALL 8 output
/// lanes `state[0..8]` of the SINGLE permutation the chip table derives for a `(arity, inputs)`
/// lookup — seeding lanes 0..6/7..10 BYTE-IDENTICALLY to the chip-row gather (the `seed456` blend
/// and the unconditional `st[7..11] = in7..in10` tail). This is the column fill a wide-commitment
/// producer writes into EACH 8-felt carrier (`out0..out7` of the wide chip tuple), so the AIR's
/// `out[i] == lane[i]` equality holds on every carrier and the 8-felt commit binds. Lane 0 is the
/// squeezed digest (out0); `chip_absorb_lanes` returns exactly lanes 1..7 of this. Unlike
/// `chip_absorb_lanes` it ALWAYS seeds the wide tail (matching the chip gather's
/// `for i in 7..CHIP_WIDE_ARITY { st[i] = in_i }`), so the arity-9 final (which seeds genuine
/// in7/in8) is faithful. `arity ≤ CHIP_RATE`; `inputs` is read up to `CHIP_RATE`, zero-padded.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn chip_absorb_all_lanes(arity: usize, inputs: &[BabyBear]) -> [BabyBear; CHIP_OUT_LANES] {
    debug_assert!(arity <= CHIP_RATE);
    let big = arity == 7;
    let wide = arity == CHIP_WIDE_ARITY;
    let node8 = arity == CHIP_NODE8_ARITY;
    let seed456 = big || wide || node8;
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    for i in 0..4 {
        st[i] = inputs.get(i).copied().unwrap_or(BabyBear::ZERO);
    }
    if seed456 {
        st[4] = inputs.get(4).copied().unwrap_or(BabyBear::ZERO);
        st[5] = inputs.get(5).copied().unwrap_or(BabyBear::ZERO);
        st[6] = inputs.get(6).copied().unwrap_or(BabyBear::ZERO);
    } else {
        st[4] = BabyBear::new(arity as u32);
    }
    // The wide carrier/limb tail (lanes 7..10) AND the node8 second-child tail (lanes 11..15):
    // seeded from the genuine (zero-padded) inputs on EVERY arity — byte-identical to the chip-row
    // gather (`for i in 7..CHIP_NODE8_ARITY`). node8 (arity 16) seeds all 16 lanes = WIDTH.
    for i in 7..CHIP_NODE8_ARITY {
        st[i] = inputs.get(i).copied().unwrap_or(BabyBear::ZERO);
    }
    perm_lanes(st)
}

/// **Phase B-GATE generic chip-lane fill.** For every declared `TID_P2` chip lookup, read the
/// absorb's INPUT values off the row, compute the genuine permutation lanes 1..7
/// (`chip_absorb_lanes`), and write them into the lookup's lane columns (the last
/// `CHIP_OUT_LANES - 1` tuple elements, each a `.var`). Descriptor-driven, so a producer can never
/// misalign with the emitted tuple; out0 (the digest) is assumed already filled by the caller's
/// hash chain. This is the exact column fill the AIR's `out[i] == lane[i]` equality demands — a
/// forged lane is UNSAT (`ir2_forged_output_lane_refuses`). Idempotent on the lane columns.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn fill_chip_lanes(desc: &EffectVmDescriptor2, row: &mut [BabyBear]) {
    for k in &desc.constraints {
        let VmConstraint2::Lookup(l) = k else {
            continue;
        };
        if l.table != TID_P2 {
            continue;
        }
        // tuple = [arity, in0..in7, out0, lane1..lane7]; the arity tag is tuple[0].
        let arity = eval_c(&l.tuple[0], row).as_u32() as usize;
        let ins: [BabyBear; CHIP_RATE] = core::array::from_fn(|i| eval_c(&l.tuple[1 + i], row));
        let lanes = chip_absorb_lanes(arity, &ins);
        for j in 0..(CHIP_OUT_LANES - 1) {
            let LeanExpr::Var(col) = l.tuple[CHIP_RATE + 2 + j] else {
                panic!("chip lookup lane column {j} must be a bare Var");
            };
            row[col] = lanes[j];
        }
    }
}

fn hash2_state_c(a: BabyBear, b: BabyBear) -> [BabyBear; POSEIDON2_WIDTH] {
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    st[0] = a;
    st[1] = b;
    st[4] = BabyBear::new(2);
    st
}

fn fact_state_c(l: BabyBear, r: BabyBear) -> [BabyBear; POSEIDON2_WIDTH] {
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    st[0] = l;
    st[1] = r;
    st[5] = BabyBear::new(FACT_MARK);
    st[6] = BabyBear::ONE;
    st
}

/// Fill one `bits`-wide decomposition (limbs + top bits) of `val`, counting the byte-bus
/// queries into `hist`. `val` must already be `< 2^bits`.
fn fill_decomp(
    val: u32,
    bits: usize,
    out: &mut Vec<BabyBear>,
    hist: &mut [u64; BYTE_TABLE_HEIGHT],
) {
    let (n, top_bits) = limb_geom(bits);
    let partial = top_bits < LIMB_BITS;
    for i in 0..n {
        let byte = (val >> (i * LIMB_BITS)) & ((1 << LIMB_BITS) - 1);
        out.push(BabyBear::new(byte));
        if !(i == n - 1 && partial) {
            hist[byte as usize] += 1;
        }
    }
    if partial {
        let top = (val >> ((n - 1) * LIMB_BITS)) & ((1 << LIMB_BITS) - 1);
        for b in 0..top_bits {
            out.push(BabyBear::new((top >> b) & 1));
        }
    }
}

fn next_pow2(n: usize) -> usize {
    n.next_power_of_two().max(MIN_TABLE_HEIGHT)
}

fn to_matrix(rows: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = rows[0].len();
    let values: Vec<P3BabyBear> = rows
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// The witness-supplied memory boundary: the declared address list (STRICTLY increasing,
/// each `< 2^30`) and the initial image over it. The final image is computed by replaying
/// the gathered log. Lean's `(minit, mfin, maddrs)` triple.
#[derive(Clone, Debug, Default)]
pub struct MemBoundaryWitness {
    /// Declared addresses, strictly increasing.
    pub addrs: Vec<u32>,
    /// Initial value per declared address (same length as `addrs`).
    pub init_vals: Vec<u32>,
}

/// The witness-supplied UNIVERSAL memory boundary: the declared `(domain, key)` address list
/// (domain-major lexicographically STRICTLY increasing; keys are full felts) and the initial
/// `Option` image over it. The final image is computed by replaying the gathered universal
/// log. Lean's `(uinit, ufin, uaddrs)` triple of `Satisfied2U`.
#[derive(Clone, Debug, Default)]
pub struct UMemBoundaryWitness {
    /// Declared `(domain, key)` addresses, lexicographically strictly increasing.
    pub addrs: Vec<(u32, BabyBear)>,
    /// Initial `Option` cell per declared address (same length as `addrs`).
    pub init_vals: Vec<Option<BabyBear>>,
}

impl UMemBoundaryWitness {
    fn is_empty(&self) -> bool {
        self.addrs.is_empty() && self.init_vals.is_empty()
    }
}

/// Which non-main tables the descriptor actually USES — a function of the constraint
/// list (and the resolved layout) ALONE, so prover and verifier compute the same set.
/// Absent tables are NOT committed: FRI opening cost is per-query × the row width of
/// every committed matrix, so a declared-but-unused table is pure proof-size regression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Presence {
    /// Chip table: any chip lookup, or any map op (the openings' permutations ride it).
    chip: bool,
    /// Byte table: any range-lookup limb, any mem/umem op (gap/address decompositions), or
    /// any absent map op (the canonical-decomposition comparators).
    byte: bool,
    /// Memory + boundary tables: any mem op.
    memory: bool,
    /// Map-ops table: any read/write map op.
    map_ops: bool,
    /// Map-absent table: any `absent` map op (the bracketed-gap non-membership leg).
    map_absent: bool,
    /// Universal memory + universal boundary tables: any umem op. NOTE: umem ops alone pull
    /// in NO chip table — the universal memory argument does zero hashing, which is the
    /// measured point of `docs/UNIVERSAL-MEMORY.md`.
    umem: bool,
    /// The universal boundary is the COHORT single-row specialization (`Ir2Air::UMemBoundaryCohort`,
    /// width 9) rather than the general `Ir2Air::UMemBoundary` (width 38). A DECLARATION property
    /// (the descriptor's table-7 sem), NOT derivable from the constraint list — both forms carry
    /// the same `umem_op` — so prover and verifier read it from the SAME descriptor and agree.
    umem_cohort: bool,
}

impl Presence {
    fn of(desc: &EffectVmDescriptor2, layout: &MainLayout) -> Self {
        let has_mem = desc
            .constraints
            .iter()
            .any(|k| matches!(k, VmConstraint2::MemOp(_)));
        let has_map_rw = desc
            .constraints
            .iter()
            .any(|k| matches!(k, VmConstraint2::MapOp(m) if m.op != MapKind::Absent));
        let has_map_absent = desc
            .constraints
            .iter()
            .any(|k| matches!(k, VmConstraint2::MapOp(m) if m.op == MapKind::Absent));
        let has_umem = desc
            .constraints
            .iter()
            .any(|k| matches!(k, VmConstraint2::UMemOp(_)));
        let has_chip_lookup = desc
            .constraints
            .iter()
            .any(|k| matches!(k, VmConstraint2::Lookup(l) if l.table == TID_P2));
        let umem_cohort = has_umem
            && desc
                .tables
                .iter()
                .any(|t| t.sem == TableSem::UMemBoundaryCohort);
        Presence {
            chip: has_chip_lookup || has_map_rw || has_map_absent,
            byte: !layout.ranges.is_empty() || has_mem || has_umem || has_map_absent,
            memory: has_mem,
            map_ops: has_map_rw,
            map_absent: has_map_absent,
            umem: has_umem,
            umem_cohort,
        }
    }
}

/// One fully assembled multi-table witness (the PRESENT instance traces; absent tables
/// are not built — and so contribute no byte-bus pad queries and no committed matrix).
struct Ir2Traces {
    main: Vec<Vec<BabyBear>>,
    chip: Option<Vec<Vec<BabyBear>>>,
    byte: Option<Vec<Vec<BabyBear>>>,
    memory: Option<Vec<Vec<BabyBear>>>,
    boundary: Option<Vec<Vec<BabyBear>>>,
    map_ops: Option<Vec<Vec<BabyBear>>>,
    map_absent: Option<Vec<Vec<BabyBear>>>,
    umemory: Option<Vec<Vec<BabyBear>>>,
    umem_boundary: Option<Vec<Vec<BabyBear>>>,
}

/// Witness fill of one canonical decomposition block `[hi4, lo27 limbs, is15, inv15]` of a
/// canonical (`< p`) value. `real` gates the is15-forcing leg exactly as the AIR's `gate`.
fn fill_canon(v: u32, real: bool, out: &mut Vec<BabyBear>, hist: &mut [u64; BYTE_TABLE_HEIGHT]) {
    let hi4 = v >> KEY_LO_BITS;
    let lo27 = v & ((1u32 << KEY_LO_BITS) - 1);
    out.push(BabyBear::new(hi4));
    hist[hi4 as usize] += 1;
    fill_decomp(lo27, KEY_LO_BITS, out, hist);
    let is15 = real && hi4 as u64 == KEY_HI_MAX;
    out.push(if is15 { BabyBear::ONE } else { BabyBear::ZERO });
    // (hi4 − 15)·inv15 = gate − is15: zero on pads; the field inverse on real non-15 rows.
    let inv15 = if !real || is15 {
        BabyBear::ZERO
    } else {
        (BabyBear::new(hi4) - BabyBear::new(KEY_HI_MAX as u32))
            .inverse()
            .expect("hi4 != 15")
    };
    out.push(inv15);
}

/// Witness fill of one lexicographic strict-lt comparator block `[s, dhi, dlo, dlo limbs]`
/// for `a < b` (both canonical), gated by `active`.
fn fill_lex_lt(
    a: u32,
    b: u32,
    active: bool,
    out: &mut Vec<BabyBear>,
    hist: &mut [u64; BYTE_TABLE_HEIGHT],
) -> Result<(), String> {
    let (a_hi, a_lo) = (a >> KEY_LO_BITS, a & ((1u32 << KEY_LO_BITS) - 1));
    let (b_hi, b_lo) = (b >> KEY_LO_BITS, b & ((1u32 << KEY_LO_BITS) - 1));
    if active && b <= a {
        return Err(format!("lex-lt witness: {b} is not strictly above {a}"));
    }
    let s = active && b_hi != a_hi;
    let dhi = if s { b_hi - a_hi - 1 } else { 0 };
    let dlo = if active && !s { b_lo - a_lo - 1 } else { 0 };
    out.push(if s { BabyBear::ONE } else { BabyBear::ZERO });
    out.push(BabyBear::new(dhi));
    hist[dhi as usize] += 1;
    out.push(BabyBear::new(dlo));
    fill_decomp(dlo, KEY_LO_BITS, out, hist);
    Ok(())
}

/// Assemble the PRESENT instance traces from the base main trace + the boundary witness +
/// the map heaps. `check` controls the prover-side pre-flight replay (the test harness
/// disables it to exercise the in-circuit refusals).
#[allow(clippy::too_many_lines)]
#[allow(clippy::too_many_arguments)]
fn build_traces(
    desc: &EffectVmDescriptor2,
    layout: &MainLayout,
    presence: Presence,
    base_trace: &[Vec<BabyBear>],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    umem_boundary: &UMemBoundaryWitness,
    check: bool,
) -> Result<Ir2Traces, String> {
    let mut byte_hist = [0u64; BYTE_TABLE_HEIGHT];

    // ---- main: base wires + range limb blocks + submask bit blocks. ----
    let mut main: Vec<Vec<BabyBear>> = Vec::with_capacity(base_trace.len());
    for (ri, base_row) in base_trace.iter().enumerate() {
        let mut row = base_row.clone();
        for rb in &layout.ranges {
            let v = base_row[rb.wire].as_u32();
            if (v as u64) >= (1u64 << rb.bits) {
                return Err(format!(
                    "row {ri}: range wire {} value {v} >= 2^{}",
                    rb.wire, rb.bits
                ));
            }
            fill_decomp(v, rb.bits, &mut row, &mut byte_hist);
        }
        for sb in &layout.submasks {
            let keep = eval_c(&sb.keep, base_row).as_u32();
            let held = eval_c(&sb.held, base_row).as_u32();
            for v in [keep, held] {
                if (v as u64) >= (1u64 << SUBMASK_BITS) {
                    return Err(format!("row {ri}: submask operand {v} >= 2^{SUBMASK_BITS}"));
                }
            }
            if check && (keep & held) != keep {
                return Err(format!(
                    "row {ri}: submask violation: keep {keep:#x} ⊄ held {held:#x}"
                ));
            }
            for i in 0..SUBMASK_BITS {
                row.push(BabyBear::new((keep >> i) & 1));
            }
            for i in 0..SUBMASK_BITS {
                row.push(BabyBear::new((held >> i) & 1));
            }
        }
        debug_assert_eq!(row.len(), layout.width);
        main.push(row);
    }

    // ---- chip histograms: absorb tuples from the main rows' chip lookups; fact tuples
    //      come from the map-ops openings below. The table itself is built after the
    //      map section so it carries one row per UNIQUE permutation of EITHER kind. ----
    let mut chip_hist: BTreeMap<Vec<u32>, u64> = BTreeMap::new();
    let mut fact_hist: BTreeMap<(u32, u32, u32), u64> = BTreeMap::new();
    if presence.chip {
        for base_row in base_trace {
            for k in &desc.constraints {
                if let VmConstraint2::Lookup(l) = k
                    && l.table == TID_P2
                {
                    let tuple: Vec<u32> = l
                        .tuple
                        .iter()
                        .map(|e| eval_c(e, base_row).as_u32())
                        .collect();
                    *chip_hist.entry(tuple).or_insert(0) += 1;
                }
            }
        }
    }

    // ---- the memory log (per row, per declared mem op, guard = 1). ----
    let mut mem_log: Vec<[BabyBear; 5]> = Vec::new();
    for (ri, base_row) in base_trace.iter().enumerate() {
        for k in &desc.constraints {
            if let VmConstraint2::MemOp(m) = k {
                let g = eval_c(&m.guard, base_row);
                if g == BabyBear::ZERO {
                    continue;
                }
                if g != BabyBear::ONE {
                    return Err(format!(
                        "row {ri}: mem_op guard evaluates to {g:?}, not 0/1"
                    ));
                }
                mem_log.push([
                    eval_c(&m.addr, base_row),
                    eval_c(&m.value, base_row),
                    eval_c(&m.prev_value, base_row),
                    eval_c(&m.prev_serial, base_row),
                    BabyBear::new(m.kind.code()),
                ]);
            }
        }
    }

    // ---- memory table: log rows in order, positional serials, gap decomposition. ----
    let mut memory: Option<Vec<Vec<BabyBear>>> = None;
    let mut boundary: Option<Vec<Vec<BabyBear>>> = None;
    if presence.memory {
        let mem_height = next_pow2(mem_log.len());
        let mut mem_rows: Vec<Vec<BabyBear>> = Vec::with_capacity(mem_height);
        for i in 0..mem_height {
            let serial = (i + 1) as u32;
            let mut row = vec![BabyBear::ZERO; MEM_ADDR];
            let (tuple, is_real): ([BabyBear; 5], bool) = if i < mem_log.len() {
                (mem_log[i], true)
            } else {
                ([BabyBear::ZERO; 5], false)
            };
            row.extend_from_slice(&tuple);
            row.push(BabyBear::new(serial));
            row.push(if is_real {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            let gap = if is_real {
                let prev = tuple[3].as_u32();
                if prev >= serial {
                    return Err(format!(
                        "memory op {i}: claimed prev serial {prev} not before own serial {serial}"
                    ));
                }
                serial - 1 - prev
            } else {
                0
            };
            if (gap as u64) >= (1u64 << MEM_GAP_BITS) {
                return Err(format!(
                    "memory op {i}: serial gap {gap} >= 2^{MEM_GAP_BITS}"
                ));
            }
            row.push(BabyBear::new(gap));
            fill_decomp(gap, MEM_GAP_BITS, &mut row, &mut byte_hist);
            debug_assert_eq!(row.len(), MEM_WIDTH);
            mem_rows.push(row);
        }
        memory = Some(mem_rows);

        // ---- memory boundary: declared addrs (strictly increasing), replayed final image. ----
        if mem_boundary.addrs.len() != mem_boundary.init_vals.len() {
            return Err("mem boundary addrs/init_vals length mismatch".to_string());
        }
        for w in mem_boundary.addrs.windows(2) {
            if w[1] <= w[0] {
                return Err(format!(
                    "mem boundary addresses must be strictly increasing ({} then {})",
                    w[0], w[1]
                ));
            }
        }
        for &a in &mem_boundary.addrs {
            if (a as u64) >= (1u64 << MEM_GAP_BITS) {
                return Err(format!("mem boundary address {a} >= 2^{MEM_GAP_BITS}"));
            }
        }
        // Replay: image addr → (value, serial); count per-address op multiplicity.
        let mut image: BTreeMap<u32, (BabyBear, u32)> = mem_boundary
            .addrs
            .iter()
            .zip(&mem_boundary.init_vals)
            .map(|(&a, &v)| (a, (BabyBear::new(v), 0u32)))
            .collect();
        let mut addr_mult: BTreeMap<u32, u64> = BTreeMap::new();
        for (i, op) in mem_log.iter().enumerate() {
            let a = op[0].as_u32();
            let Some(&(cur_v, cur_s)) = image.get(&a) else {
                return Err(format!(
                    "memory op {i} touches undeclared address {a} (memClosed)"
                ));
            };
            if check && (op[2] != cur_v || op[3].as_u32() != cur_s) {
                return Err(format!(
                    "memory op {i} at addr {a}: claimed prev ({}, {}) != replayed ({}, {cur_s})",
                    op[2].as_u32(),
                    op[3].as_u32(),
                    cur_v.as_u32(),
                ));
            }
            image.insert(a, (op[1], (i + 1) as u32));
            *addr_mult.entry(a).or_insert(0) += 1;
        }
        let mb_height = next_pow2(mem_boundary.addrs.len());
        let mut mb_rows: Vec<Vec<BabyBear>> = Vec::with_capacity(mb_height);
        for i in 0..mb_height {
            let mut row: Vec<BabyBear> = Vec::with_capacity(MB_WIDTH);
            let (addr, init_v, is_real) = if i < mem_boundary.addrs.len() {
                (
                    mem_boundary.addrs[i],
                    BabyBear::new(mem_boundary.init_vals[i]),
                    true,
                )
            } else {
                (0, BabyBear::ZERO, false)
            };
            let (fin_v, fin_s) = if is_real {
                image[&addr]
            } else {
                (BabyBear::ZERO, 0)
            };
            row.push(BabyBear::new(addr));
            row.push(init_v);
            row.push(fin_v);
            row.push(BabyBear::new(fin_s));
            row.push(if is_real {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            row.push(BabyBear::new(
                (*addr_mult.get(&addr).unwrap_or(&0) % (BABYBEAR_P as u64)) as u32
                    * (is_real as u32),
            ));
            // agap: bound on real→real transitions; zero elsewhere.
            let agap = if i + 1 < mem_boundary.addrs.len() {
                mem_boundary.addrs[i + 1] - addr - 1
            } else {
                0
            };
            row.push(BabyBear::new(agap));
            fill_decomp(agap, MEM_GAP_BITS, &mut row, &mut byte_hist);
            // addr_chk = is_real·addr.
            let achk = if is_real { addr } else { 0 };
            row.push(BabyBear::new(achk));
            fill_decomp(achk, MEM_GAP_BITS, &mut row, &mut byte_hist);
            debug_assert_eq!(row.len(), MB_WIDTH);
            mb_rows.push(row);
        }
        boundary = Some(mb_rows);
    } // if presence.memory

    // ---- the UNIVERSAL memory log (per row, per declared umem op, guard = 1). ----
    let mut umem_log: Vec<[BabyBear; 8]> = Vec::new();
    for (ri, base_row) in base_trace.iter().enumerate() {
        for k in &desc.constraints {
            if let VmConstraint2::UMemOp(m) = k {
                let g = eval_c(&m.guard, base_row);
                if g == BabyBear::ZERO {
                    continue;
                }
                if g != BabyBear::ONE {
                    return Err(format!(
                        "row {ri}: umem_op guard evaluates to {g:?}, not 0/1"
                    ));
                }
                let present = eval_c(&m.present, base_row);
                let value = eval_c(&m.value, base_row);
                let prev_present = eval_c(&m.prev_present, base_row);
                let prev_value = eval_c(&m.prev_value, base_row);
                for (p, v, what) in [
                    (present, value, "cell"),
                    (prev_present, prev_value, "prev cell"),
                ] {
                    if p != BabyBear::ZERO && p != BabyBear::ONE {
                        return Err(format!(
                            "row {ri}: umem_op {what} present bit is {p:?}, not 0/1"
                        ));
                    }
                    if p == BabyBear::ZERO && v != BabyBear::ZERO {
                        return Err(format!(
                            "row {ri}: umem_op {what} is non-canonical: absent (present = 0) \
                             with payload {v:?} != 0"
                        ));
                    }
                }
                umem_log.push([
                    BabyBear::new(m.domain),
                    eval_c(&m.key, base_row),
                    present,
                    value,
                    prev_present,
                    prev_value,
                    eval_c(&m.prev_serial, base_row),
                    BabyBear::new(m.kind.code()),
                ]);
            }
        }
    }

    // ---- universal memory table: log rows, positional serials, gaps, the nullifier
    //      insert-only indicator. NO chip rows: the one-multiset argument hashes nothing. ----
    let mut umemory: Option<Vec<Vec<BabyBear>>> = None;
    let mut umem_boundary_rows: Option<Vec<Vec<BabyBear>>> = None;
    if presence.umem {
        let um_height = next_pow2(umem_log.len());
        let mut um_rows: Vec<Vec<BabyBear>> = Vec::with_capacity(um_height);
        for i in 0..um_height {
            let serial = (i + 1) as u32;
            let (tuple, is_real): ([BabyBear; 8], bool) = if i < umem_log.len() {
                (umem_log[i], true)
            } else {
                ([BabyBear::ZERO; 8], false)
            };
            let mut row: Vec<BabyBear> = Vec::with_capacity(UM_WIDTH);
            row.extend_from_slice(&tuple);
            row.push(BabyBear::new(serial));
            row.push(if is_real {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            let gap = if is_real {
                let prev = tuple[6].as_u32();
                if prev >= serial {
                    return Err(format!(
                        "umem op {i}: claimed prev serial {prev} not before own serial {serial}"
                    ));
                }
                serial - 1 - prev
            } else {
                0
            };
            if (gap as u64) >= (1u64 << MEM_GAP_BITS) {
                return Err(format!("umem op {i}: serial gap {gap} >= 2^{MEM_GAP_BITS}"));
            }
            row.push(BabyBear::new(gap));
            fill_decomp(gap, MEM_GAP_BITS, &mut row, &mut byte_hist);
            // The forced nullifier-domain indicator + its inverse witness.
            let domain = tuple[0];
            byte_hist[domain.as_u32() as usize] += 1; // the domain nibble lookup, every row
            let is_null = is_real && domain.as_u32() == NULLIFIER_DOMAIN;
            row.push(if is_null {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            let null_inv = if !is_real || is_null {
                BabyBear::ZERO
            } else {
                (domain - BabyBear::new(NULLIFIER_DOMAIN))
                    .inverse()
                    .expect("domain != nullifiers")
            };
            row.push(null_inv);
            // THE INSERT-ONLY TOOTH, pre-flight face (the AIR refuses it in-circuit too).
            if is_null && tuple[7] == BabyBear::ONE && tuple[2] == BabyBear::ZERO {
                return Err(format!(
                    "umem op {i}: nullifier-domain write installs an ABSENT cell — \
                     insert-only discipline violated (nobody un-spends)"
                ));
            }
            debug_assert_eq!(row.len(), UM_WIDTH);
            um_rows.push(row);
        }
        umemory = Some(um_rows);

        // ---- universal boundary: declared (domain, key) addresses, lexicographically
        //      strictly increasing; replayed Option final image; full-felt key ordering via
        //      the canonical decomposition. ----
        if umem_boundary.addrs.len() != umem_boundary.init_vals.len() {
            return Err("umem boundary addrs/init_vals length mismatch".to_string());
        }
        for w in umem_boundary.addrs.windows(2) {
            let (d0, k0) = (w[0].0, w[0].1.as_u32());
            let (d1, k1) = (w[1].0, w[1].1.as_u32());
            if (d1, k1) <= (d0, k0) {
                return Err(format!(
                    "umem boundary addresses must be lexicographically strictly increasing \
                     (({d0}, {k0}) then ({d1}, {k1}))"
                ));
            }
        }
        for &(d, _) in &umem_boundary.addrs {
            if d >= DOMAIN_BOUND {
                return Err(format!("umem boundary domain {d} out of the nibble bound"));
            }
        }
        // Replay: image (domain, key) → (present, value, serial); per-address multiplicity.
        let mut image: BTreeMap<(u32, u32), (BabyBear, BabyBear, u32)> = umem_boundary
            .addrs
            .iter()
            .zip(&umem_boundary.init_vals)
            .map(|(&(d, k), &v)| {
                (
                    (d, k.as_u32()),
                    match v {
                        Some(v) => (BabyBear::ONE, v, 0u32),
                        None => (BabyBear::ZERO, BabyBear::ZERO, 0u32),
                    },
                )
            })
            .collect();
        let mut addr_mult: BTreeMap<(u32, u32), u64> = BTreeMap::new();
        for (i, op) in umem_log.iter().enumerate() {
            let a = (op[0].as_u32(), op[1].as_u32());
            let Some(&(cur_p, cur_v, cur_s)) = image.get(&a) else {
                return Err(format!(
                    "umem op {i} touches undeclared address ({}, {}) (umemClosed)",
                    a.0, a.1
                ));
            };
            if check && (op[4] != cur_p || op[5] != cur_v || op[6].as_u32() != cur_s) {
                return Err(format!(
                    "umem op {i} at ({}, {}): claimed prev cell ({}, {}, {}) != replayed \
                     ({}, {}, {cur_s})",
                    a.0,
                    a.1,
                    op[4].as_u32(),
                    op[5].as_u32(),
                    op[6].as_u32(),
                    cur_p.as_u32(),
                    cur_v.as_u32(),
                ));
            }
            image.insert(a, (op[2], op[3], (i + 1) as u32));
            *addr_mult.entry(a).or_insert(0) += 1;
        }
        // The COHORT single-row boundary (`Ir2Air::UMemBoundaryCohort`, width 9) drops the key
        // decomposition + lexicographic comparator: it requires AT MOST ONE declared address, for
        // which `Nodup` is free. Refuse a multi-address witness here (the AIR also refuses it via
        // the single-row tooth, but failing in the assembler is the clearer diagnostic).
        if presence.umem_cohort && umem_boundary.addrs.len() > 1 {
            return Err(format!(
                "umem_boundary_cohort: {} declared addresses — the cohort single-row boundary \
                 carries at most one (a multi-address leg uses the general umem_boundary table)",
                umem_boundary.addrs.len()
            ));
        }
        let ub_width = if presence.umem_cohort {
            UBC_WIDTH
        } else {
            UB_WIDTH
        };
        let ub_height = next_pow2(umem_boundary.addrs.len());
        let mut ub_rows: Vec<Vec<BabyBear>> = Vec::with_capacity(ub_height);
        for i in 0..ub_height {
            let mut row: Vec<BabyBear> = Vec::with_capacity(ub_width);
            let (domain, key, init, is_real) = if i < umem_boundary.addrs.len() {
                (
                    umem_boundary.addrs[i].0,
                    umem_boundary.addrs[i].1,
                    umem_boundary.init_vals[i],
                    true,
                )
            } else {
                (0, BabyBear::ZERO, None, false)
            };
            let (init_p, init_v) = match init {
                Some(v) => (BabyBear::ONE, v),
                None => (BabyBear::ZERO, BabyBear::ZERO),
            };
            let (fin_p, fin_v, fin_s) = if is_real {
                image[&(domain, key.as_u32())]
            } else {
                (BabyBear::ZERO, BabyBear::ZERO, 0)
            };
            row.push(BabyBear::new(domain));
            byte_hist[domain as usize] += 1; // the domain nibble lookup, every row
            row.push(key);
            row.push(init_p);
            row.push(init_v);
            row.push(fin_p);
            row.push(fin_v);
            row.push(BabyBear::new(fin_s));
            row.push(if is_real {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            });
            row.push(BabyBear::new(
                (*addr_mult.get(&(domain, key.as_u32())).unwrap_or(&0) % (BABYBEAR_P as u64))
                    as u32
                    * (is_real as u32),
            ));
            // The cohort row STOPS at the 9 base columns — the key decomposition + lexicographic
            // comparator (the general boundary's `Nodup`-establishing machinery) are absent.
            if !presence.umem_cohort {
                fill_canon(key.as_u32(), is_real, &mut row, &mut byte_hist);
                // Ordering witness vs the NEXT declared row.
                let next_real = i + 1 < umem_boundary.addrs.len();
                let (dgap, same_dom) = if next_real {
                    let nd = umem_boundary.addrs[i + 1].0;
                    (nd - domain, nd == domain)
                } else {
                    (0, false)
                };
                row.push(BabyBear::new(dgap));
                byte_hist[dgap as usize] += 1; // the dgap nibble lookup, every row
                row.push(if same_dom {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                });
                // dgap·inv = next_real − same_dom: the inverse witness when domains differ.
                row.push(if next_real && dgap != 0 {
                    BabyBear::new(dgap).inverse().expect("dgap != 0")
                } else {
                    BabyBear::ZERO
                });
                let next_key = if next_real {
                    umem_boundary.addrs[i + 1].1.as_u32()
                } else {
                    0
                };
                fill_lex_lt(key.as_u32(), next_key, same_dom, &mut row, &mut byte_hist)?;
            }
            debug_assert_eq!(row.len(), ub_width);
            ub_rows.push(row);
        }
        umem_boundary_rows = Some(ub_rows);
    } // if presence.umem

    // ---- the map-ops log + the opening witnesses. ----
    let mut map_log: Vec<([BabyBear; 5], MapKind)> = Vec::new();
    for (ri, base_row) in base_trace.iter().enumerate() {
        for k in &desc.constraints {
            if let VmConstraint2::MapOp(m) = k {
                let g = eval_c(&m.guard, base_row);
                if g == BabyBear::ZERO {
                    continue;
                }
                if g != BabyBear::ONE {
                    return Err(format!(
                        "row {ri}: map_op guard evaluates to {g:?}, not 0/1"
                    ));
                }
                map_log.push((
                    [
                        eval_c(&m.root, base_row),
                        eval_c(&m.key, base_row),
                        eval_c(&m.value, base_row),
                        BabyBear::new(m.op.code()),
                        eval_c(&m.new_root, base_row),
                    ],
                    m.op,
                ));
            }
        }
    }
    let mut map_ops: Option<Vec<Vec<BabyBear>>> = None;
    let mut map_absent: Option<Vec<Vec<BabyBear>>> = None;
    if presence.map_ops || presence.map_absent {
        let mut trees: Vec<CanonicalHeapTree> = map_heaps
            .iter()
            .map(|leaves| CanonicalHeapTree::new(leaves.clone(), HEAP_TREE_DEPTH))
            .collect();
        let mut map_rows: Vec<Vec<BabyBear>> = Vec::new();
        let mut ma_rows: Vec<Vec<BabyBear>> = Vec::new();
        for (i, (tuple, kind)) in map_log.iter().enumerate() {
            let [root, key, value, _opc, new_root] = *tuple;
            let tree = trees
                .iter()
                .find(|t| t.root() == root)
                .cloned()
                .ok_or_else(|| {
                    format!("map op {i}: no witness heap with root {}", root.as_u32())
                })?;

            // -- `absent`: the bracketed sorted-gap non-membership opening, its own table. --
            if *kind == MapKind::Absent {
                if check && new_root != root {
                    return Err(format!("map op {i}: absent must preserve the root"));
                }
                if check && value != BabyBear::ZERO {
                    return Err(format!("map op {i}: absent carries the canonical value 0"));
                }
                let key_u = key.as_u32();
                if key == SENTINEL_MIN || key.as_u32() >= SENTINEL_MAX.as_u32() {
                    return Err(format!(
                        "map op {i}: absent key {key_u} collides with the sentinel range"
                    ));
                }
                if tree.position_of(key).is_some() {
                    return Err(format!(
                        "map op {i}: absent key {key_u} IS present in the heap — no bracketing \
                     witness exists (the gap teeth would refuse it in-circuit)"
                    ));
                }
                let leaves = tree.sorted_leaves();
                let lo_pos = leaves
                    .iter()
                    .rposition(|l| l.addr.as_u32() < key_u)
                    .ok_or_else(|| format!("map op {i}: no lower bracket for key {key_u}"))?;
                let lo = leaves[lo_pos];
                let hi = *leaves
                    .get(lo_pos + 1)
                    .ok_or_else(|| format!("map op {i}: no upper bracket for key {key_u}"))?;
                debug_assert!(hi.addr.as_u32() > key_u);
                let (lo_sibs, lo_dirs) = tree
                    .prove_membership(lo_pos)
                    .ok_or_else(|| format!("map op {i}: lower bracket path failed"))?;
                let (hi_sibs, hi_dirs) = tree
                    .prove_membership(lo_pos + 1)
                    .ok_or_else(|| format!("map op {i}: upper bracket path failed"))?;

                let mut cols: Vec<BabyBear> = Vec::with_capacity(MA_WIDTH);
                cols.push(root);
                cols.push(key);
                cols.push(new_root);
                cols.push(BabyBear::ONE);
                cols.push(lo.addr);
                cols.push(lo.value);
                cols.push(hi.addr);
                cols.push(hi.value);
                // The two leaf digests (chip absorbs) + the two fact chains to the root.
                // Phase B-GATE: the absorb rides the 17-wide chip bus, so we keep all 8 lanes —
                // lane0 is the digest (the fact-chain seed), lanes 1..7 are carried to match the
                // chip row (appended at the tail of the row below).
                let leaf_lanes = |a: BabyBear, b: BabyBear| perm_lanes(hash2_state_c(a, b));
                // The 17-wide histogram key: `[2, a, b, 0×6, lane0..lane7]`.
                let absorb2_tuple = |a: BabyBear, b: BabyBear, lanes: &[BabyBear]| -> Vec<u32> {
                    let mut t = vec![2u32, a.as_u32(), b.as_u32()];
                    t.extend(std::iter::repeat_n(0u32, CHIP_RATE - 2));
                    t.extend(lanes.iter().map(|d| d.as_u32()));
                    t
                };
                let lo_lanes = leaf_lanes(lo.addr, lo.value);
                let hi_lanes = leaf_lanes(hi.addr, hi.value);
                let lo_leaf = lo_lanes[0];
                let hi_leaf = hi_lanes[0];
                *chip_hist
                    .entry(absorb2_tuple(lo.addr, lo.value, &lo_lanes))
                    .or_insert(0) += 1;
                *chip_hist
                    .entry(absorb2_tuple(hi.addr, hi.value, &hi_lanes))
                    .or_insert(0) += 1;
                cols.push(lo_leaf);
                cols.push(hi_leaf);
                let mut chains: Vec<Vec<BabyBear>> = Vec::with_capacity(2);
                for (leaf, sibs, dirs) in
                    [(lo_leaf, &lo_sibs, &lo_dirs), (hi_leaf, &hi_sibs, &hi_dirs)]
                {
                    let mut chain: Vec<BabyBear> = Vec::with_capacity(HEAP_TREE_DEPTH - 1);
                    let mut cur = leaf;
                    for lvl in 0..HEAP_TREE_DEPTH {
                        let sib = sibs[lvl];
                        let (l, r) = if dirs[lvl] != 0 {
                            (sib, cur)
                        } else {
                            (cur, sib)
                        };
                        let d = perm_aux(fact_state_c(l, r)).1;
                        *fact_hist
                            .entry((l.as_u32(), r.as_u32(), d.as_u32()))
                            .or_insert(0) += 1;
                        if lvl + 1 < HEAP_TREE_DEPTH {
                            chain.push(d);
                        }
                        cur = d;
                    }
                    debug_assert_eq!(cur, root, "bracket path must authenticate against the root");
                    chains.push(chain);
                }
                for sibs in [&lo_sibs, &hi_sibs] {
                    debug_assert_eq!(sibs.len(), HEAP_TREE_DEPTH);
                }
                cols.extend_from_slice(&lo_sibs);
                cols.extend(lo_dirs.iter().map(|&d| BabyBear::new(d as u32)));
                cols.extend_from_slice(&chains[0]);
                cols.extend_from_slice(&hi_sibs);
                cols.extend(hi_dirs.iter().map(|&d| BabyBear::new(d as u32)));
                cols.extend_from_slice(&chains[1]);
                // Canonical decompositions of (lo_addr, key, hi_addr) + the two gap comparators.
                fill_canon(lo.addr.as_u32(), true, &mut cols, &mut byte_hist);
                fill_canon(key_u, true, &mut cols, &mut byte_hist);
                fill_canon(hi.addr.as_u32(), true, &mut cols, &mut byte_hist);
                fill_lex_lt(lo.addr.as_u32(), key_u, true, &mut cols, &mut byte_hist)?;
                fill_lex_lt(key_u, hi.addr.as_u32(), true, &mut cols, &mut byte_hist)?;
                // Phase B-GATE: the appended leaf-lane columns (MA_LO_LEAF1.., MA_HI_LEAF1..).
                debug_assert_eq!(cols.len(), MA_LO_LEAF1);
                cols.extend_from_slice(&lo_lanes[1..]);
                cols.extend_from_slice(&hi_lanes[1..]);
                debug_assert_eq!(cols.len(), MA_WIDTH);
                ma_rows.push(cols);
                continue;
            }

            let (old_value, sibs, dirs) = match kind {
                MapKind::Read => {
                    let pos = tree.position_of(key).ok_or_else(|| {
                        format!("map op {i}: read key {} not in heap", key.as_u32())
                    })?;
                    let leaf = tree.sorted_leaves()[pos];
                    if check && leaf.value != value {
                        return Err(format!(
                            "map op {i}: read at key {} opens to {}, row claims {}",
                            key.as_u32(),
                            leaf.value.as_u32(),
                            value.as_u32()
                        ));
                    }
                    if check && new_root != root {
                        return Err(format!("map op {i}: read must preserve the root"));
                    }
                    let (sibs, dirs) = tree
                        .prove_membership(pos)
                        .ok_or_else(|| format!("map op {i}: membership path failed"))?;
                    (value, sibs, dirs)
                }
                MapKind::Write => {
                    let w = tree
                        .update_witness(HeapLeaf { addr: key, value })
                        .ok_or_else(|| {
                            format!(
                                "map op {i}: write key {} not present — use MapKind::Insert for \
                             fresh-key sorted inserts",
                                key.as_u32()
                            )
                        })?;
                    if check && w.new_root != new_root {
                        return Err(format!(
                            "map op {i}: claimed new_root {} != genuine sorted write {}",
                            new_root.as_u32(),
                            w.new_root.as_u32()
                        ));
                    }
                    // Advance the working set: the post-write heap is reachable for later ops.
                    let new_leaves: Vec<HeapLeaf> = tree
                        .sorted_leaves()
                        .iter()
                        .map(|l| {
                            if l.addr == key {
                                HeapLeaf { addr: key, value }
                            } else {
                                *l
                            }
                        })
                        .collect();
                    trees.push(CanonicalHeapTree::new(new_leaves, HEAP_TREE_DEPTH));
                    (w.old_leaf.value, w.siblings, w.directions)
                }
                MapKind::Insert => {
                    let w = tree
                        .insert_witness(HeapLeaf { addr: key, value })
                        .ok_or_else(|| {
                            format!(
                                "map op {i}: insert key {} already present or collides with \
                             sentinels",
                                key.as_u32()
                            )
                        })?;
                    if check && w.new_root != new_root {
                        return Err(format!(
                            "map op {i}: claimed new_root {} != genuine sorted insert {}",
                            new_root.as_u32(),
                            w.new_root.as_u32()
                        ));
                    }
                    // Advance the working set: the post-insert heap is reachable for later ops.
                    let mut new_leaves: Vec<HeapLeaf> = tree
                        .sorted_leaves()
                        .iter()
                        .filter(|l| l.addr != SENTINEL_MIN && l.addr != SENTINEL_MAX)
                        .copied()
                        .collect();
                    new_leaves.push(HeapLeaf { addr: key, value });
                    trees.push(CanonicalHeapTree::new(new_leaves, HEAP_TREE_DEPTH));
                    (BabyBear::ZERO, w.siblings, w.directions)
                }
                MapKind::Absent => unreachable!("absent handled above"),
            };
            let mut cols = vec![BabyBear::ZERO; MAP_WIDTH];
            cols[MAP_ROOT] = root;
            cols[MAP_KEY] = key;
            cols[MAP_VALUE] = value;
            cols[MAP_OP] = BabyBear::new(kind.code());
            cols[MAP_NEW_ROOT] = new_root;
            cols[MAP_IS_REAL] = BabyBear::ONE;
            cols[MAP_OLD_VALUE] = old_value;
            for lvl in 0..HEAP_TREE_DEPTH {
                cols[MAP_SIB0 + lvl] = sibs[lvl];
                cols[MAP_DIR0 + lvl] = BabyBear::new(dirs[lvl] as u32);
            }
            // The opening's permutations ride the chip table: the leaf hashes are absorb
            // tuples on the chip bus (arity = the declared leaf-input count, today 2 — the
            // `[key, value]` `Heap` leaf), the chains' node hashes are fact tuples on the fact
            // bus. The row carries digests only, never aux. The absorb tuple is built from the
            // SAME declared leaf-input values the AIR's `chip_absorb_tuple` reads off the
            // declared columns (`map_leaf_input_cols`), so prover/verifier agree on the arity.
            // Phase B-GATE: keep all 8 lanes of each leaf absorb (lane0 = the chained digest /
            // fact-chain seed, lanes 1..7 carried to match the 17-wide chip row).
            let leaf_lanes = |a: BabyBear, b: BabyBear| perm_lanes(hash2_state_c(a, b));
            let absorb2_tuple = |a: BabyBear, b: BabyBear, lanes: &[BabyBear]| -> Vec<u32> {
                // The declared inputs are `[key, value]`; the histogram key mirrors the AIR's
                // `arity :: inputs ++ pad ++ out0..out7` tuple at the declared arity.
                let inputs = [a.as_u32(), b.as_u32()];
                let mut t = vec![inputs.len() as u32];
                t.extend_from_slice(&inputs);
                t.extend(std::iter::repeat_n(0u32, CHIP_RATE - inputs.len()));
                t.extend(lanes.iter().map(|d| d.as_u32()));
                t
            };
            let is_insert = *kind == MapKind::Insert;
            let new_lanes = leaf_lanes(key, value);
            let new_leaf = new_lanes[0];
            *chip_hist
                .entry(absorb2_tuple(key, value, &new_lanes))
                .or_insert(0) += 1;
            cols[MAP_NEW_LEAF] = new_leaf;
            cols[MAP_NEW_LEAF1..MAP_NEW_LEAF1 + CHIP_OUT_LANES - 1]
                .copy_from_slice(&new_lanes[1..CHIP_OUT_LANES]);
            if is_insert {
                // Insert rows have no committed old leaf; the AIR's old-path legs are gated
                // away by `op - 3`. Leave old-leaf / old-chain columns at zero.
                cols[MAP_OLD_VALUE] = BabyBear::ZERO;
            } else {
                let old_lanes = leaf_lanes(key, old_value);
                let old_leaf = old_lanes[0];
                *chip_hist
                    .entry(absorb2_tuple(key, old_value, &old_lanes))
                    .or_insert(0) += 1;
                cols[MAP_OLD_LEAF] = old_leaf;
                cols[MAP_OLD_LEAF1..MAP_OLD_LEAF1 + CHIP_OUT_LANES - 1]
                    .copy_from_slice(&old_lanes[1..CHIP_OUT_LANES]);
                let mut cur_old = old_leaf;
                for lvl in 0..HEAP_TREE_DEPTH {
                    let sib = sibs[lvl];
                    let mix = |cur: BabyBear| -> (BabyBear, BabyBear) {
                        if dirs[lvl] != 0 {
                            (sib, cur)
                        } else {
                            (cur, sib)
                        }
                    };
                    let (lo, ro) = mix(cur_old);
                    let d_old = perm_aux(fact_state_c(lo, ro)).1;
                    *fact_hist
                        .entry((lo.as_u32(), ro.as_u32(), d_old.as_u32()))
                        .or_insert(0) += 1;
                    if lvl + 1 < HEAP_TREE_DEPTH {
                        cols[MAP_OLD_CHAIN0 + lvl] = d_old;
                    }
                    cur_old = d_old;
                }
            }
            let mut cur_new = new_leaf;
            for lvl in 0..HEAP_TREE_DEPTH {
                let sib = sibs[lvl];
                let mix = |cur: BabyBear| -> (BabyBear, BabyBear) {
                    if dirs[lvl] != 0 {
                        (sib, cur)
                    } else {
                        (cur, sib)
                    }
                };
                let (ln, rn) = mix(cur_new);
                let d_new = perm_aux(fact_state_c(ln, rn)).1;
                *fact_hist
                    .entry((ln.as_u32(), rn.as_u32(), d_new.as_u32()))
                    .or_insert(0) += 1;
                if lvl + 1 < HEAP_TREE_DEPTH {
                    cols[MAP_NEW_CHAIN0 + lvl] = d_new;
                }
                cur_new = d_new;
            }
            map_rows.push(cols);
        }
        // Pad rows: all-zero for map-ops (is_real = 0 gates every lookup and the log receive);
        // canon/comparator-shaped zeros for map-absent (its hi4/dhi/limb lookups ride the byte
        // bus with multiplicity ONE on every row, so pads contribute their zero queries).
        if presence.map_ops {
            let map_height = next_pow2(map_rows.len());
            while map_rows.len() < map_height {
                map_rows.push(vec![BabyBear::ZERO; MAP_WIDTH]);
            }
            map_ops = Some(map_rows);
        } else if !map_rows.is_empty() {
            return Err("read/write map ops gathered but the map-ops table is absent".to_string());
        }
        if presence.map_absent {
            let ma_height = next_pow2(ma_rows.len());
            while ma_rows.len() < ma_height {
                let mut cols: Vec<BabyBear> = vec![BabyBear::ZERO; MA_A_DEC0];
                for _ in 0..3 {
                    fill_canon(0, false, &mut cols, &mut byte_hist);
                }
                for _ in 0..2 {
                    fill_lex_lt(0, 0, false, &mut cols, &mut byte_hist)?;
                }
                // Phase B-GATE: the appended leaf-lane columns (is_real = 0 gates the lookup,
                // so the lanes are unconstrained on a pad row — plain zeros).
                debug_assert_eq!(cols.len(), MA_LO_LEAF1);
                cols.resize(MA_WIDTH, BabyBear::ZERO);
                debug_assert_eq!(cols.len(), MA_WIDTH);
                ma_rows.push(cols);
            }
            map_absent = Some(ma_rows);
        } else if !ma_rows.is_empty() {
            return Err("absent map ops gathered but the map-absent table is absent".to_string());
        }
    } // if presence.map_ops || presence.map_absent

    // ---- chip table: one row per unique permutation (absorb + fact), mult-counted. ----
    let chip: Option<Vec<Vec<BabyBear>>> = if presence.chip {
        let mut chip_rows: Vec<Vec<BabyBear>> = Vec::new();
        for (tuple, mult) in &chip_hist {
            // tuple = [arity, in0..in15, out0..out7] (CHIP_TUPLE_LEN = 25 wide).
            let arity_u = tuple[CHIP_ARITY];
            let big_row = arity_u == 7;
            let wide_row = arity_u as usize == CHIP_WIDE_ARITY;
            let node8_row = arity_u as usize == CHIP_NODE8_ARITY;
            // `seed456`: lanes 4/5/6 carry genuine in4/in5/in6 (rate-8 leaf, wide step, OR node8).
            let seed456 = big_row || wide_row || node8_row;
            let mut row = vec![BabyBear::ZERO; CHIP_AUX0];
            // Copy only the [arity, in0..in15] prefix from the tuple; the out0..out7 lanes are
            // DERIVED below from the genuine permutation (never trusted from the consumer's
            // tuple), so the AIR's `out[i] == lane[i]` equality constraints hold by construction.
            for j in 0..=CHIP_RATE {
                row[j] = BabyBear::new(tuple[j]);
            }
            row[CHIP_MULT] = BabyBear::new((*mult % (BABYBEAR_P as u64)) as u32);
            row[CHIP_IS_FACT] = BabyBear::ZERO;
            row[CHIP_BIG] = if big_row {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[CHIP_WIDE] = if wide_row {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[CHIP_NODE8] = if node8_row {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            // Seed-source columns, mirroring the AIR's S4/S5/S6 blend (is_fact = 0 here).
            if seed456 {
                row[CHIP_S4] = BabyBear::new(tuple[CHIP_IN0 + 4]);
                row[CHIP_S5] = BabyBear::new(tuple[CHIP_IN0 + 5]);
                row[CHIP_S6] = BabyBear::new(tuple[CHIP_IN0 + 6]);
            } else {
                row[CHIP_S4] = BabyBear::new(arity_u); // arity tag
                row[CHIP_S5] = BabyBear::ZERO; // is_fact·FACT_MARK = 0
                row[CHIP_S6] = BabyBear::ZERO; // is_fact = 0
            }
            // Seed the permutation from the SAME source columns the AIR reads.
            let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
            st[..4].copy_from_slice(&row[CHIP_IN0..CHIP_IN0 + 4]);
            st[4] = row[CHIP_S4];
            st[5] = row[CHIP_S5];
            st[6] = row[CHIP_S6];
            // Carrier/limb tail (lanes 7..15): genuine inputs on the wide (7..10) + node8 (7..15)
            // rows, pinned 0 on every narrow arity (the tuple's in7.. are zero there), matching the
            // AIR seeding. node8 (arity 16) seeds all 16 lanes = WIDTH.
            st[7..CHIP_NODE8_ARITY]
                .copy_from_slice(&row[CHIP_IN0 + 7..CHIP_IN0 + CHIP_NODE8_ARITY]);
            // Fill the 8 exposed output lanes from the genuine final permutation state.
            let lanes = perm_lanes(st);
            row[CHIP_OUT..CHIP_OUT + CHIP_OUT_LANES].copy_from_slice(&lanes[..CHIP_OUT_LANES]);
            let (aux, _digest) = perm_aux(st);
            row.extend(aux);
            chip_rows.push(row);
        }
        for (&(l, r, out), mult) in &fact_hist {
            let mut row = vec![BabyBear::ZERO; CHIP_AUX0];
            row[CHIP_IN0] = BabyBear::new(l);
            row[CHIP_IN0 + 1] = BabyBear::new(r);
            row[CHIP_OUT] = BabyBear::new(out);
            row[CHIP_MULT] = BabyBear::new((*mult % (BABYBEAR_P as u64)) as u32);
            row[CHIP_IS_FACT] = BabyBear::ONE;
            // Fact rows are rate-4 (big = 0): S4 = arity tag (0), S5 = FACT_MARK, S6 = 1 —
            // reproduces `fact_state_c` (st[5]=FACT_MARK, st[6]=1) through the S4/S5/S6 seeding.
            row[CHIP_BIG] = BabyBear::ZERO;
            row[CHIP_S4] = BabyBear::ZERO;
            row[CHIP_S5] = BabyBear::new(FACT_MARK);
            row[CHIP_S6] = BabyBear::ONE;
            // Fill the 8 exposed output lanes (the AIR's `out[i] == lane[i]` equality applies
            // to fact rows too; only the fact bus's 3-wide `[l, r, out0]` is consumed though).
            let fst = fact_state_c(BabyBear::new(l), BabyBear::new(r));
            let lanes = perm_lanes(fst);
            row[CHIP_OUT..CHIP_OUT + CHIP_OUT_LANES].copy_from_slice(&lanes[..CHIP_OUT_LANES]);
            debug_assert_eq!(row[CHIP_OUT], BabyBear::new(out));
            let (aux, _digest) = perm_aux(fst);
            row.extend(aux);
            chip_rows.push(row);
        }
        // Pad: genuine arity-0 absorb permutation rows with multiplicity 0.
        let pad_lanes = perm_lanes([BabyBear::ZERO; POSEIDON2_WIDTH]);
        let (aux, digest) = perm_aux([BabyBear::ZERO; POSEIDON2_WIDTH]);
        let mut pad = vec![BabyBear::ZERO; CHIP_AUX0];
        debug_assert_eq!(pad_lanes[0], digest);
        pad[CHIP_OUT..CHIP_OUT + CHIP_OUT_LANES].copy_from_slice(&pad_lanes[..CHIP_OUT_LANES]);
        pad.extend(aux);
        let target = next_pow2(chip_rows.len());
        while chip_rows.len() < target {
            chip_rows.push(pad.clone());
        }
        Some(chip_rows)
    } else {
        None
    };

    // ---- the byte table (height pinned at 256). ----
    let byte: Option<Vec<Vec<BabyBear>>> = presence.byte.then(|| {
        (0..BYTE_TABLE_HEIGHT)
            .map(|b| {
                vec![
                    BabyBear::new(b as u32),
                    BabyBear::new((byte_hist[b] % (BABYBEAR_P as u64)) as u32),
                ]
            })
            .collect()
    });

    Ok(Ir2Traces {
        main,
        chip,
        byte,
        memory,
        boundary,
        map_ops,
        map_absent,
        umemory,
        umem_boundary: umem_boundary_rows,
    })
}

/// The PRESENT instance AIRs for a checked descriptor, in canonical instance order
/// (main, then chip / byte / memory+boundary / map-ops, each iff the descriptor uses it).
/// Presence is a function of the descriptor alone, so the verifier rebuilds the same set.
fn instance_airs(
    desc: &EffectVmDescriptor2,
    layout: MainLayout,
    presence: Presence,
) -> Vec<Ir2Air> {
    let mut airs = vec![Ir2Air::Main {
        desc: desc.clone(),
        layout: MainLayoutPub(layout),
    }];
    if presence.chip {
        airs.push(Ir2Air::Chip);
    }
    if presence.byte {
        airs.push(Ir2Air::ByteTable);
    }
    if presence.memory {
        airs.push(Ir2Air::Memory);
        airs.push(Ir2Air::MemBoundary);
    }
    if presence.map_ops {
        airs.push(Ir2Air::MapOps);
    }
    if presence.map_absent {
        airs.push(Ir2Air::MapAbsent);
    }
    if presence.umem {
        airs.push(Ir2Air::UMemory);
        airs.push(if presence.umem_cohort {
            Ir2Air::UMemBoundaryCohort
        } else {
            Ir2Air::UMemBoundary
        });
    }
    airs
}

/// The IR-v2 FRI configuration: `log_blowup = 6, 19 queries, 16 PoW bits` — the
/// MEASURED size-optimal point at security parity with the v1 `create_config`
/// (conjectured capacity-bound: `19 × 6 + 16 = 130` bits, identical to v1's
/// `38 × 3 + 16`; proven/Johnson: `19 × 3 + 16 = 73`, identical to v1's
/// `38 × 1.5 + 16`). The full measured grid lives in
/// `tests/effect_vm_ir2_size_measure.rs::ir2_fri_grid` and
/// `docs/PROOF-ECONOMICS.md` §2c. The shape of the trade, in brief:
/// queries dominate IR-v2 proof size (the tables are 2³–2⁸ rows, so the prover-side
/// LDE cost of high blowup is milliseconds), so RAISING blowup and CUTTING queries
/// shrinks the wire — transfer: 194.1 KiB at (3, 38) → 120.4 KiB at (6, 19) — while
/// DROPPING blowup at parity (the (2, 57) / (1, 114) points) inflates it. The next
/// step up, (7, 17), buys only ~6.5 KiB for a further prover doubling: declined.
///
/// One config for every v2 descriptor: the whole-batch constraint-degree ceiling is 8
/// (`setFieldDynVmDescriptor2`'s pinned slot gate; everything else ≤ 7 — guarded by
/// `ir2_degree_budget`), far inside `log_blowup = 6`. Proofs are NOT interchangeable
/// across configs (FRI shape + Fiat–Shamir differ); the IR-v2 path is pre-cutover,
/// so this pins its wire shape.
fn ir2_config() -> DreggStarkConfig {
    // The Poseidon2 perm + MMCS + FRI params are identical on every call (the knobs are fixed),
    // so build the config ONCE per thread and hand back a clone (a few Arc bumps + small field
    // copies — far cheaper than re-deriving the perm/MMCS/FRI params per leaf). `thread_local`
    // sidesteps any `Sync` requirement on the config; the cached value is byte-identical to a
    // fresh `create_config_with_fri(6, 0, 3, 19, 16)` (same deterministic knobs).
    thread_local! {
        static IR2_CONFIG: DreggStarkConfig = create_config_with_fri(6, 0, 3, 19, 16);
    }
    IR2_CONFIG.with(|c| c.clone())
}

#[allow(clippy::too_many_arguments)]
fn prove_vm_descriptor2_inner<SC>(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    umem_boundary: &UMemBoundaryWitness,
    check: bool,
    config: &SC,
) -> Result<BatchProof<SC>, String>
where
    SC: StarkGenericConfig,
    Domain<SC>: PolynomialSpace<Val = P3BabyBear>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    SC::Challenge: p3_field::BasedVectorSpace<P3BabyBear>,
{
    let layout = check_descriptor2(desc)?;
    if base_trace.is_empty() {
        return Err("base trace must be non-empty".to_string());
    }
    if !base_trace.len().is_power_of_two() {
        return Err(format!(
            "base trace height {} must be a power of two",
            base_trace.len()
        ));
    }
    if base_trace[0].len() != desc.trace_width {
        return Err(format!(
            "base row width {} must equal descriptor trace_width {}",
            base_trace[0].len(),
            desc.trace_width
        ));
    }
    if public_inputs.len() != desc.public_input_count {
        return Err(format!(
            "public input count {} != descriptor public_input_count {}",
            public_inputs.len(),
            desc.public_input_count
        ));
    }

    let presence = Presence::of(desc, &layout);
    if !(presence.memory || mem_boundary.addrs.is_empty() && mem_boundary.init_vals.is_empty()) {
        return Err(
            "descriptor declares no mem ops but a memory boundary witness was supplied \
             (the memory tables are not committed for this descriptor)"
                .to_string(),
        );
    }
    if !(presence.map_ops || presence.map_absent || map_heaps.is_empty()) {
        return Err(
            "descriptor declares no map ops but witness heaps were supplied \
             (the map-ops/map-absent tables are not committed for this descriptor)"
                .to_string(),
        );
    }
    if !presence.umem && !umem_boundary.is_empty() {
        return Err(
            "descriptor declares no umem ops but a universal boundary witness was supplied \
             (the universal memory tables are not committed for this descriptor)"
                .to_string(),
        );
    }

    let traces = build_traces(
        desc,
        &layout,
        presence,
        base_trace,
        mem_boundary,
        map_heaps,
        umem_boundary,
        check,
    )?;
    let airs = instance_airs(desc, layout, presence);

    let mut matrices = vec![to_matrix(&traces.main)];
    for t in [
        &traces.chip,
        &traces.byte,
        &traces.memory,
        &traces.boundary,
        &traces.map_ops,
        &traces.map_absent,
        &traces.umemory,
        &traces.umem_boundary,
    ]
    .into_iter()
    .flatten()
    {
        matrices.push(to_matrix(t));
    }
    debug_assert_eq!(matrices.len(), airs.len());
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let mut pvs: Vec<Vec<P3BabyBear>> = vec![pis];
    pvs.resize(airs.len(), vec![]);

    let instances: Vec<StarkInstance<'_, SC, Ir2Air>> = airs
        .iter()
        .zip(matrices.iter())
        .zip(pvs.iter())
        .map(|((air, trace), pv)| StarkInstance {
            air,
            trace,
            public_values: pv.clone(),
        })
        .collect();

    let prover_data = ProverData::from_instances(config, &instances);
    let common = &prover_data.common;
    let proof = prove_batch(config, &instances, &prover_data);

    // Self-verify is a producer-side debug/test guard, NOT a soundness boundary: an honest
    // producer trusts its own witness (and the in-trace replay above, also gated by `check`,
    // already eagerly refuses a bad witness fail-closed), and the CONSUMER always re-verifies.
    // So the ~2-5ms full self-verify is pure redundancy on the trusted production prove path.
    // Gate it on `check && debug_assertions`: ON in debug/test builds (every `prove_vm_descriptor2*`
    // caller passes `check: true`, so the test path still self-verifies), OFF in release/production
    // (where the consumer's verify is the real check). This never disables the replay — that stays
    // under `check` alone.
    if check && cfg!(debug_assertions) {
        verify_batch(config, &airs, &proof, &pvs, common)
            .map_err(|e| format!("IR v2 batch self-verify failed: {e:?}"))?;
    }
    Ok(proof)
}

/// Clone a base trace and fill every row's chip lane columns from the descriptor's chip lookups
/// (Phase B-GATE). Honest producers fill the DIGEST (out0) chain but leave the 7 exposed lanes
/// 1..7 to this descriptor-driven weld, so no producer needs per-site lane knowledge. The
/// adversarial teeth use [`prove_vm_descriptor2_inner`] DIRECTLY (no lane fill), so a forged lane
/// stays forged and is REJECTED. Idempotent: re-deriving genuine lanes is a no-op.
fn trace_with_chip_lanes(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
) -> Vec<Vec<BabyBear>> {
    let mut t = base_trace.to_vec();
    for row in &mut t {
        // A producer may build rows at the pre-lane width; grow to the descriptor width so the
        // appended lane columns exist before filling (genuine producers fill out0; lanes ride here).
        if row.len() < desc.trace_width {
            row.resize(desc.trace_width, BabyBear::ZERO);
        }
        fill_chip_lanes(desc, row);
    }
    t
}

/// **`prove_vm_descriptor2`** — assemble + prove the multi-table batch STARK for a
/// graduated v2 descriptor over a base main trace.
///
/// * `base_trace` — the `trace_width`-column main rows (power-of-two height); digest
///   columns must already carry the genuine values (the Lean executor witness fills them).
/// * `mem_boundary` — the declared memory addresses + initial image (empty when the
///   descriptor declares no mem ops).
/// * `map_heaps` — one leaf set per pre-state heap the map ops open (empty when none).
///
/// The proof self-verifies before return. A witness violating any descriptor relation —
/// a tampered memory read, a forged map opening, an out-of-range limb, an amplified
/// submask — has no satisfying assembly (the pre-flight replay refuses it eagerly; with
/// the replay bypassed the batch prover/verifier rejects).
pub fn prove_vm_descriptor2(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> Result<BatchProof<DreggStarkConfig>, String> {
    prove_vm_descriptor2_inner(
        desc,
        &trace_with_chip_lanes(desc, base_trace),
        public_inputs,
        mem_boundary,
        map_heaps,
        &UMemBoundaryWitness::default(),
        true,
        &ir2_config(),
    )
}

/// **`prove_vm_descriptor2_umem`** — [`prove_vm_descriptor2`] for descriptors that declare
/// UNIVERSAL memory ops: takes the declared `(domain, key)` boundary + initial `Option` image
/// (`UMemBoundaryWitness`, Lean's `(uinit, ufin, uaddrs)` with `ufin` replayed). Everything
/// else is identical — and a umem-only descriptor commits NO chip table: the one-multiset
/// memory argument hashes nothing, intra-proof.
pub fn prove_vm_descriptor2_umem(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    umem_boundary: &UMemBoundaryWitness,
) -> Result<BatchProof<DreggStarkConfig>, String> {
    prove_vm_descriptor2_inner(
        desc,
        &trace_with_chip_lanes(desc, base_trace),
        public_inputs,
        mem_boundary,
        map_heaps,
        umem_boundary,
        true,
        &ir2_config(),
    )
}

/// Measurement-only variant of [`prove_vm_descriptor2`] under an explicit FRI config
/// (`tests/effect_vm_ir2_size_measure.rs` proves the SAME statement across the
/// `(log_blowup, num_queries)` grid). Proofs from non-default configs must never leak
/// onto the wire — the production IR-v2 config is `ir2_config` alone.
#[doc(hidden)]
pub fn prove_vm_descriptor2_with_config(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    config: &DreggStarkConfig,
) -> Result<BatchProof<DreggStarkConfig>, String> {
    prove_vm_descriptor2_inner(
        desc,
        &trace_with_chip_lanes(desc, base_trace),
        public_inputs,
        mem_boundary,
        map_heaps,
        &UMemBoundaryWitness::default(),
        true,
        config,
    )
}

/// **`prove_vm_descriptor2_for_config`** — the SIDESTEP prover: assemble + prove the IR-v2
/// multi-table batch under a CALLER-SUPPLIED `SC` config (rather than the fixed
/// `DreggStarkConfig`), so the rotated IVC leaf-wrap can mint a recursion-config-typed
/// `BatchProof<SC>` that the in-circuit verifier consumes directly (no cross-config type
/// mismatch). The caller passes a config whose FRI knobs match the production
/// `ir2_config` (log_blowup 6, 19 queries, 16 query-PoW) so the proof has the same FRI shape
/// the deployed descriptor proofs do — only the config TYPE differs (a newtype wrapper that
/// also impls `FriRecursionConfig`). Self-verifies before return.
pub fn prove_vm_descriptor2_for_config<SC>(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    umem_boundary: &UMemBoundaryWitness,
    config: &SC,
) -> Result<BatchProof<SC>, String>
where
    SC: StarkGenericConfig,
    Domain<SC>: PolynomialSpace<Val = P3BabyBear>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    SC::Challenge: p3_field::BasedVectorSpace<P3BabyBear>,
{
    prove_vm_descriptor2_inner(
        desc,
        &trace_with_chip_lanes(desc, base_trace),
        public_inputs,
        mem_boundary,
        map_heaps,
        umem_boundary,
        true,
        config,
    )
}

/// Verify-path `(airs, table_public_inputs, common)` triple result of
/// [`ir2_airs_and_common_for_config`] (extracted to satisfy `clippy::type_complexity`;
/// exact type-equivalent of the prior inline return type).
type Ir2AirsAndCommonResult<SC> = Result<
    (
        Vec<Ir2Air>,
        Vec<Vec<P3BabyBear>>,
        p3_batch_stark::CommonData<SC>,
    ),
    String,
>;

/// **`ir2_airs_and_common_for_config`** — the verify-path `(airs, table_public_inputs, common)`
/// triple for a proven descriptor under a caller-supplied `SC` config: the present-table
/// `Ir2Air` set, per-table public-input vectors (descriptor PIs on the main instance, empty
/// elsewhere), and the symbolic `CommonData<SC>`. Used by the rotated leaf-wrap
/// ([`ivc_turn_chain::prove_descriptor_leaf_rotated_with_config`](crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config))
/// to assemble a `RecursionInput::NativeBatchStark` leaf matching a recursion-config-typed
/// `BatchProof<SC>`. The `common` is built by the SAME
/// `ProverData::from_airs_and_degrees(config, ..)` path the inner prover/verifier use, so it
/// is the canonical common for this batch under `SC`.
pub fn ir2_airs_and_common_for_config<SC>(
    desc: &EffectVmDescriptor2,
    proof: &BatchProof<SC>,
    public_inputs: &[BabyBear],
    config: &SC,
) -> Ir2AirsAndCommonResult<SC>
where
    SC: StarkGenericConfig,
    Domain<SC>: PolynomialSpace<Val = P3BabyBear>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
{
    let layout = check_descriptor2(desc)?;
    let presence = Presence::of(desc, &layout);
    let airs = instance_airs(desc, layout, presence);
    if proof.degree_bits.len() != airs.len() {
        return Err(format!(
            "IR v2 proof carries {} instances but present-table set is {}",
            proof.degree_bits.len(),
            airs.len()
        ));
    }
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let mut table_public_inputs: Vec<Vec<P3BabyBear>> = vec![pis];
    table_public_inputs.resize(airs.len(), vec![]);
    let common = ProverData::from_airs_and_degrees(config, &airs, &proof.degree_bits).common;
    Ok((airs, table_public_inputs, common))
}

/// **`verify_vm_descriptor2`** — verify an IR v2 batch proof against the descriptor
/// (the AIRs are rebuilt from the descriptor alone; heights come from the proof).
pub fn verify_vm_descriptor2(
    desc: &EffectVmDescriptor2,
    proof: &BatchProof<DreggStarkConfig>,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    verify_vm_descriptor2_with_config(desc, proof, public_inputs, &ir2_config())
}

/// Measurement-only variant of [`verify_vm_descriptor2`] under an explicit FRI config
/// (see [`prove_vm_descriptor2_with_config`]). Generic over `SC` so it can verify a
/// recursion-config-typed batch (the SIDESTEP rotated leaf-wrap's inner proof).
#[doc(hidden)]
pub fn verify_vm_descriptor2_with_config<SC>(
    desc: &EffectVmDescriptor2,
    proof: &BatchProof<SC>,
    public_inputs: &[BabyBear],
    config: &SC,
) -> Result<(), String>
where
    SC: StarkGenericConfig,
    Domain<SC>: PolynomialSpace<Val = P3BabyBear>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    SC::Challenge: p3_field::BasedVectorSpace<P3BabyBear>,
{
    let layout = check_descriptor2(desc)?;
    let presence = Presence::of(desc, &layout);
    let airs = instance_airs(desc, layout, presence);
    if proof.degree_bits.len() != airs.len() {
        return Err(format!(
            "IR v2 proof carries {} instances but the descriptor's present-table set is {} \
             (descriptor-empty tables are not committed)",
            proof.degree_bits.len(),
            airs.len()
        ));
    }
    // The range table's HEIGHT is its CONTENT (the AIR pins `value = row index` and
    // nothing else): a prover committing a taller table would widen every limb's
    // admissible range to `[0, 2^height_bits)` and break every range check riding the
    // byte bus. Heights of the other tables are semantically free (their rows are
    // individually constrained and multiset/lookup-balanced; padding is gated), but
    // THIS one is pinned to the deployed `BYTE_TABLE_HEIGHT`.
    if presence.byte {
        let byte_idx = 1 + usize::from(presence.chip);
        if proof.degree_bits[byte_idx] != LIMB_BITS {
            return Err(format!(
                "range-table instance committed at 2^{} rows; the deployed table is \
                 2^{LIMB_BITS} (a taller table widens the limb range)",
                proof.degree_bits[byte_idx]
            ));
        }
    }
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let mut pvs: Vec<Vec<P3BabyBear>> = vec![pis];
    pvs.resize(airs.len(), vec![]);
    let common = ProverData::from_airs_and_degrees(config, &airs, &proof.degree_bits).common;
    verify_batch(config, &airs, proof, &pvs, &common)
        .map_err(|e| format!("IR v2 verification failed: {e:?}"))
}

// ============================================================================
// Tests (run on persvati with the batched validation, not by the build lane)
// ============================================================================

// The IR-v2 test suite proves AND verifies (it mints proofs via `prove_batch` / the
// trace assembly), so it is gated on `recursion` — the prover-free `verifier`-only
// build compiles the verify surface without these prover-coupled tests.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_many;

    /// **THE 8-FELT CHAIN ↔ CHIP BYTE-IDENTITY CROSS-CHECK** (Phase B-ROTATION). The plain
    /// `poseidon2::single_perm_compress` (the cell/turn/Lean-mirrored chain step) computes lanes
    /// `state[0..8]` of ONE wide arity-11 permutation. The in-circuit chip witness exposes the
    /// SAME 8 lanes as `[perm_lanes(seed)[0]` (the digest, out0)` ‖ chip_absorb_lanes(11, ins)`
    /// (lanes 1..7)]`. They MUST be byte-identical or the cell≡circuit differential cannot hold:
    /// a forged chip lane is UNSAT, so the commitment the proof binds equals the plain primitive's.
    #[test]
    fn single_perm_compress_equals_chip_wide_lanes() {
        let ins: Vec<BabyBear> = (1u32..=11).map(BabyBear::new).collect();
        let plain = crate::poseidon2::single_perm_compress(&ins);
        // The chip's arity-11 wide seed (identical to `chip_absorb_lanes`'s seeding).
        let mut seed = [BabyBear::ZERO; POSEIDON2_WIDTH];
        for i in 0..CHIP_WIDE_ARITY {
            seed[i] = ins[i];
        }
        let chip_lanes = perm_lanes(seed); // state[0..8] of the single permutation
        for i in 0..CHIP_OUT_LANES {
            assert_eq!(
                plain[i], chip_lanes[i],
                "single_perm_compress lane {i} must byte-equal the chip's perm_lanes"
            );
        }
        // And the lanes 1..7 the producer fill helper writes match plain[1..8].
        let absorb = chip_absorb_lanes(CHIP_WIDE_ARITY, &ins);
        for j in 0..(CHIP_OUT_LANES - 1) {
            assert_eq!(
                plain[j + 1],
                absorb[j],
                "chip_absorb_lanes lane {} mismatch",
                j + 1
            );
        }
    }

    /// Compute per-instance max constraint degrees (incl. LogUp legs) for a descriptor's
    /// committed table set — the quantity that drives the FRI `log_blowup` floor
    /// (`log_blowup >= log2_ceil(max_degree - 1)` per instance).
    fn instance_degrees(desc: &EffectVmDescriptor2) -> Vec<(String, usize)> {
        use p3_air::symbolic::AirLayout;
        use p3_batch_stark::symbolic::get_max_constraint_degree;
        use p3_field::extension::BinomialExtensionField;
        use p3_lookup::{LogUpGadget, Lookups};
        type Ef = BinomialExtensionField<P3BabyBear, 4>;

        let layout = check_descriptor2(desc).expect("descriptor checks");
        let presence = Presence::of(desc, &layout);
        let airs = instance_airs(desc, layout, presence);
        airs.iter()
            .map(|air| {
                let lookups = Lookups::<P3BabyBear>::from_air::<Ef, _>(air);
                let deg = get_max_constraint_degree::<P3BabyBear, Ef, _, _>(
                    air,
                    AirLayout::from_air::<P3BabyBear>(air),
                    &lookups,
                    &LogUpGadget::new(),
                );
                let name = match air {
                    Ir2Air::Main { .. } => "main",
                    Ir2Air::Chip => "chip",
                    Ir2Air::ByteTable => "byte",
                    Ir2Air::Memory => "memory",
                    Ir2Air::MemBoundary => "boundary",
                    Ir2Air::MapOps => "map_ops",
                    Ir2Air::MapAbsent => "map_absent",
                    Ir2Air::UMemory => "umemory",
                    Ir2Air::UMemBoundary => "umem_boundary",
                    Ir2Air::UMemBoundaryCohort => "umem_boundary_cohort",
                };
                (name.to_string(), deg)
            })
            .collect()
    }

    /// THE DEGREE-BUDGET TOOTH: per-table max constraint degrees (including the LogUp
    /// legs) of every graduated v2 descriptor + the full six-table gauntlet, frozen at
    /// their measured values. The whole-batch ceiling (8, `setFieldDynVmDescriptor2`'s
    /// pinned slot gate) sits far inside `ir2_config`'s `log_blowup = 6`; this tooth
    /// exists so a degree blowup (a new constraint or lookup leg compounding past the
    /// frozen budget) is caught symbolically, per table, with names — not as a deep
    /// prover panic on one descriptor later.
    ///
    /// Measured (2026-06-11): main ≤ 3 (setFieldDyn 8) · chip 7 (inline S-box) ·
    /// byte 3 · memory 3 · boundary 3 · map_ops 4 (in-tuple dir-mix legs) ·
    /// map_absent 4 (the same dir-mix legs, twice) · umemory 3 · umem_boundary 3.
    #[test]
    fn ir2_degree_budget() {
        let mut cohort: Vec<(String, EffectVmDescriptor2)> =
            crate::effect_vm_descriptors::V2_DESCRIPTORS
                .iter()
                .map(|(key, json, _)| {
                    (
                        key.to_string(),
                        parse_vm_descriptor2(json).expect("registry entry parses"),
                    )
                })
                .collect();
        cohort.push(("ir2-test-gauntlet".to_string(), test_desc()));
        cohort.push(("ir2-umem-gauntlet".to_string(), umem_desc()));
        cohort.push(("ir2-absent-gauntlet".to_string(), absent_desc()));
        for (key, desc) in &cohort {
            let degs = instance_degrees(desc);
            println!("{key} degrees: {degs:?}");
            for (table, deg) in degs {
                let budget = match table.as_str() {
                    // Lean-emitted, fingerprint-pinned constraint polynomials; the
                    // dynamic slot gate is the one descriptor above 3.
                    "main" if key == "setFieldDynVmDescriptor2" => 8,
                    "main" => 3,
                    // The inline x⁷ S-box between committed round-state blocks.
                    "chip" => 7,
                    // The in-tuple dir-mix lookup legs.
                    "map_ops" => 4,
                    // The bracketed-gap table: the in-tuple dir-mix fact legs (the
                    // comparator branches measure lower).
                    "map_absent" => 4,
                    // The one-multiset legs + the degree-3 insert-only tooth.
                    "umemory" => 3,
                    // The transition-gated lexicographic comparator legs.
                    "umem_boundary" => 3,
                    // The cohort single-row boundary: Blum legs + booleans + single-row tooth.
                    "umem_boundary_cohort" => 3,
                    // Value-pinned table + decomposition booleans + Blum legs.
                    "byte" | "memory" | "boundary" => 3,
                    other => panic!("{key}: unknown table {other}"),
                };
                assert!(
                    deg <= budget,
                    "{key}/{table}: constraint degree {deg} exceeds the frozen IR-v2 \
                     budget of {budget}"
                );
            }
        }
    }

    /// The Lean `#guard`-pinned demo-v2 golden (DescriptorIR2 §10): every v2 constraint
    /// kind + the five tables, byte-for-byte.
    const DEMO_V2: &str = "{\"name\":\"demo-v2\",\"ir\":2,\"trace_width\":2,\"public_input_count\":1,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":2,\"sem\":\"main\"},{\"id\":1,\"name\":\"poseidon2_chip\",\"arity\":17,\"sem\":\"poseidon2_chip\",\"params\":{\"field_modulus\":2013265921,\"d\":4,\"width\":16,\"sbox_degree\":7,\"sbox_registers\":1,\"half_full_rounds\":4,\"partial_rounds\":13,\"rate\":8,\"rc_source\":\"BABYBEAR_POSEIDON2_RC_16\",\"internal_diag_source\":\"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16\"}},{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30},{\"id\":3,\"name\":\"memory\",\"arity\":5,\"sem\":\"memory\"},{\"id\":4,\"name\":\"map_ops\",\"arity\":5,\"sem\":\"map_ops\"}],\"constraints\":[{\"t\":\"transition\",\"hi\":0,\"lo\":0},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"mem_op\",\"kind\":\"read\",\"guard\":{\"t\":\"const\",\"v\":1},\"addr\":{\"t\":\"var\",\"v\":0},\"value\":{\"t\":\"var\",\"v\":1},\"prev_value\":{\"t\":\"var\",\"v\":1},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"map_op\",\"op\":\"write\",\"guard\":{\"t\":\"const\",\"v\":1},\"root\":{\"t\":\"var\",\"v\":0},\"key\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"const\",\"v\":0},\"new_root\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}";

    /// The byte-pinned Lean golden parses, with every v2 element decoded.
    #[test]
    fn parses_lean_golden() {
        let d = parse_vm_descriptor2(DEMO_V2).expect("golden must parse");
        assert_eq!(d.name, "demo-v2");
        assert_eq!(d.trace_width, 2);
        assert_eq!(d.public_input_count, 1);
        assert_eq!(d.tables.len(), 5);
        assert_eq!(d.tables[2].sem, TableSem::Range { bits: 30 });
        assert_eq!(d.constraints.len(), 4);
        assert!(matches!(d.constraints[0], VmConstraint2::Base(_)));
        assert!(matches!(
            d.constraints[1],
            VmConstraint2::Lookup(LookupSpec {
                table: TID_RANGE,
                ..
            })
        ));
        assert!(matches!(
            d.constraints[2],
            VmConstraint2::MemOp(MemOpSpec {
                kind: MemKind::Read,
                ..
            })
        ));
        assert!(matches!(
            d.constraints[3],
            VmConstraint2::MapOp(MapOpSpec {
                op: MapKind::Write,
                ..
            })
        ));
    }

    /// A v1 wire string (no "ir") dispatches to the V1 arm unchanged.
    #[test]
    fn dispatches_v1() {
        let v1 = "{\"name\":\"t\",\"trace_width\":2,\"public_input_count\":0,\"constraints\":[{\"t\":\"transition\",\"hi\":0,\"lo\":0}],\"hash_sites\":[],\"ranges\":[]}";
        match parse_vm_descriptor_any(v1).expect("v1 must parse") {
            AnyVmDescriptor::V1(d) => assert_eq!(d.name, "t"),
            AnyVmDescriptor::V2(_) => panic!("v1 wire must dispatch V1"),
        }
    }

    /// Tampered chip params (wrong partial_rounds) are REFUSED at parse.
    #[test]
    fn refuses_tampered_chip_params() {
        let bad = DEMO_V2.replace("\"partial_rounds\":13", "\"partial_rounds\":12");
        assert!(parse_vm_descriptor2(&bad).is_err());
    }

    // ---- the end-to-end gauntlet descriptors ----

    /// Base layout for the test descriptor: cols 0 a, 1 b, 2 digest of hash[a,b],
    /// 3 a 30-bit balance wire, 4 mem addr, 5 mem value, 6 mem prev_value,
    /// 7 mem prev_serial, 8 mem guard, 9 map root, 10 map key, 11 map value,
    /// 12 map new_root, 13 map guard, 14 keep mask, 15 held mask.
    fn test_desc() -> EffectVmDescriptor2 {
        // Phase B-GATE: a single-output hash site emits the 17-wide chip tuple
        // `[2, a, b, 0×6, out0..out7]` but binds only out0 (= col `d`, the digest). Lanes
        // 1..7 are carried in cols 16..22 (witnessed = the genuine permutation lanes), so the
        // lookup matches the 17-wide chip row; the descriptor constrains only out0.
        let chip_tuple = |a: usize, b: usize, d: usize, lane1: usize| -> Vec<LeanExpr> {
            let mut t = vec![LeanExpr::Const(2), LeanExpr::Var(a), LeanExpr::Var(b)];
            for _ in 0..(CHIP_RATE - 2) {
                t.push(LeanExpr::Const(0));
            }
            t.push(LeanExpr::Var(d));
            for i in 0..(CHIP_OUT_LANES - 1) {
                t.push(LeanExpr::Var(lane1 + i));
            }
            t
        };
        EffectVmDescriptor2 {
            name: "ir2-test".to_string(),
            trace_width: 23,
            public_input_count: 0,
            tables: vec![TableDef2 {
                id: TID_RANGE,
                name: "range".to_string(),
                arity: 1,
                sem: TableSem::Range { bits: 30 },
            }],
            constraints: vec![
                VmConstraint2::Lookup(LookupSpec {
                    table: TID_P2,
                    tuple: chip_tuple(0, 1, 2, 16),
                }),
                VmConstraint2::Lookup(LookupSpec {
                    table: TID_RANGE,
                    tuple: vec![LeanExpr::Var(3)],
                }),
                VmConstraint2::MemOp(MemOpSpec {
                    guard: LeanExpr::Var(8),
                    addr: LeanExpr::Var(4),
                    value: LeanExpr::Var(5),
                    prev_value: LeanExpr::Var(6),
                    prev_serial: LeanExpr::Var(7),
                    kind: MemKind::Read,
                }),
                VmConstraint2::MapOp(MapOpSpec {
                    guard: LeanExpr::Var(13),
                    root: LeanExpr::Var(9),
                    key: LeanExpr::Var(10),
                    value: LeanExpr::Var(11),
                    new_root: LeanExpr::Var(12),
                    op: MapKind::Read,
                }),
                VmConstraint2::Lookup(LookupSpec {
                    table: TID_CUSTOM_SUBMASK,
                    tuple: vec![LeanExpr::Var(14), LeanExpr::Var(15)],
                }),
            ],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    fn test_heap() -> Vec<HeapLeaf> {
        vec![
            HeapLeaf {
                addr: BabyBear::new(100),
                value: BabyBear::new(77),
            },
            HeapLeaf {
                addr: BabyBear::new(200),
                value: BabyBear::new(88),
            },
        ]
    }

    fn test_base_row() -> Vec<BabyBear> {
        let a = BabyBear::new(11);
        let b = BabyBear::new(22);
        // The genuine 8 lanes of the arity-2 absorb hash[a, b]; lane0 == hash_many(&[a, b]).
        let lanes = perm_lanes(hash2_state_c(a, b));
        let digest = lanes[0];
        debug_assert_eq!(digest, hash_many(&[a, b]));
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        let mut row = vec![
            a,
            b,
            digest,
            BabyBear::new((1 << 30) - 1), // max in-range balance
            BabyBear::new(5),             // mem addr
            BabyBear::new(9),             // mem value (read returns init)
            BabyBear::new(9),             // mem prev_value
            BabyBear::ZERO,               // mem prev_serial (init)
            BabyBear::ZERO,               // mem guard (row 0 active only — set per row)
            root,                         // map root
            BabyBear::new(100),           // map key
            BabyBear::new(77),            // map value
            root,                         // map new_root (read preserves)
            BabyBear::ZERO,               // map guard (set per row)
            BabyBear::new(0b0101),        // keep ⊑ held
            BabyBear::new(0b0111),        // held
        ];
        // cols 16..22: the 7 exposed lanes 1..7 of the hash site (Phase B-GATE).
        row.extend_from_slice(&lanes[1..]);
        debug_assert_eq!(row.len(), 23);
        row
    }

    fn test_trace() -> Vec<Vec<BabyBear>> {
        // 4 rows; the mem/map ops fire on row 0 only.
        let mut rows = vec![test_base_row(); 4];
        rows[0][8] = BabyBear::ONE;
        rows[0][13] = BabyBear::ONE;
        // Rows 1..: prev_serial would still be 0 if the op fired again — guards are 0,
        // so the columns are inert there.
        rows
    }

    fn test_boundary() -> MemBoundaryWitness {
        MemBoundaryWitness {
            addrs: vec![5],
            init_vals: vec![9],
        }
    }

    /// THE acceptance gate: an honest multi-table witness (chip lookup + range lookup +
    /// memory read + map read + submask) proves and verifies through the real batch
    /// prover with LogUp.
    #[test]
    fn ir2_honest_witness_proves_and_verifies() {
        let desc = test_desc();
        let proof =
            prove_vm_descriptor2(&desc, &test_trace(), &[], &test_boundary(), &[test_heap()])
                .expect("honest IR v2 witness must prove");
        assert_eq!(
            proof.degree_bits.len(),
            6,
            "the full gauntlet uses every table: main + chip + byte + memory + boundary + map"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("honest IR v2 proof must verify");
    }

    /// FLAW-1 regression (the §2b size disease): a descriptor that uses only chip + range
    /// lookups (the graduated v1 cohort's shape — transfer et al.) commits ONLY
    /// main + chip + byte; the memory / boundary / map-ops tables are NOT in the batch,
    /// and the verifier agrees on the present-table set from the descriptor alone.
    #[test]
    fn ir2_elides_descriptor_empty_tables() {
        let mut desc = test_desc();
        desc.constraints
            .retain(|k| !matches!(k, VmConstraint2::MemOp(_) | VmConstraint2::MapOp(_)));
        let proof = prove_vm_descriptor2(
            &desc,
            &test_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
        )
        .expect("chip+range-only witness must prove");
        assert_eq!(
            proof.degree_bits.len(),
            3,
            "main + chip + byte only — descriptor-empty tables must be elided"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("elided-table proof must verify");

        // A stray witness for an elided table is a refusal, not a silent drop.
        assert!(
            prove_vm_descriptor2(&desc, &test_trace(), &[], &test_boundary(), &[]).is_err(),
            "a memory boundary witness without mem ops must refuse"
        );
        assert!(
            prove_vm_descriptor2(
                &desc,
                &test_trace(),
                &[],
                &MemBoundaryWitness::default(),
                &[test_heap()]
            )
            .is_err(),
            "witness heaps without map ops must refuse"
        );
    }

    /// A tampered memory READ (claims value 7 where the init image holds 9) must REFUSE:
    /// the pre-flight replay rejects it, and with the replay bypassed the in-circuit
    /// multiset argument has no balancing assembly (debug prover panics / proof fails
    /// verification).
    #[test]
    fn ir2_tampered_read_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        rows[0][5] = BabyBear::new(7); // value
        rows[0][6] = BabyBear::new(7); // prev_value (read discipline forces equality)
        // Pre-flight replay refuses.
        assert!(prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err());
        // In-circuit tooth: bypass the replay; the mem_check bus cannot balance.
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {} // debug prover panicked on the unbalanced bus — refused
            Ok(res) => assert!(
                res.is_err(),
                "tampered memory read produced an accepted proof — Blum tooth OPEN"
            ),
        }
    }

    /// A forged map READ (claims value 78 at key 100 where the committed heap holds 77)
    /// must refuse the same way.
    #[test]
    fn ir2_forged_map_opening_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        rows[0][11] = BabyBear::new(78);
        assert!(prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err());
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "forged map opening produced an accepted proof — opening tooth OPEN"
            ),
        }
    }

    // ---- THE DEPLOYED HEAP-WRITE SPLICE: a content-mismatched root is REJECTED (PHASE-E). ----

    /// The deployed heapWrite SPLICE column layout (`EffectVmEmitHeapRoot`, mirrored in the staged
    /// registry TSV row `heapWriteVmDescriptor2R24`): the `.write` MapOp on the heap root opens the
    /// committed root (col 65) at the recomputed address (col 102) for the written value (col 72) and
    /// FORCES the new root (col 87). This is the SAME op the deployed descriptor carries.
    const HW_ROOT_BEFORE: usize = 65;
    const HW_ROOT_AFTER: usize = 87;
    const HW_ADDR: usize = 102;
    const HW_VALUE: usize = 72;

    /// A minimal descriptor carrying EXACTLY the deployed heap-write splice `.write` MapOp (deployed
    /// columns), gated always-on — the row constraint the deployed `heapWriteVmDescriptor2R24` relies
    /// on, in isolation. Width 110 holds all referenced columns (max 102).
    fn hw_splice_desc() -> EffectVmDescriptor2 {
        EffectVmDescriptor2 {
            name: "hw-splice-deployed".to_string(),
            trace_width: 110,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Const(1),
                root: LeanExpr::Var(HW_ROOT_BEFORE),
                key: LeanExpr::Var(HW_ADDR),
                value: LeanExpr::Var(HW_VALUE),
                new_root: LeanExpr::Var(HW_ROOT_AFTER),
                op: MapKind::Write,
            })],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    /// The pre-write witness heap: an existing entry at `addr=100` whose value the write updates.
    fn hw_pre_heap() -> Vec<HeapLeaf> {
        vec![
            HeapLeaf {
                addr: BabyBear::new(100),
                value: BabyBear::new(7),
            },
            HeapLeaf {
                addr: BabyBear::new(250),
                value: BabyBear::new(9),
            },
        ]
    }

    /// One deployed-shape heap-write row: col 65 = the committed pre-root, col 102 = the addressed
    /// key (100), col 72 = the new value (42), col 87 = the GENUINE sorted-Merkle splice root (the
    /// update of addr 100 to value 42). 4 rows; the op fires on every row (constant-1 guard) so the
    /// trace carries the same genuine write each row.
    fn hw_splice_trace(new_root: BabyBear) -> Vec<Vec<BabyBear>> {
        let pre = CanonicalHeapTree::new(hw_pre_heap(), HEAP_TREE_DEPTH);
        let root = pre.root();
        let mut row = vec![BabyBear::ZERO; 110];
        row[HW_ROOT_BEFORE] = root;
        row[HW_ADDR] = BabyBear::new(100);
        row[HW_VALUE] = BabyBear::new(42);
        row[HW_ROOT_AFTER] = new_root;
        vec![row; 4]
    }

    /// THE GENUINE splice root: the update of addr 100 → value 42 over the pre-heap.
    fn hw_genuine_new_root() -> BabyBear {
        let pre = CanonicalHeapTree::new(hw_pre_heap(), HEAP_TREE_DEPTH);
        pre.update_witness(HeapLeaf {
            addr: BabyBear::new(100),
            value: BabyBear::new(42),
        })
        .expect("addr 100 is present")
        .new_root
    }

    /// **DEPLOYED-LEVEL ACCEPTANCE.** An honest deployed-shape heap-write whose published new root IS
    /// the genuine sorted-Merkle splice proves + verifies through the real batch prover (the MapOps
    /// AIR opens the OLD leaf against the committed root and recomputes the new root over the same
    /// sibling path).
    #[test]
    fn deployed_heap_splice_honest_proves_and_verifies() {
        let desc = hw_splice_desc();
        let trace = hw_splice_trace(hw_genuine_new_root());
        let proof = prove_vm_descriptor2(
            &desc,
            &trace,
            &[],
            &MemBoundaryWitness::default(),
            &[hw_pre_heap()],
        )
        .expect("honest deployed splice must prove");
        verify_vm_descriptor2(&desc, &proof, &[]).expect("honest deployed splice must verify");
    }

    /// **THE PHASE-E BAR — a content-MISMATCHED `heap_root` is REJECTED at the deployed level.** The
    /// prover advances the root to a value that does NOT match the genuine sorted-Merkle splice of the
    /// actual heap content (here: the genuine root + 1). The deployed MapOps AIR has no satisfying
    /// `update_witness` — the pre-flight replay refuses, and with the replay bypassed the in-circuit
    /// fact-bus recompute of the new root over the membership path cannot match the forged col 87.
    /// A content-mismatched root is now impossible. This is the deployed twin of the Lean
    /// `heapWrite_sat_rejects_wrong_splice_root`.
    #[test]
    fn deployed_heap_splice_rejects_content_mismatch() {
        let desc = hw_splice_desc();
        let forged = hw_genuine_new_root() + BabyBear::ONE; // NOT the genuine sorted-tree update
        assert_ne!(forged, hw_genuine_new_root());
        let trace = hw_splice_trace(forged);

        // Pre-flight replay refuses (the claimed new_root != the genuine sorted write).
        assert!(
            prove_vm_descriptor2(
                &desc,
                &trace,
                &[],
                &MemBoundaryWitness::default(),
                &[hw_pre_heap()],
            )
            .is_err(),
            "a content-mismatched heap_root must be refused by the deployed splice pre-flight"
        );

        // In-circuit tooth: bypass the replay; the MapOps fact-bus recompute cannot match col 87.
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &hw_splice_trace(forged),
                &[],
                &MemBoundaryWitness::default(),
                &[hw_pre_heap()],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {} // debug prover panicked on the unsatisfiable bus — refused
            Ok(res) => assert!(
                res.is_err(),
                "content-mismatched heap_root produced an accepted proof — the splice tooth is OPEN"
            ),
        }
    }

    /// **Phase B-GATE anti-laundering — DISTINCTNESS.** The 8 exposed chip output lanes are
    /// genuinely 8 distinct field elements (the final permutation state), NOT `[0]×8` and NOT
    /// eight copies of the digest. Also: flipping ANY one input bit changes ALL 8 lanes
    /// (full-input avalanche), so each lane depends on the whole input.
    #[test]
    fn ir2_chip_output_lanes_are_distinct() {
        for (a, b) in [(11u32, 22u32), (1, 0), (7, 7), (123456, 999999)] {
            let lanes = perm_lanes(hash2_state_c(BabyBear::new(a), BabyBear::new(b)));
            // Pairwise distinct.
            for i in 0..CHIP_OUT_LANES {
                for j in (i + 1)..CHIP_OUT_LANES {
                    assert_ne!(
                        lanes[i], lanes[j],
                        "lanes {i} and {j} collide for input ({a}, {b}) — chip output is not 8 distinct felts"
                    );
                }
            }
            // Avalanche: flipping input b's low bit changes every lane.
            let lanes2 = perm_lanes(hash2_state_c(BabyBear::new(a), BabyBear::new(b ^ 1)));
            for i in 0..CHIP_OUT_LANES {
                assert_ne!(
                    lanes[i], lanes2[i],
                    "lane {i} unchanged after a 1-bit input flip — lane does not depend on the full input"
                );
            }
        }
    }

    /// **Phase B-GATE anti-laundering — FORGED LANE IS UNSAT.** A single-output hash site carries
    /// the 7 exposed lanes 1..7 in its trace; the chip AIR equality-binds each to the genuine
    /// permutation lane. A witness with a FORGED lane (≠ the real lane) has NO matching chip row,
    /// so the LogUp lookup is unsatisfiable — the proof is REJECTED. This is what makes the new
    /// lane constraints REAL (out[i] is not a free column).
    #[test]
    fn ir2_forged_output_lane_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        // col 18 = the hash site's lane 3 (cols 16..22 hold lanes 1..7). Forge it.
        let real = rows[0][18];
        rows[0][18] = real + BabyBear::ONE;
        // A forged lane makes the LogUp lookup unsatisfiable: the prover either returns Err or
        // (in debug builds) the LogUp consistency checker panics. Either is a hard REJECTION.
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "forged output lane produced an accepted proof — the lane binding is OPEN"
            ),
        }
    }

    /// The seeded full-permutation state of a wide (arity-`CHIP_WIDE_ARITY`) absorb of `ins`
    /// (8-felt carrier ‖ 3 limbs) — the SAME seeding the AIR/witness-gen perform (in0..in10 read
    /// directly into state lanes 0..10). Used by the wide-arity anti-laundering teeth.
    fn wide_seed(ins: &[BabyBear; CHIP_WIDE_ARITY]) -> [BabyBear; POSEIDON2_WIDTH] {
        let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
        st[..CHIP_WIDE_ARITY].copy_from_slice(ins);
        st
    }

    /// A descriptor with a SINGLE wide (arity-11) chip lookup binding ALL 8 output lanes to
    /// columns. trace_width = 1 (arity tag) + 11 (inputs) + 8 (outputs) = 20; the lookup tuple's
    /// INPUT block is padded to CHIP_RATE (the in11..in15 slots are `Const 0` — the chip pins them
    /// 0 off arity 16, so they cost no column). The tuple is `[11, var1..var11, 0×5, var12..var19]`.
    fn wide_test_desc() -> EffectVmDescriptor2 {
        let mut tuple = vec![LeanExpr::Const(CHIP_WIDE_ARITY as i64)];
        for i in 0..CHIP_WIDE_ARITY {
            tuple.push(LeanExpr::Var(1 + i)); // in0..in10 at cols 1..11
        }
        for _ in CHIP_WIDE_ARITY..CHIP_RATE {
            tuple.push(LeanExpr::Const(0)); // in11..in15: padded to CHIP_RATE, no column
        }
        for i in 0..CHIP_OUT_LANES {
            tuple.push(LeanExpr::Var(1 + CHIP_WIDE_ARITY + i)); // out0..out7 at cols 12..19
        }
        EffectVmDescriptor2 {
            name: "ir2-wide-test".to_string(),
            trace_width: 1 + CHIP_WIDE_ARITY + CHIP_OUT_LANES,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::Lookup(LookupSpec {
                table: TID_P2,
                tuple,
            })],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    /// An honest wide-absorb trace: 11 distinct inputs, all 8 genuine output lanes filled.
    fn wide_test_trace() -> Vec<Vec<BabyBear>> {
        let ins: [BabyBear; CHIP_WIDE_ARITY] =
            core::array::from_fn(|i| BabyBear::new(100 + i as u32));
        let lanes = perm_lanes(wide_seed(&ins));
        // col 0 is unused (the constant arity tag lives in the lookup tuple, not a column);
        // cols 1..12 = in0..in10; cols 12..20 = out0..out7 (the genuine permutation lanes).
        let mut row = vec![BabyBear::ZERO];
        row.extend_from_slice(&ins);
        row.extend_from_slice(&lanes);
        debug_assert_eq!(row.len(), 1 + CHIP_WIDE_ARITY + CHIP_OUT_LANES);
        vec![row; 4]
    }

    /// **Phase B-GATE-INPUT anti-laundering — the wide arity GENUINELY carries an 8-felt value.**
    /// The honest arity-11 absorb proves; forging a CARRIER lane (input felt 8 — a lane BEYOND the
    /// old rate-7 cap, which the narrow chip could never seed) makes the lookup unsatisfiable. This
    /// is what proves the wide row seeds `state[0..11]` from the inputs (NOT zeros the carrier).
    #[test]
    fn ir2_wide_absorb_forged_carrier_lane_refuses() {
        let desc = wide_test_desc();
        // Honest first: a genuine wide absorb PROVES (the wide arity is admitted + satisfiable).
        // No mem/map ops in this descriptor → empty boundary + empty heap.
        let rows = wide_test_trace();
        if let Err(e) = prove_vm_descriptor2(&desc, &rows, &[], &MemBoundaryWitness::default(), &[])
        {
            panic!("honest arity-11 wide absorb must prove — the wide arity is unusable: {e}");
        }
        // Forge input felt 8 (col 9 = in8, a CARRIER felt past the old rate-7 cap). The lanes were
        // computed from the genuine in8; the perturbed in8 no longer matches any chip row.
        let mut bad = wide_test_trace();
        for r in &mut bad {
            r[1 + 8] += BabyBear::ONE; // in8 at col 9
        }
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &bad,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "wide absorb with a forged carrier lane (in8) was accepted — the wide carrier is NOT load-bearing"
            ),
        }
    }

    /// A descriptor with a SINGLE node8 (arity-16) chip lookup binding ALL 8 output lanes to
    /// columns. trace_width = 1 (arity tag) + 16 (L8‖R8 inputs) + 8 (outputs) = 25; the lookup
    /// tuple is `[16, var1..var16, var17..var24]`. The full-width Merkle-compression subject.
    fn node8_test_desc() -> EffectVmDescriptor2 {
        let mut tuple = vec![LeanExpr::Const(CHIP_NODE8_ARITY as i64)];
        for i in 0..CHIP_NODE8_ARITY {
            tuple.push(LeanExpr::Var(1 + i)); // in0..in15 at cols 1..17
        }
        for i in 0..CHIP_OUT_LANES {
            tuple.push(LeanExpr::Var(1 + CHIP_NODE8_ARITY + i)); // out0..out7 at cols 17..25
        }
        EffectVmDescriptor2 {
            name: "ir2-node8-test".to_string(),
            trace_width: 1 + CHIP_NODE8_ARITY + CHIP_OUT_LANES,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::Lookup(LookupSpec {
                table: TID_P2,
                tuple,
            })],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    /// An honest node8 trace: 16 distinct inputs (two 8-felt children), all 8 lanes filled from the
    /// genuine full-width permutation (`chip_absorb_all_lanes` at arity 16).
    fn node8_test_trace() -> Vec<Vec<BabyBear>> {
        let ins: [BabyBear; CHIP_NODE8_ARITY] =
            core::array::from_fn(|i| BabyBear::new(200 + i as u32));
        let lanes = chip_absorb_all_lanes(CHIP_NODE8_ARITY, &ins);
        let mut row = vec![BabyBear::ZERO]; // col 0 unused (arity is the const tuple[0])
        row.extend_from_slice(&ins);
        row.extend_from_slice(&lanes);
        debug_assert_eq!(row.len(), 1 + CHIP_NODE8_ARITY + CHIP_OUT_LANES);
        vec![row; 4]
    }

    /// **Phase H3 node8 — the full-width L8‖R8 compression is ADMITTED, SATISFIABLE, and binds all
    /// 16 input lanes.** The honest arity-16 absorb proves (the node8 arity is admitted by the
    /// membership gate); forging input felt 12 (a lane in the second 8-felt child, BEYOND the wide
    /// cap of 11 that no other arity can seed) makes the lookup unsatisfiable — proving the node8
    /// row genuinely seeds `state[0..16]` from both children. This is the chip-primitive tooth.
    #[test]
    fn ir2_node8_full_width_compression_binds_both_children() {
        let desc = node8_test_desc();
        let rows = node8_test_trace();
        if let Err(e) = prove_vm_descriptor2(&desc, &rows, &[], &MemBoundaryWitness::default(), &[])
        {
            panic!(
                "honest arity-16 node8 compression must prove — the node8 arity is unusable: {e}"
            );
        }
        // Forge input felt 12 (col 13 = in12, in the SECOND child, past the wide cap of 11). The
        // lanes were computed from the genuine in12; the perturbed in12 matches no chip row.
        let mut bad = node8_test_trace();
        for r in &mut bad {
            r[1 + 12] += BabyBear::ONE; // in12 at col 13
        }
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &bad,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "node8 with a forged second-child lane (in12) was accepted — the node8 child is NOT load-bearing"
            ),
        }
    }

    /// **Phase H3 node8 — both 8-felt children are load-bearing.** Perturbing ANY of the 16 input
    /// felts (across both children, including the tail lanes 11..15 that only node8 can seed)
    /// changes the digest AND every lane — the COLLISION FLOOR is now per-node at full 8-felt width.
    #[test]
    fn ir2_node8_both_children_load_bearing() {
        let base: [BabyBear; CHIP_NODE8_ARITY] =
            core::array::from_fn(|i| BabyBear::new(13 + i as u32));
        let lanes_base = chip_absorb_all_lanes(CHIP_NODE8_ARITY, &base);
        for j in 0..CHIP_NODE8_ARITY {
            let mut alt = base;
            alt[j] += BabyBear::ONE;
            let lanes_alt = chip_absorb_all_lanes(CHIP_NODE8_ARITY, &alt);
            assert_ne!(
                lanes_base[0], lanes_alt[0],
                "node8 digest unchanged after perturbing child felt {j} — that input lane is dead"
            );
            for i in 0..CHIP_OUT_LANES {
                assert_ne!(
                    lanes_base[i], lanes_alt[i],
                    "node8 lane {i} unchanged after perturbing child felt {j} — avalanche fails"
                );
            }
        }
    }

    /// **Phase B-GATE-INPUT anti-laundering — the carrier felts 7..10 are load-bearing.** Two wide
    /// absorbs differing ONLY in input felt 8 (a carrier felt the old rate-7 chip could not carry)
    /// produce DIFFERENT digests AND different lanes — the chip now genuinely carries an 8-felt
    /// value, the prerequisite for the 8-felt-chaining faithful commitment (Phase B-ROTATION).
    #[test]
    fn ir2_wide_absorb_carrier_felt_is_load_bearing() {
        let base: [BabyBear; CHIP_WIDE_ARITY] =
            core::array::from_fn(|i| BabyBear::new(7 + i as u32));
        let mut alt = base;
        alt[8] += BabyBear::ONE; // perturb carrier felt 8 only
        let lanes_base = perm_lanes(wide_seed(&base));
        let lanes_alt = perm_lanes(wide_seed(&alt));
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                lanes_base[i], lanes_alt[i],
                "lane {i} unchanged after perturbing carrier felt 8 — the wide chip does not depend on its 8-felt carrier"
            );
        }
        // Sanity: input felts 7..10 are all distinct seed positions (none aliased to a fixed lane).
        for j in 7..CHIP_WIDE_ARITY {
            let mut alt2 = base;
            alt2[j] += BabyBear::ONE;
            let lanes2 = perm_lanes(wide_seed(&alt2));
            assert_ne!(
                lanes_base[0], lanes2[0],
                "digest unchanged after perturbing carrier/limb felt {j} — that input lane is dead"
            );
        }
    }

    /// An amplified submask (keep ⋢ held) must refuse.
    #[test]
    fn ir2_amplified_submask_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        for row in &mut rows {
            row[14] = BabyBear::new(0b1000); // keep has a bit held lacks
        }
        assert!(prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err());
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                &UMemBoundaryWitness::default(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "amplified submask produced an accepted proof — non-amp tooth OPEN"
            ),
        }
    }

    /// A forged hash digest (column 2 ≠ hash[a,b]) must refuse: the chip table only
    /// carries genuine permutation rows, so the lookup cannot be served.
    #[test]
    fn ir2_forged_digest_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        for row in &mut rows {
            row[2] = row[2] + BabyBear::ONE;
        }
        // The chip table gathers the (forged) tuple and binds its own output column to
        // the REAL permutation — prover cannot satisfy both.
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()])
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "forged digest produced an accepted proof — chip tooth OPEN"
            ),
        }
    }

    /// A prover committing a TALLER range table (rows continuing past
    /// `BYTE_TABLE_HEIGHT` with multiplicity 0 — every transition and lookup
    /// constraint still satisfied, the LogUp legs still balanced) widens the
    /// admissible limb range. The RAW batch verifier accepts that assembly — the
    /// table height is prover-supplied `degree_bits` — so the explicit height pin in
    /// `verify_vm_descriptor2` is load-bearing; this asserts BOTH halves.
    #[test]
    fn ir2_oversized_byte_table_refuses() {
        let desc = test_desc();
        let layout = check_descriptor2(&desc).expect("gauntlet checks");
        let presence = Presence::of(&desc, &layout);
        let mut traces = build_traces(
            &desc,
            &layout,
            presence,
            &test_trace(),
            &test_boundary(),
            &[test_heap()],
            &UMemBoundaryWitness::default(),
            true,
        )
        .expect("honest traces");
        // The attack: a double-height range table, the increment chain continued and
        // every extra row carrying multiplicity 0.
        let byte = traces
            .byte
            .as_mut()
            .expect("gauntlet commits the range table");
        for b in BYTE_TABLE_HEIGHT..2 * BYTE_TABLE_HEIGHT {
            byte.push(vec![BabyBear::new(b as u32), BabyBear::ZERO]);
        }
        let airs = instance_airs(&desc, layout, presence);
        let mut matrices = vec![to_matrix(&traces.main)];
        for t in [
            &traces.chip,
            &traces.byte,
            &traces.memory,
            &traces.boundary,
            &traces.map_ops,
            &traces.map_absent,
            &traces.umemory,
            &traces.umem_boundary,
        ]
        .into_iter()
        .flatten()
        {
            matrices.push(to_matrix(t));
        }
        let pvs: Vec<Vec<P3BabyBear>> = vec![vec![]; airs.len()];
        let config = ir2_config();
        let instances: Vec<StarkInstance<'_, DreggStarkConfig, Ir2Air>> = airs
            .iter()
            .zip(matrices.iter())
            .zip(pvs.iter())
            .map(|((air, trace), pv)| StarkInstance {
                air,
                trace,
                public_values: pv.clone(),
            })
            .collect();
        let prover_data = ProverData::from_instances(&config, &instances);
        let proof = prove_batch(&config, &instances, &prover_data);
        verify_batch(&config, &airs, &proof, &pvs, &prover_data.common)
            .expect("the RAW batch verifier accepts the oversized table — the pin is the tooth");
        let err = verify_vm_descriptor2(&desc, &proof, &[])
            .expect_err("the IR-v2 verifier must refuse the oversized range table");
        assert!(
            err.contains("range-table instance committed"),
            "refusal must be the height pin, got: {err}"
        );
    }

    /// An out-of-range balance wire (2^30) must refuse (the tight top-limb bound).
    #[test]
    fn ir2_out_of_range_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        for row in &mut rows {
            row[3] = BabyBear::new(1 << 30);
        }
        assert!(prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err());
    }

    /// A map WRITE (in-place update at an existing key) proves: the new root is the
    /// genuine sorted write, chained so a later read against the NEW root sees it.
    #[test]
    fn ir2_map_write_update_proves() {
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        let w = tree
            .update_witness(HeapLeaf {
                addr: BabyBear::new(100),
                value: BabyBear::new(99),
            })
            .expect("key 100 present");
        let desc = EffectVmDescriptor2 {
            name: "ir2-map-write".to_string(),
            trace_width: 6,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                new_root: LeanExpr::Var(3),
                op: MapKind::Write,
            })],
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut rows = vec![
            vec![
                root,
                BabyBear::new(100),
                BabyBear::new(99),
                w.new_root,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ];
            4
        ];
        rows[0][5] = BabyBear::ONE;
        let proof = prove_vm_descriptor2(
            &desc,
            &rows,
            &[],
            &MemBoundaryWitness::default(),
            &[test_heap()],
        )
        .expect("map write update must prove");
        assert_eq!(
            proof.degree_bits.len(),
            3,
            "map-only descriptor commits main + chip + map-ops (chains ride the chip bus)"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("map write proof must verify");
    }

    /// A map INSERT at a FRESH key proves: the new root is the genuine sorted insert,
    /// and a later read against the NEW root sees the inserted value.
    #[test]
    fn ir2_map_insert_fresh_proves() {
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        let w = tree
            .insert_witness(HeapLeaf {
                addr: BabyBear::new(150),
                value: BabyBear::new(55),
            })
            .expect("key 150 fresh");
        let desc = EffectVmDescriptor2 {
            name: "ir2-map-insert".to_string(),
            trace_width: 6,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                new_root: LeanExpr::Var(3),
                op: MapKind::Insert,
            })],
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut rows = vec![
            vec![
                root,
                BabyBear::new(150),
                BabyBear::new(55),
                w.new_root,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ];
            4
        ];
        rows[0][5] = BabyBear::ONE;
        let proof = prove_vm_descriptor2(
            &desc,
            &rows,
            &[],
            &MemBoundaryWitness::default(),
            &[test_heap()],
        )
        .expect("map insert fresh must prove");
        assert_eq!(
            proof.degree_bits.len(),
            3,
            "map-only descriptor commits main + chip + map-ops (insert chains ride the chip bus)"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("map insert proof must verify");

        // A chained read against the post-insert root must open to the inserted value.
        let read_desc = EffectVmDescriptor2 {
            name: "ir2-map-insert-readback".to_string(),
            trace_width: 6,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                new_root: LeanExpr::Var(3),
                op: MapKind::Read,
            })],
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut read_rows = vec![
            vec![
                w.new_root,
                BabyBear::new(150),
                BabyBear::new(55),
                w.new_root,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ];
            4
        ];
        read_rows[0][5] = BabyBear::ONE;
        let read_heap: Vec<HeapLeaf> = {
            let mut leaves = test_heap();
            leaves.push(HeapLeaf {
                addr: BabyBear::new(150),
                value: BabyBear::new(55),
            });
            leaves
        };
        prove_vm_descriptor2(
            &read_desc,
            &read_rows,
            &[],
            &MemBoundaryWitness::default(),
            &[read_heap],
        )
        .expect("read-back against post-insert root must prove");
    }

    /// An `insert` claim for a key that is ALREADY present must refuse: the sorted
    /// tree has no authenticated gap for it, and the insert-witness builder fails.
    #[test]
    fn ir2_map_insert_present_refuses() {
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        let desc = EffectVmDescriptor2 {
            name: "ir2-map-insert-present".to_string(),
            trace_width: 6,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                new_root: LeanExpr::Var(3),
                op: MapKind::Insert,
            })],
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut rows = vec![
            vec![
                root,
                BabyBear::new(100), // key 100 is already present in test_heap
                BabyBear::new(99),
                root,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ];
            4
        ];
        rows[0][5] = BabyBear::ONE;
        assert!(
            prove_vm_descriptor2(
                &desc,
                &rows,
                &[],
                &MemBoundaryWitness::default(),
                &[test_heap()],
            )
            .is_err(),
            "insert at a present key must refuse"
        );
    }

    // ================================================================
    // The accumulator / recursive-proof-binding leg (proof_bind) — the Custom leg
    // ================================================================

    /// The Lean `#guard`-pinned demo-custom golden (DescriptorIR2 §10c): the `proof_bind` grammar
    /// (the row's commitment + vk columns, gated), byte-for-byte.
    const DEMO_CUSTOM: &str = "{\"name\":\"demo-custom\",\"ir\":2,\"trace_width\":3,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":3,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"proof_bind\",\"guard\":{\"t\":\"var\",\"v\":2},\"commit\":{\"t\":\"var\",\"v\":0},\"vk\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}";

    /// The byte-pinned Lean proof-bind golden parses, decoding the accumulator constraint kind.
    #[test]
    fn parses_lean_proof_bind_golden() {
        let d = parse_vm_descriptor2(DEMO_CUSTOM).expect("proof_bind golden must parse");
        assert_eq!(d.name, "demo-custom");
        assert_eq!(d.constraints.len(), 1);
        assert!(matches!(
            &d.constraints[0],
            VmConstraint2::ProofBind(ProofBindSpec {
                guard: LeanExpr::Var(2),
                commit: LeanExpr::Var(0),
                vk: LeanExpr::Var(1),
            })
        ));
        // The binding rides the recursion argument, not a committed table — the descriptor
        // checks (no table for the accumulator kind) and round-trips.
        check_descriptor2(&d).expect("proof_bind golden must check");
    }

    /// A v1 wire (no `"ir"` key) carrying a `proof_bind` is REFUSED — the accumulator kind is
    /// v2-only, like every other new kind.
    #[test]
    fn proof_bind_in_v1_wire_refuses() {
        let v1 = "{\"name\":\"x\",\"trace_width\":3,\"public_input_count\":0,\"constraints\":[{\"t\":\"proof_bind\",\"guard\":{\"t\":\"var\",\"v\":2},\"commit\":{\"t\":\"var\",\"v\":0},\"vk\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}";
        assert!(
            parse_vm_descriptor_any(v1).is_err(),
            "v1 wire carrying a proof_bind must refuse"
        );
    }

    /// The REAL Custom descriptor (the registry's `customVmDescriptor2`) parses, decodes the
    /// `proof_bind` op binding the `custom_proof_commitment` column (`PARAM_BASE+4 = 72`) and the
    /// `custom_program_vk_hash` column (`PARAM_BASE+0 = 68`), gated by the Custom selector (8).
    #[test]
    fn custom_registry_descriptor_binds_proof_columns() {
        let json = crate::effect_vm_descriptors::DREGG_EFFECTVM_CUSTOM_IR2_JSON;
        let d = parse_vm_descriptor2(json).expect("custom registry descriptor must parse");
        check_descriptor2(&d).expect("custom registry descriptor must check");
        // exactly one proof_bind op, binding the documented Custom param columns.
        let binds: Vec<&ProofBindSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::ProofBind(m) => Some(m),
                _ => None,
            })
            .collect();
        assert_eq!(binds.len(), 1, "Custom carries exactly one proof binding");
        let m = binds[0];
        // guard = sel::CUSTOM (8); commit = param CUSTOM_PROOF_COMMIT_BASE (PARAM_BASE+4 = 72);
        // vk = param CUSTOM_VK_HASH_BASE (PARAM_BASE+0 = 68). (PARAM_BASE = STATE_BEFORE_BASE +
        // state::SIZE = 54 + 14 = 68.)
        assert_eq!(
            m.guard,
            LeanExpr::Var(crate::effect_vm::columns::sel::CUSTOM)
        );
        assert_eq!(
            m.commit,
            LeanExpr::Var(
                crate::effect_vm::columns::PARAM_BASE
                    + crate::effect_vm::columns::param::CUSTOM_PROOF_COMMIT_BASE
            )
        );
        assert_eq!(
            m.vk,
            LeanExpr::Var(
                crate::effect_vm::columns::PARAM_BASE
                    + crate::effect_vm::columns::param::CUSTOM_VK_HASH_BASE
            )
        );
    }

    // -- The recursion-engine binding (the Rust analog of Lean `Satisfied2Custom` /
    //    `proofBind_determined`): a `proof_bind` op denotes "the row's commitment column IS the
    //    public-input commitment of a VERIFYING sub-proof, and its vk column that proof's program
    //    VK". The verification rides the recursion argument (`joint_turn_recursive.rs` leaf
    //    verifier), supplied here as a named, realizable engine — exactly as `RecursiveAggregation.
    //    EngineSound` names it. We model the engine + fire the anti-ghost BOTH ways. --

    /// A toy recursion engine: the proof carrier is `bool` (`true` = the honest sub-proof), the
    /// verifier accepts exactly `true`, a verifying proof exposes a fixed `(commit, vk)`. The
    /// REAL engine is plonky3's leaf verifier; this models the binding implication the descriptor
    /// rides.
    struct ToyEngine {
        commit: u32,
        vk: u32,
    }
    impl ToyEngine {
        fn verify(&self, p: bool) -> bool {
            p
        }
        fn pi_commit(&self, _p: bool) -> u32 {
            self.commit
        }
        fn vk_of(&self, _p: bool) -> u32 {
            self.vk
        }
        /// The named `EngineBinding`: the commitment determines the attested vk across verifying
        /// proofs (the in-circuit-verifier soundness — the one FRI obligation outside Lean).
        fn commit_determines_vk(&self) -> bool {
            true
        }
    }

    /// **HONEST Custom row VERIFIES.** A Custom row whose `custom_proof_commitment` / vk columns
    /// match a verifying sub-proof's exposed commitment / vk satisfies the proof binding — the row
    /// commits to a genuine verification. (The positive polarity of `proofBind_determined`.)
    #[test]
    fn proof_bind_honest_commitment_verifies() {
        let eng = ToyEngine {
            commit: 123,
            vk: 45,
        };
        let p = true; // the honest sub-proof
        assert!(eng.verify(p), "the honest sub-proof verifies");
        // the Custom row's commitment/vk columns carry the genuine exposed values.
        let row_commit = eng.pi_commit(p);
        let row_vk = eng.vk_of(p);
        // the binding holds: some verifying proof exposes exactly (row_commit, row_vk).
        assert_eq!(row_commit, 123);
        assert_eq!(row_vk, 45);
    }

    /// **FORGED Custom row REJECTS (the anti-ghost).** Under the named engine binding, a Custom
    /// row that claims a `custom_proof_commitment` SOME verifying sub-proof exposes but pairs it
    /// with the WRONG vk has NO satisfying binding: the commitment DETERMINES the vk, so a forged
    /// vk is excluded. The recursion analog of `proofBind_determined`: the binding cannot lie.
    #[test]
    fn proof_bind_forged_commitment_refuses() {
        let eng = ToyEngine {
            commit: 123,
            vk: 45,
        };
        assert!(eng.commit_determines_vk(), "the engine binding holds");
        // A forger claims the genuine commitment (123) but a DIFFERENT vk (99) than any verifying
        // sub-proof exposes (45). For ANY verifying proof q with pi_commit(q) = 123, the binding
        // forces vk_of(q) = 45 ≠ 99 — so no satisfying `Satisfied2Custom` exists.
        let forged_vk: u32 = 99;
        let q = true; // any verifying sub-proof at this commitment
        assert!(eng.verify(q));
        assert_eq!(eng.pi_commit(q), 123, "the forger's claimed commitment");
        assert_ne!(
            eng.vk_of(q),
            forged_vk,
            "the genuine vk (45) the binding forces differs from the forged vk (99) — REJECT"
        );
        // Equivalently: a forger claiming a commitment NO verifying sub-proof exposes also fails
        // (no `p` with verify(p) AND pi_commit(p) = forged) — the boundTo existential is empty.
        let unbacked_commit: u32 = 777;
        let exists_backing = [true, false]
            .iter()
            .any(|&p| eng.verify(p) && eng.pi_commit(p) == unbacked_commit);
        assert!(
            !exists_backing,
            "no verifying sub-proof exposes the unbacked commitment — the binding is UNSAT"
        );
    }

    // ================================================================
    // The UNIVERSAL memory leg (umem_op) + the absent (sorted-gap) leg
    // ================================================================

    /// The Lean `#guard`-pinned demo-umem golden (DescriptorIR2 §10b): the `umem_op` grammar
    /// + the `umemory`/`umem_boundary` table sems, byte-for-byte.
    const DEMO_UMEM: &str = "{\"name\":\"demo-umem\",\"ir\":2,\"trace_width\":4,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":4,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":3,\"guard\":{\"t\":\"const\",\"v\":1},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"const\",\"v\":1},\"value\":{\"t\":\"const\",\"v\":1},\"prev_present\":{\"t\":\"const\",\"v\":0},\"prev_value\":{\"t\":\"const\",\"v\":0},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"umem_op\",\"kind\":\"read\",\"domain\":3,\"guard\":{\"t\":\"const\",\"v\":1},\"key\":{\"t\":\"var\",\"v\":1},\"present\":{\"t\":\"const\",\"v\":0},\"value\":{\"t\":\"const\",\"v\":0},\"prev_present\":{\"t\":\"const\",\"v\":0},\"prev_value\":{\"t\":\"const\",\"v\":0},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":0,\"guard\":{\"t\":\"const\",\"v\":1},\"key\":{\"t\":\"var\",\"v\":2},\"present\":{\"t\":\"const\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":3},\"prev_present\":{\"t\":\"const\",\"v\":0},\"prev_value\":{\"t\":\"const\",\"v\":0},\"prev_serial\":{\"t\":\"const\",\"v\":0}}],\"hash_sites\":[],\"ranges\":[]}";

    /// The byte-pinned Lean umem golden parses, with every element decoded.
    #[test]
    fn parses_lean_umem_golden() {
        let d = parse_vm_descriptor2(DEMO_UMEM).expect("umem golden must parse");
        assert_eq!(d.name, "demo-umem");
        assert_eq!(d.tables.len(), 3);
        assert_eq!(d.tables[1].sem, TableSem::UMemory);
        assert_eq!(d.tables[1].id, TID_UMEMORY);
        assert_eq!(d.tables[2].sem, TableSem::UMemBoundary);
        assert_eq!(d.tables[2].id, TID_UMEM_BOUNDARY);
        assert_eq!(d.constraints.len(), 3);
        assert!(matches!(
            &d.constraints[0],
            VmConstraint2::UMemOp(UMemOpSpec {
                kind: MemKind::Write,
                domain: NULLIFIER_DOMAIN,
                ..
            })
        ));
        assert!(matches!(
            &d.constraints[1],
            VmConstraint2::UMemOp(UMemOpSpec {
                kind: MemKind::Read,
                domain: NULLIFIER_DOMAIN,
                ..
            })
        ));
        assert!(matches!(
            &d.constraints[2],
            VmConstraint2::UMemOp(UMemOpSpec {
                kind: MemKind::Write,
                domain: 0,
                ..
            })
        ));
        check_descriptor2(&d).expect("umem golden must check");
    }

    /// A HUGE (hash-image-scale) nullifier key: `p − 2` (hi4 = 14, lo27 = 2^27 − 1) — the
    /// canonical-decomposition machinery must order it, which the 30-bit flat regime cannot.
    const BIG_KEY: u32 = BABYBEAR_P - 2;

    /// Base layout: col 0 = inserted nullifier key, 1 = fresh-checked nullifier key,
    /// 2 = register key, 3 = register value, 4 = the op guard.
    fn umem_desc() -> EffectVmDescriptor2 {
        let op = |domain: u32,
                  key: LeanExpr,
                  present: LeanExpr,
                  value: LeanExpr,
                  prev_present: LeanExpr,
                  prev_value: LeanExpr,
                  prev_serial: LeanExpr,
                  kind: MemKind| {
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(4),
                domain,
                key,
                present,
                value,
                prev_present,
                prev_value,
                prev_serial,
                kind,
            })
        };
        EffectVmDescriptor2 {
            name: "ir2-umem-test".to_string(),
            trace_width: 5,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![
                // The nullifier INSERT (serial 1).
                op(
                    NULLIFIER_DOMAIN,
                    LeanExpr::Var(0),
                    LeanExpr::Const(1),
                    LeanExpr::Const(1),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    MemKind::Write,
                ),
                // THE FRESHNESS READ (serial 2): one row, present = 0 — `none`. No Merkle
                // path, no gap opening, no hashing (`nullifier_fresh_sound`).
                op(
                    NULLIFIER_DOMAIN,
                    LeanExpr::Var(1),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    MemKind::Read,
                ),
                // A register write (serial 3): a SECOND domain in the SAME table — the
                // one-multiset coverage (`universal_memory_sound`).
                op(
                    0,
                    LeanExpr::Var(2),
                    LeanExpr::Const(1),
                    LeanExpr::Var(3),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    LeanExpr::Const(0),
                    MemKind::Write,
                ),
            ],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    fn umem_trace() -> Vec<Vec<BabyBear>> {
        let row = vec![
            BabyBear::new(7),       // inserted nullifier
            BabyBear::new(BIG_KEY), // fresh-checked nullifier (full-felt key)
            BabyBear::new(0),       // register key
            BabyBear::new(42),      // register value
            BabyBear::ZERO,         // guard (row 0 only)
        ];
        let mut rows = vec![row; 4];
        rows[0][4] = BabyBear::ONE;
        rows
    }

    fn umem_test_boundary() -> UMemBoundaryWitness {
        UMemBoundaryWitness {
            addrs: vec![
                (0, BabyBear::new(0)),
                (NULLIFIER_DOMAIN, BabyBear::new(7)),
                (NULLIFIER_DOMAIN, BabyBear::new(BIG_KEY)),
            ],
            init_vals: vec![None, None, None],
        }
    }

    /// THE UNIVERSAL-MEMORY GATE: nullifier insert + Merkle-path-free freshness read +
    /// cross-domain register write, ONE multiset, proven and verified — with NO chip table
    /// committed (the memory argument hashes nothing; `docs/UNIVERSAL-MEMORY.md`'s point,
    /// measured).
    #[test]
    fn ir2_umem_honest_proves_and_verifies_no_chip() {
        let desc = umem_desc();
        let proof = prove_vm_descriptor2_umem(
            &desc,
            &umem_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &umem_test_boundary(),
        )
        .expect("honest umem witness must prove");
        assert_eq!(
            proof.degree_bits.len(),
            4,
            "umem descriptor commits main + byte + umemory + umem-boundary — and NO chip \
             table (zero intra-proof hashing)"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("umem proof must verify");
    }

    /// PRESENCE refusal: a universal boundary witness without umem ops must refuse (the
    /// tables are not committed), and a umem descriptor's proof must carry the tables.
    #[test]
    fn ir2_umem_presence_teeth() {
        let r = prove_vm_descriptor2_umem(
            &test_desc(),
            &test_trace(),
            &[],
            &test_boundary(),
            &[test_heap()],
            &umem_test_boundary(),
        );
        assert!(r.is_err(), "stray umem boundary witness must refuse");
    }

    /// A single-domain, single-address COHORT descriptor: one `umemOp` write, declaring the
    /// `umem_boundary_cohort` table sem (the width-9 single-row boundary). The deployed welded
    /// leg's shape (`weld_umem_into_rotated_descriptor_cohort`) in miniature.
    fn umem_cohort_desc() -> EffectVmDescriptor2 {
        EffectVmDescriptor2 {
            name: "ir2-umem-cohort-test".to_string(),
            trace_width: 3,
            public_input_count: 0,
            tables: vec![
                TableDef2 {
                    id: TID_UMEMORY,
                    name: "umemory".to_string(),
                    arity: 8,
                    sem: TableSem::UMemory,
                },
                TableDef2 {
                    id: TID_UMEM_BOUNDARY,
                    name: "umem_boundary_cohort".to_string(),
                    arity: 7,
                    sem: TableSem::UMemBoundaryCohort,
                },
            ],
            constraints: vec![VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(2),
                domain: 0,
                key: LeanExpr::Var(0),
                present: LeanExpr::Const(1),
                value: LeanExpr::Var(1),
                prev_present: LeanExpr::Const(0),
                prev_value: LeanExpr::Const(0),
                prev_serial: LeanExpr::Const(0),
                kind: MemKind::Write,
            })],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    fn umem_cohort_trace() -> Vec<Vec<BabyBear>> {
        // col0 = key, col1 = value, col2 = guard (row 0 only — one declared address).
        let row = vec![BabyBear::new(5), BabyBear::new(42), BabyBear::ZERO];
        let mut rows = vec![row; 4];
        rows[0][2] = BabyBear::ONE;
        rows
    }

    fn umem_cohort_boundary() -> UMemBoundaryWitness {
        UMemBoundaryWitness {
            addrs: vec![(0, BabyBear::new(5))],
            init_vals: vec![None],
        }
    }

    /// THE COHORT PERF LEVER: a single-address universal boundary proves through the width-9
    /// specialized AIR (`Ir2Air::UMemBoundaryCohort`), NOT the width-38 general one — the
    /// inter-row `Nodup` comparator + key decomposition (29 columns) are dropped, sound because
    /// `Nodup` of one address is `nodup_singleton` (Lean `universal_memory_sound_single`).
    #[test]
    fn ir2_umem_cohort_proves_through_specialized_air() {
        // Width: the dropped comparator is real — the cohort boundary is a quarter of the columns.
        assert_eq!(UBC_WIDTH, 9);
        assert!(
            UBC_WIDTH * 4 <= UB_WIDTH,
            "cohort boundary {UBC_WIDTH} is not ≤ a quarter of the general {UB_WIDTH}"
        );

        let desc = umem_cohort_desc();
        let layout = check_descriptor2(&desc).expect("cohort desc checks");
        let presence = Presence::of(&desc, &layout);
        assert!(
            presence.umem_cohort,
            "the cohort table sem must select the specialized boundary"
        );
        let airs = instance_airs(&desc, layout, presence);
        assert!(
            airs.iter().any(|a| matches!(a, Ir2Air::UMemBoundaryCohort)),
            "the cohort boundary AIR must be in the instance set"
        );
        assert!(
            !airs.iter().any(|a| matches!(a, Ir2Air::UMemBoundary)),
            "the general boundary AIR must NOT be committed for a cohort descriptor"
        );

        let proof = prove_vm_descriptor2_umem(
            &desc,
            &umem_cohort_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &umem_cohort_boundary(),
        )
        .expect("honest single-address cohort must prove through the specialized AIR");
        assert_eq!(
            proof.degree_bits.len(),
            4,
            "cohort commits main + byte + umemory + umem_boundary_cohort (no chip)"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("cohort proof must verify");
    }

    /// THE SINGLE-ROW TOOTH: the cohort boundary carries AT MOST ONE address. A two-address
    /// witness is REFUSED (at assembly, and the in-circuit `next.is_real = 0` tooth would refuse
    /// it too) — the specialization can never be used to skip the `Nodup` comparator for a
    /// genuinely multi-row boundary.
    #[test]
    fn ir2_umem_cohort_refuses_two_addresses() {
        let desc = umem_cohort_desc();
        let two = UMemBoundaryWitness {
            addrs: vec![(0, BabyBear::new(5)), (0, BabyBear::new(6))],
            init_vals: vec![None, None],
        };
        let r = prove_vm_descriptor2_umem(
            &desc,
            &umem_cohort_trace(),
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &two,
        );
        assert!(
            r.is_err(),
            "the cohort single-row boundary must refuse a >1-address witness"
        );
    }

    /// THE DOUBLE-SPEND TOOTH: insert nullifier 7, then claim it is STILL FRESH (the read's
    /// key re-pointed at the inserted key). Pre-flight replay refuses; with the replay
    /// bypassed the one-multiset argument has no balancing assembly.
    #[test]
    fn ir2_umem_double_spend_refuses() {
        let desc = umem_desc();
        let mut rows = umem_trace();
        rows[0][1] = BabyBear::new(7); // "fresh" read of the JUST-INSERTED nullifier
        let boundary = UMemBoundaryWitness {
            addrs: vec![(0, BabyBear::new(0)), (NULLIFIER_DOMAIN, BabyBear::new(7))],
            init_vals: vec![None, None],
        };
        assert!(
            prove_vm_descriptor2_umem(
                &desc,
                &rows,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &boundary,
            )
            .is_err(),
            "pre-flight replay must refuse the double spend"
        );
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &boundary,
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "intra-proof double spend produced an accepted proof — freshness tooth OPEN"
            ),
        }
    }

    /// THE CROSS-DOMAIN STEAL TOOTH: a caps-domain read claims the REGISTER write's cell
    /// (same key 0, value 42, serial 3 — only the domain tag differs). The tag is its own
    /// bus coordinate, so the claimed entry cancels nothing: unbalanced, refused. (The Lean
    /// twin: `UniversalMemory.lean` §6 negative polarity 1.)
    #[test]
    fn ir2_umem_cross_domain_steal_refuses() {
        let mut desc = umem_desc();
        desc.constraints.push(VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(4),
            domain: 2, // caps — stealing the registers-domain (0) tuple
            key: LeanExpr::Var(2),
            present: LeanExpr::Const(1),
            value: LeanExpr::Var(3),
            prev_present: LeanExpr::Const(1),
            prev_value: LeanExpr::Var(3),
            prev_serial: LeanExpr::Const(3),
            kind: MemKind::Read,
        }));
        let mut boundary = umem_test_boundary();
        boundary.addrs.insert(1, (2, BabyBear::new(0)));
        boundary.init_vals.insert(1, None);
        assert!(
            prove_vm_descriptor2_umem(
                &desc,
                &umem_trace(),
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &boundary,
            )
            .is_err(),
            "pre-flight replay must refuse the cross-domain steal"
        );
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &umem_trace(),
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &boundary,
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "cross-domain tuple steal produced an accepted proof — domain-tag tooth OPEN"
            ),
        }
    }

    /// THE INSERT-ONLY TOOTH: a nullifier-domain write installing `none`. The statically
    /// violating shape (present = const 0) is refused at check; the DYNAMIC shape (present
    /// rides a column that evaluates to 0) is refused by the in-circuit
    /// `is_null·kind·(1−present)` row constraint.
    #[test]
    fn ir2_umem_insert_only_refuses_unspend() {
        // Static shape: refused at descriptor check.
        let mut desc = umem_desc();
        desc.constraints[0] = VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(4),
            domain: NULLIFIER_DOMAIN,
            key: LeanExpr::Var(0),
            present: LeanExpr::Const(0),
            value: LeanExpr::Const(0),
            prev_present: LeanExpr::Const(0),
            prev_value: LeanExpr::Const(0),
            prev_serial: LeanExpr::Const(0),
            kind: MemKind::Write,
        });
        let err = check_descriptor2(&desc).expect_err("static un-spend must refuse");
        assert!(err.contains("insert-only"), "got: {err}");

        // Dynamic shape: present rides col 3 (set to 0); value 0 keeps the cell canonical.
        let mut desc2 = umem_desc();
        desc2.constraints[0] = VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(4),
            domain: NULLIFIER_DOMAIN,
            key: LeanExpr::Var(0),
            present: LeanExpr::Var(3),
            value: LeanExpr::Const(0),
            prev_present: LeanExpr::Const(0),
            prev_value: LeanExpr::Const(0),
            prev_serial: LeanExpr::Const(0),
            kind: MemKind::Write,
        });
        let mut rows = umem_trace();
        for row in &mut rows {
            row[3] = BabyBear::ZERO; // the dynamic present bit evaluates to 0
            row[1] = BabyBear::new(9); // make the freshness read consistent (key 9 untouched)
        }
        let boundary = UMemBoundaryWitness {
            addrs: vec![
                (0, BabyBear::new(0)),
                (NULLIFIER_DOMAIN, BabyBear::new(7)),
                (NULLIFIER_DOMAIN, BabyBear::new(9)),
            ],
            init_vals: vec![None, None, None],
        };
        assert!(
            prove_vm_descriptor2_umem(
                &desc2,
                &rows,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &boundary,
            )
            .is_err(),
            "pre-flight must refuse the dynamic un-spend"
        );
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc2,
                &rows,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &boundary,
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "nullifier un-spend produced an accepted proof — insert-only tooth OPEN"
            ),
        }
    }

    /// A tampered umem READ (claims register value 43 where the write installed 42) must
    /// refuse: replay pre-flight, and the multiset legs with the replay bypassed.
    #[test]
    fn ir2_umem_tampered_read_refuses() {
        let mut desc = umem_desc();
        // A read-back of the register cell, claiming the write's cell as prior.
        desc.constraints.push(VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(4),
            domain: 0,
            key: LeanExpr::Var(2),
            present: LeanExpr::Const(1),
            value: LeanExpr::Const(43), // the LIE: the write installed 42
            prev_present: LeanExpr::Const(1),
            prev_value: LeanExpr::Const(43),
            prev_serial: LeanExpr::Const(3),
            kind: MemKind::Read,
        }));
        assert!(
            prove_vm_descriptor2_umem(
                &desc,
                &umem_trace(),
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &umem_test_boundary(),
            )
            .is_err()
        );
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &umem_trace(),
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &umem_test_boundary(),
                false,
                &ir2_config(),
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "tampered umem read produced an accepted proof — Blum tooth OPEN"
            ),
        }
    }

    // ---- the `absent` (bracketed sorted-gap) realization ----

    /// Base layout: col 0 = root, 1 = key, 2 = new_root, 3 = guard.
    fn absent_desc() -> EffectVmDescriptor2 {
        EffectVmDescriptor2 {
            name: "ir2-absent-test".to_string(),
            trace_width: 4,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(3),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Const(0),
                new_root: LeanExpr::Var(2),
                op: MapKind::Absent,
            })],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    fn absent_trace(key: u32) -> Vec<Vec<BabyBear>> {
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        let mut rows = vec![vec![root, BabyBear::new(key), root, BabyBear::ZERO]; 4];
        rows[0][3] = BabyBear::ONE;
        rows
    }

    /// THE NON-MEMBERSHIP GATE: an honest `absent` op (key 150, bracketed by the committed
    /// leaves 100 and 200) proves and verifies — the realization of `opensTo … none` /
    /// `opensTo_none_of_gap`, the boundary leg of `nullifier_fresh_binds_root`.
    #[test]
    fn ir2_absent_honest_proves_and_verifies() {
        let desc = absent_desc();
        let proof = prove_vm_descriptor2(
            &desc,
            &absent_trace(150),
            &[],
            &MemBoundaryWitness::default(),
            &[test_heap()],
        )
        .expect("honest absent witness must prove");
        assert_eq!(
            proof.degree_bits.len(),
            4,
            "absent-only descriptor commits main + chip + byte + map-absent (no map-ops)"
        );
        verify_vm_descriptor2(&desc, &proof, &[]).expect("absent proof must verify");
    }

    /// An `absent` claim for a PRESENT key (100 — a committed leaf) must refuse: no
    /// bracketing witness exists, and a forged one violates the gap comparators.
    #[test]
    fn ir2_absent_of_present_key_refuses() {
        let desc = absent_desc();
        assert!(
            prove_vm_descriptor2(
                &desc,
                &absent_trace(100),
                &[],
                &MemBoundaryWitness::default(),
                &[test_heap()],
            )
            .is_err(),
            "absent of a present key must refuse"
        );
    }

    /// THE FORGED-BRACKET TOOTH, in-circuit: build the HONEST absent assembly for key 150,
    /// then tamper the claim to the PRESENT key 100 in BOTH the main row and the map-absent
    /// row (so the map-log multiset still balances — the strongest forgery shape). The raw
    /// batch prover must have no satisfying assembly: the key's canonical decomposition and
    /// the `lo < key` comparator (100 < 100) refuse the re-keyed bracketing witness.
    #[test]
    fn ir2_absent_forged_bracket_refuses() {
        let desc = absent_desc();
        let layout = check_descriptor2(&desc).expect("absent gauntlet checks");
        let presence = Presence::of(&desc, &layout);
        let mut traces = build_traces(
            &desc,
            &layout,
            presence,
            &absent_trace(150),
            &MemBoundaryWitness::default(),
            &[test_heap()],
            &UMemBoundaryWitness::default(),
            true,
        )
        .expect("honest absent traces");
        traces.main[0][1] = BabyBear::new(100); // the forged claim, main side
        traces.map_absent.as_mut().expect("absent table present")[0][MA_KEY] = BabyBear::new(100); // …and table side (multiset balanced)
        let airs = instance_airs(&desc, layout, presence);
        let mut matrices = vec![to_matrix(&traces.main)];
        for t in [
            &traces.chip,
            &traces.byte,
            &traces.memory,
            &traces.boundary,
            &traces.map_ops,
            &traces.map_absent,
            &traces.umemory,
            &traces.umem_boundary,
        ]
        .into_iter()
        .flatten()
        {
            matrices.push(to_matrix(t));
        }
        let pvs: Vec<Vec<P3BabyBear>> = vec![vec![]; airs.len()];
        let config = ir2_config();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let instances: Vec<StarkInstance<'_, DreggStarkConfig, Ir2Air>> = airs
                .iter()
                .zip(matrices.iter())
                .zip(pvs.iter())
                .map(|((air, trace), pv)| StarkInstance {
                    air,
                    trace,
                    public_values: pv.clone(),
                })
                .collect();
            let prover_data = ProverData::from_instances(&config, &instances);
            let proof = prove_batch(&config, &instances, &prover_data);
            verify_batch(&config, &airs, &proof, &pvs, &prover_data.common)
        }));
        match r {
            Err(_) => {} // the debug prover panicked on the violated gap/decomp teeth
            Ok(res) => assert!(
                res.is_err(),
                "forged absent bracket produced an accepted proof — gap tooth OPEN"
            ),
        }
    }

    /// THE ADJACENCY TOOTH, in-circuit, on a wide-bracket: the §8¾ Lean
    /// `wide_bracket_forge_rejected` shadow at the IR-v2 raw-batch level. Build the HONEST absent
    /// assembly for key 150 (bracketed by the GENUINE consecutive leaves 100/200), then forge ONLY
    /// the upper-bracket DIRECTION bits (`MA_HI_DIR0`) so the two opened leaves are NO LONGER at
    /// consecutive positions (`hi_pos − lo_pos ≠ 1`) — the literal WIDE BRACKET a commitment-knower
    /// would invent (`lo = 0x00…`, `hi = 0xFF…`, bracketing-but-not-adjacent). The adjacency
    /// constraint (`builder.assert_zero(is_real * (Σ dirᵢ·2ⁱ − 1))`) must refuse: a satisfying
    /// assignment cannot keep the leaf authentic under the root AND make the positions non-adjacent.
    /// This isolates the ADJACENCY teeth from the gap comparator (`ir2_absent_forged_bracket_refuses`
    /// forges the key; this forges the consecutiveness).
    #[test]
    fn ir2_absent_forged_wide_bracket_nonadjacent_refuses() {
        let desc = absent_desc();
        let layout = check_descriptor2(&desc).expect("absent gauntlet checks");
        let presence = Presence::of(&desc, &layout);
        let mut traces = build_traces(
            &desc,
            &layout,
            presence,
            &absent_trace(150),
            &MemBoundaryWitness::default(),
            &[test_heap()],
            &UMemBoundaryWitness::default(),
            true,
        )
        .expect("honest absent traces");
        // The honest upper-bracket position (leaf 200) sits at hi_pos = lo_pos + 1. Flip the lowest
        // direction bit of the UPPER path so the reconstructed position is no longer consecutive with
        // the lower one — the wide-bracket shape. (The `lo`/`hi` leaf digests, sibling paths and gap
        // comparators stay honest; ONLY the consecutiveness is broken, so the adjacency gate is the
        // sole tooth that can fire.)
        let ma = traces.map_absent.as_mut().expect("absent table present");
        let cur = ma[0][MA_HI_DIR0].as_u32();
        ma[0][MA_HI_DIR0] = BabyBear::new(cur ^ 1);
        let airs = instance_airs(&desc, layout, presence);
        let mut matrices = vec![to_matrix(&traces.main)];
        for t in [
            &traces.chip,
            &traces.byte,
            &traces.memory,
            &traces.boundary,
            &traces.map_ops,
            &traces.map_absent,
            &traces.umemory,
            &traces.umem_boundary,
        ]
        .into_iter()
        .flatten()
        {
            matrices.push(to_matrix(t));
        }
        let pvs: Vec<Vec<P3BabyBear>> = vec![vec![]; airs.len()];
        let config = ir2_config();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let instances: Vec<StarkInstance<'_, DreggStarkConfig, Ir2Air>> = airs
                .iter()
                .zip(matrices.iter())
                .zip(pvs.iter())
                .map(|((air, trace), pv)| StarkInstance {
                    air,
                    trace,
                    public_values: pv.clone(),
                })
                .collect();
            let prover_data = ProverData::from_instances(&config, &instances);
            let proof = prove_batch(&config, &instances, &prover_data);
            verify_batch(&config, &airs, &proof, &pvs, &prover_data.common)
        }));
        match r {
            Err(_) => {} // the debug prover panicked on the violated adjacency / leaf-binding teeth
            Ok(res) => assert!(
                res.is_err(),
                "forged NON-ADJACENT wide bracket produced an accepted proof — adjacency tooth OPEN"
            ),
        }
    }

    // ==== THE DEPLOYED noteSpend DESCRIPTOR — the double-spend wide-bracket close ====

    /// **THE DEPLOYED-LEVEL no-double-spend mutation-confirm (D1-wire).** The Lean §8¾
    /// (`Circuit/Argus/Effects/NoteSpend.lean`) proves `Adjacent ⟹ GapInterval` and that a
    /// non-consecutive wide bracket cannot be `Adjacent` (`wide_bracket_forge_rejected`); the
    /// forcing FFI it names is "the deployed noteSpend descriptor must enforce adjacency on the
    /// `(lo,hi)` bracket columns". The deployed `noteSpendVmDescriptor2R24` discharges that through
    /// its `.absent` map-op (`EffectVmEmitRotationV3.nullifierFreshOp`), realized by the IR-v2
    /// `MapAbsent` AIR — which enforces, IN-CIRCUIT, that the two opened bracket leaves sit at
    /// CONSECUTIVE positions (`hi_pos − lo_pos == 1`) AND authenticate under the committed nullifier
    /// root AND strictly straddle the spent nullifier. So the descriptor verify cannot accept a
    /// non-adjacent wide bracket — the forgery that "proves" non-membership of a nullifier that IS in
    /// the set (a double-spend).
    ///
    /// This test confirms that AT THE DEPLOYED DESCRIPTOR LEVEL (not the standalone
    /// `membership_verifier::verify_nullifier_nonmembership` unit, and not the synthetic
    /// `absent_desc`): build the HONEST deployed noteSpend assembly (real before-nullifier
    /// accumulator with ≥4 leaves; the spent nullifier brackets between two consecutive ones), prove
    /// + verify it through the deployed descriptor (NO DOWNGRADE), then forge ONLY the map-absent
    /// upper-bracket direction bits so the bracket is a NON-ADJACENT wide bracket, and confirm the
    /// deployed `noteSpendVmDescriptor2R24` verify REJECTS it. The light-client noteSpend
    /// double-spend forgery is closed end-to-end on the deployed wire.
    #[test]
    fn deployed_notespend_wide_bracket_double_spend_rejected() {
        use crate::effect_vm::trace_rotated::{
            NUM_PRE_LIMBS, ROT_WIDTH, RotatedBlockWitness, empty_caveat_manifest,
            generate_rotated_note_spend_trace_with_nullifier_tree,
        };
        use crate::effect_vm::{CellState, Effect};

        // Resolve the DEPLOYED noteSpend descriptor (the light-client V3-staged 47-PI shape carrying
        // the two nullifier map-ops — `.absent` freshness + `.insert` set-insert).
        let name = "noteSpendVmDescriptor2R24";
        let json = crate::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|l| {
                let mut it = l.splitn(3, '\t');
                if it.next() == Some(name) {
                    let _ = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("noteSpendVmDescriptor2R24 in V3_STAGED_REGISTRY_TSV");
        let desc = parse_vm_descriptor2(json).expect("deployed noteSpend descriptor parses");
        assert_eq!(
            desc.public_input_count, 47,
            "deployed noteSpend carries the nullifier-forcing pin"
        );
        // The descriptor genuinely carries the `.absent` freshness map-op (the adjacency-forcing leg).
        assert!(
            desc.constraints
                .iter()
                .any(|c| matches!(c, VmConstraint2::MapOp(m) if m.op == MapKind::Absent)),
            "the deployed noteSpend descriptor must carry the `.absent` freshness map-op"
        );

        let before_balance: u64 = 90_000;
        let value: u64 = 500;
        let nf: u32 = 0x5050; // the spent nullifier (NOT in the BEFORE set; brackets 0x4444..0x6666)
        let effect = Effect::NoteSpend {
            nullifier: BabyBear::new(nf),
            value,
        };
        let st = CellState::new(before_balance, 0);
        let effects = vec![effect];

        // A before-nullifier accumulator with FOUR leaves so the spent nullifier (0x5050) brackets
        // between the consecutive pair (0x4444, 0x6666) — and a NON-consecutive leaf (0x1111) exists
        // BELOW lo, the target of the wide-bracket forge.
        let before_nullifiers = vec![
            HeapLeaf {
                addr: BabyBear::new(0x1111),
                value: BabyBear::new(1),
            },
            HeapLeaf {
                addr: BabyBear::new(0x2222),
                value: BabyBear::new(1),
            },
            HeapLeaf {
                addr: BabyBear::new(0x4444),
                value: BabyBear::new(1),
            },
            HeapLeaf {
                addr: BabyBear::new(0x6666),
                value: BabyBear::new(1),
            },
        ];

        // The witness-INDEPENDENT block witnesses (the verify path threads trusted commits; for a
        // self-contained descriptor-level prove/verify the placeholder pre-limbs suffice — the
        // generator overrides the nullifier-root limbs from the real accumulator).
        let zero_w = RotatedBlockWitness::new(vec![BabyBear::ZERO; NUM_PRE_LIMBS], BabyBear::ZERO)
            .expect("NUM_PRE_LIMBS pre-iroot limbs");
        let caveat = empty_caveat_manifest();

        let (trace, dpis, map_heaps) = generate_rotated_note_spend_trace_with_nullifier_tree(
            &st,
            &effects,
            &zero_w,
            &zero_w,
            &caveat,
            &before_nullifiers,
        )
        .expect("deployment-real noteSpend trace builds (the spent nullifier is fresh)");
        assert_eq!(trace[0].len(), ROT_WIDTH, "deployed rotated trace width");

        // NO DOWNGRADE: the honest deployed noteSpend proves + verifies through the deployed
        // descriptor's `.absent`/`.insert` grow-gate — the adjacency tooth ACCEPTS a genuine
        // consecutive bracket.
        let mem_boundary = MemBoundaryWitness::default();
        let layout = check_descriptor2(&desc).expect("deployed noteSpend descriptor checks");
        let presence = Presence::of(&desc, &layout);
        let chip_laned = trace_with_chip_lanes(&desc, &trace);
        let honest_proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
            .expect("NO DOWNGRADE: the honest deployed noteSpend must prove");
        verify_vm_descriptor2(&desc, &honest_proof, &dpis)
            .expect("NO DOWNGRADE: the honest deployed noteSpend must verify");

        // THE FORGE (the wide-bracket double-spend): assemble the honest tables, then flip the lowest
        // upper-bracket direction bit so the two opened bracket leaves are NON-ADJACENT
        // (`hi_pos − lo_pos ≠ 1`) — the wide bracket a commitment-knower invents to fake freshness of
        // an already-spent nullifier. The deployed descriptor's `MapAbsent` adjacency constraint must
        // refuse: there is no satisfying assignment that keeps both leaves authentic under the root
        // while making their positions non-consecutive.
        let mut traces = build_traces(
            &desc,
            &layout,
            presence,
            &chip_laned,
            &mem_boundary,
            &map_heaps,
            &UMemBoundaryWitness::default(),
            true,
        )
        .expect("honest deployed noteSpend tables assemble");
        let ma = traces
            .map_absent
            .as_mut()
            .expect("deployed noteSpend descriptor commits a map-absent table");
        let cur = ma[0][MA_HI_DIR0].as_u32();
        ma[0][MA_HI_DIR0] = BabyBear::new(cur ^ 1);

        let airs = instance_airs(&desc, layout, presence);
        let mut matrices = vec![to_matrix(&traces.main)];
        for t in [
            &traces.chip,
            &traces.byte,
            &traces.memory,
            &traces.boundary,
            &traces.map_ops,
            &traces.map_absent,
            &traces.umemory,
            &traces.umem_boundary,
        ]
        .into_iter()
        .flatten()
        {
            matrices.push(to_matrix(t));
        }
        // The PIs ride the FIRST (Main) AIR only — the canonical `prove_vm_descriptor2_inner`
        // assembly (`pvs = vec![pis]` then resized to the air count).
        let pis: Vec<P3BabyBear> = dpis.iter().map(|&v| to_p3(v)).collect();
        let mut pvs: Vec<Vec<P3BabyBear>> = vec![pis];
        pvs.resize(airs.len(), vec![]);
        let config = ir2_config();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let instances: Vec<StarkInstance<'_, DreggStarkConfig, Ir2Air>> = airs
                .iter()
                .zip(matrices.iter())
                .zip(pvs.iter())
                .map(|((air, trace), pv)| StarkInstance {
                    air,
                    trace,
                    public_values: pv.clone(),
                })
                .collect();
            let prover_data = ProverData::from_instances(&config, &instances);
            let proof = prove_batch(&config, &instances, &prover_data);
            verify_batch(&config, &airs, &proof, &pvs, &prover_data.common)
        }));
        match r {
            Err(_) => {} // the debug prover panicked on the violated adjacency teeth
            Ok(res) => assert!(
                res.is_err(),
                "DEPLOYED noteSpend accepted a NON-ADJACENT wide-bracket non-membership witness — \
                 the light-client double-spend forgery is OPEN on the deployed descriptor"
            ),
        }
        eprintln!(
            "DEPLOYED noteSpend D1-WIRE: honest spend proves+verifies; a NON-ADJACENT wide-bracket \
             forged freshness witness is UNSAT through the deployed noteSpendVmDescriptor2R24 \
             MapAbsent adjacency tooth — the light-client double-spend forgery is CLOSED end-to-end."
        );
    }

    // ==== THE ROTATION (staged) — the Lean-emitted rotated-state probe ====
    //
    // `Dregg2/Circuit/Emit/EffectVmEmitRotation.lean` emits the rotated state block
    // (cells root · 16 registers · cap/nullifier/heap roots · lifecycle · epoch ·
    // committed height · the receipt-index MMR root LAST · the chained commitment)
    // as a graduated IR-v2 descriptor; the Lean keystones are
    // `rotationProbeV2_pins_commit` / `wireCommit_binds` /
    // `rotationProbe_commit_binds_published`. These tests are the Rust teeth:
    // honest witness proves+verifies (size measured), EVERY column and PI is
    // tamper-refused, and the layout/absorption coverage is drift-guarded in
    // `effect_vm_descriptors.rs`.

    fn rotation_probe_desc() -> EffectVmDescriptor2 {
        parse_vm_descriptor2(
            crate::effect_vm_descriptors::DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_JSON,
        )
        .expect("staged rotation probe parses")
    }

    /// The honest rotated-block witness: 24 distinct limbs (`100 + col`), the genuine
    /// 4-ary chained absorption (site digests on the chain carriers, final on
    /// `STATE_COMMIT`), PI = [published commit, committed height].
    fn rotation_probe_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        use crate::effect_vm::columns::rotation as rot;
        use crate::poseidon2::hash_many;
        // Phase B-GATE: the row is widened past PROBE_WIDTH by `7·n_sites` lane columns (the
        // descriptor's graduated trace width). The digest chain is built first (out0 columns),
        // then `fill_chip_lanes` writes the genuine lanes 1..7 for every chip lookup off the row.
        let desc = rotation_probe_desc();
        let mut row = vec![BabyBear::ZERO; desc.trace_width];
        for (i, cell) in row.iter_mut().enumerate().take(rot::IROOT + 1) {
            *cell = BabyBear::new(100 + i as u32);
        }
        // site 0: the first four limbs; sites 1..=6: digest + three limbs (arity 4);
        // site 7: digest + committed height (arity 2); the final site: digest + the
        // iroot LITERALLY LAST (arity 2) -> STATE_COMMIT.
        let mut d = hash_many(&[row[0], row[1], row[2], row[3]]);
        row[rot::CHAIN_BASE] = d;
        for k in 1..=6 {
            let b = 3 * k + 1;
            d = hash_many(&[d, row[b], row[b + 1], row[b + 2]]);
            row[rot::CHAIN_BASE + k] = d;
        }
        d = hash_many(&[d, row[rot::COMMITTED_HEIGHT]]);
        row[rot::CHAIN_BASE + 7] = d;
        let commit = hash_many(&[d, row[rot::IROOT]]);
        row[rot::STATE_COMMIT] = commit;
        fill_chip_lanes(&desc, &mut row);
        let pi = vec![commit, row[rot::COMMITTED_HEIGHT]];
        (vec![row; 4], pi)
    }

    /// The staged acceptance gate: the Lean-emitted rotated-state probe proves and
    /// verifies through the IR-v2 multi-table assembly (main + chip + byte — every
    /// absorption a real permutation row), and the staged shape's proof size is
    /// measured (printed; run with `--nocapture` to read it).
    #[test]
    fn rotation_probe_honest_witness_proves_verifies_and_measures() {
        let desc = rotation_probe_desc();
        let (rows, pi) = rotation_probe_trace();
        let proof = prove_vm_descriptor2(&desc, &rows, &pi, &MemBoundaryWitness::default(), &[])
            .expect("honest rotated-block witness must prove");
        assert_eq!(
            proof.degree_bits.len(),
            2,
            "rotation probe commits main + chip only (no range/mem/map lookups; \
             descriptor-empty tables elided)"
        );
        verify_vm_descriptor2(&desc, &proof, &pi).expect("rotation probe proof must verify");
        let total = postcard::to_allocvec(&proof).expect("postcard").len();
        println!(
            "rotation-state v3-staged probe proof: {total} bytes (~{:.1} KiB)",
            total as f64 / 1024.0
        );
    }

    // ==== THE REGISTER-COUNT MEASUREMENT (R ∈ {16, 24, 32}) ====
    //
    // Registers are ALWAYS-PAID: every register is a commitment limb in EVERY turn
    // proof (a main-trace column opened at each FRI query + chip absorption rows),
    // forever. Heap fields are METERED: umem rows only when touched (the real-turn
    // umem proof measures 64.4 KiB — `tests/effect_vm_umem_real_turn.rs`). The
    // parametric Lean emission (`EffectVmEmitRotationR.lean`, keystone
    // `wireCommitR_binds` parametric in R) stages R=24/R=32 probes beside the
    // deployed R=16 so the register-count decision is MEASURED, not vibed
    // (`docs/ROTATION-CUTOVER.md` pre-gates).

    /// The staged probe descriptor for a v3-staged registry key.
    fn rotation_probe_desc_key(key: &str) -> EffectVmDescriptor2 {
        let json = crate::effect_vm_descriptors::V3_STAGED_DESCRIPTORS
            .iter()
            .find(|(k, _, _)| *k == key)
            .unwrap_or_else(|| panic!("v3-staged key {key} not registered"))
            .1;
        parse_vm_descriptor2(json).expect("staged rotation probe parses")
    }

    /// The honest rotated-block witness at register count `r`: distinct limbs
    /// (`100 + col`), the genuine chained absorption (4-wide head, 3-wide groups
    /// while ≥ 3 remain, singletons after, the iroot alone LAST — the Lean
    /// `chunk31` chunking), site digests on the chain carriers, final digest on
    /// `state_commit`, PI = [published commit, committed height].
    fn rotation_probe_trace_r(r: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        use crate::effect_vm_descriptors::rotation_layout_for;
        use crate::poseidon2::hash_many;
        let lay = rotation_layout_for(r);
        // Phase B-GATE: widen to the graduated descriptor's trace width (the lane columns appended
        // past the probe width). Build the digest chain first, then `fill_chip_lanes` fills lanes
        // 1..7 for every chip lookup off the row (descriptor-driven, so R=16 == the hand builder).
        let key = match r {
            16 => "rotationProbeVmDescriptor2",
            24 => "rotationProbeVmDescriptorR24",
            32 => "rotationProbeVmDescriptorR32",
            _ => panic!("no staged rotation probe descriptor for R={r}"),
        };
        let desc = rotation_probe_desc_key(key);
        let mut row = vec![BabyBear::ZERO; desc.trace_width];
        for (i, cell) in row.iter_mut().enumerate().take(lay.iroot + 1) {
            *cell = BabyBear::new(100 + i as u32);
        }
        let mut d = hash_many(&[row[0], row[1], row[2], row[3]]);
        let mut chain = 0usize;
        row[lay.chain_base + chain] = d;
        chain += 1;
        let mut col = 4;
        while col <= lay.committed_height {
            let remaining = lay.committed_height - col + 1;
            if remaining >= 3 {
                d = hash_many(&[d, row[col], row[col + 1], row[col + 2]]);
                col += 3;
            } else {
                d = hash_many(&[d, row[col]]);
                col += 1;
            }
            row[lay.chain_base + chain] = d;
            chain += 1;
        }
        assert_eq!(chain, lay.num_chain, "chain carrier count at R={r}");
        let commit = hash_many(&[d, row[lay.iroot]]);
        row[lay.state_commit] = commit;
        fill_chip_lanes(&desc, &mut row);
        let pi = vec![commit, row[lay.committed_height]];
        (vec![row; 4], pi)
    }

    /// The honest R=16 witness built by the PARAMETRIC builder is bit-identical to
    /// the hand-built one (the pinned shape did not move).
    #[test]
    fn rotation_probe_trace_r16_matches_pinned_builder() {
        let (a, pa) = rotation_probe_trace();
        let (b, pb) = rotation_probe_trace_r(16);
        assert_eq!(a, b);
        assert_eq!(pa, pb);
    }

    /// THE MEASUREMENT: prove + verify all three register counts at the production
    /// `ir2_config` and print the always-paid grid — proof bytes, opened-values
    /// bytes, prove/verify time, chip rows, trace width. Run with
    /// `--release --nocapture` to read it; the verdict lives in
    /// `docs/ROTATION-CUTOVER.md`.
    #[test]
    fn rotation_probe_register_count_measurement() {
        for (key, r) in [
            ("rotationProbeVmDescriptor2", 16usize),
            ("rotationProbeVmDescriptorR24", 24),
            ("rotationProbeVmDescriptorR32", 32),
        ] {
            let desc = rotation_probe_desc_key(key);
            let (rows, pi) = rotation_probe_trace_r(r);
            let t0 = std::time::Instant::now();
            let proof =
                prove_vm_descriptor2(&desc, &rows, &pi, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| {
                        panic!("honest R={r} rotated-block witness must prove: {e}")
                    });
            let prove_ms = t0.elapsed().as_secs_f64() * 1e3;
            assert_eq!(
                proof.degree_bits.len(),
                2,
                "R={r}: rotation probe commits main + chip only"
            );
            let t1 = std::time::Instant::now();
            verify_vm_descriptor2(&desc, &proof, &pi)
                .unwrap_or_else(|e| panic!("R={r} rotation probe proof must verify: {e}"));
            let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
            let total = postcard::to_allocvec(&proof).expect("postcard").len();
            let opened = postcard::to_allocvec(&proof.opened_values)
                .expect("postcard")
                .len();
            println!(
                "rotation-probe R={r}: proof {total} B (~{:.1} KiB) | opened-values {opened} B \
                 (~{:.1} KiB) | prove {prove_ms:.0} ms | verify {verify_ms:.1} ms | \
                 chip 2^{} rows | main width {}",
                total as f64 / 1024.0,
                opened as f64 / 1024.0,
                proof.degree_bits[1],
                desc.trace_width,
            );
        }
    }

    /// SPOT TAMPER-REFUSAL at the measured widths (R=24, R=32): a wider block with
    /// untested columns is worse than a narrow one. A +1 tamper on a LOW register
    /// (r0), the HIGHEST register (r_{R-1} — no narrower layout carries it), the
    /// iroot, and the commit carrier each refuses; so do both PIs. (R=16 keeps the
    /// full every-column gauntlet below.)
    #[test]
    fn rotation_probe_r24_r32_spot_tamper_refusal() {
        use crate::effect_vm_descriptors::rotation_layout_for;
        use std::panic::{AssertUnwindSafe, catch_unwind};
        for (key, r) in [
            ("rotationProbeVmDescriptorR24", 24usize),
            ("rotationProbeVmDescriptorR32", 32),
        ] {
            let desc = rotation_probe_desc_key(key);
            let lay = rotation_layout_for(r);
            let (rows, pi) = rotation_probe_trace_r(r);
            let refused = |rows: &Vec<Vec<BabyBear>>, pi: &Vec<BabyBear>| -> bool {
                let res = catch_unwind(AssertUnwindSafe(|| {
                    prove_vm_descriptor2(&desc, rows, pi, &MemBoundaryWitness::default(), &[])
                }));
                match res {
                    Err(_) => true,
                    Ok(res) => res.is_err(),
                }
            };
            for col in [1, r, lay.iroot, lay.state_commit] {
                let mut t = rows.clone();
                t[0][col] = t[0][col] + BabyBear::ONE;
                assert!(refused(&t, &pi), "R={r}: tampered column {col} must refuse");
            }
            for k in 0..pi.len() {
                let mut p = pi.clone();
                p[k] = p[k] + BabyBear::ONE;
                assert!(refused(&rows, &p), "R={r}: tampered PI {k} must refuse");
            }
        }
    }

    /// TAMPER-REFUSAL, every column: each of the 33 probe columns (all 24 limbs —
    /// including the widened registers r8..r15, the heap_root limb, the committed
    /// height, and the iroot — plus the commitment carrier and every chain carrier)
    /// is load-bearing: a +1 tamper on any of them refuses. So do both PIs (the
    /// published commit and the published height). Tampers refuse either eagerly or
    /// at the batch self-verify; the debug prover may panic on the violated tooth —
    /// both are refusals (the absent-gauntlet pattern).
    #[test]
    fn rotation_probe_refuses_every_tampered_column_and_pi() {
        use crate::effect_vm::columns::rotation as rot;
        use std::panic::{AssertUnwindSafe, catch_unwind};
        let desc = rotation_probe_desc();
        let (rows, pi) = rotation_probe_trace();
        let refused = |rows: &Vec<Vec<BabyBear>>, pi: &Vec<BabyBear>| -> bool {
            let r = catch_unwind(AssertUnwindSafe(|| {
                prove_vm_descriptor2(&desc, rows, pi, &MemBoundaryWitness::default(), &[])
            }));
            match r {
                Err(_) => true,
                Ok(res) => res.is_err(),
            }
        };
        for col in 0..rot::PROBE_WIDTH {
            let mut t = rows.clone();
            t[0][col] = t[0][col] + BabyBear::ONE;
            assert!(refused(&t, &pi), "tampered column {col} must refuse");
        }
        for k in 0..pi.len() {
            let mut p = pi.clone();
            p[k] = p[k] + BabyBear::ONE;
            assert!(refused(&rows, &p), "tampered PI {k} must refuse");
        }
    }

    // ==== THE WIDENED CAVEAT OPERAND (staged) — the heap-caveat wire shape ====
    //
    // `Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean` emits the R=24 rotated
    // block + the 29-felt caveat manifest block (count + 4 × 7-felt entries
    // [type_tag, DOMAIN_TAG, KEY, p0..p3] — the operand widened from slot_index:u8
    // to (domain, key) with felt keys) + the chained caveat commitment, three PI
    // pins. Lean keystones: `caveat_operand_no_aliasing` (slot/heap domain
    // separation as a theorem), `caveatCommit_binds`,
    // `rotationCaveatProbe_binds_published`. These tests are the Rust teeth: the
    // honest witness (one register caveat + one HEAP-KEY caveat) proves+verifies;
    // a forged DOMAIN TAG refuses; a tampered HEAP KEY refuses; every manifest
    // column and every PI is load-bearing.

    fn rotation_caveat_probe_desc() -> EffectVmDescriptor2 {
        parse_vm_descriptor2(
            crate::effect_vm_descriptors::DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_JSON,
        )
        .expect("staged caveat probe parses")
    }

    /// The honest caveat-probe witness: the R=24 rotated-block witness (the
    /// parametric builder's limbs and chain), then the caveat manifest —
    /// entry 0 caveats REGISTER 3 (monotonic), entry 1 caveats HEAP KEY
    /// 123456789 (≥ 50; a key no u8 could carry) — and the genuine chained
    /// caveat absorption. PI = [state commit, height, caveat commit].
    fn rotation_caveat_probe_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        use crate::effect_vm::RotCaveatEntry;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::effect_vm_descriptors::rotation_layout_for;
        use crate::poseidon2::hash_many;
        let lay = rotation_layout_for(cav::R);
        let (rot_rows, rot_pi) = rotation_probe_trace_r(cav::R);
        // Phase B-GATE: build at the caveat descriptor's graduated trace width; copy ONLY the
        // rotated block's non-lane prefix (limbs + chain carriers + state_commit, all within
        // `lay.probe_width`) — the caveat descriptor's own lane columns are filled below by
        // `fill_chip_lanes` (the rotated lanes in `rot_rows` sit at the ROTATED descriptor's lane
        // offsets, which differ from the caveat descriptor's, so they must NOT be copied).
        let caveat_desc = rotation_caveat_probe_desc();
        let mut row = vec![BabyBear::ZERO; caveat_desc.trace_width];
        row[..lay.probe_width].copy_from_slice(&rot_rows[0][..lay.probe_width]);
        // The manifest block: count + the four entries (7 felts each).
        let e0 = RotCaveatEntry {
            type_tag: crate::effect_vm::pi::SLOT_CAVEAT_TAG_MONOTONIC,
            domain_tag: cav::DOMAIN_REGISTERS,
            key: BabyBear::new(3),
            params: [BabyBear::ZERO; 4],
        };
        let e1 = RotCaveatEntry {
            type_tag: crate::effect_vm::pi::SLOT_CAVEAT_TAG_FIELD_GTE,
            domain_tag: cav::DOMAIN_HEAP,
            key: BabyBear::new(123_456_789),
            params: [
                BabyBear::new(50),
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        };
        row[cav::COUNT_COL] = BabyBear::new(2);
        e0.write_to(&mut row[cav::ENTRY_BASE..cav::ENTRY_BASE + cav::ENTRY_SIZE]);
        e1.write_to(
            &mut row[cav::ENTRY_BASE + cav::ENTRY_SIZE..cav::ENTRY_BASE + 2 * cav::ENTRY_SIZE],
        );
        // (entries 2/3 stay zero — "no caveat".)
        // The chained caveat absorption: 4-wide head, 3-wide groups, final singleton.
        let last = cav::BASE + cav::MANIFEST_SIZE - 1; // col 71
        let mut d = hash_many(&[row[43], row[44], row[45], row[46]]);
        let mut chain = 0usize;
        row[cav::CHAIN_BASE + chain] = d;
        chain += 1;
        let mut col = 47;
        while col <= last {
            let remaining = last - col + 1;
            if remaining >= 3 {
                d = hash_many(&[d, row[col], row[col + 1], row[col + 2]]);
                col += 3;
            } else {
                d = hash_many(&[d, row[col]]);
                col += 1;
            }
            if col <= last {
                row[cav::CHAIN_BASE + chain] = d;
                chain += 1;
            }
        }
        assert_eq!(chain, cav::NUM_CHAIN, "caveat chain carrier count");
        row[cav::CAVEAT_COMMIT] = d;
        // Phase B-GATE: fill the genuine lanes 1..7 for every chip lookup (rotated before/after
        // sites + caveat sites) off the now-complete digest columns.
        fill_chip_lanes(&caveat_desc, &mut row);
        let pi = vec![rot_pi[0], rot_pi[1], d];
        (vec![row; 4], pi)
    }

    /// The staged acceptance gate: the Lean-emitted caveat probe proves and
    /// verifies through the IR-v2 multi-table assembly (every absorption a real
    /// permutation row), proof size measured.
    #[test]
    fn rotation_caveat_probe_honest_witness_proves_verifies_and_measures() {
        let desc = rotation_caveat_probe_desc();
        let (rows, pi) = rotation_caveat_probe_trace();
        let proof = prove_vm_descriptor2(&desc, &rows, &pi, &MemBoundaryWitness::default(), &[])
            .expect("honest caveat-probe witness must prove");
        assert_eq!(
            proof.degree_bits.len(),
            2,
            "caveat probe commits main + chip only"
        );
        verify_vm_descriptor2(&desc, &proof, &pi).expect("caveat probe proof must verify");
        let total = postcard::to_allocvec(&proof).expect("postcard").len();
        println!(
            "rotation-caveat v3-staged probe proof (R=24 + 29-felt manifest): {total} bytes \
             (~{:.1} KiB)",
            total as f64 / 1024.0
        );
    }

    /// THE OPERAND TEETH: a forged DOMAIN TAG (heap → registers — the aliasing
    /// attack the u8 operand could not even EXPRESS — or heap → caps) refuses; a
    /// tampered HEAP KEY refuses (the key is commitment-carried, not metadata);
    /// so do the count, every entry column, the caveat chain, the commitment
    /// carrier, and every PI. Tampers refuse eagerly or at the batch self-verify;
    /// the debug prover may panic on the violated tooth — both are refusals (the
    /// absent-gauntlet pattern).
    #[test]
    fn rotation_caveat_probe_refuses_forged_domain_and_tampered_key() {
        use crate::effect_vm::columns::rotation::caveat as cav;
        use std::panic::{AssertUnwindSafe, catch_unwind};
        let desc = rotation_caveat_probe_desc();
        let (rows, pi) = rotation_caveat_probe_trace();
        let refused = |rows: &Vec<Vec<BabyBear>>, pi: &Vec<BabyBear>| -> bool {
            let r = catch_unwind(AssertUnwindSafe(|| {
                prove_vm_descriptor2(&desc, rows, pi, &MemBoundaryWitness::default(), &[])
            }));
            match r {
                Err(_) => true,
                Ok(res) => res.is_err(),
            }
        };
        // The named attacks, by column: entry 1 (the heap caveat) lives at base 51.
        let e1 = cav::ENTRY_BASE + cav::ENTRY_SIZE;
        // Forge the heap entry's DOMAIN TAG to the registers plane (slot/heap aliasing).
        let mut t = rows.clone();
        t[0][e1 + 1] = BabyBear::new(cav::DOMAIN_REGISTERS);
        assert!(
            refused(&t, &pi),
            "forged domain tag (heap→registers) must refuse"
        );
        // Forge it to a non-caveat plane (caps = 2).
        let mut t = rows.clone();
        t[0][e1 + 1] = BabyBear::new(2);
        assert!(
            refused(&t, &pi),
            "forged domain tag (heap→caps) must refuse"
        );
        // Tamper the HEAP KEY (point the caveat at a different heap field).
        let mut t = rows.clone();
        t[0][e1 + 2] = t[0][e1 + 2] + BabyBear::ONE;
        assert!(refused(&t, &pi), "tampered heap key must refuse");
        // Every caveat column is load-bearing: the manifest block, the chain, the carrier.
        for col in cav::BASE..cav::PROBE_WIDTH {
            let mut t = rows.clone();
            t[0][col] = t[0][col] + BabyBear::ONE;
            assert!(refused(&t, &pi), "tampered caveat column {col} must refuse");
        }
        // Every PI is load-bearing — including the published caveat commit.
        for k in 0..pi.len() {
            let mut p = pi.clone();
            p[k] = p[k] + BabyBear::ONE;
            assert!(refused(&rows, &p), "tampered PI {k} must refuse");
        }
    }
}
