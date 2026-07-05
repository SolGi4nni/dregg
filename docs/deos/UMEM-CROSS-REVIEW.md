# umem-as-a-primitive — cross-review brief (for Codex)

> **Point-in-time review artifact (~2026-06-24).** Reads as the state at that session.
> One address-space change since: the `Domain` enum has gained a **sixth** constructor,
> `working` (Stage D service/interpreter scratch; deliberately never projected into
> committed state — `working_commitment_inert`), mirrored by Rust `UDomain::Working = 5`.
> The named symbols and the seven-item proof frontier below otherwise still hold; cited
> Lean line numbers have drifted but the symbols are intact.

*A second voice is requested. This document hands Codex the universal-memory work
landed in one session, names every soundness seam honestly, and lays out the Lean
proof frontier the new semantics open. Critique it, contradict it, and add your own
ideas — especially where a claim is stronger than its proof, or where a cleaner design
exists. The goal is the most correct version, not the most flattering.*

Ground truth lives in the code + Lean; this brief points at it. Where this brief and
the source disagree, the source wins — flag it.

---

## The thesis

dregg's `umem` (universal memory) was built as ONE thing: the entire world's state
projected into a single `Domain × κ` address space, offline-checked by a Blum multiset,
with a sorted-Poseidon2 boundary root and **zero intra-proof hashing** (a write+read-back
is 67.6 KiB vs 128.7 KiB as a map op). The realization driving this work: **that single
umem is one *instance* of a parametric construct, and umem should be a general primitive**
— per-cell heaps, working memory, passable intermediate states, and composition, all on
one witnessed object. Memory becomes a first-class verifiable thing, the way cells are
objects rather than ledger rows.

Three already-proven properties let many umems coexist soundly in one trace (all
`#assert_axioms`-clean): **tag isolation** (`consistentFrom_filter/_strip`), **final-column
pinning** (`memcheck_pins_final`), **boundary = committed root** (`boundary_root_derived`),
in `metatheory/Dregg2/Crypto/UniversalMemory.lean`. The executor bridge already projects the
*entire* live state and checks `fold(pre,ops)==post` (`turn/src/umem.rs` —
`project_executor_state`, `emit_trace`).

## What landed this session (commits + docs)

- **The keystone — `99a8dc94`** — bound the boundary INIT image to committed state:
  `boundary_init_root_derived` + `boundary_init_root_bound` (`UniversalMemory.lean` §4b,
  `#assert_axioms`-clean), lifted to the IR as `satisfied2U_init_root`. **And the witnessed
  cross-cell-read primitive**: a turn that mutates cell A but only *reads* cell B proves it
  read B's committed state (B's heap root → a public input, a `MapOp::Read` opens against it);
  the circuit twin of the executor-only `ObservedFieldEquals`. `effect_vm_umem_real_turn.rs`
  7/7, all tamper teeth bite.
- **Design — `UMEM-PRIMITIVE.md` (`a63b5ddf`)** — the parametric model + the four uses +
  the document-language showcase + the staged build path (Stage A = per-cell `heap_map` as a
  first-class umem collection).
- **Post-quantum — `UMEM-POSTQUANTUM.md` (`07dbf168`)** — verdict: the umem *memory argument*
  is PQ-plausible today (Poseidon2-CR + FRI + Blum, zero DLog); the non-PQ exposure is the
  *surround* (ed25519, Pedersen, X25519). Path to fully-PQ is structurally light (swap
  ed25519→ML-DSA; the Lean routes auth through a `Prop`-portal so the proof shape is unchanged).
- **Revolutions, each prototyped + green** (executable shadow; in-circuit witnessing seamed):
  - agent memory as a portable umem — checkpoint/handoff/resume an agent (`3911af58`).
  - the membrane fork/carry/stitch as umem ops — **field-granular** merge (disjoint fields of
    one cell merge clean; conflicts are first-class objects at the exact address) (`c4d97184`).
  - promises/continuations as passable umems — suspend/serialize/resume a paused computation
    (`9de9f345`).
  - checkpointable confined-runtime (android-cell) boundary state as a umem — save/restore/
    migrate, witnessed live (`873c3e36`).
  - time-travel: a snapshot IS a boundary, rewind IS restoring it — no O(history) replay
    (`turn/tests/umem_time_travel.rs`).
  - proof-shrink: −48.6% when interior memory drops a chip table (real but latent — needs a
    memory-only descriptor) (`a47f5a19`).
- **deos-side** — documents now commit to the real cell heap (`fields_map`, `fields_root`-
  witnessed) not a sidecar (`af724007`); intent/workflow/refinement surfaced on the desktop.

## Soundness status — what is actually proven vs claimed

**`#assert_axioms`-clean, proven:** the boundary-binding (init + final root derivations +
injectivity teeth, `{propext, Classical.choice, Quot.sound}`); per-cell membership for a
*touched* read cell (a faithful subset view, the cross-cell-read need); the forward
agreement square `fold(pre,ops)==post` (executor bridge); tag isolation / final pinning /
boundary=root.

**Executable-shadow only (proven in Rust tests, NOT yet in-circuit / in Lean):** every
revolution's round-trip is proven *at the projection + op-trace level* (e.g. continuation
suspend/resume equals straight-through; rewind folds the inverse trace exactly; membrane
field-merge). The cryptographic, light-client-verifiable version of each rides the proof
frontier below.

## The Lean proof frontier (the upgrades the new semantics need)

Each is the named seam of a landed revolution. **Codex: please pressure-test these — is the
obligation stated right? Is the proof tractable? Is there a cleaner formulation?**

1. **Whole-image boundary equality (the keystone's named tail).** Today the binding proves
   each *touched* cell's init/read equals the committed root (subset view). The *no-extra-cells*
   direction — an in-circuit sorted-Poseidon2 root-fold over the ENTIRE boundary — is deferred;
   its **Lean statement is landed + clean** (`boundary_init_root_bound`), only the in-circuit
   AIR realization waits (it rides the universal-map rotation). *Is per-cell membership + the
   final-pinning enough for the cross-cell-read soundness story, or is whole-image strictly
   required?*
2. **Per-cell umem soundness (Stage A).** Project `heap_map` as a `Heap{cell,collection,key}`
   collection; prove the per-cell umem boundary equals the cell's committed `heap_root`
   (should be `boundary_root_derived` filtered by `UKey::cell()` — verify the filter preserves
   soundness).
3. **Per-handoff Blum-trace witness (membrane / passable umems).** Bind a carried projection's
   `pre→post` to a genuine executor op-trace (`emit_trace`), so a recipient re-folds and refuses
   any projection no real turn produced. Obligation: the envelope's `UmemTurnWitness` ⟹ the
   projection is reachable by a disciplined trace from a committed pre-state.
4. **`reify_cell` round-trip (time-travel / restore).** `reify(project(L)) == L` after
   re-deriving the deliberately-dropped commitments (ledger Merkle root, `fields_root`, metering).
   Prove the reconstruction is faithful (the dropped fields are functions of the kept planes).
5. **Mid-forest yield_point (continuations).** Checkpoint *between* two effects of one turn
   (today captures from a *completed* turn's trace). Prove the journal-prefix snapshot +
   forward-the-rest is sound mid-turn.
6. **Promise-hole-as-nullifier (in-circuit continuation).** The partial-turn circuit work — a
   promise hole IS a nullifier, resolution = a one-shot spend (the double-spend non-membership
   the circuit already enforces). This is the deepest one; relate it to the existing
   `eventual`/`conditional`/`pending` + the noteSpend grow-gate.
7. **Deep-interior runtime checkpoint (service cells).** The android-cell boundary umem is
   witnessed; the *interior* needs either (a) a firmament app-PD whose memory IS dregg cells
   (the n=1 collapse — "confined-runtime state" and "cell state" become one object), or
   (b) deterministic replay from the ordered boundary-act log. Which is the right object?

## Open questions for Codex (please weigh in)

- Is "umem as a parametric primitive" the right abstraction, or does multiplying umems risk a
  soundness gap the single-global-umem avoids? (We believe tag-isolation covers it — verify.)
- The replayable-cell vs service-cell distinction: should the receipt commit a typed
  `Semantics::{Replayable | Serviced(boundary_digest)}` bit, and does that need a Lean change?
- The PQ path: is swapping ed25519→ML-DSA really proof-shape-preserving (the `Prop`-portal claim)?
- The proof-shrink win is latent (no current descriptor hashes *only* for memory). Is the
  partial-turn nullifier descriptor the right first place to harvest it, or is there a better one?
- What are we *missing* — a use, a soundness hole, a cleaner construction?

## How to contribute

Add your review inline (or a sibling `UMEM-CROSS-REVIEW-CODEX.md`): correct the soundness
claims against the source, sharpen or refute the proof-frontier framing, propose Lean
formulations, and name anything overstated. The most valuable thing you can do is find where a
claim outruns its proof.
