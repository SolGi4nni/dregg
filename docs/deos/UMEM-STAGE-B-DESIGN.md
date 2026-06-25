# umem Stage B — the `UmemRef` value + the checkpoint/resume effect surface

*A design for the owner to DECIDE on. No build is proposed here. Per
`UMEM-PRIMITIVE.md` §4/§7, Stage B is "the only genuinely new circuit-adjacent
surface" — the be-extremely-thoughtful effect/circuit zone — so it is designed
grounded against HEAD before any kernel code is written.*

This document grounds every claim to file:line at HEAD and names every soundness
obligation. Where a thing is already built it says so and points at it; where a
thing is new it says whether it is additive or VK-affecting and what it costs.
Nothing here is asserted to be sound that is not either deployed or backed by a
named, `#assert_axioms`-clean Lean theorem.

---

## 0. What Stage B is, in one paragraph

A umem-ref is a **content-addressed checkpoint**: the sorted-Poseidon2 boundary
root of a declared address slice of the universal memory, plus the declared
address list, plus a data-availability locator for the preimage. **Checkpoint**
= emit that root (the *final* boundary edge, already pinned in-circuit).
**Resume** = bind that root as the *init* boundary edge of a later turn and
continue. Stage B is exactly: (a) the `UmemRef` value type, (b) the
checkpoint effect-output that emits the final root, (c) the resume input that
binds it as the init root via a public input, and (d) the soundness obligations
those two seams incur. The keystone's two edges
(`boundary_root_from_memcheck` / `boundary_init_root_bound`,
`metatheory/Dregg2/Crypto/UniversalMemory.lean:429,475`) ARE checkpoint and
resume; Stage B is the *wiring of a root to a public input*, not a new soundness
argument — **with one honestly-named exception** (the whole-image
no-extra-cells fold, §3.4 / §6, which is a proved Lean theorem awaiting its
in-circuit AIR).

---

## 1. The `UmemRef` value type (§4 of UMEM-PRIMITIVE)

### 1.1 The type

```rust
/// A portable, witnessed checkpoint of a umem slice. Its `root` is the handoff
/// witness; `declared_addresses` is the boundary's declared address list (the
/// Lean `as`); `availability` locates the preimage a resumer needs to continue.
pub struct UmemRef {
    /// The domain(s) this ref commits. A single-domain ref (the common case:
    /// one cell's `Heap`) carries one; a multi-domain slice carries several,
    /// each with its OWN per-domain root (composition is Stage D, §5 of
    /// UMEM-PRIMITIVE — Stage B fixes the single-domain shape and forbids the
    /// multi-domain form rather than half-supporting it).
    pub domains: Vec<UDomain>,            // turn/src/umem.rs:93

    /// The declared boundary addresses (the Lean `as` list), SORTED and unique.
    /// These are the `(domain, key)` cells the root commits; resume opens keys
    /// from exactly this set. Sorting is load-bearing: the boundary view is the
    /// canonical sorted leaf list `boundaryCells` folds (UniversalMemory.lean:320,
    /// `boundary_root_derived` requires `as.Pairwise (· < ·)`).
    pub declared_addresses: Vec<UKey>,    // turn/src/umem.rs:118

    /// The sorted-Poseidon2 boundary root over the present declared cells. This
    /// IS the umem-ref's identity — its content address. Carried at the FAITHFUL
    /// commitment floor width (§1.3); NOT a 31-bit single felt.
    pub root: [u8; 32],

    /// WHERE the preimage lives. The root is the witness; resume needs the
    /// actual `(addr → value)` store to continue the trace, and that store is
    /// off the consensus path. `None` = the resumer is expected to already hold
    /// it (same-process handoff). `Some` = a CapTP-style SturdyRef / content
    /// locator to fetch it (cross-instance handoff). Data-availability of the
    /// preimage is a liveness concern, NOT a soundness one: a tampered or
    /// missing preimage cannot reproduce `root` (§6), so resume fail-closes.
    pub availability: Option<SturdyRef>,
}
```

### 1.2 What it is NOT

* It is **not** a snapshot of the whole world. It is a slice — a domain/address
  subset — exactly as the per-cell heap (Stage A) is a `Heap{cell, ..}` filter
  of the global projection (`turn/src/umem.rs:357`).
* The `root` does **not** carry the preimage. It binds it (injectively, under
  the CR floor — `Heap.root_injective`), but the bytes live behind
  `availability`. This is the Xanadu `Pin::At` shape, made a value.
* It is **not yet** a `UVal`. A `UVal::UmemRef` (a umem cell whose value is
  another umem's root) is **composition, Stage D** (`UMEM-PRIMITIVE.md` §5).
  Stage B keeps `UmemRef` a turn-level value (effect output / receipt field /
  carrier payload), not an in-memory cell value.

### 1.3 Root width — a load-bearing floor, not a free choice

The deployed per-cell `heap_root` is `[u8; 32]` (`cell/src/state.rs:210`), and
the cross-cell-read leg opens against a single committed-root public input
(`circuit/tests/effect_vm_umem_real_turn.rs:494`, `PiBinding` to PI 0). But the
effect-VM's state commitments (`OLD_COMMIT[4]`, `NEW_COMMIT[4]`,
`circuit/src/effect_vm/mod.rs:104`) are **4 felts**, and the chip carrier was
widened to the **faithful 8-felt commitment** (`CHIP_WIDE_ARITY = 11`,
`descriptor_ir2.rs:230`; `WIDE_K = 3`, the wide Merkle–Damgård step). Per
`docs/FAITHFUL-STATE-COMMITMENT.md` and the don't-launder-a-load-bearing-
insecurity scar: the umem-ref root **must** be carried at the system's own
soundness floor (8 felts, matching FRI ~130-bit), **not** the reserved 4 and
**never** a 31-bit single felt. The `[u8; 32]` external form is fine; the
in-circuit public-input carrier is the 8-felt faithful commitment. This is an
explicit decision point for the owner, flagged so it is not defaulted-into.

---

## 2. The checkpoint effect-output (emit the final boundary root)

### 2.1 Shape: a derived OUTPUT, not a state mutation

Checkpoint emits the boundary root of a declared slice **at end of turn**. The
crucial design realization: **the final boundary edge is already pinned
in-circuit.** `boundary_root_from_memcheck` (`UniversalMemory.lean:429`) +
`memcheck_pins_final` (line 281) force the prover's claimed final column to the
genuine fold, so the derived final root is trustworthy, not prover-chosen.
Checkpoint therefore does **not** need a new circuit; it **exposes** a value the
circuit already commits.

Concretely, checkpoint is a new **`TurnOutput`** variant (the existing
output-forwarding vocabulary, `turn/src/eventual.rs:119`):

```rust
pub enum TurnOutput {
    // ... existing GrantedCapability / CreatedNote / StateUpdate / CreatedCell ...
    /// A umem slice was checkpointed: here is its boundary root + declared
    /// addresses at end of turn. The root is the already-pinned final boundary
    /// (boundary_root_from_memcheck); this output exposes it for handoff.
    UmemCheckpoint { umem_ref: UmemRef },
}
```

### 2.2 The receipt-binding antibody

The one obligation checkpoint adds is **binding the emitted root to the genuine
final boundary** so an executor cannot emit a checkpoint of a *different* state
than the turn actually reached. This is the exact pattern `RefreshDelegation`
already uses (`turn/src/action.rs:1077`): "the executor DERIVES the genuine
value at apply time and refuses a mismatching declaration (the forge antibody);
both bind into `effects_hash`." For checkpoint:

* The executor derives the final boundary root from the post-state projection
  (the Rust shadow of `boundary_root_derived` — `compute_heap_root` over the
  declared slice, `cell/src/state.rs:403`, exactly the fold in
  `open_heap_against_committed`, `turn/src/umem.rs:501`) and **refuses** any
  declared `umem_ref.root` that mismatches.
* The `umem_ref.root` binds into `effects_hash` (and thence `receipt_hash`), so
  a light client knows WHICH slice was checkpointed and to WHAT root. This is a
  receipt-output binding, the same class as `RefreshDelegation`'s `snapshot`.

### 2.3 Linearity class

Checkpoint is **`LinearityClass::Neutral`** (`turn/src/action.rs:913`): no
resource delta — it is pure book-keeping over an already-committed boundary. It
requires no paired sibling and no conservation rung. (This is the honest reason
checkpoint is cheap: it reads the final edge, it does not move value.)

### 2.4 Minimal circuit surface for checkpoint

**One new public-input slot**: the emitted final-boundary root (8 felts,
§1.3), pinned (via the existing `PiBinding` constraint,
`descriptor_ir2.rs` / the cross-cell test at line 494) to the circuit's
already-computed final boundary root of the declared domain. No new selector, no
new table, no new AIR body. The *only* deployment cost is that adding a PI slot
changes the PI vector → changes the VK (VK-affecting; see §4).

If the declared slice is exactly a single cell's `Heap` domain (the Stage A
shape), the final boundary root is `NEW_COMMIT`-adjacent (the cell's committed
`heap_root` is already folded into the canonical commitment v6→v7,
`cell/src/state.rs:210`), so checkpoint can in principle pin against an
already-present commitment rather than a fresh PI — an even cheaper sub-case the
owner may prefer. (Decision point.)

---

## 3. The resume input (bind the root as the init boundary)

### 3.1 Shape: a boundary-witness restructure, not necessarily an effect row

Resume binds `umem_ref.root` as the **init** image of a later turn and opens the
declared addresses against it. The deployed machinery for this **already
exists**: it is the witnessed cross-cell read, `satisfied2U_init_root`
(`descriptor_ir2.rs:96-104`; Lean `boundary_init_root_derived` /
`boundary_init_root_bound`, `UniversalMemory.lean:463,475`; the working leg in
`circuit/tests/effect_vm_umem_real_turn.rs:425-601`). That leg:

1. pins a committed root to a public input (`PiBinding`, test line 494), and
2. opens each declared address against it with a `MapOp::Read`
   (`MapKind::Read`, `descriptor_ir2.rs:405`; test line 500),

so a forged root has no satisfying membership path (anti-forge tooth) and a
forged value opens to the genuine leaf and refuses (mismatch tooth).

**Resume = the cross-cell read, with the committed root supplied by a passed
`UmemRef` instead of read from a peer cell's `heap_root`.** That is the whole
move. The Stage A cross-cell read (`open_heap_against_committed`,
`turn/src/umem.rs:471`) opens cell B's heap against B's *own committed*
`heap_root`; resume opens against a root that was *handed to you in a
`UmemRef`*. Same theorem, same leg, different source of the root.

### 3.2 Where the root enters

The resumed init root is **a new committed-root public input** wired exactly
like the cross-cell test's PI 0. The resumer's turn declares: "my init image for
these addresses is the slice committed by `umem_ref.root`," supplies the
preimage as the boundary witness (`UMemBoundaryWitness`, the witness-supplied
init image, `descriptor_ir2.rs:95`), and the `PiBinding` + `MapOp::Read`
openings force the supplied preimage to be the genuine slice under that root.

### 3.3 Does resume need a selector?

**No — if resume is a boundary-witness restructure** (an init-binding leg
attached to a turn, supplying `umem_ref.root` as a PI and opening addresses). It
emits no main-trace effect row; it is the same category as the memory boundary
itself (witness-supplied, not a selector-gated effect). This is the **additive**
path and the recommended Stage B target for resume.

**Yes — if resume is reified as a first-class `Effect::ResumeUmem` row** with its
own AIR body (e.g. to make "this turn resumed ref R" a selector-gated, receipt-
visible action). That is a heavier choice (§4) and is **not** required for the
soundness story; it is an ergonomics/visibility choice. Defer unless the owner
wants resume to be an auditable verb.

### 3.4 The soundness scope of resume — named precisely

The deployed `satisfied2U_init_root` binds each **touched** address by per-cell
membership: a faithful **SUBSET** view ("address X under this root IS this
value"). This is **exactly** what a resume that only *reads forward* from
declared addresses needs.

What the subset view does **not** give, on its own: the **no-extra-cells**
direction — that the committed slice holds *nothing the boundary did not
declare*. For full continuation soundness ("the resumed init image is EXACTLY
the producer's checkpoint, no hidden cells"), you need the **whole-image** pin.
Its soundness is a **proved, `#assert_axioms`-clean Lean theorem**:
`boundary_whole_image_sem` / `boundary_image_eq_of_root`
(`UniversalMemory.lean:521,508`; IR lift `satisfied2U_init_whole_image`,
`descriptor_ir2.rs:106-114`) — pin the committed root to the sorted-Poseidon2
fold of the ENTIRE declared boundary image and, under the CR floor, the committed
heap agrees with the declared image at every address, absence off-list included.

**What is missing is purely in-circuit AIR/witness work**: an AIR that *computes*
`Heap.root hash (boundaryCells …)` over the whole declared boundary and pins it
to the committed-root PI (the theorem's `hpin` hypothesis). That per-domain
sorted-leaf fold chip **rides the universal-map rotation** (`descriptor_ir2.rs:113`,
`circuit/tests/effect_vm_umem_real_turn.rs:451`). It is the named tail — see §3.5
for the staged consequence.

### 3.5 The two resume strengths

| strength | soundness obligation | status | when it suffices |
|---|---|---|---|
| **subset resume** (read-forward) | `satisfied2U_init_root` (`boundary_init_root_bound`'s per-cell realization) | **DEPLOYED** | the resumer only reads declared addresses; extra hidden cells in the committed slice cannot affect what it reads, because it only opens declared keys |
| **whole-image resume** (exact continuation) | `boundary_whole_image_sem` + the in-circuit whole-boundary root-fold | Lean **PROVED**; AIR is the **named tail** (rides the rotation) | the resumer's correctness depends on *absence* off the declared list (e.g. "no other note exists", a freshness-style continuation) |

The honest statement: **subset resume ships on deployed machinery now;
whole-image resume is gated on the rotation's fold chip.** Stage B should target
subset resume as the floor and name whole-image as the bounded follow-up, NOT
claim whole-image is free.

### 3.6 One-shot vs idempotent resume (the promise-hole = nullifier question)

A `UmemRef` can be resumed under two regimes, and the distinction is a real
design decision (it mirrors transclusion's `Pin::At` vs `Pin::Live`,
`UMEM-PRIMITIVE.md` §8):

* **Idempotent / snapshot (`At`)**: the ref is an immutable citation; resuming it
  many times is fine (each resume re-binds the same root). No anti-replay needed.
  This is the "a citation that does not break" case.
* **One-shot / continuation (linear)**: the ref is a *continuation token* and may
  be resumed **exactly once** — resuming twice would fork a linear state. This is
  the partial-turn/promises insight already in the record: **a promise-hole IS a
  nullifier; resolution = a spend** (`project-partial-turn-promises.md`;
  `Effect::React` "to React is to SPEND the hole", `turn/src/action.rs:1317`).
  The circuit **already enforces** nullifier freshness as a memory property
  (`nullifier_fresh_sound`, `UniversalMemory.lean:611`; `NULLIFIER_DOMAIN = 3`,
  `descriptor_ir2.rs:205`). So one-shot resume is realized by **deriving a
  nullifier from the `UmemRef` and spending it on resume** — no new mechanism,
  the `Nullifiers` domain. A second resume reads a non-fresh nullifier and
  refuses.

Stage B should pick **idempotent as the default** (a checkpoint is a citation)
and offer one-shot as the nullifier-gated variant for continuation handoffs. The
owner decides whether one-shot is in Stage B or deferred to Stage C (where the
carriers — `EventualRef` resolution, the pipeline, the membrane — are the natural
place a continuation is consumed).

---

## 4. Additive vs a real new selector — and the honest cost

| component | additive? | VK-affecting? | cost |
|---|---|---|---|
| `UmemRef` value type | yes (pure data) | no | a struct + serde; off-circuit `root == compute_*_root(preimage)` validation (the `open_heap_against_committed` shadow) |
| checkpoint as `TurnOutput::UmemCheckpoint` | yes | **yes** (1 new PI slot, §2.4) | one `TurnOutput` arm + the derive-and-refuse antibody + `effects_hash` binding + the PI pin; **no selector, no table, no AIR body** |
| subset resume (boundary-witness restructure) | yes | **yes** (1 new committed-root PI slot) | reuse `satisfied2U_init_root`; supply `umem_ref.root` as PI + `MapOp::Read` openings; **no selector** |
| whole-image resume | no | yes | the universal-map rotation's per-domain sorted-leaf **fold chip** + a whole-boundary root pin — the named tail, real work |
| dedicated `ResumeUmem`/`CheckpointUmem` selector | only by **repurposing a retired index** | yes | a Lean `*VmDescriptor2` + the rotated `*V3`, an executor arm, a `LinearityClass`, the denotational differential test — the full per-effect rung |

### 4.1 The selector reality

A brand-new selector column is **not** free: the frozen verified descriptors
pin **absolute** column indices against the 188-wide trace
(`circuit/src/effect_vm/columns.rs:31,40-45`), so adding a column forces the
descriptor-relayout lane. **But** there is a deployed precedent for adding a
verb *without* a relayout: `sel::MINT = 14` **repurposed a retired index** (the
dissolved `ExportSturdyRef` slot, `columns.rs:113-122,174-176`). There are **24
retired selectors** pinned to zero (`RETIRED_SELECTORS`, `columns.rs:186`), so a
dedicated checkpoint/resume verb is feasible by repurposing one — the MINT
playbook. That is the honest path *if* a first-class verb is wanted; it is the
heaviest of the Stage B options and is **not** needed for the
boundary-witness-restructure design (§2, §3.3).

### 4.2 The PI-budget honesty

Every new public-input slot changes the PI vector and therefore the VK and the
recursion/aggregation PI-matching shape (`circuit/src/effect_vm/mod.rs:140-146`).
This is "additive in semantics, VK-affecting in deployment." The discipline (per
the don't-over-ember-gate feedback and the green-or-bust feedback): **batch all
Stage-B PI additions into ONE VK cut**, drive it to green, do not dribble VK
churn across sub-stages.

---

## 5. A staged sub-path

Each rung is independently landable and named with its closure lane.

* **B0 — `UmemRef` value + off-circuit validation.** Define the type (§1). Add
  `UmemRef::derive_root(slice) -> [u8;32]` (the `compute_heap_root` /
  `boundary_root_derived` shadow) and `UmemRef::verify(preimage) -> Result`
  (the `open_heap_against_committed` shape). **No circuit. No VK.** This is the
  Rust-only foundation both later rungs stand on.

* **B1 — checkpoint as a derived output.** `TurnOutput::UmemCheckpoint`, the
  executor derive-and-refuse antibody, the `effects_hash` binding, and the one
  PI pin to the already-pinned final boundary (§2). Reuses the **final** edge
  (`boundary_root_from_memcheck`) — no new soundness argument. **VK cut #1**
  (the PI slot).

* **B2 — subset resume.** Supply `umem_ref.root` as a committed-root PI; open
  declared addresses with `MapOp::Read` against it; this is the cross-cell read
  with the root sourced from a passed ref (§3.1-3.5). Reuses the **init** edge
  (`satisfied2U_init_root`, deployed). Fold into **VK cut #1** if landed
  together; otherwise VK cut #2. Targets **subset** soundness; names whole-image
  as the follow-up.

* **B3 — one-shot resume (optional, nullifier-gated).** Derive a nullifier from
  the `UmemRef`, spend it on resume via the `Nullifiers` domain (§3.6). Reuses
  `nullifier_fresh_sound` (deployed). May land in Stage C with the carriers.

* **B4 — whole-image resume (gated on the rotation).** The in-circuit
  whole-boundary sorted-leaf fold chip + the whole-boundary root pin discharging
  `boundary_whole_image_sem`'s `hpin` (§3.4). **This is the genuinely-new circuit
  surface** and the honest cost center; it rides the universal-map rotation and
  should NOT be promised as part of the cheap path.

* **B5 — dedicated verb (optional).** Only if a first-class auditable
  checkpoint/resume *verb* is wanted: repurpose a retired selector (MINT
  playbook, §4.1) and build the full per-effect rung. Deferrable indefinitely;
  the value-type + boundary-witness design already gives the capability.

The recommended Stage B floor is **B0 + B1 + B2**: the value type, checkpoint on
the final edge, subset resume on the init edge — all on deployed soundness
machinery, one VK cut, no new selector, no new AIR body. B4 is named as the
bounded tail for exact-continuation soundness.

---

## 6. The soundness obligations, enumerated

Every Stage B claim rests on the keystone's two edges (`UMEM-PRIMITIVE.md` §6)
applied at the checkpoint/resume seam. Named precisely:

1. **Final boundary is genuine (checkpoint).** The emitted `umem_ref.root` equals
   the genuine post-state boundary fold.
   - In-circuit: `boundary_root_from_memcheck` + `memcheck_pins_final`
     (`UniversalMemory.lean:429,281`) — DEPLOYED on the final edge.
   - Executor: the derive-and-refuse antibody (§2.2), the `RefreshDelegation`
     pattern. **New obligation:** the antibody must be wired and the root bound
     into `effects_hash`.

2. **Init boundary is bound (resume, subset).** The supplied init preimage is the
   genuine slice under `umem_ref.root`; a forged root/value refuses.
   - `boundary_init_root_derived` + `boundary_init_root_bound`
     (`UniversalMemory.lean:463,475`) → IR `satisfied2U_init_root` — DEPLOYED
     (the cross-cell read). **No new obligation** beyond sourcing the root from
     a `UmemRef` PI.

3. **No extra cells (resume, whole-image).** The committed slice holds nothing
   off the declared list.
   - `boundary_whole_image_sem` / `boundary_image_eq_of_root`
     (`UniversalMemory.lean:521,508`) → IR `satisfied2U_init_whole_image` — Lean
     PROVED. **Open obligation:** the in-circuit whole-boundary root-fold AIR
     that discharges `hpin` (B4; rides the rotation).

4. **Injectivity floor.** The root names exactly one content.
   - `Heap.root_injective` under the named `Poseidon2SpongeCR` floor — DEPLOYED;
     this is the one crypto hypothesis, entering exactly once (the same tooth as
     `boundary_init_root_bound` and `nullifier_fresh_binds_root`).
   - **Decision-point obligation:** carry the root at the 8-felt faithful
     commitment floor (§1.3), not the reserved 4 / not 31 bits.

5. **One-shot linearity (resume, linear variant).** A continuation ref resumes at
   most once.
   - `nullifier_fresh_sound` (`UniversalMemory.lean:611`), the `Nullifiers`
     domain — DEPLOYED. **New obligation (B3):** derive the ref's nullifier and
     spend it on resume.

6. **Conservation.** Checkpoint and subset/whole-image resume are
   `LinearityClass::Neutral` (no resource delta) — **no conservation rung
   required.** (If a dedicated value-bearing verb is added in B5, it needs its
   own 3-corner triangle, but the boundary-witness design does not.)

No Stage B rung requires a new soundness *argument*; rungs 1, 2, 4, 5 are
deployed theorems, rung 3 is a proved theorem awaiting its AIR, rung 6 is vacuous
by the Neutral classification. The single genuinely-new circuit artifact is the
B4 whole-boundary fold chip.

---

## 7. Open questions for the owner to decide

1. **Soundness bar for resume:** ship subset resume (B2, deployed) as the Stage B
   floor and name whole-image (B4) as the rotation-gated tail? Or hold Stage B
   until B4 so resume is exact-continuation-sound from day one?
2. **Root width:** confirm the 8-felt faithful commitment floor for the umem-ref
   root (§1.3). This is load-bearing and must not be defaulted.
3. **Linearity default:** idempotent citation (`Pin::At`-style) as the Stage B
   default, with one-shot (nullifier-gated, B3) deferred to the carriers in
   Stage C? Or both in Stage B?
4. **Verb vs restructure:** keep resume a boundary-witness restructure (no
   selector, §3.3), or reify it as a first-class auditable `ResumeUmem` verb
   (B5, MINT-playbook selector repurpose)?
5. **Data availability:** what is the DA model behind `availability` /
   `SturdyRef`? A missing preimage fail-closes soundly, but resume liveness needs
   a fetch path and a broken-promise analog (the `BrokenReason` vocabulary,
   `turn/src/pending.rs:84`, is the natural home in Stage C).
6. **Multi-domain refs:** Stage B fixes the single-domain shape and forbids
   multi-domain (§1.1). Confirm composition (`UVal::UmemRef`, recursive open)
   stays Stage D.
7. **VK cut batching:** confirm all Stage-B PI additions land in ONE VK cut
   (§4.2).

---

*Honest scope.* What EXISTS at HEAD: the single global umem and its five domains
(`turn/src/umem.rs`), the Blum trace + agreement check + no-chip-table row
(`descriptor_ir2.rs`), the final-boundary derivation and the init-binding
keystone (`boundary_root_from_memcheck` / `boundary_init_root_bound`,
`UniversalMemory.lean`), the per-cell heap projection + cross-cell read
(Stage A, `open_heap_against_committed`), and the deployed per-cell init-binding
leg (`satisfied2U_init_root`, the cross-cell-read circuit test). What Stage B
ADDS: the `UmemRef` value, the checkpoint output on the already-pinned final
edge, the subset resume sourcing its root from a passed ref, and — as the one
genuinely-new circuit artifact — the whole-boundary fold chip for exact-
continuation resume (B4, rotation-gated). Nothing here claims soundness that is
not deployed or backed by a named `#assert_axioms`-clean theorem.
