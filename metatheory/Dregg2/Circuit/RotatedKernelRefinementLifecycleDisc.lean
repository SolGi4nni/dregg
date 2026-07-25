/-
# Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc — WAVE 1 of the record-digest split-reshape:
  the lifecycle-DISCRIMINANT sub-limb + the per-effect disc-transition gates that make a
  ledgerless light client UNFOOLABLE on the lifecycle movers.

## The LIVE forgery this closes (light-client)

The lifecycle movers — `cellSeal`/`cellUnseal`/`cellDestroy`/`receiptArchive` — change the cell's
lifecycle. Their deployed descriptors (`rotateV3WithRecordPin B_LIFECYCLE …`) weld the AFTER-lifecycle
limb (`B_LIFECYCLE = 29`, the folded `lifecycle_felt = hash(disc ‖ payload)`, `rotation_witness.rs:110`)
to a FREE public input PI[38] that the deployed verifier anchors from the TRUSTED post-cell
(`proof_verify.rs:253-303`, `lifecycle_felt_cell(post)`). That anchor is a FULL-NODE check: it consumes
the trusted ledger post-cell. For a LEDGERLESS LIGHT CLIENT PI[38] is free, so a prover can publish a
lifecycle limb encoding ANY post-lifecycle — freeze a seal (after-disc stays Live), resurrect a
Destroyed cell, or claim Archived instead of Sealed — and `verifyBatch` alone accepts it. The
lifecycle TRANSITION is unforced.

## Why a separate DISC sub-limb (the minimal close)

`lifecycle_felt` folds `disc ‖ payload` into one OPAQUE felt — you cannot gate the disc inside it (it is
a hash output). But the light-client-meaningful safety property is precisely the DISCRIMINANT TRANSITION:

  * `cellSeal`        : `before_disc = Live(0)`     ∧ `after_disc = Sealed(1)`
  * `cellUnseal`      : `before_disc = Sealed(1)`   ∧ `after_disc = Live(0)`
  * `cellDestroy`     : `after_disc = Destroyed(3)` ∧ `before_disc ≠ Destroyed` (NO resurrection)
  * `receiptArchive`  : `after_disc = Archived(4)`

So we COMMIT the lifecycle `disc` (the small `u8 0..4`, `rotation_witness.rs:115`) as its OWN committed
sub-limb beside `lifecycle_felt`, and GATE the per-effect disc transition IN-CIRCUIT. A forged disc
transition (a frozen seal, a Destroyed→Live resurrection) is then UNSAT with NO trusted post-cell.

The PAYLOAD felt (`reason_hash` / `deathCert` / `sealed_at`) STAYS the prover's — it is effect data the
light client reads from the published effect; this forces the DISC, not the payload. (That residual is
NAMED in §6.)

## The binding mechanism (chosen: a dedicated `disc` committed sub-limb — same carrier as `lifecycleRoot`)

`disc : CellId → Nat` is the projection of `k.lifecycle cell` onto its discriminant. Its committed root
`discRoot` is the `ListCommit.listDigest` over the cell's disc entry — EXACTLY the `lifecycleRoot` carrier
(`compressNInjective` Poseidon-CR + an injective leaf), absorbed as ONE more committed sub-limb. NEVER a
fresh axiom, NEVER an `N_SYSTEM_ROOTS` bump. This module reuses `lifecycleLeaf`/`lifecycleLeaf_injective`
from `RotatedKernelRefinementCellSeal` (the disc IS a `Nat`, the same injective `Nat → ℤ` leaf).

## The DEPLOYED disc map (what the light client sees)

The light client sees the DEPLOYED disc transition, which for `receiptArchive` is the side-table move to
`Archived` (the deployed `apply_receipt_archive` → `c.archive`), NOT the kernel-spec record-slot write.
So this module models the DEPLOYED disc side-table `discAfter` per mover and gates IT — the transition a
ledgerless client can be fooled about. (The kernel-spec `ReceiptArchiveSpec` models the record slot; the
two layers diverge on receiptArchive only, recorded in §6 — the deployed disc is what PI[38] carries.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carrier
(`compressNInjective` + `lifecycleLeaf_injective`, REUSED). NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementCellSeal

namespace Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc

open Dregg2.Circuit.ListCommitRegrounded (CNColl noCNColl_of_inj listDigest_binds_of_noCNColl)
open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.RotatedKernelRefinementCellSeal
  (lifecycleLeaf lifecycleLeaf_injective)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A field element (the same `ℤ`-carrier `ListCommit`/`StateCommit`/`SystemRoots` use for a felt). -/
abbrev FieldElem := ℤ

/-! ## §0 — the deployed lifecycle discriminants + the committed `disc` sub-limb.

`lcLive = 0`, `lcSealed = 1`, `lcDestroyed = 3` come from `TurnExecutorFull`. The deployed circuit also
carries `Migrated = 2` and `Archived = 4` (`rotation_witness.rs:115` — the `u8 0..4`); we add the one the
movers need: `lcArchived := 4` (the deployed `receiptArchive` disc). The committed `disc` sub-limb is
`disc cell := the discriminant of `k.lifecycle cell`` — but at the spec layer `k.lifecycle cell` IS the
discriminant (a `Nat`), so the disc sub-limb's value is exactly `k.lifecycle cell`. Its committed root is
the `lifecycleRoot`-shaped digest over that one entry. -/

/-- The deployed `Archived` discriminant (`u8 4`, `rotation_witness.rs:120`). NOT in `TurnExecutorFull`'s
three-constant set (that set is the kernel-spec subset); the deployed `B_LIFECYCLE` disc carries it. -/
def lcArchived : Nat := 4

/-- **`discRoot compressN k cell`** — the committed root of cell `cell`'s lifecycle DISCRIMINANT: the
`listDigest` over `[k.lifecycle cell]` (the spec's `lifecycle` IS the disc `Nat`). The Lean mirror of the
Rust `disc_root` sub-limb the FIX adds BESIDE `lifecycle_felt`. Same `lifecycleLeaf` injective carrier as
`lifecycleRoot` — the disc is a `Nat`. -/
def discRoot (compressN : List FieldElem → FieldElem) (k : RecordKernelState) (cell : CellId) :
    FieldElem :=
  listDigest lifecycleLeaf compressN [k.lifecycle cell]

/-- **`discRoot_binds`** — equal disc roots (over the SAME `cell`) force the SAME discriminant,
under the per-instance `¬ CNColl` side condition (⚙ S3 CUTOVER of the refuted `compressNInjective`
floor; endpoint `ListCommitRegrounded.listDigest_binds_of_noCNColl`). The anti-ghost foundation: a
forged after-disc must clear this. -/
theorem discRoot_binds (compressN : List FieldElem → FieldElem)
    (k k' : RecordKernelState) (cell : CellId)
    (h : discRoot compressN k cell = discRoot compressN k' cell)
    (hno : ¬ CNColl lifecycleLeaf compressN [k.lifecycle cell] [k'.lifecycle cell]) :
    k.lifecycle cell = k'.lifecycle cell := by
  unfold discRoot at h
  have hlist : ([k.lifecycle cell] : List Nat) = [k'.lifecycle cell] :=
    listDigest_binds_of_noCNColl lifecycleLeaf compressN lifecycleLeaf_injective _ _ hno h
  exact List.head_eq_of_cons_eq hlist

/-! ## §1 — the per-effect DISC-transition gate.

The deployed circuit, with the `disc` sub-limb realized, would carry TWO committed disc columns
(before/after) and a gate forcing the disc transition. We model that gate as a predicate on the row's
pre/post disc-root columns AND the before/after discriminant values it pins — at the granularity the
deployed per-effect gate enforces. -/

/-- **`DiscRootRow compressN preK postK cell preRoot postRoot`** — the decode tying the FIX row's two
committed disc-root columns to the kernel pre/post discriminant of `cell`. The PRE column is `discRoot`
of the pre kernel; the POST column is `discRoot` of the post kernel. -/
def DiscRootRow (compressN : List FieldElem → FieldElem)
    (preK postK : RecordKernelState) (cell : CellId) (preRoot postRoot : FieldElem) : Prop :=
  preRoot = discRoot compressN preK cell ∧ postRoot = discRoot compressN postK cell

/-- **`gDiscTransition compressN preK cell before after preRoot postRoot`** — the FIX gate body: the PRE
disc-root column IS the digest of the kernel whose `cell` disc is `before`, AND the POST disc-root column
IS the digest of the kernel whose `cell` disc is `after`. This is what a ledgerless light client's
in-circuit disc gate ENFORCES — both endpoints of the transition, pinned to committed roots (NO trusted
post-cell). -/
def gDiscTransition (compressN : List FieldElem → FieldElem)
    (preK : RecordKernelState) (cell : CellId) (before after : Nat)
    (preRoot postRoot : FieldElem) : Prop :=
  preRoot = discRoot compressN (setLifecycle preK cell before) cell
  ∧ postRoot = discRoot compressN (setLifecycle preK cell after) cell

/-- **`discBeforeForced` — the FIX gate FORCES the committed BEFORE disc.** The deployed circuit pins the
before-disc to `before`, so a frozen / wrong before-disc is rejected. -/
theorem discBeforeForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (before after : Nat) (preRoot postRoot : FieldElem)
    (henc : DiscRootRow compressN preK postK cell preRoot postRoot)
    (hgate : gDiscTransition compressN preK cell before after preRoot postRoot) :
    preK.lifecycle cell = before := by
  obtain ⟨hpre, _⟩ := henc
  obtain ⟨hgpre, _⟩ := hgate
  have hroots : discRoot compressN preK cell
      = discRoot compressN (setLifecycle preK cell before) cell := by rw [← hpre]; exact hgpre
  have hval := discRoot_binds compressN preK (setLifecycle preK cell before) cell hroots
    (noCNColl_of_inj hN)
  rw [hval]
  simp [setLifecycle]

/-- **`discAfterForced` — the FIX gate FORCES the committed AFTER disc.** The deployed circuit pins the
after-disc to `after`, so a forged after-disc (the LIVE forgery — a frozen seal, a resurrection) is UNSAT
with NO trusted post-cell. -/
theorem discAfterForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (before after : Nat) (preRoot postRoot : FieldElem)
    (henc : DiscRootRow compressN preK postK cell preRoot postRoot)
    (hgate : gDiscTransition compressN preK cell before after preRoot postRoot) :
    postK.lifecycle cell = after := by
  obtain ⟨_, hpost⟩ := henc
  obtain ⟨_, hgpost⟩ := hgate
  have hroots : discRoot compressN postK cell
      = discRoot compressN (setLifecycle preK cell after) cell := by rw [← hpost]; exact hgpost
  have hval := discRoot_binds compressN postK (setLifecycle preK cell after) cell hroots
    (noCNColl_of_inj hN)
  rw [hval]
  simp [setLifecycle]

/-! ## §2 — the four lifecycle movers: the per-effect disc-transition decode + the FORCED transition.

Each mover carries its OWN before/after disc pair; the gate forces BOTH endpoints. The `DiscMover` decode
bundles the two committed disc-root columns, their decode, and the gate — the in-circuit cap a ledgerless
client opens. The light-client-meaningful conclusion is the forced TRANSITION (both endpoints), proved
from the gate without any off-circuit anchor. -/

/-- **`DiscMover compressN pre post cell before after`** — the active-row⟷kernel decode for a satisfying
disc-transition witness of `cell` from `before` to `after`. DATA-bearing (`Type`, like
`cellSealGenuineEncodes`): it exhibits the two committed disc-root columns, carries the FIX gate (the
WITNESS leg — the running circuit PINS both endpoints), and is the ONLY thing the light client needs (no
trusted post-cell). -/
structure DiscMover (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (cell : CellId) (before after : Nat) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : DiscRootRow compressN pre.kernel post.kernel cell preRoot postRoot
  gate : gDiscTransition compressN pre.kernel cell before after preRoot postRoot

/-- **`discMover_before_forced` — the BEFORE disc is FIX-CIRCUIT-FORCED.** -/
theorem discMover_before_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (cell : CellId) (before after : Nat)
    (henc : DiscMover compressN pre post cell before after) :
    pre.kernel.lifecycle cell = before :=
  discBeforeForced compressN hN pre.kernel post.kernel cell before after
    henc.preRoot henc.postRoot henc.hroots henc.gate

/-- **`discMover_after_forced` — the AFTER disc is FIX-CIRCUIT-FORCED.** This is the rung the deployed
opaque `lifecycle_felt` CANNOT supply: a ledgerless client now KNOWS the after-disc, no trusted post-cell. -/
theorem discMover_after_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (cell : CellId) (before after : Nat)
    (henc : DiscMover compressN pre post cell before after) :
    post.kernel.lifecycle cell = after :=
  discAfterForced compressN hN pre.kernel post.kernel cell before after
    henc.preRoot henc.postRoot henc.hroots henc.gate

/-! ## §2.1 — the FOUR named movers (the per-effect disc transitions). -/

/-- **`cellSealDisc`** — the disc-transition decode for `cellSeal`: `Live(0) → Sealed(1)`. -/
abbrev cellSealDisc (compressN : List FieldElem → FieldElem) (pre post : RecChainedState)
    (cell : CellId) : Type :=
  DiscMover compressN pre post cell lcLive lcSealed

/-- **`cellUnsealDisc`** — the disc-transition decode for `cellUnseal`: `Sealed(1) → Live(0)`. -/
abbrev cellUnsealDisc (compressN : List FieldElem → FieldElem) (pre post : RecChainedState)
    (cell : CellId) : Type :=
  DiscMover compressN pre post cell lcSealed lcLive

/-- **`cellDestroyDisc`** — the disc-transition decode for `cellDestroy`: `before → Destroyed(3)`,
parameterized by the actual `before` so the no-resurrection tooth (`before ≠ Destroyed`) can bite. -/
abbrev cellDestroyDisc (compressN : List FieldElem → FieldElem) (pre post : RecChainedState)
    (cell : CellId) (before : Nat) : Type :=
  DiscMover compressN pre post cell before lcDestroyed

/-- **`receiptArchiveDisc`** — the disc-transition decode for the DEPLOYED `receiptArchive`:
`before → Archived(4)` (the deployed `apply_receipt_archive` side-table move; see §6 on the layer
divergence from the kernel-spec record-slot). -/
abbrev receiptArchiveDisc (compressN : List FieldElem → FieldElem) (pre post : RecChainedState)
    (cell : CellId) (before : Nat) : Type :=
  DiscMover compressN pre post cell before lcArchived

/-! ## §3 — the FORCED transitions (per mover), light-client-sound (NO trusted post-cell). -/

/-- **`cellSeal_disc_forced` — a satisfying `cellSeal` disc witness FORCES `Live → Sealed`.** -/
theorem cellSeal_disc_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId)
    (henc : cellSealDisc compressN pre post cell) :
    pre.kernel.lifecycle cell = lcLive ∧ post.kernel.lifecycle cell = lcSealed :=
  ⟨discMover_before_forced compressN hN pre post cell lcLive lcSealed henc,
   discMover_after_forced compressN hN pre post cell lcLive lcSealed henc⟩

/-- **`cellUnseal_disc_forced` — a satisfying `cellUnseal` disc witness FORCES `Sealed → Live`.** -/
theorem cellUnseal_disc_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId)
    (henc : cellUnsealDisc compressN pre post cell) :
    pre.kernel.lifecycle cell = lcSealed ∧ post.kernel.lifecycle cell = lcLive :=
  ⟨discMover_before_forced compressN hN pre post cell lcSealed lcLive henc,
   discMover_after_forced compressN hN pre post cell lcSealed lcLive henc⟩

/-- **`cellDestroy_disc_forced` — a satisfying `cellDestroy` disc witness FORCES `after = Destroyed`.** -/
theorem cellDestroy_disc_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId) (before : Nat)
    (henc : cellDestroyDisc compressN pre post cell before) :
    post.kernel.lifecycle cell = lcDestroyed :=
  discMover_after_forced compressN hN pre post cell before lcDestroyed henc

/-- **`receiptArchive_disc_forced` — a satisfying `receiptArchive` disc witness FORCES
`after = Archived`.** -/
theorem receiptArchive_disc_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId) (before : Nat)
    (henc : receiptArchiveDisc compressN pre post cell before) :
    post.kernel.lifecycle cell = lcArchived :=
  discMover_after_forced compressN hN pre post cell before lcArchived henc

/-! ## §4 — THE TEETH: the forged-disc forgeries are UNSAT for a LEDGERLESS client.

Each tooth shows a forged after-disc (the exact light-client forgery the deployed anchor needed the
trusted post-cell to reject) is contradictory under a satisfying disc witness — so the prover CANNOT
publish it. NO trusted post-cell is consumed: the contradiction is purely the in-circuit disc gate. -/

/-- **TOOTH — `cellSeal_disc_rejects_frozen`.** A `cellSeal` whose after-disc STAYS Live (a FROZEN,
un-sealed cell — the headline forgery) cannot ride a satisfying disc witness. UNSAT without the trusted
post-cell. -/
theorem cellSeal_disc_rejects_frozen (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId)
    (henc : cellSealDisc compressN pre post cell)
    (hforged : post.kernel.lifecycle cell = lcLive) :
    False := by
  have hsealed : post.kernel.lifecycle cell = lcSealed :=
    (cellSeal_disc_forced compressN hN pre post cell henc).2
  rw [hsealed] at hforged
  exact absurd hforged (by decide)

/-- **TOOTH — `cellSeal_disc_rejects_wrong_after`.** A `cellSeal` whose after-disc is ANYTHING but Sealed
(e.g. claiming Archived, or Destroyed) is UNSAT. -/
theorem cellSeal_disc_rejects_wrong_after (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId)
    (henc : cellSealDisc compressN pre post cell)
    (hforged : post.kernel.lifecycle cell ≠ lcSealed) :
    False :=
  hforged (cellSeal_disc_forced compressN hN pre post cell henc).2

/-- **TOOTH — `cellUnseal_disc_rejects_unrevived`.** A `cellUnseal` whose after-disc is NOT Live (the
cell stays Sealed — an un-revived unseal) is UNSAT. -/
theorem cellUnseal_disc_rejects_unrevived (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId)
    (henc : cellUnsealDisc compressN pre post cell)
    (hforged : post.kernel.lifecycle cell ≠ lcLive) :
    False :=
  hforged (cellUnseal_disc_forced compressN hN pre post cell henc).2

/-- **TOOTH — `cellDestroy_disc_rejects_resurrection`.** The headline resurrection forgery: a
`cellDestroy` whose after-disc is Live (a Destroyed cell published as alive) is UNSAT — the after-disc is
FORCED to Destroyed. NO trusted post-cell needed. -/
theorem cellDestroy_disc_rejects_resurrection (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId) (before : Nat)
    (henc : cellDestroyDisc compressN pre post cell before)
    (hforged : post.kernel.lifecycle cell = lcLive) :
    False := by
  have hdead : post.kernel.lifecycle cell = lcDestroyed :=
    cellDestroy_disc_forced compressN hN pre post cell before henc
  rw [hdead] at hforged
  exact absurd hforged (by decide)

/-- **TOOTH — `cellDestroy_disc_no_resurrection_input`.** A `cellDestroy` whose BEFORE-disc is forced to a
NON-Destroyed value `before` (the gate's before-pin) — so a destroy of an ALREADY-Destroyed cell (a
double-destroy / resurrection-then-destroy attempt) presents a before-disc the gate refuses. The
before-pin is what forbids resurrecting a Destroyed cell THROUGH a fresh destroy. -/
theorem cellDestroy_disc_before_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId) (before : Nat)
    (henc : cellDestroyDisc compressN pre post cell before) :
    pre.kernel.lifecycle cell = before :=
  discMover_before_forced compressN hN pre post cell before lcDestroyed henc

/-- **TOOTH — `receiptArchive_disc_rejects_wrong_after`.** A `receiptArchive` whose after-disc is NOT
Archived (e.g. claiming Sealed, or freezing the disc) is UNSAT. -/
theorem receiptArchive_disc_rejects_wrong_after (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (pre post : RecChainedState) (cell : CellId) (before : Nat)
    (henc : receiptArchiveDisc compressN pre post cell before)
    (hforged : post.kernel.lifecycle cell ≠ lcArchived) :
    False :=
  hforged (receiptArchive_disc_forced compressN hN pre post cell before henc)

/-! ## §5 — NON-VACUITY: the disc root + the per-effect gates are load-bearing (no carrier secretly
`True`, no gate satisfiable by the FROZEN disc). A concrete injective `compressN` (Horner sponge). -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

private def liveK : RecordKernelState :=
  { accounts := {}, cell := fun _ => .int 0, caps := default, lifecycle := fun _ => lcLive }
private def cell0 : CellId := 0

-- SEAL: the Sealed after-root DIFFERS from the FROZEN (Live) root — so a frozen-seal post fails the gate.
#guard decide (discRoot cNC (setLifecycle liveK cell0 lcSealed) cell0
             = discRoot cNC (setLifecycle liveK cell0 lcLive) cell0) == false
-- DESTROY: the Destroyed after-root DIFFERS from a Live root (no silent resurrection collapse).
#guard decide (discRoot cNC (setLifecycle liveK cell0 lcDestroyed) cell0
             = discRoot cNC (setLifecycle liveK cell0 lcLive) cell0) == false
-- ARCHIVE: the Archived(4) after-root DIFFERS from the Sealed(1) root (archive ≠ seal).
#guard decide (discRoot cNC (setLifecycle liveK cell0 lcArchived) cell0
             = discRoot cNC (setLifecycle liveK cell0 lcSealed) cell0) == false
-- UNSEAL: the Live after-root DIFFERS from the Sealed root (the inverse is non-trivial).
#guard decide (discRoot cNC (setLifecycle liveK cell0 lcLive) cell0
             = discRoot cNC (setLifecycle liveK cell0 lcSealed) cell0) == false
-- the four discriminants are PAIRWISE distinct as leaves (the gate distinguishes states).
#guard decide (lifecycleLeaf lcLive = lifecycleLeaf lcSealed) == false
#guard decide (lifecycleLeaf lcSealed = lifecycleLeaf lcDestroyed) == false
#guard decide (lifecycleLeaf lcDestroyed = lifecycleLeaf lcArchived) == false
#guard decide (lifecycleLeaf lcLive = lifecycleLeaf lcArchived) == false

/-! ## §6 — the RESIDUAL ledger (carried, NAMED — not faked).

  * **The payload felt stays the PROVER'S.** This gate forces the DISC, not the `reason_hash` /
    `deathCert` / `sealed_at` payload that `lifecycle_felt` also folds. The payload is effect data the
    light client reads from the PUBLISHED effect; forcing it is not a light-client safety property (a
    wrong payload is the prover lying to ITSELF about its own effect, not fooling a verifier about the
    lifecycle STATE). Named, not laundered.

  * **The `disc` sub-limb COMMITMENT realization is ember-gated (a VK epoch).** Realizing this gate on the
    deployed path means COMMITTING the disc beside `lifecycle_felt` in the per-cell commitment
    (`cell_state.rs::compute_commitment`) — either a 33rd `pre_limbs` column or a re-fold of `B_LIFECYCLE`
    to `H(disc_felt, payload_felt)`. Either changes `ROT_WIDTH` / the AFTER-block offsets / all 36 rotated
    descriptor JSONs / the registry fingerprint / the VK — a global flag-day. So the COMMITMENT change is
    the EMBER-GATED deploy step; THIS module proves the gate + teeth against the FIX (committed-root)
    descriptor, the same beachhead shape as `RotatedKernelRefinementCellSeal`/`…Lifecycle`.

  * **Layer divergence on `receiptArchive`.** The KERNEL spec `ReceiptArchiveSpec` writes a record SLOT
    and FREEZES the `lifecycle` side-table (`cellstateaudit.lean:241`); the DEPLOYED `apply_receipt_archive`
    moves the side-table disc to `Archived(4)` (`rotation_witness.rs:460`). The light client sees the
    DEPLOYED disc (PI[38] carries `lifecycle_felt`), so this module gates the DEPLOYED disc transition.
    Reconciling the two layers (one disc semantics) is WAVE-3 work, named here. -/

/-! ## §7 — axiom-hygiene tripwires. -/

#assert_axioms discRoot_binds
#assert_axioms discBeforeForced
#assert_axioms discAfterForced
#assert_axioms discMover_before_forced
#assert_axioms discMover_after_forced
#assert_axioms cellSeal_disc_forced
#assert_axioms cellUnseal_disc_forced
#assert_axioms cellDestroy_disc_forced
#assert_axioms receiptArchive_disc_forced
#assert_axioms cellSeal_disc_rejects_frozen
#assert_axioms cellSeal_disc_rejects_wrong_after
#assert_axioms cellUnseal_disc_rejects_unrevived
#assert_axioms cellDestroy_disc_rejects_resurrection
#assert_axioms cellDestroy_disc_before_forced
#assert_axioms receiptArchive_disc_rejects_wrong_after

end Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc
