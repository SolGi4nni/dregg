/-
# Dregg2.Circuit.Argus.Effects.CellDestroy — the cell-LIFECYCLE DESTROY weld: cellDestroy as an
Argus IR term, welded against its OWN full-state dual descriptor.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell `setCell`). `Argus/Effects/BalanceA.lean` showed the STRONGER
surface — welding directly against a `*_full_sound` whose conclusion is the WHOLE post-state — by
routing the executor through an INDEPENDENT executor⟺spec corner. This module welds the cell DESTROY
effect `cellDestroy` the SAME (strong) way, in its own disjoint file (it imports the Argus IR + the
audited `cellDestroyA` dual instance + the independent `Spec/celllifecycle` corner read-only, and owns
only its own declarations — it edits no other Argus file).

## What cellDestroy does (the two SIDE-TABLE writes — NOT `cell`/`bal`)

The chained executor `cellDestroyChainA` (`TurnExecutorFull.lean:1675`) is, on the nose:

    cellDestroyChainA s actor cell certHash
      = if stateAuthB s.kernel.caps actor cell ∧ s.kernel.lifecycle cell ≠ lcDestroyed then
          some { kernel := { (setLifecycle s.kernel cell lcDestroyed) with
                              deathCert := fun c => if c = cell then certHash else s.kernel.deathCert c },
                 log    := { actor, src := cell, dst := cell, amt := 0 } :: s.log }
        else none

so a committed destroy (a) FLIPS `cell`'s `lifecycle` side-table entry to `Destroyed` (discriminant `3`),
(b) BINDS `certHash` into `cell`'s `deathCert` side-table, prepends one self-targeted receipt, and FREEZES
every other RecordKernelState field — balance-NEUTRAL (no `cell`/`bal` motion). The gate is
authority-over-cell ∧ NON-terminal (a cell already Destroyed is `Terminal`-rejected,
`cellDestroyChainA_terminal_rejects`).

Because it touches the two per-cell function registries `lifecycle` and `deathCert`, the IR body's writes
are the §A `setLifecycle` + `setDeathCert` primitives (the per-cell `CellId → Nat` registry writes) — NOT
`setCell`/`setBal`. No new IR primitive is needed: the two component-write constructors the IR already
carries (`Stmt.lean §A`) are exactly the shapes a two-side-table effect assembles.

## What this module proves (the BalanceA-grade strong pair)

  1. **The cornerstone (executor IS the term):** `interp_cellDestroyStmt_eq_destroyKernelStep` — the IR
     term's `interp` is, on the nose, the RAW-kernel destroy step `destroyKernelStep` (the kernel image
     of `cellDestroyChainA`, via `setLifecycle` + the `deathCert` bind). New, standalone, the lifecycle
     analog of `interp_balanceAStmt_eq_recKExecAsset`.

  2. **The chained lift:** `interp_cellDestroyStmt_chained` — lift the raw-kernel cornerstone to the
     CHAINED executor `execFullA s (.cellDestroyA …)` the standalone dual descriptor speaks about
     (kernel + the one receipt row), exactly as BalanceA §3 lifts to `execFullA`.

  3. **The compile weld against cellDestroy's OWN full-state descriptor:** `cellDestroy_compile_sound` —
     a satisfying witness of the audited DUAL `Surface2` circuit `cellDestroyA_full_sound`
     (`Inst/cellDestroyA.lean`, whose touched components are the WHOLE `lifecycle` + `deathCert`
     functions, `funcComponent` full-function digests) AGREES with the FULL post-state the IR term's
     executor produces — all 17 RecordKernelState fields (`lifecycle` flipped, `deathCert` bound, every
     other field frozen) AND the receipt log, the complete `CellDestroySpec`. Strictly stronger than a
     per-cell projection: both the circuit side (`cellDestroyA_full_sound ⇒ CellDestroySpec`) and the
     executor side (`cellDestroy_iff_spec`, executor ⟺ `CellDestroySpec`) name the SAME
     `CellDestroySpec`, so they PROVABLY agree on the whole state.

## SURFACE (precise — do NOT over-read)

  * **Surface = FULL-STATE `CellDestroySpec` (the dual `Surface2` descriptor), NOT the per-cell EffectVM
    row.** A SEPARATE per-cell EffectVM descriptor for cellDestroy exists
    (`EffectVmEmitCellDestroy.cellDestroyVmDescriptor`) — but it carries a REAL nonce-tick divergence
    (it ticks the runtime row nonce while freezing the economic block) AND it is OFF-ROW for the
    whole point of the effect: the lifecycle flip / deathCert bind / receipt are NOT representable as
    EffectVM state-block columns (`cellDestroy_offrow_unenforced`). The destroy SOUNDNESS lives ONLY in
    `cellDestroyA_full_sound` (that module's own header says so). So this weld deliberately targets the
    DUAL full-state descriptor — the sound surface — where there is **NO divergence**: the
    dual descriptor freezes the cell record + bal (it touches ONLY `lifecycle`/`deathCert`), exactly as
    `CellDestroySpec` and the executor do. `divergence = none`.

  * **The whole-function digest assumption** (`Function.Injective DLif`/`DDC` for the lifecycle/deathCert
    component digests, `RestIffNoLifecycleDeathCert S.RH`, `logHashInjective S.LH`) enters ONLY inside the
    reused `cellDestroyA_full_sound` as named hypotheses — the realizable Poseidon-CR / collision-freeness
    portals — not as fresh axioms in the welded conclusion's statement.

## Axiom hygiene

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no
`:= True` vacuity, no `native_decide`, no weakening-that-just-typechecks: the conclusion is the genuine
full-state agreement the reused dual soundness proves. Imports are read-only; this file owns only itself
and edits no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState

namespace Dregg2.Circuit.Argus.Effects.CellDestroy

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (lcDestroyed setLifecycle cellDestroyChainA execFullA)
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Argus (RecStmt interp)
-- The dual full-state descriptor + its soundness live in `Inst.CellDestroyA`; the independent
-- executor⟺spec corner + the declarative `CellDestroySpec`/`CellDestroyGuard`/`destroyKernelMap` live in
-- `Spec.CellLifecycle`. The realizability portals: `Surface2`/`logHashInjective` (StateCommit /
-- EffectCommit2), `satisfiedE2Dual`/`encodeE2Dual` (EffectCommit2Dual).
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2Dual (satisfiedE2Dual encodeE2Dual)
open Dregg2.Circuit.Spec.CellLifecycle
  (cellLifecycleReceipt CellDestroyGuard CellDestroySpec destroyKernelMap destroyDeathCertMap
   cellDestroy_iff_spec)
open Dregg2.Circuit.Inst.CellDestroyA
  (CellDestroyArgs cellDestroyE cellDestroyA_full_sound RestIffNoLifecycleDeathCert)

/-! ## §1 — the cellDestroy effect as an Argus IR term (gate, then the TWO side-table writes).

`cellDestroyChainA`'s kernel action, ABSTRACTED off the receipt chain, is the RAW-kernel step

    destroyKernelStep k actor cell certHash
      = if <auth ∧ non-terminal> then
          some { (setLifecycle k cell lcDestroyed) with deathCert := <bind certHash at cell> }
        else none

We capture it term-for-term: a `Bool` `guard` of the EXACT two conjuncts, then `setLifecycle` (flip the
`lifecycle` registry at `cell` to `lcDestroyed`) sequenced with `setDeathCert` (bind `certHash` at `cell`
in the `deathCert` registry). The two writes through `seq` are the side-table analog of BalanceA's single
`setBal`: the SECOND write (`setDeathCert`) reads its leaf on the INTERMEDIATE state `k₁` produced by the
first (`setLifecycle`), and because `setLifecycle` does NOT touch `deathCert`, `k₁.deathCert = k.deathCert`,
so the bind lands on the ORIGINAL death-cert registry — matching `cellDestroyChainA` exactly. -/

/-- The cellDestroy admissibility gate as a `Bool` — exactly `cellDestroyChainA`'s `if` (the two
conjuncts: self-authority over `cell`, and `cell` NOT already Destroyed — a Live OR Sealed cell may be
destroyed, terminal cells are rejected). -/
def cellDestroyGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell && (k.lifecycle cell != lcDestroyed)

/-- The RAW-kernel destroy step — the kernel image of `cellDestroyChainA` (flip lifecycle + bind death
cert), abstracted off the receipt chain. This is what `interp` of the IR term refines to (the chained
layer adds only the receipt-log prepend, §2-lift). DEFINITIONALLY `destroyKernelMap k cell certHash`
under the gate (see `interp_cellDestroyStmt_eq_destroyKernelStep`). -/
def destroyKernelStep (k : RecordKernelState) (actor cell : CellId) (certHash : Nat) :
    Option RecordKernelState :=
  if cellDestroyGuard actor cell k then
    some { (setLifecycle k cell lcDestroyed) with
            deathCert := fun c => if c = cell then certHash else k.deathCert c }
  else none

/-- **The cellDestroy effect as an IR term: gate, then the TWO side-table writes.** Mirrors the escrow
two-component shape (gate, then `seq` of two component writes) but on the per-cell function registries:
`setLifecycle` flips `cell` to Destroyed, then `setDeathCert` binds `certHash` at `cell`. The §A
`setLifecycle`/`setDeathCert` primitives (`Stmt.lean`) are exactly the shapes a two-side-table effect
assembles — NO new constructor needed. -/
def cellDestroyStmt (actor cell : CellId) (certHash : Nat) : RecStmt :=
  RecStmt.seq (RecStmt.guard (cellDestroyGuard actor cell))
    (RecStmt.seq
      (RecStmt.setLifecycle (fun k => fun c => if c = cell then lcDestroyed else k.lifecycle c))
      (RecStmt.setDeathCert (fun k => fun c => if c = cell then certHash else k.deathCert c)))

/-! ## §2 — the cornerstone: `interp` of the cellDestroy term IS the raw-kernel step `destroyKernelStep`. -/

/-- **The two-write body IS the destroy kernel map.** Running the body `seq (setLifecycle <flip>)
(setDeathCert <bind>)` on a state `k` produces exactly the destroy post-kernel
`{ (setLifecycle k cell lcDestroyed) with deathCert := <bind certHash at cell> }`. The side-table analog of
BalanceA's single-write reduction, and the load-bearing step the single-write effects never had: the
`setDeathCert` bind reads the intermediate state (post-`setLifecycle`), whose `deathCert` is still
`k.deathCert` (because `setLifecycle` writes only `lifecycle`), so the bind lands on the original registry.
The `setLifecycle` leaf `fun c => if c = cell then lcDestroyed else k.lifecycle c` is DEFINITIONALLY
`(setLifecycle k cell lcDestroyed).lifecycle`. -/
theorem cellDestroyBody_eq (k : RecordKernelState) (cell : CellId) (certHash : Nat) :
    interp (RecStmt.seq
        (RecStmt.setLifecycle (fun k => fun c => if c = cell then lcDestroyed else k.lifecycle c))
        (RecStmt.setDeathCert (fun k => fun c => if c = cell then certHash else k.deathCert c))) k
      = some { (setLifecycle k cell lcDestroyed) with
                deathCert := fun c => if c = cell then certHash else k.deathCert c } := by
  simp only [interp, Option.bind, setLifecycle]

/-- **The cornerstone (cell-lifecycle DESTROY).** `interp` of the cellDestroy term IS the raw-kernel
destroy step `destroyKernelStep` — the same partial function, by construction, exactly as the
transfer/mint/burn/balanceA cornerstones, now over the TWO per-cell side-tables (`lifecycle` flipped to
Destroyed + `deathCert` bound) via `setLifecycle`/`setDeathCert`. This is the executor-refinement: the
executor IS the meaning of the term. -/
theorem interp_cellDestroyStmt_eq_destroyKernelStep (actor cell : CellId) (certHash : Nat)
    (k : RecordKernelState) :
    interp (cellDestroyStmt actor cell certHash) k = destroyKernelStep k actor cell certHash := by
  simp only [cellDestroyStmt, interp]
  unfold destroyKernelStep
  by_cases hg : cellDestroyGuard actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the two-write body reduces (the `setLifecycle` flip
    -- then the `setDeathCert` bind — whose `deathCert` read is still `k.deathCert`), giving exactly the
    -- destroy post-kernel; the RHS `if` opens on the same `Bool` gate.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos hg]
    simp only [setLifecycle]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the same gate.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg hg]

#assert_axioms interp_cellDestroyStmt_eq_destroyKernelStep

/-! ## §3 — lifting the cornerstone to the CHAINED executor `execFullA` / `cellDestroyChainA`.

The standalone dual descriptor (§5) is keyed on the CHAINED executor `execFullA s (.cellDestroyA …) =
cellDestroyChainA s actor cell certHash` over `RecChainedState` (kernel + receipt log). The §2 cornerstone
is over the RAW kernel step `destroyKernelStep`. The chained layer is exactly `destroyKernelStep` PLUS the
receipt-log prepend `cellLifecycleReceipt actor cell :: s.log` — and crucially the chained gate reads the
SAME two conjuncts (`stateAuthB`/non-terminal) off `s.kernel`, with NO extra side-condition (unlike
balanceA, whose chained layer added a dst-`acceptsEffects` gate). So the lift is unconditional. -/

/-- **`destroyKernelStep_gate` — the raw step's gate is the chained gate verbatim.** A committed raw
destroy means the chained gate holds; bridges the §2 RAW step to `cellDestroyChainA`'s `if`. -/
theorem destroyKernelStep_some_gate {k k' : RecordKernelState} {actor cell : CellId} {certHash : Nat}
    (h : destroyKernelStep k actor cell certHash = some k') :
    stateAuthB k.caps actor cell = true ∧ (k.lifecycle cell != lcDestroyed) = true := by
  unfold destroyKernelStep at h
  by_cases hg : cellDestroyGuard actor cell k = true
  · simpa only [cellDestroyGuard, Bool.and_eq_true] using hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`interp_cellDestroyStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the §2 cornerstone commits on the kernel (`interp (cellDestroyStmt actor cell certHash) s.kernel = some k'`),
the unified action executor `execFullA s (.cellDestroyA actor cell certHash)` commits to the chained state
`⟨k', cellLifecycleReceipt actor cell :: s.log⟩`. So the Argus term's kernel meaning lifts to the chained
executor the standalone dual descriptor speaks about — UNCONDITIONALLY (destroy's gate is fully kernel-local,
no carried side-condition). -/
theorem interp_cellDestroyStmt_chained
    (s : RecChainedState) (actor cell : CellId) (certHash : Nat) (k' : RecordKernelState)
    (hexec : interp (cellDestroyStmt actor cell certHash) s.kernel = some k') :
    execFullA s (.cellDestroyA actor cell certHash)
      = some { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `destroyKernelStep`.
  rw [interp_cellDestroyStmt_eq_destroyKernelStep] at hexec
  -- `execFullA s (.cellDestroyA …)` reduces to `cellDestroyChainA s actor cell certHash`; on the gate
  -- (which `hexec` witnesses) it opens to the post-state `hexec` pins, with the receipt prepended.
  show cellDestroyChainA s actor cell certHash = some { kernel := k', log := cellLifecycleReceipt actor cell :: s.log }
  obtain ⟨hauth, hterm⟩ := destroyKernelStep_some_gate hexec
  unfold cellDestroyChainA
  rw [if_pos ⟨hauth, hterm⟩]
  -- the kernel images coincide: `cellDestroyChainA`'s commit kernel is exactly `destroyKernelStep`'s.
  have hk : { (setLifecycle s.kernel cell lcDestroyed) with
                deathCert := fun c => if c = cell then certHash else s.kernel.deathCert c } = k' := by
    have := hexec
    unfold destroyKernelStep at this
    rw [if_pos (by simpa only [cellDestroyGuard, Bool.and_eq_true] using ⟨hauth, hterm⟩)] at this
    exact (Option.some.injEq _ _).mp this
  rw [hk]; rfl

#assert_axioms interp_cellDestroyStmt_chained

/-! ## §4 — NON-VACUITY of the cornerstone: the IR term DESTROYS (both side-tables move),
and the gate REJECTS forged inputs (fail-closed).

The cornerstone would be hollow if `cellDestroyStmt` never committed, if the writes were no-ops, or if the
gate admitted everything. A concrete two-cell kernel `kCD` (cells 0,1 live; account 0 holds two node caps)
exercises a real destroy; the rejection lemmas show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts (lifecycle defaults Live = 0),
account 0 holds `node 0`/`node 1` caps (so `stateAuthB 0 0` accepts), an empty death-cert registry. -/
def kCD : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- **NON-VACUITY (the lifecycle flip is OBSERVABLE).** A committed destroy flips cell `0`'s lifecycle from
Live (`0`) to Destroyed (`lcDestroyed = 3`) — the side-table write is a real, observable state edit. -/
theorem cellDestroyStmt_flips_lifecycle :
    (interp (cellDestroyStmt 0 0 42) kCD).map (fun k => k.lifecycle 0) = some lcDestroyed := by
  rw [interp_cellDestroyStmt_eq_destroyKernelStep]
  decide

/-- **NON-VACUITY (the death-cert bind is OBSERVABLE).** A committed destroy binds `certHash = 42` into
cell `0`'s `deathCert` registry, where before it held `0` — the second side-table write is real. -/
theorem cellDestroyStmt_binds_deathCert :
    (interp (cellDestroyStmt 0 0 42) kCD).map (fun k => k.deathCert 0) = some 42 := by
  rw [interp_cellDestroyStmt_eq_destroyKernelStep]
  decide

/-- **NON-VACUITY (other cell untouched).** Destroying cell `0` leaves cell `1`'s lifecycle at Live (`0`) —
the `setLifecycle` flip writes ONLY the targeted cell (the frame holds). -/
theorem cellDestroyStmt_other_cell_untouched :
    (interp (cellDestroyStmt 0 0 42) kCD).map (fun k => k.lifecycle 1) = some 0 := by
  rw [interp_cellDestroyStmt_eq_destroyKernelStep]
  decide

/-- **NON-VACUITY (fail-closed: unauthorized).** A destroy attempted by an actor with NO authority over
cell `0` (account `1`, holding no caps) does NOT commit — the AUTHORITY leg fails. No cell is destroyed. -/
theorem cellDestroyStmt_rejects_unauthorized :
    interp (cellDestroyStmt 1 0 42) kCD = none := by
  rw [interp_cellDestroyStmt_eq_destroyKernelStep]
  decide

/-- **NON-VACUITY (fail-closed: terminal / no re-destroy).** Destroying cell `0`, then attempting to
re-destroy it, does NOT commit — the NON-TERMINAL leg fails on the already-Destroyed cell. dregg1's
`Terminal` rejection, in-band. -/
theorem cellDestroyStmt_rejects_redestroy :
    (interp (cellDestroyStmt 0 0 42) kCD).bind (fun k => interp (cellDestroyStmt 0 0 99) k) = none := by
  rw [interp_cellDestroyStmt_eq_destroyKernelStep]
  decide

#assert_axioms cellDestroyStmt_flips_lifecycle
#assert_axioms cellDestroyStmt_binds_deathCert
#assert_axioms cellDestroyStmt_other_cell_untouched
#assert_axioms cellDestroyStmt_rejects_unauthorized
#assert_axioms cellDestroyStmt_rejects_redestroy

/-! ## §5 — THE COMPILE WELD: a satisfying witness of cellDestroy's OWN full-state dual circuit AGREES with
the FULL post-state the IR term's executor interpretation produces.

This welds against cellDestroy's GENUINE standalone descriptor `cellDestroyE DLif hDLif DDC hDDC` (the dual
`Surface2` circuit whose two touched components are the WHOLE `lifecycle` + `deathCert` functions, whose
soundness is `cellDestroyA_full_sound`), NOT the per-cell EffectVM row (see this file's header for why: the
EffectVM row carries a nonce-tick divergence AND is off-row for the lifecycle/deathCert flip — the destroy
soundness lives ONLY here). The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the
independent `cellDestroy_iff_spec` (executor ⟺ `CellDestroySpec`); the circuit side is the audited
`cellDestroyA_full_sound` (circuit ⟹ `CellDestroySpec`). Both name the SAME `CellDestroySpec`, so they
PROVABLY agree on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld, with
NO divergence (the dual descriptor freezes the cell record + bal, exactly as `CellDestroySpec` and the
executor do). -/

/-- The Argus circuit interpretation of a `cellDestroy` term: cellDestroy's OWN audited standalone dual
`Surface2` circuit step — the full-state arithmetization `satisfiedE2Dual S (cellDestroyE …)
(encodeE2Dual …)` satisfied on the encoded `(s, args, s')` triple. Its soundness `cellDestroyA_full_sound`
pins the complete `CellDestroySpec`. The `cellDestroy`-keyed analog of BalanceA's `balanceACircuit`, in the
descriptor universe where cellDestroy carries its OWN genuine full-state circuit. -/
def cellDestroyCircuit (S : Surface2)
    (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (cellDestroyE DLif hDLif DDC hDDC)
    (encodeE2Dual S (cellDestroyE DLif hDLif DDC hDDC) s args s')

/-- **`cellDestroySpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CellDestroySpec s actor cell certHash ·` are equal. Rather than re-derive this field-by-field, we route
through the PROVEN executor⟺spec corner `cellDestroy_iff_spec`: each `CellDestroySpec` reconstructs the SAME
committed value `execFullA s (.cellDestroyA …) = some ·`, and `some` is injective. This is exactly the sense
in which `CellDestroySpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem cellDestroySpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId} {certHash : Nat}
    (h₁ : CellDestroySpec s actor cell certHash s₁) (h₂ : CellDestroySpec s actor cell certHash s₂) :
    s₁ = s₂ := by
  have e₁ : execFullA s (.cellDestroyA actor cell certHash) = some s₁ :=
    (cellDestroy_iff_spec s actor cell certHash s₁).mpr h₁
  have e₂ : execFullA s (.cellDestroyA actor cell certHash) = some s₂ :=
    (cellDestroy_iff_spec s actor cell certHash s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`cellDestroy_compile_sound` — the welded soundness (cellDestroy slice), against cellDestroy's OWN
full-state dual descriptor.**

Suppose, for the Argus cellDestroy term `cellDestroyStmt args.actor args.cell args.certHash`:
  * the standalone cellDestroy dual circuit `cellDestroyCircuit S DLif hDLif DDC hDDC s args s'` (= the
    `cellDestroyE` full-state dual arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-function digest portals (`hRest : RestIffNoLifecycleDeathCert S.RH`,
    `hLog : logHashInjective S.LH`, `hDLif`/`hDDC : Function.Injective …`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (cellDestroyStmt args.actor args.cell args.certHash) s.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `s' = { kernel := k', log := cellLifecycleReceipt args.actor args.cell :: s.log }`. I.e.
cellDestroy's OWN circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (`lifecycle` flipped
to Destroyed, `deathCert` bound at `cell`, every other field frozen — including the cell record + `bal`,
balance-NEUTRAL) AND the receipt log — the full `CellDestroySpec`, not a per-cell projection, with NO
divergence. So the circuit the prover runs for cellDestroy pins the complete state the IR term's executor
produces. -/
theorem cellDestroy_compile_sound
    (S : Surface2)
    (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : RestIffNoLifecycleDeathCert S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (args : CellDestroyArgs) (k' : RecordKernelState)
    (hcirc : cellDestroyCircuit S DLif hDLif DDC hDDC s args s')
    (hexec : interp (cellDestroyStmt args.actor args.cell args.certHash) s.kernel = some k') :
    s' = { kernel := k', log := cellLifecycleReceipt args.actor args.cell :: s.log } := by
  -- circuit side: cellDestroy's OWN audited dual soundness forces the FULL `CellDestroySpec` on
  -- `(s, args, s')`.
  have hspec : CellDestroySpec s args.actor args.cell args.certHash s' :=
    cellDestroyA_full_sound S DLif hDLif DDC hDDC hRest hLog s args s' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.cellDestroyA …) = some ⟨k', receipt :: s.log⟩`,
  -- and the independent executor⟺spec corner turns THAT into
  -- `CellDestroySpec s args.actor args.cell args.certHash ⟨k', receipt :: s.log⟩`.
  have hspec' : CellDestroySpec s args.actor args.cell args.certHash
      { kernel := k', log := cellLifecycleReceipt args.actor args.cell :: s.log } :=
    (cellDestroy_iff_spec s args.actor args.cell args.certHash _).mp
      (interp_cellDestroyStmt_chained s args.actor args.cell args.certHash k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact cellDestroySpec_unique hspec hspec'

#assert_axioms cellDestroy_compile_sound

/-! ## §6 — NON-VACUITY of the WELD: cellDestroy's dual circuit is the GENUINE full-state descriptor (the
two touched components are the WHOLE `lifecycle`/`deathCert` functions, NOT placeholders), and the welded
executor side commits.

The weld would be hollow if `cellDestroyE` were an inert descriptor (e.g. the `cellDestroyEWire` emission
stub whose components are `fun _ => 0`), or if `cellDestroyStmt` never committed. We pin both: the witness
kernel `kCD` (§4) drives a real destroy (the executor side `hexec` is satisfiable), and the descriptor's two
active components are the genuine full-`lifecycle`/full-`deathCert` `funcComponent` digests (their
`postClause` is the real per-cell agreement, not `True`). -/

/-- **`cellDestroyStmt_commits_on_witness` — the welded executor side is REALIZABLE (not vacuous).** On the
witness kernel `kCD` (§4) wrapped as a chained state, the IR term COMMITS — so `cellDestroy_compile_sound`'s
`hexec` hypothesis is satisfiable, and the weld is about a circuit whose executor side fires (the
destroy really happens: cell `0` → Destroyed, cert `42` bound). -/
theorem cellDestroyStmt_commits_on_witness :
    (interp (cellDestroyStmt 0 0 42) kCD).isSome = true := by
  rw [interp_cellDestroyStmt_eq_destroyKernelStep]
  decide

/-- **`cellDestroyE_components_are_full_functions` — the dual descriptor's touched components are the GENUINE
WHOLE functions (not the `fun _ => 0` emission stub).** The two active components' `postClause`s are the
real per-state FULL-FUNCTION agreements against `destroyKernelMap` — i.e. for any encoded post the clause
says the WHOLE post-`lifecycle`/`deathCert` function EQUALS the destroy map's (a `funcComponent` digests the
entire function, so its `postClause` is plain function equality, the strongest per-field binding). This is
the anti-placeholder tooth: `cellDestroy_compile_sound` welds against a descriptor that pins both
side-table FUNCTIONS, not a `True`-stubbed one (contrast `cellDestroyEWire`, whose `postClause` is `True`). -/
theorem cellDestroyE_components_are_full_functions
    (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (s : RecChainedState) (args : CellDestroyArgs) (post : RecordKernelState) :
    ((cellDestroyE DLif hDLif DDC hDDC).active1.postClause s args post
        ↔ post.lifecycle = (destroyKernelMap s.kernel args.cell args.certHash).lifecycle)
    ∧ ((cellDestroyE DLif hDLif DDC hDDC).active2.postClause s args post
        ↔ post.deathCert = (destroyKernelMap s.kernel args.cell args.certHash).deathCert) :=
  ⟨Iff.rfl, Iff.rfl⟩

#assert_axioms cellDestroyStmt_commits_on_witness
#assert_axioms cellDestroyE_components_are_full_functions

end Dregg2.Circuit.Argus.Effects.CellDestroy
