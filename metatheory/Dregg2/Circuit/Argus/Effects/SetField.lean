/-
# Dregg2.Circuit.Argus.Effects.SetField — the developer-facing `setFieldA` CAVEAT-GATED field write
welded into the Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus
cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and welded it
to the circuit for the balance/supply/escrow families. This module does the same for `setFieldA` —
dregg2's developer-facing `SetField`, the ONE effect dregg1 routes through the cell's per-slot
`RecordProgram::evaluate` caveats (`apply_set_field` → `cell/src/program.rs:1314`+). Its executor arm
(`TurnExecutorFull.execFullA`, `:3794`) is:

    | .setFieldA actor cell f v => stateStepGuarded s f actor cell v

`stateStepGuarded` (`EffectsState.lean:258`) is the CAVEAT-GATED authority write: it commits iff the
FOUR-conjunct guard

    caveatsAdmit s.kernel f actor cell v = true          -- (slot-caveat gate, per written field)
  ∧ stateAuthB  s.kernel.caps actor cell = true          -- (authority: actor holds a cap over cell)
  ∧ cell ∈ s.kernel.accounts                             -- (membership: a live account)
  ∧ cellLive   s.kernel cell = true                      -- (lifecycle liveness, R6)

holds, and then produces EXACTLY `stateStep`'s post: it writes field `f` of `cell` to `.int v` via
`writeField` (which touches ONLY the `cell` map's value at `cell`), prepends a one-row receipt to the
chain `log`, and leaves EVERYTHING ELSE literally unchanged.

## THE IR ENCODING — a SINGLE-CELL field write, gated by the four-conjunct kernel guard.

CRUCIAL observation that makes this an honest weld (not a fake): EVERY conjunct of the `stateStepGuarded`
guard reads ONLY `RecordKernelState` — `caveatsAdmit k …`, `stateAuthB k.caps …`, `cell ∈ k.accounts`,
`cellLive k …`. And `writeField k f cell (.int v)` is a PURE `RecordKernelState → RecordKernelState`
single-cell map. So the kernel-state transition of `setFieldA` is exactly a `guard`-then-`setCell`
shape — the SAME `setCell` primitive transfer/mint/burn use, now writing `setField f (k.cell c) (.int v)`
into the singleton `{cell}`. The body is therefore `seq (guard <4-conjunct kernel guard>) (setCell {cell}
<field-write leaf>)` — gate, then a single-cell write — no new IR constructor needed.

The receipt-LOG append is NOT a `RecordKernelState` field (it lives in the CHAINED state `RecChainedState
= ⟨kernel, log⟩`), so the IR term — which transforms `RecordKernelState` — captures the KERNEL transition
exactly; the log prepend is the chained layer's extra row. This is the honest KERNEL-vs-CHAINED divergence,
carried EXPLICITLY (the §3 lift produces `{ kernel := k', log := <receipt> :: s.log }`, the log row named
in full — NOT papered), the same shape BalanceA's §3 dst-liveness side-condition has.

## THE COMPILE WELD — the FULL-STATE `setfield_circuit_full_sound` (the STRONGER surface, preferred).

`setFieldA` carries TWO genuine circuit surfaces:

  * the per-cell EffectVM class-A descriptor `setFieldDescriptor_classA` (`EffectVmEmitSetField.lean`),
    which pins the per-cell post-BLOCK (the moved field column + the frozen frame under Poseidon2 CR);
  * the FULL-STATE keystone `setfield_circuit_full_sound` (`SetFieldCommit.lean`), whose satisfying
    witness pins the WHOLE declarative `SetFieldSpec` — all 17 RecordKernelState components + the receipt
    log — RECONSTRUCTED (not portaled) from a small standard Poseidon collision-resistance set
    (`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective`) + the `AccountsWF`
    structural invariant.

We weld DIRECTLY against the FULL-STATE one (BalanceA's preferred stronger surface): its conclusion is
the FULL 17-field `SetFieldSpec` agreement, strictly stronger than a per-cell projection. The executor
side routes through the §3 chained lift (`interp` ⟹ `execFullA`) + the independent
`execFullA_setFieldA_iff_spec` (executor ⟺ `SetFieldSpec`); the circuit side is the audited
`setfield_circuit_full_sound` (circuit ⟹ `SetFieldSpec`). Both name the SAME `SetFieldSpec`, which is
FUNCTIONAL (`setFieldSpec_unique`, routed through the executor⟺spec corner), so they PROVABLY agree on
the WHOLE chained post-state.

## Honesty (the surfaces + the carried divergence, named not papered)

  * Cornerstone surface: per-cell + side-table-LOG. The IR term's `interp` IS the kernel transition
    `setFieldKStep` (a `setCell {cell}` field write under the 4-conjunct guard), on the nose.
  * Weld surface: FULL-STATE `SetFieldSpec` (all 17 kernel fields + the receipt log) — the §A
    `setFieldDescriptor_classA` per-cell block is the WEAKER twin we do NOT use here.
  * DIVERGENCE (named): KERNEL-vs-CHAINED — the IR term writes the kernel; the executor `execFullA`
    ALSO prepends a one-row receipt `⟨actor, cell, cell, 0⟩` to the chained `log`. The §3 lift carries
    that log row in full as an explicit conjunct of the produced chained state (NOT a collapsed field).
    There is NO nonce-tick divergence (a field write FREEZES the on-trace seq-nonce — the runtime
    metadata bump is the distinct `incrementNonce` row, per `EffectVmEmitSetField` §1).

`#assert_axioms` on both keystones ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon CR /
`AccountsWF` assumptions enter ONLY inside the reused `setfield_circuit_full_sound` hypotheses, not in
the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only;
this file owns only its own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState

namespace Dregg2.Circuit.Argus.Effects.SetField

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (execFullA)
open Dregg2.Circuit.Argus (RecStmt interp)
-- The `setFieldA` kernel-write spine: the four-conjunct guard pieces (all `RecordKernelState`-readable)
-- + the pure single-cell field-write `writeField` / `setField`.
open Dregg2.Exec.EffectsState
  (setField fieldOf writeField stateAuthB caveatsAdmit cellLive
   stateStep stateStepGuarded)
-- The INDEPENDENT full-state declarative spec + the executor⟺spec corner (FULL 17-field, both directions).
open Dregg2.Circuit.Spec.CellStateField
  (SetFieldSpec SetFieldGuard setFieldCellMap setFieldCellMap_eq_writeField
   execFullA_setFieldA_iff_spec execFullA_setFieldA_eq)
-- The FULL-STATE circuit⟺spec keystone (the preferred stronger surface) + its commitment surface.
open Dregg2.Circuit.SetFieldCommit
  (recSetFieldCommit encodeSF satisfiedSF setfield_circuit_full_sound recSetFieldCommit_binds)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The setFieldA effect as an Argus IR term (the 4-conjunct kernel guard, then the single-cell
field write).

`stateStepGuarded` gates on `caveatsAdmit ∧ stateAuthB ∧ membership ∧ cellLive`, and on commit writes
`writeField k f cell (.int v)` (the single-cell `setField`) + a receipt row. The IR term — which
transforms `RecordKernelState` — captures the KERNEL part EXACTLY: a `Bool` `guard` of the EXACT four
conjuncts (each a `RecordKernelState` read-out), then a `setCell {cell}` whose leaf writes `setField f
(k.cell c) (.int v)`. The contrast with transfer is the move primitive's LEAF: a NAMED-FIELD write
(`setField f · (.int v)`) into the singleton target, NOT a balance move (`recTransfer`). The log row is
the chained layer's (carried in §3). -/

/-- The setFieldA admissibility gate as a `Bool` — exactly the four-conjunct `if` inside
`stateStepGuarded`/`stateStep` (caveat ∧ authority ∧ membership ∧ liveness). Every conjunct reads ONLY
`RecordKernelState` (`caveatsAdmit k …`, `stateAuthB k.caps …`, `cell ∈ k.accounts`, `cellLive k …`), so
the whole guard is a genuine kernel-state `Bool`. The `cellLive` conjunct is the R6 fail-closed gate
(no write into a Sealed/Destroyed cell). -/
def setFieldGuard (actor cell : CellId) (f : FieldName) (v : Int) (k : RecordKernelState) : Bool :=
  caveatsAdmit k f actor cell v
    && stateAuthB k.caps actor cell
    && decide (cell ∈ k.accounts)
    && cellLive k cell

/-- **The setFieldA effect as an IR term: the four-conjunct guard, then the single-cell field write.**
Mirrors `transferStmt`/`mintStmt` (gate, then a `setCell` move) but the move's LEAF is a NAMED-FIELD
write `setField f (k.cell c) (.int v)` into the singleton `{cell}` — NOT a balance move. The `setCell`
primitive is the SAME one transfer/mint/burn use (no new constructor); the field-write leaf is the
shape the developer-facing `SetField` assembles. The receipt LOG append is the chained layer's (§3). -/
def setFieldStmt (actor cell : CellId) (f : FieldName) (v : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (setFieldGuard actor cell f v))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k _ => setField f (k.cell cell) (.int v)))

/-- The KERNEL transition of `setFieldA`: gate on the four conjuncts, then write `writeField k f cell
(.int v)` (the single-cell `setField`). This is precisely the `kernel` component the chained executor
`stateStepGuarded` commits (its log-row prepend is the chained layer's, added in §3). Stated as a pure
`RecordKernelState → Option RecordKernelState` so the cornerstone names the executor term exactly. -/
def setFieldKStep (actor cell : CellId) (f : FieldName) (v : Int) (k : RecordKernelState) :
    Option RecordKernelState :=
  if setFieldGuard actor cell f v k = true then some (writeField k f cell (.int v)) else none

/-! ## §2 — The cornerstone: `interp` of the setFieldA term IS the kernel transition `setFieldKStep`. -/

/-- The `setCell {cell}` field-write RECORD-UPDATE is exactly `writeField k f cell (.int v)` — the single-
cell analog of `transferCellMap_eq`/`creditCellMap_eq`, stated at the WHOLE-record level so the cornerstone
closes by `rfl`. The `setCell` clause produces `{ k with cell := fun c => if c ∈ {cell} then setField f
(k.cell cell) (.int v) else k.cell c }`; `writeField` is `{ k with cell := fun c => if c = cell then
setField f (k.cell c) (.int v) else k.cell c }` — and the two `cell` maps agree pointwise (on the singleton,
`c = cell`, so `k.cell cell = k.cell c`), so the records are equal. -/
theorem setFieldRecord_eq (cell : CellId) (f : FieldName) (v : Int) (k : RecordKernelState) :
    { k with cell := fun c => if c ∈ ({cell} : Finset CellId)
                                then setField f (k.cell cell) (.int v) else k.cell c }
      = writeField k f cell (.int v) := by
  unfold writeField
  congr 1
  funext c
  by_cases h : c = cell
  · simp [h]
  · simp [Finset.mem_singleton, h]

/-- **The cornerstone (single-cell field write).** `interp` of the setFieldA term IS the kernel
transition `setFieldKStep` — the same partial function, by construction, exactly as the transfer/mint/
burn/escrow cornerstones, now over a NAMED-FIELD write (`setCell {cell}` of `setField f · (.int v)`)
under the four-conjunct caveat∧authority∧membership∧liveness guard. The executor IS the meaning of the
term. -/
theorem interp_setFieldStmt_eq_setFieldKStep (actor cell : CellId) (f : FieldName) (v : Int)
    (k : RecordKernelState) :
    interp (setFieldStmt actor cell f v) k = setFieldKStep actor cell f v k := by
  simp only [setFieldStmt, interp, setFieldKStep]
  by_cases hg : setFieldGuard actor cell f v k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setCell` move installs the field write, which by
    -- `setFieldRecord_eq` IS the whole `writeField` record-update.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos hg, setFieldRecord_eq]
  · -- REJECT (fail-closed): the guard fails ⇒ `none.bind _ = none`; the kernel `if` closes too.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg hg]

#assert_axioms interp_setFieldStmt_eq_setFieldKStep

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `execFullA` / `stateStepGuarded`.

The full-state descriptor (§4) is keyed on the CHAINED executor `execFullA` over `RecChainedState`
(kernel + receipt log) — the arm `execFullA s (.setFieldA …) = stateStepGuarded s f actor cell v`. The
§2 cornerstone is over the KERNEL transition `setFieldKStep`. The chained layer is exactly the kernel
transition PLUS the receipt-LOG prepend `⟨actor, cell, cell, 0⟩ :: s.log` (the named KERNEL-vs-CHAINED
divergence). We bridge faithfully, carrying that log row IN FULL in the produced chained state — NOT
papered, NOT collapsed.

The key reconciliation: both `setFieldKStep`'s guard and `stateStepGuarded`'s guard are the SAME four
conjuncts (`setFieldGuard k = SetFieldGuard s` over `s.kernel = k`), and both produce the SAME `writeField`
kernel post — so a committing `setFieldKStep s.kernel` lifts to a committing `execFullA s (.setFieldA …)`
on the nose, with the log row added. -/

/-- The IR-term guard `setFieldGuard … k` (a `Bool`) decodes to the declarative `SetFieldGuard s …`
(the spec's Prop guard) when `s.kernel = k`. The four conjuncts are the SAME, in the SAME order. -/
theorem setFieldGuard_iff (actor cell : CellId) (f : FieldName) (v : Int) (s : RecChainedState) :
    setFieldGuard actor cell f v s.kernel = true ↔ SetFieldGuard s actor cell f v := by
  simp only [setFieldGuard, SetFieldGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **`interp_setFieldStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the §2 cornerstone commits on the kernel (`interp (setFieldStmt actor cell f v) s.kernel = some k'`), the
unified action executor `execFullA s (.setFieldA actor cell f v)` commits to the chained state
`⟨k', ⟨actor, cell, cell, 0⟩ :: s.log⟩`. So the Argus term's kernel meaning lifts to the chained executor
the full-state descriptor speaks about — the log row carried IN FULL (the named kernel-vs-chained
divergence), no extra side-condition needed (the four-conjunct guard is fully captured by the IR term). -/
theorem interp_setFieldStmt_chained
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (k' : RecordKernelState)
    (hexec : interp (setFieldStmt actor cell f v) s.kernel = some k') :
    execFullA s (.setFieldA actor cell f v)
      = some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel transition `setFieldKStep`.
  rw [interp_setFieldStmt_eq_setFieldKStep, setFieldKStep] at hexec
  -- the guard FIRES (else `hexec : none = some k'` is absurd); extract the guard + the kernel post.
  by_cases hg : setFieldGuard actor cell f v s.kernel = true
  · rw [if_pos hg] at hexec
    -- the chained arm reduces to `stateStepGuarded`; on the (decoded) guard it commits `writeField` + the row.
    rw [execFullA_setFieldA_eq]
    have hguard : SetFieldGuard s actor cell f v := (setFieldGuard_iff actor cell f v s).mp hg
    -- `stateStepGuarded` commits to `writeField`'s post + the receipt row when its guard holds.
    have := (Dregg2.Circuit.Spec.CellStateField.stateStepGuarded_iff_guard_and_post
              s actor cell f v
              { kernel := writeField s.kernel f cell (.int v),
                log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }).mpr
              ⟨hguard, rfl⟩
    -- `hexec` names the kernel post as `k'`; rewrite it into the committed chained state.
    rw [← (Option.some.injEq _ _).mp hexec]
    exact this
  · rw [if_neg hg] at hexec; exact absurd hexec (by simp)

#assert_axioms interp_setFieldStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of setFieldA's FULL-STATE circuit agrees with the WHOLE
chained post-state the IR term's executor interpretation produces.

This welds against setFieldA's GENUINE FULL-STATE descriptor (`setFieldCircuit`/`setfield_circuit_full_sound`,
the keystone whose conclusion is the complete `SetFieldSpec`), NOT the weaker per-cell
`setFieldDescriptor_classA` — see this file's header. The executor side is routed through §3
(`interp` ⟹ `execFullA`) and the independent `execFullA_setFieldA_iff_spec` (executor ⟺ `SetFieldSpec`);
the circuit side is the audited `setfield_circuit_full_sound` (circuit ⟹ `SetFieldSpec`). Both name the
SAME `SetFieldSpec`, which is FUNCTIONAL, so they PROVABLY agree on the WHOLE 17-field chained post-state
— strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `setFieldA` term: setFieldA's OWN audited FULL-STATE circuit
satisfaction `satisfiedSF cmb (encodeSF …)` on the encoded chained `(s, actor, cell, f, v, s')` witness.
Its soundness `setfield_circuit_full_sound` pins the complete `SetFieldSpec`. The setFieldA-keyed analog
of `balanceACircuit`, in the descriptor universe where setFieldA carries its OWN genuine FULL-STATE
circuit. -/
def setFieldCircuitSat
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState) : Prop :=
  satisfiedSF cmb (encodeSF CH RH cmb compressN LH s actor cell f v s')

/-- **`setFieldSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`SetFieldSpec s actor cell f v ·` are equal. Rather than re-derive this field-by-field, we route through
the PROVEN executor⟺spec corner `execFullA_setFieldA_iff_spec`: each `SetFieldSpec` reconstructs the SAME
committed value `execFullA s (.setFieldA …) = some ·`, and `some` is injective. This is exactly the sense
in which `SetFieldSpec` is functional — it determines the whole chained post-state — so the circuit-side
and executor-side spec facts collapse to one welded post-state. -/
theorem setFieldSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h₁ : SetFieldSpec s actor cell f v s₁) (h₂ : SetFieldSpec s actor cell f v s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.setFieldA actor cell f v) = some s₁ :=
    (execFullA_setFieldA_iff_spec s actor cell f v s₁).mpr h₁
  have e₂ : execFullA s (.setFieldA actor cell f v) = some s₂ :=
    (execFullA_setFieldA_iff_spec s actor cell f v s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`setField_compile_sound` — the welded soundness (setFieldA slice), against setFieldA's OWN FULL-STATE
descriptor.**

Suppose, for the Argus setFieldA term `setFieldStmt actor cell f v`:
  * setFieldA's GENUINE FULL-STATE circuit `setFieldCircuitSat CH RH cmb compressN LH s actor cell f v s'`
    (= the full-state arithmetization `satisfiedSF cmb (encodeSF …)` satisfied on the encoded chained
    witness) holds, under the realizable Poseidon collision-resistance portals + structural invariant
    (`hCompressN`/`hLeaf`/`hRest`/`hLog`, `AccountsWF` on both kernels — the EXACT hypotheses the keystone
    carries, NOT papered, NOT added to the conclusion's meaning);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (setFieldStmt actor cell f v)
    s.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `s' = { kernel := k', log := ⟨actor, cell, cell, 0⟩ :: s.log }`. I.e. setFieldA's OWN circuit
and the IR term AGREE on the WHOLE 17-field RecordKernelState (the target cell's `f` slot written to `v`,
every other cell + all 16 non-`cell` components frozen) AND the receipt log — the full `SetFieldSpec`, not
a per-cell projection. So the circuit the prover runs for setFieldA pins the complete chained state the IR
term's executor produces, log row included. -/
theorem setField_compile_sound
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
    (hCompressN : StateCommit.compressNInjective compressN)
    (hLeaf : StateCommit.cellLeafInjective CH)
    (hRest : StateCommit.RestHashIffFrame RH)
    (hLog : StateCommit.logHashInjective LH)
    (s s' : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (k' : RecordKernelState)
    (hwf : StateCommit.AccountsWF s.kernel) (hwf' : StateCommit.AccountsWF s'.kernel)
    (hcirc : setFieldCircuitSat CH RH cmb compressN LH s actor cell f v s')
    (hexec : interp (setFieldStmt actor cell f v) s.kernel = some k') :
    s' = { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- circuit side: setFieldA's OWN audited FULL-STATE soundness forces the WHOLE `SetFieldSpec` on
  -- `(s, actor, cell, f, v, s')`.
  have hspec : SetFieldSpec s actor cell f v s' :=
    setfield_circuit_full_sound CH RH cmb compressN LH hCompressN hLeaf hRest hLog
      s actor cell f v s' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.setFieldA …) = some ⟨k', receipt :: log⟩`, and
  -- the independent executor⟺spec corner turns THAT into `SetFieldSpec s actor cell f v ⟨k', receipt :: log⟩`.
  have hspec' : SetFieldSpec s actor cell f v
      { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } :=
    (execFullA_setFieldA_iff_spec s actor cell f v _).mp
      (interp_setFieldStmt_chained s actor cell f v k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same chained state (the spec pins every kernel field +
  -- the log).
  exact setFieldSpec_unique hspec hspec'

#assert_axioms setField_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely WRITES the slot (the write is observable), the slot READS
BACK the written value, the OTHER fields/cells are FROZEN, and the four-conjunct gate REJECTS forged inputs
(fail-closed, each leg).

The cornerstone/weld would be hollow if setFieldA never committed, if the write were a no-op, if it
clobbered a bystander field, or if the gate admitted everything. A concrete one-account kernel `kSF0`
(cell 0 a Live self-owned account, empty slot caveats) exercises a real write; the rejection lemmas show
each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cell 0 is a Live self-owned account (lifecycle defaults Live,
empty caps ⇒ authority by OWNERSHIP via `stateAuthB`'s self-targeted turn, empty slot caveats ⇒
`caveatsAdmit` passes), carrying a record with `status = 1` and `other = 9`. -/
def kSF0 : RecordKernelState :=
  { accounts := {0}
    cell := fun _ => .record [("status", .int 1), ("other", .int 9)]
    caps := fun _ => [] }

/-- **NON-VACUITY (the WRITE is OBSERVABLE / reads back).** The committed write sets the `status` slot of
cell 0 from `1` to `7` — reading it back returns exactly `7` (the `setCell`/`setField` write/read law is
real). -/
theorem setFieldStmt_writes :
    (interp (setFieldStmt 0 0 "status" 7) kSF0).map (fun k => fieldOf "status" (k.cell 0)) = some 7 := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

/-- **NON-VACUITY (bystander field FROZEN).** The write to `status` leaves the SIBLING field `other` of the
SAME cell untouched (still `9`) — confirming the field write touches ONLY the named slot, not the whole
record (anti-clobber). -/
theorem setFieldStmt_other_field_frozen :
    (interp (setFieldStmt 0 0 "status" 7) kSF0).map (fun k => fieldOf "other" (k.cell 0)) = some 9 := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

/-- **NON-VACUITY (other cells FROZEN).** The write to cell 0 leaves cell 1's `status` field reading its
ORIGINAL value (`1`, since `kSF0` gives every cell the same starting record) — the singleton `{cell}` write
touches ONLY the target, so cell 1's `status` is NOT the written `7`. The cell-frame, observed on a sibling
cell's slot (an `Int`, so `decide`-checkable). -/
theorem setFieldStmt_other_cell_frozen :
    (interp (setFieldStmt 0 0 "status" 7) kSF0).map (fun k => fieldOf "status" (k.cell 1)) = some 1 := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

/-- **NON-VACUITY (fail-closed: unauthorized).** A write by an actor (`9`) holding NO cap over cell 0 (and
not owning it) does NOT commit — the AUTHORITY leg of the gate fails (`interp = none`). -/
theorem setFieldStmt_rejects_unauthorized :
    interp (setFieldStmt 9 0 "status" 7) kSF0 = none := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

/-- **NON-VACUITY (fail-closed: non-account).** A write targeting a cell (`5`) NOT in `accounts` does NOT
commit — the MEMBERSHIP leg fails. -/
theorem setFieldStmt_rejects_nonaccount :
    interp (setFieldStmt 5 5 "status" 7) kSF0 = none := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

/-- A pre-state whose cell 0 carries an `Immutable "status"` caveat — the slot is registered forever. -/
def kSFImmut : RecordKernelState :=
  { kSF0 with slotCaveats := fun _ => [.immutable "status"] }

/-- **NON-VACUITY (fail-closed: caveat violation).** A rewrite of an `Immutable "status"` slot to a
DIFFERENT value (old `1` → new `7`) does NOT commit — the CAVEAT leg fails closed (an `Immutable` slot
rejects any rewrite). The executor-level app-safety teeth, lifted onto the IR term. -/
theorem setFieldStmt_rejects_caveat_violation :
    interp (setFieldStmt 0 0 "status" 7) kSFImmut = none := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

/-- **NON-VACUITY (the caveat gate is TWO-valued).** The SAME `Immutable "status"` slot still admits a
no-op rewrite to the SAME value (old `1` → new `1`, which `Immutable` permits) — so the caveat gate is a
genuine discriminator, not a blanket reject. -/
theorem setFieldStmt_immut_admits_noop :
    (interp (setFieldStmt 0 0 "status" 1) kSFImmut).isSome = true := by
  rw [interp_setFieldStmt_eq_setFieldKStep]
  decide

#assert_axioms setFieldStmt_writes
#assert_axioms setFieldStmt_other_field_frozen
#assert_axioms setFieldStmt_other_cell_frozen
#assert_axioms setFieldStmt_rejects_unauthorized
#assert_axioms setFieldStmt_rejects_nonaccount
#assert_axioms setFieldStmt_rejects_caveat_violation
#assert_axioms setFieldStmt_immut_admits_noop

end Dregg2.Circuit.Argus.Effects.SetField
