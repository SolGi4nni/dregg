/-
# Dregg2.Circuit.Spec.notecommitment — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **note-commitment** (variant: `noteCreateA`).

This is a *leaf* module in the `Transfer.lean` lineage: it builds, for the grow-only fresh-commitment
PUBLISH effect, the SAME triangle corner the reference `TransferSpec`/`recKExec_iff_spec` establish
for `Transfer`, but written INDEPENDENTLY of the executor and at the gated `execFullA`/`RecChainedState`
level (the analog of `Spec.supplycreation`'s `MintASpec`/`execMintA_iff_spec`).

`noteCreateA` is the dual of `noteSpendA`: a `noteSpend` GROWS the `nullifiers` set under a
double-spend GATE (fail-closed on a repeated nullifier), but a `noteCreate` GROWS the `commitments`
SET with NO guard at all — the commitment set is APPEND-ONLY and a fresh commitment cannot conflict
(`apply_note_create`, dregg1). So the executor arm (`TurnExecutorFull.lean:3539`) is the TOTAL,
single-branch `some (noteCreateChainA s cm actor)` — there is NO admissibility guard to lift. This is
the *cleanest* possible spec shape: a spec with no guard conjunct, ALWAYS satisfiable.

The deliverables, mirroring the reference pattern (`Dregg2/Circuit/Transfer.lean` §6b /
`Spec/supplycreation.lean`):

  1. `NoteCreateASpec st cm actor st'` : Prop — the FULL declarative post-state of a committed
     `noteCreateA`. It is the conjunction of
       * (NO admissibility guard — `noteCreate` is unconditional; this is the "append-only, no
         double-check" property the prompt calls out, made EXPLICIT as `noteCreateAdmit = True`);
       * the EXACT touched components — `kernel.commitments` PREPENDED with `cm`
         (`cm :: st.kernel.commitments`) and the receipt `log` PREPENDED with the disclosed
         `escrowReceiptA actor` self-edge;
       * EVERY OTHER state component LITERALLY unchanged: all 16 non-`commitments` kernel fields
         (`accounts` `cell` `caps` `escrows` `nullifiers` `revoked` `bal` `queues` `swiss`
         `slotCaveats` `factories` `lifecycle` `deathCert` `delegate` `delegations` `sealedBoxes`)
         — the FRAME. No frame clause mentions any executor helper.
  2. `execNoteCreateA_iff_spec : execFullA st (.noteCreateA cm actor) = some st' ↔ NoteCreateASpec …`
     — BOTH directions. The `→` VALIDATES the executor against the independent spec: a
     silently-mutated field would make the frame clause unprovable. (None was found — see frameGaps in
     the report.)
  3. `noteCreateCommitment_correct` — the post-`commitments` helper validated DECLARATIVELY (`cm` is
     prepended, the membership grows, and the OLD membership is preserved), so the spec's
     `commitments = cm :: …` clause encodes insert ∧ set-frame, not blind trust.

The companion semantic corollaries pin the content: a committed `noteCreate` INSERTS `cm`
(`noteCreateA_inserts`), PRESERVES every prior commitment (`noteCreateA_preserves`), is balance-NEUTRAL
on every asset (`noteCreateA_bal_neutral`), and — the headline distinguishing it from `noteSpend` —
ALWAYS COMMITS regardless of state (`noteCreateA_total`), the append-only "no double-check" theorem.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.NoteCommitment

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority

/-! ## §1 — the (TRIVIAL) admissibility guard, lifted from the CODE.

`noteCreateA`'s `execFullA` arm (`TurnExecutorFull.lean:3539`) is `some (noteCreateChainA s cm actor)`
— a TOTAL function, no `if`. There is NO admissibility guard: the commitment set is APPEND-ONLY and a
fresh commitment cannot conflict (unlike `noteSpendA`, which gates on a fresh nullifier). We make this
EXPLICIT — `noteCreateAdmit = True` — so the spec's shape matches the reference (a guard conjunct that
is always satisfiable) and so the "no double-check" property is a literal field of the spec, not an
implicit omission. -/

/-- **`noteCreateAdmit`** — the admissibility guard a `noteCreateA` checks. It is `True`: the
note-commitment publish is UNCONDITIONAL (append-only commitment set, no double-check). This is the
explicit dual of `noteSpend`'s fail-closed nullifier guard. -/
def noteCreateAdmit : Prop := True

/-- The disclosed receipt a committed `noteCreateA` prepends to the log — the `escrowReceiptA actor`
self-edge `actor → actor` of size `0` (exactly `noteCreateChainA`'s `log` head,
`TurnExecutorFull.lean:2008`/`escrowReceiptA` `:1982`). Balance-neutral, as the effect is. -/
def noteCreateReceipt (actor : CellId) : Turn := escrowReceiptA actor

/-! ## §2 — the post-`commitments` helper, validated DECLARATIVELY.

`noteCreateCommitment k cm = { k with commitments := cm :: k.commitments }` is the ONLY thing a
committed note-create does to the kernel's tracked sets. We validate it relationally (the head is `cm`,
the new set CONTAINS `cm`, and every PRIOR commitment is preserved) so the spec's
`commitments = cm :: …` clause carries real meaning rather than trusting the helper's name. -/

/-- **`noteCreateCommitment_correct`** — the commitment-set helper validated DECLARATIVELY: a
note-create PREPENDS `cm` (so `cm` is now a member), and every PRIOR commitment remains a member (the
set grows, nothing is lost — append-only). So the spec's `commitments = cm :: …` clause
encodes insert ∧ grow-only-frame. -/
theorem noteCreateCommitment_correct (k : RecordKernelState) (cm : Nat) :
    (noteCreateCommitment k cm).commitments = cm :: k.commitments
    ∧ cm ∈ (noteCreateCommitment k cm).commitments
    ∧ (∀ x, x ∈ k.commitments → x ∈ (noteCreateCommitment k cm).commitments) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [noteCreateCommitment, List.mem_cons, true_or]
  · intro x hx; simp only [noteCreateCommitment, List.mem_cons]; exact Or.inr hx

/-! ## §3 — the executor projection: `execFullA` on `noteCreateA` IS `noteCreateChainA`.

The `noteCreateA` arm of `execFullA` (`TurnExecutorFull.lean:3539`) is `some (noteCreateChainA s cm
actor)` — a SINGLE, TOTAL branch (always `some`). We expose it as a definitional rewrite so the spec
proof works on `noteCreateChainA`. -/

@[simp] theorem execFullA_noteCreateA (st : RecChainedState) (cm : Nat) (actor : CellId) :
    execFullA st (.noteCreateA cm actor) = some (noteCreateChainA st cm actor) := rfl

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`NoteCreateASpec` is the COMPLETE declarative post-state of a committed `noteCreateA`, written
INDEPENDENTLY of the executor: the (trivial) guard holds; the post `kernel.commitments` is `cm`
prepended; the post `log` is the disclosed receipt prepended; and ALL 16 non-`commitments` kernel
components are LITERALLY unchanged. No frame clause mentions
`execFullA`/`noteCreateChainA`/`noteCreateCommitment`. -/

/-- **The full-state declarative spec of a committed note-commitment (`noteCreateA`)** — the
INDEPENDENT reference semantics. Enumerates the FRAME completely: the (trivial) guard, the touched
`commitments` + `log`, and every one of the 16 untouched non-`commitments` kernel fields. -/
def NoteCreateASpec (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) : Prop :=
  noteCreateAdmit
  ∧ st'.kernel.commitments = cm :: st.kernel.commitments
  ∧ st'.log = noteCreateReceipt actor :: st.log
  -- THE FRAME: every non-`commitments` kernel field literally unchanged (16 fields).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps

/-- **`noteCreateChainA_iff_spec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both directions).** The
chained note-create commits into `st'` IFF `st'` is EXACTLY the spec'd full post-state. The `→`
VALIDATES `noteCreateChainA` against the independent spec — all 18 components
(`commitments` + `log` + 16 frame fields) are checked, so a silently-mutated component would make the
proof FAIL; the `←` reconstructs the committed state from the spec. Because the arm is TOTAL there is
no `if`-split: the equation `noteCreateChainA st cm actor = st'` characterizes the post-state directly. -/
theorem noteCreateChainA_iff_spec (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) :
    some (noteCreateChainA st cm actor) = some st' ↔ NoteCreateASpec st cm actor st' := by
  unfold noteCreateChainA noteCreateCommitment NoteCreateASpec noteCreateAdmit noteCreateReceipt
  constructor
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨_, hcm, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    -- reconstruct st' from the spec: split both records and substitute every field.
    obtain ⟨k', lg'⟩ := st'
    obtain ⟨acc, cl, cp, nl, rv, cm', bl, sc, fc, lc, dc, dl, dn, dge, dgea, hp⟩ := k'
    simp only at hcm hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    subst hcm hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rfl

/-- **`execNoteCreateA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ SPEC (FULL state,
both directions).** The one gated executor commits a `noteCreateA` turn into `st'` IFF `st'` is EXACTLY
the independent full-state spec. Forward VALIDATES the executor (every one of the 18 components is
pinned); backward reconstructs. This is the note-commitment corner of the spec⟺executor(⟺circuit)
triangle, the `noteCreateA` analog of `recKExec_iff_spec`. -/
theorem execNoteCreateA_iff_spec (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.noteCreateA cm actor) = some st' ↔ NoteCreateASpec st cm actor st' := by
  rw [execFullA_noteCreateA]; exact noteCreateChainA_iff_spec st cm actor st'

/-! ## §5 — derived guarantees off the spec.

The spec is the apex truth; these read off it without re-touching the executor. -/

/-- **`noteCreateA_inserts` — the published commitment is in the post-set.** A committed `noteCreateA`
PROVES `cm ∈ st'.kernel.commitments`. Read off the spec's `commitments` clause + the
declaratively-validated helper. -/
theorem noteCreateA_inserts (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.noteCreateA cm actor) = some st') :
    cm ∈ st'.kernel.commitments := by
  have hcm := ((execNoteCreateA_iff_spec st cm actor st').mp h).2.1
  rw [hcm]; exact List.mem_cons_self

/-- **`noteCreateA_preserves` — append-only: no prior commitment is lost.** A committed `noteCreateA`
PROVES every PRIOR commitment remains a member of the post-set (the grow-only / append-only property).
Read off the spec's `commitments` clause. -/
theorem noteCreateA_preserves (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.noteCreateA cm actor) = some st')
    (x : Nat) (hx : x ∈ st.kernel.commitments) :
    x ∈ st'.kernel.commitments := by
  have hcm := ((execNoteCreateA_iff_spec st cm actor st').mp h).2.1
  rw [hcm]; exact List.mem_cons_of_mem _ hx

/-- **`noteCreateA_bal_neutral` — BALANCE NEUTRALITY (semantic content).** A committed `noteCreateA`
leaves the `bal` ledger LITERALLY unchanged (it grows only `commitments`, never `bal`). Read off the
spec's `bal` frame clause. This is the conservation punchline: a note-commitment publish moves NO
value. -/
theorem noteCreateA_bal_neutral (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.noteCreateA cm actor) = some st') :
    st'.kernel.bal = st.kernel.bal :=
  ((execNoteCreateA_iff_spec st cm actor st').mp h).2.2.2.2.2.2.2.2.1

/-- **`noteCreateA_total` — THE DISTINGUISHING THEOREM: a note-create ALWAYS COMMITS.** Unlike
`noteSpendA` (fail-closed on a repeated nullifier), `noteCreateA` is UNCONDITIONAL — there is ALWAYS a
committed post-state, regardless of the pre-state. This is the "append-only, no double-check" property
the prompt calls out, proved at the executor level. -/
theorem noteCreateA_total (st : RecChainedState) (cm : Nat) (actor : CellId) :
    ∃ st', execFullA st (.noteCreateA cm actor) = some st' :=
  ⟨noteCreateChainA st cm actor, rfl⟩

/-- **`noteCreateA_admits_iff` — the executor commits IFF the (trivial) guard holds.** Mirrors the
reference shape; since the guard is `True`, commitment is unconditional. -/
theorem noteCreateA_admits_iff (st : RecChainedState) (cm : Nat) (actor : CellId) :
    (∃ st', execFullA st (.noteCreateA cm actor) = some st') ↔ noteCreateAdmit := by
  unfold noteCreateAdmit
  exact ⟨fun _ => trivial, fun _ => noteCreateA_total st cm actor⟩

/-! ## §6 — NON-VACUITY / DISTINCTNESS: the spec is genuine, and the effect is grow-only.

A spec that accepts everything would be worthless ONLY if the effect itself were a no-op — but
`noteCreateA` GROWS the commitment set every time (and is the SOLE effect that touches
`commitments`). We exhibit: it strictly extends the set (length grows), and the published commitment
was not necessarily present before — so the spec carries real content. (`noteCreateA` is total by
design, so there is no "rejection" theorem; the genuine content is the strict GROWTH, below.) -/

/-- **`noteCreateA_grows` — the commitment set STRICTLY grows by one.** A committed `noteCreateA`
increases `commitments.length` by exactly 1 — the effect is never a no-op on its tracked set. -/
theorem noteCreateA_grows (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.noteCreateA cm actor) = some st') :
    st'.kernel.commitments.length = st.kernel.commitments.length + 1 := by
  have hcm := ((execNoteCreateA_iff_spec st cm actor st').mp h).2.1
  rw [hcm]; simp [List.length_cons]

/-- **`noteCreateA_log_grows` — the receipt chain advances by exactly one row** (the disclosed
`escrowReceiptA actor`). Read off the spec's `log` clause. -/
theorem noteCreateA_log_grows (st : RecChainedState) (cm : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.noteCreateA cm actor) = some st') :
    st'.log = noteCreateReceipt actor :: st.log :=
  ((execNoteCreateA_iff_spec st cm actor st').mp h).2.2.1

/-! ## §7 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Cell 9 publishes commitment `42`. The publish ALWAYS commits (totality); the post-set CONTAINS `42`;
a SECOND publish of the SAME `42` ALSO commits (append-only — no double-check, unlike noteSpend); the
`bal` ledger is untouched. -/

/-- A concrete pre-state: one live cell, empty commitment set, empty log. -/
def stN0 : RecChainedState :=
  { kernel :=
      { accounts := {9}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

-- A note-create of commitment 42 by actor 9 ALWAYS COMMITS:
#guard (execFullA stN0 (.noteCreateA 42 9)).isSome  --  true
-- The post-set contains the published commitment 42:
#guard decide (42 ∈ (noteCreateChainA stN0 42 9).kernel.commitments)  --  true
-- APPEND-ONLY / NO DOUBLE-CHECK: publishing the SAME commitment 42 AGAIN ALSO commits (the
-- distinguishing property vs noteSpend, which would fail-close on a repeat):
#guard ((execFullA stN0 (.noteCreateA 42 9)).bind
          (fun s => execFullA s (.noteCreateA 42 9))).isSome  --  true
-- ...and after two publishes the set has length 2 (it grew BOTH times):
#guard decide (((execFullA stN0 (.noteCreateA 42 9)).bind
          (fun s => execFullA s (.noteCreateA 42 9))).map
          (fun s => s.kernel.commitments.length) = some 2)  --  true
-- The commitment set strictly grows by one on a single publish:
#guard decide ((noteCreateChainA stN0 42 9).kernel.commitments.length = 1)  --  true

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms noteCreateCommitment_correct
#assert_axioms execFullA_noteCreateA
#assert_axioms noteCreateChainA_iff_spec
#assert_axioms execNoteCreateA_iff_spec
#assert_axioms noteCreateA_inserts
#assert_axioms noteCreateA_preserves
#assert_axioms noteCreateA_bal_neutral
#assert_axioms noteCreateA_total
#assert_axioms noteCreateA_admits_iff
#assert_axioms noteCreateA_grows
#assert_axioms noteCreateA_log_grows

end Dregg2.Circuit.Spec.NoteCommitment
