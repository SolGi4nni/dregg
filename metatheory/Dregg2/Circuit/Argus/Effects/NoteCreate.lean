/-
# Dregg2.Circuit.Argus.Effects.NoteCreate — the note-COMMITMENT PUBLISH effect `noteCreate` welded
into the Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` welded the genuinely-different per-asset
ledger primitive against its OWN standalone v2 `Surface2` descriptor (the FULL 17-field `*_full_sound`
surface). This module welds the grow-only commitment-SET primitive `noteCreate` the SAME way: against
its OWN audited v2 `Surface2` descriptor (`Inst/noteCreateA.lean`'s `noteCreateA_full_sound`), the
strongest surface this effect genuinely supports.

`noteCreate` is the APPEND-ONLY dual of `noteSpend`: a `noteSpend` GROWS the `nullifiers` set under a
double-spend GATE (fail-closed on a repeated nullifier), but a `noteCreate` GROWS the `commitments`
SET with NO guard at all — the commitment set is append-only and a fresh commitment cannot conflict
(`apply_note_create`, dregg1). So the kernel step is the TOTAL, single-branch insert
`noteCreateCommitment k cm = { k with commitments := cm :: k.commitments }`
(`RecordKernel.lean:2136`) — balance-NEUTRAL, touching ONLY `commitments` (NOT `bal`/`nullifiers`/
`escrows`/any of the other 16 fields). That is EXACTLY the §A component-write primitive `setCommitments`
(`Stmt.lean:59`/`:102`): `interp (setCommitments g) k = some { k with commitments := g k }`. No new IR
constructor is needed; no guard is needed (noteCreate is unconditional). The cleanest possible body:
ONE component write, no gate.

## THE DESCRIPTOR SURFACE (the most load-bearing finding — read this).

`noteCreate` carries TWO circuit universes, and the choice of which to weld against is load-bearing:

  * The EFFECTVM per-row descriptor (`Emit/EffectVmEmitNoteCreate.lean`, `noteCreateVmDescriptor`) models
    the publish — RECONCILED onto the runtime hand-AIR — as BALANCE-NEUTRAL + nonce TICK:
    `new_bal_lo = old_bal_lo` (the note value is hidden in the commitment, never moved on the transparent
    ledger), the nonce ticks, the frame freezes. A PRIOR version modeled it as a transparent debit
    (`new_bal_lo = old_bal_lo − value`), which diverged from the universe-A balance-neutral convention;
    that divergence is now CLOSED at the source (the EffectVM descriptor + the Rust circuit AIR/trace are
    balance-neutral, matching the executor), so the EffectVM descriptor AGREES with the IR term's
    balance-neutral executor for EVERY note (`EffectVmEmitNoteCreate.noteCreate_balance_neutral_matches_univA`).

  * The v2 `Surface2` / `EffectCommit2` descriptor (`Inst/noteCreateA.lean`) is the GENUINE standalone
    full-state crown jewel: `noteCreateE` (the `EffectSpec2` whose touched component is the WHOLE
    `commitments` list via a `listComponent` full-list digest) and
    `noteCreateA_full_sound : satisfiedE2 … (noteCreateE …) … ⟹ NoteCreateASpec` — a FULL 17-field
    declarative post-state soundness, balance-NEUTRAL (`bal' = bal`), keyed on the CHAINED executor
    `execFullA`/`noteCreateChainA` via the independent `execNoteCreateA_iff_spec` (`Spec/notecommitment`).
    This is the SAME shielding convention as the executor (value hidden in the commitment, never moved on
    the transparent ledger), so it AGREES with the IR term's executor on the WHOLE state with NO
    divergence.

So this module welds against the v2 `Surface2` descriptor (the BalanceA surface) — strictly stronger
than a per-cell EffectVM weld AND divergence-free, because that descriptor binds the whole-state
full-list digest and shares the executor's balance-neutral convention. The EffectVM descriptor is NOW
ALSO balance-neutral, so the two surfaces AGREE: §6 (`noteCreate_effectvm_agrees_argus`) proves the
EffectVM descriptor's per-cell post-balance EQUALS the IR term's executor's, for every note — the
formerly-carried divergence is CLOSED, not relabeled.

This module is therefore HONEST in both directions:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_noteCreateStmt_eq_noteCreateCommitment`
      — the kernel insert `noteCreateCommitment` IS the Argus term, using `setCommitments`. New, standalone,
      the grow-only-SET analog of `interp_transferStmt_eq_recKExec`.

  (2) **Compile weld against noteCreate's OWN standalone v2 `Surface2` descriptor:** lift the cornerstone
      to the chained executor (`interp_noteCreateStmt_chained`), then weld to the standalone
      `noteCreateCircuit`/`noteCreateA_full_sound`. The conclusion is the FULL `NoteCreateASpec` agreement
      (all 17 kernel fields + the receipt log + the trivial guard) — a satisfying witness of noteCreate's
      own circuit agrees with the WHOLE post-state the IR term's executor produces. Strictly stronger than
      a per-cell weld, because noteCreate's standalone descriptor carries the whole-state full-list digest.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
whole-list-digest assumption enters ONLY inside the reused `noteCreateA_full_sound` (its
`compressNInjective`/`listLeafInjective`/`logHashInjective`/`RestIffNoCommitments` portal hypotheses),
not in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are
read-only; this file OWNS only its own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate

namespace Dregg2.Circuit.Argus.Effects.NoteCreate

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/noteCreateA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective`/`compressNInjective`/`listLeafInjective` live in `StateCommit`; `Surface2`/
-- `satisfiedE2`/`encodeE2` in `EffectCommit2`. (`effect2CircuitStep` is the `EffectRefinement` hub
-- abbrev for exactly `satisfiedE2 S E (encodeE2 S E …)`; we inline it here to keep this module's
-- v2-import surface to `Inst.noteCreateA`.)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.NoteCommitment
  (NoteCreateASpec noteCreateAdmit noteCreateReceipt execNoteCreateA_iff_spec
   noteCreateA_bal_neutral noteCreateA_total)
open Dregg2.Circuit.Inst.NoteCreateA
  (NoteCreateArgs noteCreateE noteCreateA_full_sound RestIffNoCommitments)

/-! ## §1 — The noteCreate effect as an Argus IR term (one component write, NO guard).

`noteCreateCommitment k cm = { k with commitments := cm :: k.commitments }` (`RecordKernel.lean:2136`)
is the kernel insert: TOTAL (always commits — a fresh commitment cannot conflict), balance-NEUTRAL,
touching ONLY `commitments`. The §A component-write primitive `setCommitments g`
(`Stmt.lean:59`/`:102`) writes EXACTLY one component (`commitments := g k`) and nothing else, and its
`interp` ALWAYS commits — the precise shape this unconditional grow-only insert needs. So the term is a
BARE `setCommitments` (no `guard` wrapper, because noteCreate has no admissibility gate), with the leaf
`fun k => cm :: k.commitments`. The contrast with transfer/createEscrow: NO gate at all, and the move is
the LIST side-table write `setCommitments` over a cons, NOT a `setCell`/`setBal` cell/ledger move. -/

/-- **The noteCreate effect as an IR term: the single `setCommitments` grow-only insert.** Unlike
transfer/mint/burn/createEscrow (gate, then move), noteCreate has NO gate — the body is the bare
`setCommitments` whose leaf prepends the fresh commitment `cm` onto the `commitments` SET, EXACTLY the
post-set `noteCreateCommitment` installs. The §A `setCommitments` primitive is the genuine list
side-table write a grow-only-SET effect assembles — no new constructor, no guard needed. -/
def noteCreateStmt (cm : Nat) : RecStmt :=
  RecStmt.setCommitments (fun k => cm :: k.commitments)

/-! ## §2 — The cornerstone: `interp` of the noteCreate term IS the kernel insert `noteCreateCommitment`. -/

/-- **The cornerstone (grow-only commitment SET).** `interp` of the noteCreate term IS the verified
kernel insert `noteCreateCommitment` — the same total function, by construction, exactly as the
transfer cornerstone, now over the `commitments` list side-table via `setCommitments`/a cons (NOT the
record-cell `setCell`/`recTransfer` nor the ledger `setBal`). This is the grow-only-SET
executor-refinement: the executor IS the meaning of the term. Note the absence of any `by_cases`
split — `setCommitments`' `interp` ALWAYS commits, and `noteCreateCommitment` is likewise total, so the
two partial functions coincide DEFINITIONALLY (the append-only "no double-check" property, in the IR). -/
theorem interp_noteCreateStmt_eq_noteCreateCommitment (cm : Nat) (k : RecordKernelState) :
    interp (noteCreateStmt cm) k = some (noteCreateCommitment k cm) := by
  simp only [noteCreateStmt, interp, noteCreateCommitment]

#assert_axioms interp_noteCreateStmt_eq_noteCreateCommitment

/-- **`noteCreateStmt_total` — the IR term ALWAYS COMMITS (the append-only, no-double-check property).**
Unlike `noteSpendStmt` (fail-closed on a repeated nullifier), the noteCreate term is UNCONDITIONAL —
there is ALWAYS a committed post-state, regardless of the pre-state. The distinguishing dual of the
double-spend gate, proved at the IR level. -/
theorem noteCreateStmt_total (cm : Nat) (k : RecordKernelState) :
    ∃ k', interp (noteCreateStmt cm) k = some k' :=
  ⟨noteCreateCommitment k cm, interp_noteCreateStmt_eq_noteCreateCommitment cm k⟩

#assert_axioms noteCreateStmt_total

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `noteCreateChainA` / `execFullA`.

The standalone noteCreate descriptor (§4) is keyed on the CHAINED executor `execFullA`/`noteCreateChainA`
over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.noteCreateA cm actor) =
some (noteCreateChainA s cm actor)` (`Spec/notecommitment.lean:96`). The §2 cornerstone is over the RAW
kernel insert `noteCreateCommitment`. The chained layer is exactly `noteCreateCommitment` on the kernel
PLUS the receipt-log prepend `escrowReceiptA actor :: s.log`. Because the kernel step is TOTAL (no gate),
the lift carries NO side-condition (unlike balanceA's `acceptsEffects` dst-liveness or transfer's gate) —
the chained executor ALWAYS commits the IR term's kernel meaning, augmented with the receipt row. -/

/-- **`interp_noteCreateStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the §2 cornerstone commits on the kernel (`interp (noteCreateStmt cm) st.kernel = some k'`), the unified
action executor `execFullA st (.noteCreateA cm actor)` commits to the chained state
`⟨k', escrowReceiptA actor :: st.log⟩`. So the Argus term's kernel meaning lifts to the chained executor
the standalone descriptor speaks about — with NO carried side-condition (noteCreate is unconditional, so
the chained arm is total). -/
theorem interp_noteCreateStmt_chained
    (st : RecChainedState) (cm : Nat) (actor : CellId) (k' : RecordKernelState)
    (hexec : interp (noteCreateStmt cm) st.kernel = some k') :
    execFullA st (.noteCreateA cm actor) = some { kernel := k', log := escrowReceiptA actor :: st.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel insert `noteCreateCommitment`.
  rw [interp_noteCreateStmt_eq_noteCreateCommitment] at hexec
  simp only [Option.some.injEq] at hexec
  -- `execFullA st (.noteCreateA cm actor)` reduces to `some (noteCreateChainA st cm actor)`, whose kernel
  -- is `noteCreateCommitment st.kernel cm = k'` and whose log is the receipt-prepended chain.
  show execFullA st (.noteCreateA cm actor) = _
  simp only [execFullA, noteCreateChainA, ← hexec]

#assert_axioms interp_noteCreateStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of noteCreate's OWN standalone v2 `Surface2` circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against noteCreate's GENUINE standalone descriptor `noteCreateCircuit S … (noteCreateE …)`
(the v2 `Surface2` circuit whose soundness is `noteCreateA_full_sound`), the whole-state full-list-digest
surface — see the descriptor surface investigation in this file's header. The executor side is routed
through §3 (`interp` ⟹ `execFullA`) and the independent `execNoteCreateA_iff_spec` (executor ⟺
`NoteCreateASpec`); the circuit side is the audited `noteCreateA_full_sound` (circuit ⟹ `NoteCreateASpec`).
Both name the SAME `NoteCreateASpec`, so they PROVABLY agree on the WHOLE 17-field state + the log —
strictly stronger than a per-cell weld, and DIVERGENCE-FREE (this descriptor shares the executor's
balance-neutral convention; the EffectVM descriptor is now ALSO balance-neutral and AGREES — §6). -/

/-- The Argus circuit interpretation of a `noteCreate` term: noteCreate's OWN audited standalone v2
`Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (noteCreateE LE cN hN hLE)
(encodeE2 …)` satisfied on the encoded `(st, ⟨cm, actor⟩, st')` triple (DEFINITIONALLY the
`EffectRefinement` hub's `effect2CircuitStep S (noteCreateE …) st ⟨cm,actor⟩ st'`, inlined here so this
module's v2-import surface is only `Inst.noteCreateA`). Its soundness `noteCreateA_full_sound` pins the
complete `NoteCreateASpec`. The `noteCreate`-keyed analog of `balanceACircuit`, in the descriptor
universe where noteCreate carries its OWN genuine full-state circuit (the whole-state full-list digest). -/
def noteCreateCircuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (st : RecChainedState) (cm : Nat) (actor : CellId) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (noteCreateE LE cN hN hLE)
    (encodeE2 S (noteCreateE LE cN hN hLE) st ⟨cm, actor⟩ st')

/-- **`noteCreateASpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`NoteCreateASpec st cm actor ·` are equal. Rather than re-derive this field-by-field, we route through the
PROVEN executor⟺spec corner `execNoteCreateA_iff_spec`: each `NoteCreateASpec` reconstructs the SAME
committed value `execFullA st (.noteCreateA cm actor) = some ·`, and `some` is injective. This is exactly
the sense in which `NoteCreateASpec` is functional — it determines the post-state — so the circuit-side
and executor-side spec facts collapse to one welded post-state (the BalanceA `*_unique` analog). -/
theorem noteCreateASpec_unique {st st₁ st₂ : RecChainedState} {cm : Nat} {actor : CellId}
    (h₁ : NoteCreateASpec st cm actor st₁) (h₂ : NoteCreateASpec st cm actor st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.noteCreateA cm actor) = some st₁ :=
    (execNoteCreateA_iff_spec st cm actor st₁).mpr h₁
  have e₂ : execFullA st (.noteCreateA cm actor) = some st₂ :=
    (execNoteCreateA_iff_spec st cm actor st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`noteCreate_compile_sound` — the welded soundness (noteCreate slice), against noteCreate's OWN descriptor.**

Suppose, for the Argus noteCreate term `noteCreateStmt cm`:
  * the standalone noteCreate circuit `noteCreateCircuit S LE cN hN hLE st cm actor st'` (= `noteCreateE`'s
    full-state v2 arithmetization satisfied on the encoded triple) holds, under the realizable
    whole-list-digest portals (`hRest : RestIffNoCommitments S.RH`, `hLog : logHashInjective S.LH`,
    `hN : compressNInjective cN`, `hLE : listLeafInjective LE`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (noteCreateStmt cm) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := escrowReceiptA actor :: st.log }`. I.e. noteCreate's OWN circuit
and the IR term AGREE on the WHOLE 17-field RecordKernelState (`commitments` prepended with `cm`, every
other field — INCLUDING `bal`, balance-NEUTRAL — frozen) AND the receipt log AND the trivial guard — the
full `NoteCreateASpec`, not a per-cell projection. So the circuit the prover runs for noteCreate pins the
complete state the IR term's executor produces. NO nonce-tick / collapsed-field divergence enters this
surface (the v2 descriptor is balance-neutral, matching the executor); the EffectVM descriptor is now
ALSO balance-neutral and AGREES with this surface (§6). -/
theorem noteCreate_compile_sound
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (cm : Nat) (actor : CellId) (k' : RecordKernelState)
    (hcirc : noteCreateCircuit S LE cN hN hLE st cm actor st')
    (hexec : interp (noteCreateStmt cm) st.kernel = some k') :
    st' = { kernel := k', log := escrowReceiptA actor :: st.log } := by
  -- circuit side: noteCreate's OWN audited soundness forces the FULL `NoteCreateASpec` on `(st, ⟨cm,actor⟩, st')`.
  have hspec : NoteCreateASpec st cm actor st' :=
    noteCreateA_full_sound S LE cN hN hLE hRest hLog st ⟨cm, actor⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.noteCreateA cm actor) = some ⟨k', receipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `NoteCreateASpec st cm actor ⟨k', receipt :: log⟩`.
  have hspec' : NoteCreateASpec st cm actor { kernel := k', log := escrowReceiptA actor :: st.log } :=
    (execNoteCreateA_iff_spec st cm actor _).mp (interp_noteCreateStmt_chained st cm actor k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact noteCreateASpec_unique hspec hspec'

#assert_axioms noteCreate_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely GROWS the commitment set (insert observable), is balance-
NEUTRAL, and ALWAYS commits (append-only — the distinguishing no-double-check, the dual of noteSpend's
fail-closed gate).

The cornerstone/weld would be hollow if noteCreate never committed, if the insert were a no-op, or if it
touched `bal`. A concrete kernel exercises a real growth; the balance-neutrality + append-only theorems
pin the effect's genuine content. (noteCreate is total BY DESIGN, so — unlike a gated effect — there is no
"rejection" tooth; the genuine teeth are the observable GROWTH and the append-only no-double-check.) -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts, cell 0 holds 30 of asset 0 on
the genuine per-asset ledger `bal`, an EMPTY commitment set and empty nullifier set. -/
def kN0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 30 else 0 }

/-- **NON-VACUITY (the INSERT is OBSERVABLE).** The committed publish GROWS the commitment set from `[]`
to `[42]` — the fresh commitment `42` genuinely lands in the set (the `setCommitments`/cons insert is
real, not a no-op). -/
theorem noteCreateStmt_inserts :
    (interp (noteCreateStmt 42) kN0).map (fun k => k.commitments) = some [42] := by
  rw [interp_noteCreateStmt_eq_noteCreateCommitment]
  decide

/-- **NON-VACUITY (the published commitment is a MEMBER).** After the publish, `42 ∈ commitments` — the
membership the off-ledger note-tree relies on. -/
theorem noteCreateStmt_member :
    (interp (noteCreateStmt 42) kN0).map (fun k => decide (42 ∈ k.commitments)) = some true := by
  rw [interp_noteCreateStmt_eq_noteCreateCommitment]
  decide

/-- **NON-VACUITY (the set STRICTLY grows by one).** The committed publish raises `commitments.length`
from `0` to `1` — the effect is never a no-op on its tracked set. -/
theorem noteCreateStmt_grows :
    (interp (noteCreateStmt 42) kN0).map (fun k => k.commitments.length) = some 1 := by
  rw [interp_noteCreateStmt_eq_noteCreateCommitment]
  decide

/-- **NON-VACUITY (BALANCE NEUTRALITY — the conservation punchline).** The committed publish leaves the
per-asset ledger entry `(0, 0)` UNTOUCHED at `30` — noteCreate moves NO transparent value (it grows only
`commitments`, never `bal`). The balance-neutral convention BOTH the v2 surface and the (now-fixed)
EffectVM descriptor share (§6), proved on the term. -/
theorem noteCreateStmt_bal_neutral :
    (interp (noteCreateStmt 42) kN0).map (fun k => k.bal 0 0) = some 30 := by
  rw [interp_noteCreateStmt_eq_noteCreateCommitment]
  decide

/-- **NON-VACUITY (APPEND-ONLY / NO DOUBLE-CHECK).** Publishing the SAME commitment `42` AGAIN on the
post-state ALSO commits, growing the set to length `2` — the distinguishing property vs `noteSpend`,
which would FAIL-CLOSE on a repeat. The composed append-only barrier, in the IR. -/
theorem noteCreateStmt_append_only :
    ((interp (noteCreateStmt 42) kN0).bind (interp (noteCreateStmt 42))).map
        (fun k => k.commitments.length) = some 2 := by
  rw [interp_noteCreateStmt_eq_noteCreateCommitment]
  simp only [Option.bind]
  rw [interp_noteCreateStmt_eq_noteCreateCommitment]
  decide

#assert_axioms noteCreateStmt_inserts
#assert_axioms noteCreateStmt_member
#assert_axioms noteCreateStmt_grows
#assert_axioms noteCreateStmt_bal_neutral
#assert_axioms noteCreateStmt_append_only

/-! ## §6 — THE CLOSED DIVERGENCE — now AGREEMENT: the EffectVM descriptor matches this balance-neutral weld.

This weld (§4) is against the v2 `Surface2` descriptor, which shares the executor's balance-NEUTRAL
convention. The OTHER (EffectVM per-row) descriptor `EffectVmEmitNoteCreate.noteCreateVmDescriptor` was
FIXED (this campaign) to ALSO be balance-neutral (`post.balLo = pre.balLo`; the formerly-carried
transparent-debit divergence is closed at the source — the Rust circuit AIR/trace are balance-neutral
too, matching the executor). So both surfaces now agree: we PROVE, at the Argus layer, that the EffectVM
descriptor's per-cell post-balance EQUALS the IR term's executor's post-balance, for EVERY note (no
`value = 0` side-condition). The divergence is CLOSED, not relabeled. -/

/-- **`noteCreate_effectvm_agrees_argus` — the CLOSED divergence, now AGREEMENT at the Argus layer.** The
Argus IR term's executor is BALANCE-NEUTRAL: on a committed publish the post-state's per-asset ledger
entry `(c, asset)` equals the pre-state's (`noteCreateA_bal_neutral`). The EffectVM per-row descriptor is
NOW ALSO balance-neutral: its post-balance for this entry is the FROZEN `effPost` with `effPost = pre`
(after the fix — `CellNoteSpec`'s `post.balLo = pre.balLo`). So the EffectVM descriptor's post-balance
EQUALS the IR term's executor's post-balance — they AGREE for every note, the shielding-convention
divergence is CLOSED. We take the EffectVM post-balance `effPost` as an explicit parameter together with
the descriptor's freeze fact `heff : effPost = st.kernel.bal c asset`, and conclude it coincides with the
executor's actual post-balance `st'.kernel.bal c asset`. -/
theorem noteCreate_effectvm_agrees_argus
    (st st' : RecChainedState) (cm : Nat) (actor c : CellId) (asset : AssetId) (effPost : ℤ)
    (hexec : execFullA st (.noteCreateA cm actor) = some st')
    -- the EffectVM descriptor FREEZES the entry (balance-neutral): its post-balance is the pre-balance.
    (heff : effPost = st.kernel.bal c asset) :
    -- AGREEMENT: the EffectVM post-balance EQUALS the IR term's executor post-balance — no divergence.
    effPost = st'.kernel.bal c asset := by
  -- the IR term's executor freezes the ledger (balance-neutral) ⇒ the entry is unchanged …
  have hneutral : st'.kernel.bal = st.kernel.bal := noteCreateA_bal_neutral st cm actor st' hexec
  have hentry : st'.kernel.bal c asset = st.kernel.bal c asset := by rw [hneutral]
  -- … and the EffectVM descriptor's freeze is the SAME unchanged entry — they agree, no divergence.
  rw [heff, hentry]

#assert_axioms noteCreate_effectvm_agrees_argus

end Dregg2.Circuit.Argus.Effects.NoteCreate
