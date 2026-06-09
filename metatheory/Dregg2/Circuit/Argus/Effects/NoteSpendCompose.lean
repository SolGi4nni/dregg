/-
# Dregg2.Circuit.Argus.Effects.NoteSpendCompose — the COMPOSED noteSpend (proof-gated double-spend)
welded into the Argus IR.

`Argus/Effects/NoteSpend.lean` welded the BASE noteSpend non-membership: `noteSpendStmt nf =
insFresh (fun _ => nf)`, whose `interp` IS the kernel double-spend gate `noteSpendNullifier`
(`nf ∉ nullifiers ⇒ insert; else fail-closed`), with the no-double-spend carried INLINE in the term
(`noteSpendStmt_no_double_spend`). This module welds the genuinely-composed sibling the executor
actually runs — the arm `execFullA s (.noteSpendA nf actor spendProof) = noteSpendChainA s nf actor
spendProof` (`TurnExecutorFull.lean:3845`) — which WRAPS the base noteSpend in TWO additional pieces
the base term does not carry:

  noteSpendChainA s nf actor spendProof   (`TurnExecutorFull.lean:2178`)
    = if spendProof = true then
        match noteSpendNullifier s.kernel nf with
        | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
        | none    => none
      else none

so the composed effect is the base `noteSpendNullifier` non-membership-and-insert, COMPOSED UNDER

  (i)  the §8 STARK spending-proof gate `spendProof = true` (`apply.rs:929` "spending proof
       verification failed" — a fail-closed gate the base kernel `noteSpendNullifier` lacks), and
  (ii) the receipt-chain prepend `escrowReceiptA actor :: log` (a self-`Turn` on `actor`, `amt = 0`).

## The IR boundary, stated precisely (NOT papered)

The Argus IR `interp : RecStmt → RecordKernelState → Option RecordKernelState` is a transformer of the
KERNEL state — it has NO `log` component (`RecChainedState = kernel × log`, `RecordKernel.lean:938`).
So a single `RecStmt` term can faithfully capture EXACTLY the kernel-level composed step — gate (i)
COMPOSED WITH the base non-membership — but the receipt-chain prepend (ii) is a CHAINED-layer concern,
the same boundary `Argus/Effects/BalanceA.lean` carries via `interp_balanceAStmt_chained` (the IR term
produces the kernel post-state; a separate LIFT theorem connects it to `execFullA` with the log). We
follow that exact two-part discipline:

  * **§1 cornerstone (kernel-level):** `noteSpendComposeStmt nf spendProof = seq (guard (fun _ =>
    spendProof)) (noteSpendStmt nf)` — the base noteSpend term COMPOSED UNDER the §8 proof gate. Its
    `interp` IS the kernel-level composed step `if spendProof then noteSpendNullifier k nf else none`,
    proved EXACTLY (`interp_noteSpendComposeStmt_eq_kStep`). This adds gate (i) over the base term's
    non-membership — the term's own meaning now fail-closes WITHOUT the proof too.

  * **§2 lift to the chained `execFullA`:** when the §1 cornerstone commits on the kernel, the unified
    action executor commits to the chained state `⟨k', escrowReceiptA actor :: log⟩`
    (`interp_noteSpendComposeStmt_chained`). UNLIKE balanceA (which needs an `acceptsEffects`
    dst-liveness side-condition), noteSpend's chained arm adds NOTHING but the receipt — so the lift is
    UNCONDITIONAL. This is the receipt-chain prepend (ii), carried as the honest chained connector.

  * **§3 compile weld:** against noteSpend's OWN standalone full-state descriptor
    `noteSpendA_full_sound` (`Inst/noteSpendA.lean`, the v2 `Surface2` circuit whose touched component
    is the WHOLE `nullifiers` list `funcComponent`-style digest), routed executor-side through §2 +
    the independent `execFullA_noteSpend_iff_spec`. Both name the SAME bespoke full-state
    `NoteSpendSpec` (all 17 RecordKernelState fields + the receipt log), so they PROVABLY agree on the
    WHOLE post-state — strictly stronger than a per-cell projection (this PREFERS the Surface2
    full_sound surface, as the task directs).

## What the weld pins vs. assumes (HONEST SURFACE — do NOT over-read)

The conclusion `st' = { kernel := k', log := escrowReceiptA actor :: st.log }` is the FULL agreement:
the circuit-pinned chained post-state IS the chained post-state the IR term's executor produces (the
nullifier set grown by exactly `nf`, all 16 other kernel fields frozen, the receipt prepended). The
DIVERGENCE carried explicitly (the §1↔§2 split, not hidden): the receipt-chain row (ii) is NOT a
clause of the kernel `interp` — it is supplied by the §2 lift, because the Argus IR is kernel-state-
only. No IR primitive is LACKING for the kernel-level composed step (the base `noteSpendStmt` +
`guard` fully capture gates (i)+(ii-kernel)); the log is the chained-layer connector, exactly as
balanceA's weld treats it.

The Poseidon2-CR / whole-list-digest assumption enters ONLY inside the reused `noteSpendA_full_sound`
(its `compressNInjective cN` + `listLeafInjective LE` portals), not in the welded conclusion's
statement. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every headline theorem; no
`sorry`, no `:= True`, no `native_decide`. Imports are READ-ONLY; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Effects.NoteSpend
import Dregg2.Circuit.Inst.noteSpendA

namespace Dregg2.Circuit.Argus.Effects.NoteSpendCompose

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp noteSpendStmt interp_noteSpendStmt_eq_noteSpendNullifier)
-- noteSpend's OWN standalone full-state descriptor lives in `Inst/noteSpendA`; the bespoke spec +
-- its executor corner in `Spec/notenullifier`. Broad opens so the names resolve unqualified.
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoNullifiers satisfiedE2 encodeE2)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.Spec.NoteNullifier
  (NoteSpendSpec noteSpendGuard noteSpendReceipt execFullA_noteSpend_iff_spec)
open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs noteSpendE noteSpendA_full_sound)

/-! ## §1 — The COMPOSED noteSpend as an Argus IR term (the §8 proof gate ∘ the base non-membership).

`noteSpendChainA`'s kernel content is `if spendProof = true then noteSpendNullifier s.kernel nf else
none` — the base noteSpend `noteSpendNullifier` (the double-spend gate `noteSpendStmt` already welds)
COMPOSED UNDER the §8 spending-proof gate `spendProof = true`. We capture that kernel-level step
term-for-term: a `Bool` `guard (fun _ => spendProof)` (the §8 proof gate — a CONSTANT predicate of the
state, since `spendProof` is an effect argument, not a state read), SEQ the base `noteSpendStmt nf`
(the non-membership-and-insert). The composition is genuine: the term now fail-closes BOTH on a stale
nullifier (the base term's job) AND on a missing proof (the new outer gate). -/

/-- The kernel-level COMPOSED step the executor's `noteSpendChainA` runs (modulo the chained-layer
receipt): the base `noteSpendNullifier` double-spend gate COMPOSED UNDER the §8 spending-proof gate
`spendProof = true`. Stated INDEPENDENTLY of the IR term (so §1's cornerstone is a genuine refinement,
not a definitional unfold of the term). On `spendProof = false` it fail-closes (`none`), exactly the
`apply.rs:929` proof-verification rejection. -/
def noteSpendComposeKStep (k : RecordKernelState) (nf : Nat) (spendProof : Bool) :
    Option RecordKernelState :=
  if spendProof = true then noteSpendNullifier k nf else none

/-- **`noteSpendComposeStmt nf spendProof`** — the composed noteSpend effect as an Argus IR term: the
§8 proof gate `guard (fun _ => spendProof)` SEQ the base `noteSpendStmt nf` (the non-membership-and-
insert this file's sibling `NoteSpend.lean` welded). A WRAPPER over the base noteSpend term — its
meaning is the base double-spend gate, now ALSO gated on the spending proof. -/
def noteSpendComposeStmt (nf : Nat) (spendProof : Bool) : RecStmt :=
  RecStmt.seq (RecStmt.guard (fun _ => spendProof)) (noteSpendStmt nf)

/-- **`interp_noteSpendComposeStmt_eq_kStep` — the cornerstone (executor IS the term, kernel level).**
`interp` of the composed noteSpend term IS the kernel-level composed step `noteSpendComposeKStep` —
the §8 proof gate composed with the base `noteSpendNullifier` non-membership, the SAME partial
function `noteSpendChainA` runs on the kernel, by construction. The base term's `interp` (=
`noteSpendNullifier`, `interp_noteSpendStmt_eq_noteSpendNullifier`) is reused VERBATIM under the new
outer guard. -/
theorem interp_noteSpendComposeStmt_eq_kStep (nf : Nat) (spendProof : Bool) (k : RecordKernelState) :
    interp (noteSpendComposeStmt nf spendProof) k = noteSpendComposeKStep k nf spendProof := by
  simp only [noteSpendComposeStmt, interp, noteSpendComposeKStep]
  by_cases hp : spendProof = true
  · -- proof present: the outer guard fires (`some k`), the bind runs the base term, whose `interp`
    -- IS `noteSpendNullifier` (the welded base cornerstone). Rewrite BOTH the interp-guard `if` and
    -- the kStep `if` on the SAME hypothesis.
    rw [if_pos hp, if_pos hp]
    simp only [Option.bind, interp_noteSpendStmt_eq_noteSpendNullifier]
  · -- proof absent: the outer guard fails (`none`), the bind short-circuits, exactly the kStep's
    -- `else none`.
    rw [if_neg hp, if_neg hp]
    simp only [Option.bind]

#assert_axioms interp_noteSpendComposeStmt_eq_kStep

/-! ## §1a — the composition has teeth: BOTH the proof gate and the base non-membership fail closed.

The whole point of the composition is that it adds the §8 proof gate ON TOP of the base double-spend
gate — so the term must fail-close on EITHER a missing proof OR a stale nullifier, and commit only
when BOTH hold. We pin all three. -/

/-- **`noteSpendComposeStmt_requires_proof` — PROVED (the §8 proof teeth, in the term).** WITHOUT the
spending proof (`spendProof = false`), the composed term fail-closes (`= none`) — EVEN on a fresh
nullifier. The outer §8 gate the base `noteSpendStmt` lacked, now enforced by the term's own `interp`.
-/
theorem noteSpendComposeStmt_requires_proof (nf : Nat) (k : RecordKernelState)
    (hp : spendProof = false) :
    interp (noteSpendComposeStmt nf spendProof) k = none := by
  rw [interp_noteSpendComposeStmt_eq_kStep]
  simp only [noteSpendComposeKStep, hp, if_neg (by decide : ¬ (false = true))]

/-- **`noteSpendComposeStmt_no_double_spend` — PROVED (the base non-membership SURVIVES composition).**
If the composed term COMMITS, the spent nullifier was NOT already in the set (`nf ∉ k.nullifiers`) —
the base double-spend guarantee is PRESERVED under the §8-proof wrapper (the composition does not
weaken it). -/
theorem noteSpendComposeStmt_no_double_spend {nf : Nat} {spendProof : Bool}
    {k k' : RecordKernelState} (h : interp (noteSpendComposeStmt nf spendProof) k = some k') :
    nf ∉ k.nullifiers := by
  rw [interp_noteSpendComposeStmt_eq_kStep] at h
  simp only [noteSpendComposeKStep] at h
  by_cases hp : spendProof = true
  · rw [if_pos hp] at h
    -- the base step committed ⇒ the base non-membership lemma applies (via the welded base cornerstone).
    rw [← interp_noteSpendStmt_eq_noteSpendNullifier] at h
    exact Dregg2.Circuit.Argus.noteSpendStmt_no_double_spend h
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-- **`noteSpendComposeStmt_commits_iff` — PROVED (the composition criterion: BOTH gates).** The
composed term COMMITS IFF the §8 proof verified AND the nullifier is fresh — the two gates are jointly
necessary and sufficient, the kernel-level shadow of `execFullA_noteSpend_commits_iff`. -/
theorem noteSpendComposeStmt_commits_iff (nf : Nat) (spendProof : Bool) (k : RecordKernelState) :
    (∃ k', interp (noteSpendComposeStmt nf spendProof) k = some k')
      ↔ (spendProof = true ∧ nf ∉ k.nullifiers) := by
  simp only [interp_noteSpendComposeStmt_eq_kStep, noteSpendComposeKStep]
  by_cases hp : spendProof = true
  · rw [if_pos hp]
    by_cases hin : nf ∈ k.nullifiers
    · rw [note_no_double_spend k nf hin]
      constructor
      · rintro ⟨k', hk'⟩; exact absurd hk' (by simp)
      · rintro ⟨_, hg⟩; exact absurd hin hg
    · constructor
      · intro _; exact ⟨hp, hin⟩
      · intro _
        refine ⟨{ k with nullifiers := nf :: k.nullifiers }, ?_⟩
        unfold noteSpendNullifier; rw [if_neg hin]
  · rw [if_neg hp]
    constructor
    · rintro ⟨k', hk'⟩; exact absurd hk' (by simp)
    · rintro ⟨hg, _⟩; exact absurd hg hp

#assert_axioms noteSpendComposeStmt_requires_proof
#assert_axioms noteSpendComposeStmt_no_double_spend
#assert_axioms noteSpendComposeStmt_commits_iff

/-! ## §2 — Lifting the kernel cornerstone to the CHAINED executor `execFullA` (the receipt connector).

noteSpend's OWN standalone full-state descriptor (§3) is keyed on the CHAINED executor `execFullA`
over `RecChainedState` — the arm `execFullA s (.noteSpendA nf actor spendProof) = noteSpendChainA s nf
actor spendProof`. The §1 cornerstone is over the RAW kernel step `noteSpendComposeKStep`. The chained
layer is exactly that PLUS the receipt-chain prepend `escrowReceiptA actor :: s.log` — and, crucially,
NOTHING ELSE (unlike balanceA, which adds an `acceptsEffects` dst-liveness pre-gate; noteSpend's
chained arm has NO extra gate). So the lift is UNCONDITIONAL. This is the chained-layer connector (ii),
carried faithfully. -/

/-- **`interp_noteSpendComposeStmt_chained` — the IR term's executor, lifted to the chained
`execFullA`.** When the §1 cornerstone commits on the kernel (`interp (noteSpendComposeStmt nf
spendProof) st.kernel = some k'`), the unified action executor `execFullA st (.noteSpendA nf actor
spendProof)` commits to the chained state `⟨k', escrowReceiptA actor :: st.log⟩`. UNCONDITIONALLY —
noteSpend's chained arm adds only the receipt (no dst-liveness side-condition). So the Argus term's
kernel meaning lifts to the chained executor the standalone descriptor speaks about, with the receipt
the honest chained connector. -/
theorem interp_noteSpendComposeStmt_chained
    (st : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) (k' : RecordKernelState)
    (hexec : interp (noteSpendComposeStmt nf spendProof) st.kernel = some k') :
    execFullA st (.noteSpendA nf actor spendProof)
      = some { kernel := k', log := escrowReceiptA actor :: st.log } := by
  -- the §1 cornerstone turns the IR term into the kernel-level composed step.
  rw [interp_noteSpendComposeStmt_eq_kStep] at hexec
  simp only [noteSpendComposeKStep] at hexec
  -- `execFullA st (.noteSpendA …)` reduces to `noteSpendChainA st nf actor spendProof`; on
  -- `spendProof = true` it opens to `match noteSpendNullifier st.kernel nf …`, and `hexec` names it.
  show noteSpendChainA st nf actor spendProof = some { kernel := k', log := escrowReceiptA actor :: st.log }
  unfold noteSpendChainA
  by_cases hp : spendProof = true
  · rw [if_pos hp] at hexec ⊢
    -- `hexec : noteSpendNullifier st.kernel nf = some k'`; rewrite the `match` on it.
    rw [hexec]
  · -- proof absent ⇒ the kStep returned `none`, contradicting `hexec : none = some k'`.
    rw [if_neg hp] at hexec; exact absurd hexec (by simp)

#assert_axioms interp_noteSpendComposeStmt_chained

/-! ## §3 — THE COMPILE WELD: a satisfying witness of noteSpend's OWN standalone full-state circuit
agrees with the FULL chained post-state the IR term's executor interpretation produces.

This welds against noteSpend's GENUINE standalone descriptor `noteSpendE` (the v2 `Surface2` circuit
whose soundness is `noteSpendA_full_sound`, touched component the WHOLE `nullifiers` list digest —
`ListDigestBindsList`, so a drop/reorder of an existing nullifier is REJECTED, anti-replay teeth at the
circuit level). The executor side is routed through §2 (`interp` ⟹ `execFullA`) and the independent
`execFullA_noteSpend_iff_spec` (executor ⟺ `NoteSpendSpec`); the circuit side is the audited
`noteSpendA_full_sound` (circuit ⟹ `NoteSpendSpec`). Both name the SAME `NoteSpendSpec`, so they
PROVABLY agree on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld.
-/

/-- **`noteSpendSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `NoteSpendSpec st nf actor spendProof ·` are equal. Rather than re-derive field-by-field, we
route through the PROVEN executor⟺spec corner `execFullA_noteSpend_iff_spec`: each `NoteSpendSpec`
reconstructs the SAME committed value `execFullA st (.noteSpendA …) = some ·`, and `some` is injective.
This is the sense in which `NoteSpendSpec` is functional — it determines the post-state — so the
circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem noteSpendSpec_unique {st st₁ st₂ : RecChainedState} {nf : Nat} {actor : CellId}
    {spendProof : Bool} (h₁ : NoteSpendSpec st nf actor spendProof st₁)
    (h₂ : NoteSpendSpec st nf actor spendProof st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.noteSpendA nf actor spendProof) = some st₁ :=
    (execFullA_noteSpend_iff_spec st nf actor spendProof st₁).mpr h₁
  have e₂ : execFullA st (.noteSpendA nf actor spendProof) = some st₂ :=
    (execFullA_noteSpend_iff_spec st nf actor spendProof st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- The Argus circuit interpretation of a composed `noteSpendA` term: noteSpend's OWN audited
standalone v2 `Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (noteSpendE …)
(encodeE2 …)` satisfied on the encoded `(st, args, st')` triple. Its soundness `noteSpendA_full_sound`
pins the complete `NoteSpendSpec`. The `noteSpendA`-keyed analog of `balanceACircuit`, in the
descriptor universe where noteSpend carries its OWN genuine full-state circuit. -/
def noteSpendComposeCircuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (st : RecChainedState) (args : NoteSpendArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) st args st')

/-- **`noteSpendCompose_compile_sound` — the welded soundness (composed noteSpend), against
noteSpend's OWN full-state descriptor.**

Suppose, for the Argus composed-noteSpend term `noteSpendComposeStmt nf spendProof`:
  * the standalone noteSpend circuit `noteSpendComposeCircuit S LE cN hN hLE st ⟨nf, actor,
    spendProof⟩ st'` (= `noteSpendE`'s full-state v2 arithmetization satisfied on the encoded triple)
    holds, under the realizable whole-list-digest portals (`hRest : RestIffNoNullifiers S.RH`,
    `hLog : logHashInjective S.LH`, `hN : compressNInjective cN`, `hLE : listLeafInjective LE`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (noteSpendComposeStmt nf
    spendProof) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := escrowReceiptA actor :: st.log }`. I.e. noteSpend's OWN circuit
and the IR term AGREE on the WHOLE 17-field RecordKernelState (the `nullifiers` set grown by exactly
`nf`, every other field frozen) AND the receipt log — the full `NoteSpendSpec`, not a per-cell
projection. So the circuit the prover runs for the composed noteSpend pins the complete chained state
the IR term's executor produces.

The DIVERGENCE carried (NOT papered): the receipt-chain row `escrowReceiptA actor :: st.log` is NOT a
clause of the kernel-state `interp` (the Argus IR is kernel-state-only); it is supplied by the §2 lift
`interp_noteSpendComposeStmt_chained`. The kernel-level composed step (the §8 proof gate ∘ the base
non-membership) is captured EXACTLY by the term; the log is the chained-layer connector, exactly as
`balanceA_compile_sound` treats it. -/
theorem noteSpendCompose_compile_sound
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (k' : RecordKernelState)
    (hcirc : noteSpendComposeCircuit S LE cN hN hLE st ⟨nf, actor, spendProof⟩ st')
    (hexec : interp (noteSpendComposeStmt nf spendProof) st.kernel = some k') :
    st' = { kernel := k', log := escrowReceiptA actor :: st.log } := by
  -- circuit side: noteSpend's OWN audited soundness forces the FULL `NoteSpendSpec` on `(st, args, st')`.
  have hspec : NoteSpendSpec st nf actor spendProof st' :=
    noteSpendA_full_sound S LE cN hN hLE hRest hLog st ⟨nf, actor, spendProof⟩ st' hcirc
  -- executor side: the §2 lift gives `execFullA st (.noteSpendA …) = some ⟨k', receipt :: st.log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `NoteSpendSpec st nf actor spendProof
  -- ⟨k', receipt :: st.log⟩`.
  have hspec' : NoteSpendSpec st nf actor spendProof
      { kernel := k', log := escrowReceiptA actor :: st.log } :=
    (execFullA_noteSpend_iff_spec st nf actor spendProof _).mp
      (interp_noteSpendComposeStmt_chained st nf actor spendProof k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every field + the log).
  exact noteSpendSpec_unique hspec hspec'

#assert_axioms noteSpendSpec_unique
#assert_axioms noteSpendCompose_compile_sound

/-! ## §4 — NON-VACUITY: the composed term genuinely INSERTS under the proof gate, and fail-closes on
EACH of the two gates (stale nullifier, missing proof). Plus the welded descriptor is the genuine
full-state one (not the empty placeholder).

The cornerstone/weld would be hollow if the composed term never committed, if the insert were a no-op,
or if either gate admitted everything. A concrete kernel `kNSC` (live accounts {0,1}, empty nullifier
set) exercises a real proof-gated insert; the rejection lemmas show BOTH gates fail closed. -/

/-- A concrete kernel for the witnesses: live accounts {0, 1}, empty nullifier set, empty caps. -/
def kNSC : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [], caps := fun _ => [], nullifiers := [] }

-- The composed term is genuinely two-gated, three-way non-vacuous:
-- a fresh nullifier WITH a valid proof COMMITS; a stale nullifier is REJECTED; a missing proof is
-- REJECTED even on a fresh nullifier.
#guard ((interp (noteSpendComposeStmt 7 true) kNSC).isSome)                       -- fresh ∧ proof ⇒ commit
#guard ((interp (noteSpendComposeStmt 7 false) kNSC).isNone)                      -- fresh ∧ NO proof ⇒ reject
#guard (((interp (noteSpendComposeStmt 7 true) kNSC).map (fun k => k.nullifiers)) == some [7])  -- inserts nf

/-- **NON-VACUITY (the INSERT is OBSERVABLE under the proof gate).** Running the composed term on
`kNSC` with a fresh nullifier `7` and a VALID §8 proof commits, and the nullifier set grows from `[]`
to `[7]`: the proof-gated insert is a real, observable mutation (not a no-op). -/
theorem noteSpendComposeStmt_inserts :
    (interp (noteSpendComposeStmt 7 true) kNSC).map (fun k => k.nullifiers) = some [7] := by
  rw [interp_noteSpendComposeStmt_eq_kStep]
  decide

/-- **NON-VACUITY (fail-closed: missing proof).** A fresh-nullifier spend WITHOUT the §8 proof
(`spendProof = false`) does NOT commit — the term returns `none` (the new outer §8 gate fail-closes),
EVEN though the nullifier `7` is fresh. The §8 proof teeth the base `noteSpendStmt` lacked. -/
theorem noteSpendComposeStmt_rejects_no_proof :
    interp (noteSpendComposeStmt 7 false) kNSC = none := by
  rw [interp_noteSpendComposeStmt_eq_kStep]
  decide

/-- **NON-VACUITY (fail-closed: double-spend).** A spend of an ALREADY-spent nullifier (here the kernel
already holds `[7]`) with a valid proof does NOT commit — the base non-membership gate fail-closes
inside the composition. The base double-spend teeth SURVIVE the §8 wrapper. -/
theorem noteSpendComposeStmt_rejects_double :
    interp (noteSpendComposeStmt 7 true)
        { kNSC with nullifiers := [7] } = none := by
  rw [interp_noteSpendComposeStmt_eq_kStep]
  decide

/-- The welded composed-noteSpend circuit is the genuine standalone full-state descriptor, NOT the
empty placeholder: its emitted AIR carries the dedicated name `dregg-noteSpendA-v2` (the v2 effect-
commit descriptor), distinct from an inert stub. So `noteSpendCompose_compile_sound` is about a REAL
full-state-binding circuit. -/
theorem noteSpendAEmitted_named :
    Dregg2.Circuit.Inst.NoteSpendA.noteSpendAEmitted.name
      = Dregg2.Circuit.Inst.NoteSpendA.noteSpendAAirName := by
  decide

#assert_axioms noteSpendComposeStmt_inserts
#assert_axioms noteSpendComposeStmt_rejects_no_proof
#assert_axioms noteSpendComposeStmt_rejects_double
#assert_axioms noteSpendAEmitted_named

/-! ## §5 — THE COMPOSED EFFECT'S RUNNABLE EFFECTVM DESCRIPTOR IS FULL-STATE (magnesium breadth).

The composed noteSpend's per-row RUNNABLE circuit is `EffectVmEmitNoteSpend.noteSpendVmDescriptorWide`
(the per-row arithmetic — transparent credit + `nullifiers`-root advance + frame freeze — is IDENTICAL to
the base noteSpend's; the §8 spending-proof gate is a CHAINED/argument-level leg, NOT a per-row column,
exactly the §1↔§2 split this file carries). That wide descriptor is now lifted to the GENERIC full-state-
on-RUNNABLE crown: a satisfying per-row wide witness pins the FULL 17-field post-state, and tamper of ANY
field/root is UNSAT. We re-export it for the composed effect so this module names the RUNNABLE
descriptor's full-state property; the §3 weld (vs the v2 `Surface2` full-state descriptor) and the
RUNNABLE EffectVM descriptor BOTH now bind the whole post-state. The proof gate + freshness remain the
documented chained/turn-level legs (the per-row layer binds the INSERT's committed digest, not the
non-membership). -/

/-- **`noteSpendCompose_runnable_full_sound` — the composed effect's RUNNABLE descriptor is FULL-state.**
Re-export of `EffectVmEmitNoteSpend.noteSpend_runnable_full_sound` for the composed effect (which shares
the per-row wide descriptor): a row satisfying noteSpend's WIDE RUNNABLE descriptor, under the structured
decode, pins the FULL 17-field declarative post-state — the per-cell credit + nonce tick AND the
`nullifiers`-root digest advance AND every other side-table root frozen. The per-row layer of the §1–§3
composition is now at FULL state; the §8 proof gate + freshness non-membership are the named
chained/turn-level legs. -/
theorem noteSpendCompose_runnable_full_sound (hash : List ℤ → ℤ)
    (value : ℤ) (preRoots postRoots : Dregg2.Exec.SystemRoots.SysRoots) (step : ℤ)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (pr : Dregg2.Exec.SystemRoots.SysRoots)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.IsNoteSpendRow env)
    (hdec : Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.NoteSpendDecode hash value preRoots postRoots step
              env pre post pr)
    (hsat : Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash
              Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpendVmDescriptorWide env true true) :
    Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.NoteSpendFullClause hash value preRoots postRoots step
      pre post pr :=
  Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpend_runnable_full_sound
    hash value preRoots postRoots step env pre post pr hrow hdec hsat

#assert_axioms noteSpendCompose_runnable_full_sound

end Dregg2.Circuit.Argus.Effects.NoteSpendCompose
