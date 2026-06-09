/-
# Dregg2.Circuit.Argus.Effects.EmitEvent — the observation-log effect `emitEvent` welded into the
Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell moves) + createEscrow (two-component side-table). `BalanceA.lean`
welded the genuinely DIFFERENT ledger primitive against a FULL-STATE `Surface2` descriptor whose
soundness concludes the WHOLE 17-field post-state. This module welds `emitEvent`, in a disjoint file (it
imports the Argus IR + the audited `emitEventA` v1 instance + its independent spec read-only and owns
only its own declarations).

## The effect — a KERNEL-FROZEN, authority-FREE log append.

`emitEvent` is the most special shape so far: it writes the OBSERVATION log and NOTHING in the kernel.
The verified kernel step is `emitEventStep` (`Exec/Handlers/Lifecycle.lean:76`):

    emitEventStep k a = if a.cell ∈ k.accounts then some k else none

so a committed emit is a PURE DOMAIN RESTRICTOR on the `RecordKernelState`: gate on cell-liveness
(`cell ∈ accounts`) — dregg1 `apply_emit_event`'s ONLY gate, with NO authority check, anyone may post
on a live cell — and return the kernel LITERALLY UNCHANGED (all 17 fields frozen). This is precisely the
`guard` primitive's shape (`interp (.guard φ) k = if φ k then some k else none`, `Stmt.lean:92`): the
IR term needs NO component-write primitive at all (the kernel is frozen), and NONE is missing — the
`guard` constructor captures `emitEventStep` term-for-term. That is the whole structural contrast with
every prior weld: transfer/balanceA MOVE a component (`setCell`/`setBal`); emit MOVES NOTHING in the
kernel, it only ADMITS.

## THE KERNEL-VS-RUNTIME DIVERGENCE (carried explicitly, NOT papered).

There are TWO faithful executor layers here, and they GENUINELY differ — the honest core of this weld:

  * the RAW KERNEL step `emitEventStep : RecordKernelState → Option RecordKernelState` freezes the kernel
    and gates on liveness. This is what the Argus `interp` (a `RecordKernelState` transformer) can see and
    refine, so the §2 cornerstone `interp_emitEventStmt_eq_emitEventStep` is over THIS step.

  * the CHAINED RUNTIME arm `execFullA st (.emitEventA actor cell topic data)`
    (`TurnExecutorFull.lean:3795`) gates on the SAME liveness, but on commit runs `emitStep`, which
    ADDITIONALLY prepends one `emitReceipt actor cell` row to the observation `log` (the kernel half is
    still frozen). The standalone full-state descriptor (`emitEventA_full_sound`) is keyed on THIS chained
    state (kernel + log) and its `EmitEventSpec` pins BOTH the frozen kernel AND the log prepend.

So the Argus `interp`'s `RecordKernelState` meaning is the FROZEN-KERNEL half of the runtime, but it does
NOT see the LOG prepend (the `interp` type has no log component). This is a genuine kernel-vs-runtime
divergence — `interp` refines the kernel projection of the runtime, while the runtime additionally ticks
the observation clock. We carry it as an EXPLICIT hypothesis in the chained lift (§3): the kernel step's
`some k'` becomes the runtime's `some ⟨k', emitReceipt actor cell :: st.log⟩`, the log prepend named in
the conclusion (NOT hidden, NOT absorbed). The `divergence` field of this module's result records it.

## What this module proves (the BalanceA FULL-STATE template, transposed onto the log domain).

  (1) **Cornerstone (the executor-refinement the task names):** `interp_emitEventStmt_eq_emitEventStep`
      — the kernel step `emitEventStep` IS the Argus term, using `guard` (the pure domain restrictor).
      New, standalone, the log-domain analog of `interp_balanceAStmt_eq_recKExecAsset` (but a `guard`
      rather than a `setBal`, because emit freezes the kernel).

  (2) **Chained lift (carrying the runtime log-prepend divergence):** `interp_emitEventStmt_chained` —
      when the §2 cornerstone commits on the kernel (`= some k'`), the runtime `execFullA` commits to
      `⟨k', emitReceipt actor cell :: st.log⟩`. The BalanceA §3 analog, with the log-prepend named.

  (3) **Compile weld against emit's OWN full-state descriptor:** `emitEvent_compile_sound` — route the
      executor side through (2) + the independent `execFullA_emitEvent_iff_spec` (executor ⟺ full
      `EmitEventSpec`), and the circuit side through the audited `emitEventA_full_sound` (circuit ⟹ full
      `EmitEventSpec`). Both name the SAME `EmitEventSpec`, so they PROVABLY agree on the WHOLE 17-field
      kernel (every field frozen) AND the observation log (the receipt prepended) — strictly stronger
      than a per-cell weld, exactly the BalanceA `Surface` surface.

## HONEST SURFACE — full-state, with the kernel-vs-runtime divergence named.

The welded conclusion is the FULL `EmitEventSpec`: all 17 kernel fields frozen + the exact log
post-image. This is the strongest surface (it pins the whole post-state), the BalanceA `Surface2`-grade
weld. The ONLY honest caveat — carried as an explicit hypothesis and conclusion, not papered — is the
kernel-vs-runtime layering: the Argus `interp` refines the kernel-step (frozen kernel); the descriptor +
the conclusion additionally pin the runtime's receipt-row append. There is NO nonce-tick divergence (emit
freezes the cell nonce too — its kernel is literally unchanged), and NO collapsed field (the spec checks
all 17). The payload `topic`/`data` are honestly INERT (the receipt row carries `cell` in both `src`/`dst`
and `0` in `amt`, independent of payload) — exposed as a non-vacuity tooth.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
log-hash injectivity assumptions enter ONLY inside the reused `emitEventA_full_sound` (its CR portal
hypotheses), not in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Exec.Handlers.Lifecycle

namespace Dregg2.Circuit.Argus.Effects.EmitEvent

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (execFullA emitStep)
open Dregg2.Circuit.Argus (RecStmt interp)
-- The independent full-state spec + executor⟺spec corner (the BalanceA-style executor side).
open Dregg2.Circuit.Spec.CellStateLog
  (EmitEventSpec emitGuard emitReceipt execFullA_emitEvent_iff_spec)
-- emit's OWN standalone full-state descriptor + its soundness (the circuit side), and its arg/surface
-- vocabulary. `CommitSurface` + the CR portals + `satisfiedE`/`encodeE` live in `EffectCommit`;
-- `compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` in `StateCommit`.
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE encodeE)
open Dregg2.Circuit.StateCommit
  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
open Dregg2.Circuit.Inst.EmitEventA (EmitEventArgs emitEventE emitEventA_full_sound)
-- The kernel step `emitEventStep` + its `EmitEventArgs` live in the lifecycle handler batch. Its
-- `EmitEventArgs` field-name collides with the `Inst` one, so we name it by its full path at use sites.

/-! ## §1 — The emitEvent effect as an Argus IR term (a PURE GUARD — the kernel is frozen).

`emitEventStep k a = if a.cell ∈ k.accounts then some k else none`. We capture it term-for-term with the
`guard` primitive — the in-band domain restrictor whose `interp` is exactly `if φ k then some k else none`
(`Stmt.lean:92`), returning `k` UNCHANGED on admit. The whole contrast with transfer/balanceA: emit needs
NO move primitive (its kernel is frozen), so the term is a LONE `guard`, no `seq`/`setCell`/`setBal`. The
guard predicate is the single cell-liveness conjunct `cell ∈ accounts` as a `Bool`. -/

/-- The emit-event admissibility gate as a `Bool` — exactly `emitEventStep`'s `if` (the single
cell-liveness conjunct `cell ∈ k.accounts`; authority-FREE — dregg1 `apply_emit_event` runs no cap
check). Stated over the `Finset CellId` membership the kernel uses. -/
def emitEventGuardB (cell : CellId) (k : RecordKernelState) : Bool :=
  decide (cell ∈ k.accounts)

/-- **The emitEvent effect as an IR term: a LONE guard (the kernel is frozen).** Unlike
transfer/balanceA (gate THEN move), emit has NO move — the kernel is literally unchanged, so the body is
just the `guard` domain restrictor on cell-liveness. The `guard` primitive returns `k` UNCHANGED on
admit, EXACTLY the post-kernel `emitEventStep` produces. -/
def emitEventStmt (cell : CellId) : RecStmt :=
  RecStmt.guard (emitEventGuardB cell)

/-! ## §2 — The cornerstone: `interp` of the emitEvent term IS the kernel step `emitEventStep`. -/

/-- The emit-event `Bool` gate decodes to `emitEventStep`'s admissibility proposition (the single
cell-liveness conjunct). The log-domain analog of `transferGuard_iff` / `balanceAGuard_iff`. -/
theorem emitEventGuardB_iff (cell : CellId) (k : RecordKernelState) :
    emitEventGuardB cell k = true ↔ cell ∈ k.accounts := by
  simp only [emitEventGuardB, decide_eq_true_eq]

/-- **The cornerstone (observation log).** `interp` of the emitEvent term IS the verified kernel step
`emitEventStep` — the same partial function, by construction, exactly as the transfer/balanceA
cornerstones, now over a KERNEL-FROZEN domain-restrictor via `guard` (NOT a move primitive). The emit's
executor-refinement: the executor IS the meaning of the term (here, a pure admit-and-freeze). -/
theorem interp_emitEventStmt_eq_emitEventStep (actor cell : CellId) (topic data : Int)
    (k : RecordKernelState) :
    interp (emitEventStmt cell) k
      = Dregg2.Exec.Handlers.Lifecycle.emitEventStep k
          { actor := actor, cell := cell, topic := topic, data := data } := by
  simp only [emitEventStmt, interp]
  unfold Dregg2.Exec.Handlers.Lifecycle.emitEventStep
  by_cases hg : emitEventGuardB cell k = true
  · -- ADMIT: the guard fires (`some k` unchanged — emit freezes the kernel); the RHS `if` opens on the
    -- decoded liveness Prop, giving the SAME `some k`.
    rw [if_pos hg, if_pos ((emitEventGuardB_iff cell k).mp hg)]
  · -- REJECT: the guard fails ⇒ `none`; the RHS `if` closes on the (negated) decoded liveness Prop.
    rw [if_neg hg, if_neg (fun hp => hg ((emitEventGuardB_iff cell k).mpr hp))]

#assert_axioms interp_emitEventStmt_eq_emitEventStep

/-! ## §3 — Lifting the cornerstone to the CHAINED RUNTIME `execFullA` (carrying the log-prepend
divergence EXPLICITLY).

The standalone descriptor (§4) is keyed on the CHAINED runtime `execFullA st (.emitEventA …)` over
`RecChainedState` (kernel + observation log). The §2 cornerstone is over the RAW kernel step
`emitEventStep`, which freezes the kernel but — being a `RecordKernelState → Option RecordKernelState` —
has NO log component. The runtime arm gates on the SAME liveness, but on commit runs `emitStep`, which
ADDITIONALLY prepends `emitReceipt actor cell` to the log.

This is the kernel-vs-runtime DIVERGENCE, and we carry it FAITHFULLY: the kernel step's `some k'` lifts to
the runtime's `some ⟨k', emitReceipt actor cell :: st.log⟩` — the log prepend NAMED in the conclusion, not
hidden. (Because emit's kernel step freezes the kernel, the lifted `k'` IS `st.kernel`; we state it via the
generic cornerstone `some k'` so the §2 refinement is what drives the lift, keeping the layering honest.) -/

/-- **`interp_emitEventStmt_chained` — the IR term's kernel meaning, lifted to the chained runtime
`execFullA`, with the LOG-PREPEND divergence named.** When the §2 cornerstone commits on the kernel
(`interp (emitEventStmt cell) st.kernel = some k'`), the unified runtime `execFullA st (.emitEventA actor
cell topic data)` commits to the chained state `⟨k', emitReceipt actor cell :: st.log⟩`. So the Argus
term's kernel meaning lifts to the chained runtime the standalone descriptor speaks about — and the
runtime's EXTRA receipt-row append (the kernel step does NOT see the log) is carried EXPLICITLY in the
conclusion, the honest kernel-vs-runtime divergence. -/
theorem interp_emitEventStmt_chained
    (st : RecChainedState) (actor cell : CellId) (topic data : Int) (k' : RecordKernelState)
    (hexec : interp (emitEventStmt cell) st.kernel = some k') :
    execFullA st (.emitEventA actor cell topic data)
      = some { kernel := k', log := emitReceipt actor cell :: st.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `emitEventStep`, which on the liveness
  -- guard is `some st.kernel`; reading `hexec` extracts both the liveness fact and `k' = st.kernel`.
  rw [interp_emitEventStmt_eq_emitEventStep actor cell topic data] at hexec
  unfold Dregg2.Exec.Handlers.Lifecycle.emitEventStep at hexec
  by_cases hg : cell ∈ st.kernel.accounts
  · -- ADMIT: the kernel step is `some st.kernel`, so `hexec : some st.kernel = some k'`, giving
    -- `k' = st.kernel`. The runtime arm `execFullA … (.emitEventA …)` opens on the SAME liveness to
    -- `some (emitStep …)`, whose kernel is `st.kernel` and whose log is the receipt prepend.
    rw [if_pos hg] at hexec
    simp only [Option.some.injEq] at hexec
    subst hexec
    show (if cell ∈ st.kernel.accounts then some (emitStep st actor cell topic data) else none)
        = some { kernel := st.kernel, log := emitReceipt actor cell :: st.log }
    rw [if_pos hg]
    simp only [emitStep, emitReceipt]
  · -- REJECT is impossible: `hexec` would be `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_emitEventStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of emit's OWN full-state circuit agrees with the FULL
post-state the IR term's executor interpretation produces (kernel frozen + log prepended).

This welds against emit's GENUINE standalone descriptor `emitEventCircuitStep CS emitEventE` (the v1
`CommitSurface` full-state circuit whose soundness is `emitEventA_full_sound`), exactly the BalanceA
surface (a `*_full_sound` concluding the WHOLE post-state). The executor side is routed through §3
(`interp` ⟹ `execFullA`, log-prepend carried) and the independent `execFullA_emitEvent_iff_spec`
(executor ⟺ full `EmitEventSpec`); the circuit side is the audited `emitEventA_full_sound` (circuit ⟹
full `EmitEventSpec`). Both name the SAME `EmitEventSpec`, so they PROVABLY agree on the WHOLE 17-field
kernel (every field frozen) AND the observation log. -/

/-- The Argus circuit interpretation of an `emitEvent` term: emit's OWN audited standalone v1
`CommitSurface` circuit step — the full-state arithmetization `satisfiedE CS emitEventE (encodeE …)`
satisfied on the encoded `(st, args, st')` triple. Its soundness `emitEventA_full_sound` pins the
complete `EmitEventSpec` (all 17 kernel fields frozen + the receipt log). The `emitEvent`-keyed analog of
`balanceACircuit`, in the descriptor universe where emit carries its OWN genuine full-state circuit. -/
def emitEventCircuit (CS : CommitSurface) (s : RecChainedState) (args : EmitEventArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS emitEventE (encodeE CS emitEventE s args s')

/-- **`emitEventSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`EmitEventSpec st actor cell topic data ·` are equal. Rather than re-derive this field-by-field, we route
through the PROVEN executor⟺spec corner `execFullA_emitEvent_iff_spec`: each `EmitEventSpec` reconstructs
the SAME committed value `execFullA st (.emitEventA …) = some ·`, and `some` is injective. This is exactly
the sense in which `EmitEventSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state (the BalanceA `balanceMovementSpec_unique`
analog). -/
theorem emitEventSpec_unique {st st₁ st₂ : RecChainedState} {actor cell : CellId} {topic data : Int}
    (h₁ : EmitEventSpec st actor cell topic data st₁)
    (h₂ : EmitEventSpec st actor cell topic data st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.emitEventA actor cell topic data) = some st₁ :=
    (execFullA_emitEvent_iff_spec st actor cell topic data st₁).mpr h₁
  have e₂ : execFullA st (.emitEventA actor cell topic data) = some st₂ :=
    (execFullA_emitEvent_iff_spec st actor cell topic data st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`emitEvent_compile_sound` — the welded soundness (emit slice), against emit's OWN full-state
descriptor.**

Suppose, for the Argus emitEvent term `emitEventStmt cell` (with the runtime args `actor`/`topic`/`data`):
  * the standalone emit circuit `emitEventCircuit CS ⟨…⟩ st st'` (= `emitEventE`'s full-state v1
    arithmetization satisfied on the encoded triple) holds, under the realizable Poseidon-CR portals
    (`hN`/`hL`/`hRest`/`hLog`) + `AccountsWF` on both states (`hwf`/`hwf'`, the descriptor's well-formed
    accounts hypotheses);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (emitEventStmt cell) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces, with the runtime log-prepend named: `st' = { kernel := k', log := emitReceipt actor cell ::
st.log }`. I.e. emit's OWN circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (every
field frozen) AND the observation log (the receipt prepended) — the full `EmitEventSpec`, not a per-cell
projection. So the circuit the prover runs for emit pins the complete state the IR term's executor
produces (the kernel-frozen half it refines, plus the runtime's receipt tick it lifts to). -/
theorem emitEvent_compile_sound
    (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (st st' : RecChainedState) (actor cell : CellId) (topic data : Int) (k' : RecordKernelState)
    (hwf : AccountsWF st.kernel) (hwf' : AccountsWF st'.kernel)
    (hcirc : emitEventCircuit CS st ⟨actor, cell, topic, data⟩ st')
    (hexec : interp (emitEventStmt cell) st.kernel = some k') :
    st' = { kernel := k', log := emitReceipt actor cell :: st.log } := by
  -- circuit side: emit's OWN audited soundness forces the FULL `EmitEventSpec` on `(st, args, st')`.
  have hspec : EmitEventSpec st actor cell topic data st' :=
    emitEventA_full_sound CS hN hL hRest hLog st ⟨actor, cell, topic, data⟩ st' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.emitEventA …) = some ⟨k', receipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `EmitEventSpec st … ⟨k', receipt :: log⟩`.
  have hspec' : EmitEventSpec st actor cell topic data
      { kernel := k', log := emitReceipt actor cell :: st.log } :=
    (execFullA_emitEvent_iff_spec st actor cell topic data _).mp
      (interp_emitEventStmt_chained st actor cell topic data k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact emitEventSpec_unique hspec hspec'

#assert_axioms emitEvent_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely COMMITS on a live cell, FREEZES the kernel, and the guard
REJECTS a dead cell (fail-closed); the runtime ticks the log; the payload is honestly INERT.

The cornerstone/weld would be hollow if emit never committed, if the guard admitted everything, or if the
"frozen kernel" claim were vacuous. A concrete two-cell kernel `kE` (cells 0,1 live) exercises a real
admit; the rejection lemma shows the liveness guard fails closed; the runtime witnesses show the log ticks
by exactly one receipt and the payload does NOT ride it. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts, cell 7 is NOT. -/
def kE : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => [] }

/-- A concrete chained pre-state over `kE` (empty observation log), for the runtime witnesses. -/
def stE : RecChainedState := { kernel := kE, log := [] }

-- The emit term is a GENUINE two-valued domain restrictor on the kernel:
--   ADMITS a live cell (1 ∈ {0,1}) returning the kernel UNCHANGED; REJECTS a dead cell (7 ∉ {0,1}).
#guard (interp (emitEventStmt 1) kE).isSome    -- admit (live cell)
#guard (interp (emitEventStmt 7) kE).isNone    -- reject (dead cell)
-- the runtime arm ticks the observation log by exactly one row on a live-cell emit (payload 9, 42):
#guard ((execFullA stE (.emitEventA 5 1 9 42)).map (fun s => s.log.length)) == some 1
#guard (stE.log.length == 0)                    -- before: empty log

/-- **NON-VACUITY (commits + FREEZES the kernel, observably).** Emitting on the LIVE cell `1` commits and
returns the kernel LITERALLY UNCHANGED — the term genuinely admits, and the "frozen kernel" claim is real
(the post-kernel IS `kE`, not a no-op vacuity). The log-domain analog of `balanceAStmt_debits`, but here
the observable is that the kernel is PRESERVED (emit is a pure domain restrictor). -/
theorem emitEventStmt_admits_frozen :
    interp (emitEventStmt 1) kE = some kE := by
  -- the cornerstone turns the term into `emitEventStep kE …`; unfold and discharge the liveness `if`
  -- on the DECIDABLE membership `1 ∈ ({0,1} : Finset CellId)` (the record itself is NOT decidable-eq,
  -- so we route through `if_pos`, not `decide` on `= some kE`).
  rw [interp_emitEventStmt_eq_emitEventStep 0 1 0 0]
  unfold Dregg2.Exec.Handlers.Lifecycle.emitEventStep
  rw [if_pos (show (1 : CellId) ∈ kE.accounts by decide)]

/-- **NON-VACUITY (fail-closed: dead cell).** An emit whose target `cell` is NOT a live account (here
cell `7 ∉ {0,1}`) does NOT commit — the term returns `none` (the cell-liveness leg of the guard fails).
The one gate emit carries is genuinely a gate. -/
theorem emitEventStmt_rejects_dead :
    interp (emitEventStmt 7) kE = none := by
  -- the cornerstone turns the term into `emitEventStep kE …`; the liveness `if` closes on the DECIDABLE
  -- non-membership `7 ∉ ({0,1} : Finset CellId)`, giving `none`.
  rw [interp_emitEventStmt_eq_emitEventStep 0 7 0 0]
  unfold Dregg2.Exec.Handlers.Lifecycle.emitEventStep
  rw [if_neg (show (7 : CellId) ∉ kE.accounts by decide)]

/-- **NON-VACUITY (the runtime ticks the observation clock by exactly one row).** A committed runtime emit
on the live cell `1` prepends EXACTLY the `emitReceipt 5 1` row onto the (empty) log — the kernel-vs-runtime
divergence is OBSERVABLE: the kernel step freezes, but the runtime advances the log by one. Confirms §3's
log-prepend conclusion is a real append, not a no-op. -/
theorem emitEventStmt_runtime_log_ticks :
    (execFullA stE (.emitEventA 5 1 9 42)).map (fun s => s.log) = some [emitReceipt 5 1] := by
  have hk : interp (emitEventStmt 1) stE.kernel = some kE := by
    show interp (emitEventStmt 1) kE = some kE
    exact emitEventStmt_admits_frozen
  rw [interp_emitEventStmt_chained stE 5 1 9 42 kE hk]
  rfl

/-- **NON-VACUITY (the payload is honestly INERT).** Two runtime emits on the live cell `1` that DIFFER
only in `topic`/`data` (`(9,42)` vs `(0,0)`) produce the SAME observation log — the receipt row carries
`cell` in both `src`/`dst` and `0` in `amt`, INDEPENDENT of the event payload. This pins the honest
boundary stated in the header: `topic`/`data` ride the args for guard/bookkeeping but do NOT affect the
post-state (the spec's log clause is payload-independent). -/
theorem emitEventStmt_payload_inert :
    (execFullA stE (.emitEventA 5 1 9 42)).map (fun s => s.log)
      = (execFullA stE (.emitEventA 5 1 0 0)).map (fun s => s.log) := by
  have hk : interp (emitEventStmt 1) stE.kernel = some kE := emitEventStmt_admits_frozen
  rw [interp_emitEventStmt_chained stE 5 1 9 42 kE hk,
      interp_emitEventStmt_chained stE 5 1 0 0 kE hk]

#assert_axioms emitEventStmt_admits_frozen
#assert_axioms emitEventStmt_rejects_dead
#assert_axioms emitEventStmt_runtime_log_ticks
#assert_axioms emitEventStmt_payload_inert

end Dregg2.Circuit.Argus.Effects.EmitEvent
