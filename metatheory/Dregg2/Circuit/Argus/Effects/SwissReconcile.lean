/-
# Dregg2.Circuit.Argus.Effects.SwissReconcile — the CapTP sturdy-ref 3-vat HANDOFF cert-RECONCILE
  effect `swissHandoffA` welded into the Argus IR, as a FULL-STATE `Surface2` weld, in its OWN disjoint
  module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn/createEscrow. `Effects/SwissExport.lean` welded the swiss-table MINT (`exportSturdyRefA`,
the `setSwiss` LIST-prepend) and `Effects/SwissDrop.lean` welded the swiss-table GC (`swissDropA`, the
conditional `setSwiss` remove/decrement) — both against their genuine standalone v2 `Surface2` descriptors
(the FULL 17-field `*_full_sound` surface). This module welds the THIRD genuinely-different swiss-table arm:
the 3-vat introduce-cert RECONCILE `swissHandoffA`, the operation that RECONCILES a presented handoff cert
against the committed swiss entry — binding `cert := some certHash` and bumping the entry's `refcount` (the
recipient's new live reference) — against swissHandoff's OWN audited v2 `Surface2` descriptor
(`Inst/swissHandoffA.lean`'s `swissHandoffA_full_sound`), the strongest surface this effect supports.

`swissHandoffA sw certHash introducer exporter` RECONCILES the cert: the verified RAW kernel step is
`swissHandoffK` (`RecordKernel.lean:2733`):

    swissHandoffK k sw certHash
      = match findSwiss k.swiss sw with
        | none   => none
        | some e => some { k with swiss := replaceSwiss k.swiss sw
                                    { e with cert := some certHash, refcount := e.refcount + 1 } }

so a committed reconcile is FAIL-CLOSED if the swiss number is ABSENT (a cert cannot be reconciled against a
sturdy ref that does not exist), and otherwise rewrites EXACTLY the `swiss` list side-table (the declarative
cert-bind/refcount-bump image `Spec.SwissHandoff.handoffSwissPost k.swiss sw e certHash`), freezing every
other RecordKernelState field — it is balance-NEUTRAL (`swissHandoffK_balNeutral`). Because the body touches
the `swiss` list side-table, the IR move is the §A `setSwiss` component-write primitive — NOT `setCell`
(transfer's), `setBal` (balanceA's), nor `setLifecycle` (cellSeal's). That is the structural contrast.

UNLIKE `swissDropK` (whose GC domain ALSO requires `0 < e.refcount`, the positive-refcount leg), the
reconcile kernel gate is PURE MEMBERSHIP — a found entry is ALWAYS reconcilable (the cert-bind/bump is
unconditional once the ref exists). So the IR term is the SIMPLEST of the swiss family: a `seq (guard
<found>) (setSwiss <handoffSwissPost of the found entry>)`. The guard captures the fail-closed MEMBERSHIP
domain (entry present), and the `setSwiss` leaf reads the found entry and installs the declarative
cert-bind/bump image — matching `swissHandoffK` on the nose via the audited `handoffSwissUpdate`/
`handoffSwissPost` bridge lemmas (`Spec/swisshandoff.lean`).

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; the verified chained
step `swissHandoffChainA` (`TurnExecutorFull.lean:2823`) is a `RecChainedState → Option RecChainedState`
step — it ALSO (i) PRE-GATES on `stateAuthB s.kernel.caps introducer exporter` (the INTRODUCER's authority
over the exporting cell — the auth leg `swissHandoffK` itself does NOT check; it lives in the chained
wrapper) and (ii) PREPENDS one self-targeted receipt row `handoffReceipt introducer exporter :: s.log`, and
the `log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's `interp` cannot — and
does not — emit the auth gate or the log row; it captures EXACTLY the KERNEL side of the chained step (the
`swissHandoffK` cert-bind/bump). This is the SAME chained-vs-raw boundary `SwissExport`/`SwissDrop` carry
(their `interp` is on the raw kernel; the chained `execFullA` adds a `stateAuthB` pre-gate + a log prepend),
here named precisely:

  * `interp (swissReconcileStmt sw certHash introducer exporter) k` produces the KERNEL post-state — exactly
    `swissHandoffK k sw certHash` (`interp_swissReconcileStmt_eq_swissHandoffK`), the cert-bind/refcount-bump
    on the `swiss` side-table, fail-closed on the membership domain. It does NOT see `introducer`/`exporter`
    (those are the auth leg of the chained wrapper); they are carried as IR parameters only so the term names
    the same effect.
  * lifting to the chained `execFullA` (`interp_swissReconcileStmt_chained`) re-attaches BOTH the runtime
    `stateAuthB` auth gate (carried as an explicit hypothesis `hauth`) and the receipt row
    `handoffReceipt introducer exporter :: s.log` — the runtime layer the kernel `interp` does not model. The
    welded conclusion (§4) then names the chained post-state `{ kernel := k', log := receipt :: s.log }`
    EXPLICITLY, so the auth side-condition + receipt-log obligation are part of the welded statement (not
    papered).

## THE DESCRIPTOR — a GENUINE full-state v2 `Surface2`, NOT EffectVM-inherited.

`swissHandoffA` carries its OWN standalone v2 `EffectCommit2`/`Surface2` descriptor + full soundness
(`Dregg2/Circuit/Inst/swissHandoffA.lean`): `swissHandoffE` (the `EffectSpec2` whose touched component is the
WHOLE `swiss : List SwissRecord` side-table, a `listComponent` full-list digest — so a drop/reorder of an
EXISTING sturdy ref, or a reconcile that does NOT bind the cert, is REJECTED, not just "the count grew") and
`swissHandoffA_full_sound : satisfiedE2 … (swissHandoffE …) … ⟹ HandoffSpec` — a FULL declarative post-state
soundness keyed on the CHAINED executor `swissHandoffChainA`/`execFullA` via the INDEPENDENT
`execFullA_handoff_iff_spec` (executor ⟺ `HandoffSpec`, BOTH directions). `HandoffSpec` pins the touched
`swiss` side-table, the receipt-log growth, AND the 16-field frame (its strengthened twin `HandoffSpecFull`,
`Spec/swisshandoff.lean`, spells out the frame as 16 checkable conjuncts and proves `HandoffSpec ≡
HandoffSpecFull`, with an anti-ghost `delegate`-tamper tooth). This is the strictly-stronger
`SwissExport`/`SwissDrop` surface (whole-state full-list digest), not the per-cell EffectVM `sturdyref_root`
surface — that runtime `field[4]` move is universe-A's `swiss`-digest projection (`EffectVmEmitSwissHandoff`)
but does NOT carry the full 17-field declarative post-state, so the standalone v2 descriptor is the honest
strongest weld here.

This module is therefore HONEST in both directions:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_swissReconcileStmt_eq_swissHandoffK` —
      the RAW-kernel step `swissHandoffK` IS the Argus term, using `guard` (MEMBERSHIP) then `setSwiss` (the
      cert-bind/bump on the list side-table). New, standalone, the swiss-reconcile analog of
      `interp_swissDropStmt_eq_swissDropK` (the cleaner gate: pure membership, no refcount leg).

  (2) **Compile weld against swissHandoff's OWN standalone v2 `Surface2` descriptor:** lift the cornerstone
      to the chained executor (`interp_swissReconcileStmt_chained`, carrying the `stateAuthB` AUTHORITY
      side-condition + the receipt-log row), then weld to the standalone `swissReconcileCircuit`/
      `swissHandoffA_full_sound`. The conclusion is the FULL `HandoffSpec` agreement (all 17 kernel fields +
      the receipt log + the 2-conjunct guard) — a satisfying witness of swissHandoff's own circuit agrees
      with the WHOLE post-state the IR term's executor produces. Strictly stronger than a per-cell weld.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the whole-list digest
assumptions enter ONLY inside the reused `swissHandoffA_full_sound` (its `compressNInjective` /
`listLeafInjective` digest-injectivity hypotheses + the Poseidon-CR `RestIffNoSwiss` / `logHashInjective`
portals), not in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. The
chained-vs-raw AUTHORITY gap + the receipt-log row are carried as EXPLICIT obligations (`hauth` + the
conclusion's `log`), not papered. Imports are read-only; this file OWNS only its own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.swissHandoffA
import Dregg2.Circuit.Spec.swisshandoff

namespace Dregg2.Circuit.Argus.Effects.SwissReconcile

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
-- `stateAuthB` (the introducer's authority gate, the chained wrapper's auth leg) lives in
-- `Dregg2.Exec.EffectsState`. (`open` is not transitive, so it is named even though the Inst/Spec deps
-- use it.)
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/swissHandoffA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective` AND `compressNInjective` live in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2`
-- in `EffectCommit2`; `listLeafInjective` in `ListCommit`.
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.Spec.SwissHandoff
  (HandoffGuard HandoffSpec handoffReceipt handoffRecord handoffSwissPost handoffSwissUpdate
   handoffSwissUpdate_some handoffSwissUpdate_eq_k execFullA_handoff_iff_spec)
open Dregg2.Circuit.Inst.SwissHandoffA (HandoffArgs swissHandoffE swissHandoffA_full_sound RestIffNoSwiss)
open Dregg2.Authority (Auth)

/-! ## §1 — The swissReconcile effect as an Argus IR term (gate, then the `setSwiss` cert-bind/bump move).

`swissHandoffK`'s shape is `match findSwiss k.swiss sw with | none => none | some e => some { k with swiss :=
replaceSwiss k.swiss sw { e with cert := some certHash, refcount := e.refcount + 1 } }`. We capture its
KERNEL side term-for-term: a `Bool` `reconcileKGuard` of EXACTLY the fail-closed MEMBERSHIP domain (the swiss
entry `sw` is PRESENT), then a `setSwiss` whose leaf reads the found entry and installs the declarative
cert-bind/bump image `handoffSwissPost k.swiss sw e certHash`. The contrast with transfer/balanceA/cellSeal
is the move primitive: `setSwiss` (rewrites the `swiss` list side-table) over the cert-bind/refcount-bump,
NOT `setCell` / `setBal` / `setLifecycle`. The contrast with `swissDrop` is the GATE: pure MEMBERSHIP (no
refcount-positivity leg — a found entry is always reconcilable). -/

/-- The swissReconcile KERNEL admissibility gate as a `Bool` — exactly `swissHandoffK`'s fail-closed
MEMBERSHIP domain: the swiss entry `sw` is PRESENT (`findSwiss k.swiss sw` is `some _`). When the entry is
absent, the gate is `false` and the term rejects (`none`), matching `swissHandoffK` exactly. UNLIKE the GC
gate `dropKGuard`, there is NO refcount-positivity leg — a sturdy ref that EXISTS is always cert-reconcilable
(`swissHandoffK` binds+bumps unconditionally on a found entry). The AUTH leg (`stateAuthB`) is NOT here — it
is the chained wrapper's gate, re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
def reconcileKGuard (sw : Nat) (k : RecordKernelState) : Bool :=
  (findSwiss k.swiss sw).isSome

/-- The swissReconcile `setSwiss` leaf — the post-`swiss` list `swissHandoffK` installs on a committed
reconcile. On a present entry it is the declarative cert-bind/bump image `handoffSwissPost k.swiss sw e
certHash` (`replaceSwiss` with the cert bound + refcount bumped); off the membership domain (absent entry) it
is the identity (`k.swiss`), which never fires because the guard rejects there. The genuine `setSwiss`
payload — NOT a no-op. -/
def reconcileSwissLeaf (sw certHash : Nat) (k : RecordKernelState) : List SwissRecord :=
  match findSwiss k.swiss sw with
  | some e => handoffSwissPost k.swiss sw e certHash
  | none   => k.swiss

/-- **The swissReconcile effect as an IR term: gate, then the `setSwiss` cert-bind/bump.** Mirrors
`swissDropStmt` (gate, then a `setSwiss` move) but the gate is pure MEMBERSHIP (no refcount leg) and the move
is the cert-bind/refcount-bump of the found entry — NOT the conditional remove/decrement. The `setSwiss` leaf
is `reconcileSwissLeaf sw certHash k`, EXACTLY the post-`swiss` `swissHandoffK` installs on the kernel (the
runtime `stateAuthB` auth gate + receipt-log row are re-attached in §3). `introducer`/`exporter` are carried
as IR parameters only (the chained wrapper's auth leg names them); the KERNEL step `swissHandoffK` does not
read them. -/
def swissReconcileStmt (sw certHash : Nat) (_introducer _exporter : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (reconcileKGuard sw))
    (RecStmt.setSwiss (fun k => reconcileSwissLeaf sw certHash k))

/-! ## §2 — The cornerstone: `interp` of the swissReconcile term IS the raw kernel step `swissHandoffK`. -/

/-- The swissReconcile `Bool` gate decodes to `swissHandoffK`'s fail-closed MEMBERSHIP domain (entry
present). The analog of `dropKGuard_iff`, but pure membership (no refcount conjunct). -/
theorem reconcileKGuard_iff (sw : Nat) (k : RecordKernelState) :
    reconcileKGuard sw k = true ↔ (∃ e : SwissRecord, findSwiss k.swiss sw = some e) := by
  unfold reconcileKGuard
  cases hf : findSwiss k.swiss sw with
  | none   => simp
  | some e => simp

/-- **The cornerstone (raw-kernel cert-bind/bump).** `interp` of the swissReconcile term IS the verified RAW
kernel step `swissHandoffK` — the same partial function, by construction, exactly as the
transfer/swissExport/swissDrop cornerstones, now over the `swiss` list side-table via
`setSwiss`/`handoffSwissPost` (NOT the record-cell `setCell`/`setBal` nor the `setLifecycle` of cellSeal). On
the membership domain the term commits to `{ k with swiss := handoffSwissPost k.swiss sw e certHash }` —
exactly the cert-bind/bump `swissHandoffK` installs — and rejects (`none`) on exactly the same fail-closed
gate (entry absent). This is the per-effect executor-refinement for the CapTP 3-vat handoff family. The
runtime auth gate + receipt-log prepend are re-attached in §3 (the kernel-vs-runtime divergence this file
carries).

The `swissHandoffK` body is a `match findSwiss … | none => none | some e => some { k with swiss := … }`; the
IR term's `guard` decodes (via `reconcileKGuard_iff`) to `∃ e, findSwiss … = some e`, so the two coincide: on
an absent swiss number the guard is FALSE ⇒ both are `none`; on a found entry the `setSwiss` leaf reduces to
`handoffSwissPost k.swiss sw e certHash`, and `handoffSwissPost = replaceSwiss … (handoffRecord e certHash)`
is DEFINITIONALLY the kernel's `replaceSwiss … { e with cert := some certHash, refcount := e.refcount + 1 }`
(`handoffRecord` IS that record-update). -/
theorem interp_swissReconcileStmt_eq_swissHandoffK (sw certHash : Nat) (introducer exporter : CellId)
    (k : RecordKernelState) :
    interp (swissReconcileStmt sw certHash introducer exporter) k = swissHandoffK k sw certHash := by
  simp only [swissReconcileStmt, interp]
  by_cases hg : reconcileKGuard sw k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setSwiss` move installs `reconcileSwissLeaf sw
    -- certHash k`, which on the found entry is `handoffSwissPost k.swiss sw e certHash`. That is
    -- DEFINITIONALLY the kernel's post-`swiss` (`handoffRecord` = the `{ e with cert, refcount+1 }` update,
    -- `handoffSwissPost` = `replaceSwiss … (handoffRecord …)`).
    obtain ⟨e, hf⟩ := (reconcileKGuard_iff sw k).mp hg
    rw [if_pos hg]
    simp only [Option.bind]
    -- the leaf reduces to `handoffSwissPost k.swiss sw e certHash` on the found entry.
    have hleaf : reconcileSwissLeaf sw certHash k = handoffSwissPost k.swiss sw e certHash := by
      simp only [reconcileSwissLeaf, hf]
    rw [hleaf]
    -- `swissHandoffK k sw certHash = some { k with swiss := handoffSwissPost k.swiss sw e certHash }`.
    symm
    unfold swissHandoffK
    rw [hf]
    -- both sides are `some { k with swiss := replaceSwiss … (handoffRecord e certHash) }`; `handoffRecord`
    -- and `handoffSwissPost` unfold to the kernel's literal record-update / `replaceSwiss`.
    simp only [handoffSwissPost, handoffRecord]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; and `swissHandoffK k sw certHash = none` on the SAME
    -- domain (entry absent), since the guard decoded EXACTLY membership.
    rw [if_neg hg]
    simp only [Option.bind]
    symm
    unfold swissHandoffK
    cases hf : findSwiss k.swiss sw with
    | none   => rfl
    | some e =>
      -- found entry ⇒ the guard would have admitted; contradiction with `hg`.
      exact absurd ((reconcileKGuard_iff sw k).mpr ⟨e, hf⟩) hg

#assert_axioms interp_swissReconcileStmt_eq_swissHandoffK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `swissHandoffChainA` / `execFullA`.

The standalone swissHandoff descriptor (§4) is keyed on the CHAINED executor `swissHandoffChainA` /
`execFullA` over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.swissHandoffA sw certHash
introducer exporter) = swissHandoffChainA s sw certHash introducer exporter`. The §2 cornerstone is over the
RAW kernel step `swissHandoffK`. The chained layer is exactly the §2 kernel cert-bind/bump PLUS two things: a
`stateAuthB` auth pre-gate (the introducer's authority over the exporting cell, which `swissHandoffK` does
NOT check) and the runtime receipt-log prepend `handoffReceipt introducer exporter :: s.log`. We bridge
faithfully, carrying the `stateAuthB` auth conjunct as an explicit hypothesis and naming the receipt-row
prepend EXPLICITLY in the chained post-state (the honest kernel-vs-runtime divergence — NOT papered). -/

/-- **`interp_swissReconcileStmt_chained` — the IR term's RAW kernel executor, lifted to the chained
`execFullA`.** When the introducer has authority over the exporting cell (`hauth :
stateAuthB s.kernel.caps introducer exporter = true`, the chained layer's extra auth gate) and the §2
cornerstone commits on the kernel (`interp (swissReconcileStmt sw certHash introducer exporter) s.kernel =
some k'`), the unified action executor `execFullA s (.swissHandoffA sw certHash introducer exporter)` commits
to the chained state `⟨k', handoffReceipt introducer exporter :: s.log⟩`. So the Argus term's KERNEL meaning
lifts to the chained executor the standalone descriptor speaks about, with the runtime auth side-condition
carried + the runtime receipt-log row (which the kernel `interp` does not model) re-attached HERE — the
explicit kernel-vs-runtime bridge. -/
theorem interp_swissReconcileStmt_chained
    (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId) (k' : RecordKernelState)
    (hauth : stateAuthB s.kernel.caps introducer exporter = true)
    (hexec : interp (swissReconcileStmt sw certHash introducer exporter) s.kernel = some k') :
    execFullA s (.swissHandoffA sw certHash introducer exporter)
      = some { kernel := k', log := handoffReceipt introducer exporter :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `swissHandoffK`.
  rw [interp_swissReconcileStmt_eq_swissHandoffK] at hexec
  -- `execFullA s (.swissHandoffA …)` reduces to `swissHandoffChainA s sw certHash introducer exporter`, which
  -- on `stateAuthB` opens to a `match swissHandoffK …` — and `hexec` names that as `some k'`.
  show swissHandoffChainA s sw certHash introducer exporter
    = some { kernel := k', log := handoffReceipt introducer exporter :: s.log }
  unfold swissHandoffChainA handoffReceipt
  rw [if_pos hauth, hexec]

#assert_axioms interp_swissReconcileStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of swissHandoff's OWN standalone full-state circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against swissHandoff's GENUINE standalone descriptor `swissReconcileCircuit S (swissHandoffE …)`
(the v2 `Surface2` circuit whose soundness is `swissHandoffA_full_sound`), NOT an EffectVM `sturdyref_root`
row — see the descriptor note in this file's header. The executor side is routed through §3 (`interp` ⟹
`execFullA`) and the independent `execFullA_handoff_iff_spec` (executor ⟺ `HandoffSpec`); the circuit side is
the audited `swissHandoffA_full_sound` (circuit ⟹ `HandoffSpec`). Both name the SAME `HandoffSpec`, so they
PROVABLY agree on the WHOLE post-state — the touched `swiss` side-table (cert-bind/bump image), the
receipt-log growth, and the 16-field frame — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `swissReconcile` term: swissHandoff's OWN audited standalone v2
`Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (swissHandoffE …) (encodeE2 …)`
satisfied on the encoded `(s, ⟨sw,certHash,introducer,exporter⟩, s')` triple (the `EffectRefinement` hub's
`effect2CircuitStep`, inlined here so this module imports only `Inst.swissHandoffA`). Its soundness
`swissHandoffA_full_sound` pins the complete `HandoffSpec`. The `swissReconcile`-keyed analog of
`swissDropCircuit`, in the descriptor universe where swissHandoff carries its OWN genuine full-state circuit
(NOT EffectVM-inherited). The whole-list digest closure `LE`/`cN` + their injectivity witnesses are passed
through verbatim (the realizable Poseidon carriers). -/
def swissReconcileCircuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2 S (swissHandoffE LE cN hN hLE) (encodeE2 S (swissHandoffE LE cN hN hLE) s args s')

/-- **`handoffSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`HandoffSpec s sw certHash introducer exporter ·` are equal. Rather than re-derive this field-by-field, we
route through the PROVEN executor⟺spec corner `execFullA_handoff_iff_spec`: each `HandoffSpec` reconstructs
the SAME committed value `execFullA s (.swissHandoffA sw certHash introducer exporter) = some ·`, and `some`
is injective. This is exactly the sense in which `HandoffSpec` is functional — it determines the post-state —
so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem handoffSpec_unique {s s₁ s₂ : RecChainedState} {sw certHash : Nat} {introducer exporter : CellId}
    (h₁ : HandoffSpec s sw certHash introducer exporter s₁)
    (h₂ : HandoffSpec s sw certHash introducer exporter s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s₁ :=
    (execFullA_handoff_iff_spec s sw certHash introducer exporter s₁).mpr h₁
  have e₂ : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s₂ :=
    (execFullA_handoff_iff_spec s sw certHash introducer exporter s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`swissReconcile_compile_sound` — the welded soundness (swissReconcile slice), against swissHandoff's OWN
descriptor.**

Suppose, for the Argus swissReconcile term `swissReconcileStmt sw certHash introducer exporter`:
  * the standalone swissHandoff circuit `swissReconcileCircuit S LE cN hN hLE s ⟨sw,certHash,introducer,
    exporter⟩ s'` (= `swissHandoffE`'s full-state v2 arithmetization satisfied on the encoded triple) holds,
    under the realizable whole-list digest portals (`hRest : RestIffNoSwiss S.RH`, `hLog : logHashInjective
    S.LH`, and the digest-injectivity witnesses `hN`/`hLE` carried inside the descriptor);
  * the IR term's RAW kernel executor interpretation COMMITS:
    `interp (swissReconcileStmt sw certHash introducer exporter) s.kernel = some k'` (`hexec`), with the
    introducer authorized over the exporting cell (`hauth`, the chained auth side-condition).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached:
`s' = { kernel := k', log := handoffReceipt introducer exporter :: s.log }`. I.e. swissHandoff's OWN circuit
and the IR term AGREE on the WHOLE post-state — the `swiss` side-table cert-bound/refcount-bumped at `sw`
(`handoffSwissPost`), every other RecordKernelState field frozen — AND the receipt log — the full
`HandoffSpec`, not a per-cell projection. The auth side-condition + receipt-log row are named EXPLICITLY
(hypothesis `hauth` + the conclusion's `log`), so the kernel-vs-runtime divergence is part of the welded
statement. So the circuit the prover runs for swissReconcile pins the complete chained state the IR term's
executor produces. -/
theorem swissReconcile_compile_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId) (k' : RecordKernelState)
    (hcirc : swissReconcileCircuit S LE cN hN hLE s ⟨sw, certHash, introducer, exporter⟩ s')
    (hauth : stateAuthB s.kernel.caps introducer exporter = true)
    (hexec : interp (swissReconcileStmt sw certHash introducer exporter) s.kernel = some k') :
    s' = { kernel := k', log := handoffReceipt introducer exporter :: s.log } := by
  -- circuit side: swissHandoff's OWN audited soundness forces the FULL `HandoffSpec` on
  -- `(s, ⟨sw,certHash,introducer,exporter⟩, s')`.
  have hspec : HandoffSpec s sw certHash introducer exporter s' :=
    swissHandoffA_full_sound S LE cN hN hLE hRest hLog s ⟨sw, certHash, introducer, exporter⟩ s' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.swissHandoffA …) = some ⟨k', receipt::log⟩`, and
  -- the independent executor⟺spec corner turns THAT into `HandoffSpec s … ⟨k', receipt::log⟩`.
  have hspec' : HandoffSpec s sw certHash introducer exporter
      { kernel := k', log := handoffReceipt introducer exporter :: s.log } :=
    (execFullA_handoff_iff_spec s sw certHash introducer exporter _).mp
      (interp_swissReconcileStmt_chained s sw certHash introducer exporter k' hauth hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact handoffSpec_unique hspec hspec'

#assert_axioms swissReconcile_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely RECONCILES the cert (cert-bind + refcount-bump observable),
preserves every other field (frame), and the gate REJECTS forged / out-of-domain inputs (fail-closed).

The cornerstone/weld would be hollow if swissReconcile never committed, if the cert-bind were a no-op, if it
touched `bal`, or if the gate admitted everything. A concrete kernel `kR0` with a real swiss entry (swiss
`7`, refcount `1`, NO cert) exercises a genuine cert-bind + bump; the rejection lemma shows the fail-closed
MEMBERSHIP gate returns `none` on an absent swiss number. The anti-ghost punchline: after the reconcile the
entry's `cert` is GENUINELY `some certHash` (a forged post-state that leaves the cert `none` does NOT match —
the load-bearing 3-vat binding `swissHandoffA_full_sound`'s digest enforces). -/

/-- A concrete kernel for the §5 witnesses: cells 0,1 live; an EMPTY `bal` ledger; and a `swiss` table with
ONE entry — swiss `7` at refcount `1`, exporter 0, target 1, NO bound cert (the genuine pre-handoff sturdy
ref a 3-vat introduce reconciles against). -/
def kR0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0
    swiss := [ { swiss := 7, exporter := 0, target := 1, rights := [], refcount := 1, cert := none } ] }

/-- **NON-VACUITY (the term ACTUALLY commits).** The reconcile of a present swiss entry COMMITS (`isSome`) —
the MEMBERSHIP gate genuinely admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem swissReconcileStmt_commits :
    (interp (swissReconcileStmt 7 99 0 0) kR0).isSome = true := by
  rw [interp_swissReconcileStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (the CERT-BIND is OBSERVABLE — the 3-vat reconcile punchline).** A reconcile on swiss `7`
binds the handoff cert: after the commit, `findSwiss` returns the entry with `cert = some 99` (it was `none`
before). The cert-bind is real, not a no-op — this is the load-bearing 3-vat introduce binding the
anti-ghost forgery (`cert` stays `none`) would fail. -/
theorem swissReconcileStmt_binds_cert :
    (interp (swissReconcileStmt 7 99 0 0) kR0).map (fun k => (findSwiss k.swiss 7).bind (·.cert))
      = some (some 99) := by
  rw [interp_swissReconcileStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (the REFCOUNT-BUMP is OBSERVABLE).** A reconcile on swiss `7` (refcount `1`) bumps its
`refcount` from `1` to `2` — the recipient's new live reference (the `replaceSwiss`/`handoffRecord` bump is
real). The CapTP handoff grant, observed. -/
theorem swissReconcileStmt_bumps_refcount :
    (interp (swissReconcileStmt 7 99 0 0) kR0).map (fun k => (findSwiss k.swiss 7).map (·.refcount))
      = some (some 2) := by
  rw [interp_swissReconcileStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (frame: `bal` is untouched).** A reconcile on swiss `7` leaves the `(0,0)` ledger entry at
`0` — the reconcile is balance-NEUTRAL (`setSwiss` writes only `swiss`, never `bal`), exactly the
frozen-frame leg of `HandoffSpec`. No value is conjured or destroyed by a cert-reconcile. -/
theorem swissReconcileStmt_bal_frozen :
    (interp (swissReconcileStmt 7 99 0 0) kR0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_swissReconcileStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (frame: the entry's TARGET/EXPORTER/RIGHTS are untouched).** A reconcile on swiss `7`
leaves the entry's `target` at `1` — the cert-bind/bump rewrites ONLY `cert` + `refcount`, never the
sturdy-ref's identity (exporter/target/rights). The per-entry frame, observed: a handoff cannot silently
re-point a sturdy ref. -/
theorem swissReconcileStmt_target_untouched :
    (interp (swissReconcileStmt 7 99 0 0) kR0).map (fun k => (findSwiss k.swiss 7).map (·.target))
      = some (some 1) := by
  rw [interp_swissReconcileStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (fail-closed: absent entry).** A reconcile on a swiss number that is NOT in the table (here
`42`) does NOT commit — the term returns `none` (the MEMBERSHIP leg of the gate fails). A handoff cert cannot
be reconciled against a sturdy ref that does not exist. -/
theorem swissReconcileStmt_rejects_absent :
    interp (swissReconcileStmt 42 99 0 0) kR0 = none := by
  rw [interp_swissReconcileStmt_eq_swissHandoffK]
  decide

#assert_axioms swissReconcileStmt_commits
#assert_axioms swissReconcileStmt_binds_cert
#assert_axioms swissReconcileStmt_bumps_refcount
#assert_axioms swissReconcileStmt_bal_frozen
#assert_axioms swissReconcileStmt_target_untouched
#assert_axioms swissReconcileStmt_rejects_absent

end Dregg2.Circuit.Argus.Effects.SwissReconcile
