/-
# Dregg2.Circuit.Argus.Effects.SwissHandoff — the CapTP three-party sturdy-ref HANDOFF effect
`swissHandoffA` welded into the Argus IR, as a FULL-STATE `Surface2` weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn/createEscrow. `Effects/SwissExport.lean` and `Effects/SwissDrop.lean` then welded the
sibling CapTP swiss-table arms (MINT / GC-decrement) to their genuine standalone v2 `Surface2` descriptors,
concluding the WHOLE 17-field post-state. This module follows that STRONGER surface for the three-party
HANDOFF primitive `swissHandoffA`, in a disjoint file (it imports the Argus IR + the audited `swissHandoffA`
v2 instance + the independent handoff spec, all read-only, and owns only its own declarations).

`swissHandoffA sw certHash introducer exporter` binds a 3-vat introduce CERT (the GIFTER→GIFTEE handoff
certificate hash `certHash`) to the swiss-table entry `sw` AND grants the recipient a new live reference by
BUMPING the entry's `refcount` (`apply.rs:4109`). The verified RAW kernel step is `swissHandoffK`
(`RecordKernel.lean:2733`):

    swissHandoffK k sw certHash
      = match findSwiss k.swiss sw with
        | none   => none
        | some e => some { k with swiss := replaceSwiss k.swiss sw
                                    { e with cert := some certHash, refcount := e.refcount + 1 } }

so a committed handoff is FAIL-CLOSED if the swiss number is ABSENT, and otherwise rewrites EXACTLY the
`swiss` list side-table (the declarative cert-bind/refcount-bump image
`Spec.SwissHandoff.handoffSwissPost k.swiss sw e certHash`), freezing every other RecordKernelState field —
it is balance-NEUTRAL (`swissHandoffK_balNeutral`). Because the body touches the `swiss` list side-table,
the IR move is the §A `setSwiss` component-write primitive — NOT `setCell` (transfer's), `setBal`
(balanceA's), nor `setLifecycle` (cellSeal's). That is the structural contrast.

A real difference from swissDrop: `swissHandoffK` is UNCONDITIONAL on commit. swissDrop is a genuinely
CONDITIONAL state edit (remove-vs-decrement, fail-closed below refcount > 0); `swissHandoffK` ALWAYS commits
the cert-bind/bump once the entry is FOUND (no positive-refcount side-gate — a handoff grows the refcount,
it cannot under-flow it). So the IR term's guard is the SINGLE membership conjunct `(findSwiss k.swiss sw)
.isSome` — the ONLY admission condition the kernel step checks — and the `setSwiss` leaf reads the found
entry and installs the declarative cert-bind/bump image, matching `swissHandoffK` on the nose via the
audited `handoffSwissUpdate`/`handoffSwissPost` bridge lemmas (`Spec/swisshandoff.lean`).

## THE CERT IS WITNESS-SUPPLIED — the non-amplification honesty (read this).

The `certHash` is a PARAMETER of the effect, NOT validated in the kernel step `swissHandoffK` itself: the
step binds WHATEVER `certHash` it is handed (`cert := some certHash`). The CapTP three-party-handoff
SOUNDNESS — that `certHash` is a GENUINE GIFTER→GIFTEE introduce certificate, not a forged one — is NOT
discharged on this Argus surface. What IS enforced inline, on the kernel step:

  * MEMBERSHIP — the swiss entry `sw` must exist (`findSwiss … = some e`); a handoff of a non-existent
    sturdy ref is fail-closed (`interp … = none`). Carried as the guard.
  * AUTHORITY — the introducer must hold authority over the exporting cell
    (`stateAuthB s.kernel.caps introducer exporter`); the CHAINED layer's pre-gate. Carried as the explicit
    `hauth` side-condition in §3/§4 (NOT papered).

So this module is HONEST that the handoff's non-amplification rests on a NAMED ASSUMPTION carried OUTSIDE
the Argus term: the `certHash` is treated as an opaque, witness-supplied cert hash, and its provenance is a
3-vat introduce-protocol obligation discharged elsewhere (`Exec.CapTPHandoffSound`, the unforgeability
model), NOT in `swissHandoffK` / this IR weld. The Argus weld faithfully captures EXACTLY what the kernel
step does with the cert (bind it, bump the refcount, fail-closed on absent swiss), and is precise about
what it does NOT (validate the cert's authenticity). See the `divergence` note in the structured result.

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; the verified chained
step `swissHandoffChainA` (`TurnExecutorFull.lean:2823`) is a `RecChainedState → Option RecChainedState`
step — it ALSO (i) PRE-GATES on `stateAuthB s.kernel.caps introducer exporter` (the introducer's authority
over the exporting cell — the auth leg `swissHandoffK` itself does NOT check; it lives in the chained
wrapper) and (ii) PREPENDS one self-targeted receipt row `handoffReceipt introducer exporter :: s.log`, and
the `log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's `interp` cannot — and
does not — emit the auth gate or the log row; it captures EXACTLY the KERNEL side of the chained step (the
`swissHandoffK` cert-bind/bump). This is the SAME chained-vs-raw boundary `SwissDrop` carries, here named
precisely:

  * `interp (swissHandoffStmt sw certHash introducer exporter) k` produces the KERNEL post-state — exactly
    `swissHandoffK k sw certHash` (`interp_swissHandoffStmt_eq_swissHandoffK`), the cert-bind/bump on the
    `swiss` side-table, fail-closed on the membership domain. It does NOT see `introducer`/`exporter` (those
    are the auth leg of the chained wrapper); they are carried as IR parameters only so the term names the
    same effect.
  * lifting to the chained `execFullA` (`interp_swissHandoffStmt_chained`) re-attaches BOTH the runtime
    `stateAuthB` auth gate (carried as an explicit hypothesis `hauth`) and the receipt row
    `handoffReceipt introducer exporter :: s.log` — the runtime layer the kernel `interp` does not model.
    The welded conclusion (§4) then names the chained post-state `{ kernel := k', log := receipt :: s.log }`
    EXPLICITLY, so the auth side-condition + receipt-log obligation are part of the welded statement (not
    papered).

## THE DESCRIPTOR — a GENUINE full-state v2 `Surface2`, NOT EffectVM-inherited.

`swissHandoffA` carries its OWN standalone v2 `EffectCommit2`/`Surface2` descriptor + full soundness
(`Dregg2/Circuit/Inst/swissHandoffA.lean`): `swissHandoffE` (the `EffectSpec2` whose touched component is
the WHOLE `swiss : List SwissRecord` side-table, a `listComponent` FULL-list digest) and
`swissHandoffA_full_sound : satisfiedE2 … (swissHandoffE …) … ⟹ HandoffSpec` — a FULL declarative
post-state soundness keyed on the CHAINED executor `swissHandoffChainA`/`execFullA` via the INDEPENDENT
`execFullA_handoff_iff_spec` (executor ⟺ `HandoffSpec`, BOTH directions, `Spec/swisshandoff.lean`).
`HandoffSpec` pins the touched `swiss` side-table, the receipt-log growth, AND (through its strengthened
twin `HandoffSpecFull`, with an anti-ghost `delegate`-tamper tooth) the 16-field frame. This is the
strictly-stronger `SwissExport`/`SwissDrop` surface (whole-state full-list digest), not the per-cell
EffectVM/`cellProj` surface transfer/delegate live on. (The EffectVM `sturdyref_root` descriptor for this
effect, `Emit/EffectVmEmitSwissHandoff.lean`, is precisely flagged NAME-ONLY there — no live runtime
selector; we weld the genuine full-state v2 surface instead.)

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the whole-list digest
assumptions enter ONLY inside the reused `swissHandoffA_full_sound` (its `compressNInjective` /
`listLeafInjective` digest-injectivity hypotheses + the Poseidon-CR `RestIffNoSwiss` / `logHashInjective`
portals), not in the welded conclusion's statement. The handoff-cert authenticity is a NAMED out-of-band
assumption (carried, NOT discharged here — see the cert-honesty header above). No `sorry`, no `:= True`, no
`native_decide`. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.swissHandoffA
import Dregg2.Circuit.Spec.swisshandoff
import Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull

namespace Dregg2.Circuit.Argus.Effects.SwissHandoff

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
   handoffSwissUpdate_eq_k handoffSwissUpdate_some execFullA_handoff_iff_spec)
open Dregg2.Circuit.Inst.SwissHandoffA (HandoffArgs swissHandoffE swissHandoffA_full_sound RestIffNoSwiss)

/-! ## §1 — The swissHandoff effect as an Argus IR term (gate, then the `setSwiss` cert-bind/bump move).

`swissHandoffK`'s shape is `match findSwiss k.swiss sw with | none => none | some e => some { k with swiss
:= replaceSwiss k.swiss sw { e with cert := some certHash, refcount := e.refcount + 1 } }`. We capture its
KERNEL side term-for-term: a `Bool` `handoffKGuard` of EXACTLY the fail-closed admission domain (the swiss
entry `sw` is PRESENT — the SINGLE membership conjunct, since `swissHandoffK` commits UNCONDITIONALLY once
the entry is found), then a `setSwiss` whose leaf reads the found entry and installs the declarative
cert-bind/bump image `handoffSwissPost k.swiss sw e certHash`. The contrast with transfer/balanceA/cellSeal
is the move primitive: `setSwiss` (rewrites the `swiss` list side-table) over the cert-bind + refcount-bump,
NOT `setCell` / `setBal` / `setLifecycle`. The AUTH leg (`stateAuthB`) is NOT here — it is the chained
wrapper's gate, re-attached in §3. -/

/-- The swissHandoff KERNEL admissibility gate as a `Bool` — exactly `swissHandoffK`'s fail-closed domain:
the swiss entry `sw` is PRESENT (`findSwiss` is `some`). UNLIKE swissDrop, there is NO refcount-positive
side-condition: a handoff binds the cert and BUMPS the refcount, so it commits unconditionally once the
entry is found (a bump cannot under-flow). When the entry is absent the gate is `false` and the term rejects
(`none`), matching `swissHandoffK` exactly. The AUTH leg (`stateAuthB`) is NOT here — it is the chained
wrapper's gate, re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
def handoffKGuard (sw : Nat) (k : RecordKernelState) : Bool :=
  (findSwiss k.swiss sw).isSome

/-- The swissHandoff `setSwiss` leaf — the post-`swiss` list `swissHandoffK` installs on a committed
handoff. On a present entry it is the declarative cert-bind/bump image `handoffSwissPost k.swiss sw e
certHash` (`replaceSwiss` of the entry with `cert := some certHash, refcount := e.refcount + 1`); off the
membership domain (absent entry) it is the identity (`k.swiss`), which never fires because the guard rejects
there. The genuine `setSwiss` payload — NOT a no-op. -/
def handoffSwissLeaf (sw certHash : Nat) (k : RecordKernelState) : List SwissRecord :=
  match findSwiss k.swiss sw with
  | some e => handoffSwissPost k.swiss sw e certHash
  | none   => k.swiss

/-- **The swissHandoff effect as an IR term: gate, then the `setSwiss` cert-bind/bump.** Mirrors
`swissDropStmt` (gate, then a `setSwiss` move on the `swiss` side-table) but the move is the cert-bind +
refcount-bump (`handoffSwissPost`) under the SINGLE membership gate (no positive-refcount side-condition —
the handoff is unconditional once found), NOT swissDrop's conditional remove/decrement. The `setSwiss` leaf
is `handoffSwissLeaf sw certHash k`, EXACTLY the post-`swiss` `swissHandoffK` installs on the kernel (the
runtime `stateAuthB` auth gate + receipt-log row are re-attached in §3). `introducer`/`exporter` are carried
as IR parameters only (the chained wrapper's auth leg names them); the KERNEL step `swissHandoffK` does not
read them. -/
def swissHandoffStmt (sw certHash : Nat) (_introducer _exporter : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (handoffKGuard sw))
    (RecStmt.setSwiss (fun k => handoffSwissLeaf sw certHash k))

/-! ## §2 — The cornerstone: `interp` of the swissHandoff term IS the raw kernel step `swissHandoffK`. -/

/-- The swissHandoff `Bool` gate decodes to `swissHandoffK`'s fail-closed admission domain (entry present).
The analog of `transferGuard_iff` / `dropKGuard_iff` — but a SINGLE membership conjunct (no refcount leg),
since the handoff commits unconditionally once the entry is found. -/
theorem handoffKGuard_iff (sw : Nat) (k : RecordKernelState) :
    handoffKGuard sw k = true ↔ (∃ e : SwissRecord, findSwiss k.swiss sw = some e) := by
  unfold handoffKGuard
  cases hf : findSwiss k.swiss sw with
  | none   =>
    simp only [hf, Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
    intro e he; exact absurd he (by simp)
  | some e =>
    simp only [hf, Option.isSome_some, true_iff]
    exact ⟨e, rfl⟩

/-- **The cornerstone (raw-kernel cert-bind/bump).** `interp` of the swissHandoff term IS the verified RAW
kernel step `swissHandoffK` — the same partial function, by construction, exactly as the transfer/swissDrop
cornerstones, now over the `swiss` list side-table via `setSwiss`/`handoffSwissPost` (NOT the record-cell
`setCell`/`setBal` nor the `setLifecycle` of cellSeal). On the membership domain the term commits to
`{ k with swiss := handoffSwissPost k.swiss sw e certHash }` — exactly the cert-bind/bump `swissHandoffK`
installs — and rejects (`none`) on exactly the same fail-closed gate (entry absent). This is the per-effect
executor-refinement for the CapTP three-party-handoff family. The runtime auth gate + receipt-log prepend
are re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
theorem interp_swissHandoffStmt_eq_swissHandoffK (sw certHash : Nat) (introducer exporter : CellId)
    (k : RecordKernelState) :
    interp (swissHandoffStmt sw certHash introducer exporter) k = swissHandoffK k sw certHash := by
  simp only [swissHandoffStmt, interp]
  by_cases hg : handoffKGuard sw k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setSwiss` move installs `handoffSwissLeaf sw
    -- certHash k`, which on the found entry is `handoffSwissPost k.swiss sw e certHash`. The audited
    -- `handoffSwissUpdate_some` + `handoffSwissUpdate_eq_k` bridge that to `swissHandoffK k sw certHash =
    -- some { k with swiss := handoffSwissPost … }`.
    obtain ⟨e, hf⟩ := (handoffKGuard_iff sw k).mp hg
    rw [if_pos hg]
    simp only [Option.bind]
    -- the leaf reduces to `handoffSwissPost k.swiss sw e certHash` on the found entry.
    have hleaf : handoffSwissLeaf sw certHash k = handoffSwissPost k.swiss sw e certHash := by
      simp only [handoffSwissLeaf, hf]
    rw [hleaf]
    -- `swissHandoffK k sw certHash = some { k with swiss := handoffSwissPost k.swiss sw e certHash }`
    -- via the audited bridge.
    exact ((handoffSwissUpdate_eq_k k sw certHash (handoffSwissPost k.swiss sw e certHash)).mp
      (handoffSwissUpdate_some k.swiss sw certHash e hf)).symm
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; and `swissHandoffK k sw certHash = none` on the SAME
    -- domain (entry absent), since the guard decoded EXACTLY that domain.
    rw [if_neg hg]
    simp only [Option.bind]
    -- the negated guard says: NOT (∃ e, found). Show `swissHandoffK k sw certHash = none`.
    symm
    unfold swissHandoffK
    cases hf : findSwiss k.swiss sw with
    | none   => rfl
    | some e =>
      -- found entry ⇒ the guard WOULD have admitted; contradiction with the negated guard.
      exact absurd ((handoffKGuard_iff sw k).mpr ⟨e, hf⟩) hg

#assert_axioms interp_swissHandoffStmt_eq_swissHandoffK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `swissHandoffChainA` / `execFullA`.

The standalone swissHandoff descriptor (§4) is keyed on the CHAINED executor `swissHandoffChainA` /
`execFullA` over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.swissHandoffA sw certHash
introducer exporter) = swissHandoffChainA s sw certHash introducer exporter`. The §2 cornerstone is over the
RAW kernel step `swissHandoffK`. The chained layer is exactly the §2 kernel cert-bind/bump PLUS two things:
a `stateAuthB` auth pre-gate (the introducer's authority over the exporting cell, which `swissHandoffK` does
NOT check) and the runtime receipt-log prepend `handoffReceipt introducer exporter :: s.log`. We bridge
faithfully, carrying the `stateAuthB` auth conjunct as an explicit hypothesis and naming the receipt-row
prepend EXPLICITLY in the chained post-state (the honest kernel-vs-runtime divergence — NOT papered). -/

/-- **`interp_swissHandoffStmt_chained` — the IR term's RAW kernel executor, lifted to the chained
`execFullA`.** When the introducer has authority over the exporting cell (`hauth : stateAuthB s.kernel.caps
introducer exporter = true`, the chained layer's extra auth gate) and the §2 cornerstone commits on the
kernel (`interp (swissHandoffStmt sw certHash introducer exporter) s.kernel = some k'`), the unified action
executor `execFullA s (.swissHandoffA sw certHash introducer exporter)` commits to the chained state
`⟨k', handoffReceipt introducer exporter :: s.log⟩`. So the Argus term's KERNEL meaning lifts to the chained
executor the standalone descriptor speaks about, with the runtime auth side-condition carried + the runtime
receipt-log row (which the kernel `interp` does not model) re-attached HERE — the explicit kernel-vs-runtime
bridge. -/
theorem interp_swissHandoffStmt_chained
    (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId) (k' : RecordKernelState)
    (hauth : stateAuthB s.kernel.caps introducer exporter = true)
    (hexec : interp (swissHandoffStmt sw certHash introducer exporter) s.kernel = some k') :
    execFullA s (.swissHandoffA sw certHash introducer exporter)
      = some { kernel := k', log := handoffReceipt introducer exporter :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `swissHandoffK`.
  rw [interp_swissHandoffStmt_eq_swissHandoffK] at hexec
  -- `execFullA s (.swissHandoffA …)` reduces to `swissHandoffChainA s sw certHash introducer exporter`,
  -- which on `stateAuthB` opens to a `match swissHandoffK …` — and `hexec` names that as `some k'`.
  show swissHandoffChainA s sw certHash introducer exporter
    = some { kernel := k', log := handoffReceipt introducer exporter :: s.log }
  unfold swissHandoffChainA handoffReceipt
  rw [if_pos hauth, hexec]

#assert_axioms interp_swissHandoffStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of swissHandoff's OWN standalone full-state circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against swissHandoff's GENUINE standalone descriptor `swissHandoffCircuit S (swissHandoffE …)`
(the v2 `Surface2` circuit whose soundness is `swissHandoffA_full_sound`), NOT the EffectVM `sturdyref_root`
descriptor (NAME-ONLY there — see this file's header). The executor side is routed through §3 (`interp` ⟹
`execFullA`) and the independent `execFullA_handoff_iff_spec` (executor ⟺ `HandoffSpec`); the circuit side is
the audited `swissHandoffA_full_sound` (circuit ⟹ `HandoffSpec`). Both name the SAME `HandoffSpec`, so they
PROVABLY agree on the WHOLE post-state — the touched `swiss` side-table (cert-bind/bump image), the
receipt-log growth, and the 16-field frame — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `swissHandoff` term: swissHandoff's OWN audited standalone v2
`Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (swissHandoffE …) (encodeE2 …)`
satisfied on the encoded `(s, ⟨sw, certHash, introducer, exporter⟩, s')` triple (the `EffectRefinement`
hub's `effect2CircuitStep`, inlined here so this module imports only `Inst.swissHandoffA` + the spec). Its
soundness `swissHandoffA_full_sound` pins the complete `HandoffSpec`. The `swissHandoff`-keyed analog of
`swissDropCircuit` / `swissExportCircuit`, in the descriptor universe where swissHandoff carries its OWN
genuine full-state circuit (NOT EffectVM-inherited). The whole-list digest closure `LE`/`cN` + their
injectivity witnesses are passed through verbatim (the realizable Poseidon carriers). -/
def swissHandoffCircuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2 S (swissHandoffE LE cN hN hLE) (encodeE2 S (swissHandoffE LE cN hN hLE) s args s')

/-- **`handoffSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`HandoffSpec s sw certHash introducer exporter ·` are equal. Rather than re-derive this field-by-field, we
route through the PROVEN executor⟺spec corner `execFullA_handoff_iff_spec`: each `HandoffSpec` reconstructs
the SAME committed value `execFullA s (.swissHandoffA sw certHash introducer exporter) = some ·`, and `some`
is injective. This is exactly the sense in which `HandoffSpec` is functional — it determines the post-state
— so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem handoffSpec_unique {s s₁ s₂ : RecChainedState} {sw certHash : Nat} {introducer exporter : CellId}
    (h₁ : HandoffSpec s sw certHash introducer exporter s₁)
    (h₂ : HandoffSpec s sw certHash introducer exporter s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s₁ :=
    (execFullA_handoff_iff_spec s sw certHash introducer exporter s₁).mpr h₁
  have e₂ : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s₂ :=
    (execFullA_handoff_iff_spec s sw certHash introducer exporter s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`swissHandoff_compile_sound` — the welded soundness (swissHandoff slice), against swissHandoff's OWN
descriptor.**

Suppose, for the Argus swissHandoff term `swissHandoffStmt sw certHash introducer exporter`:
  * the standalone swissHandoff circuit `swissHandoffCircuit S LE cN hN hLE s ⟨sw, certHash, introducer,
    exporter⟩ s'` (= `swissHandoffE`'s full-state v2 arithmetization satisfied on the encoded triple) holds,
    under the realizable whole-list digest portals (`hRest : RestIffNoSwiss S.RH`, `hLog : logHashInjective
    S.LH`, and the digest-injectivity witnesses `hN`/`hLE` carried inside the descriptor);
  * the IR term's RAW kernel executor interpretation COMMITS:
    `interp (swissHandoffStmt sw certHash introducer exporter) s.kernel = some k'` (`hexec`), with the
    introducer authorized over the exporting cell (`hauth`, the chained auth side-condition).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached:
`s' = { kernel := k', log := handoffReceipt introducer exporter :: s.log }`. I.e. swissHandoff's OWN circuit
and the IR term AGREE on the WHOLE post-state — the `swiss` side-table cert-bound/refcount-bumped at `sw`
(`handoffSwissPost`), every other RecordKernelState field frozen (INCLUDING `bal`, balance-NEUTRAL) — AND
the receipt log — the full `HandoffSpec`, not a per-cell projection. The auth side-condition + receipt-log
row are named EXPLICITLY (hypothesis `hauth` + the conclusion's `log`), so the kernel-vs-runtime divergence
is part of the welded statement.

DIVERGENCE CARRIED (honest): the `certHash` is witness-supplied and NOT validated for authenticity by either
the IR term or the circuit (both bind whatever cert they are handed); the three-party-handoff cert
unforgeability is a NAMED out-of-band assumption (`Exec.CapTPHandoffSound`), not discharged on this surface.
So the circuit the prover runs for swissHandoff pins the complete chained state the IR term's executor
produces, MODULO that named cert-authenticity assumption. -/
theorem swissHandoff_compile_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId) (k' : RecordKernelState)
    (hcirc : swissHandoffCircuit S LE cN hN hLE s ⟨sw, certHash, introducer, exporter⟩ s')
    (hauth : stateAuthB s.kernel.caps introducer exporter = true)
    (hexec : interp (swissHandoffStmt sw certHash introducer exporter) s.kernel = some k') :
    s' = { kernel := k', log := handoffReceipt introducer exporter :: s.log } := by
  -- circuit side: swissHandoff's OWN audited soundness forces the FULL `HandoffSpec` on
  -- `(s, ⟨sw,certHash,introducer,exporter⟩, s')`.
  have hspec : HandoffSpec s sw certHash introducer exporter s' :=
    swissHandoffA_full_sound S LE cN hN hLE hRest hLog s ⟨sw, certHash, introducer, exporter⟩ s' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.swissHandoffA …) = some ⟨k', receipt::log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `HandoffSpec s … ⟨k', receipt::log⟩`.
  have hspec' : HandoffSpec s sw certHash introducer exporter
      { kernel := k', log := handoffReceipt introducer exporter :: s.log } :=
    (execFullA_handoff_iff_spec s sw certHash introducer exporter _).mp
      (interp_swissHandoffStmt_chained s sw certHash introducer exporter k' hauth hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact handoffSpec_unique hspec hspec'

#assert_axioms swissHandoff_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely binds the cert / bumps the refcount (move observable),
preserves every other field (frame), and the gate REJECTS forged / out-of-domain inputs (fail-closed).

The cornerstone/weld would be hollow if swissHandoff never committed, if the move were a no-op, if it
touched `bal`, or if the gate admitted everything. A concrete kernel `kH0` with a real swiss entry (swiss
`7`, refcount `2`, no cert) exercises a genuine cert-bind + refcount-bump; the rejection lemma shows the
fail-closed membership gate returns `none` on an absent entry; a frame lemma shows a DIFFERENT entry is
untouched; balance-neutrality is observed on the per-asset ledger. -/

/-- A concrete kernel for the §5 witnesses: cells 0,1 live; an EMPTY `bal` ledger; and a `swiss` table with
TWO entries — swiss `7` at refcount `2`, no cert (the cert-bind/bump witness) and swiss `9` at refcount `1`
(the frame witness — must stay untouched). -/
def kH0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0
    swiss := [ { swiss := 7, exporter := 0, target := 1, rights := [], refcount := 2, cert := none },
               { swiss := 9, exporter := 0, target := 1, rights := [], refcount := 1, cert := none } ] }

/-- **NON-VACUITY (the CERT-BIND is OBSERVABLE).** A handoff on swiss `7` binding cert `99` commits and sets
the entry's `cert` from `none` to `some 99` — the `setSwiss`/`handoffSwissPost` cert-bind is real, not a
no-op. The load-bearing fact a later cert-membership check reads. -/
theorem swissHandoffStmt_binds_cert :
    (interp (swissHandoffStmt 7 99 0 0) kH0).map (fun k => (findSwiss k.swiss 7).map (·.cert))
      = some (some (some 99)) := by
  rw [interp_swissHandoffStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (the REFCOUNT-BUMP is OBSERVABLE).** The same handoff bumps swiss `7`'s `refcount` from
`2` to `3` — the recipient's new live reference (the `+1` is real). A handoff GROWS the refcount; it cannot
under-flow it (why no positive-refcount side-gate is needed). -/
theorem swissHandoffStmt_bumps_refcount :
    (interp (swissHandoffStmt 7 99 0 0) kH0).map (fun k => (findSwiss k.swiss 7).map (·.refcount))
      = some (some 3) := by
  rw [interp_swissHandoffStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (the term ACTUALLY commits).** The handoff of a present swiss entry COMMITS (`isSome`) —
the membership gate genuinely admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem swissHandoffStmt_commits :
    (interp (swissHandoffStmt 7 99 0 0) kH0).isSome = true := by
  rw [interp_swissHandoffStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT swiss entry is untouched).** Handing off swiss `7` leaves the OTHER
entry (swiss `9`) at its original `refcount 1` and `cert none` — `setSwiss`/`handoffSwissPost` rewrites ONLY
the handed-off entry, confirming the move is local (not a global swiss-table collapse). The per-entry frame,
observed. -/
theorem swissHandoffStmt_other_entry_untouched :
    (interp (swissHandoffStmt 7 99 0 0) kH0).map
        (fun k => (findSwiss k.swiss 9).map (fun e => (e.refcount, e.cert)))
      = some (some (1, none)) := by
  rw [interp_swissHandoffStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (frame: `bal` is untouched — the CapTP punchline).** Handing off swiss `7` leaves the
`(0,0)` ledger entry at `0` — the handoff is balance-NEUTRAL (`setSwiss` writes only `swiss`, never `bal`),
exactly the frozen-frame leg of `HandoffSpec`. A handoff moves a REFERENCE, NOT balance. -/
theorem swissHandoffStmt_bal_frozen :
    (interp (swissHandoffStmt 7 99 0 0) kH0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_swissHandoffStmt_eq_swissHandoffK]
  decide

/-- **NON-VACUITY (fail-closed: absent entry / MEMBERSHIP).** A handoff on a swiss number that is NOT in the
table (here `42`) does NOT commit — the term returns `none` (the MEMBERSHIP leg of the gate fails). A
non-existent reference cannot be handed off. -/
theorem swissHandoffStmt_rejects_absent :
    interp (swissHandoffStmt 42 99 0 0) kH0 = none := by
  rw [interp_swissHandoffStmt_eq_swissHandoffK]
  decide

#assert_axioms swissHandoffStmt_binds_cert
#assert_axioms swissHandoffStmt_bumps_refcount
#assert_axioms swissHandoffStmt_commits
#assert_axioms swissHandoffStmt_other_entry_untouched
#assert_axioms swissHandoffStmt_bal_frozen
#assert_axioms swissHandoffStmt_rejects_absent

/-! ## §MAGNESIUM — the RUNNABLE descriptor binds the FULL `system_roots` sub-block (whole-state).

`Emit/EffectVmEmitSwissFamilyFull.lean` lifts the RUNNABLE EffectVM descriptor for `swissHandoffA` to bind
the FULL 17-field post-state (`swissHandoff_runnable_full_sound` pins `SwissFullClause`; the anti-ghost
`swissHandoff_runnable_rejects_root_tamper` rules out a tamper of ANY of the 8 side-table roots). This
section restates the headline at the effect level: the STURDYREF root advances to the cert-bound/bumped-list
digest, and the 7 OTHER side-table roots are provably FROZEN — the whole-state binding the per-cell
descriptor could not state. -/

open Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull
  (SwissFullClause SwissFullClause_sturdyref_advance SwissFullClause_other_roots_frozen sturdyrefIdx)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Exec.SystemRoots (SysRoots N_SYSTEM_ROOTS)

/-- **`magnesium_binds_full_sysroots` — the whole-`system_roots` binding for swissHandoff.** From the
RUNNABLE full-state crown's `SwissFullClause`, the post STURDYREF root IS the witnessed cert-bound/bumped
swiss-list digest `d`, and EVERY other side-table root is FROZEN at its pre value. So a `swissHandoffA` proof
binds the whole `system_roots` sub-block, not a per-cell projection. -/
theorem magnesium_binds_full_sysroots
    {d : ℤ} {pre post : CellState} {preRoots postRoots : SysRoots}
    (hfull : SwissFullClause d pre post preRoots postRoots) :
    postRoots sturdyrefIdx = d
    ∧ (∀ i : Fin N_SYSTEM_ROOTS, i ≠ sturdyrefIdx → postRoots i = preRoots i) :=
  ⟨SwissFullClause_sturdyref_advance hfull, fun i hi => SwissFullClause_other_roots_frozen hfull i hi⟩

#assert_axioms magnesium_binds_full_sysroots

end Dregg2.Circuit.Argus.Effects.SwissHandoff
