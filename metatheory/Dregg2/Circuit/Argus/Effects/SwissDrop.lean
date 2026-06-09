/-
# Dregg2.Circuit.Argus.Effects.SwissDrop — the CapTP sturdy-ref DROP / GC effect `swissDropA` welded
into the Argus IR, as a FULL-STATE `Surface2` weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` and `Effects/CellSeal.lean` then welded
per-component / side-table effects to their genuine standalone v2 `Surface2` descriptors, concluding the
WHOLE 17-field post-state. This module follows that STRONGER surface for the genuinely different CapTP
garbage-collection primitive `swissDropA`, in a disjoint file (it imports the Argus IR + the audited
`swissDropA` v2 instance + the independent drop spec, all read-only, and owns only its own declarations).

`swissDropA sw actor exporter` GCs a sturdy reference: it DECREMENTS the swiss-table entry `sw`'s
`refcount`, and when that count reaches `0` it REMOVES the entry entirely (`apply.rs:4051`,
"refcount is already zero"). The verified RAW kernel step is `swissDropK` (`RecordKernel.lean:2745`):

    swissDropK k sw
      = match findSwiss k.swiss sw with
        | none   => none
        | some e => if e.refcount = 0 then none
                    else if e.refcount - 1 = 0 then some { k with swiss := removeSwiss k.swiss sw }
                    else some { k with swiss := replaceSwiss k.swiss sw { e with refcount := e.refcount - 1 } }

so a committed drop is FAIL-CLOSED if the swiss number is ABSENT or the `refcount` is already `0`, and
otherwise rewrites EXACTLY the `swiss` list side-table (the declarative GC/decrement image
`Spec.SwissDrop.dropSwissPost k.swiss sw e`), freezing every other RecordKernelState field — it is
balance-NEUTRAL (`swissDropK_balNeutral`). Because the body touches the `swiss` list side-table, the IR
move is the §A `setSwiss` component-write primitive — NOT `setCell` (transfer's), `setBal` (balanceA's),
nor `setLifecycle` (cellSeal's). That is the structural contrast.

A real difference from cellSeal/balanceA: `swissDropK` is a GENUINELY CONDITIONAL state edit. The post-
`swiss` is not an unconditional rewrite of one field (cellSeal's `setLifecycle k cell lcSealed`); it
either REMOVES (`removeSwiss`, refcount hits 0) or DECREMENTS (`replaceSwiss` with `refcount-1`) the
found entry, and is `none` outside the membership/positive-refcount domain. So the IR term is a
`seq (guard <found ∧ refcount>0>) (setSwiss <dropSwissPost of the found entry>)`: the guard captures the
fail-closed GC domain (entry present, refcount positive), and the `setSwiss` leaf reads the found entry
and installs the declarative GC/decrement image — matching `swissDropK` on the nose via the audited
`dropSwissUpdate`/`dropSwissPost` bridge lemmas (`Spec/swissdrop.lean`).

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; the verified chained
step `swissDropChainA` (`TurnExecutorFull.lean:2833`) is a `RecChainedState → Option RecChainedState` step
— it ALSO (i) PRE-GATES on `stateAuthB s.kernel.caps actor exporter` (the holder's authority over the
exporting cell — the auth leg `swissDropK` itself does NOT check; it lives in the chained wrapper) and
(ii) PREPENDS one self-targeted receipt row `dropReceipt actor exporter :: s.log`, and the `log` lives in
`RecChainedState`, NOT in `RecordKernelState`. So the IR term's `interp` cannot — and does not — emit the
auth gate or the log row; it captures EXACTLY the KERNEL side of the chained step (the `swissDropK`
GC/decrement). This is the SAME chained-vs-raw boundary `BalanceA` carries (its `interp` is on the raw
kernel; the chained `execFullA` adds an `acceptsEffects` pre-gate + a log prepend) and `CellSeal` carries
(receipt-log prepend), here named precisely:

  * `interp (swissDropStmt sw actor exporter) k` produces the KERNEL post-state — exactly `swissDropK k sw`
    (`interp_swissDropStmt_eq_swissDropK`), the GC/decrement on the `swiss` side-table, fail-closed on the
    membership/positive-refcount domain. It does NOT see `actor`/`exporter` (those are the auth leg of the
    chained wrapper); they are carried as IR parameters only so the term names the same effect.
  * lifting to the chained `execFullA` (`interp_swissDropStmt_chained`) re-attaches BOTH the runtime
    `stateAuthB` auth gate (carried as an explicit hypothesis `hauth`) and the receipt row
    `dropReceipt actor exporter :: s.log` — the runtime layer the kernel `interp` does not model. The
    welded conclusion (§4) then names the chained post-state `{ kernel := k', log := receipt :: s.log }`
    EXPLICITLY, so the auth side-condition + receipt-log obligation are part of the welded statement (not
    papered).

## THE DESCRIPTOR — a GENUINE full-state v2 `Surface2`, NOT EffectVM-inherited.

`swissDropA` carries its OWN standalone v2 `EffectCommit2`/`Surface2` descriptor + full soundness
(`Dregg2/Circuit/Inst/swissDropA.lean`): `swissDropE` (the `EffectSpec2` whose touched component is the
WHOLE `swiss : List SwissRecord` side-table, a `listComponent` full-list digest) and
`swissDropA_full_sound : satisfiedE2 … (swissDropE …) … ⟹ DropSpec` — a FULL declarative post-state
soundness keyed on the CHAINED executor `swissDropChainA`/`execFullA` via the INDEPENDENT
`execFullA_drop_iff_spec` (executor ⟺ `DropSpec`, BOTH directions). `DropSpec` pins the touched `swiss`
side-table, the receipt-log growth, AND the 16-field frame (its strengthened twin `DropSpecFull`,
`Spec/swissdrop.lean`, spells out the frame as 16 checkable conjuncts and proves `DropSpec ≡ DropSpecFull`,
with an anti-ghost `caps`-tamper tooth). This is the strictly-stronger `BalanceA`/`CellSeal` surface
(whole-state full-list digest), not the per-cell EffectVM/`cellProj` surface transfer/delegate live on.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the whole-list
digest assumptions enter ONLY inside the reused `swissDropA_full_sound` (its `compressNInjective` /
`listLeafInjective` digest-injectivity hypotheses + the Poseidon-CR `RestIffNoSwiss` / `logHashInjective`
portals), not in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports
are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.swissDropA
import Dregg2.Circuit.Spec.swissdrop

namespace Dregg2.Circuit.Argus.Effects.SwissDrop

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
-- `stateAuthB` (the holder's authority gate, the chained wrapper's auth leg) lives in
-- `Dregg2.Exec.EffectsState`. (`open` is not transitive, so it is named even though the Inst/Spec deps
-- use it.)
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/swissDropA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective` AND `compressNInjective` live in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2`
-- in `EffectCommit2`; `listLeafInjective` in `ListCommit`.
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.Spec.SwissDrop
  (DropGuard DropSpec dropReceipt dropSwissPost dropSwissUpdate dropSwissUpdate_eq_k
   dropSwissPost_eq_update execFullA_drop_iff_spec)
open Dregg2.Circuit.Inst.SwissDropA (DropArgs swissDropE swissDropA_full_sound RestIffNoSwiss)

/-! ## §1 — The swissDrop effect as an Argus IR term (gate, then the `setSwiss` GC/decrement move).

`swissDropK`'s shape is `match findSwiss k.swiss sw with | none => none | some e => if e.refcount = 0 then
none else some { k with swiss := dropSwissPost k.swiss sw e }`. We capture its KERNEL side term-for-term:
a `Bool` `dropKGuard` of EXACTLY the fail-closed GC domain (the swiss entry is present AND its `refcount`
is positive), then a `setSwiss` whose leaf reads the found entry and installs the declarative GC/decrement
image `dropSwissPost k.swiss sw e`. The contrast with transfer/balanceA/cellSeal is the move primitive:
`setSwiss` (rewrites the `swiss` list side-table) over the conditional remove/decrement, NOT `setCell` /
`setBal` / `setLifecycle`. -/

/-- The swissDrop KERNEL admissibility gate as a `Bool` — exactly `swissDropK`'s fail-closed GC domain:
the swiss entry `sw` is PRESENT (`findSwiss` is `some e`) AND its `refcount` is POSITIVE (`0 < e.refcount`,
i.e. NOT already zero). When the entry is absent OR the refcount is already `0`, the gate is `false` and
the term rejects (`none`), matching `swissDropK` exactly. The AUTH leg (`stateAuthB`) is NOT here — it is
the chained wrapper's gate, re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
def dropKGuard (sw : Nat) (k : RecordKernelState) : Bool :=
  match findSwiss k.swiss sw with
  | some e => decide (0 < e.refcount)
  | none   => false

/-- The swissDrop `setSwiss` leaf — the post-`swiss` list `swissDropK` installs on a committed drop. On a
present entry it is the declarative GC/decrement image `dropSwissPost k.swiss sw e` (remove if refcount
hits 0, else replace with `refcount-1`); off the membership domain (absent entry) it is the identity
(`k.swiss`), which never fires because the guard rejects there. The genuine `setSwiss` payload — NOT a
no-op. -/
def dropSwissLeaf (sw : Nat) (k : RecordKernelState) : List SwissRecord :=
  match findSwiss k.swiss sw with
  | some e => dropSwissPost k.swiss sw e
  | none   => k.swiss

/-- **The swissDrop effect as an IR term: gate, then the `setSwiss` GC/decrement.** Mirrors
`transferStmt`/`balanceAStmt`/`cellSealStmt` (gate, then move) but the move is `setSwiss` over the
conditional remove/decrement of the `swiss` side-table — NOT `setCell`/`setBal`/`setLifecycle`. The
`setSwiss` leaf is `dropSwissLeaf sw k`, EXACTLY the post-`swiss` `swissDropK` installs on the kernel (the
runtime `stateAuthB` auth gate + receipt-log row are re-attached in §3). `actor`/`exporter` are carried as
IR parameters only (the chained wrapper's auth leg names them); the KERNEL step `swissDropK` does not read
them. -/
def swissDropStmt (sw : Nat) (_actor _exporter : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (dropKGuard sw))
    (RecStmt.setSwiss (fun k => dropSwissLeaf sw k))

/-! ## §2 — The cornerstone: `interp` of the swissDrop term IS the raw kernel step `swissDropK`. -/

/-- The swissDrop `Bool` gate decodes to `swissDropK`'s fail-closed GC domain (entry present ∧ refcount
positive). The analog of `transferGuard_iff`/`balanceAGuard_iff`/`cellSealGuard_iff`. -/
theorem dropKGuard_iff (sw : Nat) (k : RecordKernelState) :
    dropKGuard sw k = true ↔
      (∃ e : SwissRecord, findSwiss k.swiss sw = some e ∧ 0 < e.refcount) := by
  unfold dropKGuard
  cases hf : findSwiss k.swiss sw with
  | none   =>
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨e, he, _⟩; exact absurd he (by simp)
  | some e =>
    simp only [decide_eq_true_eq]
    constructor
    · intro hpos; exact ⟨e, rfl, hpos⟩
    · rintro ⟨e', he', hpos⟩; rw [Option.some.injEq] at he'; subst he'; exact hpos

/-- **The cornerstone (raw-kernel GC/decrement).** `interp` of the swissDrop term IS the verified RAW
kernel step `swissDropK` — the same partial function, by construction, exactly as the transfer/balanceA
cornerstones, now over the `swiss` list side-table via `setSwiss`/`dropSwissPost` (NOT the record-cell
`setCell`/`setBal` nor the `setLifecycle` of cellSeal). On the membership/positive-refcount domain the
term commits to `{ k with swiss := dropSwissPost k.swiss sw e }` — exactly the GC/decrement `swissDropK`
installs — and rejects (`none`) on exactly the same fail-closed gate (entry absent OR refcount already
zero). This is the per-effect executor-refinement for the CapTP GC family. The runtime auth gate +
receipt-log prepend are re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
theorem interp_swissDropStmt_eq_swissDropK (sw : Nat) (actor exporter : CellId) (k : RecordKernelState) :
    interp (swissDropStmt sw actor exporter) k = swissDropK k sw := by
  simp only [swissDropStmt, interp]
  by_cases hg : dropKGuard sw k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setSwiss` move installs `dropSwissLeaf sw k`,
    -- which on the found entry is `dropSwissPost k.swiss sw e`. The audited `dropSwissPost_eq_update` +
    -- `dropSwissUpdate_eq_k` bridge that to `swissDropK k sw = some { k with swiss := dropSwissPost … }`.
    obtain ⟨e, hf, hpos⟩ := (dropKGuard_iff sw k).mp hg
    rw [if_pos hg]
    simp only [Option.bind]
    -- the leaf reduces to `dropSwissPost k.swiss sw e` on the found entry.
    have hleaf : dropSwissLeaf sw k = dropSwissPost k.swiss sw e := by
      simp only [dropSwissLeaf, hf]
    rw [hleaf]
    -- `swissDropK k sw = some { k with swiss := dropSwissPost k.swiss sw e }` via the audited bridge.
    exact ((dropSwissUpdate_eq_k k sw (dropSwissPost k.swiss sw e)).mp
      (dropSwissPost_eq_update k.swiss sw e hf hpos)).symm
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; and `swissDropK k sw = none` on the SAME domain
    -- (entry absent OR refcount zero), since the guard decoded EXACTLY that domain.
    rw [if_neg hg]
    simp only [Option.bind]
    -- the negated guard says: NOT (∃ e, found ∧ 0 < refcount). Show `swissDropK k sw = none`.
    symm
    unfold swissDropK
    cases hf : findSwiss k.swiss sw with
    | none   => rfl
    | some e =>
      -- found entry ⇒ the guard would have admitted unless refcount = 0; the negated guard forces that.
      have hz : e.refcount = 0 := by
        by_contra hne
        exact hg ((dropKGuard_iff sw k).mpr ⟨e, hf, Nat.pos_of_ne_zero hne⟩)
      simp only [if_pos hz]

#assert_axioms interp_swissDropStmt_eq_swissDropK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `swissDropChainA` / `execFullA`.

The standalone swissDrop descriptor (§4) is keyed on the CHAINED executor `swissDropChainA` / `execFullA`
over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.swissDropA sw actor exporter) =
swissDropChainA s sw actor exporter`. The §2 cornerstone is over the RAW kernel step `swissDropK`. The
chained layer is exactly the §2 kernel GC/decrement PLUS two things: a `stateAuthB` auth pre-gate (the
holder's authority over the exporting cell, which `swissDropK` does NOT check) and the runtime receipt-log
prepend `dropReceipt actor exporter :: s.log`. We bridge faithfully, carrying the `stateAuthB` auth
conjunct as an explicit hypothesis and naming the receipt-row prepend EXPLICITLY in the chained post-state
(the honest kernel-vs-runtime divergence — NOT papered). -/

/-- **`interp_swissDropStmt_chained` — the IR term's RAW kernel executor, lifted to the chained
`execFullA`.** When the holder has authority over the exporting cell (`hauth :
stateAuthB s.kernel.caps actor exporter = true`, the chained layer's extra auth gate) and the §2
cornerstone commits on the kernel (`interp (swissDropStmt sw actor exporter) s.kernel = some k'`), the
unified action executor `execFullA s (.swissDropA sw actor exporter)` commits to the chained state
`⟨k', dropReceipt actor exporter :: s.log⟩`. So the Argus term's KERNEL meaning lifts to the chained
executor the standalone descriptor speaks about, with the runtime auth side-condition carried + the
runtime receipt-log row (which the kernel `interp` does not model) re-attached HERE — the explicit
kernel-vs-runtime bridge. -/
theorem interp_swissDropStmt_chained
    (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (k' : RecordKernelState)
    (hauth : stateAuthB s.kernel.caps actor exporter = true)
    (hexec : interp (swissDropStmt sw actor exporter) s.kernel = some k') :
    execFullA s (.swissDropA sw actor exporter)
      = some { kernel := k', log := dropReceipt actor exporter :: s.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `swissDropK`.
  rw [interp_swissDropStmt_eq_swissDropK] at hexec
  -- `execFullA s (.swissDropA …)` reduces to `swissDropChainA s sw actor exporter`, which on
  -- `stateAuthB` opens to a `match swissDropK …` — and `hexec` names that as `some k'`.
  show swissDropChainA s sw actor exporter = some { kernel := k', log := dropReceipt actor exporter :: s.log }
  unfold swissDropChainA
  rw [if_pos hauth, hexec]
  rfl

#assert_axioms interp_swissDropStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of swissDrop's OWN standalone full-state circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against swissDrop's GENUINE standalone descriptor `swissDropCircuit S (swissDropE …)` (the v2
`Surface2` circuit whose soundness is `swissDropA_full_sound`), NOT an EffectVM `cellProj` row — see the
descriptor note in this file's header. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and
the independent `execFullA_drop_iff_spec` (executor ⟺ `DropSpec`); the circuit side is the audited
`swissDropA_full_sound` (circuit ⟹ `DropSpec`). Both name the SAME `DropSpec`, so they PROVABLY agree on
the WHOLE post-state — the touched `swiss` side-table (GC/decrement image), the receipt-log growth, and the
16-field frame — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `swissDrop` term: swissDrop's OWN audited standalone v2
`Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (swissDropE …) (encodeE2 …)`
satisfied on the encoded `(s, ⟨sw,actor,exporter⟩, s')` triple (the `EffectRefinement` hub's
`effect2CircuitStep`, inlined here so this module imports only `Inst.swissDropA`). Its soundness
`swissDropA_full_sound` pins the complete `DropSpec`. The `swissDrop`-keyed analog of `balanceACircuit` /
`cellSealCircuit`, in the descriptor universe where swissDrop carries its OWN genuine full-state circuit
(NOT EffectVM-inherited). The whole-list digest closure `LE`/`cN` + their injectivity witnesses are passed
through verbatim (the realizable Poseidon carriers). -/
def swissDropCircuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2 S (swissDropE LE cN hN hLE) (encodeE2 S (swissDropE LE cN hN hLE) s args s')

/-- **`dropSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`DropSpec s sw actor exporter ·` are equal. Rather than re-derive this field-by-field, we route through
the PROVEN executor⟺spec corner `execFullA_drop_iff_spec`: each `DropSpec` reconstructs the SAME committed
value `execFullA s (.swissDropA sw actor exporter) = some ·`, and `some` is injective. This is exactly the
sense in which `DropSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem dropSpec_unique {s s₁ s₂ : RecChainedState} {sw : Nat} {actor exporter : CellId}
    (h₁ : DropSpec s sw actor exporter s₁) (h₂ : DropSpec s sw actor exporter s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.swissDropA sw actor exporter) = some s₁ :=
    (execFullA_drop_iff_spec s sw actor exporter s₁).mpr h₁
  have e₂ : execFullA s (.swissDropA sw actor exporter) = some s₂ :=
    (execFullA_drop_iff_spec s sw actor exporter s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`swissDrop_compile_sound` — the welded soundness (swissDrop slice), against swissDrop's OWN
descriptor.**

Suppose, for the Argus swissDrop term `swissDropStmt sw actor exporter`:
  * the standalone swissDrop circuit `swissDropCircuit S LE cN hN hLE s ⟨sw,actor,exporter⟩ s'`
    (= `swissDropE`'s full-state v2 arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-list digest portals (`hRest : RestIffNoSwiss S.RH`, `hLog : logHashInjective S.LH`,
    and the digest-injectivity witnesses `hN`/`hLE` carried inside the descriptor);
  * the IR term's RAW kernel executor interpretation COMMITS:
    `interp (swissDropStmt sw actor exporter) s.kernel = some k'` (`hexec`), with the holder authorized
    over the exporting cell (`hauth`, the chained auth side-condition).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached:
`s' = { kernel := k', log := dropReceipt actor exporter :: s.log }`. I.e. swissDrop's OWN circuit and the
IR term AGREE on the WHOLE post-state — the `swiss` side-table GC/decremented at `sw` (`dropSwissPost`),
every other RecordKernelState field frozen — AND the receipt log — the full `DropSpec`, not a per-cell
projection. The auth side-condition + receipt-log row are named EXPLICITLY (hypothesis `hauth` + the
conclusion's `log`), so the kernel-vs-runtime divergence is part of the welded statement. So the circuit
the prover runs for swissDrop pins the complete chained state the IR term's executor produces. -/
theorem swissDrop_compile_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (sw : Nat) (actor exporter : CellId) (k' : RecordKernelState)
    (hcirc : swissDropCircuit S LE cN hN hLE s ⟨sw, actor, exporter⟩ s')
    (hauth : stateAuthB s.kernel.caps actor exporter = true)
    (hexec : interp (swissDropStmt sw actor exporter) s.kernel = some k') :
    s' = { kernel := k', log := dropReceipt actor exporter :: s.log } := by
  -- circuit side: swissDrop's OWN audited soundness forces the FULL `DropSpec` on `(s, ⟨sw,actor,exporter⟩, s')`.
  have hspec : DropSpec s sw actor exporter s' :=
    swissDropA_full_sound S LE cN hN hLE hRest hLog s ⟨sw, actor, exporter⟩ s' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.swissDropA …) = some ⟨k', receipt::log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `DropSpec s sw actor exporter ⟨k', receipt::log⟩`.
  have hspec' : DropSpec s sw actor exporter { kernel := k', log := dropReceipt actor exporter :: s.log } :=
    (execFullA_drop_iff_spec s sw actor exporter _).mp
      (interp_swissDropStmt_chained s sw actor exporter k' hauth hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact dropSpec_unique hspec hspec'

#assert_axioms swissDrop_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely GCs/decrements the swiss-table (move observable), preserves
every other field (frame), and the gate REJECTS forged / out-of-domain inputs (fail-closed).

The cornerstone/weld would be hollow if swissDrop never committed, if the move were a no-op, or if the gate
admitted everything. A concrete kernel `kD0` with a real swiss entry (swiss `7`, refcount `2`) exercises a
genuine decrement; a second entry at refcount `1` exercises the GC (remove) branch; the rejection lemmas
show each fail-closed gate leg (absent entry, already-zero refcount) returns `none`. -/

/-- A concrete kernel for the §5 witnesses: cells 0,1 live; an EMPTY `bal` ledger; and a `swiss` table with
TWO entries — swiss `7` at refcount `2` (the decrement witness) and swiss `9` at refcount `1` (the GC/remove
witness). -/
def kD0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0
    swiss := [ { swiss := 7, exporter := 0, target := 1, rights := [], refcount := 2, cert := none },
               { swiss := 9, exporter := 0, target := 1, rights := [], refcount := 1, cert := none } ] }

/-- **NON-VACUITY (the DECREMENT is OBSERVABLE).** A drop on swiss `7` (refcount `2 > 1`) commits and lowers
its `refcount` from `2` to `1` — the entry STAYS (not GC'd) with the decremented count (the
`setSwiss`/`dropSwissPost` decrement is real, not a no-op). -/
theorem swissDropStmt_decrements :
    (interp (swissDropStmt 7 0 0) kD0).map (fun k => (findSwiss k.swiss 7).map (·.refcount))
      = some (some 1) := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

/-- **NON-VACUITY (the GC/REMOVE is OBSERVABLE).** A drop on swiss `9` (refcount `1`, the LAST ref) commits
and REMOVES the entry entirely — `findSwiss` for `9` is `none` afterward (the `dropSwissPost` GC/remove
branch is real). The CapTP garbage-collection at refcount-zero, observed. -/
theorem swissDropStmt_gcs_at_one :
    (interp (swissDropStmt 9 0 0) kD0).map (fun k => (findSwiss k.swiss 9).isSome) = some false := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

/-- **NON-VACUITY (the term ACTUALLY commits).** The drop of a present, positive-refcount swiss entry
COMMITS (`isSome`) — the GC-domain gate genuinely admits. (Pins that the weld's `hexec` hypothesis is
satisfiable.) -/
theorem swissDropStmt_commits :
    (interp (swissDropStmt 7 0 0) kD0).isSome = true := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT swiss entry is untouched).** Dropping swiss `7` leaves the OTHER
entry (swiss `9`) at its original `refcount 1` — `setSwiss`/`dropSwissPost` rewrites ONLY the dropped
entry, confirming the move is local (not a global swiss-table collapse). The per-entry frame, observed. -/
theorem swissDropStmt_other_entry_untouched :
    (interp (swissDropStmt 7 0 0) kD0).map (fun k => (findSwiss k.swiss 9).map (·.refcount))
      = some (some 1) := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

/-- **NON-VACUITY (frame: `bal` is untouched).** Dropping swiss `7` leaves the `(0,0)` ledger entry at `0`
— the drop is balance-NEUTRAL (`setSwiss` writes only `swiss`, never `bal`), exactly the frozen-frame leg
of `DropSpec`. No value is conjured or destroyed by a GC operation. -/
theorem swissDropStmt_bal_frozen :
    (interp (swissDropStmt 7 0 0) kD0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

/-- **NON-VACUITY (fail-closed: absent entry).** A drop on a swiss number that is NOT in the table (here
`42`) does NOT commit — the term returns `none` (the MEMBERSHIP leg of the gate fails). A non-existent
reference cannot be GC'd. -/
theorem swissDropStmt_rejects_absent :
    interp (swissDropStmt 42 0 0) kD0 = none := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

/-- **NON-VACUITY (fail-closed: already-zero refcount).** A drop on a swiss entry whose `refcount` is
ALREADY `0` does NOT commit — the term returns `none` (the POSITIVE-refcount leg of the gate fails;
"refcount is already zero"). A double-free is rejected, not silently under-flowed. -/
theorem swissDropStmt_rejects_zero_refcount :
    interp (swissDropStmt 7 0 0)
        { kD0 with swiss := [ { swiss := 7, exporter := 0, target := 1, rights := [],
                                refcount := 0, cert := none } ] } = none := by
  rw [interp_swissDropStmt_eq_swissDropK]
  decide

#assert_axioms swissDropStmt_decrements
#assert_axioms swissDropStmt_gcs_at_one
#assert_axioms swissDropStmt_commits
#assert_axioms swissDropStmt_other_entry_untouched
#assert_axioms swissDropStmt_bal_frozen
#assert_axioms swissDropStmt_rejects_absent
#assert_axioms swissDropStmt_rejects_zero_refcount

end Dregg2.Circuit.Argus.Effects.SwissDrop
