/-
# Dregg2.Circuit.Argus.Effects.SwissExport — the CapTP sturdy-ref MINT effect `exportSturdyRefA`
  (swiss/sturdyref EXPORT) welded into the Argus IR, in its OWN disjoint module (the per-effect-farm
  vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` welded the per-asset ledger primitive
against its OWN standalone v2 `Surface2` descriptor (the FULL 17-field `*_full_sound` surface), and
`Effects/NoteCreate.lean` welded the grow-only `commitments` LIST side-table primitive the SAME way.
This module welds the CapTP sturdy-ref MINT `exportSturdyRefA` — the swiss-table EXPORT arm — against
its OWN audited v2 `Surface2` descriptor (`Inst/swissExportA.lean`'s `swissExportA_full_sound`), the
strongest surface this effect genuinely supports.

`exportSturdyRefA sw actor exporter target rights` MINTS a fresh sturdy ref: it GROWS the swiss-table
LIST side-table `kernel.swiss` (`List SwissRecord`) by a fresh `SwissRecord` (keyed by swiss number
`sw`, minted by `exporter`, pointing at `target`, carrying the exported `rights`, `refcount := 1`, no
bound cert), prepends an authority receipt to the log, and FREEZES the 16 non-`swiss` kernel fields. So
it is a SINGLE-component effect whose touched component is the `swiss` list — exactly the `listComponent`
shape `noteCreate` (`commitments`) exercises, only over `swiss` with element type `SwissRecord`. The §A
component-write primitive for that component is `setSwiss g` (`Stmt.lean:62`/`:105`):
`interp (setSwiss g) k = some { k with swiss := g k }`. No new IR constructor is needed.

UNLIKE `noteCreate` (which is unconditional), `exportSturdyRefA` is GATED. The gate splits across the two
executor layers exactly as the kernel layering demands:

  * `swissExportK k sw exporter target rights` (`RecordKernel.lean:2707`) — the RAW-kernel step — checks
    TWO conjuncts: FRESHNESS (`findSwiss k.swiss sw = none`, no duplicate export) and NON-AMPLIFICATION
    (`rightsNarrowerOrEqual rights (heldAuths k exporter)`, the exported `rights` are `⊆` the rights the
    exporter GENUINELY holds, read off the ADVERSARY-UNCONTROLLABLE committed c-list — NOT a caller bound).
    It is `match findSwiss … | some _ => none | none => if <non-amp> then some {k with swiss := …} else none`.
  * `swissExportChainA s …` (`TurnExecutorFull.lean:2803`) — the CHAINED layer — adds the THIRD conjunct
    AUTHORITY (`stateAuthB s.kernel.caps actor exporter`, the actor holds authority over the exporting
    cell) as a pre-gate AND prepends the authority receipt to the log.

So the cornerstone (§2) captures `swissExportK` EXACTLY (the freshness + non-amplification gate, then the
`setSwiss` prepend), and the chained lift (§3) carries the `stateAuthB` AUTHORITY conjunct as an explicit
hypothesis — the honest chained-vs-raw contrast, NOT papered (precisely the role `acceptsEffects` plays in
BalanceA's chained lift).

## THE DESCRIPTOR SURFACE (the most load-bearing finding — read this).

`exportSturdyRefA` carries TWO circuit universes, and the choice of which to weld against is load-bearing:

  * The EFFECTVM per-row descriptor (`Emit/EffectVmEmitSwissExport.lean`, `swissExportVmDescriptor`) models
    the export as a `sturdyref_root` MOVE on a dedicated root column. That module's OWN header REPORTS that
    `swissExportA`'s universe-A spec GROWS the swiss list (moving the sturdyref root) while the LIVE runtime
    `EXPORT_STURDY_REF=14` selector is counter-only — a precisely-flagged IR-blocked guard/list-structure
    reconciliation (it does NOT carry the full 17-field declarative post-state).

  * The v2 `Surface2` / `EffectCommit2` descriptor (`Inst/swissExportA.lean`) is the GENUINE standalone
    full-state crown jewel: `swissExportE` (the `EffectSpec2` whose touched component is the WHOLE `swiss`
    list via a `listComponent` FULL-list digest — `ListDigestBindsList`, so a drop/reorder of an EXISTING
    sturdy ref is REJECTED, not just "grew by the new record") and
    `swissExportA_full_sound : satisfiedE2 … (swissExportE …) … ⟹ ExportSpec` — a FULL 17-field declarative
    post-state soundness, balance-NEUTRAL, keyed on the CHAINED executor `execFullA`/`swissExportChainA`
    via the independent `Spec.SwissExport.export_iff_spec` (`Spec/swissexport.lean`). It carries the
    3-conjunct `ExportGuard` (AUTHORITY ∧ FRESHNESS ∧ NON-AMPLIFICATION) and shares the executor's
    balance-neutral convention, so it AGREES with the IR term's executor on the WHOLE state with NO
    divergence.

So this module welds against the v2 `Surface2` descriptor (the BalanceA/NoteCreate surface) — strictly
stronger than a per-cell EffectVM weld AND divergence-free, because that descriptor binds the whole-state
full-list digest, carries the genuine 3-conjunct CapTP gate, and shares the executor's balance-neutral
convention.

This module is therefore HONEST in both directions:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_swissExportStmt_eq_swissExportK`
      — the RAW-kernel step `swissExportK` IS the Argus term, using `guard` (freshness ∧ non-amplification)
      then `setSwiss` (the list-side-table prepend). New, standalone, the swiss-export analog of
      `interp_noteCreateStmt_eq_noteCreateCommitment` (now GATED).

  (2) **Compile weld against swissExport's OWN standalone v2 `Surface2` descriptor:** lift the cornerstone
      to the chained executor (`interp_swissExportStmt_chained`, carrying the `stateAuthB` AUTHORITY
      side-condition), then weld to the standalone `swissExportCircuit`/`swissExportA_full_sound`. The
      conclusion is the FULL `ExportSpec` agreement (all 17 kernel fields + the receipt log + the 3-conjunct
      guard) — a satisfying witness of swissExport's own circuit agrees with the WHOLE post-state the IR
      term's executor produces. Strictly stronger than a per-cell weld, because swissExport's standalone
      descriptor carries the whole-state full-list digest.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
whole-list-digest assumption enters ONLY inside the reused `swissExportA_full_sound` (its
`compressNInjective`/`listLeafInjective`/`logHashInjective`/`RestIffNoSwiss` portal hypotheses), not in
the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. The chained-vs-raw
AUTHORITY gap is carried as an EXPLICIT hypothesis (`haccess`), not papered. Imports are read-only; this
file OWNS only its own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.swissExportA

namespace Dregg2.Circuit.Argus.Effects.SwissExport

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/swissExportA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective`/`compressNInjective`/`listLeafInjective` live in `StateCommit`/`ListCommit`;
-- `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`. (`effect2CircuitStep` is the `EffectRefinement`
-- hub abbrev for exactly `satisfiedE2 S E (encodeE2 S E …)`; we inline it here to keep this module's
-- v2-import surface to `Inst.swissExportA`.)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.SwissExport
  (ExportSpec ExportGuard exportRecord exportReceipt export_iff_spec)
open Dregg2.Circuit.Inst.SwissExportA
  (ExportArgs swissExportE swissExportA_full_sound RestIffNoSwiss)
open Dregg2.Authority (Auth)

/-! ## §1 — The swissExport effect as an Argus IR term (the kernel-step gate, then the `setSwiss` prepend).

`swissExportK k sw exporter target rights` (`RecordKernel.lean:2707`) is

    match findSwiss k.swiss sw with
    | some _ => none
    | none   => if rightsNarrowerOrEqual rights (heldAuths k exporter)
                then some { k with swiss := exportRecord sw exporter target rights :: k.swiss } else none

i.e. fail-closed on a duplicate swiss number (FRESHNESS) OR an amplifying export (NON-AMPLIFICATION), and
on commit PREPENDS the fresh `SwissRecord` onto the `swiss` list. We capture it term-for-term: a `Bool`
`guard` of the EXACT two raw-kernel conjuncts (FRESHNESS ∧ NON-AMPLIFICATION), then a `setSwiss` whose
leaf prepends `exportRecord …` onto `k.swiss`. The §A `setSwiss` primitive (`Stmt.lean:62`/`:105`) writes
EXACTLY the `swiss` component (`swiss := g k`) and nothing else — the genuine list-side-table write a
swiss-export effect assembles, NO new constructor needed. (The third — AUTHORITY — conjunct lives in the
CHAINED layer, carried in §3.) -/

/-- The RAW-kernel swissExport admissibility gate as a `Bool` — exactly `swissExportK`'s two checks:
FRESHNESS (`findSwiss k.swiss sw = none`, the swiss number is not already in use) and NON-AMPLIFICATION
(`rightsNarrowerOrEqual rights (heldAuths k exporter)`, the exported `rights` are `⊆` the exporter's REAL
committed rights, read off the ADVERSARY-UNCONTROLLABLE c-list). This is the raw-kernel gate; the chained
`swissExportChainA` adds the AUTHORITY conjunct `stateAuthB actor exporter` on top (carried in §3). -/
def swissExportGuard (sw : Nat) (exporter : CellId) (rights : List Auth) (k : RecordKernelState) : Bool :=
  decide (findSwiss k.swiss sw = none)
    && rightsNarrowerOrEqual rights (heldAuths k exporter)

/-- **The swissExport effect as an IR term: gate, then the `setSwiss` list-side-table prepend.** Mirrors
`createEscrowStmt` (gate, then a component write) but the move is the LIST side-table write `setSwiss`
over a cons of the freshly-minted `exportRecord` — NOT `setCell`/`setBal` (cell/ledger moves). The
`setSwiss` leaf is `fun k => exportRecord sw exporter target rights :: k.swiss`, EXACTLY the post-`swiss`
list `swissExportK` installs. The guard is the raw-kernel FRESHNESS ∧ NON-AMPLIFICATION conjunction. -/
def swissExportStmt (sw : Nat) (exporter target : CellId) (rights : List Auth) : RecStmt :=
  RecStmt.seq (RecStmt.guard (swissExportGuard sw exporter rights))
    (RecStmt.setSwiss (fun k => exportRecord sw exporter target rights :: k.swiss))

/-! ## §2 — The cornerstone: `interp` of the swissExport term IS the kernel step `swissExportK`. -/

/-- The swissExport `Bool` gate decodes to `swissExportK`'s two raw-kernel admissibility conjuncts (in the
SAME order the kernel checks them: FRESHNESS then NON-AMPLIFICATION). The swiss-export analog of
`createEscrowGuard_iff`. -/
theorem swissExportGuard_iff (sw : Nat) (exporter : CellId) (rights : List Auth) (k : RecordKernelState) :
    swissExportGuard sw exporter rights k = true ↔
      (findSwiss k.swiss sw = none
        ∧ rightsNarrowerOrEqual rights (heldAuths k exporter) = true) := by
  simp only [swissExportGuard, Bool.and_eq_true, decide_eq_true_eq]

/-- **The cornerstone (swiss-table EXPORT, list side-table, GATED).** `interp` of the swissExport term IS
the verified RAW-kernel step `swissExportK` — the same partial function, by construction, exactly as the
transfer/noteCreate cornerstones, now over the `swiss` list side-table via `setSwiss`/a cons under the
freshness ∧ non-amplification gate (NOT the record-cell `setCell`/`recTransfer` nor the ledger `setBal`).
This is the swiss-export executor-refinement: the executor IS the meaning of the term.

The `swissExportK` body is a `match findSwiss … | some _ => none | none => if <non-amp> …`; the IR term's
`guard` decodes (via `swissExportGuard_iff`) to `findSwiss … = none ∧ <non-amp>`, so the two coincide:
on a duplicate swiss number the guard is FALSE (the `decide (findSwiss = none)` conjunct fails) ⇒ both are
`none`; on a fresh number the guard reduces to `<non-amp>` and the `setSwiss` prepend matches the kernel's
`some { k with swiss := … }`. -/
theorem interp_swissExportStmt_eq_swissExportK (sw : Nat) (exporter target : CellId) (rights : List Auth)
    (k : RecordKernelState) :
    interp (swissExportStmt sw exporter target rights) k = swissExportK k sw exporter target rights := by
  simp only [swissExportStmt, interp]
  unfold swissExportK
  -- split on the FRESHNESS lookup, mirroring the kernel `match`.
  cases hf : findSwiss k.swiss sw with
  | some e =>
    -- duplicate swiss number ⇒ the guard's FRESHNESS conjunct is false ⇒ `interp guard = none` ⇒
    -- `none.bind _ = none`; the kernel `match` arm is `none`.
    have hg : swissExportGuard sw exporter rights k = false := by
      simp only [swissExportGuard, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (by rw [hf]; simp)
    rw [hg]; simp only [Bool.false_eq_true, if_false, Option.bind]
  | none =>
    -- fresh swiss number ⇒ the guard reduces to NON-AMPLIFICATION; split on it.
    by_cases hr : rightsNarrowerOrEqual rights (heldAuths k exporter) = true
    · have hg : swissExportGuard sw exporter rights k = true :=
        (swissExportGuard_iff sw exporter rights k).mpr ⟨hf, hr⟩
      rw [hg]; simp only [if_true, Option.bind, if_pos hr, exportRecord]
    · have hg : swissExportGuard sw exporter rights k = false := by
        simp only [swissExportGuard, Bool.and_eq_false_iff]
        exact Or.inr (by simpa using hr)
      rw [hg]; simp only [Bool.false_eq_true, if_false, Option.bind, if_neg hr]

#assert_axioms interp_swissExportStmt_eq_swissExportK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `swissExportChainA` / `execFullA`.

The standalone swissExport descriptor (§4) is keyed on the CHAINED executor `execFullA`/`swissExportChainA`
over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.exportSturdyRefA sw actor exporter
target rights) = swissExportChainA s sw actor exporter target rights` (`TurnExecutorFull.lean:3887`). The §2
cornerstone is over the RAW-kernel step `swissExportK`. The chained layer is exactly `swissExportK` PLUS two
things: the AUTHORITY pre-gate `stateAuthB s.kernel.caps actor exporter` (the actor holds authority over the
exporting cell — the THIRD `ExportGuard` conjunct, absent from the raw kernel step) and the receipt-log
prepend `exportReceipt actor exporter :: s.log`. We bridge faithfully, carrying the AUTHORITY conjunct as an
explicit hypothesis (the honest chained-vs-raw contrast — NOT papered, exactly as BalanceA carries
`acceptsEffects`). -/

/-- **`interp_swissExportStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the actor holds authority over the exporting cell (`stateAuthB s.kernel.caps actor exporter = true`, the
chained layer's extra AUTHORITY gate) and the §2 cornerstone commits on the kernel
(`interp (swissExportStmt sw exporter target rights) st.kernel = some k'`), the unified action executor
`execFullA st (.exportSturdyRefA sw actor exporter target rights)` commits to the chained state
`⟨k', exportReceipt actor exporter :: st.log⟩`. So the Argus term's kernel meaning lifts to the chained
executor the standalone descriptor speaks about, modulo the carried AUTHORITY side-condition. -/
theorem interp_swissExportStmt_chained
    (st : RecChainedState) (sw : Nat) (actor exporter target : CellId) (rights : List Auth)
    (k' : RecordKernelState)
    (haccess : stateAuthB st.kernel.caps actor exporter = true)
    (hexec : interp (swissExportStmt sw exporter target rights) st.kernel = some k') :
    execFullA st (.exportSturdyRefA sw actor exporter target rights)
      = some { kernel := k', log := exportReceipt actor exporter :: st.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `swissExportK`.
  rw [interp_swissExportStmt_eq_swissExportK] at hexec
  -- `execFullA st (.exportSturdyRefA …)` reduces to `swissExportChainA st …`, which on `stateAuthB` opens
  -- to a `match swissExportK …` — and `hexec` names that as `some k'`.
  show swissExportChainA st sw actor exporter target rights
    = some { kernel := k', log := exportReceipt actor exporter :: st.log }
  unfold swissExportChainA exportReceipt
  rw [if_pos haccess, hexec]

#assert_axioms interp_swissExportStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of swissExport's OWN standalone v2 `Surface2` circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against swissExport's GENUINE standalone descriptor `swissExportCircuit S … (swissExportE …)`
(the v2 `Surface2` circuit whose soundness is `swissExportA_full_sound`), NOT the EffectVM `sturdyref_root`
descriptor — see the descriptor surface investigation in this file's header. The executor side is routed
through §3 (`interp` ⟹ `execFullA`, modulo AUTHORITY) and the independent `export_iff_spec` (executor ⟺
`ExportSpec`); the circuit side is the audited `swissExportA_full_sound` (circuit ⟹ `ExportSpec`). Both name
the SAME `ExportSpec`, so they PROVABLY agree on the WHOLE 17-field state + the log + the 3-conjunct guard —
strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `swissExport` term: swissExport's OWN audited standalone v2
`Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (swissExportE LE cN hN hLE)
(encodeE2 …)` satisfied on the encoded `(st, ⟨sw, actor, exporter, target, rights⟩, st')` triple
(DEFINITIONALLY the `EffectRefinement` hub's `effect2CircuitStep S (swissExportE …) st args st'`, inlined
here so this module's v2-import surface is only `Inst.swissExportA`). Its soundness
`swissExportA_full_sound` pins the complete `ExportSpec`. The `swissExport`-keyed analog of
`noteCreateCircuit`, in the descriptor universe where swissExport carries its OWN genuine full-state
circuit (NOT EffectVM-inherited). -/
def swissExportCircuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (st : RecChainedState) (args : ExportArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (swissExportE LE cN hN hLE)
    (encodeE2 S (swissExportE LE cN hN hLE) st args st')

/-- **`exportSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`ExportSpec st sw actor exporter target rights ·` are equal. Rather than re-derive this field-by-field, we
route through the PROVEN executor⟺spec corner `export_iff_spec`: each `ExportSpec` reconstructs the SAME
committed value `execFullA st (.exportSturdyRefA …) = some ·`, and `some` is injective. This is exactly the
sense in which `ExportSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state (the BalanceA/NoteCreate `*_unique` analog). -/
theorem exportSpec_unique {st st₁ st₂ : RecChainedState} {sw : Nat} {actor exporter target : CellId}
    {rights : List Auth}
    (h₁ : ExportSpec st sw actor exporter target rights st₁)
    (h₂ : ExportSpec st sw actor exporter target rights st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.exportSturdyRefA sw actor exporter target rights) = some st₁ :=
    (export_iff_spec st sw actor exporter target rights st₁).mpr h₁
  have e₂ : execFullA st (.exportSturdyRefA sw actor exporter target rights) = some st₂ :=
    (export_iff_spec st sw actor exporter target rights st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`swissExport_compile_sound` — the welded soundness (swissExport slice), against swissExport's OWN descriptor.**

Suppose, for the Argus swissExport term `swissExportStmt sw exporter target rights`:
  * the standalone swissExport circuit `swissExportCircuit S LE cN hN hLE st ⟨sw, actor, exporter, target,
    rights⟩ st'` (= `swissExportE`'s full-state v2 arithmetization satisfied on the encoded triple) holds,
    under the realizable whole-list-digest portals (`hRest : RestIffNoSwiss S.RH`, `hLog : logHashInjective
    S.LH`, `hN : compressNInjective cN`, `hLE : listLeafInjective LE`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (swissExportStmt sw exporter target rights) st.kernel = some k'` (`hexec`), with the actor
    holding authority over the exporting cell (`haccess`, the chained AUTHORITY side-condition).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := exportReceipt actor exporter :: st.log }`. I.e. swissExport's OWN
circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (`swiss` prepended with the fresh
sturdy ref, every other field — INCLUDING `bal`, balance-NEUTRAL — frozen) AND the receipt log AND the
3-conjunct guard — the full `ExportSpec`, not a per-cell projection. So the circuit the prover runs for
swissExport pins the complete state the IR term's executor produces.

The honest chained-vs-raw AUTHORITY gap is carried as the explicit `haccess` hypothesis (NOT papered): the
RAW-kernel `swissExportK` the cornerstone captures gates only on FRESHNESS ∧ NON-AMPLIFICATION, while the
CHAINED executor the descriptor speaks about adds the AUTHORITY conjunct. NO nonce-tick / collapsed-field
divergence enters this surface (the v2 descriptor is balance-neutral, matching the executor). -/
theorem swissExport_compile_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (sw : Nat) (actor exporter target : CellId) (rights : List Auth)
    (k' : RecordKernelState)
    (hcirc : swissExportCircuit S LE cN hN hLE st ⟨sw, actor, exporter, target, rights⟩ st')
    (haccess : stateAuthB st.kernel.caps actor exporter = true)
    (hexec : interp (swissExportStmt sw exporter target rights) st.kernel = some k') :
    st' = { kernel := k', log := exportReceipt actor exporter :: st.log } := by
  -- circuit side: swissExport's OWN audited soundness forces the FULL `ExportSpec` on
  -- `(st, ⟨sw,actor,exporter,target,rights⟩, st')`.
  have hspec : ExportSpec st sw actor exporter target rights st' :=
    swissExportA_full_sound S LE cN hN hLE hRest hLog st ⟨sw, actor, exporter, target, rights⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.exportSturdyRefA …) = some ⟨k', receipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `ExportSpec st … ⟨k', receipt :: log⟩`.
  have hspec' : ExportSpec st sw actor exporter target rights
      { kernel := k', log := exportReceipt actor exporter :: st.log } :=
    (export_iff_spec st sw actor exporter target rights _).mp
      (interp_swissExportStmt_chained st sw actor exporter target rights k' haccess hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact exportSpec_unique hspec hspec'

#assert_axioms swissExport_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely GROWS the swiss table (insert observable, the new sturdy ref
is the LIVE entry), is balance-NEUTRAL, and the gate REJECTS forged inputs (fail-closed on a DUPLICATE swiss
number AND on an AMPLIFYING export).

The cornerstone/weld would be hollow if swissExport never committed, if the insert were a no-op, if it
touched `bal`, or if the gate admitted everything. A concrete two-account kernel exercises a real mint; the
rejection lemmas show each raw-kernel guard conjunct fails closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts, cell 0 holds 30 of asset 0 on the
genuine per-asset ledger `bal`, an EMPTY swiss table (so any fresh export is admissible), and an EMPTY c-list
(so `heldAuths k 0 = []` and the non-amplification gate admits ONLY the empty rights list). -/
def kS0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 30 else 0 }

/-- **NON-VACUITY (the EXPORT is OBSERVABLE).** The committed export GROWS the swiss table from `[]` to
length `1` — the fresh sturdy ref genuinely lands in the table (the `setSwiss`/cons insert is real, not a
no-op). The empty exported rights `[]` keep the non-amplification gate (`[] ⊆ heldAuths`) trivially
satisfied so the commit fires on `kS0`'s empty c-list. -/
theorem swissExportStmt_inserts :
    (interp (swissExportStmt 7 0 1 []) kS0).map (fun k => k.swiss.length) = some 1 := by
  rw [interp_swissExportStmt_eq_swissExportK]
  decide

/-- **NON-VACUITY (the minted sturdy ref is the LIVE entry).** After the export, `findSwiss` returns the
fresh `exportRecord` for swiss number `7` (keyed `7`, target `1`, rights `[]`, `refcount = 1`, no cert) —
the load-bearing fact a later enliven/handoff/drop reads. The insert is the genuine CapTP MINT, not a stub. -/
theorem swissExportStmt_minted_entry :
    (interp (swissExportStmt 7 0 1 []) kS0).bind (fun k => findSwiss k.swiss 7)
      = some (exportRecord 7 0 1 []) := by
  rw [interp_swissExportStmt_eq_swissExportK]
  decide

/-- **NON-VACUITY (BALANCE NEUTRALITY — the CapTP punchline).** The committed export leaves the per-asset
ledger entry `(0, 0)` UNTOUCHED at `30` — a swiss export moves a REFERENCE, NOT balance (it grows only
`swiss`, never `bal`). The load-bearing distinction from a value-moving effect, proved on the term. -/
theorem swissExportStmt_bal_neutral :
    (interp (swissExportStmt 7 0 1 []) kS0).map (fun k => k.bal 0 0) = some 30 := by
  rw [interp_swissExportStmt_eq_swissExportK]
  decide

/-- **NON-VACUITY (fail-closed: DUPLICATE swiss number / FRESHNESS).** Exporting a swiss number `7` that is
ALREADY in use (here the post-state of a first export of `7`) does NOT commit — the term returns `none` (the
FRESHNESS conjunct of the gate fails). The swiss number space is collision-free by construction; no duplicate
export. -/
theorem swissExportStmt_rejects_duplicate :
    (interp (swissExportStmt 7 0 1 []) kS0).bind (interp (swissExportStmt 7 0 1 [])) = none := by
  simp only [interp_swissExportStmt_eq_swissExportK]
  decide

/-- **NON-VACUITY (fail-closed: AMPLIFYING export / NON-AMPLIFICATION).** Exporting a sturdy ref carrying
rights `[Auth.read]` the exporter does NOT genuinely hold (cell `0`'s c-list is EMPTY on `kS0`, so
`heldAuths kS0 0 = []` and `[Auth.read] ⊄ []`) does NOT commit — the term returns `none` (the
NON-AMPLIFICATION conjunct fails). A bare-authority actor cannot mint a sturdy ref carrying rights its cell
never held: the capability-amplification hole is closed, in the IR. -/
theorem swissExportStmt_rejects_amplifying :
    interp (swissExportStmt 7 0 1 [Auth.read]) kS0 = none := by
  rw [interp_swissExportStmt_eq_swissExportK]
  decide

#assert_axioms swissExportStmt_inserts
#assert_axioms swissExportStmt_minted_entry
#assert_axioms swissExportStmt_bal_neutral
#assert_axioms swissExportStmt_rejects_duplicate
#assert_axioms swissExportStmt_rejects_amplifying

end Dregg2.Circuit.Argus.Effects.SwissExport
