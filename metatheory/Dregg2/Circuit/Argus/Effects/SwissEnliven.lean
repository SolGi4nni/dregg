/-
# Dregg2.Circuit.Argus.Effects.SwissEnliven — the CapTP sturdy-ref ENLIVEN effect `enlivenRefA`
  (swiss/sturdyref ENLIVEN) welded into the Argus IR, in its OWN disjoint module (the per-effect-farm
  vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` welded the per-asset ledger primitive
against its OWN standalone v2 `Surface2` descriptor (the FULL 17-field `*_full_sound` surface), and the
sibling `Effects/SwissExport.lean` welded the swiss-table EXPORT (MINT) the SAME way (the `swiss` LIST
side-table via `setSwiss`, gated). This module welds the CapTP sturdy-ref ENLIVEN `enlivenRefA` — the
swiss-table ENLIVEN arm — against its OWN audited v2 `Surface2` descriptor (`Inst/enlivenRefA.lean`'s
`enlivenRefA_full_sound`), the strongest surface this effect genuinely supports.

`enlivenRefA sw actor exporter claimed` VALIDATES a presented swiss number `sw` against the committed
swiss-table, checks NON-AMPLIFICATION of the bearer's `claimed` rights against the entry's exported
`rights`, and on success BUMPS that entry's GC `refcount` (a new live reference) via `replaceSwiss`. So
it is a SINGLE-component effect whose touched component is the `swiss` LIST side-table — exactly the
`listComponent` shape `swissExport` exercises, only the move is a `replaceSwiss` refcount-BUMP (in
place), NOT a `cons` (prepend). The §A component-write primitive for that component is `setSwiss g`
(`Stmt.lean:62`/`:105`): `interp (setSwiss g) k = some { k with swiss := g k }`. No new IR constructor
is needed; the only structural contrast with EXPORT is the leaf (an in-place bump vs a prepend) and the
gate (MEMBERSHIP — the swiss number must already be PRESENT — vs FRESHNESS).

UNLIKE the unconditional `noteCreate`, `enlivenRefA` is GATED, and — exactly as the kernel layering
demands — the gate splits across the two executor layers:

  * `swissEnlivenK k sw claimed` (`RecordKernel.lean:2721`) — the RAW-kernel step — checks TWO conjuncts:
    MEMBERSHIP (`findSwiss k.swiss sw = some e`, the swiss number IS in the committed table) and
    NON-AMPLIFICATION (`rightsNarrowerOrEqual claimed e.rights`, the bearer's `claimed` rights are `⊆`
    the EXPORTED rights of the FOUND entry — a sturdy ref must NOT grant authority the export did not
    hold). It is `match findSwiss … | none => none | some e => if <non-amp> then some {k with swiss :=
    replaceSwiss …(e.refcount+1)} else none`. Fail-closed on an ABSENT swiss number OR an amplifying
    enliven.
  * `swissEnlivenChainA s …` (`TurnExecutorFull.lean:2813`) — the CHAINED layer — adds the THIRD conjunct
    AUTHORITY (`stateAuthB s.kernel.caps actor exporter`, the actor holds authority over the exporting
    cell) as a pre-gate AND prepends the authority receipt (`enlivenReceipt actor exporter`) to the log.

So the cornerstone (§2) captures `swissEnlivenK` EXACTLY (the membership + non-amplification gate, then
the `setSwiss` refcount-bump), and the chained lift (§3) carries the `stateAuthB` AUTHORITY conjunct as
an explicit hypothesis — the honest chained-vs-raw contrast, NOT papered (precisely the role `haccess`
plays in SwissExport's chained lift, and `acceptsEffects` in BalanceA's).

## THE GUARD/LEAF ENCODING (the load-bearing structural finding — read this).

`swissEnlivenK`'s NON-AMPLIFICATION conjunct references `e.rights`, where `e` is the entry BOUND by the
`findSwiss` match — there is no caller-supplied `e` to pin in a `decide`-style `Bool` guard the way
`swissExport` pins FRESHNESS (`decide (findSwiss = none)`). So this effect's faithful Argus encoding
routes BOTH legs through the already-audited combinator `enlivenSwissUpdate k.swiss sw claimed`
(`Spec/swissenliven.lean:23`):

    enlivenSwissUpdate ss sw claimed =
      match findSwiss ss sw with
      | none   => none
      | some e => if rightsNarrowerOrEqual claimed e.rights then some (enlivenSwissPost ss sw e) else none

which IS the swiss-list post-image of `swissEnlivenK` (the verified bridge `enlivenSwissUpdate_eq_k` says
`enlivenSwissUpdate k.swiss sw claimed = some ss ↔ swissEnlivenK k sw claimed = some { k with swiss := ss }`).
The Argus term is therefore `seq (guard <isSome>) (setSwiss <getD>)`:

  * the `guard` is the `Bool` `(enlivenSwissUpdate k.swiss sw claimed).isSome` — TRUE iff the membership
    AND non-amplification conjuncts BOTH hold (it fails closed on an absent swiss number OR an amplifying
    enliven, decoding to EXACTLY the two raw-kernel conjuncts, see `enlivenStmtGuard_iff`);
  * the `setSwiss` leaf is `(enlivenSwissUpdate k.swiss sw claimed).getD k.swiss` — the bumped swiss list
    on commit (an in-place `replaceSwiss` refcount-bump), the original list on the (unreached) reject
    branch.

`interp (seq (guard …) (setSwiss …)) k` is then DEFINITIONALLY `swissEnlivenK k sw claimed`: on a
committing `enlivenSwissUpdate = some ss` the guard admits and `setSwiss` installs `{k with swiss := ss}`;
on `enlivenSwissUpdate = none` the guard rejects and the bind short-circuits to `none` — matching the
kernel `match` arm-for-arm. This is HONEST — the guard genuinely carries both conjuncts, and the leaf is
the genuine refcount-bumped list, NOT a placeholder.

## THE DESCRIPTOR SURFACE (the strongest surface — read this).

`enlivenRefA` carries its GENUINE standalone full-state crown jewel in the v2 `Surface2` / `EffectCommit2`
universe (`Inst/enlivenRefA.lean`): `enlivenE` (the `EffectSpec2` whose touched component is the WHOLE
`swiss` list via a `listComponent` FULL-list digest — so a drop/reorder of an EXISTING sturdy ref is
REJECTED, not just "the target entry was bumped") and
`enlivenRefA_full_sound : satisfiedE2 … (enlivenE …) … ⟹ EnlivenSpec` — a FULL 17-field declarative
post-state soundness, balance-NEUTRAL, keyed on the CHAINED executor `execFullA`/`swissEnlivenChainA` via
the independent `Spec.SwissEnliven.execFullA_enliven_iff_spec` (`Spec/swissenliven.lean`). It carries the
3-conjunct `EnlivenGuard` (AUTHORITY ∧ MEMBERSHIP ∧ NON-AMPLIFICATION) and shares the executor's
balance-neutral convention, so it AGREES with the IR term's executor on the WHOLE state with NO divergence.

So this module welds against the v2 `Surface2` descriptor (the BalanceA/SwissExport surface) — strictly
stronger than a per-cell EffectVM weld AND divergence-free, because that descriptor binds the whole-state
full-list digest, carries the genuine 3-conjunct CapTP gate, and shares the executor's balance-neutral
convention.

This module is therefore HONEST in both directions:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_enlivenStmt_eq_swissEnlivenK` — the
      RAW-kernel step `swissEnlivenK` IS the Argus term, using `guard` (membership ∧ non-amplification,
      both via `enlivenSwissUpdate`) then `setSwiss` (the list-side-table refcount-bump). New, standalone,
      the swiss-enliven analog of `interp_swissExportStmt_eq_swissExportK` (the EXPORT sibling).

  (2) **Compile weld against enliven's OWN standalone v2 `Surface2` descriptor:** lift the cornerstone to
      the chained executor (`interp_enlivenStmt_chained`, carrying the `stateAuthB` AUTHORITY
      side-condition), then weld to the standalone `enlivenCircuit`/`enlivenRefA_full_sound`. The
      conclusion is the FULL `EnlivenSpec` agreement (all 17 kernel fields + the receipt log + the
      3-conjunct guard) — a satisfying witness of enliven's own circuit agrees with the WHOLE post-state
      the IR term's executor produces. Strictly stronger than a per-cell weld, because enliven's standalone
      descriptor carries the whole-state full-list digest.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
whole-list-digest assumption enters ONLY inside the reused `enlivenRefA_full_sound` (its
`compressNInjective`/`listLeafInjective`/`logHashInjective`/`RestIffNoSwiss` portal hypotheses), not in the
welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. The chained-vs-raw AUTHORITY
gap is carried as an EXPLICIT hypothesis (`haccess`), not papered, so the `divergence` is the empty one
(the v2 descriptor is balance-neutral, matching the executor). Imports are read-only; this file OWNS only
its own declarations.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.enlivenRefA
import Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull

namespace Dregg2.Circuit.Argus.Effects.SwissEnliven

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/enlivenRefA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective`/`compressNInjective` live in `StateCommit`; `listLeafInjective` in `ListCommit`;
-- `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`. (`effect2CircuitStep` is the `EffectRefinement`
-- hub abbrev for exactly `satisfiedE2 S E (encodeE2 S E …)`; we inline it here to keep this module's
-- v2-import surface to `Inst.enlivenRefA`.)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.SwissEnliven
  (EnlivenSpec EnlivenGuard enlivenReceipt enlivenRecord enlivenSwissPost enlivenSwissUpdate
   enlivenSwissUpdate_some enlivenSwissUpdate_eq_k execFullA_enliven_iff_spec)
-- `swissEnlivenK_only_swiss` (a committed enliven edits ONLY `swiss`) lives in the shared `SwissFrame`
-- helper module, transitively imported via `Inst.enlivenRefA`; opened so the cornerstone proof can name it.
open Dregg2.Circuit.Spec.SwissFrame (swissEnlivenK_only_swiss)
open Dregg2.Circuit.Inst.EnlivenRefA
  (EnlivenArgs enlivenE enlivenRefA_full_sound RestIffNoSwiss)
open Dregg2.Authority (Auth)

/-! ## §1 — The enliven effect as an Argus IR term (the kernel-step gate, then the `setSwiss` refcount-bump).

`swissEnlivenK k sw claimed` (`RecordKernel.lean:2721`) is

    match findSwiss k.swiss sw with
    | none   => none
    | some e => if rightsNarrowerOrEqual claimed e.rights
                then some { k with swiss := replaceSwiss k.swiss sw { e with refcount := e.refcount + 1 } }
                else none

i.e. fail-closed on an ABSENT swiss number (MEMBERSHIP) OR an amplifying enliven (NON-AMPLIFICATION), and
on commit BUMPS the found entry's `refcount` in place (via `replaceSwiss`). Because the non-amplification
conjunct references the BOUND entry `e.rights`, we route BOTH legs through the audited swiss-list combinator
`enlivenSwissUpdate k.swiss sw claimed` (the verified post-image of `swissEnlivenK`, see the file header):
a `Bool` `guard` of `(enlivenSwissUpdate …).isSome` (TRUE iff MEMBERSHIP ∧ NON-AMPLIFICATION), then a
`setSwiss` whose leaf is `(enlivenSwissUpdate …).getD k.swiss` — the bumped swiss list on commit. The §A
`setSwiss` primitive (`Stmt.lean:62`/`:105`) writes EXACTLY the `swiss` component and nothing else — the
genuine list-side-table write a swiss-enliven effect assembles, NO new constructor needed. (The third —
AUTHORITY — conjunct lives in the CHAINED layer, carried in §3.) -/

/-- The RAW-kernel enliven admissibility gate as a `Bool` — the post-image combinator `enlivenSwissUpdate`
COMMITS, i.e. `(enlivenSwissUpdate k.swiss sw claimed).isSome`. This is TRUE iff BOTH raw-kernel conjuncts
hold: MEMBERSHIP (`findSwiss k.swiss sw = some e`) and NON-AMPLIFICATION (`rightsNarrowerOrEqual claimed
e.rights` of the FOUND entry). It fails closed on an absent swiss number OR an amplifying enliven (decoded in
`enlivenStmtGuard_iff`). This is the raw-kernel gate; the chained `swissEnlivenChainA` adds the AUTHORITY
conjunct `stateAuthB actor exporter` on top (carried in §3). -/
def enlivenStmtGuard (sw : Nat) (claimed : List Auth) (k : RecordKernelState) : Bool :=
  (enlivenSwissUpdate k.swiss sw claimed).isSome

/-- The committing swiss-list leaf — the bumped swiss table on commit (an in-place `replaceSwiss` refcount
bump of the found entry), the original list `k.swiss` on the (unreached, gate-rejected) `none` branch. The
`setSwiss` leaf of the enliven term; on the commit branch this IS the post-`swiss` list `swissEnlivenK`
installs. -/
def enlivenStmtLeaf (sw : Nat) (claimed : List Auth) (k : RecordKernelState) : List SwissRecord :=
  (enlivenSwissUpdate k.swiss sw claimed).getD k.swiss

/-- **The enliven effect as an IR term: gate, then the `setSwiss` list-side-table refcount-bump.** Mirrors
`swissExportStmt` (gate, then a `setSwiss` component write) but the move is the in-place `replaceSwiss`
refcount-BUMP (encoded via `enlivenSwissUpdate`) rather than a `cons` prepend — and the gate is MEMBERSHIP
(swiss number PRESENT) rather than FRESHNESS. The `setSwiss` leaf is `enlivenStmtLeaf sw claimed`, EXACTLY
the post-`swiss` list `swissEnlivenK` installs on commit. The guard is the raw-kernel MEMBERSHIP ∧
NON-AMPLIFICATION conjunction (carried jointly by `enlivenSwissUpdate.isSome`). -/
def enlivenStmt (sw : Nat) (claimed : List Auth) : RecStmt :=
  RecStmt.seq (RecStmt.guard (enlivenStmtGuard sw claimed))
    (RecStmt.setSwiss (enlivenStmtLeaf sw claimed))

/-! ## §2 — The cornerstone: `interp` of the enliven term IS the kernel step `swissEnlivenK`. -/

/-- The enliven `Bool` gate decodes to `swissEnlivenK`'s two raw-kernel admissibility conjuncts: MEMBERSHIP
(`∃ e, findSwiss k.swiss sw = some e`) ∧ NON-AMPLIFICATION (`rightsNarrowerOrEqual claimed e.rights` of that
found entry). The swiss-enliven analog of `swissExportGuard_iff` — but because the non-amp leg reads the
BOUND entry's rights, the decode is an EXISTENTIAL over the found record (exactly `EnlivenGuard`'s membership
∧ non-amp pair). The proof case-splits on the `findSwiss` lookup the combinator opens. -/
theorem enlivenStmtGuard_iff (sw : Nat) (claimed : List Auth) (k : RecordKernelState) :
    enlivenStmtGuard sw claimed k = true ↔
      (∃ e : SwissRecord, findSwiss k.swiss sw = some e
        ∧ rightsNarrowerOrEqual claimed e.rights = true) := by
  simp only [enlivenStmtGuard, enlivenSwissUpdate]
  cases hf : findSwiss k.swiss sw with
  | none => simp
  | some e =>
    by_cases hr : rightsNarrowerOrEqual claimed e.rights
    · simp only [if_pos hr, Option.isSome_some, true_iff]; exact ⟨e, rfl, hr⟩
    · simp only [if_neg hr, Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
      rintro e' ⟨he', hr'⟩
      rw [Option.some.inj he'] at hr; exact hr hr'

/-- **`enlivenSwissUpdate_getD_commit` — the `setSwiss` leaf IS the kernel post-`swiss` list on commit.**
When the gate admits (`enlivenSwissUpdate k.swiss sw claimed = some ss`), the leaf `enlivenStmtLeaf`
reduces to `ss` — the bumped swiss list, exactly what `swissEnlivenK` installs (via `enlivenSwissUpdate_eq_k`).
The bridge from the `Option.getD` leaf to the kernel's `{ k with swiss := ss }`. -/
theorem enlivenSwissUpdate_getD_commit (sw : Nat) (claimed : List Auth) (k : RecordKernelState)
    {ss : List SwissRecord} (h : enlivenSwissUpdate k.swiss sw claimed = some ss) :
    enlivenStmtLeaf sw claimed k = ss := by
  simp only [enlivenStmtLeaf, h, Option.getD_some]

/-- **The cornerstone (swiss-table ENLIVEN, list side-table, GATED).** `interp` of the enliven term IS the
verified RAW-kernel step `swissEnlivenK` — the same partial function, by construction, exactly as the
transfer/swissExport cornerstones, now over the `swiss` list side-table via `setSwiss` and an in-place
`replaceSwiss` refcount-bump under the MEMBERSHIP ∧ NON-AMPLIFICATION gate (NOT the record-cell
`setCell`/`recTransfer`, nor a `cons` prepend like EXPORT). This is the swiss-enliven executor-refinement:
the executor IS the meaning of the term.

The proof routes through the audited bridge `enlivenSwissUpdate_eq_k` (`enlivenSwissUpdate k.swiss sw claimed
= some ss ↔ swissEnlivenK k sw claimed = some { k with swiss := ss }`): on a committing
`enlivenSwissUpdate = some ss` the IR `guard` admits (`isSome`) and `setSwiss` installs `{k with swiss := ss}`,
matching `swissEnlivenK`; on `enlivenSwissUpdate = none` the guard rejects and the bind short-circuits to
`none`, matching the kernel's `none`/`else` arms. -/
theorem interp_enlivenStmt_eq_swissEnlivenK (sw : Nat) (claimed : List Auth) (k : RecordKernelState) :
    interp (enlivenStmt sw claimed) k = swissEnlivenK k sw claimed := by
  simp only [enlivenStmt, interp]
  -- split on whether the audited post-image combinator commits, mirroring `swissEnlivenK`'s `match`.
  cases hu : enlivenSwissUpdate k.swiss sw claimed with
  | none =>
    -- gate rejects (`isSome = false`) ⇒ `none.bind _ = none`; and `enlivenSwissUpdate = none`
    -- ⟺ `swissEnlivenK = none` (the bridge: a `some` post-image would witness a `some` kernel step).
    have hg : enlivenStmtGuard sw claimed k = false := by simp [enlivenStmtGuard, hu]
    rw [hg]
    simp only [Bool.false_eq_true, if_false, Option.bind]
    -- `swissEnlivenK k sw claimed = none`: if it were `some k'`, the bridge forces `enlivenSwissUpdate = some _`.
    cases hk : swissEnlivenK k sw claimed with
    | none => rfl
    | some k' =>
      have hk' : k' = { k with swiss := k'.swiss } := by
        have := swissEnlivenK_only_swiss hk; exact this
      have : enlivenSwissUpdate k.swiss sw claimed = some k'.swiss :=
        (enlivenSwissUpdate_eq_k k sw claimed k'.swiss).mpr (hk.trans (congr_arg some hk'))
      rw [hu] at this; exact absurd this (by simp)
  | some ss =>
    -- gate admits (`isSome = true`) ⇒ `some k` then `setSwiss` installs `{ k with swiss := ss }`;
    -- and the bridge turns `enlivenSwissUpdate = some ss` into `swissEnlivenK = some { k with swiss := ss }`.
    have hg : enlivenStmtGuard sw claimed k = true := by simp [enlivenStmtGuard, hu]
    rw [hg]
    simp only [if_true, Option.bind]
    rw [enlivenSwissUpdate_getD_commit sw claimed k hu]
    exact ((enlivenSwissUpdate_eq_k k sw claimed ss).mp hu).symm

#assert_axioms interp_enlivenStmt_eq_swissEnlivenK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `swissEnlivenChainA` / `execFullA`.

The standalone enliven descriptor (§4) is keyed on the CHAINED executor `execFullA`/`swissEnlivenChainA`
over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.enlivenRefA sw actor exporter claimed)
= swissEnlivenChainA s sw actor exporter claimed` (`TurnExecutorFull.lean:3888`). The §2 cornerstone is over
the RAW-kernel step `swissEnlivenK`. The chained layer is exactly `swissEnlivenK` PLUS two things: the
AUTHORITY pre-gate `stateAuthB s.kernel.caps actor exporter` (the actor holds authority over the exporting
cell — the THIRD `EnlivenGuard` conjunct, absent from the raw kernel step) and the receipt-log prepend
`enlivenReceipt actor exporter :: s.log`. We bridge faithfully, carrying the AUTHORITY conjunct as an
explicit hypothesis (the honest chained-vs-raw contrast — NOT papered, exactly as SwissExport carries
`haccess` and BalanceA carries `acceptsEffects`). -/

/-- **`interp_enlivenStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When the
actor holds authority over the exporting cell (`stateAuthB s.kernel.caps actor exporter = true`, the chained
layer's extra AUTHORITY gate) and the §2 cornerstone commits on the kernel (`interp (enlivenStmt sw claimed)
st.kernel = some k'`), the unified action executor `execFullA st (.enlivenRefA sw actor exporter claimed)`
commits to the chained state `⟨k', enlivenReceipt actor exporter :: st.log⟩`. So the Argus term's kernel
meaning lifts to the chained executor the standalone descriptor speaks about, modulo the carried AUTHORITY
side-condition. -/
theorem interp_enlivenStmt_chained
    (st : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth)
    (k' : RecordKernelState)
    (haccess : stateAuthB st.kernel.caps actor exporter = true)
    (hexec : interp (enlivenStmt sw claimed) st.kernel = some k') :
    execFullA st (.enlivenRefA sw actor exporter claimed)
      = some { kernel := k', log := enlivenReceipt actor exporter :: st.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `swissEnlivenK`.
  rw [interp_enlivenStmt_eq_swissEnlivenK] at hexec
  -- `execFullA st (.enlivenRefA …)` reduces to `swissEnlivenChainA st …`, which on `stateAuthB` opens to a
  -- `match swissEnlivenK …` — and `hexec` names that as `some k'`. `enlivenReceipt` is exactly the chained
  -- receipt literal `{ actor, exporter, exporter, 0 }`.
  show swissEnlivenChainA st sw actor exporter claimed
    = some { kernel := k', log := enlivenReceipt actor exporter :: st.log }
  unfold swissEnlivenChainA enlivenReceipt
  rw [if_pos haccess, hexec]

#assert_axioms interp_enlivenStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of enliven's OWN standalone v2 `Surface2` circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against enliven's GENUINE standalone descriptor `enlivenCircuit S … (enlivenE …)` (the v2
`Surface2` circuit whose soundness is `enlivenRefA_full_sound`), NOT a per-row EffectVM descriptor — see the
descriptor surface investigation in this file's header. The executor side is routed through §3 (`interp` ⟹
`execFullA`, modulo AUTHORITY) and the independent `execFullA_enliven_iff_spec` (executor ⟺ `EnlivenSpec`);
the circuit side is the audited `enlivenRefA_full_sound` (circuit ⟹ `EnlivenSpec`). Both name the SAME
`EnlivenSpec`, so they PROVABLY agree on the WHOLE 17-field state + the log + the 3-conjunct guard — strictly
stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of an `enliven` term: enliven's OWN audited standalone v2 `Surface2`
circuit step — the full-state arithmetization `satisfiedE2 S (enlivenE LE cN hN hLE) (encodeE2 …)` satisfied
on the encoded `(st, ⟨sw, actor, exporter, claimed⟩, st')` triple (DEFINITIONALLY the `EffectRefinement`
hub's `effect2CircuitStep S (enlivenE …) st args st'`, inlined here so this module's v2-import surface is
only `Inst.enlivenRefA`). Its soundness `enlivenRefA_full_sound` pins the complete `EnlivenSpec`. The
`enliven`-keyed analog of `swissExportCircuit`, in the descriptor universe where enliven carries its OWN
genuine full-state circuit. -/
def enlivenCircuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (st : RecChainedState) (args : EnlivenArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (enlivenE LE cN hN hLE)
    (encodeE2 S (enlivenE LE cN hN hLE) st args st')

/-- **`enlivenSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`EnlivenSpec st sw actor exporter claimed ·` are equal. Rather than re-derive this field-by-field, we route
through the PROVEN executor⟺spec corner `execFullA_enliven_iff_spec`: each `EnlivenSpec` reconstructs the
SAME committed value `execFullA st (.enlivenRefA …) = some ·`, and `some` is injective. This is exactly the
sense in which `EnlivenSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state (the BalanceA/SwissExport `*_unique` analog). -/
theorem enlivenSpec_unique {st st₁ st₂ : RecChainedState} {sw : Nat} {actor exporter : CellId}
    {claimed : List Auth}
    (h₁ : EnlivenSpec st sw actor exporter claimed st₁)
    (h₂ : EnlivenSpec st sw actor exporter claimed st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.enlivenRefA sw actor exporter claimed) = some st₁ :=
    (execFullA_enliven_iff_spec st sw actor exporter claimed st₁).mpr h₁
  have e₂ : execFullA st (.enlivenRefA sw actor exporter claimed) = some st₂ :=
    (execFullA_enliven_iff_spec st sw actor exporter claimed st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`enliven_compile_sound` — the welded soundness (enliven slice), against enliven's OWN descriptor.**

Suppose, for the Argus enliven term `enlivenStmt sw claimed`:
  * the standalone enliven circuit `enlivenCircuit S LE cN hN hLE st ⟨sw, actor, exporter, claimed⟩ st'`
    (= `enlivenE`'s full-state v2 arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-list-digest portals (`hRest : RestIffNoSwiss S.RH`, `hLog : logHashInjective S.LH`,
    `hN : compressNInjective cN`, `hLE : listLeafInjective LE`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (enlivenStmt sw claimed) st.kernel
    = some k'` (`hexec`), with the actor holding authority over the exporting cell (`haccess`, the chained
    AUTHORITY side-condition).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := enlivenReceipt actor exporter :: st.log }`. I.e. enliven's OWN
circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (`swiss` with the target entry's
`refcount` bumped by one and every other swiss entry UNCHANGED, every other field — INCLUDING `bal`,
balance-NEUTRAL — frozen) AND the receipt log AND the 3-conjunct guard — the full `EnlivenSpec`, not a
per-cell projection. So the circuit the prover runs for enliven pins the complete state the IR term's
executor produces.

The honest chained-vs-raw AUTHORITY gap is carried as the explicit `haccess` hypothesis (NOT papered): the
RAW-kernel `swissEnlivenK` the cornerstone captures gates only on MEMBERSHIP ∧ NON-AMPLIFICATION, while the
CHAINED executor the descriptor speaks about adds the AUTHORITY conjunct. NO nonce-tick / collapsed-field
divergence enters this surface (the v2 descriptor is balance-neutral, matching the executor). -/
theorem enliven_compile_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth)
    (k' : RecordKernelState)
    (hcirc : enlivenCircuit S LE cN hN hLE st ⟨sw, actor, exporter, claimed⟩ st')
    (haccess : stateAuthB st.kernel.caps actor exporter = true)
    (hexec : interp (enlivenStmt sw claimed) st.kernel = some k') :
    st' = { kernel := k', log := enlivenReceipt actor exporter :: st.log } := by
  -- circuit side: enliven's OWN audited soundness forces the FULL `EnlivenSpec` on
  -- `(st, ⟨sw,actor,exporter,claimed⟩, st')`.
  have hspec : EnlivenSpec st sw actor exporter claimed st' :=
    enlivenRefA_full_sound S LE cN hN hLE hRest hLog st ⟨sw, actor, exporter, claimed⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.enlivenRefA …) = some ⟨k', receipt :: log⟩`, and
  -- the independent executor⟺spec corner turns THAT into `EnlivenSpec st … ⟨k', receipt :: log⟩`.
  have hspec' : EnlivenSpec st sw actor exporter claimed
      { kernel := k', log := enlivenReceipt actor exporter :: st.log } :=
    (execFullA_enliven_iff_spec st sw actor exporter claimed _).mp
      (interp_enlivenStmt_chained st sw actor exporter claimed k' haccess hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact enlivenSpec_unique hspec hspec'

#assert_axioms enliven_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely BUMPS the target entry's refcount (live-reference observable),
preserves the other swiss entries + is balance-NEUTRAL, and the gate REJECTS forged inputs (fail-closed on an
ABSENT swiss number AND on an AMPLIFYING enliven).

The cornerstone/weld would be hollow if enliven never committed, if the refcount-bump were a no-op, if it
touched `bal`, or if the gate admitted everything. A concrete two-account kernel PRE-POPULATED with one swiss
record (swiss number `7`, exported rights `[Auth.read]`, refcount `1`) exercises a real enliven; the rejection
lemmas show each raw-kernel guard conjunct fails closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts, cell 0 holds 30 of asset 0 on the
genuine per-asset ledger `bal`, and the swiss table holds ONE exported sturdy ref — swiss number `7`, exporter
0, target 1, exported rights `[Auth.read]`, `refcount = 1`, no cert (so an enliven of `7` claiming `⊆ [read]`
is admissible and BUMPS its refcount to 2). -/
def kE0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 30 else 0
    swiss := [{ swiss := 7, exporter := 0, target := 1, rights := [Auth.read], refcount := 1, cert := none }] }

/-- **NON-VACUITY (the ENLIVEN is OBSERVABLE — the refcount BUMPS).** The committed enliven of swiss number `7`
claiming the empty rights `[]` (trivially `⊆ [read]`) RAISES the entry's GC `refcount` from `1` to `2` — a new
LIVE reference genuinely lands (the `setSwiss`/`replaceSwiss` in-place bump is real, not a no-op). This is the
load-bearing GC fact a later drop reads. -/
theorem enlivenStmt_bumps_refcount :
    (interp (enlivenStmt 7 []) kE0).bind (fun k => (findSwiss k.swiss 7).map (·.refcount))
      = some 2 := by
  rw [interp_enlivenStmt_eq_swissEnlivenK]
  decide

/-- **NON-VACUITY (the swiss table stays length-stable — enliven BUMPS, does not GROW).** Unlike EXPORT (which
prepends a fresh record), enliven of `7` leaves the swiss table at length `1` — it updates the EXISTING entry
in place rather than adding one. The structural contrast with the EXPORT sibling, proved on the term. -/
theorem enlivenStmt_length_stable :
    (interp (enlivenStmt 7 []) kE0).map (fun k => k.swiss.length) = some 1 := by
  rw [interp_enlivenStmt_eq_swissEnlivenK]
  decide

/-- **NON-VACUITY (BALANCE NEUTRALITY — the CapTP punchline).** The committed enliven leaves the per-asset
ledger entry `(0, 0)` UNTOUCHED at `30` — enlivening a sturdy ref grants a live REFERENCE, NOT balance (it
edits only `swiss`, never `bal`). The load-bearing distinction from a value-moving effect, proved on the term. -/
theorem enlivenStmt_bal_neutral :
    (interp (enlivenStmt 7 []) kE0).map (fun k => k.bal 0 0) = some 30 := by
  rw [interp_enlivenStmt_eq_swissEnlivenK]
  decide

/-- **NON-VACUITY (fail-closed: ABSENT swiss number / MEMBERSHIP).** Enlivening a swiss number `9` that is NOT
in the committed table (`kE0` holds only `7`) does NOT commit — the term returns `none` (the MEMBERSHIP
conjunct of the gate fails). Authority only flows from a genuinely-minted swiss entry; an unminted reference is
unreachable. -/
theorem enlivenStmt_rejects_absent :
    interp (enlivenStmt 9 []) kE0 = none := by
  rw [interp_enlivenStmt_eq_swissEnlivenK]
  decide

/-- **NON-VACUITY (fail-closed: AMPLIFYING enliven / NON-AMPLIFICATION).** Enlivening swiss number `7` while
CLAIMING rights `[Auth.write]` that EXCEED the entry's exported rights (`[Auth.read]`, and `[write] ⊄ [read]`)
does NOT commit — the term returns `none` (the NON-AMPLIFICATION conjunct fails). A bearer cannot enliven a
sturdy ref into MORE authority than the export granted: the capability-amplification hole is closed, in the IR. -/
theorem enlivenStmt_rejects_amplifying :
    interp (enlivenStmt 7 [Auth.write]) kE0 = none := by
  rw [interp_enlivenStmt_eq_swissEnlivenK]
  decide

#assert_axioms enlivenStmt_bumps_refcount
#assert_axioms enlivenStmt_length_stable
#assert_axioms enlivenStmt_bal_neutral
#assert_axioms enlivenStmt_rejects_absent
#assert_axioms enlivenStmt_rejects_amplifying

/-! ## §MAGNESIUM — the RUNNABLE descriptor binds the FULL `system_roots` sub-block (whole-state).

`Emit/EffectVmEmitSwissFamilyFull.lean` lifts the RUNNABLE EffectVM descriptor for `enlivenRefA` to bind the
FULL 17-field post-state (`swissEnliven_runnable_full_sound` pins `SwissFullClause`; the anti-ghost
`swissEnliven_runnable_rejects_root_tamper` rules out a tamper of ANY of the 8 side-table roots). This
section restates the headline at the effect level: the STURDYREF root advances to the refcount-bumped-list
digest, and the 7 OTHER side-table roots are provably FROZEN — the whole-state binding the per-cell
descriptor could not state. -/

open Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull
  (SwissFullClause SwissFullClause_sturdyref_advance SwissFullClause_other_roots_frozen sturdyrefIdx)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Exec.SystemRoots (SysRoots N_SYSTEM_ROOTS)

/-- **`magnesium_binds_full_sysroots` — the whole-`system_roots` binding for swissEnliven.** From the
RUNNABLE full-state crown's `SwissFullClause`, the post STURDYREF root IS the witnessed refcount-bumped
swiss-list digest `d`, and EVERY other side-table root is FROZEN at its pre value. So an `enlivenRefA` proof
binds the whole `system_roots` sub-block, not a per-cell projection. -/
theorem magnesium_binds_full_sysroots
    {d : ℤ} {pre post : CellState} {preRoots postRoots : SysRoots}
    (hfull : SwissFullClause d pre post preRoots postRoots) :
    postRoots sturdyrefIdx = d
    ∧ (∀ i : Fin N_SYSTEM_ROOTS, i ≠ sturdyrefIdx → postRoots i = preRoots i) :=
  ⟨SwissFullClause_sturdyref_advance hfull, fun i hi => SwissFullClause_other_roots_frozen hfull i hi⟩

#assert_axioms magnesium_binds_full_sysroots

end Dregg2.Circuit.Argus.Effects.SwissEnliven
