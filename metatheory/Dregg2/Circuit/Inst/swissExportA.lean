/-
# Dregg2.Circuit.Inst.swissExportA — the v2 (`EffectCommit2`) instance for the CapTP sturdy-ref MINT
  `exportSturdyRefA` (the swiss-table EXPORT arm of `execFullA`).

`exportSturdyRefA sw actor exporter target rights` MINTS a fresh sturdy ref: it GROWS the swiss-table
list `kernel.swiss` by a fresh `SwissRecord` (keyed by swiss number `sw`, minted by `exporter`, pointing
at `target`, carrying the exported `rights`, `refcount := 1`, no bound cert), prepends an authority
receipt to the log, and FREEZES the 16 non-`swiss` kernel fields. It is GATED on a THREE-way
admissibility conjunction (`ExportGuard`): AUTHORITY (the actor holds authority over the exporting cell),
FRESHNESS (the swiss number is not already in use), and NON-AMPLIFICATION (the exported `rights` are `⊆`
the exporter's GENUINELY-held rights, read off the committed c-list — a bare-authority actor cannot mint
a sturdy ref carrying rights its cell never held).

So this is a SINGLE-component effect whose touched component is the `List`-side-table `swiss`
(`List SwissRecord`) — exactly the `listComponent` shape of `noteCreateA` (`commitments`), only over
`swiss` with element type `SwissRecord` instead of `commitments` with element type `Nat`. Through the
v2 framework (`EffectCommit2`):
  * touched component = `swiss` (a `listComponent`, FULL-list digest `ListCommit.listDigest`; its
    `binds` is `ListDigestBindsList` — FULL-list equality, so a drop/reorder of an EXISTING sturdy ref
    is REJECTED, not just "grew by the new record"). The spec'd post-shape is the full list
    `exportRecord sw exporter target rights :: pre.swiss`;
  * the log GROWS by the authority receipt (`exportReceipt actor exporter :: s.log`);
  * the guard is the 3-conjunct `ExportGuard` (AUTHORITY ∧ FRESHNESS ∧ NON-AMPLIFICATION), committed as
    ONE `propBit` column (the bit-gate pattern — guard-agnostic, so the 3-conjunct fits the same shape);
  * the frame is the 16 non-`swiss` kernel fields (`RestIffNoSwiss`, ADDED here — the v1
    `RestHashIffFrame` with `swiss` omitted; the swarm adds one `RestIffNo*` per touched field).

`swissExportA_full_sound` CONCLUDES the bespoke `Spec.SwissExport.ExportSpec` THROUGH the framework:
`effect2_circuit_full_sound` gives the derived `apex`, and `apex_iff_exportSpec` (a DIRECT identity
match — the `restFrame` order is verbatim `ExportSpec`'s 16-field frame order, and the guard / `swiss`
component / log clauses line up one-to-one) rewrites it to the bespoke spec. The bespoke spec's executor
corner is `export_iff_spec` (`execFullA` ⟺ `ExportSpec`), so the circuit⟺spec corner here completes the
swissExport triangle.

ADDITIVE: imports `EffectCommit2` + the bespoke spec `Dregg2.Circuit.Spec.swissexport`; edits NEITHER
`EffectCommit2`/`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.swissexport

namespace Dregg2.Circuit.Inst.SwissExportA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.SwissExport
open Dregg2.Authority (Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

`exportSturdyRefA`'s guard is the 3-conjunct `ExportGuard` (AUTHORITY ∧ FRESHNESS ∧ NON-AMPLIFICATION),
not a per-gate circuit, so we commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode
via `propBit p = 1 ↔ p`. (Identical to `burnA`/`noteSpendA`; the bit gate is guard-agnostic, so the
3-conjunct `ExportGuard` fits the same shape as `burnA`'s 4-conjunct `BurnGuard`.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoSwiss` portal (the v1 `RestHashIffFrame` minus `swiss`).

The realizable injective-rest-hash portal for the effect that touches the `swiss` list: the rest hash
binds the 16 non-`swiss` components (BIDIRECTIONAL), OMITTING `swiss` (the touched field of
`exportSturdyRefA`). This is the 1-line mirror of `EffectCommit2.RestIffNoNullifiers`, swapping the
omitted field from `nullifiers` to `swiss`. Carried Prop hypothesis (realizable — a Poseidon hash of a
canonical serialization of the named fields), never an axiom. The omitted/included fields are precisely
`ExportSpec`'s 16-field frame (`accounts cell caps escrows nullifiers revoked commitments bal queues
slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`). -/

/-- **`RestIffNoSwiss RH`** — the rest hash binds the 16 non-`swiss` components (BIDIRECTIONAL), omitting
`swiss` (the touched field of `exportSturdyRefA`). -/
def RestIffNoSwiss (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-! ## §2 — the `swissExportA` instance (touched component = `swiss`). -/

/-- The swiss-export effect arguments: swiss number, actor, exporter, target, exported rights. -/
structure ExportArgs where
  sw       : Nat
  actor    : CellId
  exporter : CellId
  target   : CellId
  rights   : List Auth

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The export guard as a `Prop` (the spec's 3-conjunct `ExportGuard`). -/
def exportGuardProp (s : RecChainedState) (args : ExportArgs) : Prop :=
  ExportGuard s args.sw args.actor args.exporter args.rights

instance (s : RecChainedState) (args : ExportArgs) : Decidable (exportGuardProp s args) := by
  unfold exportGuardProp ExportGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The export guard's witness generator: the single `propBit` column at wire `0`. -/
def exportGuardEncode (s : RecChainedState) (args : ExportArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (exportGuardProp s args) else 0

/-- The export guard sub-system: the single `propBit` gate. -/
def exportGuardGates : ConstraintSystem := [cBitGuard]

/-- **`exportGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem exportGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied exportGuardGates a ↔ satisfied exportGuardGates b := by
  unfold satisfied exportGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `swiss` list component: digest = `listDigest LE cN` over the swiss-table list. The carriers
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor. The
spec'd post-shape is the FULL list `exportRecord … :: pre.swiss` — a drop/reorder of a prior sturdy ref
is REJECTED by `ListDigestBindsList`. -/
def swissComponent (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState ExportArgs :=
  listComponent (·.swiss) LE cN hN hLE
    (fun s args => exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)

/-- **`swissExportE`** — the `EffectSpec2` for `exportSturdyRefA`, supplied to the v2 framework. -/
def swissExportE (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState ExportArgs where
  view         := chainView
  active       := swissComponent LE cN hN hLE
  logUpdate    := some (fun s args => exportReceipt args.actor args.exporter :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := exportGuardGates
  guardProp    := exportGuardProp
  guardWidth   := 1
  guardEncode  := exportGuardEncode
  guardLocal   := exportGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `swissExportE`. -/

/-- **`GuardDecodes2 (swissExportE …)`** — the single bit gate decodes to `ExportGuard`. -/
theorem exportGuardDecodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (swissExportE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied exportGuardGates (exportGuardEncode s args s') at hsat
  show exportGuardProp s args
  have hg := hsat cBitGuard (by simp [exportGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, exportGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (swissExportE …)`** — `ExportGuard` encodes to the satisfied bit gate. -/
theorem exportGuardEncodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (swissExportE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied exportGuardGates (exportGuardEncode s args s')
  intro c hc
  simp only [exportGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, exportGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `swissExportE` rest-frame portal (the `→`): `RestIffNoSwiss RH`'s soundness side. -/
theorem exportRestFrameDecodes (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoSwiss S.RH) :
    RestFrameDecodes2 S (swissExportE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `ExportSpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM `ExportSpec`'s frame
order (`accounts cell caps escrows nullifiers revoked commitments bal queues slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`), and the guard / component / log clauses line up
one-to-one. So both directions are a flat re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_exportSpec`** — the framework's derived `apex` for `swissExportE` is EXACTLY
`ExportSpec`. The guard is `ExportGuard`; the component `postClause` is the FULL swiss-list equality
(`exportRecord … :: pre`); the log is the receipt-prepended chain; the `restFrame` is the 16 non-`swiss`
frame clauses in `ExportSpec`'s order. -/
theorem apex_iff_exportSpec (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState) :
    (swissExportE LE cN hN hLE).apex s args s'
      ↔ ExportSpec s args.sw args.actor args.exporter args.target args.rights s' := by
  show (exportGuardProp s args
        ∧ s'.kernel.swiss = exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss
        ∧ s'.log = exportReceipt args.actor args.exporter :: s.log
        ∧ ((swissExportE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ ExportSpec s args.sw args.actor args.exporter args.target args.rights s'
  unfold ExportSpec exportGuardProp swissExportE
  constructor
  · rintro ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `swissExportA_full_sound ⇒ ExportSpec` through the framework. -/

/-- **`swissExportA_full_sound` — the VALIDATION (swiss-export through the v2 framework).** A satisfying
v2 full-state witness for `swissExportE` proves the complete declarative bespoke `ExportSpec`. Portals:
`RestIffNoSwiss RH` (the `swiss`-omitting rest frame), `logHashInjective LH` (the growing log),
`compressNInjective cN` + `listLeafInjective LE` (the `swiss` list-component carriers — the realizable
Poseidon-CR set). This CONCLUDES the bespoke swiss-export spec through the generic
`effect2_circuit_full_sound`, the circuit⟺spec corner of the swiss-export triangle (whose executor
corner is `Spec.SwissExport.export_iff_spec`). -/
theorem swissExportA_full_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissExportE LE cN hN hLE) (encodeE2 S (swissExportE LE cN hN hLE) s args s')) :
    ExportSpec s args.sw args.actor args.exporter args.target args.rights s' := by
  have hapex : (swissExportE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (swissExportE LE cN hN hLE)
      (exportRestFrameDecodes S LE cN hN hLE hRest) hLog (exportGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_exportSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def swissExportEWire : EffectSpec2 RecChainedState ExportArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := exportGuardGates
  guardProp    := exportGuardProp
  guardWidth   := 1
  guardEncode  := exportGuardEncode
  guardLocal   := exportGuardLocal
  guardWidth_le := by decide

def swissExportAAirName : String := "dregg-swissExportA-v2"

def swissExportAEmitted : EmittedDescriptor := emittedEffect2 swissExportAAirName swissExportEWire

#guard swissExportAEmitted.name == swissExportAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms exportGuardLocal
#assert_axioms exportGuardDecodes
#assert_axioms exportGuardEncodes
#assert_axioms apex_iff_exportSpec
#assert_axioms swissExportA_full_sound

end Dregg2.Circuit.Inst.SwissExportA
