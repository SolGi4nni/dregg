/-
# Dregg2.Circuit.Inst.sealA — the v2 (`EffectCommit2`) instance for the SEAL-BOX effect `sealA`.

`sealA` is the single-component seal-box constructor of the FULL op-set executor `execFullA`
(`execFullA s (.sealA pid actor payload) = sealChainA s pid actor payload`,
`TurnExecutorFull.lean:1845`). It PREPENDS one `SealedBoxRecord ⟨pid, actor, payload⟩` to the
holding-store `sealedBoxes`, prepends a disclosing receipt to the log, and freezes the 16 non-
`sealedBoxes` kernel fields (INCLUDING `caps` — the sealer's c-list is unchanged, the cap is COPIED
into the box, the FRAME-GAP flagged in the spec). It is the LIST-FIELD analogue of the `noteCreateA`
worked template (`Inst/noteCreateA.lean`): the SAME touched shape (a `listComponent` over a
side-table `List`, FULL-list digest `ListCommit.listDigest`, so a drop/reorder of an existing box is
REJECTED), the SAME growing log, the SAME single-`propBit` guard column — differing ONLY in (1) the
touched field is `sealedBoxes` (not `commitments`), so the rest frame OMITS `sealedBoxes`
(`RestIffNoSealedBoxes`, ADDED here — the v1 `RestHashIffFrame` with `sealedBoxes` omitted), (2) the
spec-predicted post-list is the box prepend `sealedBoxPrepend …` (a REAL `SealedBoxRecord`, not a
`Nat` commitment), (3) the guard is the NON-trivial 2-conjunct `sealAdmitGuard` (the actor HOLDS the
sealer cap for `pid` ∧ HOLDS the `payload` cap it seals — unlike `noteCreateA`'s trivial `True`),
and (4) the receipt + bridge target are the seal's (`sealReceipt`, `SealSpec`).

THE VALIDATION: `sealA_full_sound ⇒ SealSpec` THROUGH the framework. A satisfying v2 full-state
witness for `sealE` proves the complete declarative `SealSpec` (the apex truth in
`Dregg2/Circuit/Spec/sealboxoperations.lean`, whose executor corner is `execFullA_seal_iff_spec`).

ADDITIVE: imports `EffectCommit2` + the seal-box-operations spec; edits NEITHER them NOR any `Spec/*`
file NOR `Dregg2.lean`. Follows the `noteCreateA` LIST-field template (`Inst/noteCreateA.lean`) and
the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.sealboxoperations

namespace Dregg2.Circuit.Inst.SealA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.SealBoxOperations
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

`sealA`'s guard is the NON-trivial 2-conjunct `sealAdmitGuard` (held-sealer-cap ∧ held-payload-cap).
The bit gate is guard-AGNOSTIC, so the 2-conjunct guard fits the same single-`propBit`-column shape
as `burnA`'s 4-conjunct / `noteCreateA`'s trivial guard: we commit it as ONE `propBit` column at wire
`0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoSealedBoxes` portal (the v1 `RestHashIffFrame` minus `sealedBoxes`).

The realizable injective-rest-hash portal for the effect that touches the `sealedBoxes` list: the
rest hash binds the 16 non-`sealedBoxes` components (BIDIRECTIONAL), OMITTING `sealedBoxes` (the
touched field of `sealA`). This is the 1-line mirror of `EffectCommit2.RestIffNoNullifiers`, swapping
the omitted field from `nullifiers` to `sealedBoxes`. The clause ORDER is verbatim `SealSpec`'s frame
order (`accounts cell caps escrows nullifiers revoked commitments bal queues swiss slotCaveats
factories lifecycle deathCert delegate delegations`) so the bridge is a DIRECT identity. Carried Prop
hypothesis (realizable — a Poseidon hash of a canonical serialization of the named fields), never an
axiom. -/

/-- **`RestIffNoSealedBoxes RH`** — the rest hash binds the 16 non-`sealedBoxes` components
(BIDIRECTIONAL), omitting `sealedBoxes` (the touched field of `sealA`). -/
def RestIffNoSealedBoxes (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-! ## §2 — the `sealA` instance (touched component = `sealedBoxes`). -/

/-- The seal effect arguments: the seal-pair id, the acting principal, and the payload cap sealed. -/
structure SealArgs where
  pid     : Nat
  actor   : CellId
  payload : Cap

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The seal guard as a `Prop` (the spec's 2-conjunct `sealAdmitGuard`). -/
def sealGuardProp (s : RecChainedState) (args : SealArgs) : Prop :=
  sealAdmitGuard s args.pid args.actor args.payload

instance (s : RecChainedState) (args : SealArgs) : Decidable (sealGuardProp s args) := by
  unfold sealGuardProp sealAdmitGuard; exact inferInstanceAs (Decidable (_ ∧ _))

/-- The seal guard's witness generator: the single `propBit` column at wire `0`. -/
def sealGuardEncode (s : RecChainedState) (args : SealArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (sealGuardProp s args) else 0

/-- The seal guard sub-system: the single `propBit` gate. -/
def sealGuardGates : ConstraintSystem := [cBitGuard]

/-- **`sealGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem sealGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied sealGuardGates a ↔ satisfied sealGuardGates b := by
  unfold satisfied sealGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `sealedBoxes` list component: digest = `listDigest LE cN` over the holding-store. The carriers
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor; the
leaf `LE : SealedBoxRecord → ℤ` is a Poseidon serialization of one box. The spec'd post-shape is the
FULL list `sealedBoxPrepend pre … = ⟨pid, actor, payload⟩ :: pre.sealedBoxes` — a drop/reorder of a
prior box is REJECTED by `ListDigestBindsList`, not merely "grew by the new box". -/
def boxesComponent (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState SealArgs :=
  listComponent (·.sealedBoxes) LE cN hN hLE
    (fun s args => sealedBoxPrepend s.kernel.sealedBoxes args.pid args.actor args.payload)

/-- **`sealE`** — the `EffectSpec2` for `sealA`, supplied to the v2 framework. -/
def sealE (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState SealArgs where
  view         := chainView
  active       := boxesComponent LE cN hN hLE
  logUpdate    := some (fun s args => sealReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := sealGuardGates
  guardProp    := sealGuardProp
  guardWidth   := 1
  guardEncode  := sealGuardEncode
  guardLocal   := sealGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `sealE`. -/

/-- **`GuardDecodes2 (sealE …)`** — the single bit gate on the guard witness decodes to
`sealAdmitGuard`. -/
theorem sealGuardDecodes (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (sealE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied sealGuardGates (sealGuardEncode s args s') at hsat
  show sealGuardProp s args
  have hg := hsat cBitGuard (by simp [sealGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, sealGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (sealE …)`** — `sealAdmitGuard` encodes to the satisfied bit gate. -/
theorem sealGuardEncodes (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (sealE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied sealGuardGates (sealGuardEncode s args s')
  intro c hc
  simp only [sealGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, sealGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `sealE` rest-frame portal (the `→`): `RestIffNoSealedBoxes RH`'s soundness side (the
`sealedBoxes`-omitting rest frame). -/
theorem sealRestFrameDecodes (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoSealedBoxes S.RH) :
    RestFrameDecodes2 S (sealE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `SealSpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM `SealSpec`'s frame
order (`accounts cell caps escrows nullifiers revoked commitments bal queues swiss slotCaveats
factories lifecycle deathCert delegate delegations`), and the guard / component / log clauses line up
one-to-one. The component `postClause` is `s'.kernel.sealedBoxes = sealedBoxPrepend …`, definitionally
the spec's `sealedBoxes` clause. So both directions are a flat re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_sealSpec`** — the framework's derived `apex` for `sealE` is EXACTLY `SealSpec`. The
guard is `sealAdmitGuard`; the component `postClause` is the FULL box-list equality
(`sealedBoxPrepend …`); the log is the seal-receipt-prepended chain; the `restFrame` is the 16
non-`sealedBoxes` frame clauses in `SealSpec`'s order. -/
theorem apex_iff_sealSpec (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) :
    (sealE LE cN hN hLE).apex s args s' ↔ SealSpec s args.pid args.actor args.payload s' := by
  show (sealGuardProp s args
        ∧ s'.kernel.sealedBoxes = sealedBoxPrepend s.kernel.sealedBoxes args.pid args.actor args.payload
        ∧ s'.log = sealReceipt args.actor :: s.log
        ∧ ((sealE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ SealSpec s args.pid args.actor args.payload s'
  unfold SealSpec sealGuardProp sealE
  constructor
  · rintro ⟨hg, hsb, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hDgs⟩
    exact ⟨hg, hsb, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hDgs⟩
  · rintro ⟨hg, hsb, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hDgs⟩
    exact ⟨hg, hsb, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hDgs⟩

/-! ### §2c — THE VALIDATION: `sealA_full_sound ⇒ SealSpec` through the framework. -/

/-- **`sealA_full_sound` — the VALIDATION (seal through the v2 framework).** A satisfying v2 full-state
witness for `sealE` proves the complete declarative bespoke `SealSpec`. Portals:
`RestIffNoSealedBoxes RH` (the `sealedBoxes`-omitting rest frame), `logHashInjective LH` (the growing
log), `compressNInjective cN` + `listLeafInjective LE` (the `sealedBoxes` list-component carriers — the
realizable Poseidon-CR set). CONCLUDES the bespoke `Spec.SealBoxOperations.SealSpec` THROUGH the
generic `effect2_circuit_full_sound`, the circuit⟺spec corner of the seal-box triangle (whose executor
corner is `execFullA_seal_iff_spec`). -/
theorem sealA_full_sound
    (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (sealE LE cN hN hLE) (encodeE2 S (sealE LE cN hN hLE) s args s')) :
    SealSpec s args.pid args.actor args.payload s' := by
  have hapex : (sealE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (sealE LE cN hN hLE)
      (sealRestFrameDecodes S LE cN hN hLE hRest) hLog (sealGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_sealSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def sealEWire : EffectSpec2 RecChainedState SealArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := sealGuardGates
  guardProp    := sealGuardProp
  guardWidth   := 1
  guardEncode  := sealGuardEncode
  guardLocal   := sealGuardLocal
  guardWidth_le := by decide

def sealAAirName : String := "dregg-sealA-v2"

def sealAEmitted : EmittedDescriptor := emittedEffect2 sealAAirName sealEWire

#guard sealAEmitted.name == sealAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms sealGuardLocal
#assert_axioms sealGuardDecodes
#assert_axioms sealGuardEncodes
#assert_axioms apex_iff_sealSpec
#assert_axioms sealA_full_sound

end Dregg2.Circuit.Inst.SealA
