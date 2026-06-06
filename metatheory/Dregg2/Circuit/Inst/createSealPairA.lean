/-
# Dregg2.Circuit.Inst.createSealPairA — the v2 (`EffectCommit2`) instance for SEAL-PAIR-CREATION.

`createSealPairA` is the single-component `caps`-shape constructor of `FullActionA`: a GATED double
c-list grant that installs a sealer/unsealer keypair. GATED on `actor` holding authority over
`sealerHolder` (`stateAuthB s.kernel.caps actor sealerHolder = true`, the writer of the pair). On
commit it rewrites ONLY `kernel.caps` to the pure double grant `createSealPairCaps` (grant `sealerCap
pid` to `sealerHolder`, then `unsealerCap pid` to `unsealerHolder`), prepends a receipt to the log,
and freezes the 16 non-`caps` kernel fields. It is bal-NEUTRAL (edits `caps`, never `bal`).

This is the `caps` analog of the `bal`-touching `burnA` template (`Dregg2/Circuit/Inst/burnA.lean`):
the SAME `funcComponent` shape (the touched thing is a FUNCTION-field whose digest is an injective
whole-function hash — the realizable `cellLeafInjective` bar; for `caps : Label → List Cap` it is a
Poseidon Merkle over the canonical serialization of the slot-function), the SAME growing log, the same
single-bit guard sub-system. It differs from `burnA` only in (1) the touched field is `caps` (not
`bal`), so the frame portal is `RestIffNoCaps` (ADDED here — the v1 `RestHashIffFrame` with `caps`
omitted; the `RestIffNo*` portal for `caps` is not yet in `EffectCommit2`, so we mirror it locally as
`noteCreateA` did for `RestIffNoCommitments`), (2) the spec-predicted ledger value is the pure double
grant `createSealPairCaps … pid sealerHolder unsealerHolder` (not a `recBalCredit`), (3) the guard is
`CreateSealPairGuard` (a single decidable `stateAuthB … = true`), and (4) the receipt + bridge target
are the seal-pair's (`createSealPairReceipt`, `CreateSealPairSpec`).

THE VALIDATION: `createSealPairA_full_sound ⇒ CreateSealPairSpec` THROUGH the framework. A satisfying
v2 full-state witness for `createSealPairE` proves the complete declarative `CreateSealPairSpec` (the
apex truth in `Dregg2/Circuit/Spec/sealpaircreation.lean`, whose executor corner is
`createSealPair_iff_spec`). The post-`caps` clause is FULL function equality, so a tamper of ANY
slot's caps (a third holder's authority) is REJECTED by `effectCircuit2_rejects_wrong_component` — not
merely "the two recipients gained a cap".

ADDITIVE: imports `EffectCommit2` + the seal-pair-creation spec; edits NEITHER (nor any `Spec/*` file
NOR `Dregg2.lean`). Follows the `burnA` template (`Dregg2/Circuit/Inst/burnA.lean`) + the recipe in
`Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.sealpaircreation

namespace Dregg2.Circuit.Inst.CreateSealPairA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.SealPairCreation
open Dregg2.Authority (Caps)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the `burnA` template).

The seal-pair spec exposes its guard as a `Prop` (`CreateSealPairGuard` = a single decidable
`stateAuthB … = true`), not a per-gate circuit, so we commit it as ONE `propBit` column at wire `0`
(guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical to `burnA`/`mintE`; the bit gate is
guard-agnostic, so the 1-conjunct authority guard fits the same shape.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoCaps` portal (the v1 `RestHashIffFrame` minus `caps`).

The realizable injective-rest-hash portal for the effect that touches the `caps` function-field: the
rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), OMITTING `caps` (the touched field of
`createSealPairA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted
field from `bal` to `caps`. The frame field order is VERBATIM `CreateSealPairSpec`'s frame order
(`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`). Carried Prop hypothesis (realizable — a
Poseidon hash of a canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL),
omitting `caps` (the touched field of `createSealPairA`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `createSealPairE` instance (touched component = `caps`).

`createSealPairA` over `RecChainedState`: the touched component is the `caps` slot-function (a
`funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`); the log GROWS by the seal-pair receipt; the frame is the 16 non-`caps` kernel
fields (`RestIffNoCaps`). -/

/-- The seal-pair effect arguments: pid, actor, sealer holder, unsealer holder. -/
structure CreateSealPairArgs where
  pid           : Nat
  actor         : CellId
  sealerHolder  : CellId
  unsealerHolder : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The seal-pair guard as a `Prop` (the spec's `CreateSealPairGuard`). -/
def createSealPairGuardProp (s : RecChainedState) (args : CreateSealPairArgs) : Prop :=
  CreateSealPairGuard s args.actor args.sealerHolder

instance (s : RecChainedState) (args : CreateSealPairArgs) :
    Decidable (createSealPairGuardProp s args) := by
  unfold createSealPairGuardProp CreateSealPairGuard
  exact inferInstanceAs (Decidable (_ = _))

/-- The seal-pair guard's witness generator: lay the single `propBit` column at wire `0`. -/
def createSealPairGuardEncode (s : RecChainedState) (args : CreateSealPairArgs)
    (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (createSealPairGuardProp s args) else 0

/-- The seal-pair guard sub-system: the single `propBit` gate. -/
def createSealPairGuardGates : ConstraintSystem := [cBitGuard]

/-- **`createSealPairGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem createSealPairGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied createSealPairGuardGates a ↔ satisfied createSealPairGuardGates b := by
  unfold satisfied createSealPairGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the pure double grant `createSealPairCaps … pid sealerHolder unsealerHolder`
(the SOLE arithmetic difference from `burnA`, which predicts a `recBalCredit`). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateSealPairArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args =>
      createSealPairCaps s.kernel.caps args.pid args.sealerHolder args.unsealerHolder)

/-- **`createSealPairE`** — the `EffectSpec2` for `createSealPairA`, supplied to the v2 framework. -/
def createSealPairE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState CreateSealPairArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args =>
    createSealPairReceipt args.actor args.sealerHolder :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := createSealPairGuardGates
  guardProp    := createSealPairGuardProp
  guardWidth   := 1
  guardEncode  := createSealPairGuardEncode
  guardLocal   := createSealPairGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `createSealPairE`. -/

/-- **`GuardDecodes2 (createSealPairE …)`** — the single bit gate on the guard witness decodes to
`CreateSealPairGuard`. -/
theorem createSealPairGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (createSealPairE D hD) := by
  intro s args s' hsat
  change satisfied createSealPairGuardGates (createSealPairGuardEncode s args s') at hsat
  show createSealPairGuardProp s args
  have hg := hsat cBitGuard (by simp [createSealPairGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createSealPairGuardEncode, if_pos]
    at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (createSealPairE …)`** — `CreateSealPairGuard` encodes to the satisfied bit
gate. -/
theorem createSealPairGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (createSealPairE D hD) := by
  intro s args s' hg
  show satisfied createSealPairGuardGates (createSealPairGuardEncode s args s')
  intro c hc
  simp only [createSealPairGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createSealPairGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `createSealPairE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the
`caps`-omitting rest frame). -/
theorem createSealPairRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (createSealPairE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `CreateSealPairSpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM
`CreateSealPairSpec`'s frame order (`accounts cell escrows nullifiers revoked commitments bal queues
swiss slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`), and the guard /
component / log clauses line up one-to-one. So both directions are a flat re-packaging of the same 19
conjuncts. -/

/-- **`apex_iff_createSealPairSpec`** — the framework's derived `apex` for `createSealPairE` is EXACTLY
`CreateSealPairSpec`. The guard is `CreateSealPairGuard`; the component `postClause` is the FULL `caps`
function equality (`createSealPairCaps …` — a tamper of ANY slot is rejected, not just the two
recipients); the log is the receipt-prepended chain; the `restFrame` is the 16 non-`caps` frame
clauses in `CreateSealPairSpec`'s order. -/
theorem apex_iff_createSealPairSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState) :
    (createSealPairE D hD).apex s args s'
      ↔ CreateSealPairSpec s args.pid args.actor args.sealerHolder args.unsealerHolder s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (createSealPairGuardProp s args
        ∧ s'.kernel.caps
            = createSealPairCaps s.kernel.caps args.pid args.sealerHolder args.unsealerHolder
        ∧ s'.log = createSealPairReceipt args.actor args.sealerHolder :: s.log
        ∧ ((createSealPairE D hD).restFrame s.kernel s'.kernel))
       ↔ CreateSealPairSpec s args.pid args.actor args.sealerHolder args.unsealerHolder s'
  unfold CreateSealPairSpec createSealPairGuardProp createSealPairE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `createSealPairA_full_sound ⇒ CreateSealPairSpec` through the framework. -/

/-- **`createSealPairA_full_sound` — the VALIDATION (seal-pair-creation through the v2 framework).** A
satisfying v2 full-state witness for `createSealPairE` proves the complete declarative
`CreateSealPairSpec`. Portals: `RestIffNoCaps RH` (the `caps`-omitting rest frame), `logHashInjective
LH` (the growing log), `Function.Injective D` (the `caps` component's whole-function digest — the
realizable Poseidon-CR bar). CONCLUDES the bespoke `Spec.SealPairCreation.CreateSealPairSpec` THROUGH
the generic `effect2_circuit_full_sound`, the circuit⟺spec corner of the seal-pair triangle. -/
theorem createSealPairA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (createSealPairE D hD) (encodeE2 S (createSealPairE D hD) s args s')) :
    CreateSealPairSpec s args.pid args.actor args.sealerHolder args.unsealerHolder s' := by
  have hapex : (createSealPairE D hD).apex s args s' :=
    effect2_circuit_full_sound S (createSealPairE D hD)
      (createSealPairRestFrameDecodes S D hD hRest) hLog (createSealPairGuardDecodes D hD) s args s' h
  exact (apex_iff_createSealPairSpec D hD s args s').mp hapex

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms createSealPairGuardLocal
#assert_axioms createSealPairGuardDecodes
#assert_axioms createSealPairGuardEncodes
#assert_axioms apex_iff_createSealPairSpec
#assert_axioms createSealPairA_full_sound

end Dregg2.Circuit.Inst.CreateSealPairA
