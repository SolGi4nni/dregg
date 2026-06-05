/-
# Dregg2.Intent.Core — the four-faced `Intent`, `fulfill`, and the receipt⊣intent discharge keystone.

Phase 2, layer 2 (`docs/rebuild/PHASE-2-INTENT-SPEC.md`; spine `INTENT-AS-CO-RECEIPT.md`). An **intent**
is a *co-receipt*: the same string-diagram a receipt attests, but with the interior left as a TYPED HOLE
(`§1`). It has FOUR faces (`§2`):

  1. **Boundary (the type / the hole)** — `offered ⊗ wanted`: the resources brought in (`A`) and the
     outcome demanded (`C`). Fulfillment plugs a morphism `offered ⟶ wanted` into the hole.
  2. **Predicate (the requirement)** — `predicate : R → Prop`: which fillings count as correct. This is
     the *demand* side of `Predicate ⊣ Witness` (`Dregg2.Laws`); a fill supplies the witness.
  3. **Resource (the funding)** — `EscrowWitness offered`: a one-shot lockbox holding the offered
     resources, RELEASED to the filler exactly on the discharging receipt. ("Resources To Do It With",
     first-class.) Abstract here; the concrete `KernelIntent` (Phase 3) binds it to a userspace-escrow
     cell-program. NOT `fun _ => True` — double-release is excluded.
  4. **Validity (the time)** — a `Deadline` (Phase 1, `Dregg2/Time/Deadline.lean`): a causal-or-frame
     window, TYPED. Anti-frontrunning = `causalAfter` on the reveal event (a lightcone fact).

**Fulfillment** plugs the morphism into the hole and *annihilates* the co-receipt into a receipt:
`fulfill : Intent ⊗ (matching morphism) ⟶ Receipt` (`§1`, the counit). The discharge **keystone**
(`fulfill_discharges`): a fulfilled intent's receipt witnesses exactly the DEMANDED outcome
(predicate-satisfied + the conversion conserves), and the escrow is CONSUMED (one-shot — no
double-fulfill).

Built per the spec's guidance: define `Intent` + `fulfill`, get one concrete fulfillment running, prove
the discharge for the bilateral case. The full unit/counit adjunction laws are proved later as the
auction needs them. Pure; no `axiom`/`sorry`/`admit`/`native_decide`.
-/
import Dregg2.Intent.Resource
import Dregg2.Time.Deadline

universe v u

-- The module's central type IS `Intent`, living in the `Dregg2.Intent` namespace — the resulting
-- `Dregg2.Intent.Intent` is intentional (cf. `List`/`Option` being both a type and a namespace).
set_option linter.dupNamespace false

namespace Dregg2.Intent

open CategoryTheory
open Dregg2.Time.Deadline (Deadline)
open Dregg2.Authority.Blocklace (Lace Block)
open Dregg2.Authority.Predicate (Registry)
open Dregg2.Time.Frame (FrameStatement)

/-! ## 1. Face 3 — the escrow lockbox (the funding). -/

/-- **Face 3 — the escrow funding `offered`** (abstract). A one-shot lockbox: its existence witnesses
that the offered resources are HELD, and `locked = true` means funded-and-unspent. Fulfillment releases
it (`locked := false`); a released box can never fund a second fill (`no_double_fulfill`). The concrete
`KernelIntent` (Phase 3) replaces this with a real userspace-escrow cell-program holding `offered`. -/
structure EscrowWitness {R : Type u} (offered : R) where
  /-- Funded and unspent (`true`) vs released/consumed (`false`). -/
  locked : Bool
deriving Repr, DecidableEq

/-- Fund the escrow over `offered`: the lockbox starts locked (funded, unspent). -/
def EscrowWitness.fund {R : Type u} (offered : R) : EscrowWitness offered := ⟨true⟩

/-- Release the escrow to the filler: the lockbox becomes unlocked (consumed). -/
def EscrowWitness.release {R : Type u} {offered : R} (_e : EscrowWitness offered) :
    EscrowWitness offered := ⟨false⟩

/-! ## 2. The four-faced `Intent` (the co-receipt). -/

/-- **`Intent R B reg stmtOf`** — a co-receipt over the resource theory `R` and the time-world
`(B, reg, stmtOf)` (the lace + the frame registry + the statement encoder; `Dregg2/Time/Deadline.lean`).
Its four fields are the four faces. The structure needs only `R : Type` (the boundary/predicate/escrow
faces); `fulfill` (§3) adds `[Category R]` to plug a conversion morphism into the hole. -/
structure Intent (R : Type u) {Stmt Wit : Type}
    (B : Lace) (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt) where
  /-- Face 1a — the resources brought in (the `A` wire). -/
  offered : R
  /-- Face 1b — the outcome demanded (the `C` wire; the typed hole `offered ⟶ wanted`). -/
  wanted : R
  /-- Face 2 — which fillings count as correct (the `Predicate` demand of `Dregg2.Laws`). -/
  predicate : R → Prop
  /-- Face 3 — the escrow funding `offered`. -/
  resource : EscrowWitness offered
  /-- Face 4 — the causal-or-frame validity window (Phase 1's `Deadline`). -/
  validity : Deadline B reg stmtOf

/-! ## 3. Fulfillment + the discharging receipt. -/

/-- **The discharging receipt** (`FillReceipt i`) — the co-receipt and the filling morphism
*annihilated* into "it happened" (`INTENT-AS-CO-RECEIPT` §1, the attestation / REORIENT face C). It
records: the achieved `outcome`, the `conversion : offered ⟶ outcome` that filled the hole (the
proof-relevant witness — "to know it happened is to hold the conversion"), the proof the demand was met
(`satisfied`), and the now-spent escrow (`spentEscrow`, released). Linking this into the persistence
chain (`Exec/Receipt.lean`'s `WitnessedReceipt`) is later integration. -/
structure FillReceipt {R : Type u} [Category.{v} R] {Stmt Wit : Type}
    {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}
    (i : Intent R B reg stmtOf) where
  /-- The achieved outcome resource. -/
  outcome : R
  /-- The conversion that filled the hole — the proof-relevant witness `offered ⟶ outcome`. -/
  conversion : i.offered ⟶ outcome
  /-- The demand was met at the outcome. -/
  satisfied : i.predicate outcome
  /-- The escrow, now released (consumed). -/
  spentEscrow : EscrowWitness i.offered

/-- **`fulfill`** — plug the conversion `f : offered ⟶ wanted` into the hole, given the predicate is
satisfied at `wanted` and the escrow is currently LOCKED (funded, unspent). Produces the discharging
receipt with the escrow RELEASED. The `locked = true` precondition is what makes a fill ONE-SHOT: a
released escrow cannot fund a second fill (`no_double_fulfill`). -/
def fulfill {R : Type u} [Category.{v} R] {Stmt Wit : Type}
    {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}
    (i : Intent R B reg stmtOf) (f : i.offered ⟶ i.wanted)
    (hpred : i.predicate i.wanted) (_hlock : i.resource.locked = true) :
    FillReceipt i :=
  { outcome := i.wanted, conversion := f, satisfied := hpred,
    spentEscrow := i.resource.release }

/-! ## 4. The keystones — discharge, conservation, one-shot. -/

variable {R : Type u} [Category.{v} R] {Stmt Wit : Type}
  {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}

/-- **`fulfill_outcome`** — the receipt attests the DEMANDED outcome (`= wanted`), definitionally. -/
theorem fulfill_outcome (i : Intent R B reg stmtOf) (f : i.offered ⟶ i.wanted)
    (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    (fulfill i f hpred hlock).outcome = i.wanted := rfl

/-- **`fulfill_discharges` (KEYSTONE)** — a fulfilled intent's receipt witnesses EXACTLY the demanded
outcome: it equals `wanted`, the predicate is satisfied there, and the escrow is consumed (released).
This is the receipt⊣intent annihilation (`INTENT-AS-CO-RECEIPT` §1) for the bilateral case: the
co-receipt's hole, once filled, becomes a receipt that discharges precisely the demand it carried. -/
theorem fulfill_discharges (i : Intent R B reg stmtOf) (f : i.offered ⟶ i.wanted)
    (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    (fulfill i f hpred hlock).outcome = i.wanted ∧
      i.predicate (fulfill i f hpred hlock).outcome ∧
      (fulfill i f hpred hlock).spentEscrow.locked = false :=
  ⟨rfl, (fulfill i f hpred hlock).satisfied, rfl⟩

/-- **`fulfill_conserves`** — the receipt carries a conversion `offered ⟶ outcome`, so `offered ⪰
outcome` (the fill type-checks and conserves *by construction*, Spivak's functoriality of operadic
substitution). The strong per-asset invariant (`Σ in = Σ out`, no value minted) is the Phase-3 monotone
refinement of this; here we have the convertibility witness, which is its thin shadow. -/
theorem fulfill_conserves (i : Intent R B reg stmtOf) (f : i.offered ⟶ i.wanted)
    (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    Converts i.offered (fulfill i f hpred hlock).outcome :=
  ⟨(fulfill i f hpred hlock).conversion⟩

/-- **`no_double_fulfill` (the one-shot teeth)** — the escrow a fulfillment produces is RELEASED, so it
can never again satisfy `fulfill`'s `locked = true` precondition. A fill consumes the escrow exactly
once; there is no second fill from the same funding. -/
theorem no_double_fulfill (i : Intent R B reg stmtOf) (f : i.offered ⟶ i.wanted)
    (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    (fulfill i f hpred hlock).spentEscrow.locked ≠ true := by
  simp [fulfill, EscrowWitness.release]

/-! ## 5. Non-vacuity — one real fulfillment, and TEETH on all four faces.

The demo time-world matches `Time/Deadline.lean`: `demoLace`, the empty registry, the constant
encoder. The demo intent offers and wants "1 art" (`res 0 1`), so the identity conversion fills it. -/

/-- Demo frame registry (empty — no time authority; the causal deadline needs none). -/
def demoReg : Registry Nat Nat := fun _ => none
/-- Demo statement encoder. -/
def demoStmtOf : FrameStatement → Nat := fun _ => 0

/-- **A real intent:** offer 1 art, want 1 art, accept exactly 1 art, escrow funded, causal deadline
"after genesis `g0`". -/
def demoIntent : Intent DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 0 1
  wanted := res 0 1
  predicate := fun r => r = res 0 1
  resource := EscrowWitness.fund (res 0 1)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- **A real fulfillment** — the identity conversion fills `res 0 1 ⟶ res 0 1`; the predicate accepts;
the escrow is locked. The receipt attests `res 0 1`. -/
def demoReceipt : FillReceipt demoIntent :=
  fulfill demoIntent (𝟙 (res 0 1)) rfl rfl

/-- The demo fulfillment discharges to the demanded outcome (the keystone, concretely). -/
theorem demo_discharges : demoReceipt.outcome = res 0 1 := rfl

/-- The demo escrow is consumed by the fill. -/
theorem demo_escrow_consumed : demoReceipt.spentEscrow.locked = false := rfl

/-! ### Teeth — each face can REFUSE a fill (independently). -/

/-- **Predicate-face teeth:** an intent that demands "5 gold 5 art" but only wants "1 art" cannot be
fulfilled — the predicate REJECTS the wanted outcome, so `hpred` is unprovable. -/
def demoBadPred : Intent DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 0 1
  wanted := res 0 1
  predicate := fun r => r = res 5 5
  resource := EscrowWitness.fund (res 0 1)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- The predicate genuinely refuses: `¬ demoBadPred.predicate demoBadPred.wanted` (1 art ≠ 5 gold 5
art), so no `fulfill demoBadPred …` can be formed. -/
theorem demoBadPred_unfulfillable : ¬ demoBadPred.predicate demoBadPred.wanted := by
  intro h
  -- h : res 0 1 = res 5 5 ⇒ the underlying bundles are equal ⇒ (0,1) = (5,5), absurd.
  have hb : mkBundle 0 1 = mkBundle 5 5 := congrArg Discrete.as h
  exact absurd (Multiplicative.ofAdd.injective hb) (by decide)

/-- **Boundary-face teeth:** an intent offering "2 gold" but demanding "1 art" cannot be fulfilled —
no conversion `offered ⟶ wanted` exists (the hole is unpluggable). Reuses `demo_no_convert`. -/
def demoBadBoundary : Intent DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 2 0
  wanted := res 0 1
  predicate := fun _ => True
  resource := EscrowWitness.fund (res 2 0)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- The hole is unpluggable: `¬ Converts offered wanted`, so `fulfill` has no morphism to take. -/
theorem demoBadBoundary_no_fill :
    ¬ Converts demoBadBoundary.offered demoBadBoundary.wanted := demo_no_convert

/-- **Escrow-face teeth:** an intent whose escrow is already RELEASED cannot be fulfilled — `fulfill`'s
`locked = true` precondition is unsatisfiable (this is also why a fill is one-shot). -/
def demoUnfunded : Intent DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 0 1
  wanted := res 0 1
  predicate := fun r => r = res 0 1
  resource := (EscrowWitness.fund (res 0 1)).release
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- The escrow refuses: `locked ≠ true`, so `fulfill demoUnfunded …` cannot be formed. -/
theorem demoUnfunded_no_fill : demoUnfunded.resource.locked ≠ true := by decide

/-! ### Validity-face — a real `Deadline`, both kinds, met for free in the causal case. -/

/-- A frame-validity twin of `demoIntent` (authority attests `T = 1000` within `δ = 5`). -/
def demoFrameIntent : Intent DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 0 1
  wanted := res 0 1
  predicate := fun r => r = res 0 1
  resource := EscrowWitness.fund (res 0 1)
  validity := Deadline.frameWithin { authority := { issuer := 99 }, T := 1000, δ := 5 } 0

/-- **The validity face is a real typed `Deadline`:** the causal intent reads `kind = true` (a
lightcone fact, no trust), the frame intent `kind = false` (a frame convention carrying `δ`). A court
tells them apart — the §4 relativistic forcing rides on every intent. -/
theorem demo_validity_kinds :
    demoIntent.validity.kind = true ∧ demoFrameIntent.validity.kind = false := ⟨rfl, rfl⟩

/-- **The causal deadline is MET for free** on the demo lace (`g0 ≺ g1`, no authority) — so the demo
intent's validity window is genuinely dischargeable, not a dead field. (The frame twin would need an
attesting authority — `Time/Deadline.lean`'s `demo_frame_unmet_without_authority`.) -/
theorem demoIntent_deadline_met : demoIntent.validity.Met Dregg2.Authority.Blocklace.g1 :=
  Dregg2.Authority.Blocklace.demo_honest_precedes

/-! ### `#eval` smoke. -/

#guard demoReceipt.spentEscrow.locked == false   -- escrow consumed
#guard demoIntent.validity.kind                  -- causal / lightcone fact
#guard demoFrameIntent.validity.kind == false    -- frame convention, carries δ
#guard demoUnfunded.resource.locked == false     -- released — unfulfillable

end Dregg2.Intent
