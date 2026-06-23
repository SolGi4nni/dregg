/-
# Dregg2.Exec.CrossVatCharter — cross-vat charters as the common bilateral+credential pattern.

A **charter** packages what production cross-vat maneuvers need together:

  1. a **coordinated covenant** `φ` (reads BOTH ledgers — discharged via the atomic equalizer);
  2. a **bilateral turn** `bt` over `{A, B}` (the joint maneuver);
  3. **biscuit credentials** on each vat leg (public-key, cross-vat verifiable — macaroons are
     rejected by the Φ-domain law).

This is the executable glue between `Exec.VatBoundary` (cross-vat token discharge on a living cell),
`Exec.CoordinatedCaveat` (the `.coordinated` tier's positive equalizer discharge), and
`Exec.CrossCaveat` (the no-TOCTOU cross-cell read). Charters are the reusable template Apps should
copy: covenant ∧ biscuits ∧ bilateral commit.

Crypto soundness stays in §8 carriers.
-/
import Dregg2.Exec.VatBoundary
import Dregg2.Exec.CoordinatedCaveat

namespace Dregg2.Exec.CrossVatCharter

open Dregg2.Authority
open Dregg2.Exec (Req actorIs0 vatAdmits)
open Dregg2.Exec.JointCell
open Dregg2.Exec.CrossCaveat
open Dregg2.Exec.CoordinatedCaveat

/-! ## §1 — The charter carrier. -/

/-- A **cross-vat charter** — the common pattern for an authorized bilateral maneuver across two
trust roots. The coordinated covenant `φ` forces a joint (equalized) turn; each vat presents a
**biscuit** (never a macaroon) authorizing its actor at the stated chain height. -/
structure Charter where
  /-- The coordinated cross-cell covenant (the `.coordinated` tier's equalizer target). -/
  covenant : CoordinatedCaveat
  /-- The bilateral maneuver over ledgers `(A, B)`. -/
  bt       : BiTurn
  /-- Biscuit credential authorizing the A-side actor at the crossing. -/
  biscuitA : Token Req Unit
  /-- Biscuit credential authorizing the B-side actor at the crossing. -/
  biscuitB : Token Req Unit

/-- Request contexts recovered from the bilateral turn at each vat's chain height. -/
def reqA (ch : Charter) (heightA : Nat) : Req :=
  { actor := ch.bt.actorA, height := heightA }

def reqB (ch : Charter) (heightB : Nat) : Req :=
  { actor := ch.bt.actorB, height := heightB }

/-- **`charterAdmits`** — the charter's admission decision BEFORE the equalizer commit: both biscuits
discharge their leg's request, both are cross-vat verifiable (biscuits only), AND the coordinated
covenant `φ` holds on the joint kernel pre-state `(A, B)`. -/
def charterAdmits (ch : Charter) (A B : KernelState) (heightA heightB : Nat)
    (dA dB : Discharges Unit) : Bool :=
  ch.biscuitA.crossVatVerifiable &&
  ch.biscuitB.crossVatVerifiable &&
  ch.biscuitA.admits (reqA ch heightA) dA &&
  ch.biscuitB.admits (reqB ch heightB) dB &&
  ch.covenant.φ A B

/-- **`charterDischarge`** — commit the bilateral equalizer ONLY when the charter admits on the SAME
atomic pre-state. Fail-closed on any leg. -/
def charterDischarge (ch : Charter) (A B : KernelState) (heightA heightB : Nat)
    (dA dB : Discharges Unit) : Option (KernelState × KernelState) :=
  if charterAdmits ch A B heightA heightB dA dB then
    dischargeCoordinated ch.covenant A B ch.bt
  else none

/-! ## §2 — The keystones. -/

/-- **`charter_macaroon_rejected`** — macaroons are NOT charter carriers: they fail the cross-vat
verifiability leg (`macaroon_not_crossvat`), matching the Φ-domain law. -/
theorem charter_macaroon_rejected (ch : Charter) (A B : KernelState) (heightA heightB : Nat)
    (dA dB : Discharges Unit) (h : ch.biscuitA.kind = .macaroon ∨ ch.biscuitB.kind = .macaroon) :
    charterAdmits ch A B heightA heightB dA dB = false := by
  unfold charterAdmits
  rcases h with hA | hB
  · have hcv := macaroon_not_crossvat ch.biscuitA hA
    rw [hcv]
    simp [Token.crossVatVerifiable]
  · have hcv := macaroon_not_crossvat ch.biscuitB hB
    rw [hcv]
    simp [Token.crossVatVerifiable]

/-- **`charter_discharge_sound`** — a committed charter discharge is sound: CG-5 conservation,
CG-2 binding, and `φ` on the atomic snapshot. Direct reuse of `coordinated_discharge_sound`. -/
theorem charter_discharge_sound (ch : Charter) {A B A' B' : KernelState} (bind : SharedBinding ch.bt)
    (heightA heightB : Nat) (dA dB : Discharges Unit)
    (h : charterDischarge ch A B heightA heightB dA dB = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧ bind.sidOfA = bind.sidOfB ∧ ch.covenant.φ A B = true := by
  unfold charterDischarge at h
  by_cases hadm : charterAdmits ch A B heightA heightB dA dB
  · rw [if_pos hadm] at h
    exact coordinated_discharge_sound ch.covenant bind h
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`charter_no_toctou`** — the covenant check and the bilateral commit read the SAME `(A, B)`. -/
theorem charter_no_toctou (ch : Charter) {A B A' B' : KernelState}
    (heightA heightB : Nat) (dA dB : Discharges Unit)
    (h : charterDischarge ch A B heightA heightB dA dB = some (A', B')) :
    ch.covenant.φ A B = true ∧ jointApply A B ch.bt = some (A', B') :=
  coordinated_no_toctou ch.covenant (by
    unfold charterDischarge at h
    by_cases hadm : charterAdmits ch A B heightA heightB dA dB
    · rw [if_pos hadm] at h; exact h
    · rw [if_neg hadm] at h; exact absurd h (by simp))

/-! ## §3 — Demo charter + `#guard` witnesses. -/

/-- A biscuit caveated to a specific actor (the cross-vat leg authorizer). -/
def actorBiscuit (n : Nat) : Token Req Unit :=
  { kind := .biscuit, caveats := [.opaque (fun r => decide (r.actor = n))] }

/-- The standard HTLC-style covenant charter: `covenantCoord` + `goodBi` + per-leg actor biscuits. -/
def demoCharter : Charter :=
  { covenant := covenantCoord, bt := goodBi
  , biscuitA := actorBiscuit 0, biscuitB := actorBiscuit 7 }

def noDischarges : Discharges Unit := fun _ => false

theorem demoCharter_admits_high_false :
    charterAdmits demoCharter sA sBhigh 0 0 noDischarges noDischarges = false := by
  unfold charterAdmits demoCharter actorBiscuit covenantCoord covenant noDischarges
    Token.crossVatVerifiable Token.admits Caveat.ok
  decide

/-- **`charter_covenant_teeth`** — a violated covenant rejects the charter EVEN IF the raw bilateral
would commit. -/
theorem charter_covenant_teeth :
    charterDischarge demoCharter sA sBhigh 0 0 noDischarges noDischarges = none := by
  simp [charterDischarge, if_neg, Bool.not_eq_true', demoCharter_admits_high_false]

#guard (charterAdmits demoCharter sA sB 0 0 noDischarges noDischarges)  --  true
#guard (charterAdmits demoCharter sA sBhigh 0 0 noDischarges noDischarges) == false  --  covenant violated
#guard ((charterDischarge demoCharter sA sB 0 0 noDischarges noDischarges).isSome)  --  commits
#guard ((charterDischarge demoCharter sA sBhigh 0 0 noDischarges noDischarges).isSome) == false  --  rejects

/-! ## §4 — Axiom hygiene. -/

#assert_axioms charter_macaroon_rejected
#assert_axioms charter_discharge_sound
#assert_axioms charter_no_toctou
#assert_axioms charter_covenant_teeth

end Dregg2.Exec.CrossVatCharter