/-
# Dregg2.Crypto.Temporal — end-to-end §8 discharge for a temporal-window predicate.

Discharges the time-window predicate: the witnessed event time `t` lies in the disclosed closed
interval `[lo, hi]`. The AIR carries a `DIFF` column and a `DIFF_BITS` bit-decomposition
with a high-bit-zero range constraint — the comparison is the bit-decomposition range gadget,
not a hash primitive. The window check `lo ≤ t ≤ hi` is two such comparisons, each
`RecordCircuit.range_iff`. The cascade:

    temporal_bridge       : Satisfies circuit (lo,hi,t) ↔ (lo ≤ t ∧ t ≤ hi)   [fully proved, no primitive seam]
    temporal_verify_sound : verify accepts → (lo ≤ t ∧ t ≤ hi)                  [derived, given STARK extractable]
    temporal_dial_wired   : dial pinned at `selective` floor                     [window disclosed, exact time may be hidden]

There is no `compress`/hash in the temporal gadget: the bounds algebra is pure comparison
combinatorics, fully proved. The only cryptographic residue is the STARK `extractable` carrier.
-/
import Dregg2.Crypto.Primitives
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.Temporal

open Dregg2.Crypto Dregg2.Exec.RecordCircuit

/-! ## The temporal relation — a closed-interval window check.

The witnessed event time `t` lies in `[lo, hi]`: `lo ≤ t ∧ t ≤ hi`. A window is the conjunction of
a lower and an upper threshold (`Gte`/`Lte`). Everything is over `ℤ` (field is `BabyBear` in Rust). -/

/-- **`InWindow lo hi t`** — the temporal statement: the event time `t` lies in the closed interval
`[lo, hi]`. The relation the verifier's accepting bit must certify. -/
def InWindow (lo hi t : Int) : Prop := lo ≤ t ∧ t ≤ hi

/-! ## `CircuitIR` — the temporal AIR's two range gadgets, no primitive seam.

`loBits` decomposes `t - lo` (proving `lo ≤ t`), `hiBits` decomposes `hi - t` (proving `t ≤ hi`).
No `compress`, no hash — pure comparison combinatorics. -/

/-- **The temporal circuit IR** — the trace: the two range-gadget bit-witnesses, one for each side of
the window. `loBits` is the boolean decomposition of `t - lo` (the lower-bound `Gte` gadget),
`hiBits` of `hi - t` (the upper-bound `Lte` gadget). -/
structure CircuitIR where
  /-- Little-endian boolean bits decomposing `t - lo` (the `DIFF_BITS` of the lower-bound gadget). -/
  loBits : List Int
  /-- Little-endian boolean bits decomposing `hi - t` (the `DIFF_BITS` of the upper-bound gadget). -/
  hiBits : List Int
  deriving Repr

/-- `Satisfies circuit lo hi t` — the full temporal AIR check: each side's bits are boolean and
recompose the corresponding difference (`bitsToInt loBits = t - lo`, `bitsToInt hiBits = hi - t`).
Booleanity + recomposition is the `range_iff` gadget; soundness gives `0 ≤ diff`. -/
def Satisfies (circuit : CircuitIR) (lo hi t : Int) : Prop :=
  -- lower-bound gadget: loBits is a boolean decomposition of t - lo (⇒ 0 ≤ t - lo ⇒ lo ≤ t).
  (Boolean circuit.loBits ∧ bitsToInt circuit.loBits = t - lo) ∧
  -- upper-bound gadget: hiBits is a boolean decomposition of hi - t (⇒ 0 ≤ hi - t ⇒ t ≤ hi).
  (Boolean circuit.hiBits ∧ bitsToInt circuit.hiBits = hi - t)

/-! ## The bridge — `Satisfies ↔ InWindow`, fully proved (no primitive seam).

Both directions use `range_iff` from `Exec/RecordCircuit.lean`. No `compress`, no primitive seam. -/

/-- `temporal_sound` (the `→` half): a satisfying trace proves the window via `range_proves_le`
on each side. Fully proved, no crypto. -/
theorem temporal_sound (circuit : CircuitIR) (lo hi t : Int)
    (h : Satisfies circuit lo hi t) : InWindow lo hi t := by
  obtain ⟨⟨hloBool, hloRec⟩, ⟨hhiBool, hhiRec⟩⟩ := h
  refine ⟨?_, ?_⟩
  · -- range_proves_le : Boolean bits → bitsToInt bits = b - a → a ≤ b, with (a,b) = (lo, t).
    exact range_proves_le lo t circuit.loBits hloBool hloRec
  · -- with (a, b) = (t, hi): bitsToInt hiBits = hi - t ⇒ t ≤ hi.
    exact range_proves_le t hi circuit.hiBits hhiBool hhiRec

/-- `temporal_complete` (the `←` half): a genuine window membership yields a satisfying trace via
`range_complete` on each side (canonical `Int.toNat`-based widths). -/
theorem temporal_complete (lo hi t : Int) (h : InWindow lo hi t) :
    ∃ circuit : CircuitIR, Satisfies circuit lo hi t := by
  obtain ⟨hlo, hhi⟩ := h
  -- Non-negative differences, each gets a boolean decomposition at a sufficient bit-width.
  have hlo0 : (0 : Int) ≤ t - lo := by omega
  have hhi0 : (0 : Int) ≤ hi - t := by omega
  -- A width whose 2^width strictly exceeds the difference (the difference fits in `d+1` bits).
  obtain ⟨loBits, _, hloBool, hloRec⟩ :=
    range_complete (t - lo).toNat (t - lo) hlo0 (by
      have : (t - lo) = ((t - lo).toNat : Int) := (Int.toNat_of_nonneg hlo0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  obtain ⟨hiBits, _, hhiBool, hhiRec⟩ :=
    range_complete (hi - t).toNat (hi - t) hhi0 (by
      have : (hi - t) = ((hi - t).toNat : Int) := (Int.toNat_of_nonneg hhi0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  exact ⟨⟨loBits, hiBits⟩, ⟨hloBool, hloRec⟩, ⟨hhiBool, hhiRec⟩⟩

/-- `temporal_bridge` — the temporal AIR's satisfiability is exactly `lo ≤ t ∧ t ≤ hi`. Both
directions proved via `range_proves_le`/`range_complete`. No primitive seam — pure comparison
combinatorics. The only cryptographic residue is the STARK `extractable` carrier. -/
theorem temporal_bridge (lo hi t : Int) :
    (∃ circuit : CircuitIR, Satisfies circuit lo hi t) ↔ InWindow lo hi t :=
  ⟨fun ⟨c, hc⟩ => temporal_sound c lo hi t hc, temporal_complete lo hi t⟩

-- Tripwires: the temporal gadget is fully proved with no primitive seam.
#assert_axioms temporal_sound
#assert_axioms temporal_complete
#assert_axioms temporal_bridge

/-! ## Layer B — the temporal `VerifierKernel`: `verify` + carrier + derived `verify_sound`.

`verify` is the §8 oracle over the disclosed `(lo, hi, t)`; `extractable` gives "accept ⇒ a
satisfying trace exists"; `temporal_verify_sound` is derived off the bridge. -/

/-- The public inputs the verifier sees: the window bounds `(lo, hi)` and the event time `t`. At the
`selective` floor the window is disclosed; the exact time may be the hidden witness. -/
structure Statement where
  /-- The lower window bound (public). -/
  lo : Int
  /-- The upper window bound (public). -/
  hi : Int
  /-- The witnessed event time. -/
  t : Int
  deriving Repr

/-- The temporal `VerifierKernel`. `verify` is the §8 oracle; `extractable` is the STARK-soundness
carrier; `extract` unpacks it — an accepted proof witnesses a satisfying trace. No commitment, no
hash: the only assumption is STARK extractability. -/
class TemporalVerifierKernel (Proof : Type) where
  /-- The §8 verify oracle: does `proof` discharge the disclosed window statement `(lo, hi, t)`? -/
  verify : Statement → Proof → Bool
  /-- CARRIER — STARK extractability/soundness (FRI + Fiat-Shamir): accept ⇒ a satisfying trace
  exists. A `Prop`; never proved. -/
  extractable : Prop
  /-- `extractable` unpacked: an accepted proof witnesses a satisfying temporal trace. -/
  extract : extractable →
    ∀ (stmt : Statement) (proof : Proof), verify stmt proof = true →
      ∃ circuit : CircuitIR, Satisfies circuit stmt.lo stmt.hi stmt.t

variable {Proof : Type}

/-- `temporal_verify_sound` — given `extractable`, an accepted proof proves the event time lies in the
window: `verify stmt proof = true → InWindow stmt.lo stmt.hi stmt.t`. Derived by composing `extract`
with `temporal_bridge`'s soundness half. The only hypothesis is `extractable`. -/
theorem temporal_verify_sound [K : TemporalVerifierKernel Proof]
    (hext : K.extractable) (stmt : Statement) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    InWindow stmt.lo stmt.hi stmt.t := by
  obtain ⟨circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact (temporal_bridge stmt.lo stmt.hi stmt.t).1 ⟨circuit, hsat⟩

#assert_axioms temporal_verify_sound

/-! ## Layer C — the kind obligation + dial wiring at the `selective` floor.

The window `[lo, hi]` is disclosed but the exact event time `t` may be blinded. The epistemic floor
is therefore `selective` (chosen facts — the window — plus the conclusion): not `acceptanceOnly`
(which would hide the window) and not `fullDisclosure` (which would reveal the exact time). Parallels
Pedersen, which also sits at `selective`. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- `KindObligation` for temporal: statement = `Statement`, dial floor = `selective` (window
disclosed, exact event time may be hidden). -/
structure KindObligation where
  /-- The public-input algebra: the disclosed window + time. -/
  Statement : Type
  /-- The dial floor — `selective` for temporal (window disclosed, time may be blinded). -/
  dialFloor : Dial

/-- The temporal kind's obligation: statement = the disclosed window/time, floor = `selective`. -/
def temporalKindObligation : KindObligation where
  Statement := Statement
  dialFloor := Dial.selective

@[simp] theorem temporalKindObligation_floor :
    temporalKindObligation.dialFloor = Dial.selective := rfl

/-- `selective` is strictly above `acceptanceOnly`: the temporal proof discloses more than one bit
(it reveals the window). -/
theorem temporal_floor_above_bot :
    (⊥ : Dial) < temporalKindObligation.dialFloor := by
  show Dial.acceptanceOnly < Dial.selective
  exact Dial.acceptanceOnly_lt_selective

/-! ### Dial wiring — `DiscloseAt` instantiated at the temporal verifier's `selective` floor. -/

section Wiring

variable {P : Type}

/-- A `Verifier Statement P` from the kernel's §8 `verify` oracle. -/
def temporalVerifier [K : TemporalVerifierKernel P] : Verifier Statement P :=
  fun stmt proof => K.verify stmt proof

/-- The temporal-kind registry: the §8 `verify` oracle installed at `temporal`. -/
def temporalReg [TemporalVerifierKernel P]
    (base : Registry Statement P) : Registry Statement P :=
  fun j => if j = .temporal then some temporalVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `def`, not auto-synthesized). -/
@[reducible] def temporalSeam [TemporalVerifierKernel P]
    (base : Registry Statement P) : Verifiable Statement P :=
  verifiableOfRegistry (temporalReg base) .temporal

/-- `temporalDisclose` — a `DiscloseAt` whose `accepts d := Discharged stmt proof` (position-
independent). Realizes the dial at the `selective` (window disclosed, exact time may be blinded)
floor. -/
def temporalDisclose [TemporalVerifierKernel P]
    (base : Registry Statement P) (stmt : Statement) (proof : P) :
    @DiscloseAt Unit Statement P _ (temporalSeam base) :=
  letI : Verifiable Statement P := temporalSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- `temporal_dial_wired` — the temporal kind's floor is `selective`; the dial's bottom notch's
acceptance bit is the temporal verifier's `Discharged` bit; and given STARK `extractable`, an
accepting proof proves window membership. The dial is pinned to the per-kind verifier. -/
theorem temporal_dial_wired [K : TemporalVerifierKernel P]
    (hext : K.extractable)
    (base : Registry Statement P) (stmt : Statement) (proof : P) :
    -- (1) the floor is selective:
    temporalKindObligation.dialFloor = Dial.selective ∧
    -- (2) the dial's bottom notch accepts IFF the temporal verifier discharges:
    (@DiscloseAt.accepts Unit Statement P _ (temporalSeam base)
        (temporalDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged Statement P (temporalSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES the window membership (the cascade):
    (K.verify stmt proof = true → InWindow stmt.lo stmt.hi stmt.t) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit Statement P _ (temporalSeam base)
      (temporalDisclose base stmt proof)
  · exact fun haccept => temporal_verify_sound hext stmt proof haccept

/-- `temporal_registry_cascade` — an accepted proof both `Discharged`s the registry predicate and,
given STARK `extractable`, proves window membership. The single trust boundary is `extractable`. -/
theorem temporal_registry_cascade [K : TemporalVerifierKernel P]
    (hext : K.extractable)
    (base : Registry Statement P)
    (stmt : Statement) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged Statement P (verifiableOfRegistry (temporalReg base) .temporal) stmt proof)
      ∧ InWindow stmt.lo stmt.hi stmt.t := by
  refine ⟨?_, temporal_verify_sound hext stmt proof haccept⟩
  apply registry_sound (temporalReg base) .temporal stmt proof
  show registryVerify (temporalReg base) .temporal stmt proof = true
  unfold registryVerify temporalReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms temporal_dial_wired
#assert_axioms temporal_registry_cascade

/-! ## Reference — non-vacuity witnesses over `ℤ`.

A degenerate temporal verifier kernel `def` (not a global `instance`, to avoid silent
auto-resolution) witnessing the bridge / verify-sound / cascade end-to-end. Not real crypto. -/

namespace Reference

/-- A concrete window/time over `ℤ`: window `[10, 20]`, event time `15` — inside. -/
def sampleStmt : Statement := { lo := 10, hi := 20, t := 15 }

/-- Non-vacuity of the BRIDGE: `15 ∈ [10, 20]`, so a satisfying trace exists (via `temporal_complete`,
the two boolean decompositions of `15 - 10 = 5` and `20 - 15 = 5`). -/
example : ∃ circuit : CircuitIR, Satisfies circuit 10 20 15 :=
  temporal_complete 10 20 15 ⟨by norm_num, by norm_num⟩

/-- Non-vacuity of the SOUNDNESS heart: any satisfying trace for `(10, 20, 15)` proves `15 ∈ [10, 20]`.
We exhibit a concrete trace (`loBits = bits of 5`, `hiBits = bits of 5`) and run `temporal_sound`. -/
example : InWindow 10 20 15 := by
  obtain ⟨circuit, hsat⟩ := temporal_complete 10 20 15 ⟨by norm_num, by norm_num⟩
  exact temporal_sound circuit 10 20 15 hsat

/-- A degenerate reference temporal verifier kernel over `ℤ` (`def`, not a global `instance`).
`verify` accepts iff `stmt.lo ≤ stmt.t ∧ stmt.t ≤ stmt.hi` (the decidable window check directly);
`extractable := True`. `extract` rebuilds the satisfying trace from the accepted window via
`temporal_complete`. -/
@[reducible] def refKernel : TemporalVerifierKernel Int where
  verify stmt _ := decide (stmt.lo ≤ stmt.t ∧ stmt.t ≤ stmt.hi)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    simp only [decide_eq_true_eq] at haccept
    exact temporal_complete stmt.lo stmt.hi stmt.t haccept

/-- The empty base registry over the toy `ℤ` temporal statement/proof. -/
def base : Registry Statement Int := fun _ => none

/-- Non-vacuity of `temporal_verify_sound`: an accepted proof proves the event lies in the window. -/
example : InWindow sampleStmt.lo sampleStmt.hi sampleStmt.t :=
  temporal_verify_sound (K := refKernel) trivial sampleStmt 0 (by decide)

/-- Non-vacuity of the full cascade: an accepted proof both `Discharged`s the registry predicate and
proves window membership. Named so its axiom footprint is checkable with `#print axioms`. -/
theorem reference_cascade_nonvacuous :
    (@Discharged Statement Int
        (verifiableOfRegistry (@temporalReg Int refKernel base) .temporal) sampleStmt 0)
      ∧ InWindow sampleStmt.lo sampleStmt.hi sampleStmt.t :=
  temporal_registry_cascade (K := refKernel) trivial base sampleStmt 0 (by decide)

-- The reference cascade rests only on the three standard kernel axioms — no `sorryAx`, no crypto axiom.
#print axioms reference_cascade_nonvacuous

/-- Non-vacuity of the dial wiring: the floor is `selective`, the dial's bottom notch is the verifier's
bit, and an accepting proof proves the window membership. -/
example : temporalKindObligation.dialFloor = Dial.selective :=
  (temporal_dial_wired (K := refKernel) trivial base sampleStmt 0).1

end Reference

-- No primitive seam
-- anywhere (no hash/commitment in the temporal predicate). Only cryptographic residue is the
-- `extractable` carrier (passed as a hypothesis).
#assert_axioms temporal_bridge
#assert_axioms temporal_verify_sound
#assert_axioms temporal_registry_cascade
#assert_axioms temporal_dial_wired

end Dregg2.Crypto.Temporal
