/-
# `Dregg2.Storage.DealLifecycle` — the storage-market deal as a PROVEN state machine (protocol spec).

The market's temporal spine, `Open → Claimed → Active → Audited{Pass|Fail} → {Settled | Slashed}`,
as an abstract state machine with its soundness proved — the "reason about the whole protocol"
artifact. `ProviderMarket.lean` is the executor-wired cell-program (field slots + claim/slash guards);
THIS is the protocol it refines: the full lifecycle with per-transition guards, terminal finality,
bond monotonicity, and the reachability fact that a slashed deal's history REQUIRED a failed audit.

Every transition is a partial function (returns `none` unless its guard holds), so an illegal
step is unrepresentable. The proofs are the market's temporal guarantees: you cannot settle without
a passing audit, cannot slash without a failing one, cannot move a terminal deal, and the bond only
ever shrinks (never conjured).
-/
import Dregg2.Tactics

namespace Dregg2.Storage.DealLifecycle

/-- The lifecycle states. `auditedPass`/`auditedFail` are the two audit outcomes that route to the
two terminals. -/
inductive DealState where
  | open        -- posted by a client; no provider yet
  | claimed     -- a bonded provider took it (bond locked)
  | active      -- data stored (root committed), serving reads
  | auditedPass -- a proof-of-retrievability audit PASSED
  | auditedFail -- a proof-of-retrievability audit FAILED
  | settled     -- provider paid, bond released (happy terminal)
  | slashed     -- bond burned (sad terminal)
deriving DecidableEq, Repr

/-- A deal: its lifecycle state and the provider's locked collateral bond. -/
structure Deal where
  state : DealState
  bond : Nat
deriving DecidableEq, Repr

/-- The two terminal states admit no further transition. -/
def isTerminal : DealState → Bool
  | .settled | .slashed => true
  | _ => false

/-! ## §1 — transitions (partial: `none` unless the guard holds). -/

/-- `Open → Claimed`: a provider claims the deal, locking bond `b`. -/
def claim (d : Deal) (b : Nat) : Option Deal :=
  match d.state with
  | .open => some { state := .claimed, bond := b }
  | _ => none

/-- `Claimed → Active`: the provider stores the data + commits the root. -/
def activate (d : Deal) : Option Deal :=
  match d.state with
  | .claimed => some { d with state := .active }
  | _ => none

/-- `Active → AuditedPass`: a proof-of-retrievability audit succeeds. -/
def auditPass (d : Deal) : Option Deal :=
  match d.state with
  | .active => some { d with state := .auditedPass }
  | _ => none

/-- `Active → AuditedFail`: a proof-of-retrievability audit fails. -/
def auditFail (d : Deal) : Option Deal :=
  match d.state with
  | .active => some { d with state := .auditedFail }
  | _ => none

/-- `AuditedPass → Settled`: the provider is paid; the bond is RELEASED (returned, unchanged). -/
def settle (d : Deal) : Option Deal :=
  match d.state with
  | .auditedPass => some { d with state := .settled }
  | _ => none

/-- `AuditedFail → Slashed`: the bond is BURNED by `penalty` (the economic tooth). -/
def slash (d : Deal) (penalty : Nat) : Option Deal :=
  match d.state with
  | .auditedFail => some { state := .slashed, bond := d.bond - penalty }
  | _ => none

/-- One protocol step — any legal transition. Illegal steps are unrepresentable (the constructors
carry `= some d'`). -/
inductive Step : Deal → Deal → Prop where
  | claim {d b d'} : claim d b = some d' → Step d d'
  | activate {d d'} : activate d = some d' → Step d d'
  | auditPass {d d'} : auditPass d = some d' → Step d d'
  | auditFail {d d'} : auditFail d = some d' → Step d d'
  | settle {d d'} : settle d = some d' → Step d d'
  | slash {d p d'} : slash d p = some d' → Step d d'

/-! ## §2 — soundness proofs. -/

/-- **Terminal finality.** A settled or slashed deal admits NO step — the deal is done. -/
theorem terminal_is_final (d d' : Deal) (ht : isTerminal d.state = true) : ¬ Step d d' := by
  intro hstep
  cases hstep <;>
    rename_i h <;>
    · simp only [claim, activate, auditPass, auditFail, settle, slash] at h
      cases hs : d.state <;> simp [hs, isTerminal] at ht h

/-- **Settle requires a passing audit** (and releases the bond unchanged). You cannot pay a provider
whose retrievability audit did not pass. -/
theorem settle_requires_passed_audit (d d' : Deal) (h : settle d = some d') :
    d.state = .auditedPass ∧ d'.bond = d.bond ∧ d'.state = .settled := by
  simp only [settle] at h
  cases hs : d.state <;> simp [hs] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- **Slash requires a failing audit** and STRICTLY concerns a burn. You cannot slash a provider
whose audit did not fail. -/
theorem slash_requires_failed_audit (d d' : Deal) (p : Nat) (h : slash d p = some d') :
    d.state = .auditedFail ∧ d'.bond = d.bond - p ∧ d'.state = .slashed := by
  simp only [slash] at h
  cases hs : d.state <;> simp [hs] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- **The bond is never conjured once locked.** After the deal leaves `open` (the only step that
SETS the bond is `claim`, which locks it), every step leaves the collateral unchanged (activate /
audit / settle) or strictly smaller (slash) — a provider's bond can't grow mid-deal, and value isn't
created. -/
theorem bond_nonincreasing_after_claim (d d' : Deal) (h : Step d d') (hopen : d.state ≠ .open) :
    d'.bond ≤ d.bond := by
  cases h with
  | claim h => simp only [claim] at h; cases hs : d.state <;> simp only [hs] at h hopen <;> simp_all
  | activate h =>
    simp only [activate] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp)
  | auditPass h =>
    simp only [auditPass] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp)
  | auditFail h =>
    simp only [auditFail] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp)
  | settle h =>
    simp only [settle] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp)
  | slash h =>
    simp only [slash] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp)


#assert_axioms terminal_is_final
#assert_axioms settle_requires_passed_audit
#assert_axioms slash_requires_failed_audit
#assert_axioms bond_nonincreasing_after_claim

end Dregg2.Storage.DealLifecycle
