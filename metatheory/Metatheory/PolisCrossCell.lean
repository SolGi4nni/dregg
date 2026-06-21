/-
# Metatheory.PolisCrossCell — the shared adversary-stream carrier (polis ∥ circuit, separate preds).

gpt5.5's answer to Q6 (`docs/POLIS-HYPERPROPERTY-FRONTIER.md`): the polis anti-capture floor and
circuit cross-cell soundness are NOT the same property — but they share a carrier: properties of
public interleaved adversary STREAMS. Build the generic framework + the shared **monitorability**
decision fragment; keep the two predicates DISTINCT (collapsing them would prove circuit confluence
and falsely claim anti-tyranny). Deployment: instantiate `polisFloorProp` from
`PolisSelfCompose.dominationBar` lifted to streams, and `circuitSoundnessProp` from the deployed
`CoinductiveAdversary` confluence; share `violation_has_finite_witness`, never the predicate.

Pure Lean 4 core (imports only the import-free `Metatheory.Polis`); no `sorry`.
-/
import Metatheory.Polis

namespace Metatheory.PolisCrossCell

variable {Event : Type}

/-- The shared carrier: a property of a public interleaved adversary stream. -/
def StreamProp (Event : Type) := (Nat → Event) → Prop

/-- A **monitorability** witness for a stream property `P`: a public length-`n` prefix predicate
`bad` (reading only `σ 0 … σ (n-1)`) that is SOUND (a bad prefix forces a violation) and COMPLETE
(every violation has a bad prefix). This is the safety / bounded-liveness fragment — a finite public
witness governs the property, no interior, no need to observe the infinite stream. The shared
decision fragment both frontiers reuse. -/
structure Monitorable (P : StreamProp Event) where
  bad : (Nat → Event) → Nat → Prop
  sound : ∀ σ n, bad σ n → ¬ P σ
  complete : ∀ σ, ¬ P σ → ∃ n, bad σ n

/-- **Monitorability ⇒ a finite public witness for every violation.** Any stream violating a
monitorable `P` has a finite bad prefix — governable from a finite public trace. -/
theorem violation_has_finite_witness {P : StreamProp Event} (M : Monitorable P)
    (σ : Nat → Event) (h : ¬ P σ) : ∃ n, M.bad σ n :=
  M.complete σ h

/-! ### Non-vacuity: a concrete monitorable property (so the framework has a model). -/

/-- A safety property: the stream never emits `false`. -/
def neverFalse : StreamProp Bool := fun σ => ∀ n, σ n = true

/-- It is monitorable — the bad prefix is "some position `< n` already failed `= true`". -/
def neverFalseMon : Monitorable neverFalse where
  bad σ n := ∃ i, i < n ∧ σ i ≠ true
  sound := fun _ _ => fun ⟨i, _, hi⟩ hp => hi (hp i)
  complete := fun σ h =>
    let key : ∃ n, σ n ≠ true :=
      Classical.byContradiction (fun hc =>
        h (fun n => Classical.byContradiction (fun hn => hc ⟨n, hn⟩)))
    match key with
    | ⟨n, hn⟩ => ⟨n + 1, n, Nat.lt_succ_self n, hn⟩

/-- The framework is inhabited: the all-`false` stream violates `neverFalse`, and the witness
theorem produces its finite bad prefix. -/
example : ∃ n, neverFalseMon.bad (fun _ => false) n :=
  violation_has_finite_witness neverFalseMon (fun _ => false)
    (fun hp => absurd (hp 0) (by decide))

end Metatheory.PolisCrossCell
