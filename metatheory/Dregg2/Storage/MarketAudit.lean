/-
# `Dregg2.Storage.MarketAudit` — the audit drives the lifecycle: honest ⇒ safe, withholding ⇒ slashed.

The end-to-end market-integrity composition. `Retrievability.por_sound` proves a provider that PASSES
the proof-of-retrievability audit genuinely holds the committed data (and `por_refuses_substitution`
that a forgery cannot pass). `DealLifecycle` proves the deal's transitions are sound. THIS ties them:
the PoR verdict drives the audit transition, so —
* an HONEST provider (audit passes) can NEVER be slashed, and
* a WITHHOLDING provider (audit fails) IS slashable.

The `porPassed` bit is exactly the `Retrievability.passes` verdict the executor computes from the real
openings; `por_sound` is what makes "passed" mean "genuinely holds the data". So the honest provider
keeps its bond *because the audit it passed was sound*, and the tooth only bites real withholding.
-/
import Dregg2.Storage.DealLifecycle

namespace Dregg2.Storage.MarketAudit

open Dregg2.Storage.DealLifecycle

/-- Run the market audit on an active deal: a PASSING proof-of-retrievability (`porPassed = true`,
i.e. `Retrievability.passes`) moves the deal to `auditedPass` (settleable); a FAILING one to
`auditedFail` (slashable). -/
def runAudit (d : Deal) (porPassed : Bool) : Option Deal :=
  match porPassed with
  | true => auditPass d
  | false => auditFail d

/-- **An HONEST provider is never slashed.** If the PoR audit PASSED on an active deal, the deal
reaches `auditedPass`, from which `slash` is IMPOSSIBLE (its guard demands `auditedFail`). Composed
with `Retrievability.por_sound` — "passed" means the provider genuinely holds the data — this says: a
provider that actually holds what it committed keeps its bond, always. -/
theorem honest_provider_not_slashed (d d' : Deal) (hactive : d.state = .active)
    (h : runAudit d true = some d') (p : Nat) : slash d' p = none := by
  simp only [runAudit, auditPass, hactive, Option.some.injEq] at h
  subst h
  simp [slash]

/-- **Withholding IS slashable.** If the PoR audit FAILED on an active deal, the deal reaches
`auditedFail`, from which a slash succeeds — the economic tooth bites a provider that could not answer
the challenge (by `por_refuses_substitution`, it could not have faked a pass). -/
theorem withholding_is_slashable (d d' : Deal) (hactive : d.state = .active)
    (h : runAudit d false = some d') (p : Nat) :
    slash d' p = some { state := .slashed, bond := d'.bond - p } := by
  simp only [runAudit, auditFail, hactive, Option.some.injEq] at h
  subst h
  simp [slash]

#assert_axioms honest_provider_not_slashed
#assert_axioms withholding_is_slashable

end Dregg2.Storage.MarketAudit
