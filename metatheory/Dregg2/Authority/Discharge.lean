/-
# Dregg2.Authority.Discharge — discharge monotonicity for the await authority-face.

A **third-party caveat** suspends a cross-vat turn until a named gateway discharges it.
Discharges only accumulate: a settled gateway stays settled, so resolution moves strictly
forward. This module proves that monotonicity on `Token.admits` in the `Discharges`
parameter (`admits_mono_discharge`), building on `Authority.Caveat`.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Caveat

namespace Dregg2.Authority

open Dregg2.Laws

variable {Ctx : Type}
variable {Gateway : Type}

/-! ## The order on discharges: discharges only accumulate (a settled gateway stays settled). -/

/-- **`Discharges.le d d'`** — `d'` has *at least as many* discharges as `d`: every gateway
that has settled under `d` is still settled under `d'`. This is the forward-only order on the
await authority-face — time can add discharges but never retract one (a settled gateway is
permanent, the ▶-guarded "resolve forward"). -/
def Discharges.le (d d' : Discharges Gateway) : Prop :=
  ∀ g, d g = true → d' g = true

/-- `Discharges.le` is reflexive (the present moment has the discharges it has). -/
theorem Discharges.le_refl (d : Discharges Gateway) : Discharges.le d d :=
  fun _ h => h

/-- `Discharges.le` is transitive (discharges accumulated across two intervals accumulate). -/
theorem Discharges.le_trans {d d' d'' : Discharges Gateway}
    (h₁ : Discharges.le d d') (h₂ : Discharges.le d' d'') : Discharges.le d d'' :=
  fun g hg => h₂ g (h₁ g hg)

/-! ## A satisfied caveat stays satisfied as discharges accumulate. -/

/-- **`caveat_ok_mono`** — a satisfied caveat stays satisfied as discharges accumulate. A
local caveat ignores discharges (trivially preserved); a third-party caveat is satisfied iff
its gateway has discharged, and discharges only grow, so by `Discharges.le` it stays
satisfied. -/
theorem caveat_ok_mono (c : Caveat Ctx Gateway) (ctx : Ctx)
    {d d' : Discharges Gateway} (hle : Discharges.le d d')
    (h : c.ok ctx d = true) : c.ok ctx d' = true := by
  cases c with
  | «local» check =>
    -- the local check is independent of the discharges
    simpa [Caveat.ok] using h
  | thirdParty g =>
    -- a discharged gateway stays discharged
    simp only [Caveat.ok] at h ⊢
    exact hle g h

/-! ## Admissibility resolves forward, never un-resolves. -/

/-- **`admits_mono_discharge`** — if `d'` accumulates the discharges of `d`, any request the
token admits under `d` it still admits under `d'`. A suspended cross-vat turn, once a gateway
settles it, stays admissible. Proof: `Token.admits` is the `List.all` of `Caveat.ok` over the
caveat chain; each conjunct is monotone by `caveat_ok_mono`, pushed through memberwise. -/
theorem admits_mono_discharge (tok : Token Ctx Gateway) (ctx : Ctx)
    {d d' : Discharges Gateway} (hle : Discharges.le d d')
    (h : tok.admits ctx d = true) : tok.admits ctx d' = true := by
  simp only [Token.admits, List.all_eq_true] at h ⊢
  intro c hc
  exact caveat_ok_mono c ctx hle (h c hc)

/-- **`admits_mono_subset`** — as discharges accumulate, the admissible-request set only grows.
Dual in polarity to `attenuate_subset`: along the delegation axis authority narrows; along the
discharge/time axis admissibility widens. -/
theorem admits_mono_subset (tok : Token Ctx Gateway)
    {d d' : Discharges Gateway} (hle : Discharges.le d d') :
    {ctx | tok.admits ctx d = true} ⊆ {ctx | tok.admits ctx d' = true} :=
  fun ctx h => admits_mono_discharge tok ctx hle h

/-! ## Awaiting — a suspended / blocked cross-vat turn (a zkpromise / ConditionalTurn). -/

/-- **`Awaiting tok ctx d`** — the token does NOT admit the request under the current
discharges: a *suspended* cross-vat turn, blocked waiting for a gateway to settle. This is the
proposition-level `zkpromise` / `ConditionalTurn` — the turn exists but is not yet live. -/
def Awaiting (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Prop :=
  tok.admits ctx d = false

/-- `Awaiting` is decidable (admissibility is a `Bool`), so "is this turn still suspended?" is a
runnable check — the scheduler can poll it. -/
instance (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) :
    Decidable (Awaiting tok ctx d) :=
  inferInstanceAs (Decidable (_ = false))

/-! ## The resolution theorem — a suspended turn becomes admissible once gateways discharge. -/

/-- The single gateway-discharge step: flip gateway `g` to settled, leaving every other
gateway as it was. The forward-only update that resolves a third-party caveat. -/
def Discharges.settle (d : Discharges Gateway) [DecidableEq Gateway] (g : Gateway) :
    Discharges Gateway :=
  fun g' => if g' = g then true else d g'

/-- **`settle_le`** — settling a gateway is a forward step: `d ≤ d.settle g`. Settling adds
the discharge of `g` and retracts nothing, so it is always a legal move in the
accumulating-discharge order. -/
theorem settle_le [DecidableEq Gateway] (d : Discharges Gateway) (g : Gateway) :
    Discharges.le d (d.settle g) := by
  intro g' hg'
  simp only [Discharges.settle]
  split <;> simp_all

/-- **`settle_discharges`** — after settling `g`, gateway `g` reads as discharged. -/
theorem settle_discharges [DecidableEq Gateway] (d : Discharges Gateway) (g : Gateway) :
    (d.settle g) g = true := by
  simp [Discharges.settle]

/-- **`resolve_forward`** — a turn suspended on gateway `g` becomes admissible the moment `g`
discharges. If the parent token admits under `d`, then attaching a third-party caveat on `g`
yields a token that admits after `g` settles (`d.settle g`). -/
theorem resolve_forward [DecidableEq Gateway]
    (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) (g : Gateway)
    (hpar : tok.admits ctx d = true) :
    (tok.attenuate (.thirdParty g)).admits ctx (d.settle g) = true := by
  -- the suspended turn = parent ∧ (third-party g)
  simp only [Token.admits, Token.attenuate, List.all_append, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- the parent's caveats stay satisfied as `d → d.settle g` (the keystone, applied to the chain)
    have hpar' : tok.admits ctx (d.settle g) = true :=
      admits_mono_discharge tok ctx (settle_le d g) hpar
    simpa [Token.admits, List.all_eq_true] using hpar'
  · -- the new third-party caveat: gateway g has now discharged
    simp only [Caveat.ok]
    exact ⟨settle_discharges d g, trivial⟩

/-- **`awaiting_resolves`** — a turn that was `Awaiting` on gateway `g` is no longer suspended
after `g` discharges, provided the parent admitted. -/
theorem awaiting_resolves [DecidableEq Gateway]
    (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) (g : Gateway)
    (hpar : tok.admits ctx d = true) :
    ¬ Awaiting (tok.attenuate (.thirdParty g)) ctx (d.settle g) := by
  unfold Awaiting
  rw [resolve_forward tok ctx d g hpar]
  simp

/-! ## `#eval` demos: blocked → admitted → never un-admitted. -/

/-- Two gateways for demo purposes (an oracle and a co-signer). -/
inductive GW where
  | oracle
  | cosigner
  deriving DecidableEq, Repr

/-- A root biscuit windowed to `[100,200]`, then **suspended** on gateway `oracle`: a cross-vat
turn that cannot become live until the oracle gateway discharges it. -/
def suspendedTurn : Token Height GW :=
  ((({ kind := .biscuit, caveats := [] } : Token Height GW)
      |>.attenuate (.local (fun h => decide (100 ≤ h))))
      |>.attenuate (.local (fun h => decide (h ≤ 200))))
      |>.attenuate (.thirdParty .oracle)

/-- No gateway discharged yet. -/
def none' : Discharges GW := fun _ => false

/-- The oracle gateway has discharged (and only it). -/
def oracleSettled : Discharges GW := none'.settle .oracle

/-- Both gateways discharged. -/
def bothSettled : Discharges GW := oracleSettled.settle .cosigner

#guard suspendedTurn.admits 150 none' == false  -- blocked, oracle has not discharged
#guard suspendedTurn.admits 150 oracleSettled   -- oracle discharged ⇒ the turn resolves forward
#guard suspendedTurn.admits 150 bothSettled     -- MORE discharges never un-admit (keystone)

-- the height-window caveat still bites: discharge resolves the gateway, not the local gate
#guard suspendedTurn.admits 50  oracleSettled == false  -- 50 < 100 — a local caveat narrowed it out

-- `Awaiting` as a runnable scheduler poll: suspended under none', live under oracleSettled
#guard decide (Awaiting suspendedTurn 150 none')                  -- still suspended
#guard decide (Awaiting suspendedTurn 150 oracleSettled) == false -- resolved

-- forward-only order witnesses: settling adds a discharge, retracts none
#guard (none'.settle GW.oracle) GW.oracle               -- oracle now settled
#guard (none'.settle GW.oracle) GW.cosigner == false    -- untouched gateway unchanged

end Dregg2.Authority
