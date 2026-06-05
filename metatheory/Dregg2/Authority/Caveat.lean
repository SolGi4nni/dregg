/-
# Dregg2.Authority.Caveat — the keys-as-caps token layer (biscuit / macaroon / caveat / discharge).

Models dregg1's authority/credential framework (`Authorization::Token { encoded, key_ref, discharges }`
+ `TokenKeyRef`, `turn/src/action.rs:422`): the macaroon caveat chain, the biscuit delegation graph,
third-party caveats, and discharge.

Load-bearing content:
- a **token** = a `RootSeal` + an append-only attenuation chain of caveats (biscuit cross-vat /
  macaroon intra-vat), admitting a request iff all caveats are discharged (meet ⋀);
- **attenuation = appending a caveat = narrowing** — `attenuate_narrows` proves it can only shrink
  the admissible set ("a key may only narrow"; the Heyting residual `⇨`);
- the **biscuit/macaroon split = the vat boundary**: a biscuit is public-key verifiable off-island;
  a macaroon's HMAC root secret is held only by its scoping cell, so it is NOT third-party verifiable
  — a macaroon presented cross-domain is rejected;
- a **third-party caveat = the await engine's authority-face**: suspends until a named gateway's
  discharge resolves it (the discharge/`ConditionalTurn` isomorphism);
- **bridge to the verify/find seam**: a token's verification IS a `Laws.Discharged` witness.

Pure, computable, `#eval`-able.
-/
import Dregg2.Laws

namespace Dregg2.Authority

open Dregg2.Laws

/- The request binding-site `Ctx` — the `AuthRequest` facts a caveat is evaluated against (block
height, action, resource, sender, …). Abstract; instantiated by the real PI surface. `Gateway` =
the identity of a third-party caveat's resolving gateway. -/
variable {Ctx : Type}
variable {Gateway : Type}

/-- **A caveat** — the universal gate (`WitnessedCondition`), here in two engines: a **local**
checkable predicate over the request context (a macaroon 1st-party caveat / a biscuit fact / a
`CapabilityCaveat`), or a **third-party** caveat naming a `gateway` that must *discharge* it (the
await authority-face). -/
inductive Caveat (Ctx Gateway : Type) where
  | local      (check : Ctx → Bool)
  | thirdParty (gateway : Gateway)

/-- The discharges presented alongside a token (dregg1 `Authorization::Token.discharges`): which
gateways have produced a resolution. -/
abbrev Discharges (Gateway : Type) := Gateway → Bool

/-- A caveat is satisfied at a request iff its local check holds, or its gateway has discharged. -/
def Caveat.ok (c : Caveat Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  match c with
  | .local check  => check ctx
  | .thirdParty g => d g

/-- The two token carriers (dregg1 `TokenKeyRef`). -/
inductive TokenKind where
  /-- **biscuit** (`eb2_…`): cross-vat — Ed25519 public-key, offline-verifiable by *anyone*; the
  biscuit delegation graph ≡ the distributed CDT. -/
  | biscuit
  /-- **macaroon** (`em2_…`): intra-vat — a cell-scoped HMAC; the root secret is held only by the
  scoping cell, so it is NOT third-party-verifiable (`discoveries §6.3`). -/
  | macaroon
  deriving DecidableEq, Repr

/-- **A token** — a kind (biscuit/macaroon) + an **append-only attenuation chain of caveats**. The
chain *is* the path of monotone-narrowing `(parent → child)` edges from a `RootSeal` (the CDT
rendering); authority = the meet of all caveats. -/
structure Token (Ctx Gateway : Type) where
  kind    : TokenKind
  caveats : List (Caveat Ctx Gateway)

/-- **A token admits a request iff ALL its caveats are satisfied** (the conjunction / meet ⋀) — the
fail-closed authority decision. -/
def Token.admits (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  tok.caveats.all (fun c => c.ok ctx d)

/-- **Attenuation = appending a caveat** — the *one rule the system rests on* (`dregg2 §1.1`):
narrowing only. A child token = `attenuate parent cav`. -/
def Token.attenuate (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway) : Token Ctx Gateway :=
  { tok with caveats := tok.caveats ++ [c] }

/-! ## The keystone — attenuation can only NARROW (the LossyMorphism, realized). -/

/-- **`attenuate_narrows`** — anything an attenuated token admits, the parent already admitted:
adding a caveat never grows authority. The concrete realization of "a key may only narrow"
(the Heyting residual `⇨`) on the actual biscuit/macaroon chain. -/
theorem attenuate_narrows (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (ctx : Ctx) (d : Discharges Gateway) :
    (tok.attenuate c).admits ctx d = true → tok.admits ctx d = true := by
  simp only [Token.admits, Token.attenuate, List.all_append, Bool.and_eq_true]
  intro h; exact h.1

/-- **`attenuate_subset`** — set form: a more-attenuated token's admissible-request set is a
subset of the parent's. Authority strictly shrinks down a delegation chain. -/
theorem attenuate_subset (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (d : Discharges Gateway) :
    {ctx | (tok.attenuate c).admits ctx d = true} ⊆ {ctx | tok.admits ctx d = true} :=
  fun ctx h => attenuate_narrows tok c ctx d h

/-- Attenuating by an always-true caveat leaves authority unchanged (the trivial
attenuation = identity edge). Sanity companion to `attenuate_narrows`. -/
theorem attenuate_trivial (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) :
    (tok.attenuate (.local (fun _ => true))).admits ctx d = tok.admits ctx d := by
  simp [Token.admits, Token.attenuate, List.all_append, Caveat.ok]

/-! ## The biscuit / macaroon split IS the vat boundary. -/

/-- Only a biscuit verifies off-island (public-key); a macaroon's HMAC root secret is held
only by its scoping cell, so a non-holder cannot verify it (HMAC ≠ third-party-verifiable). -/
def Token.crossVatVerifiable (tok : Token Ctx Gateway) : Bool :=
  match tok.kind with | .biscuit => true | .macaroon => false

/-- **A macaroon is never cross-vat verifiable.** Presenting it to a non-holding verifier
fails closed: off-island keys-as-caps is the biscuit's job, not the macaroon's. -/
theorem macaroon_not_crossvat (tok : Token Ctx Gateway) (h : tok.kind = .macaroon) :
    tok.crossVatVerifiable = false := by
  unfold Token.crossVatVerifiable; rw [h]

/-- **A biscuit is cross-vat verifiable** (the `Obs` badge that leaves the vat). -/
theorem biscuit_crossvat (tok : Token Ctx Gateway) (h : tok.kind = .biscuit) :
    tok.crossVatVerifiable = true := by
  unfold Token.crossVatVerifiable; rw [h]

/-! ## Bridge to the verify/find seam: a verifying token IS a `Laws.Discharged` witness. -/

/-- A token (with its discharges) instantiates the verify/find seam (`Laws.Verifiable`): the
predicate is the request context, the witness is the `(token, discharges)` pair, and `Verify` is
`Token.admits`. The token layer is a `Verify` — biscuit and STARK are both witnesses differing
only in cost. -/
instance tokenVerifiable : Verifiable Ctx (Token Ctx Gateway × Discharges Gateway) where
  Verify ctx w := w.1.admits ctx w.2

/-- **`token_discharges`** — a token that admits the request is a discharged verify/find-seam
witness. The cap's authorization across the boundary is a `Verify`, feeding the cross-vat case
of the vat-boundary law. -/
theorem token_discharges (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway)
    (h : tok.admits ctx d = true) :
    Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway) ctx (tok, d) := h

/-! ## It runs (`#eval`) — a macaroon attenuated down a chain. -/

/-- A toy request context: the current block height. -/
abbrev Height := Nat

/-- A root biscuit with no caveats (full authority over its target). -/
def rootBiscuit : Token Height Unit := { kind := .biscuit, caveats := [] }

/-- Attenuate it with "height ≥ 100" then "height ≤ 200" — a validity window. -/
def windowed : Token Height Unit :=
  (rootBiscuit.attenuate (.local (fun h => decide (100 ≤ h)))).attenuate (.local (fun h => decide (h ≤ 200)))

/-- No discharges needed (no third-party caveats). -/
def noDischarges : Discharges Unit := fun _ => false

#guard rootBiscuit.admits 150 noDischarges           -- root admits everything
#guard windowed.admits 150 noDischarges              -- 150 ∈ [100,200]
#guard windowed.admits 50  noDischarges == false     -- 50 < 100 — a caveat narrowed it out
#guard windowed.admits 250 noDischarges == false     -- 250 > 200
#guard windowed.crossVatVerifiable                   -- a biscuit travels off-island
#guard rootBiscuit.crossVatVerifiable

/-- A macaroon version of the same window — cannot be verified off-island. -/
def macWindowed : Token Height Unit := { windowed with kind := .macaroon }
#guard macWindowed.crossVatVerifiable == false   -- HMAC ≠ third-party-verifiable

/-- A third-party caveat: this turn cannot become admissible until gateway `()` discharges it
(the await authority-face). -/
def needsGateway : Token Height Unit := windowed.attenuate (.thirdParty ())
#guard needsGateway.admits 150 (fun _ => false) == false  -- gateway has not discharged
#guard needsGateway.admits 150 (fun _ => true)            -- gateway discharged ⇒ suspended turn resolves

end Dregg2.Authority
