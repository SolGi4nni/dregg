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
import Dregg2.Tactics

namespace Dregg2.Authority

open Dregg2.Laws

/- The request binding-site `Ctx` — the `AuthRequest` facts a caveat is evaluated against (block
height, action, resource, sender, …). Abstract; instantiated by the real PI surface. `Gateway` =
the identity of a third-party caveat's resolving gateway. -/
variable {Ctx : Type}
variable {Gateway : Type}

/-- Logical request time (block height / wall-clock tick), the dimension `CaveatPred.validAfter`
gates on. `Int` to match the protocol's time convention (`Time/Frame`, `ThirdPartyDischarge`). -/
abbrev Time := Int

/-! ## The reified caveat predicate AST (`CaveatPred`) — the D6 content-level vocabulary.

`Caveat.opaque` carries an *opaque* `Ctx → Bool`: you can RUN it, but you cannot reason about, print,
or structurally compare what it SAYS. `CaveatPred` is the introspectable twin — a small inductive AST
of *content-level* request-context atoms closed under the same `and`/`or`/`not`/`true`/`false`
connectives as `Exec.PredAlgebra.Pred`, so the caveat vocabulary is INSPECTABLE data, not a function.

**The fork question (honest).** `Exec.PredAlgebra.Pred` denotes over the `(old, new) : Value`
*transition* of a slot write; `CaveatPred` denotes over the *request context* `Ctx` (block height /
time / action / sender — the `AuthRequest` facts). The two share their CONNECTIVE shape
(`and`/`or`/`not`/`tt`/`ff`) but NOT their denotation domain, so a literal alias would be unsound. We
therefore MIRROR `Pred`'s connective layer here (zero re-fork of the connectives' meaning) while
keeping the atom layer request-context-typed. The atoms read `Ctx` through an explicit `view : Ctx →
Time` seam carried alongside the AST in the `pred` arm — so the AST itself stays pure DATA
(`validAfter t` is a `Time`, never a captured closure) AND `Caveat.ok` needs NO new typeclass
(everything downstream of the old `local` arm lifts with only the `local → opaque` rename — zero
regression).

**Honest framing (no overclaim).** This is an EXPRESSIVENESS / language gain — composable, printable,
structurally-comparable caveats and the content-level narrowing metatheory below — NOT a soundness
gain. The circuit still binds an aggregate `caveatBit` and trusts the executor's decision; reifying a
caveat does not force its policy in-circuit. -/

/-- **`CaveatPred`** — the reified, introspectable caveat AST. One real *content-level* atom
(`validAfter`, a temporal caveat: "this caveat admits only at request-time ≥ `t`" — the simplest
`DreggGrant` dimension) plus the Boolean connectives, mirroring `Exec.PredAlgebra.Pred`'s shape. A
`CaveatPred` is data you can PRINT, structurally compare, and refine — not an opaque `Ctx → Bool`. -/
inductive CaveatPred where
  /-- **`validAfter t`** — admits a request iff its time is `≥ t` (a "not-before" / temporal floor;
  the macaroon `time >` caveat / the `DreggGrant.validAfter` dimension), as inspectable data. -/
  | validAfter (t : Time)
  /-- Top — admits every request. -/
  | tt
  /-- Bottom — admits no request (fail-closed). -/
  | ff
  /-- Conjunction (meet). -/
  | and (l r : CaveatPred)
  /-- Disjunction (join). -/
  | or  (l r : CaveatPred)
  /-- Negation — at every level (mirroring `Pred.not`, not a single-level escape). -/
  | not (p : CaveatPred)
  deriving Repr, DecidableEq

/-- **`CaveatPred.eval`** — the denotation of the reified AST over a request context, reading request
facts through the explicit `view : Ctx → Time` seam (the `AuthRequest`'s time field). The structural
fold mirrors `Pred.eval`: `validAfter t` admits iff `t ≤ view ctx`; the connectives are
`&&`/`||`/`!`/`true`/`false`. Decidable, computable, fail-closed (`ff` rejects). -/
def CaveatPred.eval (view : Ctx → Time) : CaveatPred → Ctx → Bool
  | .validAfter t, ctx => decide (t ≤ view ctx)
  | .tt,           _   => true
  | .ff,           _   => false
  | .and l r,      ctx => l.eval view ctx && r.eval view ctx
  | .or  l r,      ctx => l.eval view ctx || r.eval view ctx
  | .not p,        ctx => !(p.eval view ctx)

/-- **A caveat** — the universal gate (`WitnessedCondition`), here in three engines: a **reified**
`CaveatPred` carrying its request-`view` seam (introspectable content-level AST, D6), an **opaque**
handwritten predicate over the request context (the escape hatch for caveats not yet in the AST
vocabulary — `local` renamed: it IS opaque), or a **third-party** caveat naming a `gateway` that must
*discharge* it (the await authority-face). -/
inductive Caveat (Ctx Gateway : Type) where
  | pred       (p : CaveatPred) (view : Ctx → Time)
  | opaque     (check : Ctx → Bool)
  | thirdParty (gateway : Gateway)

/-- The discharges presented alongside a token (dregg1 `Authorization::Token.discharges`): which
gateways have produced a resolution. -/
abbrev Discharges (Gateway : Type) := Gateway → Bool

/-- A caveat is satisfied at a request iff its reified `CaveatPred` admits (under its bundled `view`),
its opaque check holds, or its gateway has discharged. The reified arm folds through `CaveatPred.eval`
(so a `pred`-caveat is an inspectable policy), the opaque arm just RUNS its closure. No typeclass —
the `pred` arm is a drop-in for the old `local` arm, so all downstream `admits`/`ok` consumers lift
with only the `local → opaque` rename. -/
def Caveat.ok (c : Caveat Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  match c with
  | .pred p view  => p.eval view ctx
  | .opaque check => check ctx
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
theorem attenuate_trivial (tok : Token Ctx Gateway) (ctx : Ctx)
    (d : Discharges Gateway) :
    (tok.attenuate (.opaque (fun _ => true))).admits ctx d = tok.admits ctx d := by
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

/-- The toy request `view`: a block height IS the request's logical time. (A `CaveatPred.validAfter t`
over a `Height` request gates on "height ≥ t".) The seam the real PI surface instantiates per-`Ctx`. -/
def heightView : Height → Time := fun h => (h : Int)

/-- A root biscuit with no caveats (full authority over its target). -/
def rootBiscuit : Token Height Unit := { kind := .biscuit, caveats := [] }

/-- Attenuate it with "height ≥ 100" then "height ≤ 200" — a validity window. The lower bound is the
REIFIED `validAfter 100` caveat (`CaveatPred` carrying `heightView`, inspectable); the upper bound
stays an `opaque` check (no `validBefore` atom in the toy AST yet — the escape hatch carries it,
nothing regresses). -/
def windowed : Token Height Unit :=
  (rootBiscuit.attenuate (.pred (.validAfter 100) heightView)).attenuate
    (.opaque (fun h => decide (h ≤ 200)))

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

/-! ## THE D6 PAYOFF — content-level caveat refinement (the metatheory reification BUYS).

`attenuate_narrows` says appending a caveat narrows the admissible-request set — but it is
AST-blind: it holds for `opaque` and `pred` caveats alike, reasoning only about the LIST. With the
`opaque` arm that is *all* you can say — the check is a black box. The reification lets us reason
about what a caveat SAYS: a `CaveatPred` *refines* another (`refines a b` ⇔ `a ⊨ b`, "everything `a`
admits, `b` admits") as a structural relation over the AST content, decided once over all contexts.

For the temporal atom this is the genuinely-new statement: `validAfter t₂ ⊑ validAfter t₁` IFF
`t₁ ≤ t₂` — tightening the not-before floor is a refinement, loosening it is NOT. This is content-
level narrowing you can DECIDE from the AST, impossible for an opaque `Ctx → Bool`. -/

/-- **`CaveatPred.refines view a b`** — `a` refines (narrows) `b` under request-view `view`: at EVERY
request context, if `a` admits then `b` admits (`a ⊨ b`). The semantic narrowing order on reified
caveats — the content-level sharpening of the list-level `attenuate_narrows`. -/
def CaveatPred.refines (view : Ctx → Time) (a b : CaveatPred) : Prop :=
  ∀ ctx : Ctx, CaveatPred.eval view a ctx = true → CaveatPred.eval view b ctx = true

/-- **`caveatPred_refines` (the D6 payoff).** Under ANY request view, tightening a temporal floor IS a
refinement: `validAfter t₂` refines `validAfter t₁` exactly when `t₁ ≤ t₂` (a later not-before admits
a subset of requests). The content-level narrowing the reification buys over the opaque function —
you reason about what the caveat SAYS, decided from the AST, not by running a black box. -/
theorem caveatPred_refines {view : Ctx → Time} {t₁ t₂ : Time} (h : t₁ ≤ t₂) :
    CaveatPred.refines view (.validAfter t₂) (.validAfter t₁) := by
  intro ctx hadm
  simp only [CaveatPred.eval, decide_eq_true_eq] at hadm ⊢
  exact le_trans h hadm

/-! ### Non-vacuity of `caveatPred_refines` — BOTH poles, over the concrete `Height` view (`by decide`).
A tighter floor refines a looser one; a looser floor does NOT refine a tighter one (the negative
tooth — `refines` is a genuine, non-trivial order, not always-true). -/

-- POSITIVE: `validAfter 100` ⊑ `validAfter 50` (since 50 ≤ 100). Refinement holds.
example : CaveatPred.refines heightView (.validAfter 100) (.validAfter 50) :=
  caveatPred_refines (by decide)

-- NEGATIVE: `validAfter 50` does NOT refine `validAfter 100` — height 75 is admitted by the looser
-- floor (50 ≤ 75) but REJECTED by the tighter one (100 ≤ 75 is false), a concrete counterexample.
example : ¬ CaveatPred.refines heightView (.validAfter 50) (.validAfter 100) := by
  intro hrefines
  have := hrefines 75 (by decide)
  exact absurd this (by decide)

/-- **`caveatPred_refines_nonvacuous`** — the order is BOTH inhabited and non-trivial: a tighter floor
refines a looser one, and a looser floor does NOT refine a tighter one. No laundered vacuity. -/
theorem caveatPred_refines_nonvacuous :
    CaveatPred.refines heightView (.validAfter 100) (.validAfter 50) ∧
    ¬ CaveatPred.refines heightView (.validAfter 50) (.validAfter 100) :=
  ⟨caveatPred_refines (by decide),
   fun hrefines => absurd (hrefines 75 (by decide)) (by decide)⟩

/-! ### The reified atom RUNS on the live token leg (`#guard`) — a `validAfter` caveat narrows a real
token exactly like the opaque one did, with both admit/reject polarities. -/

/-- A reified token: full authority narrowed by `validAfter 100` (the `pred` arm, inspectable). -/
def reifiedWindowStart : Token Height Unit :=
  rootBiscuit.attenuate (.pred (.validAfter 100) heightView)

#guard reifiedWindowStart.admits 150 noDischarges            -- true  (150 ≥ 100: temporal floor met)
#guard reifiedWindowStart.admits 50  noDischarges == false   -- false (50 < 100: not-before refuses)
#guard windowed.admits 150 noDischarges                      -- the mixed pred+opaque window still works
#guard windowed.admits 50  noDischarges == false             -- (50 < 100: the reified floor narrowed it)

/-- A composed reified caveat: `validAfter 100 ∧ ¬ validAfter 300` ≡ the window `[100, 300)`, authored
in the Boolean connectives of the AST (the thing an opaque `Ctx → Bool` cannot be reasoned about). -/
def reifiedBand : CaveatPred := .and (.validAfter 100) (.not (.validAfter 300))
#guard (CaveatPred.eval heightView reifiedBand 150)            -- true  (100 ≤ 150 < 300)
#guard (CaveatPred.eval heightView reifiedBand 50)  == false   -- false (below the floor)
#guard (CaveatPred.eval heightView reifiedBand 350) == false   -- false (at/after the ceiling)
example : CaveatPred.eval heightView reifiedBand 150 = true  := by decide
example : CaveatPred.eval heightView reifiedBand 350 = false := by decide

#assert_axioms caveatPred_refines
#assert_axioms caveatPred_refines_nonvacuous
#assert_axioms attenuate_narrows
#assert_axioms Caveat.ok

end Dregg2.Authority
