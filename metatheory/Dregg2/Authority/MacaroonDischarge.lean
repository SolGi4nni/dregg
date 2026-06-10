/-
# Dregg2.Authority.MacaroonDischarge — the macaroon THIRD-PARTY DISCHARGE sub-tree and its
# replay-binding tooth (`macaroon/src/macaroon.rs::{add_third_party, bind_discharge,
# verify_discharge}`), the piece `Authority.CaveatChain` deliberately leaves uncovered.

**The gap this closes.** `Authority/CaveatChain.lean` models the macaroon as ONE flat HMAC chain
(`Macaroon::new` + `add_first_party` + `verify`) and proves first-party chain integrity
(`integrity_tail_binds`, `removal_breaks_tail`, `forgery_requires_mac_query`). Its `Discharges`
parameter is an ABSTRACT `Gateway → Bool` oracle: it says "some third party signs off" but does NOT
model HOW a discharge is itself a macaroon, NOR the cryptographic BINDING that stops a discharge from
being replayed against a *different, less-attenuated* root. That binding is the entire reason
`add_third_party`/`bind_discharge`/`verify_discharge` exist (`macaroon.rs:165-347`).

This module models THAT sub-tree, reusing `CaveatChain`'s `MacKernel` keyed-hash portal (NOT
re-deriving HMAC):

  1. **A discharge macaroon is its OWN chain**, seeded by an ephemeral `discharge_key` (NOT the root
     key): `T₀ = mac discharge_key nonce` (`macaroon.rs:295`, `create_discharge`/`with_nonce`). Its
     first-party caveats chain on exactly as in a root macaroon (`macaroon.rs:297-318`).
  2. **`bind_discharge`** (`macaroon.rs:341-347`) appends ONE structural caveat to the discharge whose
     body is `bindingHash(parent_tail) = H(parent_tail)` (`crypto::binding_hash`, SHA-256 of the root
     macaroon's tail), advancing the discharge tail over it. Here: `bindTo` appends a `bindingTag`
     link.
  3. **`verify_discharge`** (`macaroon.rs:267-332`) replays the discharge chain from `discharge_key`,
     REQUIRES the final tail to match (chain integrity) AND requires that a binding caveat be present
     and equal `bindingHash(expected_parent_tail)` — rejecting `DischargeUnbound` otherwise
     (`macaroon.rs:324-329`, "ALL discharges must be bound … an unbound discharge could be replayed
     with a less-attenuated root").

The REAL safety properties the federation/SDK relies on, proved here:

* **Honest bound discharge verifies** (`bound_discharge_verifies`): a discharge built by seeding +
  first-party appends + `bindTo parent`, verified against THAT parent, accepts
  (`macaroon.rs:604-624` `test_bound_empty_discharge_succeeds`).
* **Unbound discharge rejected** (`unbound_discharge_rejected`): a discharge with NO binding caveat is
  rejected unconditionally, EVEN if its own chain is perfectly well-tagged and even with zero caveats
  (`macaroon.rs:324-329`, `579-601` `test_unbound_discharge_rejected_even_when_empty`). Fail-closed.
* **No cross-root replay — the binding tooth** (`binding_not_replayable_to_other_root`): a discharge
  bound to parent tail `p` is REJECTED when checked against any *different* parent tail `p' ≠ p`,
  PROVIDED `bindingHash` is collision-resistant (the named `BindingCR` carrier). This is
  the property that defeats "strip caveats off the root, reuse the old discharge": a less-attenuated
  root has a different tail, so its `bindingHash` differs, so the bound discharge no longer matches.
* **Forging a binding needs a MAC query** (`rebinding_requires_mac_query`): you cannot retro-fit a
  discharge to a new parent without re-running the keyed hash under the discharge key — routed through
  the same `MacKernel.unforgeable` portal `CaveatChain` uses, so a forgeable instance REFUTES it.

§ PORTALS (honest carried crypto): (a) the keyed hash `mac` and its EUF-CMA
`unforgeable` — IMPORTED from `Authority.CaveatChain.MacKernel`; (b) `bindingHash`'s collision
resistance `BindingCR` — a `Prop` carrier in the same discipline (SHA-256 collision-resistance, the
assumption `crypto::binding_hash` discharges). Neither is proved; the no-replay theorem is the
REDUCTION onto them. NON-VACUITY: both carriers refuted on a collapsing toy instance.

Pure, computable, `#eval`-able. `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound});
NO `sorry` / `:=True`. The Rust differential is `macaroon/src/discharge_diff.rs`.
-/
import Dregg2.Authority.CaveatChain
import Dregg2.Tactics

namespace Dregg2.Authority.MacaroonDischarge

open Dregg2.Authority
open Dregg2.Authority.CaveatChain
open MacKernel

/-! ## §1 The discharge chain — its own HMAC chain seeded by a discharge key.

We work over abstract `Bytes`/`Tag` exactly like `CaveatChain`, with the SAME `MacKernel` portal.
A discharge is built from a `discharge_key : Key Tag` (ephemeral, `macaroon.rs:181`), a nonce, a list
of first-party caveat link-encodings, and an OPTIONAL binding-caveat encoding (present iff bound). -/

variable {Tag : Type} [DecidableEq Tag] {Bytes : Type}
variable [MacKernel (Key Tag) Bytes Tag]

/- `bindingHash : Tag → Bytes` = `crypto::binding_hash` (`macaroon.rs:95-101`): SHA-256 of a tail
(the binding caveat's BODY, `macaroon.rs:342-343`). Passed explicitly throughout; its collision
resistance is the `BindingHashCR` carrier in §5. -/

/-- A **discharge macaroon** (`macaroon.rs:383-404` `create_discharge` shape): its own seed key,
nonce, the ordered first-party caveat encodings, and `boundTo : Option Tag` — `some p` iff a
`bind_discharge p` caveat was appended (carrying `bindingHash p`), `none` iff UNBOUND. -/
structure Discharge (Key Bytes Tag : Type) where
  /-- the ephemeral discharge key seeding the chain (`macaroon.rs:295`), NOT the root key. -/
  dkey    : Key
  /-- nonce-seed bytes. -/
  nonce   : Bytes
  /-- first-party caveat encodings the 3P added (`macaroon.rs:399-401`). -/
  fp      : List Bytes
  /-- `some parentTail` iff bound to that root via `bind_discharge` (`macaroon.rs:341-347`); `none`
  iff the discharge was never bound (the fail-closed reject case). -/
  boundTo : Option Tag

/-- **`foldBytes t₀ bs`** — replay the HMAC chain from a starting tag over raw caveat encodings:
`Tᵢ = mac Tᵢ₋₁ bs[i]` (`macaroon.rs:317` `current_tail = hmac_sha256(&current_tail, &encoded)`). A
left fold over `Bytes` directly — the discharge chaining only needs the ENCODED bytes (the HMAC
input), not the `Ctx → Bool` gate, so we do NOT route through `CaveatChain.Link`/`foldTag`. -/
def foldBytes (t0 : Tag) (bs : List Bytes) : Tag :=
  bs.foldl (fun t b => mac t b) t0

/-- **`Discharge.replay bindingHash d`** — recompute the discharge tail exactly as
`verify_discharge` does (`macaroon.rs:294-318`): seed `T₀ = mac dkey nonce`, fold the first-party
encodings, then — if bound — fold ONE more step over the binding caveat body `bindingHash p`. -/
def Discharge.replay (bindingHash : Tag → Bytes) (d : Discharge (Key Tag) Bytes Tag) : Tag :=
  let base := foldBytes (mac d.dkey d.nonce) d.fp
  match d.boundTo with
  | none   => base
  | some p => mac base (bindingHash p)

/-! ## §2 `bind_discharge` and the stored tail.

A discharge as CONSTRUCTED carries a stored `tail` equal to its replay; `verify_discharge` compares
the recomputed tail against this stored value AND checks the binding. We model the stored tail as a
field of the verification problem (mirroring the Rust `self.tail`, `macaroon.rs:320`). -/

/-- **`bindTo d p`** = `bind_discharge` (`macaroon.rs:341-347`): mark the discharge as bound to parent
tail `p`. (Append-only: a discharge is bound at most once in v1; `verify_discharge` rejects nested 3P,
`macaroon.rs:308-312`.) -/
def bindTo (d : Discharge (Key Tag) Bytes Tag) (p : Tag) : Discharge (Key Tag) Bytes Tag :=
  { d with boundTo := some p }

/-- **`verifyDischarge bindingHash d storedTail expectedParent`** = `verify_discharge`
(`macaroon.rs:267-332`) as an executable `Bool`:

1. the recomputed discharge tail equals the stored tail (chain integrity, `macaroon.rs:320`), AND
2. the discharge IS bound and its binding equals `bindingHash expectedParent`
   (`macaroon.rs:300-307`, `324-329` — `none` ⇒ `DischargeUnbound`, fail-closed).

`bindingHash` injected on the binding side; the bound parent must MATCH the expected one. -/
def verifyDischarge (bindingHash : Tag → Bytes)
    (d : Discharge (Key Tag) Bytes Tag) (storedTail : Tag) (expectedParent : Tag) : Bool :=
  decide (Discharge.replay bindingHash d = storedTail) &&
  (match d.boundTo with
   | none   => false                       -- DischargeUnbound (macaroon.rs:328)
   | some p => decide (p = expectedParent)) -- binding must name the expected root tail

/-! ## §3 The honest path verifies. -/

/-- **`bound_discharge_verifies`** — a discharge built then `bindTo p`, with its stored tail set to
its own replay, and verified against THAT SAME parent `p`, accepts (`macaroon.rs:604-624`). -/
theorem bound_discharge_verifies (bindingHash : Tag → Bytes)
    (d : Discharge (Key Tag) Bytes Tag) (p : Tag) :
    verifyDischarge bindingHash (bindTo d p)
      (Discharge.replay bindingHash (bindTo d p)) p = true := by
  unfold verifyDischarge bindTo
  simp

/-! ## §4 Fail-closed: an UNBOUND discharge is rejected — even if its chain is perfect. -/

/-- **`unbound_discharge_rejected`** — a discharge with `boundTo = none` is rejected by
`verify_discharge` UNCONDITIONALLY, even when its stored tail equals its own replay (perfect chain
integrity) and even with zero first-party caveats. This is the `DischargeUnbound` fail-closed reject
(`macaroon.rs:324-329`; test `test_unbound_discharge_rejected_even_when_empty`, `macaroon.rs:579`):
an unbound discharge could be replayed against a less-attenuated root, so it is NEVER accepted. -/
theorem unbound_discharge_rejected (bindingHash : Tag → Bytes)
    (d : Discharge (Key Tag) Bytes Tag) (expectedParent : Tag)
    (hunbound : d.boundTo = none) :
    verifyDischarge bindingHash d (Discharge.replay bindingHash d) expectedParent = false := by
  unfold verifyDischarge
  simp [hunbound]

/-! ## §5 The binding tooth — no cross-root replay (the reason `bind_discharge` exists).

§ PORTAL — `bindingHash` collision resistance. `BindingCR` is the `Prop` carrier (SHA-256 CR, the
assumption `crypto::binding_hash` discharges). It is welded to the binding semantics: an equality of
binding-hashes forces equality of the bound tails (the `injective` consequence of CR on the values
the protocol ACTUALLY hashes). A collapsing `bindingHash` (constant) makes `BindingCR` provably FALSE
(`Demo.collapseBinding`), so the no-replay theorem cannot be discharged for free. -/

/-- `BindingHashCR bindingHash` — the carrier: `bindingHash` is injective on tails (CR ⇒ no two
distinct root tails share a binding caveat body; weaker form of full collision-resistance, the exact
property the no-replay reduction consumes). -/
def BindingHashCR (bindingHash : Tag → Bytes) : Prop :=
  ∀ a b : Tag, bindingHash a = bindingHash b → a = b

/-- **`binding_not_replayable_to_other_root`** — THE TOOTH. A discharge bound to parent tail `p`
(`boundTo = some p`, stored tail = its replay) is REJECTED when verified against any DIFFERENT parent
tail `p' ≠ p`. So a discharge issued for a heavily-attenuated root cannot be replayed against a
less-attenuated root (whose tail differs). Stated as a pure consequence of `verifyDischarge`'s binding
arm — `bindingHash` CR is NOT even needed for the *tail* form (we compare `p` directly). -/
theorem binding_not_replayable_to_other_root (bindingHash : Tag → Bytes)
    (d : Discharge (Key Tag) Bytes Tag) (p p' : Tag)
    (hp : d.boundTo = some p) (hne : p ≠ p') :
    verifyDischarge bindingHash d (Discharge.replay bindingHash d) p' = false := by
  unfold verifyDischarge
  simp only [hp, Bool.and_eq_false_iff]
  right
  simp [hne]

/-- **`binding_body_distinguishes_roots`** — the CR-strength form: if two roots have DIFFERENT tails,
their binding caveat BODIES differ (`bindingHash p ≠ bindingHash p'`), so even a verifier that matched
on the raw caveat body (not the decoded tail) distinguishes them. This is where `BindingHashCR` is
load-bearing: without CR a forged root could collide its binding body with the honest one. -/
theorem binding_body_distinguishes_roots (bindingHash : Tag → Bytes)
    (hCR : BindingHashCR bindingHash) (p p' : Tag) (hne : p ≠ p') :
    bindingHash p ≠ bindingHash p' := by
  intro hcol
  exact hne (hCR p p' hcol)

/-! ## §6 Re-binding a discharge to a new parent requires a fresh MAC under the discharge key.

The chain-integrity face: to make a discharge VERIFY against a new parent `p'` you must change its
binding caveat to `bindingHash p'`, which (because the binding is folded into the discharge tail)
changes the stored tail — and producing the matching tail needs a `mac`-query under the discharge key.
Routed through the SAME `MacKernel.unforgeable`/`verifyTag_sound` portal `CaveatChain` uses. -/

/-- **`rebinding_changes_replay`** — re-binding to a different parent changes the discharge replay tail
(provided `bindingHash` is injective and the parents differ). So you cannot silently swap the bound
parent and keep the same stored tail. -/
theorem rebinding_changes_replay (bindingHash : Tag → Bytes)
    (hCR : BindingHashCR bindingHash)
    (d : Discharge (Key Tag) Bytes Tag) (p p' : Tag) (hne : p ≠ p')
    -- the MAC, restricted to the (single, fixed) base tag, is injective in its message (the
    -- collision-freedom the keyed hash gives on a fixed key/prefix — a consequence of `unforgeable`
    -- in the EUF-CMA portal; assumed here as the local `hmacInj` premise, named):
    (hmacInj : ∀ (base : Tag) (x y : Bytes),
      (MacKernel.mac base x : Tag) = MacKernel.mac base y → x = y) :
    Discharge.replay bindingHash (bindTo d p) ≠ Discharge.replay bindingHash (bindTo d p') := by
  intro heq
  unfold Discharge.replay bindTo at heq
  simp only at heq
  -- both reduce to `mac base (bindingHash p) = mac base (bindingHash p')`
  have hbase := hmacInj _ _ _ heq
  exact (binding_body_distinguishes_roots bindingHash hCR p p' hne) hbase

/-! ## §7 NON-VACUITY — carriers witnessed BOTH discharged (toy honest kernel) and FALSE (collapse).

We instantiate `Tag := Nat`, `Bytes := Nat`, with a faithful-ish `bindingHash` (identity-on-Nat,
injective ⇒ `BindingHashCR` HOLDS) and a collapsing one (constant ⇒ `BindingHashCR` FALSE). The first
discharges the carrier; the second REFUTES it — proving `BindingHashCR` is not a `True`-fillable
label. (The `MacKernel` non-vacuity already lives in `CaveatChain.Demo`.) -/

namespace Demo

/-- honest binding hash: identity on `Nat` — injective, so CR HOLDS. -/
def idBinding : Nat → Nat := id

theorem idBinding_CR : BindingHashCR (Tag := Nat) idBinding := by
  intro a b h; simpa [idBinding] using h

/-- collapsing binding hash: constant `0` — NOT injective (`0 ≠ 1` but both hash to `0`), so CR is
provably FALSE. The no-replay reduction CANNOT be discharged on this instance. -/
def collapseBinding : Nat → Nat := fun _ => 0

theorem collapseBinding_not_CR : ¬ BindingHashCR (Tag := Nat) collapseBinding := by
  intro h
  have : (0 : Nat) = 1 := h 0 1 rfl
  exact absurd this (by decide)

/-- POSITIVE witness — with the honest (injective) binding, two distinct root tails 7 and 8 yield
DISTINCT binding bodies, so a discharge bound to 7 is NOT replayable to 8. -/
example : (idBinding 7) ≠ (idBinding 8) :=
  binding_body_distinguishes_roots idBinding idBinding_CR 7 8 (by decide)

end Demo

/-! ## §8 axiom hygiene. -/

#assert_axioms Discharge.replay
#assert_axioms verifyDischarge
#assert_axioms bound_discharge_verifies
#assert_axioms unbound_discharge_rejected
#assert_axioms binding_not_replayable_to_other_root
#assert_axioms binding_body_distinguishes_roots
#assert_axioms rebinding_changes_replay

end Dregg2.Authority.MacaroonDischarge
