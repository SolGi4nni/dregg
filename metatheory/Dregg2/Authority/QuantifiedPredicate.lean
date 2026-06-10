/-
# Dregg2.Authority.QuantifiedPredicate — the QUANTIFIED fragment of the guard language (DREGG3 §8).

**The last fragment of the §8 closure: "for ALL / there EXISTS".** The relational/arithmetic closure
(`Authority.RelationalClosure`) gives the full algebra of decidable affine relations over the *named*
post-record slots — the axis named "relational arity". The remaining expressive gap §8 names is the
QUANTIFIED one: the predicates an app author actually reaches for —

  * "is the SENDER in the authorized set?"      (∃ entry in a committed set = elem — membership)
  * "do ALL queue entries satisfy the invariant?" (∀ i < N, P(entry[i]) — bounded universal)
  * "does ANY slot match the pattern?"           (∃ i < N, P(entry[i]) — bounded existential)

These compile to STANDARD gadgets, and the compilation is the whole point of this module:

  * **bounded-∀** over a finite index range is the **N-fold conjunction** of the body predicate —
    so it DE-QUANTIFIES into a `RelPred` (`RelationalClosure`), needing NO new circuit primitive for
    the cleartext case. O(N) of the body's constraints, full stop.
  * **bounded-∃** over a finite index range is the **N-fold disjunction** — likewise a `RelPred`.
  * **membership against a committed set root** is the one quantifier that does NOT de-quantify: the
    set is not in the cleartext post-record, it lives behind a Merkle/set commitment. That routes
    through the `witnessed(vk)` interface (`Authority.Predicate.merkleMembership`), where the verifier
    is the §8 Merkle-membership oracle — the SAME shape `Predicate.senderAuthorized` already exposes.
    We CITE that AIR (`Crypto.BlindedSet` / `Crypto.Merkle`), we do not re-implement it.

So this module sits ON TOP of `RelationalClosure`: a bounded quantifier over a per-index family of
`RelPred`s, with a decidable evaluator over the post-record, and a `compile` that folds it back into
ONE `RelPred` — the keystone `forall_eq_andFold` / `exists_eq_orFold`. The membership atom is the
named escape to the witnessed seam, connected to the existing `MemberOf` / `SenderAuthorized` shape.

NEW file only. Does NOT edit `RelationalClosure`, `Authority.Predicate`, `Exec.Value`, or `Dregg2.lean`.
Reuses `RelationalClosure.RelPred` (the relational closure) + `Authority.Predicate.registryVerify`
(the witnessed-membership dispatch). Every keystone `#assert_axioms`-pinned — no sorry, no `:= True`.
-/
import Dregg2.Authority.RelationalClosure
import Dregg2.Authority.Predicate
import Dregg2.Tactics

namespace Dregg2.Authority.QuantifiedPredicate

open Dregg2.Exec
open Dregg2.Authority.RelationalClosure (RelPred affineSum)
open Dregg2.Authority.Predicate (WitnessedKind Registry Verifier registryVerify registry_sound
  verifiableOfRegistry)
open Dregg2.Laws (Discharged)

/-! ## §1 — `QuantPred` — bounded ∃/∀ over an index range, plus the membership atom.

The index domain is a FINITE `range : List ι` (a finite slot range, an enumerated set of entry
indices). The body is a per-index family `P : ι → RelPred` — for each index it picks out a
relational predicate over the post-record (e.g. "entry[i] ≤ capacity" instantiated at `i`). This is
the bounded quantifier: the range is fixed by the predicate, never by the witness, so the circuit
width is fixed (the `flatten_width` discipline — `Exec.Value`).

Membership against a *committed set root* is the orthogonal atom: the set is NOT cleartext, so it
cannot de-quantify into a `RelPred`; it carries a `WitnessedKind` (the §8 oracle slot — typically
`merkleMembership` / `blindedSet`) and routes through `registryVerify`. -/

variable {ι : Type}

/-- **`QuantPred`** — the quantified fragment of the guard language over a finite index domain `ι`.
Three shapes:

  * `forall_ range P` — `∀ i ∈ range, (P i) holds on the post-record` (bounded universal).
  * `exists_ range P` — `∃ i ∈ range, (P i) holds on the post-record` (bounded existential).
  * `memberOf kind` — the membership atom: an element is in a COMMITTED set (Merkle/set root). The
    `kind : WitnessedKind` names the §8 verifier slot (`merkleMembership` / `blindedSet`); the actual
    membership is decided by `registryVerify`, NOT by reading the cleartext record. -/
inductive QuantPred (ι : Type) where
  /-- Bounded universal: `∀ i ∈ range, (P i)` holds on the post-record. -/
  | forall_ (range : List ι) (P : ι → RelPred)
  /-- Bounded existential: `∃ i ∈ range, (P i)` holds on the post-record. -/
  | exists_ (range : List ι) (P : ι → RelPred)
  /-- Membership against a committed set root — routes to the §8 witnessed verifier at `kind`. -/
  | memberOf (kind : WitnessedKind)

/-! ## §2 — The decidable evaluator over the post-record (for the bounded quantifiers).

`forall_`/`exists_` are decidable: range is finite, the body `RelPred.eval` is a total `Bool`. They
evaluate over the post-record ALONE (inheriting `RelPred`'s record-locality). `memberOf` is NOT a
function of the cleartext record — its bit comes from the witnessed verifier — so `eval` takes the
membership bit as a parameter supplied by `registryVerify` (the §8 oracle), keeping the cleartext
evaluator honest about what it can and cannot see. -/

/-- **`QuantPred.evalClear p rec`** — the cleartext evaluator for the BOUNDED quantifiers over the
post-record `rec`. `forall_` is `List.all` of the body bits; `exists_` is `List.any`. `memberOf` is
NOT cleartext-decidable (the set is committed, not in `rec`) — it FAILS CLOSED here (`false`), and is
discharged only through `evalWitnessed` / `registryVerify`. -/
def QuantPred.evalClear : QuantPred ι → Value → Bool
  | .forall_ range P, rec => range.all (fun i => (P i).eval rec)
  | .exists_ range P, rec => range.any (fun i => (P i).eval rec)
  | .memberOf _,      _   => false  -- committed set not in cleartext record ⇒ fail closed

/-! ## §3 — DE-QUANTIFICATION: bounded-∀ = N-fold ∧, bounded-∃ = N-fold ∨ (the keystone).

A bounded quantifier over CLEARTEXT collapses to a finite Boolean fold of the body `RelPred`s — so it
SUBSUMES into the relational closure: no new circuit primitive, just O(N) of the body's constraints.
`compileForall` folds the range into `RelPred.and` (seed `⊤`); `compileExists` into `RelPred.or`
(seed `⊥`). The keystone theorems prove the fold's `RelPred.eval` equals the quantifier's `evalClear`
— pointwise, on EVERY record. -/

/-- **`andFold range P`** — the N-fold conjunction `(P i₀) ∧ (P i₁) ∧ … ∧ ⊤` as a single `RelPred`.
The compilation of `forall_ range P` into the relational closure (seed `⊤`, the empty-AND identity). -/
def andFold (range : List ι) (P : ι → RelPred) : RelPred :=
  range.foldr (fun i acc => .and (P i) acc) .top

/-- **`orFold range P`** — the N-fold disjunction `(P i₀) ∨ (P i₁) ∨ … ∨ ⊥` as a single `RelPred`.
The compilation of `exists_ range P` into the relational closure (seed `⊥`, the empty-OR identity). -/
def orFold (range : List ι) (P : ι → RelPred) : RelPred :=
  range.foldr (fun i acc => .or (P i) acc) .bot

/-- **`forall_eq_andFold` — PROVED (the keystone).** A bounded universal evaluates IDENTICALLY to the
N-fold conjunction of its body. So `forall_ range P` DE-QUANTIFIES into `andFold range P : RelPred` —
a bounded-∀ over cleartext is exactly O(N) of the body's relational constraints, NO new primitive. -/
theorem forall_eq_andFold (range : List ι) (P : ι → RelPred) (rec : Value) :
    (QuantPred.forall_ range P).evalClear rec = (andFold range P).eval rec := by
  show range.all (fun i => (P i).eval rec) = (andFold range P).eval rec
  unfold andFold
  induction range with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, List.foldr_cons, RelPred.eval]
    rw [ih]

/-- **`exists_eq_orFold` — PROVED (the keystone, dual).** A bounded existential evaluates IDENTICALLY
to the N-fold disjunction of its body. So `exists_ range P` DE-QUANTIFIES into `orFold range P :
RelPred` — a bounded-∃ over cleartext is exactly O(N) of the body's relational constraints. -/
theorem exists_eq_orFold (range : List ι) (P : ι → RelPred) (rec : Value) :
    (QuantPred.exists_ range P).evalClear rec = (orFold range P).eval rec := by
  show range.any (fun i => (P i).eval rec) = (orFold range P).eval rec
  unfold orFold
  induction range with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.any_cons, List.foldr_cons, RelPred.eval]
    rw [ih]

/-- **`compile`** — the de-quantifier: send a bounded quantifier to its `RelPred` fold. `memberOf` is
NOT in the cleartext fragment (the committed set is behind a `witnessed(vk)`), so it has no `RelPred`
image — `compile` is defined only on the bounded shapes and reports the membership escape as `none`. -/
def compile : QuantPred ι → Option RelPred
  | .forall_ range P => some (andFold range P)
  | .exists_ range P => some (orFold range P)
  | .memberOf _      => none  -- routes to the witnessed seam, not the relational closure

/-- **`compile_sound` — PROVED.** Whenever `compile p = some r`, the compiled `RelPred` `r` evaluates
IDENTICALLY to `p`'s cleartext evaluator on EVERY record. So the de-quantification is faithful: the
bounded quantifier and its O(N) relational compilation agree everywhere (anti-vacuously — see §6). -/
theorem compile_sound (p : QuantPred ι) (r : RelPred) (hc : compile p = some r) (rec : Value) :
    p.evalClear rec = r.eval rec := by
  cases p with
  | forall_ range P => cases hc; exact forall_eq_andFold range P rec
  | exists_ range P => cases hc; exact exists_eq_orFold range P rec
  | memberOf _ => exact absurd hc (by simp [compile])

/-! ## §3.1 — The bounded-circuit corollary: the de-quantification costs O(N) of the body.

The §8 honest tax for the quantified fragment: a bounded quantifier over `range` of length `N`
compiles to a `RelPred` whose `constraintBudget` (`RelationalClosure`) is at most `N · (max body
cost) + N + 1` — linear in the range. We state the structural form: `andFold`/`orFold` add one
Boolean node per range element on top of the bodies, so the cost is the sum of the body costs plus
`N + 1`. (We bound the SHAPE here; the per-body cost is `RelationalClosure.relPred_constraints_bounded`.) -/

/-- **`andFold_budget` — PROVED.** The N-fold conjunction's constraint budget is the sum of the body
budgets plus `N + 1` (one `.and` node per element + the `⊤` seed). Linear in the range length — the
bounded-∀ stays efficiently circuit-expressible. -/
theorem andFold_budget (range : List ι) (P : ι → RelPred) :
    RelationalClosure.constraintBudget (andFold range P)
      = (range.map (fun i => RelationalClosure.constraintBudget (P i))).foldr (· + ·) 0
        + range.length + 1 := by
  unfold andFold
  induction range with
  | nil => simp [RelationalClosure.constraintBudget]
  | cons i rest ih =>
    simp only [List.foldr_cons, List.map_cons, List.length_cons,
      RelationalClosure.constraintBudget]
    omega

/-- **`orFold_budget` — PROVED (dual).** The N-fold disjunction's constraint budget is likewise the
sum of the body budgets plus `N + 1` — the bounded-∃ is linear in the range length too. -/
theorem orFold_budget (range : List ι) (P : ι → RelPred) :
    RelationalClosure.constraintBudget (orFold range P)
      = (range.map (fun i => RelationalClosure.constraintBudget (P i))).foldr (· + ·) 0
        + range.length + 1 := by
  unfold orFold
  induction range with
  | nil => simp [RelationalClosure.constraintBudget]
  | cons i rest ih =>
    simp only [List.foldr_cons, List.map_cons, List.length_cons,
      RelationalClosure.constraintBudget]
    omega

/-! ## §4 — MEMBERSHIP: the ∃-over-a-committed-set atom = the `SenderAuthorized` / `MemberOf` shape.

"Is the sender in the authorized set?" is `∃ entry in the committed set, entry = sender`. The set is
not cleartext — it is a Merkle/set commitment (a root `Digest`), so the membership does NOT
de-quantify; it is decided by a witness (a Merkle path) checked by the §8 oracle. This is EXACTLY the
shape `Authority.Predicate.senderAuthorized` already exposes (a `witnessed s` guard discharged through
the verify seam) and `Crypto.BlindedSet.MemberOf` / `Crypto.Merkle.MerkleMembers` realize as an AIR.

We CONNECT to that shape, we do not re-implement it: `memberOf kind` discharges iff the registry's
verifier for `kind` accepts the (root, path) witness — `registryVerify` — which `registry_sound`
turns into `Discharged`. The Merkle/set AIR itself (the recomposition relation, the binding) is the
§8 portal, cited from `Crypto.BlindedSet`. -/

/-- **`memberWitnessed reg kind root path`** — the WITNESSED membership bit for `memberOf kind`: the
committed set's root is the statement, the path is the witness, and the registry's verifier for
`kind` (the Merkle / blinded-set oracle, §8) decides. This is the same dispatch
`Predicate.senderAuthorized` uses; the cleartext `evalClear` cannot see this (fails closed there). -/
def memberWitnessed {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (kind : WitnessedKind) (root : Stmt) (path : Wit) : Bool :=
  registryVerify reg kind root path

/-- **`memberOf_discharges` — PROVED.** When the registry's `kind`-verifier ACCEPTS the (root, path)
witness, the membership atom is `Discharged` at the witnessed seam — the `SenderAuthorized` /
`MemberOf` discharge, lifted to `memberOf kind` through the existing registry keystone. Soundness is
the registry's, against any (possibly adversarial) prover; the Merkle binding stays a §8 obligation. -/
theorem memberOf_discharges {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (kind : WitnessedKind) (root : Stmt) (path : Wit)
    (haccept : memberWitnessed reg kind root path = true) :
    @Discharged Stmt Wit (verifiableOfRegistry reg kind) root path :=
  -- `memberWitnessed` is `registryVerify` verbatim; the registry keystone discharges it.
  registry_sound reg kind root path haccept

/-- **`senderAuthorized`** — the named app predicate "the sender is in the authorized set", as a
`memberOf` atom over the `merkleMembership` kind (the §8 Merkle-membership oracle slot, mirroring
`Predicate.WitnessedKind.merkleMembership` / `Crypto.BlindedSet.MemberOf`). This is the membership
shape an app author writes; it discharges through `memberOf_discharges`. -/
def senderAuthorized : QuantPred ι := .memberOf .merkleMembership

/-- **`senderAuthorized_is_memberOf` — PROVED (the connection).** `senderAuthorized` IS literally the
`memberOf` atom at the Merkle-membership kind: it routes to the same witnessed verifier, no separate
machinery. So the "sender in the authorized set" predicate is exactly the committed-set membership
quantifier — the connection to the existing `SenderAuthorized` atom, made definitional. -/
theorem senderAuthorized_is_memberOf :
    (senderAuthorized : QuantPred ι) = QuantPred.memberOf .merkleMembership := rfl

/-! ## §5 — The named ESCAPE: membership does NOT de-quantify (it is not cleartext).

The boundary, stated as a theorem: `memberOf` has no `RelPred` image (`compile … = none`) and its
cleartext evaluator is `false` (fail-closed) — because the committed set is behind a `witnessed(vk)`,
not in the post-record. Only the BOUNDED-RANGE quantifiers de-quantify; membership is the §8 portal. -/

/-- **`memberOf_no_cleartext_compile` — PROVED (the boundary).** `compile (memberOf kind) = none`:
membership over a committed set has NO relational-closure image — it must route through the witnessed
seam (`memberOf_discharges`), not the cleartext fold. The de-quantification keystone is precisely for
the bounded-range fragment; this names where it stops. -/
theorem memberOf_no_cleartext_compile (kind : WitnessedKind) :
    compile (ι := ι) (.memberOf kind) = none := rfl

/-- **`memberOf_clear_fails_closed` — PROVED.** The cleartext evaluator FAILS CLOSED on `memberOf`:
the committed set is not in the post-record, so `evalClear` cannot witness membership and returns
`false`. Membership is discharged ONLY through the witnessed verifier (`memberOf_discharges`). -/
theorem memberOf_clear_fails_closed (kind : WitnessedKind) (rec : Value) :
    (QuantPred.memberOf kind : QuantPred ι).evalClear rec = false := rfl

/-! ## §6 — §NON-VACUITY: the bounded-∀ app example + the membership app example, both DISCRIMINATING.

The §8 bar (`feedback-dont-launder-vacuity-as-honest`): every keystone must witness BOTH bits. We give
two concrete, app-relevant quantified predicates, each true of a good witness and false of a violating
one — and show the de-quantification preserves the discrimination. -/

/-! ### §6.1 — "ALL queue entries are below capacity" as a bounded-∀.

A queue cell with three entry slots `q0, q1, q2` and a `capacity`. The invariant: EVERY entry is
below capacity, i.e. `∀ i ∈ {0,1,2}, entry[i] − capacity ≤ 0`. Each body is the `RelPred` atom
`entry[i] ≤ capacity`; the bounded-∀ folds them into `andFold`. -/

/-- The body family: `entry[i] ≤ capacity`, i.e. `1·qᵢ + (−1)·capacity ≤ 0`, as a `RelPred` atom. -/
def belowCap (i : Nat) : RelPred :=
  .affineLe [((1 : Int), s!"q{i}"), ((-1 : Int), "capacity")] 0

/-- "All three queue entries are below capacity" as a bounded-∀ over `{0, 1, 2}`. -/
def allBelowCap : QuantPred Nat := .forall_ [0, 1, 2] belowCap

/-- A GOOD queue record: capacity 10, entries 3/5/2 — all below 10. -/
def qOk : Value :=
  .record [("q0", .int 3), ("q1", .int 5), ("q2", .int 2), ("capacity", .int 10)]

/-- A VIOLATING queue record: entry `q1` pushed to 12 > capacity 10 (one over-bound entry). -/
def qBad : Value :=
  .record [("q0", .int 3), ("q1", .int 12), ("q2", .int 2), ("capacity", .int 10)]

-- The bounded-∀ DISCRIMINATES: holds on the good record, FAILS on the one violating entry.
#guard allBelowCap.evalClear qOk == true
#guard allBelowCap.evalClear qBad == false

-- The DE-QUANTIFICATION preserves the bits: the compiled N-fold ∧ agrees on both records.
#guard (andFold [0, 1, 2] belowCap).eval qOk == true
#guard (andFold [0, 1, 2] belowCap).eval qBad == false
#guard allBelowCap.evalClear qOk == (andFold [0, 1, 2] belowCap).eval qOk
#guard allBelowCap.evalClear qBad == (andFold [0, 1, 2] belowCap).eval qBad

/-- **`allBelowCap_discriminates` — PROVED (non-vacuity, as a theorem).** The bounded-∀ "all queue
entries below capacity" returns DIFFERENT bits on the good and the violating record — a genuine
discriminator, not a vacuous `:= true`. One over-bound entry flips it (`List.all` is fail-closed). -/
theorem allBelowCap_discriminates :
    allBelowCap.evalClear qOk = true ∧ allBelowCap.evalClear qBad = false := by
  constructor <;> rfl

/-- **`allBelowCap_dequantifies` — PROVED.** The bounded-∀ equals its N-fold-∧ compilation on BOTH
records — so the de-quantification keystone (`forall_eq_andFold`) is non-vacuous: it carries a real,
discriminating predicate into the relational closure, both bits preserved. -/
theorem allBelowCap_dequantifies :
    allBelowCap.evalClear qOk = (andFold [0, 1, 2] belowCap).eval qOk ∧
    allBelowCap.evalClear qBad = (andFold [0, 1, 2] belowCap).eval qBad :=
  ⟨forall_eq_andFold _ _ qOk, forall_eq_andFold _ _ qBad⟩

/-! ### §6.2 — "ANY queue entry equals the target" as a bounded-∃ (the dual discriminator). -/

/-- The body family: `entry[i] = 5`, as an `affineEq` `RelPred`. -/
def isFive (i : Nat) : RelPred :=
  RelPred.affineEq [((1 : Int), s!"q{i}")] 5

/-- "Some queue entry equals 5" as a bounded-∃ over `{0, 1, 2}`. -/
def anyIsFive : QuantPred Nat := .exists_ [0, 1, 2] isFive

-- The bounded-∃ DISCRIMINATES: `qOk` has `q1 = 5` (holds); `qBad` has no entry = 5 (fails).
#guard anyIsFive.evalClear qOk == true
#guard anyIsFive.evalClear qBad == false
#guard anyIsFive.evalClear qOk == (orFold [0, 1, 2] isFive).eval qOk
#guard anyIsFive.evalClear qBad == (orFold [0, 1, 2] isFive).eval qBad

/-- **`anyIsFive_discriminates` — PROVED (non-vacuity, the ∃ side).** The bounded-∃ "some entry = 5"
returns DIFFERENT bits: true where an entry matches (`qOk.q1 = 5`), false where none does (`qBad`). A
genuine discriminator — `List.any` is satisfied by exactly one witness and unsatisfiable without. -/
theorem anyIsFive_discriminates :
    anyIsFive.evalClear qOk = true ∧ anyIsFive.evalClear qBad = false := by
  constructor <;> rfl

/-! ### §6.3 — The membership app example: "the sender is in the authorized set" — DISCHARGES on an
accepting witness, REJECTS a non-member even from an adversarial prover. -/

namespace MemberDemo

/-- Toy statement: the committed set root, as a `Nat` (a `Digest` stand-in). -/
abbrev Root := Nat
/-- Toy witness: a claimed membership path, as a `Nat`. -/
abbrev Path := Nat

/-- A toy Merkle-membership verifier: accepts iff `path = root + 1` (a stand-in for "the path
recomposes to the committed root" — the real check is the §8 Merkle AIR, `Crypto.BlindedSet`). -/
def merkleVerifier : Verifier Root Path := fun root path => decide (path = root + 1)

/-- A registry with the Merkle-membership verifier installed; every other kind fails closed. -/
def memberReg : Registry Root Path := fun
  | .merkleMembership => some merkleVerifier
  | _                 => none

/-- An ADVERSARIAL prover proposing a NON-member witness (`999`, ignoring the root). -/
def adversarialPath : Root → Option Path := fun _ => some 999

-- ACCEPT: an honest membership witness (`path = root + 1 = 43` at root `42`) is verified ⇒ the
-- sender-authorized atom DISCHARGES (`memberOf_discharges`).
#guard memberWitnessed memberReg .merkleMembership 42 43 == true
-- REJECT: a NON-member witness is rejected even though the adversarial prover proposes it.
#guard (adversarialPath 42).map (memberWitnessed memberReg .merkleMembership 42) == some false
-- FAIL CLOSED: cleartext evaluation of the membership atom is always `false` (set not in record).
#guard (senderAuthorized : QuantPred Nat).evalClear qOk == false

/-- **`member_demo_discharges` — PROVED.** The honest membership witness `(root 42, path 43)` makes
the `sender-authorized` atom `Discharged` — the §6.3 accept, through `memberOf_discharges`. -/
theorem member_demo_discharges :
    @Discharged Root Path (verifiableOfRegistry memberReg .merkleMembership) 42 43 :=
  memberOf_discharges memberReg .merkleMembership 42 43 (by decide)

/-- **`member_demo_rejects_nonmember` — PROVED (non-vacuity, the membership side).** A NON-member
witness is REJECTED by the verifier even when an adversarial prover proposes it: `memberWitnessed`
returns `false`, so the atom does NOT discharge. The gate, not the prover, decides — membership is a
genuine discriminator (accepts a member, rejects a non-member). -/
theorem member_demo_rejects_nonmember (find : Root → Option Path)
    (_hfound : find 42 = some 999) :
    memberWitnessed memberReg .merkleMembership 42 999 = false := by decide

end MemberDemo

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over every keystone). -/

#assert_axioms forall_eq_andFold
#assert_axioms exists_eq_orFold
#assert_axioms compile_sound
#assert_axioms andFold_budget
#assert_axioms orFold_budget
#assert_axioms memberOf_discharges
#assert_axioms senderAuthorized_is_memberOf
#assert_axioms memberOf_no_cleartext_compile
#assert_axioms memberOf_clear_fails_closed
#assert_axioms allBelowCap_discriminates
#assert_axioms allBelowCap_dequantifies
#assert_axioms anyIsFive_discriminates
#assert_axioms MemberDemo.member_demo_discharges
#assert_axioms MemberDemo.member_demo_rejects_nonmember

end Dregg2.Authority.QuantifiedPredicate
