/-
# Dregg2.Circuit.AccountsCommit — the `accounts` growth carrier (sorted-`Finset` list digest).

`createCellA` / `spawnA` grow `accounts : Finset CellId`. The honest commitment is the Poseidon
list-sponge over the canonical sorted account index (`k.accounts.sort (· ≤ ·)`), reusing
`ListCommit.listDigest` + the REGROUNDED `ListCommitRegrounded.listDigest_binds_or_collides`. The
`accountsComponent` smart constructor is the `ActiveComponent` shape for account-growth effects
paired with other touched fields.

## ⚑ THE FINDING (2026-08-01) — `ActiveComponent.binds` NEVER NEEDED RE-TYPING

An earlier pass measured this site as "the one place where the per-instance form provably does not
apply": `accountsComponent` took `(hN : compressNInjective cN) (hLE : listLeafInjective LE)` as
STRUCTURE DATA and consumed them in its `binds` field; `binds` is UNIVERSALLY QUANTIFIED over
`(pre, args, post)`, so a `¬ Coll` SIDE CONDITION on it would have had to be universally quantified
too — which is injectivity again, rewritten. The conclusion drawn was that only
conclusion-weakening works, and therefore that `ActiveComponent.binds` itself has to be RE-TYPED
to `… ∨ Resid`, gating ~25 declarations across the `Inst/*A.lean` family and the five
`EffectCommit{2,2Dual,3,4,5}` apexes.

**That conclusion is wrong, and the reason is worth stating once.** `binds` has type

    ∀ (pre : St) (args : Args) (post : RecordKernelState),
      digest post = expected pre args → postClause pre args post

and `postClause : St → Args → RecordKernelState → Prop` is ALREADY the per-instance-indexed
conclusion slot. Putting the residual INSIDE `postClause` makes `binds`'s own type read

    ∀ pre args post, digest post = expected pre args →
      (post.accounts = expectedAccounts pre args ∨ AccountsResid … pre args post)

which is LITERALLY the sound `_or_collides` shape — the residual is instantiated at the very triple
the binder quantifies over, so each instance is PRICED. It is not the free shirk: the refuted
`P ∨ (∃ xs ys, xs ≠ ys ∧ h xs = h ys)` is free because its right disjunct does not mention the
instance and pigeonhole proves it outright; `AccountsResid LE cN ea pre args post` names the ONE
pair `(accountsSorted post, (ea pre args).sort (· ≤ ·))` and is FALSE at every instance where those
two lists do not actually collide (`accountsResid_dischargeable`, below, proves the honest prover
discharges it for free at EVERY carrier).

So the blast radius is the THREE `accountsComponent` consumers plus their `apex_iff_*` theorems —
not the `ActiveComponent` interface, not the five apexes, not the ~59 other component
constructors. `ActiveComponent` is UNTOUCHED by this file.

⚠ WHAT THIS DOES NOT SAY. The same move works for `EffectCommit2.listComponent`,
`funcComponent` and `keyedComponent` — each has its own `postClause` slot and each still carries a
refuted floor (`compressNInjective` / an uncountable-domain `Function.Injective D`) as structure
data. They are NOT ported here. A reader must not read "`ActiveComponent` needs no re-type" as
"`ActiveComponent`'s other constructors are floor-free"; they are not.

## The port, precisely
  * `binds` is HYPOTHESIS-FREE (S2): `listDigest_binds_or_collides`, no injectivity anywhere.
  * `encodes` survives the widened `postClause` because a `ListColl` at a named pair FORCES equal
    digests (`listDigest_eq_of_listColl`) — completeness is not weakened by the new disjunct.
  * the S3 restoration happens at the CONSUMER (`apex_iff_*`), where `¬ AccountsResid …` is a
    per-instance hypothesis at the named triple, discharged through the EXISTING baselined bridge
    `ListCommitRegrounded.noColl_of_carriers` by the `*_full_sound` theorems that already bind
    `hN`/`hLE`. NO new `_of_CR` bridge is minted here — that would be carrier-neutral and would
    trip the accrual gate.

ADDITIVE: imports `EffectCommit2` (reuses `ActiveComponent`) + `ListCommitRegrounded`; edits none
of the keystones.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.ListCommitRegrounded

namespace Dregg2.Circuit.AccountsCommit

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.ListCommitRegrounded
open Dregg2.Exec

set_option linter.dupNamespace false

/-- Canonical sorted account index (the list the digest sponges). -/
def accountsSorted (k : RecordKernelState) : List CellId :=
  k.accounts.sort (· ≤ ·)

/-- Equal sorted account lists force equal `accounts` Finsets. -/
theorem accounts_eq_of_sorted_eq (s t : Finset CellId)
    (h : s.sort (· ≤ ·) = t.sort (· ≤ ·)) : s = t := by
  have h' := congr_arg List.toFinset h
  rwa [Finset.sort_toFinset, Finset.sort_toFinset] at h'

theorem accountsSorted_eq_of_eq (s t : Finset CellId) (h : s = t) :
    s.sort (· ≤ ·) = t.sort (· ≤ ·) := by rw [h]

/-! ## §1 — the residual, and the two facts that make the widened `postClause` work. -/

/-- **`AccountsResid LE cN ea pre args post`** — the NAMED, PER-INSTANCE residual of the accounts
binding: a `ListCommitRegrounded.ListColl` at the ONE pair of lists this instance sponges, the post
kernel's sorted account index against the spec's predicted one. Distinctness is intrinsic to
`ListColl`, and `ListColl.extracts` turns it into a genuine collision of `cN` or of `LE`. -/
def AccountsResid {St Args : Type} (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (expectedAccounts : St → Args → Finset CellId)
    (pre : St) (args : Args) (post : RecordKernelState) : Prop :=
  ListColl LE cN (accountsSorted post) ((expectedAccounts pre args).sort (· ≤ ·))

/-- A `ListColl` at a named pair FORCES equal `listDigest`s — `listDigest LE cN = cN ∘ (·.map LE)`,
so the sponge-side event IS the digest equality and the leaf-side event implies it. This is what
keeps COMPLETENESS (`encodes`) total after the residual is admitted into `postClause`: the new
disjunct is not a hole in the ← direction. -/
theorem listDigest_eq_of_listColl {α : Type} (LE : α → ℤ) (cN : List ℤ → ℤ) {xs ys : List α}
    (h : ListColl LE cN xs ys) : listDigest LE cN xs = listDigest LE cN ys := by
  rcases h with ⟨_, heq⟩ | ⟨_, hmap⟩
  · exact heq
  · unfold listDigest; rw [hmap]

/-! ## §2 — the smart constructor, FLOOR-FREE. -/

/-- **`accountsComponent`** — an `ActiveComponent` for `accounts` growth: digest is the sorted-list
sponge; `postClause` is FULL `Finset` equality (a drop/reorder of an existing id is REJECTED) **OR
the NAMED per-instance residual at the pair this instance sponges**.

⚑ NO `compressNInjective` / `listLeafInjective` — the floor binders this constructor used to take
as structure data are GONE, and `binds` is `listDigest_binds_or_collides`, which assumes nothing.
See the ⚑ FINDING block at the top of this file for why this needed no change to
`ActiveComponent`. -/
def accountsComponent {St Args : Type} (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (expectedAccounts : St → Args → Finset CellId) : ActiveComponent St Args where
  digest    := fun k => listDigest LE cN (accountsSorted k)
  expected  := fun pre args => listDigest LE cN ((expectedAccounts pre args).sort (· ≤ ·))
  postClause := fun pre args post =>
    post.accounts = expectedAccounts pre args ∨ AccountsResid LE cN expectedAccounts pre args post
  binds     := fun pre args post h =>
    (listDigest_binds_or_collides LE cN (accountsSorted post)
        ((expectedAccounts pre args).sort (· ≤ ·)) h).imp
      (accounts_eq_of_sorted_eq _ _) id
  encodes   := fun _ _ _ h =>
    h.elim (fun he => listDigest_congr LE cN (accountsSorted_eq_of_eq _ _ he))
      (fun hc => listDigest_eq_of_listColl LE cN hc)

/-! ## §3 — TEETH. The residual is FREE FOR THE HONEST PROVER, FIRES at a broken sponge, and is
LOAD-BEARING (deleting it makes the clause FALSE). -/

/-- **DISCHARGEABLE, at EVERY carrier.** An honest post — one whose account set IS the predicted one
— refutes the residual outright, for any `LE` and any `cN`. So the per-instance side condition the
consumers carry costs the honest prover nothing; it prices only equivocation. (The analogue of
`DeployedMapDenotation.openResidS_dischargeable`.) -/
theorem accountsResid_dischargeable {St Args : Type} (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (expectedAccounts : St → Args → Finset CellId)
    (pre : St) (args : Args) (post : RecordKernelState)
    (h : post.accounts = expectedAccounts pre args) :
    ¬ AccountsResid LE cN expectedAccounts pre args post := by
  have hs : accountsSorted post = (expectedAccounts pre args).sort (· ≤ ·) :=
    accountsSorted_eq_of_eq _ _ h
  rintro (⟨hne, _⟩ | ⟨hne, _⟩) <;> exact hne (by rw [hs])

private def leafA : CellId → ℤ := fun n => (n : ℤ)
private def constCN : List ℤ → ℤ := fun _ => 0

private theorem leafA_inj : Function.Injective leafA := by
  intro a b h; exact Nat.cast_injective h

/-- **THE RESIDUAL FIRES exactly where the deployed object is broken.** At a CONSTANT sponge (the
maximally-broken carrier) every wrong post-state satisfies the residual — so the widened
`postClause` degrades to the collision disjunct precisely when the sponge cannot bind, and never
silently claims the good branch. A residual that could not fire would be decoration. -/
theorem accountsResid_fires_at_broken_sponge {St Args : Type}
    (expectedAccounts : St → Args → Finset CellId)
    (pre : St) (args : Args) (post : RecordKernelState)
    (hne : post.accounts ≠ expectedAccounts pre args) :
    AccountsResid leafA constCN expectedAccounts pre args post := by
  refine Or.inl ⟨?_, rfl⟩
  intro hmap
  exact hne (accounts_eq_of_sorted_eq _ _ (List.map_injective_iff.mpr leafA_inj hmap))

private def kOne : RecordKernelState :=
  { accounts := {1}, cell := fun _ => .record [], caps := fun _ => [] }

private def eaEmpty : Unit → Unit → Finset CellId := fun _ _ => (∅ : Finset CellId)

/-- **⚑ THE RESIDUAL IS LOAD-BEARING** — the mutation canary for this port. `accountsComponent`'s
`postClause` with the residual disjunct DELETED is FALSE: at a constant sponge the digests agree
while the account sets do not. Anything that "ports" this constructor by dropping the disjunct is
not a port, it is a refuted statement. -/
theorem accountsComponent_left_disjunct_alone_false :
    ¬ ∀ (pre args : Unit) (post : RecordKernelState),
        (accountsComponent leafA constCN eaEmpty).digest post
            = (accountsComponent leafA constCN eaEmpty).expected pre args →
          post.accounts = eaEmpty pre args := by
  intro hall
  have h : kOne.accounts = eaEmpty () () := hall () () kOne rfl
  simp only [kOne, eaEmpty] at h
  exact absurd h (by decide)

#assert_axioms accounts_eq_of_sorted_eq
#assert_axioms listDigest_eq_of_listColl
#assert_axioms accountsResid_dischargeable
#assert_axioms accountsResid_fires_at_broken_sponge
#assert_axioms accountsComponent_left_disjunct_alone_false

end Dregg2.Circuit.AccountsCommit
