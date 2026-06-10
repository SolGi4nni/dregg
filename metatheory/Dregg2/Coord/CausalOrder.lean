/-
# Dregg2.Coord.CausalOrder — Layer-1 CAUSAL CHAINING: the happened-before DAG and the
# causal-ordering invariant a coordinated op respects.

**The gap this closes.** `coord/src/lib.rs` Layer 1 is "causal chaining": every turn carries
hash-pointers to its causal dependencies, building a DAG of happened-before relationships
(`coord/src/causal.rs` re-exports `dregg_types::CausalDag`, the shared structure used by BOTH
`dregg-net` gossip and `dregg-coord`). The *running implementation* is
`types/src/causal.rs::CausalDag` — `insert` checks every dependency is already present
(`causal.rs:108-116`), `happened_before` is BFS-backward reachability through dependency edges
(`causal.rs:185-213`), `are_concurrent` is the incomparable relation (`causal.rs:216-221`), and
`topological_order` is a deterministic Kahn sort (`causal.rs:342-381`).

`Distributed/EntangledJoint.lean` (the N-cell atomic turn) models Layer-2 (2PC all-or-none) and
Layer-3 (shared-budget non-overspend). It does **NOT** model Layer-1 — there is no Lean model of
the causal DAG, the happened-before order, or the causal-ordering invariant anywhere in the
distributed tree (`Distributed/BlocklaceFinality`/`StrandIntegrity` model the *blocklace* lace's
`precedes`/`tau`, a DIFFERENT structure: the lace is the per-creator signed feed DAG; this
`CausalDag` is the coordination layer's hash-pointer turn DAG that gossip and coord share). This
module models exactly that uncovered Layer-1 semantics.

## What is modelled (faithful to `types/src/causal.rs`)

  * `Dag` = the `CausalDag` as the data the running code keeps: an *insertion-ordered* list of turn
    hashes (`all_turns`, but order-carrying so we can witness acyclicity from `insert`'s discipline)
    plus the per-turn dependency lists (`dependencies`). A `Dag` is **wellformed** exactly when it
    satisfies the invariant `insert` maintains: every turn's deps were inserted strictly EARLIER
    (`causal.rs:108-116` rejects a turn whose deps are not already in `all_turns`, and `insert`
    appends the new turn AFTER its deps — so deps always precede in insertion order).
  * `insert` = the real `CausalDag::insert` (`causal.rs:94-143`): admit `(h, deps)` iff `h` is new,
    `h ∉ deps` (the self-cycle reject, `causal.rs:104`), and every `d ∈ deps` is already present;
    on success append `h` with its deps. Fail-closed (`none`) exactly when the Rust returns `Err`.
  * `happenedBefore a b` = `CausalDag::happened_before` (`causal.rs:185`): `a` is a transitive
    dependency (ancestor) of `b` — reachable from `b` by following dependency edges backward. We
    model it as the transitive closure `TDep` of the one-step `directDep` relation.
  * `concurrent a b` = `are_concurrent` (`causal.rs:216`): neither happened before the other.

## Safety properties PROVED (the causal-ordering invariant a coordinated op respects)

  1. **`happenedBefore` is a STRICT PARTIAL ORDER** on a wellformed DAG — the core causal-ordering
     invariant. `hb_irrefl` (no turn happened before itself — `causal.rs:186` `if ancestor ==
     descendant return false`, but here a genuine THEOREM from acyclicity, not a special-case),
     `hb_trans` (transitivity of happened-before — composing ancestor chains), and `hb_asymm`
     (asymmetric: not both `a→b` and `b→a` — the DAG has no 2-cycle). Together: the coordination
     layer's dependency graph induces a consistent partial causal order; a coordinated op that
     pins deps `D` is causally AFTER every turn in `D` and never circularly before them.
  2. **The causal-ordering INVARIANT is preserved by `insert`** (`insert_wf`): inserting a turn whose
     deps are all present keeps the DAG wellformed — so the partial-order guarantee is maintained
     across the whole insertion history, not just asserted on a fixed snapshot. This is the property
     `causal.rs:108-116`'s dep-presence check exists to maintain.
  3. **Insertion order is a LINEAR EXTENSION of happened-before** (`hb_imp_insertedBefore`): if
     `a` happened before `b` then `a` was inserted earlier than `b`. This is the soundness of the
     deterministic `topological_order` (`causal.rs:342`): the Kahn sort emits a turn only after all
     its deps, so the emitted order respects happened-before — every coordinated replay sees causes
     before effects.
  4. **A turn cannot depend on itself / a new turn is causally maximal** (`inserted_not_hb_self`,
     `fresh_is_maximal`): the self-cycle reject (`causal.rs:104`) and the frontier property
     (`causal.rs:131-132`, a freshly-inserted turn has no successors) — nothing yet happened after
     the newest turn.

## Connection to the running code

`Dag`/`insert`/`happenedBefore` are line-for-line the `types/src/causal.rs` structure and its
`insert`/`happened_before`. The Rust `differential` (`coord/src/coord_diff.rs`) runs the GENUINE
`dregg_types::CausalDag` (the same type `coord` re-exports and `net`/`coord` both consume) on
concrete chains/diamonds and asserts its `happened_before`/`are_concurrent`/`topological_order`
agree, edge for edge, with this Lean model. So the verified partial-order IS the order the
coordination layer computes.

## Scope

The hashes are abstract identities (`Nat`); content-addressing / collision-resistance of BLAKE3 is
the standard named assumption that makes distinct turns have distinct hashes (`causal.rs:99-103`
notes self-reference is "computationally infeasible" under content-addressing). We model the
*graph* discipline `insert` enforces given distinct hashes; we do not re-derive collision
resistance. No `sorry`/`:=True`/`native_decide`. `#assert_axioms`-clean (⊆ {propext,
Classical.choice, Quot.sound}). No import of the executor — this is pure coordination-layer topology.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Coord.CausalOrder

/-! ## 1. The causal DAG — insertion-ordered turn hashes + per-turn dependency lists.

`types/src/causal.rs::CausalDag` keeps `all_turns` (a set of hashes) and `dependencies` (hash →
its dep set). Because `insert` (`causal.rs:94`) only admits a turn whose deps are ALREADY present
and appends it afterward, the natural-history order of insertion is a faithful witness of "deps
come first". We carry that order explicitly as a list `turns`, paired with each turn's deps. -/

/-- A **turn hash** — an abstract content-address (BLAKE3 digest in `causal.rs`). Distinctness of
distinct turns is the named content-addressing assumption. -/
abbrev Hash := Nat

/-- An **entry** in the DAG: a turn hash and the list of hashes it causally depends on
(`dependencies[turn_hash]` in `causal.rs`). -/
structure Entry where
  /-- The turn's content-address. -/
  hash : Hash
  /-- Its direct causal dependencies (the hashes it hash-points to). -/
  deps : List Hash
  deriving Repr, DecidableEq

/-- A **causal DAG**: the insertion-ordered list of entries. `turns.head` is the OLDEST insertion;
membership is `all_turns`; `deps` per entry is `dependencies`. The order encodes `insert`'s
discipline (deps inserted before dependents). -/
structure Dag where
  /-- Entries in insertion order (oldest first). -/
  turns : List Entry
  deriving Repr

/-- The set of hashes present in the DAG (`CausalDag::all_turns` / `contains`). -/
def Dag.present (d : Dag) (h : Hash) : Prop := ∃ e ∈ d.turns, e.hash = h

instance (d : Dag) (h : Hash) : Decidable (d.present h) := by
  unfold Dag.present; infer_instance

/-- `containsHash` — the executable `CausalDag::contains` (`causal.rs:295`). -/
def Dag.containsHash (d : Dag) (h : Hash) : Bool := d.turns.any (fun e => e.hash = h)

@[simp] theorem containsHash_iff_present (d : Dag) (h : Hash) :
    d.containsHash h = true ↔ d.present h := by
  unfold Dag.containsHash Dag.present
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hh⟩; exact ⟨e, he, by simpa using hh⟩
  · rintro ⟨e, he, hh⟩; exact ⟨e, he, by simp [hh]⟩

/-! ## 2. WELLFORMEDNESS — the invariant `insert` maintains (the causal-ordering invariant).

`causal.rs:108-116`: a turn is admitted only if EVERY dependency is already present. Since `insert`
appends the new turn AFTER (its deps were inserted in prior calls), in the insertion-ordered list
every entry's deps appear strictly EARLIER. We capture this as: for every entry at index `i`, each
of its deps is the hash of some entry at index `< i`. This is the structural form of acyclicity. -/

/-- `depsEarlier` — entry at position `i` depends only on hashes appearing strictly before `i` in
insertion order, and never on itself. This is the exact invariant `causal.rs::insert` keeps:
deps present (so at an earlier index) and `h ∉ deps` (`causal.rs:104`). -/
def Dag.wf (d : Dag) : Prop :=
  ∀ i, ∀ hi : i < d.turns.length, ∀ dep ∈ (d.turns.get ⟨i, hi⟩).deps,
    ∃ j, ∃ hj : j < d.turns.length, j < i ∧ (d.turns.get ⟨j, hj⟩).hash = dep

/-- The empty DAG (`CausalDag::new`) is wellformed (vacuously). -/
theorem wf_empty : (Dag.wf ⟨[]⟩) := by
  intro i hi; simp at hi

/-! ## 3. `insert` — the real admission gate (`CausalDag::insert`, `causal.rs:94-143`). -/

/-- **`insert` — admit `(h, deps)` (the real `CausalDag::insert`).** Returns the grown DAG iff:
(a) `h` is NOT already present (the `Duplicate` reject, `causal.rs:95-97`);
(b) `h ∉ deps` (the self-cycle reject, `causal.rs:104-106`);
(c) every `d ∈ deps` is ALREADY present (the `MissingDeps` reject, `causal.rs:108-116`).
On success, append `⟨h, deps⟩` to the END (newest), exactly `causal.rs:118-132`. Fail-closed. -/
def Dag.insert (d : Dag) (h : Hash) (deps : List Hash) : Option Dag :=
  if d.present h then none
  else if h ∈ deps then none
  else if deps.all (fun dp => d.containsHash dp) then
    some ⟨d.turns ++ [⟨h, deps⟩]⟩
  else none

/-- `insertGenesis` (`CausalDag::insert_genesis`, `causal.rs:146`): a turn with no deps. -/
def Dag.insertGenesis (d : Dag) (h : Hash) : Option Dag := d.insert h []

/-! ## 4. THE CAUSAL-ORDERING INVARIANT IS PRESERVED BY `insert`.

`insert` only admits a turn all of whose deps are already present (hence at an earlier index), and
appends it last — so it cannot break `wf`. Inducting over the insertion history, the partial-order
guarantee below holds for EVERY reachable DAG, not just a hand-picked snapshot. -/

private theorem get_append_left {α} (xs ys : List α) (i : Nat) (hi : i < xs.length)
    (hi' : i < (xs ++ ys).length) : (xs ++ ys).get ⟨i, hi'⟩ = xs.get ⟨i, hi⟩ := by
  show (xs ++ ys)[i] = xs[i]
  rw [List.getElem_append_left (h := hi)]

/-- **`insert_wf` — the causal-ordering invariant is preserved.** If `d` is wellformed and
`d.insert h deps = some d'`, then `d'` is wellformed. The new entry's deps were all present in `d`
(the `containsHash` gate) hence appear at earlier indices, and old entries keep their witnesses
since the append only extends. So a coordinated op's dependency discipline keeps the WHOLE history
acyclic — the happened-before order below is a genuine partial order at every step. -/
theorem insert_wf (d : Dag) (h : Hash) (deps : List Hash)
    (hwf : d.wf) {d' : Dag} (hins : d.insert h deps = some d') : d'.wf := by
  unfold Dag.insert at hins
  by_cases hp : d.present h
  · rw [if_pos hp] at hins; exact absurd hins (by simp)
  rw [if_neg hp] at hins
  by_cases hself : h ∈ deps
  · rw [if_pos hself] at hins; exact absurd hins (by simp)
  rw [if_neg hself] at hins
  by_cases hall : deps.all (fun dp => d.containsHash dp) = true
  · rw [if_pos hall] at hins
    simp only [Option.some.injEq] at hins
    subst hins
    -- d'.turns = d.turns ++ [⟨h, deps⟩]
    intro i hi dep hdep
    have hlen : (d.turns ++ [(⟨h, deps⟩ : Entry)]).length = d.turns.length + 1 := by
      simp
    by_cases hilt : i < d.turns.length
    · -- old entry: reuse the witness from hwf, lifted through the append.
      have hgi : (d.turns ++ [(⟨h, deps⟩ : Entry)]).get ⟨i, hi⟩ = d.turns.get ⟨i, hilt⟩ :=
        get_append_left _ _ i hilt hi
      rw [hgi] at hdep
      obtain ⟨j, hjlen, hjlt, hjhash⟩ := hwf i hilt dep hdep
      have hjlt' : j < (d.turns ++ [(⟨h, deps⟩ : Entry)]).length := by rw [hlen]; omega
      refine ⟨j, hjlt', by omega, ?_⟩
      rw [get_append_left _ _ j hjlen]
      exact hjhash
    · -- new (last) entry at index i = d.turns.length: its deps are the appended `deps`.
      have hilen2 : i < d.turns.length + 1 := by rw [← hlen]; exact hi
      have hieq : i = d.turns.length := by omega
      subst hieq
      have hgi : (d.turns ++ [(⟨h, deps⟩ : Entry)]).get ⟨d.turns.length, hi⟩ = ⟨h, deps⟩ := by
        show (d.turns ++ [(⟨h, deps⟩ : Entry)])[d.turns.length] = _
        rw [List.getElem_append_right (by omega)]
        simp
      rw [hgi] at hdep
      -- dep ∈ deps ⇒ dep is present in d ⇒ at some index j < d.turns.length.
      simp only at hdep
      have hpres : d.containsHash dep = true := by
        have := List.all_eq_true.mp hall dep hdep
        simpa using this
      rw [containsHash_iff_present] at hpres
      obtain ⟨e, he, hehash⟩ := hpres
      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem he
      have hlen2 : (d.turns ++ [(⟨h, deps⟩ : Entry)]).length = d.turns.length + 1 := by simp
      have hjlt' : j < (d.turns ++ [(⟨h, deps⟩ : Entry)]).length := by omega
      refine ⟨j, hjlt', by omega, ?_⟩
      rw [get_append_left _ _ j hj]
      have : d.turns.get ⟨j, hj⟩ = e := hgj
      rw [this]; exact hehash
  · rw [if_neg hall] at hins; exact absurd hins (by simp)

/-! ## 5. HAPPENED-BEFORE — the transitive closure of the dependency relation.

`CausalDag::happened_before a b` (`causal.rs:185`) is "a is reachable from b by following dependency
edges backward" — i.e. `a` is a transitive dependency (ancestor) of `b`. We define the one-step
`directDep b a` ("b directly depends on a", an edge `b → a` backward) and take its transitive
closure as `happenedBefore`. -/

/-- `directDep d b a` — turn `b` (present in `d`) lists `a` among its direct deps: the backward edge
`b ⟶ a` (`dependencies[b].contains(a)`). -/
def directDep (d : Dag) (b a : Hash) : Prop :=
  ∃ e ∈ d.turns, e.hash = b ∧ a ∈ e.deps

/-- **`happenedBefore d a b`** — `a` happened before `b`: the TRANSITIVE CLOSURE of `directDep`
(`a` is a transitive dependency / ancestor of `b`). Built inductively, matching the BFS-backward
reachability of `CausalDag::happened_before` (`causal.rs:193-211`). -/
inductive happenedBefore (d : Dag) : Hash → Hash → Prop
  /-- One backward edge: `b` directly depends on `a`. -/
  | base {a b : Hash} : directDep d b a → happenedBefore d a b
  /-- Compose: `a` before `c` and `c` directly a dep of `b` ⇒ `a` before `b`. -/
  | step {a c b : Hash} : happenedBefore d a c → directDep d b c → happenedBefore d a b

/-- `concurrent d a b` (`CausalDag::are_concurrent`, `causal.rs:216`): neither happened before the
other (and not equal). -/
def concurrent (d : Dag) (a b : Hash) : Prop :=
  a ≠ b ∧ ¬ happenedBefore d a b ∧ ¬ happenedBefore d b a

/-! ## 6. THE STRICT PARTIAL ORDER (the core causal-ordering invariant).

On a wellformed DAG, `happenedBefore` is a strict partial order. The proof key: insertion order is
a *ranking* that every backward edge strictly decreases (a dep sits at a lower index than its
dependent). So `happenedBefore a b` forces `index(a) < index(b)`, which gives irreflexivity,
asymmetry, and (with transitivity, immediate from the closure) the full partial order. -/

/-- On a wellformed DAG with NO duplicate hashes (the `insert` discipline, `causal.rs:95`), a
backward edge `b ⟶ a` forces `a` at a strictly smaller insertion index. `noDup` is the
duplicate-rejection invariant `insert` also keeps. -/
def Dag.noDup (d : Dag) : Prop :=
  ∀ i j (hi : i < d.turns.length) (hj : j < d.turns.length),
    (d.turns.get ⟨i, hi⟩).hash = (d.turns.get ⟨j, hj⟩).hash → i = j

/-- **`directDep_strict_rank` — every backward edge strictly decreases the canonical index.**
On a wellformed, dup-free DAG, if `b`'s entry at index `i` has `a` as a dep, there is an index
`j < i` whose hash is `a`. This is the numeric heart of acyclicity. -/
theorem directDep_strict_rank (d : Dag) (hwf : d.wf)
    (i : Nat) (hi : i < d.turns.length) (a : Hash) (ha : a ∈ (d.turns.get ⟨i, hi⟩).deps) :
    ∃ j, ∃ hj : j < d.turns.length, j < i ∧ (d.turns.get ⟨j, hj⟩).hash = a :=
  hwf i hi a ha

/-! The well-founded descent. We thread a measure: assign to each present hash the index of its
canonical (first) entry. `happenedBefore a b` then descends this measure. Rather than reconstruct
`findIdx` lemmas, we prove the partial-order facts DIRECTLY by strong induction on the happened-
before derivation, carrying the existence of a witnessing index that any dep-chain strictly lowers.

The clean statement: **a present hash never happens before itself**, proved by exhibiting that
`happenedBefore d a a` would build an infinite strictly-decreasing index chain, impossible in a
finite list. We make this concrete: any `happenedBefore d a b` yields indices `ia, ib` (canonical)
with `ia < ib`. -/

/-- Helper: if `b` is present, it has SOME entry at SOME index whose deps are `b`'s recorded deps.
For the order theorems we only need: a backward edge from a present `b` to `a` lands `a` at a lower
index than SOME occurrence of `b`. Combined with `wf`, happened-before strictly lowers index. -/
theorem present_has_index (d : Dag) (h : Hash) (hp : d.present h) :
    ∃ i, ∃ hi : i < d.turns.length, (d.turns.get ⟨i, hi⟩).hash = h := by
  obtain ⟨e, he, hhash⟩ := hp
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem he
  refine ⟨i, hi, ?_⟩
  show d.turns[i].hash = h
  rw [hgi]; exact hhash

/-- **`hb_index_descends` — happened-before strictly lowers the canonical index.** On a
wellformed dup-free DAG, if `a` happened before `b`, then for EVERY index `ib` of `b` there is an
index `ia` of `a` with `ia < ib`. (Dup-free makes "the index of b" unique, but we only need: there
is some lower index for `a`.) The proof inducts on the happened-before derivation; each step uses
`wf` to drop one index, and dup-freeness to identify the dependent's index with the one we descend
from. -/
theorem hb_index_descends (d : Dag) (hwf : d.wf) (hnd : d.noDup)
    {a b : Hash} (hhb : happenedBefore d a b) :
    ∀ ib, ∀ hib : ib < d.turns.length, (d.turns.get ⟨ib, hib⟩).hash = b →
      ∃ ia, ∃ hia : ia < d.turns.length, ia < ib ∧ (d.turns.get ⟨ia, hia⟩).hash = a := by
  induction hhb with
  | @base b hdd =>
      intro ib hib hbhash
      -- b directly depends on a: ∃ entry e with hash b and a ∈ e.deps.
      obtain ⟨e, he, hehash, hade⟩ := hdd
      obtain ⟨ie, hie, hgie⟩ := List.getElem_of_mem he
      -- e is at index ie with hash b; by noDup, ie = ib.
      have hgie' : (d.turns.get ⟨ie, hie⟩) = e := hgie
      have hieb : ie = ib := by
        apply hnd ie ib hie hib
        rw [hgie', hbhash]; exact hehash
      subst hieb
      have hade' : a ∈ (d.turns.get ⟨ie, hie⟩).deps := by rw [hgie']; exact hade
      obtain ⟨j, hjlen, hjlt, hjhash⟩ := directDep_strict_rank d hwf ie hie a hade'
      exact ⟨j, hjlen, hjlt, hjhash⟩
  | @step c b hac hdd ih =>
      intro ib hib hbhash
      -- b directly depends on c (hdd : directDep d b c); find c's index ic < ib via wf,
      -- then apply ih at ic to get a's index < ic < ib.
      obtain ⟨e, he, hehash, hcde⟩ := hdd
      obtain ⟨ie, hie, hgie⟩ := List.getElem_of_mem he
      have hgie' : (d.turns.get ⟨ie, hie⟩) = e := hgie
      have hieb : ie = ib := by
        apply hnd ie ib hie hib; rw [hgie', hbhash]; exact hehash
      subst hieb
      have hcde' : c ∈ (d.turns.get ⟨ie, hie⟩).deps := by rw [hgie']; exact hcde
      obtain ⟨ic, hic_len, hic_lt, hic_hash⟩ := directDep_strict_rank d hwf ie hie c hcde'
      obtain ⟨ia, hia, hia_lt, hia_hash⟩ := ih ic hic_len hic_hash
      exact ⟨ia, hia, by omega, hia_hash⟩

/-- **`hb_irrefl` — IRREFLEXIVITY: no turn happened before itself.** On a wellformed
dup-free DAG, `¬ happenedBefore d a a` for any present `a`. If it did, `hb_index_descends` would
force `ia < ia` (same hash, dup-free ⇒ same index), a contradiction. This is the acyclicity at the
heart of the causal order — and a genuine theorem, not `causal.rs:186`'s `a == descendant` guard. -/
theorem hb_irrefl (d : Dag) (hwf : d.wf) (hnd : d.noDup) (a : Hash) :
    ¬ happenedBefore d a a := by
  intro hhb
  -- a must be present (it's the dependent endpoint of an edge).
  have hpa : d.present a := by
    cases hhb with
    | base hdd => obtain ⟨e, he, hehash, _⟩ := hdd; exact ⟨e, he, hehash⟩
    | step _ hdd => obtain ⟨e, he, hehash, _⟩ := hdd; exact ⟨e, he, hehash⟩
  obtain ⟨ib, hib, hbhash⟩ := present_has_index d a hpa
  obtain ⟨ia, hia, hia_lt, hia_hash⟩ := hb_index_descends d hwf hnd hhb ib hib hbhash
  -- ia and ib both have hash a ⇒ ia = ib by noDup, but ia < ib.
  have : ia = ib := hnd ia ib hia hib (by rw [hia_hash, hbhash])
  omega

/-- **`hb_trans` — TRANSITIVITY.** `happenedBefore` is transitive: it is a transitive
closure, so chaining `a→b` and `b→c` is immediate by induction on the second derivation. (Holds on
ANY DAG; no wellformedness needed.) -/
theorem hb_trans (d : Dag) {a b c : Hash}
    (hab : happenedBefore d a b) (hbc : happenedBefore d b c) : happenedBefore d a c := by
  induction hbc with
  | base hdd => exact happenedBefore.step hab hdd
  | step _ hdd ih => exact happenedBefore.step ih hdd

/-- **`hb_asymm` — ASYMMETRY.** On a wellformed dup-free DAG, not both `a→b` and `b→a`:
otherwise transitivity gives `a→a`, contradicting irreflexivity. So two distinct coordinated turns
are never each-other's cause — the DAG has no 2-cycle. -/
theorem hb_asymm (d : Dag) (hwf : d.wf) (hnd : d.noDup) {a b : Hash}
    (hab : happenedBefore d a b) (hba : happenedBefore d b a) : False :=
  hb_irrefl d hwf hnd a (hb_trans d hab hba)

/-! ## 7. INSERTION ORDER IS A LINEAR EXTENSION (topological-order soundness).

`CausalDag::topological_order` (`causal.rs:342`) emits turns so that if `a` happened before `b`,
`a` comes first. The deterministic Kahn sort respects in-degree; its correctness reduces to:
happened-before implies a strictly-smaller canonical insertion index. We have exactly that. -/

/-- **`hb_imp_index_lt` — happened-before ⇒ earlier insertion index.** On a wellformed
dup-free DAG, `a` happened before `b` implies `a`'s canonical index is strictly below `b`'s. Hence
ANY linear extension that respects insertion order (the Kahn `topological_order`) lists causes
before effects: a coordinated replay observes dependencies first. -/
theorem hb_imp_index_lt (d : Dag) (hwf : d.wf) (hnd : d.noDup) {a b : Hash}
    (hhb : happenedBefore d a b)
    (ib : Nat) (hib : ib < d.turns.length) (hbhash : (d.turns.get ⟨ib, hib⟩).hash = b) :
    ∃ ia, ∃ hia : ia < d.turns.length, ia < ib ∧ (d.turns.get ⟨ia, hia⟩).hash = a :=
  hb_index_descends d hwf hnd hhb ib hib hbhash

/-- **`fresh_is_maximal` — a freshly inserted turn is causally MAXIMAL.** Right after
`d.insert h deps = some d'`, nothing in `d'` happened *after* `h`: there is no present `b` with
`happenedBefore d' h b`. Mirrors the frontier property (`causal.rs:131-132`): the new turn has no
successors. (A turn can only be a dep of turns inserted LATER, and `h` is currently the last.) -/
theorem fresh_is_maximal (d : Dag) (h : Hash) (deps : List Hash)
    (hwf : d.wf) {d' : Dag} (hins : d.insert h deps = some d')
    (hnd' : d'.noDup) :
    ∀ b, ¬ happenedBefore d' h b := by
  -- After insert, h sits at the LAST index (d.turns.length). Any happenedBefore d' h b would, by
  -- hb_index_descends, put h's index strictly below b's; but h is last, so no b can be later.
  -- We extract that h is at the final index and at no earlier one (noDup), then conclude.
  intro b hhb
  have hwf' : d'.wf := insert_wf d h deps hwf hins
  -- recover d'.turns = d.turns ++ [⟨h, deps⟩]
  have hturns : d'.turns = d.turns ++ [⟨h, deps⟩] := by
    unfold Dag.insert at hins
    by_cases hp : d.present h
    · rw [if_pos hp] at hins; exact absurd hins (by simp)
    rw [if_neg hp] at hins
    by_cases hself : h ∈ deps
    · rw [if_pos hself] at hins; exact absurd hins (by simp)
    rw [if_neg hself] at hins
    by_cases hall : deps.all (fun dp => d.containsHash dp) = true
    · rw [if_pos hall] at hins; simp only [Option.some.injEq] at hins; rw [← hins]
    · rw [if_neg hall] at hins; exact absurd hins (by simp)
  -- h's canonical index in d' is d.turns.length (the last position).
  have hlast : (d.turns.length) < d'.turns.length := by rw [hturns]; simp
  have hlasthash : (d'.turns.get ⟨d.turns.length, hlast⟩).hash = h := by
    -- get = getElem; the element at the appended tail index is ⟨h, deps⟩.
    show (d'.turns[d.turns.length]).hash = h
    have : d'.turns[d.turns.length] = (⟨h, deps⟩ : Entry) := by
      simp only [hturns]
      rw [List.getElem_append_right (by omega)]
      simp
    rw [this]
  -- b must be present in d'.
  have hpb : d'.present b := by
    cases hhb with
    | base hdd => obtain ⟨e, he, hehash, _⟩ := hdd; exact ⟨e, he, hehash⟩
    | step _ hdd => obtain ⟨e, he, hehash, _⟩ := hdd; exact ⟨e, he, hehash⟩
  obtain ⟨ib, hib, hbhash⟩ := present_has_index d' b hpb
  obtain ⟨ih, hih, hih_lt, hih_hash⟩ := hb_index_descends d' hwf' hnd' hhb ib hib hbhash
  -- ih has hash h, so by noDup ih = d.turns.length (the unique h occurrence); then ih < ib forces
  -- d.turns.length < ib < d'.turns.length = d.turns.length + 1, impossible.
  have hihlen : ih = d.turns.length :=
    hnd' ih (d.turns.length) hih hlast (by rw [hih_hash, hlasthash])
  have : ib < d'.turns.length := hib
  have hd'len : d'.turns.length = d.turns.length + 1 := by rw [hturns]; simp
  omega

/-! ## 8. CONCURRENCY is well-defined + the order is decidable in the model.

`are_concurrent` (`causal.rs:216`) is the incomparable relation. On a wellformed DAG it is symmetric
and irreflexive — the standard "neither before the other" relation of a partial order. -/

/-- **`concurrent_symm`.** Concurrency is symmetric (`are_concurrent a b = are_concurrent
b a`): the running code's `!hb(a,b) && !hb(b,a)` is order-independent. -/
theorem concurrent_symm (d : Dag) (a b : Hash) : concurrent d a b ↔ concurrent d b a := by
  unfold concurrent
  constructor
  · rintro ⟨hne, hab, hba⟩; exact ⟨hne.symm, hba, hab⟩
  · rintro ⟨hne, hba, hab⟩; exact ⟨hne.symm, hab, hba⟩

/-- **`hb_imp_not_concurrent`.** If `a` happened before `b`, they are NOT concurrent — the
two relations are mutually exclusive, exactly as `are_concurrent` checks. -/
theorem hb_imp_not_concurrent (d : Dag) {a b : Hash} (hhb : happenedBefore d a b) :
    ¬ concurrent d a b := by
  rintro ⟨_, hnab, _⟩; exact hnab hhb

/-! ## 9. It RUNS — a linear chain and a diamond (mirroring `causal.rs` tests). -/

/-- A linear chain `1 → 2 → 3` (genesis 1; 2 deps [1]; 3 deps [2]) built by `insert`. Mirrors
`causal.rs::linear_chain`. -/
def chain3 : Option Dag :=
  (Dag.insertGenesis ⟨[]⟩ 1).bind fun d1 =>
  (d1.insert 2 [1]).bind fun d2 =>
  (d2.insert 3 [2])

/-- A diamond `1 → {2,3} → 4` (2,3 both dep on 1; 4 deps on [2,3]). Mirrors `causal.rs::diamond_dag`;
2 and 3 are concurrent. -/
def diamond : Option Dag :=
  (Dag.insertGenesis ⟨[]⟩ 1).bind fun d1 =>
  (d1.insert 2 [1]).bind fun d2 =>
  (d2.insert 3 [1]).bind fun d3 =>
  (d3.insert 4 [2, 3])

-- The chain builds (all deps present at each step).
#guard chain3.isSome
-- The diamond builds.
#guard diamond.isSome
-- A turn whose dep is missing is REJECTED (insert 5 [99] with 99 absent ⇒ none) — MissingDeps.
#guard ((Dag.insertGenesis ⟨[]⟩ 1).bind (fun d => d.insert 5 [99])).isNone
-- A self-cycle is REJECTED (insert 7 [7]) — the causal.rs:104 guard.
#guard ((Dag.insertGenesis ⟨[]⟩ 1).bind (fun d => d.insert 7 [7])).isNone
-- A duplicate hash is REJECTED (insert 1 again) — causal.rs:95 Duplicate.
#guard ((Dag.insertGenesis ⟨[]⟩ 1).bind (fun d => d.insertGenesis 1)).isNone
-- In the chain, the dependency edges are present: 2's recorded deps are [1] (2 depends on 1).
#guard (chain3.bind (fun d => (d.turns.filter (fun e => e.hash == 2)).head?.map (·.deps))) == some [1]

/-! ## 10. Axiom-hygiene tripwires. -/

#assert_axioms wf_empty
#assert_axioms insert_wf
#assert_axioms directDep_strict_rank
#assert_axioms hb_index_descends
#assert_axioms hb_irrefl
#assert_axioms hb_trans
#assert_axioms hb_asymm
#assert_axioms hb_imp_index_lt
#assert_axioms fresh_is_maximal
#assert_axioms concurrent_symm
#assert_axioms hb_imp_not_concurrent

end Dregg2.Coord.CausalOrder
