/-
# Dregg2.Authority.CSpace — the CONTAINER capability model (tier-3 / seL4 CSpace, lifted & generalized).

SANDBOX prototype (no ripple into the existing flat `Cap`/`Caps`): we explore the container cap model
— cnodes that point into cell-MUTABLE cap-stores, resolved by a (distributed) fuel-bounded walk — and
prove its scaling laws here, BEFORE migrating the executor onto it. The payoff over the flat
`Caps := Label → List Cap`: delegating ONE `cnode` shares a WHOLE authority subtree in O(1) (the seL4
scaling), `revoke` walks the derivation tree (the MDB = the kernel-state revocation registry), and
resolution is a fuel-bounded walk that is local+immediate at n=1 and topology-bounded when distributed.

Two design commitments (ember, 2026-06-01) that make this STRONGER than seL4:
- **cell-mutable captable**: a cell's cap-store IS its mutable state — the owning cell grows/shrinks
  its own slots within its authority, and every `cnode`-holder tracks the change LIVE (dynamic
  delegation; seL4's CNodes are kernel-managed, this is cell-owned).
- **distributed captable**: `cnode table` names a cell `table` that may live on another node, so a
  walk ACROSS a cnode is a (remote, topology-bounded) hop. n=1 collapses it to a local immediate walk
  — the single-machine principle: the honest bounds are the distributed bounds, parametrized by depth.

Discipline: no `axiom`/`admit`/`native_decide`/`sorry`. Pure, `#eval`-able.
-/
import Dregg2.Authority.Positional

namespace Dregg2.Authority.CSpace

open Dregg2.Authority (Label Auth)

/-! ## §1 — The container capability and the navigable (distributed) cap-store. -/

/-- A **container capability**. `null`/`endpoint` are the leaves (as in the flat `Cap`); `cnode table
rights` is the new one — a handle into cell `table`'s cap-store, the operations on it attenuated to
`rights`. Holding a `cnode table` lets a walk descend into `table`'s slots (and onward), so ONE cnode
confers reach to a whole SUBTREE — the structural sharing the flat model could not express. -/
inductive CCap where
  | null
  | endpoint (target : Label) (rights : List Auth)
  | cnode    (table  : Label) (rights : List Auth)
  deriving DecidableEq, Repr

/-- The cap-store. In the migrated model this is part of each cell's MUTABLE record (a cell edits its
own slots); here a total function for the prototype. The `cnode` caps let a walk cross from one cell's
store into another's — the navigable, distributed CSpace (vs the flat `Label → List Cap`). -/
abbrev CSpace := Label → List CCap

/-- The rights a cap confers DIRECTLY (a `cnode` confers its `rights` over the table it names — e.g.
the authority to read/insert/derive within `table`'s store). The transitive REACH is separate
(`reaches`); this is just the local rights component the attenuation order compares. -/
def cAuth : CCap → List Auth
  | .null         => []
  | .endpoint _ r => r
  | .cnode _ r    => r

/-- Attenuate a cap — narrow its rights (drop the ones not in `keep`). A `cnode` narrows what the
holder may DO with the whole subtree (read-only sharing of a table, say). `null` is fixed. -/
def attenuateC (keep : List Auth) : CCap → CCap
  | .endpoint t r => .endpoint t (r.filter (fun a => keep.contains a))
  | .cnode t r    => .cnode t (r.filter (fun a => keep.contains a))
  | .null         => .null

/-! ## §2 — Reachability: the distributed, fuel-bounded CSpace walk. -/

/-- **`reaches cs fuel src t`** — does `src`'s cap-store let it reach cell `t`? Directly (it holds an
`endpoint`/`cnode` naming `t`) OR transitively (it holds a `cnode table` and `table`'s store reaches
`t`). `fuel` bounds the walk depth — seL4's fixed cap-address width / the guarded-radix depth; in the
distributed reading it is the topology hop-budget. STRUCTURALLY DECREASING on `fuel`. -/
def reaches (cs : CSpace) : Nat → Label → Label → Bool
  | 0,        _,   _ => false
  | fuel + 1, src, t =>
    (cs src).any (fun c => match c with
      | .endpoint t' _ => t' == t
      | .cnode table _ => (table == t) || reaches cs fuel table t
      | .null          => false)

/-- A starting CSpace: cell 0 holds a `cnode` into cell 1's store; cell 1 holds an `endpoint` to 7.
So 0 reaches 7 in 2 hops THROUGH the container (the subtree-sharing the flat model can't state). -/
def cs0 : CSpace := fun l =>
  if l = 0 then [CCap.cnode 1 [Auth.read, Auth.grant]]
  else if l = 1 then [CCap.endpoint 7 [Auth.read, Auth.write]]
  else []

#eval reaches cs0 3 0 7    -- true  (0 ⟶ cnode 1 ⟶ endpoint 7)
#eval reaches cs0 1 0 7    -- false (one hop is not enough — the depth bound bites)
#eval reaches cs0 3 0 1    -- true  (0 reaches the table cell 1 directly)
#eval reaches cs0 3 1 7    -- true  (1 holds the endpoint)
#eval reaches cs0 3 7 0    -- false (7 holds nothing)

/-! ## §3 — `grant`/`derive`: O(1) subtree sharing (the seL4 scaling move). -/

/-- **`grantC cs holder c`** — add cap `c` to `holder`'s store (the `cap_insert` move; other stores
untouched). When `c` is a `cnode`, this hands `holder` a handle to a WHOLE table in ONE slot. -/
def grantC (cs : CSpace) (holder : Label) (c : CCap) : CSpace :=
  fun l => if l = holder then c :: cs l else cs l

/-- **`deriveC cs holder keep c`** — grant `holder` an ATTENUATED copy of `c` (`grant ∘ attenuate`,
l4v `derive_cap`). For a `cnode`, this shares the entire referenced table — attenuated to `keep` —
in O(1): the holder now reaches the whole subtree, but may only exert `keep` over it. -/
def deriveC (cs : CSpace) (holder : Label) (keep : List Auth) (c : CCap) : CSpace :=
  grantC cs holder (attenuateC keep c)

/-- **`attenuateC_cAuth_subset` — PROVED (the container RIGHTS non-amplification).** Attenuating any
cap — leaf OR container — only narrows the rights it confers. The `cnode` case is the new content:
sharing a whole table under `keep` cannot confer authority outside `keep`. -/
theorem attenuateC_cAuth_subset (keep : List Auth) (c : CCap) :
    cAuth (attenuateC keep c) ⊆ cAuth c := by
  cases c with
  | null => simp [attenuateC, cAuth]
  | endpoint t r =>
      intro a ha; simp only [attenuateC, cAuth] at ha ⊢; exact (List.mem_filter.mp ha).1
  | cnode t r =>
      intro a ha; simp only [attenuateC, cAuth] at ha ⊢; exact (List.mem_filter.mp ha).1

/-- The cell a cap POINTS AT (its connectivity target): `endpoint`/`cnode` name a cell, `null` none.
The reach-relevant projection — orthogonal to the rights `cAuth`. -/
def target? : CCap → Option Label
  | .null         => none
  | .endpoint t _ => some t
  | .cnode t _    => some t

/-- **`attenuateC` preserves the REACH target** — narrowing rights never changes which cells a cap
points at (`cnode`'s `table` / `endpoint`'s `target` is untouched by the rights filter). So
attenuation is a pure rights-narrowing: connectivity is orthogonal to permission, exactly as in the
flat model (`confersEdgeTo` vs `capAuthConferred`). The reach NON-AMPLIFICATION (a derived `cnode`
lets the holder reach ⊆ the delegator's reach) is the next headline — its precise statement is a
design call (transitive reach through cycles), which is the §4 MDB/derivation work. -/
theorem attenuateC_target (keep : List Auth) :
    ∀ c : CCap, target? (attenuateC keep c) = target? c := by
  intro c; cases c <;> rfl

-- O(1) SUBTREE SHARING, operationally: cell 2 holds nothing (can't reach 7); ONE `deriveC` of cell
-- 0's container cap hands 2 the whole subtree under table 1 — now 2 reaches 7 too, read-only.
#eval reaches cs0 3 2 7    -- false (2 holds nothing)
#eval reaches (deriveC cs0 2 [Auth.read] (CCap.cnode 1 [Auth.read, Auth.grant])) 3 2 7  -- true (shared!)
#eval cAuth (attenuateC [Auth.read] (CCap.cnode 1 [Auth.read, Auth.grant]))             -- [read] (grant dropped)

/-! ## §4 — MONOTONICITY of reach under grant (the ANALYZABILITY half — why CAP/FLP do NOT bite the
common path).

The worry: a navigable DISTRIBUTED cspace makes cap-resolution a cross-node query, and cross-node
queries inherit CAP (partition) and FLP (consensus). The escape: **resolution is MONOTONE under the
grant fragment** — granting a cap NEVER removes anyone's reach. A monotone query over a join-semilattice
state needs NO coordination (it is I-confluent / CRDT — the `Confluence`/drift-stability machinery): a
node may answer "X reaches Y" from a STALE local replica and only ever UNDER-approximate (it might not
have seen a grant yet), never wrongly grant. So `grant` + `resolve` is the coordination-free,
available-under-partition, FLP-immune fragment; only `revoke` (the non-monotone op) carries the CAP/FLP
cost — and that we DIAL (soft/hard fail), exactly as the single-machine principle predicts (n=1 ⇒
immediate full revocation; distributed ⇒ topology-bounded). This theorem is that monotonicity. -/
theorem reaches_mono_grant (cs : CSpace) (holder : Label) (cap : CCap) :
    ∀ fuel src t, reaches cs fuel src t = true → reaches (grantC cs holder cap) fuel src t = true := by
  intro fuel
  induction fuel with
  | zero => intro src t h; simp [reaches] at h
  | succ n ih =>
      intro src t h
      simp only [reaches] at h ⊢
      rw [List.any_eq_true] at h ⊢
      obtain ⟨c, hmem, hc⟩ := h
      refine ⟨c, ?_, ?_⟩
      · -- `c` survives into the GROWN store (grant only adds at `holder`, others unchanged)
        unfold grantC
        by_cases hh : src = holder
        · rw [if_pos hh]; exact List.mem_cons_of_mem _ hmem
        · rw [if_neg hh]; exact hmem
      · -- the per-cap reach predicate is preserved (a `cnode`'s onward walk is monotone by `ih`)
        cases c with
        | null => exact hc
        | endpoint t' r => exact hc
        | cnode table r =>
            simp only [Bool.or_eq_true] at hc ⊢
            rcases hc with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (ih table t h2)

end Dregg2.Authority.CSpace
