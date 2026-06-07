/-
# Dregg2.Authority.CSpace — the container capability model (tier-3 / seL4 CSpace, lifted and generalized).

A prototype of the container cap model — cnodes that point into cell-mutable cap-stores, resolved by
a fuel-bounded walk — with its scaling laws proved here, prior to migrating the executor onto it.
Advantage over the flat `Caps := Label → List Cap`: delegating one `cnode` shares a whole authority
subtree in O(1); `revoke` walks the derivation tree (the MDB); resolution is a fuel-bounded walk that
is local+immediate at n=1 and topology-bounded when distributed.

Two design differences from seL4:
- **cell-mutable captable**: a cell's cap-store is its mutable state — the owning cell grows/shrinks
  its own slots; seL4's CNodes are kernel-managed, this is cell-owned.
- **distributed captable**: `cnode table` may name a cell on another node, so a walk across a cnode
  is a remote, topology-bounded hop. n=1 collapses it to a local immediate walk (the single-machine
  principle: honest distributed bounds parametrized by topology depth).

Pure, `#eval`-able.
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

#guard reaches cs0 3 0 7            -- 0 ⟶ cnode 1 ⟶ endpoint 7
#guard reaches cs0 1 0 7 == false   -- one hop is not enough — the depth bound bites
#guard reaches cs0 3 0 1            -- 0 reaches the table cell 1 directly
#guard reaches cs0 3 1 7            -- 1 holds the endpoint
#guard reaches cs0 3 7 0 == false   -- 7 holds nothing

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

/-- **`attenuateC_cAuth_subset`** — attenuating any cap (leaf or container) only narrows the rights
it confers. The `cnode` case: sharing a whole table under `keep` cannot confer authority outside `keep`. -/
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

/-- **`attenuateC` preserves the reach target** — narrowing rights never changes which cells a cap
points at (`cnode`'s `table` / `endpoint`'s `target` is untouched by the rights filter). Attenuation
is a pure rights-narrowing: connectivity is orthogonal to permission, as in the flat model. -/
theorem attenuateC_target (keep : List Auth) :
    ∀ c : CCap, target? (attenuateC keep c) = target? c := by
  intro c; cases c <;> rfl

-- O(1) SUBTREE SHARING, operationally: cell 2 holds nothing (can't reach 7); ONE `deriveC` of cell
-- 0's container cap hands 2 the whole subtree under table 1 — now 2 reaches 7 too, read-only.
#guard reaches cs0 3 2 7 == false   -- 2 holds nothing
#guard reaches (deriveC cs0 2 [Auth.read] (CCap.cnode 1 [Auth.read, Auth.grant])) 3 2 7  -- shared!
#guard cAuth (attenuateC [Auth.read] (CCap.cnode 1 [Auth.read, Auth.grant])) == [Auth.read]  -- grant dropped

/-! ## §4 — Monotonicity of reach under grant.

Resolution is monotone under the grant fragment — granting a cap never removes anyone's reach. A
monotone query over a join-semilattice state needs no coordination (I-confluent / CRDT): a node may
answer "X reaches Y" from a stale local replica and only ever under-approximate, never wrongly grant.
So `grant` + `resolve` is coordination-free, available-under-partition, FLP-immune; only `revoke`
(the non-monotone op) carries the CAP/FLP cost — dialed soft/hard, with n=1 giving immediate full
revocation and distributed giving topology-bounded revocation. -/
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

/-! ## §5 — Write-through: a cnode mutates the remote table.

A capability delegates authority to ACT, not just observe — `cnode table [grant]` lets the holder
mutate `table`'s store remotely. Write-through does not break the monotone/non-monotone seam because
that seam is about the operation (add vs remove), orthogonal to local-vs-remote. A write-through
grant is just `grantC` landing at the target cell; its monotonicity is the same theorem —
insert-anywhere is monotone. The hardness stays confined to REMOVE (revoke — dialed) and
MOVE/reparent (the CRDT-tree problem, Kleppmann's highly-available move). -/

/-- Issuer may write-through-grant `cap` into `target`'s store iff it HOLDS a `cnode target` cap
carrying `Auth.grant` AND `cap`'s conferred authority is ⊆ that cnode's rights — NON-AMPLIFICATION
across the cnode (the `recKDelegateAtten` discipline, lifted to remote write: you cannot write-through
authority you do not yourself hold over the table). -/
def writeGrantOK (cs : CSpace) (issuer target : Label) (cap : CCap) : Bool :=
  (cs issuer).any (fun c => match c with
    | .cnode tbl r => (tbl == target) && r.contains Auth.grant && (cAuth cap).all (fun a => r.contains a)
    | _            => false)

/-- WRITE-THROUGH grant: gated, the issuer adds `cap` to the REMOTE `target`'s store. The STATE effect
is EXACTLY `grantC cs target cap` (a CRDT add landing at `target`), fail-closed when the gate is
false. So a remote write-through reuses the local insert — and inherits its monotonicity verbatim. -/
def writeThroughGrant (cs : CSpace) (issuer target : Label) (cap : CCap) : CSpace :=
  if writeGrantOK cs issuer target cap then grantC cs target cap else cs

/-- **`writeThroughGrant_mono`** — a remote write-through grant only grows reach: inserting a cap
is monotone wherever it lands. The distributed write-through grant fragment is coordination-free /
CAP-available / FLP-immune, exactly like local grant. The non-monotone residue (revoke, move) is all
that carries the distributed cost. -/
theorem writeThroughGrant_mono (cs : CSpace) (issuer target : Label) (cap : CCap) :
    ∀ fuel src t, reaches cs fuel src t = true →
      reaches (writeThroughGrant cs issuer target cap) fuel src t = true := by
  intro fuel src t h
  unfold writeThroughGrant
  by_cases hg : writeGrantOK cs issuer target cap
  · rw [if_pos hg]; exact reaches_mono_grant cs target cap fuel src t h
  · rw [if_neg hg]; exact h

-- WRITE-THROUGH, operationally: cell 0 holds `cnode 1 [read,grant]`. It MUTATES cell 1's REMOTE store,
-- inserting `endpoint 9` — now cell 1 reaches 9. The non-amplification gate bites on rights 0 lacks.
#guard reaches cs0 3 1 9 == false                                                       -- 1 ⇏ 9 yet
#guard reaches (writeThroughGrant cs0 0 1 (CCap.endpoint 9 [Auth.read])) 3 1 9           -- 0 mutated 1!
#guard writeGrantOK cs0 0 1 (CCap.endpoint 9 [Auth.read])                                -- read ⊆ {read,grant}
#guard writeGrantOK cs0 0 1 (CCap.endpoint 9 [Auth.write]) == false                      -- write ∉ — no amplify

end Dregg2.Authority.CSpace
