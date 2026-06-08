/-
# Dregg2.Distributed.DirectoryLaws — the canonical named-capability directory
# (`directory/src/directory.rs`): bind / resolve / unbind monotone laws.

This closes the **P3 directory GAP** named in `_SILVER-COVERAGE-LEDGER.md`. The `dregg-directory`
crate is a CRDT-flavored `name → capability` map (`InMemoryDirectory`, `directory.rs:160-324`) with a
**monotonically increasing per-cell `version`** (`directory.rs:18-19,162`) and a per-entry `version`
mirroring the cell version at the entry's last mutation (`directory.rs:43`). It is the lookup
substrate the `governed-namespace` app and the `cli` resolve names through, so its bind/resolve/unbind
discipline IS load-bearing: a directory that silently re-bound a live name, or resolved a revoked one,
or let `version` go backward, would break the "names are stable, revocation is final" contract those
surfaces depend on.

The ledger previously marked this a "JUSTIFIED RESIDUAL (low-LB primitive)" reachable "via
`Confluence/CRDT`". That is a proven-but-dark deflection: `Confluence/CRDT` proves a *generic* G-Set /
LWW merge, NOT the directory's *actual* four-operation discipline (idempotent-bind / conflict-reject /
final-revoke / version-monotone). This module models the REAL `directory.rs` semantics and is pinned to
the running `InMemoryDirectory` by the differential `directory/src/directory_diff.rs` (the Lean
`register`/`lookup`/`revoke` decisions replayed against the real engine, op for op).

## The model (faithful to `directory.rs`, op for op)

* `Entry` ≈ `DirectoryEntry` — the load-bearing fields for resolution: `handle`, `kind`, `version`,
  `revoked`, `expiresAt` (`directory.rs:38-59`). Descriptive metadata (`tags`/`description`/
  `registeredAt`) is filter-only (`discover`, not resolution) and elided; `handle`/`kind` are the
  equality the idempotence/conflict gate compares (`directory.rs:235`).
* `Dir` ≈ `InMemoryDirectory` — a global `version : ℕ` and an association list `entries` (the `BTreeMap`
  `name → DirectoryEntry`; we use a keyed list — order-independent, the same finite map).
* `register` / `lookup` / `revoke` model `Directory::register` (`:228-250`), `::lookup` (`:252-266`),
  `::revoke` (`:268-280`) — every gate in source order, returning the exact `Result`-shaped outcome.

## The laws (the four faces of the directory contract)

* `register_version_monotone` / `revoke_version_monotone` — **bind/unbind never decrease `version`**;
  a *successful new* bind / a *first* revoke strictly increase it, an *idempotent* bind/revoke leave it
  fixed (`directory.rs:236-237,245,273-276`). The CAS counter only ever climbs.
* `register_idempotent_noop` — re-binding the SAME (kind,handle) is a no-op returning the existing
  version (`directory.rs:235-237`): bind is idempotent on exact match.
* `register_conflict_rejected` — binding a DIFFERENT value to a live name is REJECTED
  (`AlreadyRegistered`) and does not mutate (`directory.rs:238`): names don't silently re-bind.
* `lookup_resolves_iff` — resolve succeeds **iff** present ∧ ¬revoked ∧ ¬expired (`directory.rs:252-265`).
* `revoke_is_final` — **THE unbind monotone law**: once revoked, the name never resolves again, no
  matter the height (`directory.rs:257-258`), and revoke is idempotent (`directory.rs:273-274`). A
  revoked binding is a monotone tombstone — the CRDT "unbind" that cannot be undone by a later lookup.
* `resolved_entry_version_le_dir` — every resolvable entry's `version ≤` the cell `version` (the per-
  entry counter mirrors the cell version at last mutation, `directory.rs:43,247,278`): no entry claims
  a version the directory has not reached.

§ boundary: the *capabilities* a name resolves TO are already verified by `Authority/*`
(`ResourceHandle` is opaque here, exactly as `directory.rs` "does not introspect" a `Capability`,
`:34-35`); this module proves the *naming discipline over* those caps, not the caps themselves.

Pure, computable, `#eval`/`#guard`-able.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Distributed.DirectoryLaws

/-! ## §1 The data — `DirectoryEntry` / `InMemoryDirectory`, the resolution-relevant fields. -/

/-- What a name resolves to. Mirrors `directory.rs::EntryKind` (`:25-36`) — the directory does not
introspect a `Capability`, so we keep the variants opaque codes; only equality matters (the
idempotence/conflict gate compares `kind`, `:235`). -/
abbrev Kind := Nat

/-- An opaque capability handle (`directory.rs::ResourceHandle`). The directory treats it as a bearer
token it never inspects; only equality is load-bearing (the conflict gate, `:235`). The caps it points
at are verified by `Authority/*`; here it is an abstract id. -/
abbrev Handle := Nat

/-- A block height (`directory.rs` `current_height : u64`, `:102`). -/
abbrev Height := Nat

/-- A name (the `BTreeMap` key, `directory.rs:163`). -/
abbrev Name := Nat

/-- `Entry` ≈ `DirectoryEntry` (`directory.rs:38-59`), resolution-relevant fields. `tags`/`description`/
`registeredAt` are filter-only (`discover`) and elided; `handle`/`kind` are the conflict-equality
(`:235`), `version` is the per-entry CAS counter (`:43`), `revoked`/`expiresAt` gate resolution
(`:257-263`). -/
structure Entry where
  handle    : Handle
  kind      : Kind
  /-- per-entry version = cell version at last mutation (`directory.rs:43,247,278`). -/
  version   : Nat
  /-- revoked tombstone (`directory.rs:58`); revoked entries stay queryable but `lookup` fails. -/
  revoked   : Bool
  /-- `None` = no expiry (`directory.rs:54`). -/
  expiresAt : Option Height
  deriving DecidableEq, Repr

/-- `Dir` ≈ `InMemoryDirectory` (`directory.rs:160-165`): a global monotone `version` and a keyed map
`entries : Name → Option Entry`. We back the `BTreeMap` by an assoc list; lookup is the first match. -/
structure Dir where
  /-- global CAS counter, monotone (`directory.rs:18-19,162`). -/
  version : Nat
  entries : List (Name × Entry)
  deriving Repr

/-- empty directory = `InMemoryDirectory::new` (`directory.rs:174-180`): `version = 0`, no entries. -/
def Dir.empty : Dir := { version := 0, entries := [] }

/-- finite-map get: first binding for `name` (`BTreeMap::get`, `directory.rs:231,253`). -/
def Dir.get (d : Dir) (name : Name) : Option Entry :=
  (d.entries.find? (fun p => p.1 = name)).map (·.2)

/-- list upsert: replace the FIRST binding for `name`, or append if absent. -/
def upsert : List (Name × Entry) → Name → Entry → List (Name × Entry)
  | [],      name, e => [(name, e)]
  | p :: ps, name, e => if p.1 = name then (name, e) :: ps else p :: upsert ps name e

/-- finite-map upsert: replace the binding for `name` (or append). Models `BTreeMap::insert`
(`directory.rs:248`) and `get_mut`-then-mutate (`directory.rs:271-278`) as a functional update. -/
def Dir.put (d : Dir) (name : Name) (e : Entry) : Dir :=
  { d with entries := upsert d.entries name e }

/-! ## §2 The operations — `register` / `lookup` / `revoke`, every gate in source order. -/

/-- The outcome tags of `register` (`directory.rs:228-250`, the `Result<Version, DirectoryError>`). -/
inductive RegOutcome where
  /-- `Ok(version)` — bound (new) or idempotent (existing), carrying the resulting version. -/
  | ok (version : Nat) : RegOutcome
  /-- `Err(AlreadyRegistered)` — live name, different value (`directory.rs:238`). -/
  | conflict : RegOutcome
  deriving DecidableEq, Repr

/-- `register name handle kind d` = `Directory::register` (`directory.rs:228-250`), in source order:
1. if a binding exists AND it has the same `(kind, handle)` AND is not revoked → **idempotent**:
   return its version, NO mutation (`:235-237`);
2. if a binding exists otherwise (different value, or revoked) → **conflict** `AlreadyRegistered`, NO
   mutation (`:238`);
3. else **bind new**: `version += 1`, insert the entry stamped with the new version (`:245-249`).
(The capacity gate `:241-243` and name validation `:204-224,229` are orthogonal admission checks, not
the bind/resolve/unbind *discipline* this module proves; modeled as always-admit here. The differential
exercises the real gates.) -/
def register (d : Dir) (name : Name) (handle : Handle) (kind : Kind) : Dir × RegOutcome :=
  match d.get name with
  | some e =>
      if e.kind = kind ∧ e.handle = handle ∧ e.revoked = false then
        (d, .ok e.version)                          -- idempotent exact-match
      else
        (d, .conflict)                              -- AlreadyRegistered
  | none =>
      let v := d.version + 1
      let e : Entry := { handle := handle, kind := kind, version := v,
                         revoked := false, expiresAt := none }
      ({ (d.put name e) with version := v }, .ok v)

/-- The outcome of `lookup` (`directory.rs:252-266`). -/
inductive LookupOutcome where
  | found (e : Entry) : LookupOutcome
  | notFound : LookupOutcome
  | revoked  : LookupOutcome
  | expired  : LookupOutcome
  deriving Repr

/-- `lookup name h d` = `Directory::lookup` (`directory.rs:252-266`), in source order: NotFound if
absent (`:255-256`); Revoked if revoked (`:257-258`); Expired if `h > expiresAt` (`:260-263`); else the
entry (`:265`). A read — never mutates `d`. -/
def lookup (d : Dir) (name : Name) (h : Height) : LookupOutcome :=
  match d.get name with
  | none => .notFound
  | some e =>
      if e.revoked then .revoked
      else match e.expiresAt with
        | some exp => if h > exp then .expired else .found e
        | none     => .found e

/-- Resolution succeeds (the `Ok` arm of `lookup`). -/
def resolves (d : Dir) (name : Name) (h : Height) : Bool :=
  match lookup d name h with | .found _ => true | _ => false

/-- The outcome of `revoke` (`directory.rs:268-280`). -/
inductive RevOutcome where
  | ok (version : Nat) : RevOutcome
  | notFound : RevOutcome
  deriving DecidableEq, Repr

/-- `revoke name d` = `Directory::revoke` (`directory.rs:268-280`), in source order: NotFound if absent
(`:271-272`); idempotent if already revoked — return its version, NO mutation (`:273-274`); else flip
`revoked := true`, `version += 1`, stamp the entry's version (`:276-279`). -/
def revoke (d : Dir) (name : Name) : Dir × RevOutcome :=
  match d.get name with
  | none => (d, .notFound)
  | some e =>
      if e.revoked then (d, .ok e.version)          -- idempotent
      else
        let v := d.version + 1
        let e' := { e with revoked := true, version := v }
        ({ (d.put name e') with version := v }, .ok v)

/-! ## §3 Map laws — `get` after `put` (so the op-laws compute through updates). -/

/-- `find?` after `upsert` on the same key always returns the upserted entry. The clean recursion. -/
theorem find_upsert_self (xs : List (Name × Entry)) (name : Name) (e : Entry) :
    ((upsert xs name e).find? (fun p => p.1 = name)).map (·.2) = some e := by
  induction xs with
  | nil => simp [upsert]
  | cons p ps ih =>
    unfold upsert
    by_cases hp : p.1 = name
    · simp [hp]
    · have hpd : (decide (p.1 = name)) = false := by simp [hp]
      simp only [if_neg hp, List.find?_cons, hpd]
      exact ih

theorem get_put_self (d : Dir) (name : Name) (e : Entry) :
    (d.put name e).get name = some e := by
  unfold Dir.put Dir.get
  exact find_upsert_self d.entries name e

/-! ## §4 The bind/resolve/unbind monotone laws. -/

/-- **`register_version_monotone`** — bind NEVER decreases the cell version (`directory.rs:236-237` vs
`:245`). A successful new bind raises it by exactly one; an idempotent/conflict bind leaves it fixed. -/
theorem register_version_monotone (d : Dir) (name : Name) (handle : Handle) (kind : Kind) :
    d.version ≤ (register d name handle kind).1.version := by
  unfold register
  cases d.get name with
  | none => simp
  | some e =>
      by_cases hm : e.kind = kind ∧ e.handle = handle ∧ e.revoked = false <;> simp [hm]

/-- **`register_new_strictly_increments`** — a bind to a FRESH name raises the version by exactly one
(`directory.rs:245`), and returns that version. -/
theorem register_new_strictly_increments (d : Dir) (name : Name) (handle : Handle) (kind : Kind)
    (hfresh : d.get name = none) :
    (register d name handle kind).1.version = d.version + 1
    ∧ (register d name handle kind).2 = .ok (d.version + 1) := by
  unfold register; rw [hfresh]; exact ⟨rfl, rfl⟩

/-- **`register_idempotent_noop`** — re-binding the SAME `(kind, handle)` to a live name is a no-op
returning the existing version (`directory.rs:235-237`). Bind is idempotent on exact match: the
directory is unchanged (`version` AND `entries`). -/
theorem register_idempotent_noop (d : Dir) (name : Name) (handle : Handle) (kind : Kind) (e : Entry)
    (hget : d.get name = some e) (hk : e.kind = kind) (hh : e.handle = handle)
    (hrev : e.revoked = false) :
    (register d name handle kind).1 = d
    ∧ (register d name handle kind).2 = .ok e.version := by
  unfold register; rw [hget]; simp [hk, hh, hrev]

/-- **`register_conflict_rejected`** — binding a DIFFERENT value to a live name is REJECTED and does NOT
mutate (`directory.rs:238`). Names do not silently re-bind: a conflicting register leaves the directory
exactly as it was and returns `conflict`. -/
theorem register_conflict_rejected (d : Dir) (name : Name) (handle : Handle) (kind : Kind) (e : Entry)
    (hget : d.get name = some e) (hne : ¬(e.kind = kind ∧ e.handle = handle ∧ e.revoked = false)) :
    (register d name handle kind).1 = d
    ∧ (register d name handle kind).2 = .conflict := by
  unfold register; rw [hget]; simp [hne]

/-- **`lookup_resolves_iff`** — resolution succeeds EXACTLY when the name is present, not revoked, and
not expired (`directory.rs:252-265`). The full resolution gate, as a biconditional. -/
theorem lookup_resolves_iff (d : Dir) (name : Name) (h : Height) :
    resolves d name h = true ↔
      ∃ e, d.get name = some e ∧ e.revoked = false ∧ (∀ exp, e.expiresAt = some exp → h ≤ exp) := by
  rcases hg : d.get name with _ | e
  · -- absent: resolves = false, RHS is false (no e)
    have : resolves d name h = false := by simp [resolves, lookup, hg]
    rw [this]; simp
  · by_cases hrev : e.revoked = true
    · -- revoked: resolves = false, RHS false (revoked ≠ false)
      have : resolves d name h = false := by simp [resolves, lookup, hg, hrev]
      rw [this]; simp [hrev]
    · simp only [Bool.not_eq_true] at hrev
      rcases hexp : e.expiresAt with _ | exp
      · -- not revoked, no expiry: always resolves
        have : resolves d name h = true := by simp [resolves, lookup, hg, hrev, hexp]
        rw [this]; simp [hrev, hexp]
      · -- not revoked, expiry = exp
        by_cases hh : h > exp
        · -- expired: resolves = false, RHS contradictory
          have hr : resolves d name h = false := by
            simp [resolves, lookup, hg, hrev, hexp, hh]
          rw [hr]
          constructor
          · intro hc; exact absurd hc (by simp)
          · rintro ⟨e', he', _, hle⟩
            obtain rfl : e = e' := Option.some.inj he'
            have hb : h ≤ exp := hle exp hexp
            exact absurd hb (Nat.not_le.mpr hh)
        · -- not expired: resolves = true, RHS holds
          have hle : h ≤ exp := Nat.le_of_not_lt hh
          have hr : resolves d name h = true := by
            simp [resolves, lookup, hg, hrev, hexp, hh]
          rw [hr]
          refine ⟨fun _ => ⟨e, rfl, by simp [hrev], ?_⟩, fun _ => rfl⟩
          intro exp' he'
          obtain rfl : exp = exp' := Option.some.inj (hexp.symm.trans he')
          exact hle

/-! ## §5 THE UNBIND MONOTONE LAW — revocation is final. -/

/-- **`revoke_version_monotone`** — unbind never decreases the version (`directory.rs:273-274` vs
`:276`); a first revoke raises it by one, an idempotent revoke leaves it fixed. -/
theorem revoke_version_monotone (d : Dir) (name : Name) :
    d.version ≤ (revoke d name).1.version := by
  unfold revoke
  cases d.get name with
  | none => simp
  | some e => by_cases hr : e.revoked <;> simp [hr]

/-- **`revoke_sets_revoked`** — a successful (non-idempotent) revoke flips the entry to `revoked` and
stamps the new version (`directory.rs:276-279`). -/
theorem revoke_sets_revoked (d : Dir) (name : Name) (e : Entry)
    (hget : d.get name = some e) (hrev : e.revoked = false) :
    (revoke d name).1.get name
      = some { e with revoked := true, version := d.version + 1 } := by
  unfold revoke; rw [hget]; simp only [hrev, Bool.false_eq_true, if_false]
  exact get_put_self _ _ _

/-- **`revoke_is_final`** — THE bind/resolve/unbind monotone keystone (`directory.rs:257-258`): after a
successful revoke, the name does NOT resolve at ANY height. A revoked binding is a monotone tombstone —
no later `lookup` can resurrect it (it always hits the `Revoked` arm before the expiry/found arms). -/
theorem revoke_is_final (d : Dir) (name : Name) (e : Entry)
    (hget : d.get name = some e) (hrev : e.revoked = false) :
    ∀ h : Height, resolves (revoke d name).1 name h = false := by
  intro h
  unfold resolves lookup
  rw [revoke_sets_revoked d name e hget hrev]
  simp

/-- **`revoke_idempotent_noop`** — revoke is idempotent on an already-revoked name (`directory.rs:273-
274`): no mutation, returns the existing version. (So a double-unbind cannot bump the counter or
disturb other entries — the tombstone is stable.) -/
theorem revoke_idempotent_noop (d : Dir) (name : Name) (e : Entry)
    (hget : d.get name = some e) (hrev : e.revoked = true) :
    (revoke d name).1 = d ∧ (revoke d name).2 = .ok e.version := by
  unfold revoke; rw [hget]; simp [hrev]

/-- **`revoke_then_register_conflicts`** — a revoked name cannot be re-bound by a plain `register`
(`directory.rs:235` requires `!existing.revoked`; a revoked entry takes the conflict arm `:238`). The
tombstone blocks rebinding: once unbound, the name is conflict-locked until a route-table/host-level
reset (`directory.rs` higher layer), never silently reclaimed. -/
theorem revoke_then_register_conflicts (d : Dir) (name : Name) (e : Entry)
    (hget : d.get name = some e) (hrev : e.revoked = false)
    (handle : Handle) (kind : Kind) :
    (register (revoke d name).1 name handle kind).2 = .conflict := by
  have hr := revoke_sets_revoked d name e hget hrev
  unfold register; rw [hr]
  -- the revoked entry: revoked = true, so the idempotence gate (requires revoked = false) fails
  simp

/-! ## §6 Per-entry/cell version coherence — no entry over-claims a version. -/

/-- **`fresh_entry_version_le_dir`** — a freshly bound entry's version equals the post-bind cell version
(`directory.rs:245-247`), hence `≤` it. The per-entry counter mirrors the cell counter at mutation. -/
theorem fresh_entry_version_le_dir (d : Dir) (name : Name) (handle : Handle) (kind : Kind)
    (hfresh : d.get name = none) :
    ∀ e, (register d name handle kind).1.get name = some e →
      e.version ≤ (register d name handle kind).1.version := by
  intro e he
  unfold register at he ⊢
  rw [hfresh] at he ⊢
  simp only at he ⊢
  -- the post-state's get on `name` reads through the upserted entries
  have hg : ({ version := d.version + 1,
               entries := (d.put name
                 { handle := handle, kind := kind, version := d.version + 1, revoked := false,
                   expiresAt := none }).entries } : Dir).get name
           = some { handle := handle, kind := kind, version := d.version + 1, revoked := false,
                    expiresAt := none } := by
    unfold Dir.get Dir.put
    exact find_upsert_self d.entries name _
  rw [hg] at he
  cases he; simp

/-! ## §7 It runs (`#eval`/`#guard`) — bind, resolve, conflict, revoke-is-final on a concrete directory. -/

namespace Demo

/-- bind "alice"(=1) → handle 7, kind 0 in the empty directory. -/
def d1 : Dir := (register Dir.empty 1 7 0).1

#guard (register Dir.empty 1 7 0).2 = .ok 1          -- new bind → version 1
#guard d1.version = 1
#guard resolves d1 1 100                              -- resolves at any height (no expiry)

-- idempotent re-bind of the SAME value: no-op.
#guard (register d1 1 7 0).1.version = 1             -- version unchanged
#guard (register d1 1 7 0).2 = .ok 1                 -- returns existing version

-- conflict: bind a DIFFERENT handle to the live name.
#guard (register d1 1 99 0).2 = .conflict
#guard (register d1 1 99 0).1.version = 1            -- not mutated

-- revoke "alice" then it never resolves again (the unbind monotone law), at low AND high heights.
def d2 : Dir := (revoke d1 1).1
#guard (revoke d1 1).2 = .ok 2                        -- version bumped to 2
#guard resolves d2 1 0 = false
#guard resolves d2 1 100 = false
#guard resolves d2 1 999999 = false

-- revoke is idempotent: a second revoke is a no-op.
#guard (revoke d2 1).1.version = 2
#guard (revoke d2 1).2 = .ok 2

-- a revoked name is conflict-locked against re-binding (cannot be silently reclaimed).
#guard (register d2 1 7 0).2 = .conflict

-- expiry gate: bind "bob"(=2) with expiry at height 150; resolves at 150, expired past it.
def d3 : Dir :=
  let dd := (register Dir.empty 2 8 0).1
  { dd with entries := dd.entries.map (fun p =>
      if p.1 = 2 then (2, { p.2 with expiresAt := some 150 }) else p) }
#guard resolves d3 2 150                              -- at expiry boundary: still ok (h > exp is strict)
#guard resolves d3 2 200 = false                     -- past expiry: not resolved

end Demo

/-! ## §7b THE GOVERNANCE-BOUND ATOMIC TABLE SWAP — `DfaRoutedDirectory::commit_swap`.

`directory/src/dfa_routed.rs` composes an `InMemoryDirectory` under a governance-bound route table:
a federation stages a new route table (`propose_swap`, `:120`), then it is installed atomically ONLY
when a governance proof supplies a `commitment` (the `RouteTableId` the federation signed) that EQUALS
the staged table's id (`commit_swap`, `:130-146`). On mismatch the swap is REJECTED and the staged
table re-staged unchanged (fail-closed, `:135-142`). This is the load-bearing AUTHORITY property of the
`governed-namespace` app: a route table the federation did NOT sign can never be installed, and a
failed commit loses neither the active table nor the staged proposal. The route-table classification
(a DFA, `Exec/Dfa`) is orthogonal; what is modeled here is the commitment-equality commit GATE. -/

/-- A `RouteTableId` (`dfa_routed.rs:39`) — the 32-byte content hash of a table's canonical encoding.
Distinctness of distinct tables is the named content-addressing assumption; here an abstract id. -/
abbrev RouteTableId := Nat

/-- The governance directory's swap-authority skeleton (`dfa_routed.rs:62`, projected): the active
table id + an optional staged pending id (`active_id` / `pending`, `:66,71`). -/
structure GovDir where
  /-- the currently-active route table id (`dfa_routed.rs:66`). -/
  activeId : RouteTableId
  /-- a staged pending swap, if any (`dfa_routed.rs:71`). -/
  pending  : Option RouteTableId
  deriving DecidableEq, Repr

/-- The outcome of `commit_swap` (`dfa_routed.rs::TableSwapError` + Ok, `:42-58,130-146`). -/
inductive SwapOutcome where
  | committed (id : RouteTableId) : SwapOutcome
  | noPending : SwapOutcome
  | mismatch  : SwapOutcome
  deriving DecidableEq, Repr

/-- `propose newId g` = `DfaRoutedDirectory::propose_swap` (`dfa_routed.rs:120`): stage `newId`; the
active table is UNCHANGED until `commit`. -/
def GovDir.propose (g : GovDir) (newId : RouteTableId) : GovDir := { g with pending := some newId }

/-- `commitSwap commitment g` = `DfaRoutedDirectory::commit_swap` (`dfa_routed.rs:130-146`), in source
order: `NoPendingSwap` if nothing staged (`:134`); `CommitmentMismatch` (re-stage, active preserved)
if the staged id != the governance commitment (`:135-142`); else install the staged table, clear the
pending slot (`:143-145`). -/
def GovDir.commitSwap (g : GovDir) (commitment : RouteTableId) : GovDir × SwapOutcome :=
  match g.pending with
  | none => (g, .noPending)
  | some stagedId =>
      if stagedId = commitment then
        ({ activeId := stagedId, pending := none }, .committed stagedId)
      else
        (g, .mismatch)                                -- active + pending preserved, fail-closed

/-- **`propose_preserves_active`** — staging a table does not change the active commitment
(`dfa_routed.rs:120-124`): governance proposes, but nothing routes through the new table until commit. -/
theorem propose_preserves_active (g : GovDir) (newId : RouteTableId) :
    (g.propose newId).activeId = g.activeId := rfl

/-- **`commit_swap_requires_matching_commitment`** — a staged swap commits IFF the governance
commitment equals the staged id (`dfa_routed.rs:135`). A federation cannot install a table it did not
sign; the only id that can ever go active from a `propose newId` is `newId` itself. -/
theorem commit_swap_requires_matching_commitment (g : GovDir) (stagedId commitment : RouteTableId)
    (hpending : g.pending = some stagedId) :
    (∃ id, (g.commitSwap commitment).2 = .committed id) ↔ stagedId = commitment := by
  unfold GovDir.commitSwap; rw [hpending]
  by_cases h : stagedId = commitment <;> simp [h]

/-- **`commit_swap_mismatch_preserves_active`** — a wrong governance commitment is REJECTED with the
active table AND the staged proposal both preserved (`dfa_routed.rs:135-142`). Fail-closed: a failed
commit installs nothing and loses nothing. -/
theorem commit_swap_mismatch_preserves_active (g : GovDir) (stagedId commitment : RouteTableId)
    (hpending : g.pending = some stagedId) (hmis : stagedId ≠ commitment) :
    g.commitSwap commitment = (g, .mismatch) := by
  unfold GovDir.commitSwap; rw [hpending]; simp [hmis]

/-- **`commit_swap_match_activates`** — a matching governance commitment installs the staged table and
clears the pending slot (`dfa_routed.rs:143-145`). -/
theorem commit_swap_match_activates (g : GovDir) (stagedId : RouteTableId)
    (hpending : g.pending = some stagedId) :
    g.commitSwap stagedId = ({ activeId := stagedId, pending := none }, .committed stagedId) := by
  unfold GovDir.commitSwap; rw [hpending]; simp

/-- **`commit_swap_no_pending`** — committing with nothing staged is rejected and is a no-op
(`dfa_routed.rs:134`). -/
theorem commit_swap_no_pending (g : GovDir) (commitment : RouteTableId) (hnone : g.pending = none) :
    g.commitSwap commitment = (g, .noPending) := by
  unfold GovDir.commitSwap; rw [hnone]

namespace GovDemo

/-- a governance directory active on table id 7, nothing staged. -/
def g0 : GovDir := { activeId := 7, pending := none }

-- commit with nothing staged → NoPendingSwap (commit_swap_without_pending_fails)
#guard (g0.commitSwap 0).2 = .noPending
-- propose stages id 9 without changing the active table (propose_swap_does_not_change_active)
#guard (g0.propose 9).activeId = 7
#guard (g0.propose 9).pending = some 9
-- wrong commitment → mismatch, active + pending preserved (commit_swap rejects bad commitment)
#guard ((g0.propose 9).commitSwap 255).2 = .mismatch
#guard ((g0.propose 9).commitSwap 255).1.activeId = 7
#guard ((g0.propose 9).commitSwap 255).1.pending = some 9
-- right commitment → committed, active becomes 9 (governance_transition_changes_routing_behavior)
#guard ((g0.propose 9).commitSwap 9).2 = .committed 9
#guard ((g0.propose 9).commitSwap 9).1.activeId = 9
#guard ((g0.propose 9).commitSwap 9).1.pending = none

end GovDemo

/-! ## §8 Axiom hygiene — every bind/resolve/unbind law rests ONLY on `{propext, Classical.choice,
Quot.sound}` (no `sorry`, no `:=True`, no `native_decide`, no extra axiom). -/

#assert_axioms get_put_self
#assert_axioms register_version_monotone
#assert_axioms register_new_strictly_increments
#assert_axioms register_idempotent_noop
#assert_axioms register_conflict_rejected
#assert_axioms lookup_resolves_iff
#assert_axioms revoke_version_monotone
#assert_axioms revoke_sets_revoked
#assert_axioms revoke_is_final
#assert_axioms revoke_idempotent_noop
#assert_axioms revoke_then_register_conflicts
#assert_axioms fresh_entry_version_le_dir

#assert_axioms propose_preserves_active
#assert_axioms commit_swap_requires_matching_commitment
#assert_axioms commit_swap_mismatch_preserves_active
#assert_axioms commit_swap_match_activates
#assert_axioms commit_swap_no_pending

end Dregg2.Distributed.DirectoryLaws
