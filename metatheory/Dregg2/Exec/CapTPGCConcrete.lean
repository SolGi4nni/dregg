/-
# Dregg2.Exec.CapTPGCConcrete — CapTP distributed-GC SAFETY (the `gc.rs` per-session model).

`Exec.CapTPGC` closed the distributed-GC *liveness* OPEN by lease-based reclaim (a handle whose
lease has lapsed is reclaimable; a current lease is never reclaimed; cross-vat cycles leak only
until lease expiry). That is the **eventual-reclamation** half. This module supplies the dual
**no-premature-reclaim / Byzantine-resistance** half over the per-holder session table, the model
of `captp/src/gc.rs` that `DistributedExports.dregg_captp_process_drop` runs verbatim —
and we DO NOT re-prove the lease-liveness half (we re-export it from `CapTPGC` for the headline).

F3 NOTE: the old §1 (refcount laws over the KERNEL swiss side-table) died with the
seal/swiss/sturdyref verb family — stored-capability semantics live in the caps-in-slots factory
(`Apps/CapSlotFactory.lean`, R7 epoch-at-retrieval). The `gc.rs` per-session protocol model below
is the SURVIVOR: it is the transport-layer GC the captp runtime actually runs.

The safety tooth, at `n > 1` (multiple holders / multiple sessions; `n = 1` is the
scales-to-zero special case, NOT the target):

  **§2 — the session-id Byzantine tooth.** A faithful EXECUTABLE Lean model of
  `ExportGcManager::process_drop_inner` (`gc.rs:170`) — a per-`(cell, federation)` refcount table
  carrying a `session_id`, with `processDrop` performing the EXACT session check
  (`ref_count.session_id != expected ⇒ DropResult::Invalid`, `gc.rs:194`). We prove
  `byzantine_node_different_session_cannot_drop_others_refs` (`gc.rs:670`) AS A THEOREM at `n = 2`
  holders: a Byzantine node presenting the WRONG session for a victim holder's ref leaves
  `total_refs` UNCHANGED, while the honest holder on the correct session CAN decrement its own ref.

§2.5 keeps the SCALAR-coherence laws (`SwissHoldersCoherent refc t := refc = totalRefs t` over a
plain `Nat` scalar — the `ExportEntry.total_refs == Σ holders` invariant, `gc.rs:198–201`):
`bridge_processDrop_tracks_refcount` proves the accept-path decrement is unit-exact and
`bridge_last_ref_iff` aligns `canRevoke` with GC-at-zero (subset `{propext, Classical.choice,
Quot.sound}`, key-uniqueness `NoDupFeds` carried as the `gc.rs` `HashMap` invariant).

The Rust differential corpus (`gcDifferentialCorpus`) mirrors the `gc.rs` / redteam session tests
after the F-11/F-12 fix: `byzantine_node_different_session_cannot_drop_others_refs`,
`export_reexport_does_not_steal_original_session_drop_rights`,
`export_new_session_cannot_drop_other_sessions_refs`, and the F-11 denied session-free path.

F-11 / F-12 (closed): session validation is MANDATORY and PER-REF. `§2`'s `processDrop` is a
`Session`-taking function (no `Option`, no session-free door) over per-session buckets, so the proof
now bites on the refcount-drop path the lease-only model was blind to: `f11_session_free_drop_denied`
(a session that minted nothing reclaims nothing) and `f12_*` (a re-export keeps the original
session's drop rights; each session drops only the refs it minted).

Crypto note: session IDs here are MODELLED as opaque `Nat` tokens whose unforgeability is an
EXTERNAL assumption (a session id is minted by `CapHello` and is unguessable to a Byzantine peer).
We do NOT model the handshake; the theorem is "GIVEN the adversary cannot present the victim's
session id, it cannot drop the victim's ref" — `SessionUnforgeable` names that hypothesis.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.CapTPGC
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPGCConcrete

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §2 — The session-id Byzantine tooth (a faithful executable model of `gc.rs`).

`gc.rs`'s `ExportGcManager` keeps, per exported `cell`, a map `federation ↦ RefCount` where each
`RefCount` carries PER-SESSION buckets (`sessions : HashMap<SessionId, u64>`, the F-12 fix). A
`DropRef` is processed by `process_drop_inner` (`gc.rs:172`): look up the cell, then the holder;
**reject if the presented session's bucket is empty** (`sessions.get(&session)` absent or 0) — this
is BOTH the wrong-session reject AND the F-11 unauthenticated-drop reject; else decrement that
session's bucket, the holder's count, and the cell's `total_refs`. We model the per-cell holder
table (the inner `HashMap<FederationId, RefCount>`) faithfully as an association list, with each
holder's per-session buckets as a nested assoc list, and reproduce `process_drop_inner` EXACTLY. -/

/-- A federation/holder id (the `gc.rs` `FederationId`, modelled as a `Nat`). -/
abbrev Fed := Nat

/-- A session id (the `gc.rs` `SessionId = u64`, an opaque unguessable token; see crypto note). -/
abbrev Session := Nat

/-- The per-holder reference count with its PER-SESSION buckets — the `gc.rs` `RefCount`
(`gc.rs:39`) AFTER the F-12 fix, minus the `last_activity` field (that drives the *lease* half,
already in `CapTPGC`; here we model the *session/refcount* half).

`sessions` is the `gc.rs` `HashMap<SessionId, u64>`: each session that minted a ref maps to the
number of refs it minted. `count` is the maintained SUM of all buckets (the `gc.rs`
`RefCount.count`), so existing readers and the `total_refs = Σ count` invariant are unchanged.

The F-12 fix lives HERE: there is NO single per-holder `session` scalar to overwrite. A re-export
under a new session adds (or grows) THAT session's bucket and leaves every other session's bucket
untouched, so each session retains the right to drop exactly the refs it minted. -/
structure HolderRef where
  /-- how many references this holder has in total (`RefCount.count` = sum of `sessions`). -/
  count    : Nat
  /-- per-session ref counts (`RefCount.sessions : HashMap<SessionId,u64>`), as an assoc list. -/
  sessions : List (Session × Nat)
deriving DecidableEq, Repr

/-- The per-cell export entry's holder table — the `gc.rs` `ExportEntry.holders`
(`HashMap<FederationId, RefCount>`) as an association list keyed by `Fed`. -/
abbrev HolderTable := List (Fed × HolderRef)

/-- Look up a holder's `RefCount` (first match), `none` if absent — `holders.get(&fed)`. -/
def findHolder (t : HolderTable) (fed : Fed) : Option HolderRef :=
  (t.find? (fun p => p.1 == fed)).map (·.2)

/-- The ref count a holder minted under `sess` — `RefCount.sessions.get(&sess).unwrap_or(0)`. -/
def sessionCount (rc : HolderRef) (sess : Session) : Nat :=
  ((rc.sessions.find? (fun p => p.1 == sess)).map (·.2)).getD 0

/-- Decrement a session's bucket by 1, removing the bucket entirely at 0 (the `gc.rs`
`*bucket -= 1; if *bucket == 0 { sessions.remove(&session) }`). Other sessions untouched. -/
def decSession (buckets : List (Session × Nat)) (sess : Session) : List (Session × Nat) :=
  (buckets.map (fun p =>
      if p.1 == sess then (p.1, p.2 - 1) else p)).filter
    (fun p => !(p.1 == sess && p.2 == 0))

/-- The drop verdict — the `gc.rs` `DropResult` (`gc.rs:65`). -/
inductive DropResult where
  | stillHeld
  | canRevoke
  | invalid
deriving DecidableEq, Repr

open DropResult

/-- `total_refs` — the SUM of all holder counts (the `gc.rs` `ExportEntry.total_refs`, maintained
incrementally there; we DEFINE it as the sum so the model's invariant is checkable). -/
def totalRefs (t : HolderTable) : Nat :=
  (t.map (fun p => p.2.count)).sum

/-- Decrement a holder's `sess` bucket (and its total `count`) by 1, dropping the holder entirely
when its total `count` hits 0 (the `gc.rs` `if ref_count.count == 0 { holders.remove(&fed) }`,
`gc.rs:203`). The bucket decrement is the F-12 core: only `sess`'s refs are touched. Other holders
and other sessions are untouched. -/
def decHolderSession (t : HolderTable) (fed : Fed) (sess : Session) : HolderTable :=
  (t.map (fun p =>
      if p.1 == fed then
        (p.1, { count := p.2.count - 1, sessions := decSession p.2.sessions sess })
      else p)).filter
    (fun p => !(p.1 == fed && p.2.count == 0))

/-- **`processDrop t fed sess`** — a FAITHFUL executable model of `gc.rs`'s
`process_drop_inner` (`gc.rs:172`) AFTER the F-11/F-12 fix. Session validation is MANDATORY (a
`Session`, not an `Option`): the legacy session-free path is GONE. Returns the verdict AND the
post-table:

  * unknown holder ⇒ `(invalid, t)` (no change);
  * the session `sess` minted no refs on this holder (`sessionCount rc sess = 0`) ⇒ `(invalid, t)`
    (no change) — this is BOTH the Byzantine wrong-session reject AND the F-11 unauthenticated /
    forged / absent-session reject (a session that minted nothing decrements nothing);
  * else decrement `sess`'s bucket (and the holder's total) by exactly one — only the refs THIS
    session minted are dropped (F-12). -/
def processDrop (t : HolderTable) (fed : Fed) (sess : Session) : DropResult × HolderTable :=
  match findHolder t fed with
  | none    => (invalid, t)                          -- unknown holder ⇒ Invalid, no change
  | some rc =>
      if sessionCount rc sess = 0 then (invalid, t)  -- no refs under this session ⇒ Invalid, no change
      else
        let t' := decHolderSession t fed sess
        (if totalRefs t' = 0 then canRevoke else stillHeld, t')

/-! ### §2a — the session check is a NO-OP when the session minted nothing (the core invariant). -/

/-- **`wrong_session_no_op` — a drop on a session that minted no ref here does NOT touch the
table.** If the holder `fed` exists but the presented session `s'` has an EMPTY bucket on it
(`sessionCount rc s' = 0`), `processDrop` returns `(invalid, t)` — the table is RETURNED UNCHANGED.
This is the exact `gc.rs` per-session guard (`match sessions.get_mut(&session) { Some(b) if *b > 0
=> …, _ => return Invalid }`), BEFORE any decrement. The Byzantine-resistance primitive AND the F-11
unauthenticated-drop reject in one: a session bucket of 0 (wrong session, forged session, or no
session) authorizes nothing. -/
theorem wrong_session_no_op (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc)
    (s' : Session) (hzero : sessionCount rc s' = 0) :
    processDrop t fed s' = (invalid, t) := by
  unfold processDrop
  rw [hf]
  simp only [if_pos hzero]

/-- **`wrong_session_preserves_total` — `total_refs` is UNCHANGED by a no-bucket drop.**
The corollary the Rust test `byzantine_node_different_session_cannot_drop_others_refs` asserts: a
wrong-session drop leaves `totalRefs` exactly as it was. Follows from `wrong_session_no_op`. -/
theorem wrong_session_preserves_total (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc)
    (s' : Session) (hzero : sessionCount rc s' = 0) :
    totalRefs (processDrop t fed s').2 = totalRefs t := by
  rw [wrong_session_no_op t fed rc hf s' hzero]

/-! ### §2b — the named (honest) unforgeability hypothesis.

The security claim is conditional on the adversary being UNABLE to present a session under which the
victim minted a ref. `gc.rs` mints session ids in `CapHello`; we do NOT model the handshake.
`SessionUnforgeable` names that assumption: a Byzantine federation, acting on a victim holder's ref,
can only present sessions whose bucket on the victim is EMPTY (it never minted a ref under them).
This is the honest crypto boundary — the theorem is sound MODULO this hypothesis, which we state,
never fake. -/

/-- **`SessionUnforgeable t victim byzSession`** — the byzantine peer's presented session
`byzSession` minted NO ref on the victim holder (its bucket is empty). (In the real system this
holds because a session id is an unguessable `CapHello`-minted token, so the adversary can only
present sessions it owns — under which the victim minted nothing.) -/
def SessionUnforgeable (t : HolderTable) (victim : Fed) (byzSession : Session) : Prop :=
  ∀ rc : HolderRef, findHolder t victim = some rc → sessionCount rc byzSession = 0

/-- **`byzantine_cannot_drop_victim_ref` (n>1) — the headline Byzantine theorem.**
THE security property modelled from `gc.rs:670`'s
`byzantine_node_different_session_cannot_drop_others_refs`, at `n = 2` holders. GIVEN the byzantine
peer cannot forge a session under which the victim minted a ref (`SessionUnforgeable`), a `DropRef`
it submits against the VICTIM's holder slot (carrying the byzantine peer's own session) is REJECTED
as `invalid` AND leaves `total_refs` untouched — the victim's ref survives. -/
theorem byzantine_cannot_drop_victim_ref
    (t : HolderTable) (victim : Fed) (rc : HolderRef)
    (hf : findHolder t victim = some rc)
    (byzSession : Session) (hunf : SessionUnforgeable t victim byzSession) :
    processDrop t victim byzSession = (invalid, t)
    ∧ totalRefs (processDrop t victim byzSession).2 = totalRefs t := by
  have hzero : sessionCount rc byzSession = 0 := hunf rc hf
  exact ⟨wrong_session_no_op t victim rc hf byzSession hzero,
         wrong_session_preserves_total t victim rc hf byzSession hzero⟩

/-! ### §2c — the HONEST side still works (the model is not vacuously fail-closed).

A fail-closed model that rejected EVERYTHING would trivially satisfy §2b. We prove the dual: the
honest holder, presenting a session under which it DID mint a ref, CAN decrement that ref — so the
rejection in §2b is SESSION-SCOPED, not a blanket refusal. -/

/-- **`right_session_decrements` — the honest holder drops its OWN ref.** With a session
whose bucket is non-empty (`0 < sessionCount rc sess`), the drop succeeds and the post-table is
exactly `decHolderSession t fed sess`. Witnesses that `processDrop` is NOT vacuously fail-closed. -/
theorem right_session_decrements (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc) (sess : Session) (hpos : 0 < sessionCount rc sess) :
    (processDrop t fed sess).2 = decHolderSession t fed sess := by
  unfold processDrop
  rw [hf]
  have hz : ¬ sessionCount rc sess = 0 := by omega
  simp only [if_neg hz]

/-! ## §2.5 — THE BRIDGE: §2's per-holder SUM IS §1's swiss-entry `refcount` (MID-1 / F1).

§1 reasons over the swiss entry's SCALAR `refcount` field (the `gc.rs` `ExportEntry.total_refs`);
§2 reasons over the per-holder `HolderTable` (the `gc.rs` `ExportEntry.holders` map). The runtime
maintains the invariant `ExportEntry.total_refs == Σ holders, holder.count` (`gc.rs:198–201`
increments/decrements the scalar in lockstep with the per-holder map). Until now that connection
lived only in prose (the `gcDropTotal` phantom, F1). Here it is a THEOREM:

  * **coherence** (`SwissHoldersCoherent e t`) is `e.refcount = totalRefs t` — the swiss-entry scalar
    IS the per-holder sum. This is a *full* equality of the two models' refcount, NOT an aggregate
    standing in for a per-asset fact: the scalar `refcount` and the structured holder table are
    pinned to the same number, and each §2 holder decrement is matched by a §1 scalar decrement.
  * **`decHolder_pred_total`** — an accepting drop on a present, positive holder lowers `totalRefs`
    by EXACTLY one (the per-holder model's decrement is unit-exact; the `HashMap` key-uniqueness
    invariant `NoDupFeds` rules out a single `fed` being double-counted).
  * **`bridge_drop_tracks`** — the WELD: when §2's `processDrop` accepts (correct session, positive
    count) AND the kernel-scalar side commits the `refcount > 1` decrement branch, coherence is PRESERVED
    across the joint step (`e'.refcount = totalRefs t'`). The two halves now move in lockstep.
  * **`bridge_last_ref_reclaims`** — the boundary: when the LAST holder drops (`totalRefs t' = 0`),
    the scalar hits the GC boundary (the remove branch) — §2's `canRevoke` verdict and
    §1's GC-at-zero agree. -/

/-- **`NoDupFeds t`** — the `gc.rs` `HashMap<FederationId, RefCount>` key-uniqueness invariant: no
federation id appears twice in the holder table. A real `HashMap` guarantees this by construction;
we carry it as an explicit hypothesis so the per-holder decrement is provably UNIT-exact (a duplicate
key would let one `processDrop` lower `totalRefs` by more than one). -/
def NoDupFeds (t : HolderTable) : Prop := (t.map Prod.fst).Nodup

/-- `fed` not a key ⇒ every element's key differs from `fed`. -/
theorem forall_key_ne (t : HolderTable) (fed : Fed)
    (hnm : fed ∉ t.map Prod.fst) : ∀ p ∈ t, ¬ p.1 = fed := by
  intro p hp h
  apply hnm
  rw [List.mem_map]
  exact ⟨p, hp, h⟩

/-- The `map` half of `decHolderSession` is the identity on a table with no `fed` key (helper for the
unit-exact decrement: a non-matching tail is untouched by the count-decrement map). -/
theorem decHolderMap_not_mem (t : HolderTable) (fed : Fed) (sess : Session)
    (hnm : fed ∉ t.map Prod.fst) :
    t.map (fun p => if p.1 == fed then
        (p.1, { count := p.2.count - 1, sessions := decSession p.2.sessions sess }) else p) = t := by
  have hkey := forall_key_ne t fed hnm
  clear hnm
  induction t with
  | nil => rfl
  | cons hd tl ih =>
      have hhd : ¬ hd.1 = fed := hkey hd (by simp)
      simp only [List.map_cons]
      rw [if_neg (by simpa using hhd)]
      congr 1
      exact ih (fun p hp => hkey p (by simp [hp]))

/-- The `filter` half of `decHolderSession` keeps every entry of a table with no `fed` key (its guard
`p.1 == fed && …` never fires). -/
theorem decHolderFilter_not_mem (t : HolderTable) (fed : Fed)
    (hnm : fed ∉ t.map Prod.fst) :
    t.filter (fun p => !(p.1 == fed && p.2.count == 0)) = t := by
  have hkey := forall_key_ne t fed hnm
  apply List.filter_eq_self.mpr
  intro p hp
  have hpf : ¬ p.1 = fed := hkey p hp
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp]
  intro hpe
  exact absurd (by simpa using hpe) hpf

/-- A `fed` absent from the key set leaves `decHolderSession` a NO-OP (map + filter both pass
through). -/
theorem decHolder_not_mem (t : HolderTable) (fed : Fed) (sess : Session)
    (hnm : fed ∉ t.map Prod.fst) : decHolderSession t fed sess = t := by
  unfold decHolderSession
  rw [decHolderMap_not_mem t fed sess hnm, decHolderFilter_not_mem t fed hnm]

/-- **`totalRefs_pos_of_findHolder`** — a present holder with positive count makes the SUM
positive. The arithmetic that proves the tail recursion of the unit-exact decrement does not
under-flow. -/
theorem totalRefs_pos_of_findHolder (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc) (hpos : 0 < rc.count) : 1 ≤ totalRefs t := by
  induction t with
  | nil => exact absurd hf (by simp [findHolder])
  | cons hd tl ih =>
    have htot : totalRefs (hd :: tl) = hd.2.count + totalRefs tl := by
      simp only [totalRefs, List.map_cons, List.sum_cons]
    simp only [findHolder, List.find?_cons] at hf
    by_cases hhd : (hd.1 == fed) = true
    · simp only [hhd, if_true, Option.map_some, Option.some.injEq] at hf
      subst hf
      rw [htot]; omega
    · simp only [hhd, Bool.false_eq_true, if_false] at hf
      have hrec := ih (by simp only [findHolder]; exact hf)
      rw [htot]; omega

/-- **`decHolder_pred_total` — the per-holder decrement is UNIT-exact.** Given key-uniqueness
(`NoDupFeds`), if `fed` is present with positive count, `decHolderSession t fed sess` lowers
`totalRefs` by EXACTLY one. The per-session bucket detail is invisible to `totalRefs` (which sums the
holder `count`s), so the arithmetic is the same unit-exact decrement as before the F-12 refactor —
this is the heart of the bridge: §2's structured drop matches §1's scalar `- 1`. -/
theorem decHolder_pred_total (t : HolderTable) (fed : Fed) (rc : HolderRef) (sess : Session)
    (hnd : NoDupFeds t) (hf : findHolder t fed = some rc) (hpos : 0 < rc.count) :
    totalRefs (decHolderSession t fed sess) = totalRefs t - 1 := by
  unfold NoDupFeds at hnd
  induction t with
  | nil => exact absurd hf (by simp [findHolder])
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hdnotin, hndtl⟩ := hnd
    simp only [findHolder, List.find?_cons] at hf
    have htot : totalRefs (hd :: tl) = hd.2.count + totalRefs tl := by
      simp only [totalRefs, List.map_cons, List.sum_cons]
    by_cases hhd : (hd.1 == fed) = true
    · -- head matches; `rc = hd.2`; tl has no `fed` key so the rest is untouched.
      simp only [hhd, if_true, Option.map_some, Option.some.injEq] at hf
      subst hf
      have hfedeq : hd.1 = fed := by simpa using hhd
      have hnmtl : fed ∉ tl.map Prod.fst := by rw [← hfedeq]; exact hdnotin
      have hmaptl := decHolderMap_not_mem tl fed sess hnmtl
      have hfilttl := decHolderFilter_not_mem tl fed hnmtl
      have hexpand : decHolderSession (hd :: tl) fed sess =
          List.filter (fun p => !(p.1 == fed && p.2.count == 0))
            ((hd.1, ({ count := hd.2.count - 1, sessions := decSession hd.2.sessions sess } : HolderRef)) :: tl) := by
        unfold decHolderSession
        simp only [List.map_cons, hhd, if_true, hmaptl]
      rw [hexpand, List.filter_cons]
      by_cases hc1 : hd.2.count - 1 = 0
      · -- count was exactly 1 → head's decremented count is 0 → filtered out.
        have hguard : (!((hd.1, ({ count := hd.2.count - 1, sessions := decSession hd.2.sessions sess } : HolderRef)).1 == fed &&
            (hd.1, ({ count := hd.2.count - 1, sessions := decSession hd.2.sessions sess } : HolderRef)).2.count == 0)) = false := by
          simp only [hhd, hc1, beq_self_eq_true, Bool.and_self, Bool.not_true]
        rw [if_neg (by simp [hguard]), hfilttl, htot]
        omega
      · -- count > 1 → head kept with decremented count.
        have hguard : (!((hd.1, ({ count := hd.2.count - 1, sessions := decSession hd.2.sessions sess } : HolderRef)).1 == fed &&
            (hd.1, ({ count := hd.2.count - 1, sessions := decSession hd.2.sessions sess } : HolderRef)).2.count == 0)) = true := by
          simp only [Bool.not_eq_true', Bool.and_eq_false_imp]
          intro _; simpa using hc1
        rw [if_pos (by simp [hguard]), hfilttl]
        have hcons : totalRefs ((hd.1, ({ count := hd.2.count - 1, sessions := decSession hd.2.sessions sess } : HolderRef)) :: tl)
            = (hd.2.count - 1) + totalRefs tl := by
          simp only [totalRefs, List.map_cons, List.sum_cons]
        rw [hcons, htot]
        omega
    · -- head does not match; `fed` lives in the tail. Recurse.
      simp only [hhd, Bool.false_eq_true, if_false] at hf
      have hffull : findHolder tl fed = some rc := by simp only [findHolder]; exact hf
      have hrec : totalRefs (decHolderSession tl fed sess) = totalRefs tl - 1 := ih hndtl hffull
      have hfedne : ¬ hd.1 = fed := by simpa using hhd
      have hexpand : decHolderSession (hd :: tl) fed sess = hd :: decHolderSession tl fed sess := by
        unfold decHolderSession
        simp only [List.map_cons, hhd, Bool.false_eq_true, if_false, List.filter_cons]
        have hguard : (!(hd.1 == fed && hd.2.count == 0)) = true := by
          simp only [hhd, Bool.false_and, Bool.not_false]
        rw [if_pos (by simp [hguard])]
      have htlpos : 1 ≤ totalRefs tl := totalRefs_pos_of_findHolder tl fed rc hffull hpos
      rw [hexpand]
      have h2 : totalRefs (hd :: decHolderSession tl fed sess)
          = hd.2.count + totalRefs (decHolderSession tl fed sess) := by
        simp only [totalRefs, List.map_cons, List.sum_cons]
      rw [h2, hrec, htot]
      omega

/-- **`SwissHoldersCoherent refc t`** — THE bridge predicate: §1's scalar `refcount` IS §2's
per-holder SUM. Stated over the scalar `refc` (the `SwissRecord.refcount` field) so it composes with
the scalar GC decrement, which writes exactly `refc - 1`. Not an aggregate standing in for a
per-holder fact — a FULL equality the joint-step lemma below PRESERVES under a synchronized drop. -/
def SwissHoldersCoherent (refc : Nat) (t : HolderTable) : Prop :=
  refc = totalRefs t

/-- **`bridge_accept_preserves_coherence` — the WELD, §2-side.** Coherence between the
scalar refcount and the per-holder sum is PRESERVED across an accepting drop: if `refc = totalRefs t`
and `fed` is a present, positive holder under a key-unique table, then after §2's `decHolder` the
DECREMENTED scalar `refc - 1` still equals `totalRefs (decHolder t fed)`. The scalar `-1` that
the scalar decrement writes is EXACTLY the per-holder sum after the holder drop — the two models move in
lockstep, not two disconnected halves. -/
theorem bridge_accept_preserves_coherence (refc : Nat) (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (sess : Session) (hnd : NoDupFeds t) (hf : findHolder t fed = some rc) (hpos : 0 < rc.count)
    (hco : SwissHoldersCoherent refc t) :
    SwissHoldersCoherent (refc - 1) (decHolderSession t fed sess) := by
  unfold SwissHoldersCoherent at hco ⊢
  rw [hco, decHolder_pred_total t fed rc sess hnd hf hpos]

/-- **`bridge_last_ref_iff` — the GC boundary agrees across the two models.** Under
coherence and an accepting drop, §2's per-holder sum hits `0` (the `canRevoke` verdict's
`totalRefs t' = 0` condition, `gc.rs:201`) IF AND ONLY IF the scalar hits `0` (the GC boundary's
remove branch condition `e.refcount - 1 = 0`). So §2's `canRevoke` and §1's GC-at-zero reclaim
EXACTLY together — neither reclaims while the other still holds a ref. -/
theorem bridge_last_ref_iff (refc : Nat) (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (sess : Session) (hnd : NoDupFeds t) (hf : findHolder t fed = some rc) (hpos : 0 < rc.count)
    (hco : SwissHoldersCoherent refc t) :
    totalRefs (decHolderSession t fed sess) = 0 ↔ refc - 1 = 0 := by
  unfold SwissHoldersCoherent at hco
  rw [decHolder_pred_total t fed rc sess hnd hf hpos, hco]

/-! ### §2.5a — welding §2's `processDrop` ACCEPT path to the scalar decrement.

The lemmas above are stated over `decHolder` (the structured drop) and the scalar `- 1`. We now pin
that `decHolder` IS the table `processDrop` returns on its accept path — so the bridge holds over
the ACTUAL `gc.rs` verdict function (§2), not just its decomposition. -/

/-- **`processDrop_accept_table` — the accept path returns `decHolderSession`.** When the
session `sess` has a non-empty bucket on a present holder, `processDrop`'s post-table is exactly
`decHolderSession t fed sess`. This pins the bridge's structured drop to the real `gc.rs` verdict
function's output. -/
theorem processDrop_accept_table (t : HolderTable) (fed : Fed) (rc : HolderRef) (sess : Session)
    (hf : findHolder t fed = some rc) (hpos : 0 < sessionCount rc sess) :
    (processDrop t fed sess).2 = decHolderSession t fed sess :=
  right_session_decrements t fed rc hf sess hpos

/-- **`bridge_processDrop_tracks_refcount` — THE bridge over the real functions.** Given
coherence (`refc = totalRefs t`), key-uniqueness, a present holder with positive total `count`, and a
session whose bucket on it is non-empty, §2's `processDrop` accept-path post-table has `totalRefs`
equal to the DECREMENTED §1 scalar `refc - 1`. This is `gcDropTotal` made real: the §2 per-holder
model's drop and the scalar `refc - 1` track each other. -/
theorem bridge_processDrop_tracks_refcount (refc : Nat) (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (sess : Session) (hnd : NoDupFeds t) (hf : findHolder t fed = some rc) (hpos : 0 < rc.count)
    (hsess : 0 < sessionCount rc sess) (hco : SwissHoldersCoherent refc t) :
    totalRefs (processDrop t fed sess).2 = refc - 1 := by
  rw [processDrop_accept_table t fed rc sess hf hsess, decHolder_pred_total t fed rc sess hnd hf hpos]
  unfold SwissHoldersCoherent at hco; omega

/-! ## §3 — the lease-liveness half is RE-EXPORTED, not re-proved.

`CapTPGC` already PROVED the eventual-reclamation half (lease expiry reclaims, current lease never
reclaimed, cross-vat cycles leak only until lease expiry). We re-export the two keystones so the
full distributed-GC guarantee — SAFETY (no premature reclaim, §1; Byzantine-resistant, §2) PLUS
LIVENESS (eventual reclaim, §3) — reads off one module, WITHOUT duplicating those proofs. -/

/-- Re-export: an expired-lease handle IS reclaimable (the liveness keystone; proved in `CapTPGC`). -/
theorem leased_reclaim_eventual {CellId Rights : Type*}
    (lh : Dregg2.Exec.CapTPGC.LeasedHandle CellId Rights) (now : Nat)
    (hexp : Dregg2.Liveness.leaseExpired lh.lease now = true) :
    Dregg2.Exec.CapTPGC.Reclaimable lh now = true :=
  Dregg2.Exec.CapTPGC.captp_gc_by_lease lh now hexp

/-- Re-export: a current-lease handle is NOT reclaimed (the safety dual; proved in `CapTPGC`). -/
theorem leased_no_premature {CellId Rights : Type*}
    (lh : Dregg2.Exec.CapTPGC.LeasedHandle CellId Rights) (now : Nat)
    (hcur : Dregg2.Liveness.leaseExpired lh.lease now = false) :
    Dregg2.Exec.CapTPGC.Reclaimable lh now = false :=
  Dregg2.Exec.CapTPGC.captp_no_premature_reclaim lh now hcur

/-! ## §4 — Non-vacuity + the Rust differential corpus.

Concrete `n = 2` tables exercised so the abstract theorems witness BOTH a TRUE (drop succeeds) and a
FALSE (drop rejected) outcome — and a corpus the Rust `gc.rs` tests mirror one-for-one. -/

section Differential

/-- A two-holder export table: federation `10` holds 1 ref minted under session `42`; federation
`20` holds 1 ref minted under session `99`. `total_refs = 2` (matches the `gc.rs` byzantine test). -/
def demoTable : HolderTable :=
  [(10, { count := 1, sessions := [(42, 1)] }), (20, { count := 1, sessions := [(99, 1)] })]

#guard totalRefs demoTable == 2

-- BYZANTINE: session 99 presented against federation 10's slot ⇒ REJECTED (no bucket), total unchanged.
#guard (processDrop demoTable 10 99).1 == DropResult.invalid
#guard totalRefs (processDrop demoTable 10 99).2 == 2

-- HONEST: federation 10 drops on its CORRECT session 42 ⇒ accepted, total falls to 1 (still held by 20).
#guard (processDrop demoTable 10 42).1 == DropResult.stillHeld
#guard totalRefs (processDrop demoTable 10 42).2 == 1

-- F-11: a drop on session 0 (no ref minted under it) is REJECTED — the legacy session-free path
-- is gone; presenting a session under which nothing was minted decrements nothing.
#guard (processDrop demoTable 10 0).1 == DropResult.invalid
#guard totalRefs (processDrop demoTable 10 0).2 == 2

-- F-12: a holder with TWO sessions' refs. fed 10 minted 2 refs under session 7 and 1 under session 99
-- (e.g. a re-export / reconnect). Per-ref scoping: each session drops only the refs IT minted.
def reexportTable : HolderTable :=
  [(10, { count := 3, sessions := [(7, 2), (99, 1)] })]
#guard totalRefs reexportTable == 3
-- Session 7 (the ORIGINAL) KEEPS its rights: it can drop the two refs it minted (3→2, 2→1).
#guard (processDrop reexportTable 10 7).1 == DropResult.stillHeld
#guard totalRefs (processDrop reexportTable 10 7).2 == 2
-- Session 99 (the NEW one) can drop ONLY its own ref — the last ref reclaims (3→2 here, single drop).
#guard (processDrop reexportTable 10 99).1 == DropResult.stillHeld
#guard totalRefs (processDrop reexportTable 10 99).2 == 2
-- After session 99 spends its only ref, session 99 can no longer drop (its bucket is gone): Invalid.
#guard (processDrop (decHolderSession reexportTable 10 99) 10 99).1 == DropResult.invalid

-- ABSENT holder ⇒ Invalid, no change.
#guard (processDrop demoTable 99 1).1 == DropResult.invalid

/-- **The Rust differential corpus.** Each row is `(table, fed, session, verdict, postTotal)`
mirroring a `gc.rs` / redteam test. A Rust harness replays `process_drop_with_session` on the same
inputs and checks the `DropResult` + `ExportEntry.total_refs` agree. Session is now MANDATORY
(F-11): there is no session-free row. The F-12 rows pin the per-ref scoping (a re-export keeps the
original session's drop rights, and each session drops only what it minted). -/
def gcDifferentialCorpus : List (HolderTable × Fed × Session × DropResult × Nat) :=
  [ -- byzantine_node_different_session_cannot_drop_others_refs: session 99 vs fed 10's slot
    (demoTable, 10, 99, DropResult.invalid, 2)
  , -- honest drop on correct session (still held by peer)
    (demoTable, 10, 42, DropResult.stillHeld, 1)
  , -- F-11: a session-0 drop (no ref minted under it) is rejected — the session-free door is shut
    (demoTable, 10, 0, DropResult.invalid, 2)
  , -- F-12: the ORIGINAL session 7 keeps its drop rights after a re-export under session 99 (3→2)
    (reexportTable, 10, 7, DropResult.stillHeld, 2)
  , -- F-12: the NEW session 99 may drop only the ONE ref it minted (3→2)
    (reexportTable, 10, 99, DropResult.stillHeld, 2)
  , -- unknown federation ⇒ Invalid
    (demoTable, 99, 1, DropResult.invalid, 2) ]

/-- The corpus is self-consistent: every row's recorded `(verdict, postTotal)` is exactly what
`processDrop` produces. (A Rust mirror checks `process_drop_with_session` matches these rows.) -/
theorem gcDifferentialCorpus_faithful :
    ∀ row ∈ gcDifferentialCorpus,
      (processDrop row.1 row.2.1 row.2.2.1).1 = row.2.2.2.1
      ∧ totalRefs (processDrop row.1 row.2.1 row.2.2.1).2 = row.2.2.2.2 := by
  decide

/-! ### §4a — the F-11 / F-12 headline laws (the closed findings, as theorems).

These are the proof teeth that would CATCH a regression of either finding: F-11 (a session-free /
unauthenticated drop must not reclaim) and F-12 (a re-export must not transfer the original session's
drop rights, and a session must not drop refs another session minted). They live over `processDrop`,
the faithful model of the fixed `gc.rs` — exactly the refcount-drop path the lease-only proof was
blind to. -/

/-- **`f11_session_free_drop_denied` — F-11 closed.** A session under which the holder
minted NO ref (`sessionCount rc sess = 0`) — a forged, stale, or "session 0 / no session" credential
— cannot reclaim: the drop is `invalid` and `total_refs` is unchanged. This is the headline F-11
law: the session-free reclaim door is shut at the model level, so a blind lease proof cannot
hide the gap. -/
theorem f11_session_free_drop_denied (t : HolderTable) (fed : Fed) (rc : HolderRef) (sess : Session)
    (hf : findHolder t fed = some rc) (hzero : sessionCount rc sess = 0) :
    (processDrop t fed sess).1 = invalid ∧ totalRefs (processDrop t fed sess).2 = totalRefs t := by
  refine ⟨?_, wrong_session_preserves_total t fed rc hf sess hzero⟩
  rw [wrong_session_no_op t fed rc hf sess hzero]

/-- **`f12_reexport_preserves_original_session_rights` — F-12 closed (half 1).** A
re-export under a NEW session does not strip the ORIGINAL session's bucket: if the original session
`s₀` had a positive bucket, it STILL has the same positive bucket after the new session `s₁ ≠ s₀`
mints a ref. So the original session retains the right to drop the refs it minted. (Modelled as: the
holder's `s₀` bucket is unchanged when its `sessions` grows a distinct `s₁` entry.) -/
theorem f12_reexport_preserves_original_session_rights
    (rc : HolderRef) (s₀ s₁ : Session) (k : Nat)
    (hne : s₁ ≠ s₀)
    (hrc' : HolderRef)
    (hadd : hrc'.sessions = (s₁, k) :: rc.sessions) :
    sessionCount hrc' s₀ = sessionCount rc s₀ := by
  unfold sessionCount
  rw [hadd]
  simp only [List.find?_cons]
  have : (s₁ == s₀) = false := by simpa using hne
  rw [this]

/-- **`f12_session_drops_only_its_own` — F-12 closed (half 2).** A drop on a holder with two
session buckets touches ONLY the named session: the OTHER session's bucket is left intact, so the new
session can never reclaim a ref the original session minted, and vice-versa. We witness this on the
concrete `reexportTable`: dropping session 99 leaves federation 10's session-7 bucket = 2 untouched. -/
theorem f12_session_drops_only_its_own :
    (findHolder (decHolderSession reexportTable 10 99) 10).map (fun rc => sessionCount rc 7)
      = some 2 := by
  decide

/-! ### §4b — the bridge predicate is NON-VACUOUS (witnessed TRUE and FALSE).

`SwissHoldersCoherent` and `NoDupFeds` are real predicates: each is satisfied by a concrete table and
REFUTED by another. So the bridge theorems are not vacuously discharged by an unsatisfiable
hypothesis. -/

/-- Coherence holds when the scalar `refcount` equals the per-holder sum (`demoTable` sums to `2`). -/
theorem coherent_demo : SwissHoldersCoherent 2 demoTable := by
  unfold SwissHoldersCoherent; decide

/-- Coherence FAILS when the scalar disagrees with the sum (`3 ≠ totalRefs demoTable = 2`) — the
predicate constrains, it is not `True`. -/
theorem not_coherent_demo : ¬ SwissHoldersCoherent 3 demoTable := by
  unfold SwissHoldersCoherent; decide

/-- After an accepting drop on `demoTable` (holder `10`, its session `42`), coherence to scalar `1`
holds — the per-holder sum fell from `2` to `1` in lockstep with the §1 scalar `2 - 1`. -/
theorem coherent_after_drop : SwissHoldersCoherent 1 (decHolderSession demoTable 10 42) := by
  unfold SwissHoldersCoherent; decide

/-- `NoDupFeds` admits the well-formed two-holder table. -/
theorem nodup_demo : NoDupFeds demoTable := by unfold NoDupFeds; decide

/-- `NoDupFeds` REJECTS a duplicate-key table — the key-uniqueness invariant rules something out, so
the unit-exactness it underwrites is not vacuous. -/
theorem not_nodup_dup :
    ¬ NoDupFeds [(10, { count := 1, sessions := [(1, 1)] }), (10, { count := 1, sessions := [(2, 1)] })] := by
  unfold NoDupFeds; decide

/-- End-to-end concrete witness of `bridge_processDrop_tracks_refcount`: starting coherent at scalar
`2`, the §2 accept-path post-table (drop holder `10` on its session `42`) sums to `1 = 2 - 1`. -/
theorem bridge_tracks_demo :
    totalRefs (processDrop demoTable 10 42).2 = 2 - 1 :=
  bridge_processDrop_tracks_refcount 2 demoTable 10 { count := 1, sessions := [(42, 1)] } 42
    nodup_demo (by decide) (by decide) (by decide) coherent_demo

end Differential

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms wrong_session_no_op
#assert_axioms wrong_session_preserves_total
#assert_axioms byzantine_cannot_drop_victim_ref
#assert_axioms right_session_decrements
#assert_axioms f11_session_free_drop_denied
#assert_axioms f12_reexport_preserves_original_session_rights
#assert_axioms f12_session_drops_only_its_own
#assert_axioms decHolderMap_not_mem
#assert_axioms decHolderFilter_not_mem
#assert_axioms decHolder_not_mem
#assert_axioms totalRefs_pos_of_findHolder
#assert_axioms decHolder_pred_total
#assert_axioms bridge_accept_preserves_coherence
#assert_axioms bridge_last_ref_iff
#assert_axioms processDrop_accept_table
#assert_axioms bridge_processDrop_tracks_refcount
#assert_axioms leased_reclaim_eventual
#assert_axioms leased_no_premature
#assert_axioms gcDifferentialCorpus_faithful

end Dregg2.Exec.CapTPGCConcrete
