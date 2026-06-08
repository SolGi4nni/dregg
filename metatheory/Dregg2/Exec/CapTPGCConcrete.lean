/-
# Dregg2.Exec.CapTPGCConcrete — CapTP distributed-GC SAFETY over the verified swiss refcount table.

`Exec.CapTPGC` closed the distributed-GC *liveness* OPEN by lease-based reclaim (a handle whose
lease has lapsed is reclaimable; a current lease is never reclaimed; cross-vat cycles leak only
until lease expiry). That is the **eventual-reclamation** half. This module supplies the dual
**no-premature-reclaim / Byzantine-resistance** half — over the *actually-verified* state, the
`RecordKernel` swiss refcount table that `execFullA`'s `swissDropA` / `enlivenRefA` arms mutate —
and we DO NOT re-prove the lease-liveness half (we re-export it from `CapTPGC` for the headline).

Two safety teeth, both at `n > 1` (multiple holders / multiple sessions; `n = 1` is the
scales-to-zero special case, NOT the target):

  **§1 — refcount-positivity (no premature reclaim over the swiss table).** Over the verified
  `swissDropK` / `swissDropA` GC-at-zero arm: an entry with `refcount > 1` STAYS in the swiss
  table under a drop (the entry is found by `findSwiss` after the drop — it is NOT reclaimed); a
  drop on a `refcount = 0` entry is REJECTED (fail-closed); the entry is removed ONLY at the
  `refcount = 1 → 0` boundary (`swissDropK_gc_at_one`, reused). This is the swiss-table mirror of
  the Rust `ExportEntry.total_refs > 0 ⇒ entry retained` invariant (`gc.rs:207`).

  **§2 — the session-id Byzantine tooth.** A faithful EXECUTABLE Lean model of
  `ExportGcManager::process_drop_inner` (`gc.rs:170`) — a per-`(cell, federation)` refcount table
  carrying a `session_id`, with `processDrop` performing the EXACT session check
  (`ref_count.session_id != expected ⇒ DropResult::Invalid`, `gc.rs:194`). We prove
  `byzantine_node_different_session_cannot_drop_others_refs` (`gc.rs:670`) AS A THEOREM at `n = 2`
  holders: a Byzantine node presenting the WRONG session for a victim holder's ref leaves
  `total_refs` UNCHANGED, while the honest holder on the correct session CAN decrement its own ref.

The connection to the verified executor: §1 is stated directly over `execFullA … (.swissDropA …)`
and `swissDropK`. §2's table MODELS the *per-holder* session refcounts of `gc.rs`. HONESTY: §1
and §2 are at present TWO INDEPENDENTLY-SOUND models that are NOT YET BRIDGED — there is no
theorem proving that §2's per-holder SUM equals §1's swiss-entry `refcount` field, nor a
`gcDropTotal`-tracks-decrement lemma (no such def exists). The intended bridge
(`swissEntry.refcount = Σ_{holders} holder.total_refs`, plus decrement-tracking) is OPEN; see
`docs/rebuild/_PROOF-INTEGRITY-LEDGER.md` MID-1. Both halves bite on their own model.

The Rust differential corpus (`gcDifferentialCorpus`) mirrors the four `gc.rs` session tests:
`export_drop_rejected_from_wrong_session`, `export_session_superseded_by_reexport`,
`byzantine_node_different_session_cannot_drop_others_refs`, and the legacy session-0 path.

Crypto note: session IDs here are MODELLED as opaque `Nat` tokens whose unforgeability is an
EXTERNAL assumption (a session id is minted by `CapHello` and is unguessable to a Byzantine peer).
We do NOT model the handshake; the theorem is "GIVEN the adversary cannot present the victim's
session id, it cannot drop the victim's ref" — `SessionUnforgeable` names that hypothesis honestly.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.CapTPGC
import Dregg2.Circuit.Spec.swissdrop
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPGCConcrete

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SwissDrop (DropSpec execFullA_drop_iff_spec dropReceipt)

/-! ## §1 — Refcount-positivity safety over the VERIFIED swiss table.

The runtime invariant we want is: *while a sturdy-ref export still has live references
(`refcount > 0`), the swiss-table entry is RETAINED — it is never GC-reclaimed prematurely.* The
swiss entry's `refcount` field IS the `gc.rs` `ExportEntry.total_refs` (the SUM of per-holder
counts). `swissDropK` (the verified GC arm `swissDropA` runs) decrements it and removes the entry
EXACTLY at the `1 → 0` boundary. So: a drop on a `> 1` entry leaves it FINDABLE (retained), a drop
on a `= 0` entry is REJECTED, and only the last-ref drop reclaims. -/

/-- **`drop_retains_when_refcount_gt_one` (PROVED) — a multi-ref entry STAYS in the swiss table.**
If the swiss entry for `sw` has `refcount > 1` and a `swissDropA` commits into `s'`, the entry is
STILL present after the drop (`findSwiss s'.kernel.swiss sw = some …` with the decremented count) —
it is NOT reclaimed. This is the no-premature-reclaim guarantee at the verified-state level:
`total_refs > 1` (more than one outstanding holder) ⇒ the export entry is retained. -/
theorem drop_retains_when_refcount_gt_one (s s' : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (e : SwissRecord)
    (hf : findSwiss s.kernel.swiss sw = some e) (hgt : 1 < e.refcount)
    (h : execFullA s (.swissDropA sw actor exporter) = some s') :
    findSwiss s'.kernel.swiss sw = some { e with refcount := e.refcount - 1 } := by
  -- recover the kernel post-state from the executor⟺spec characterization.
  rcases (execFullA_drop_iff_spec s sw actor exporter s').mp h with ⟨_, ⟨k', hk, hs'⟩⟩
  have hker : s'.kernel = k' := congr_arg RecChainedState.kernel hs'
  -- `swissDropK` on a `> 1` entry takes the DECREMENT (replace) branch, not the GC (remove) branch.
  have hz : ¬ e.refcount = 0 := by omega
  have hone : ¬ e.refcount - 1 = 0 := by omega
  have hk2 : swissDropK s.kernel sw =
      some { s.kernel with swiss := replaceSwiss s.kernel.swiss sw { e with refcount := e.refcount - 1 } } := by
    simp only [swissDropK, hf, if_neg hz, if_neg hone]
  rw [hker]
  have hkeq : k' = { s.kernel with swiss := replaceSwiss s.kernel.swiss sw { e with refcount := e.refcount - 1 } } :=
    Option.some.inj (hk.symm.trans hk2)
  rw [hkeq]
  -- after replacing with the decremented record, looking `sw` up returns exactly that record.
  exact findSwiss_replaceSwiss_self s.kernel.swiss sw e { e with refcount := e.refcount - 1 } hf
    (by show e.swiss = sw; exact findSwiss_swiss_eq hf)

/-- **`drop_rejected_when_refcount_zero` (PROVED) — fail-closed at zero.** A drop on an entry whose
`refcount` is already `0` is REJECTED by `execFullA` (the GC gate never under-flows). The verified
mirror of `process_drop_inner`'s `if ref_count.count == 0 { return Invalid }` (`gc.rs:186`). -/
theorem drop_rejected_when_refcount_zero (s : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (e : SwissRecord)
    (hf : findSwiss s.kernel.swiss sw = some e) (hz : e.refcount = 0) :
    execFullA s (.swissDropA sw actor exporter) = none :=
  Dregg2.Circuit.Spec.SwissDrop.drop_rejects_zero_refcount s sw actor exporter e hf hz

/-- **`reclaim_only_at_last_ref` (PROVED) — the entry is reclaimed ONLY when its last ref drops.**
The contrapositive packaging of the two laws above: if a `swissDropA` reclaims the entry (makes it
absent: `findSwiss s'.kernel.swiss sw = none`), then the PRE-drop refcount was exactly `1` — i.e.
reclamation happens at, and only at, the `1 → 0` boundary, never while `refcount > 1`. So
`total_refs > 0` after the would-be decrement is impossible to have been reclaimed: a `> 1` entry is
retained (`drop_retains_when_refcount_gt_one`), a `0` entry is rejected outright. -/
theorem reclaim_only_at_last_ref (s s' : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (e : SwissRecord)
    (hf : findSwiss s.kernel.swiss sw = some e)
    (h : execFullA s (.swissDropA sw actor exporter) = some s')
    (hgone : findSwiss s'.kernel.swiss sw = none) :
    e.refcount = 1 := by
  -- positivity comes from the guard (a committed drop requires `0 < refcount`).
  rcases (execFullA_drop_iff_spec s sw actor exporter s').mp h with ⟨⟨_, e', hf', hpos'⟩, _⟩
  have hee : e' = e := Option.some.inj (hf'.symm.trans hf)
  rw [hee] at hpos'
  -- if `refcount > 1`, the entry would still be present — contradicting `hgone`.
  rcases Nat.lt_or_ge 1 e.refcount with hgt | hle
  · have := drop_retains_when_refcount_gt_one s s' sw actor exporter e hf hgt h
    rw [this] at hgone; exact absurd hgone (by simp)
  · -- `0 < refcount ≤ 1` forces `refcount = 1`.
    omega

/-! ## §2 — The session-id Byzantine tooth (a faithful executable model of `gc.rs`).

`gc.rs`'s `ExportGcManager` keeps, per exported `cell`, a map `federation ↦ RefCount` where each
`RefCount` carries a `session_id`. A `DropRef` is processed by `process_drop_inner` (`gc.rs:170`):
look up the cell, then the holder; reject if absent or `count == 0`; **reject if the presented
session id ≠ the holder's stored session id**; else decrement that holder's count and the cell's
`total_refs`. We model the per-cell holder table (the inner `HashMap<FederationId, RefCount>`)
faithfully as an association list and reproduce `process_drop_inner` EXACTLY. -/

/-- A federation/holder id (the `gc.rs` `FederationId`, modelled as a `Nat`). -/
abbrev Fed := Nat

/-- A session id (the `gc.rs` `SessionId = u64`, an opaque unguessable token; see crypto note). -/
abbrev Session := Nat

/-- The per-holder reference count with its session binding — the `gc.rs` `RefCount`
(`gc.rs:39`), minus the `last_activity` field (that drives the *lease* half, already in
`CapTPGC`; here we model the *session/refcount* half). -/
structure HolderRef where
  /-- how many references this holder has (`RefCount.count`). -/
  count   : Nat
  /-- the session under which this holder's ref was created (`RefCount.session_id`). -/
  session : Session
deriving DecidableEq, Repr

/-- The per-cell export entry's holder table — the `gc.rs` `ExportEntry.holders`
(`HashMap<FederationId, RefCount>`) as an association list keyed by `Fed`. -/
abbrev HolderTable := List (Fed × HolderRef)

/-- Look up a holder's `RefCount` (first match), `none` if absent — `holders.get(&fed)`. -/
def findHolder (t : HolderTable) (fed : Fed) : Option HolderRef :=
  (t.find? (fun p => p.1 == fed)).map (·.2)

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

/-- Decrement a holder's count by 1, dropping the holder entirely when it hits 0 (the `gc.rs`
`if ref_count.count == 0 { holders.remove(&fed) }`, `gc.rs:203`). Other holders untouched. -/
def decHolder (t : HolderTable) (fed : Fed) : HolderTable :=
  (t.map (fun p =>
      if p.1 == fed then (p.1, { p.2 with count := p.2.count - 1 }) else p)).filter
    (fun p => !(p.1 == fed && p.2.count == 0))

/-- **`processDrop t fed expected`** — a FAITHFUL executable model of `gc.rs`'s
`process_drop_inner` (`gc.rs:170`). Returns the verdict AND the post-table. The session check is
EXACT: `expected = some sess` and the holder's stored session ≠ `sess` ⇒ `(invalid, t)` (NO
mutation). `expected = none` is the legacy session-unaware `process_drop` path (`gc.rs:0`). -/
def processDrop (t : HolderTable) (fed : Fed) (expected : Option Session) : DropResult × HolderTable :=
  match findHolder t fed with
  | none    => (invalid, t)                        -- unknown holder ⇒ Invalid, no change
  | some rc =>
      if rc.count = 0 then (invalid, t)            -- over-decrement guard ⇒ Invalid, no change
      else
        match expected with
        | some sess =>
            if rc.session ≠ sess then (invalid, t) -- SESSION MISMATCH ⇒ Invalid, NO MUTATION
            else
              let t' := decHolder t fed
              (if totalRefs t' = 0 then canRevoke else stillHeld, t')
        | none =>
            let t' := decHolder t fed
            (if totalRefs t' = 0 then canRevoke else stillHeld, t')

/-! ### §2a — the session check is a NO-OP on a mismatch (the core invariant). -/

/-- **`wrong_session_no_op` (PROVED) — a wrong-session drop does NOT touch the table.** If the
holder `fed` exists with a positive count under session `s`, and a `DropRef` is presented with
`expected = some s'` for `s' ≠ s`, then `processDrop` returns `(invalid, t)` — the table is
RETURNED UNCHANGED. This is the exact `gc.rs:194` `if ref_count.session_id != expected { return
Invalid }` short-circuit, BEFORE any decrement. The Byzantine-resistance primitive. -/
theorem wrong_session_no_op (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc) (hpos : 0 < rc.count)
    (s' : Session) (hne : rc.session ≠ s') :
    processDrop t fed (some s') = (invalid, t) := by
  unfold processDrop
  rw [hf]
  have hz : ¬ rc.count = 0 := by omega
  simp only [if_neg hz, if_pos hne]

/-- **`wrong_session_preserves_total` (PROVED) — `total_refs` is UNCHANGED by a wrong-session drop.**
The corollary the Rust test `byzantine_node_different_session_cannot_drop_others_refs` asserts: a
wrong-session drop leaves `totalRefs` exactly as it was. Follows from `wrong_session_no_op` (the
whole table is unchanged, so its sum is). -/
theorem wrong_session_preserves_total (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc) (hpos : 0 < rc.count)
    (s' : Session) (hne : rc.session ≠ s') :
    totalRefs (processDrop t fed (some s')).2 = totalRefs t := by
  rw [wrong_session_no_op t fed rc hf hpos s' hne]

/-! ### §2b — the named (honest) unforgeability hypothesis.

The security claim is conditional on the adversary being UNABLE to present the victim holder's
session id. `gc.rs` mints session ids in `CapHello`; we do NOT model the handshake. `SessionUnforgeable`
names that assumption: a Byzantine federation `byz`, acting on a victim holder `victim`'s ref, can
only present sessions DISTINCT from the victim's stored session. This is the honest crypto boundary
— the theorem is sound MODULO this hypothesis, which we state, never fake. -/

/-- **`SessionUnforgeable t victim byzSession`** — the byzantine peer's presented session
`byzSession` is NOT the victim holder's stored session. (In the real system this holds because the
victim's session id is an unguessable `CapHello`-minted token; here it is an explicit hypothesis.) -/
def SessionUnforgeable (t : HolderTable) (victim : Fed) (byzSession : Session) : Prop :=
  ∀ rc : HolderRef, findHolder t victim = some rc → rc.session ≠ byzSession

/-- **`byzantine_cannot_drop_victim_ref` (PROVED, n>1) — the headline Byzantine theorem.**
THE security property modelled from `gc.rs:670`'s
`byzantine_node_different_session_cannot_drop_others_refs`, at `n = 2` holders (a victim and the
byzantine peer both hold refs to the same cell). GIVEN the byzantine peer cannot forge the victim's
session (`SessionUnforgeable`), a `DropRef` it submits against the VICTIM's holder slot
(`from_federation = victim`, but carrying the byzantine peer's own session) is REJECTED as
`invalid` AND leaves `total_refs` untouched — the victim's ref survives. The drop touched neither
the victim's count nor anyone else's. -/
theorem byzantine_cannot_drop_victim_ref
    (t : HolderTable) (victim : Fed) (rc : HolderRef)
    (hf : findHolder t victim = some rc) (hpos : 0 < rc.count)
    (byzSession : Session) (hunf : SessionUnforgeable t victim byzSession) :
    processDrop t victim (some byzSession) = (invalid, t)
    ∧ totalRefs (processDrop t victim (some byzSession)).2 = totalRefs t := by
  have hne : rc.session ≠ byzSession := hunf rc hf
  exact ⟨wrong_session_no_op t victim rc hf hpos byzSession hne,
         wrong_session_preserves_total t victim rc hf hpos byzSession hne⟩

/-! ### §2c — the HONEST side still works (the model is not vacuously fail-closed).

A fail-closed model that rejected EVERYTHING would trivially satisfy §2b. We prove the dual: the
honest holder, presenting its CORRECT session, CAN decrement its own ref — so the rejection in §2b
is genuinely SESSION-SCOPED, not a blanket refusal. This is the de-vacuity tooth for the tool. -/

/-- **`right_session_decrements` (PROVED) — the honest holder drops its OWN ref.** With the matching
session, a `count = 1` holder's drop succeeds: the verdict reflects the post-table and the holder's
own count went to 0 (so it is removed from the table). Witnesses that `processDrop` is NOT vacuously
fail-closed — the session gate ADMITS the right session. -/
theorem right_session_decrements (t : HolderTable) (fed : Fed) (rc : HolderRef)
    (hf : findHolder t fed = some rc) (hpos : 0 < rc.count) :
    (processDrop t fed (some rc.session)).2 = decHolder t fed := by
  unfold processDrop
  rw [hf]
  have hz : ¬ rc.count = 0 := by omega
  simp only [if_neg hz, ne_eq, not_true_eq_false, if_false]

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

/-- A two-holder export table: federation `10` holds 1 ref on session `42`; federation `20` holds
1 ref on session `99`. `total_refs = 2` (matches the `gc.rs` byzantine test's setup). -/
def demoTable : HolderTable := [(10, { count := 1, session := 42 }), (20, { count := 1, session := 99 })]

#guard totalRefs demoTable == 2

-- BYZANTINE: federation 20's session (99) presented against federation 10's slot ⇒ REJECTED, total unchanged.
#guard (processDrop demoTable 10 (some 99)).1 == DropResult.invalid
#guard totalRefs (processDrop demoTable 10 (some 99)).2 == 2

-- HONEST: federation 10 drops with its CORRECT session 42 ⇒ accepted, total falls to 1 (still held by 20).
#guard (processDrop demoTable 10 (some 42)).1 == DropResult.stillHeld
#guard totalRefs (processDrop demoTable 10 (some 42)).2 == 1

-- WRONG-SESSION SUPERSEDED: a re-export bumps the session; the OLD session no longer drops.
-- (Federation 10 re-exported on session 7 supersedes its session-42 binding.)
def supersededTable : HolderTable := [(10, { count := 2, session := 7 })]
#guard (processDrop supersededTable 10 (some 1)).1 == DropResult.invalid   -- old session 1 fails
#guard totalRefs (processDrop supersededTable 10 (some 1)).2 == 2
#guard (processDrop supersededTable 10 (some 7)).1 == DropResult.stillHeld -- current session 7 works (2→1)
#guard totalRefs (processDrop supersededTable 10 (some 7)).2 == 1

-- LEGACY session-0 path (`expected = none`): no session check, drop proceeds.
#guard (processDrop demoTable 10 none).1 == DropResult.stillHeld
#guard totalRefs (processDrop demoTable 10 none).2 == 1

-- ABSENT holder ⇒ Invalid, no change.
#guard (processDrop demoTable 99 (some 1)).1 == DropResult.invalid

/-- **The Rust differential corpus.** Each row is `(table, fed, expectedSession, verdict, postTotal)`
mirroring a `gc.rs` test. A Rust harness replays `process_drop_with_session` on the same inputs and
checks the `DropResult` + `ExportEntry.total_refs` agree. -/
def gcDifferentialCorpus : List (HolderTable × Fed × Option Session × DropResult × Nat) :=
  [ -- byzantine_node_different_session_cannot_drop_others_refs (gc.rs:670)
    (demoTable, 10, some 99, DropResult.invalid, 2)
  , -- honest drop on correct session (still held by peer)
    (demoTable, 10, some 42, DropResult.stillHeld, 1)
  , -- export_drop_rejected_from_wrong_session (gc.rs:~470): re-export superseded the session
    (supersededTable, 10, some 1, DropResult.invalid, 2)
  , -- correct (current) session succeeds
    (supersededTable, 10, some 7, DropResult.stillHeld, 1)
  , -- legacy process_drop (session-unaware) path (gc.rs:~510)
    (demoTable, 10, none, DropResult.stillHeld, 1)
  , -- unknown federation ⇒ Invalid
    (demoTable, 99, some 1, DropResult.invalid, 2) ]

/-- The corpus is self-consistent: every row's recorded `(verdict, postTotal)` is exactly what
`processDrop` produces. (A Rust mirror checks `process_drop_with_session` matches these rows.) -/
theorem gcDifferentialCorpus_faithful :
    ∀ row ∈ gcDifferentialCorpus,
      (processDrop row.1 row.2.1 row.2.2.1).1 = row.2.2.2.1
      ∧ totalRefs (processDrop row.1 row.2.1 row.2.2.1).2 = row.2.2.2.2 := by
  decide

end Differential

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms drop_retains_when_refcount_gt_one
#assert_axioms drop_rejected_when_refcount_zero
#assert_axioms reclaim_only_at_last_ref
#assert_axioms wrong_session_no_op
#assert_axioms wrong_session_preserves_total
#assert_axioms byzantine_cannot_drop_victim_ref
#assert_axioms right_session_decrements
#assert_axioms leased_reclaim_eventual
#assert_axioms leased_no_premature
#assert_axioms gcDifferentialCorpus_faithful

end Dregg2.Exec.CapTPGCConcrete
