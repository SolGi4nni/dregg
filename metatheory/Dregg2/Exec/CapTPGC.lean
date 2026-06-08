/-
# Dregg2.Exec.CapTPGC — closing the CapTP distributed-GC OPEN by LEASE-BASED RECLAIM.

`Dregg2.Exec.CapTP` §4 left distributed GC as a documented `-- OPEN:` residue:

  > -- OPEN: distributed_gc_liveness — eventual reclamation of unreachable exported caps.
  > --   Reason: cross-vat reference cycles cannot be decided dead by one vat (CellLiveness's
  > --   death_is_timed_out / cross-vat-cycle impossibility); needs a cross-vat lease model.

This module supplies that cross-vat lease model and closes the OPEN *honestly* — NOT by
faking a "decide dead across vats" theorem (that decision is **impossible**, and
`Liveness.dead_undecidable` PROVES it), but by REALIZING the only sound resolution the design
and `Liveness` already endorse: **lease-based reclaim**. An exported cap's local import
handle carries a lease (`gc.rs`'s `last_activity + max_idle_blocks` idle window — see
`ExportGcManager::stale_exports`, `gc.rs:219`); the runtime reclaims a handle once its lease
has expired, and *never* reclaims a handle whose lease is still current (fail-closed). The
cross-vat reference CYCLE leaks — and that leak is a PROVED CONSEQUENCE of the impossibility,
the price of soundness, not a bug to fix.

The faithful `gc.rs` correspondence (the lease IS the idle window):

  * `RefCount.last_activity` (`gc.rs:43`) + a `maxIdle` window  ⟶  a `Liveness.Lease`
    whose `expiresAt = lastActivity + maxIdle`;
  * `stale_exports`' predicate `current_height - last_activity > max_idle_blocks`
    (`gc.rs:226`)  ⟶  `Liveness.leaseExpired` at `now`;
  * `record_export_with_session` bumping `last_activity = current_height` (`gc.rs:136`)
    ⟶  lease RENEWAL (a fresh, un-expired lease as of `now`);
  * `crossvat_cycle_leaks` / `dead_undecidable`  ⟶  why proven-death reclaim is impossible
    and lease-expiry is the ONLY sound trigger.

This module REUSES `Liveness`/`Exec.CellLiveness` and `Exec.CapTP.ImportHandle` directly; it
invents no new verify side and no new decision procedure.
-/
import Dregg2.Liveness
import Dregg2.Exec.CellLiveness
import Dregg2.Exec.CapTP
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPGC

open Dregg2.Liveness
open Dregg2.Exec.CapTP (ImportHandle)

/-! ## §1 — The leased import handle.

An import handle (`Exec.CapTP.ImportHandle` — the local face of a cap exported to a remote
vat) is reclaimed not by proving it dead (impossible across vats) but by **lease expiry**.
We attach to it the `gc.rs` idle window as a `Liveness.Lease`: the lease lapses at
`lastActivity + maxIdle`, exactly `stale_exports`' `current_height - last_activity >
max_idle_blocks` boundary. -/

/-- **`leaseOf last maxIdle`** — the `Liveness.Lease` realizing `gc.rs`'s idle window for a
handle last active at block `last` with idle threshold `maxIdle`. The lease lapses at
`last + maxIdle`; `leaseExpired (leaseOf last maxIdle) now` is `decide (last + maxIdle ≤ now)`,
the locally-decidable stale-export test (`gc.rs:226`, modulo `>` vs `≤` at the boundary, which
`stale_exports` resolves with strict `>`; we use the `Lease`'s own `≤` convention — the
honest, locally-decidable timeout either way). -/
def leaseOf (last maxIdle : Nat) : Lease :=
  { expiresAt := last + maxIdle, lastActivity := last }

/-- **`LeasedHandle`** — an `ImportHandle` together with the lease that governs its reclaim.
This is the local bookkeeping `ImportGcManager` keeps (`gc.rs`): the handle stands in for the
remote cap, and the lease (the idle window over `last_activity`) is the ONLY sound reclaim
trigger across vats. -/
structure LeasedHandle (CellId Rights : Type*) where
  /-- The import handle (the local proxy for the remote cap). -/
  handle : ImportHandle CellId Rights
  /-- The lease governing reclaim (the `gc.rs` idle window as a `Liveness.Lease`). -/
  lease  : Lease

/-- **`Reclaimable lh now`** — the locally-decidable reclaim trigger: the handle's lease has
expired at `now`. This is `stale_exports`' verdict — a handle whose idle window has lapsed is
a candidate for reclaim — lifted to the `Liveness.leaseExpired` test. It NEVER decides global
deadness; it times the handle out. Pure `Bool`, no cross-vat cooperation, no global snapshot. -/
def Reclaimable {CellId Rights : Type*} (lh : LeasedHandle CellId Rights) (now : Nat) : Bool :=
  leaseExpired lh.lease now

/-- **`renew lh now`** — lease RENEWAL: `record_export_with_session` bumping `last_activity`
to the current block (`gc.rs:136`). The renewed handle's lease is fresh as of `now` (lapses at
`now + maxIdle`), so it is NOT reclaimable at `now` for any positive idle window. -/
def renew {CellId Rights : Type*} (lh : LeasedHandle CellId Rights) (now maxIdle : Nat) :
    LeasedHandle CellId Rights :=
  { lh with lease := leaseOf now maxIdle }

/-! ## §2 — The two reclaim laws: expired ⇒ reclaimable, renewed ⇒ NOT reclaimed. -/

/-- **`captp_gc_by_lease` (PROVED) — an expired-lease import handle is reclaimable.**
If the handle's lease has lapsed at `now` (`leaseExpired lh.lease now = true` — the
`stale_exports` idle window has elapsed), then the handle IS `Reclaimable`. This is the sound
distributed-GC trigger that CLOSES the `Exec.CapTP` §4 OPEN: reclamation is driven by lease
expiry, the locally-decidable timeout, never by deciding global deadness. The honest
realization of "eventual reclamation of unreachable exported caps" — eventual, because every
handle's lease eventually lapses unless renewed. -/
theorem captp_gc_by_lease {CellId Rights : Type*}
    (lh : LeasedHandle CellId Rights) (now : Nat)
    (hexp : leaseExpired lh.lease now = true) :
    Reclaimable lh now = true :=
  hexp

/-- **`captp_no_premature_reclaim` (PROVED) — a current-lease handle is NOT reclaimed.**
Fail-closed safety: if the handle's lease has NOT yet lapsed at `now`
(`leaseExpired lh.lease now = false` — the holder is still within its idle window), then the
handle is NOT `Reclaimable`. The runtime never reclaims a handle whose lease is current, so a
live-leased cap is never stranded — exactly `stale_exports` refusing to list a recently-active
export. This is the safety dual of `captp_gc_by_lease`. -/
theorem captp_no_premature_reclaim {CellId Rights : Type*}
    (lh : LeasedHandle CellId Rights) (now : Nat)
    (hcur : leaseExpired lh.lease now = false) :
    Reclaimable lh now = false :=
  hcur

/-- **`captp_renewed_not_reclaimed` (PROVED) — a leased-AND-renewed handle is NOT reclaimed.**
The headline no-premature-reclaim law on RENEWAL: renewing a handle at block `now` with a
positive idle window (`0 < maxIdle`) yields a handle that is NOT reclaimable at `now`. Renewal
(`record_export_with_session` bumping `last_activity = now`, `gc.rs:136`) sets the lease to
lapse at `now + maxIdle > now`, so `leaseExpired` is `false` and reclaim is refused. Activity
keeps a cross-vat cap alive precisely as long as the holder keeps touching it — the lease is
the liveness bound, renewed by use. -/
theorem captp_renewed_not_reclaimed {CellId Rights : Type*}
    (lh : LeasedHandle CellId Rights) (now maxIdle : Nat)
    (hpos : 0 < maxIdle) :
    Reclaimable (renew lh now maxIdle) now = false := by
  unfold Reclaimable renew leaseOf leaseExpired
  -- The renewed lease lapses at `now + maxIdle`; `now + maxIdle ≤ now` is false since `0 < maxIdle`.
  simp only [decide_eq_false_iff_not, Nat.not_le]
  omega

/-! ## §3 — The cross-vat cycle leak is THE PRICE of the impossibility.

The reason CapTP cannot reclaim by proven-death — and must fall back to lease expiry — is the
PROVED impossibility of `Liveness`: deadness is undecidable (`dead_undecidable`) and a sound
local collector NEVER reclaims a cross-vat cycle (`crossvat_cycle_leaks`). We connect both
here: the leak is a CONSEQUENCE of soundness, and lease-reclaim is the honest workaround. -/

/-- **`captp_cycle_leak_is_the_price` (PROVED, reuses `Liveness.crossvat_cycle_leaks`).**
The cross-vat reference CYCLE leaks under any sound local-evidence collector: given a
`SoundLocalCollector` and a `CrossVatCycle g a b`, the collector reclaims NEITHER node by
reachability (`collect g a = false ∧ collect g b = false`). Each node pins the other's
refcount ≥ 1 forever, so the only sound local trigger (`refcountZero`) never fires — yet both
cells are genuinely dead. This is precisely WHY CapTP cannot close its §4 GC by proven-death:
no sound vat-local collector can decide the cycle dead. The leak is the PROVED PRICE of
soundness, not a bug — and lease expiry (`captp_gc_by_lease`) is the only honest reclaim. -/
theorem captp_cycle_leak_is_the_price
    (col : SoundLocalCollector) (g : LivenessGraph) (a b : CellId)
    (hcyc : CrossVatCycle g a b) :
    col.collect g a = false ∧ col.collect g b = false :=
  crossvat_cycle_leaks col g a b hcyc

/-- **`captp_death_undecidable_so_lease` (PROVED, reuses `Liveness.dead_undecidable`) — the
deep reason lease-reclaim is forced.** There is NO computable procedure deciding deadness of
the gadget cell across the halting-reduction family: a computable decider would solve the
halting problem. So CapTP distributed GC CANNOT be "decide dead, then reclaim" — that decision
does not exist as an algorithm. Lease expiry (`captp_gc_by_lease`) is not a convenience; it is
the ONLY locally-decidable reclaim trigger available once proven-death is off the table. We
re-expose `Liveness.dead_undecidable` to make the entailment "undecidable ⇒ lease" explicit at
the CapTP layer. -/
theorem captp_death_undecidable_so_lease (n : ℕ) :
    ¬ ∃ d : Nat.Partrec.Code → Bool,
        Computable d ∧
        (∀ c : Nat.Partrec.Code, d c = true ↔ Dead (haltGraph ((Nat.Partrec.Code.eval c n).Dom)) 1) :=
  dead_undecidable n

/-- **`captp_leaked_handle_reclaimed_by_lease` (PROVED, reuses `Liveness.leak_bounded_by_lease`)
— the leak is bounded, not forever.** A leaked cross-vat-cycle node, never reachability-
collected (`captp_cycle_leak_is_the_price`), is STILL reclaimed at the operational `Live` level
once its lease lapses: a dead cycle node past its lease is not `Live`. So an import handle on a
cross-vat cycle leaks not *forever* but only *until its lease expires* — the dregg2-coherent
bound that needs no global view, survives partition, and respects graph privacy. This is the
exact sense in which lease-reclaim CLOSES the §4 OPEN: the leak is real and proved, and the
lease bounds it. -/
theorem captp_leaked_handle_reclaimed_by_lease
    (g : LivenessGraph) (l : Lease) (now : Nat) (a b : CellId)
    (hcyc : CrossVatCycle g a b) (hexp : leaseExpired l now = true) :
    ¬ Live g l now a :=
  leak_bounded_by_lease g l now a b hcyc hexp

/-! ## §4 — Non-vacuity: concrete expired-lease reclaim and renewed-no-reclaim. -/

section NonVacuity

/-- A concrete leased handle: holder cell `0`, exported cap to target `1` with unit rights,
last active at block 100 with a 50-block idle window (lease lapses at 150). -/
def demoLeased : LeasedHandle Nat Unit :=
  { handle := { holder := 0, exported := { target := 1, rights := () } }
  , lease  := leaseOf 100 50 }

/-- At `now = 200` the lease (lapse at 150) has expired, so the handle IS reclaimable —
concrete `captp_gc_by_lease`. -/
example : Reclaimable demoLeased 200 = true :=
  captp_gc_by_lease demoLeased 200 (by decide)

/-- At `now = 120` the lease (lapse at 150) is current, so the handle is NOT reclaimed —
concrete `captp_no_premature_reclaim` (fail-closed while leased). -/
example : Reclaimable demoLeased 120 = false :=
  captp_no_premature_reclaim demoLeased 120 (by decide)

/-- Renewing at `now = 120` with a positive idle window leaves the handle NOT reclaimable at
`120` — concrete `captp_renewed_not_reclaimed` (activity renews the lease). -/
example : Reclaimable (renew demoLeased 120 50) 120 = false :=
  captp_renewed_not_reclaimed demoLeased 120 50 (by decide)

-- Expired lease ⇒ reclaimable; current lease ⇒ not. Locally-decidable, no global view.
#guard (Reclaimable demoLeased 200)  --  expected: true  (200 ≥ 150, lease lapsed)
#guard (Reclaimable demoLeased 120) == false  --  expected: false (120 < 150, lease current)
#guard (Reclaimable (renew demoLeased 120 50) 120) == false  --  expected: false (renewed: lapses at 170)
#guard (s!"demo handle holder={demoLeased.handle.holder}, lease expiresAt={demoLeased.lease.expiresAt}: \
reclaim@200={Reclaimable demoLeased 200}, reclaim@120={Reclaimable demoLeased 120}"
        == "demo handle holder=0, lease expiresAt=150: reclaim@200=true, reclaim@120=false")

end NonVacuity

/-! ## §6 — The REFCOUNT-DROP path (F-11 / F-12): closing the proof's blind spot.

The §1–§4 lease model is one of the TWO reclaim triggers in `gc.rs`. The OTHER is the
**explicit `DropRef` refcount path** (`ExportGcManager::process_drop*`). The red-team found
that the proof was BLIND to it (`_THREAT-MODEL.md` F-11):

  > the Lean `captp_no_premature_reclaim` only models the LEASE path; the refcount-drop path is
  > unmodeled, so this [session-free premature-reclaim] gap is invisible to the proof.

This section MODELS the refcount-drop path faithfully and proves the two safety laws that
catch F-11 (a session-free / wrong-session drop must NOT decrement a victim's refcount) and
F-12 (a drop is scoped to the requesting session's OWN bucket; a re-export under a new session
never transfers another session's drop rights). The model mirrors `gc.rs`'s per-session
`RefCount.sessions : HashMap<SessionId, u64>` and the **mandatory** session check in
`process_drop_inner` (`gc.rs:228`, post-F-11/F-12). Sessions are `Nat`; a holder's per-session
bucket map is a total function `Nat → Nat` (absent bucket = 0), exactly `session_count`
(`gc.rs:70`). -/

section RefcountDrop

/-- **`Buckets`** — a holder's per-session refcount, mirroring `gc.rs`'s
`RefCount.sessions : HashMap<SessionId, u64>`. `b s` is the number of refs minted under session
`s` (an absent HashMap key is `0`). The holder's total `count` is `Σ s, b s` — here we track the
buckets directly and reason about the touched bucket. -/
abbrev Buckets := Nat → Nat

/-- **`mintUnder b s`** — `record_export_with_session` minting one ref under session `s`
(`gc.rs:166`: `*ref_count.sessions.entry(session_id).or_insert(0) += 1`). Adds one to bucket
`s`, leaves every other bucket untouched. -/
def mintUnder (b : Buckets) (s : Nat) : Buckets :=
  fun t => if t = s then b t + 1 else b t

/-- **`dropUnder b s`** — `process_drop_inner` with **mandatory** session `s` (`gc.rs:228`).
The decrement is applied to bucket `s` ONLY, and ONLY if it is positive; a wrong/absent session
(`b s = 0`) authorizes NOTHING and the buckets are returned UNCHANGED (the `Invalid`, no-mutation
branch — `gc.rs:246-248`). This is the post-F-11/F-12 semantics: no session ⇒ no authority. -/
def dropUnder (b : Buckets) (s : Nat) : Buckets :=
  fun t => if t = s then b t - 1 else b t

/-- **`dropAuthorized b s`** — whether a drop carrying session `s` is authorized: the session
must have minted at least one ref on this holder (`gc.rs:247`, `Some(b) if *b > 0`). A
session-free legacy `process_drop` is modeled as a drop carrying a session that minted nothing
(`b s = 0`) — `dropAuthorized` is then `false`, and the runtime takes the `Invalid` no-op branch. -/
def dropAuthorized (b : Buckets) (s : Nat) : Bool :=
  decide (0 < b s)

/-- **`applyDrop b s`** — the FULL `process_drop_inner` transition: decrement bucket `s` iff the
drop is authorized, else leave the buckets untouched. This is the faithful executable semantics
the red-team attacks; the laws below are about THIS function. -/
def applyDrop (b : Buckets) (s : Nat) : Buckets :=
  if dropAuthorized b s then dropUnder b s else b

/-! ### F-11: a session that minted nothing cannot decrement ANY bucket.

The session-free / wrong-session drop is exactly the case `b reqSession = 0`. The law: such a
drop is a NO-OP on every bucket — in particular it cannot drive a victim's bucket toward 0 and
force a premature `CanRevoke`. This is the proof that WOULD HAVE CAUGHT the F-11 finding: the
old session-free `process_drop` decremented regardless, so this law would have been FALSE for
it. -/

/-- **`captp_drop_requires_minting_session` (PROVED) — F-11 safety.**
A DropRef whose session `reqSession` minted no refs on this holder (`b reqSession = 0` — the
session-free legacy path, or any wrong/forged session) leaves the buckets COMPLETELY UNCHANGED.
No bucket is decremented, so no victim ref is reclaimed. Catches F-11: the pre-fix session-free
`process_drop` violated this (it decremented anyway). -/
theorem captp_drop_requires_minting_session (b : Buckets) (reqSession : Nat)
    (hUnauth : b reqSession = 0) :
    applyDrop b reqSession = b := by
  unfold applyDrop dropAuthorized
  simp [hUnauth]

/-- **`captp_unauth_drop_preserves_bucket` (PROVED) — F-11, per-victim form.**
The concrete victim consequence: an unauthorized drop (`b reqSession = 0`) preserves the VICTIM
session's bucket exactly. A victim's still-wanted refs survive a session-free drop attempt —
the premature-reclaim door is shut. -/
theorem captp_unauth_drop_preserves_bucket (b : Buckets) (reqSession victim : Nat)
    (hUnauth : b reqSession = 0) :
    applyDrop b reqSession victim = b victim := by
  rw [captp_drop_requires_minting_session b reqSession hUnauth]

/-! ### F-12: a drop touches ONLY the requesting session's bucket.

Even an AUTHORIZED drop is scoped: it decrements bucket `reqSession` and leaves every OTHER
session's bucket untouched. So a re-export under a new session (which mints into a fresh bucket
via `mintUnder`) can never let the new session drop refs the ORIGINAL session minted, nor strip
the original session's right to drop its own. This is the F-12 per-ref scoping the pre-fix
holder-scoped `session_id` violated. -/

/-- **`captp_drop_scoped_to_session` (PROVED) — F-12 scoping.**
A drop carrying `reqSession` leaves every OTHER session's bucket (`other ≠ reqSession`) exactly
as it was, authorized or not. A session can only ever reach its own bucket. -/
theorem captp_drop_scoped_to_session (b : Buckets) (reqSession other : Nat)
    (hne : other ≠ reqSession) :
    applyDrop b reqSession other = b other := by
  unfold applyDrop dropUnder
  by_cases h : dropAuthorized b reqSession <;> simp [h, hne]

/-- **`captp_reexport_preserves_original_session` (PROVED) — F-12 under re-export.**
A re-export under a NEW session `newS` (minting into `newS`'s bucket) followed by a drop on
that new session leaves the ORIGINAL session `origS`'s bucket UNCHANGED (`origS ≠ newS`). The
original session keeps every ref it minted; the new session's activity cannot touch them. This
is the exact scenario the F-12 red-team test exercises — proven safe. -/
theorem captp_reexport_preserves_original_session
    (b : Buckets) (origS newS : Nat) (hne : origS ≠ newS) :
    applyDrop (mintUnder b newS) newS origS = b origS := by
  rw [captp_drop_scoped_to_session (mintUnder b newS) newS origS hne]
  unfold mintUnder
  simp [hne]

/-- **`captp_authorized_drop_decrements_own_bucket` (PROVED) — liveness companion.**
The dual of the safety laws: an AUTHORIZED drop (the minting session, `0 < b reqSession`) DOES
decrement its OWN bucket by one. The genuine holder retains the ability to drop the refs it
minted — session validation is not vacuously fail-closed (it lets the real holder through). -/
theorem captp_authorized_drop_decrements_own_bucket (b : Buckets) (reqSession : Nat)
    (hAuth : 0 < b reqSession) :
    applyDrop b reqSession reqSession = b reqSession - 1 := by
  unfold applyDrop dropAuthorized dropUnder
  simp [hAuth]

end RefcountDrop

/-! ### §6 non-vacuity — the F-11 attack, replayed in Lean.

A concrete holder with TWO refs under session `10` and ZERO under any other session. A
session-free / wrong-session drop (session `999`, which minted nothing) is a NO-OP; the genuine
session `10` drop decrements; a re-export under session `99` never touches session `10`'s refs. -/

section RefcountNonVacuity

/-- Holder buckets: session `10` minted 2 refs, everything else 0. -/
def demoBuckets : Buckets := fun s => if s = 10 then 2 else 0

/-- F-11: a session-free / wrong-session drop (`999` minted nothing) is a NO-OP — the victim's
session-`10` bucket still holds 2. -/
example : applyDrop demoBuckets 999 10 = 2 :=
  captp_unauth_drop_preserves_bucket demoBuckets 999 10 (by decide)

/-- Liveness: the genuine session-`10` holder CAN drop, decrementing its own bucket to 1. -/
example : applyDrop demoBuckets 10 10 = 1 :=
  captp_authorized_drop_decrements_own_bucket demoBuckets 10 (by decide)

/-- F-12: a re-export under session `99` followed by a `99` drop leaves session `10` at 2. -/
example : applyDrop (mintUnder demoBuckets 99) 99 10 = 2 :=
  captp_reexport_preserves_original_session demoBuckets 10 99 (by decide)

#guard (applyDrop demoBuckets 999 10) == 2   -- F-11: unauth drop is a no-op on the victim
#guard (applyDrop demoBuckets 10 10) == 1    -- authorized drop decrements own bucket
#guard (applyDrop (mintUnder demoBuckets 99) 99 10) == 2  -- F-12: re-export preserves session 10
#guard (mintUnder demoBuckets 99 99) == 1    -- the new session's bucket got exactly its 1 ref

end RefcountNonVacuity

/-! ## §5 — Axiom-hygiene tripwires.

Every PROVED keystone depends ONLY on the three standard kernel axioms (no `sorryAx`). The
cross-vat-cycle leak and deadness-undecidability are REUSED from `Liveness` (themselves
`sorry`-free), so the entailment "undecidable ⇒ lease-reclaim" carries no hidden residue. The
§6 refcount-drop laws (F-11/F-12) are pure arithmetic over the per-session bucket model and
likewise carry no `sorry`. -/

#assert_axioms captp_gc_by_lease
#assert_axioms captp_no_premature_reclaim
#assert_axioms captp_renewed_not_reclaimed
#assert_axioms captp_cycle_leak_is_the_price
#assert_axioms captp_death_undecidable_so_lease
#assert_axioms captp_leaked_handle_reclaimed_by_lease
#assert_axioms captp_drop_requires_minting_session
#assert_axioms captp_unauth_drop_preserves_bucket
#assert_axioms captp_drop_scoped_to_session
#assert_axioms captp_reexport_preserves_original_session
#assert_axioms captp_authorized_drop_decrements_own_bucket

end Dregg2.Exec.CapTPGC
