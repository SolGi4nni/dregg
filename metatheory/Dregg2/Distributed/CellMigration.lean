/-
# Dregg2.Distributed.CellMigration — the EXECUTABLE two-step **atomic cell handoff**
# (Hosted↔Sovereign / cross-federation), with **no-double-existence** + **authority-conservation**
# proved at n > 1.

**The gap this closes.** `Exec/Cell.lean` / `Exec/CellUpgrade.lean` / `Exec/StateMigration.lean`
model a cell's *intra-federation* life: `CellMode` is fixed at construction, `make_sovereign` flips
Hosted↔Sovereign *in one ledger*, and `StateMigration` re-shapes a cell's record on a schema
upgrade. NONE of them MOVES a cell's **home** from one federation (ledger) to another. The
`CellLifecycle.Migrated` tombstone existed in the Rust cell model (`cell/src/lifecycle.rs`) as an
inert terminal variant that *nothing produced*. There was no protocol for relocating a cell across
federations while (a) preserving its identity and authority and (b) preventing the cell from being
*live in two places at once* (double-existence — the on-chain analog of a double-spend, but of a
whole agent).

This module models THAT protocol — the **two-phase atomic handoff** the Rust `cell/src/migration.rs`
+ `cell/src/ledger.rs` (`migrate_prepare` / `migrate_accept` / `migrate_commit`) implement —
following the consensus template (`Distributed/EntangledJoint.lean`,
`Distributed/BlocklaceFinality.lean`): a FAITHFUL, EXECUTABLE Lean model of the real protocol, two
SAFETY properties proved at **n > 1** (≥ 2 federations), a connection to the conserved-quantity
reasoning the verified executor relies on (`recTotalAsset`-style per-cell balance conservation), and
a Rust DIFFERENTIAL (the Lean transitions reproduce the exact `prepare/accept/commit` arc the Rust
ledger walks).

## The protocol (faithful to `cell/src/migration.rs` / `ledger.rs`)

A `World` holds, for each federation `f`, the set of cells that are **live** there
(`Custody f`), plus a global tombstone map (which cells have been COMMIT-finalized as `Migrated`,
to where). The handoff is three transitions on the `World`:

  1. `prepare s d c`  — the SOURCE `s` LOCKS cell `c` (it stays live in `s` but quiescent — a
     `Lock` records the in-flight voucher). PREPARE mints a `Voucher` binding `c`'s identity, its
     EXACT pre-migration `bal`/`caps` (the `state_commitment`), and the `(from, to)` pair. (Rust:
     `Ledger::migrate_prepare`.)
  2. `accept v`       — the DESTINATION `v.to` INSTALLS `c` live, but ONLY if it does not already
     hold it (the no-double-existence gate, Rust: `Ledger::migrate_accept`'s `DestinationOccupied`)
     and the carried `bal`/`caps` match the voucher commitment (authority cannot be inflated in
     transit). It emits a `Receipt`.
  3. `commit r`       — the SOURCE, on the destination's `Receipt`, TOMBSTONES `c` to `Migrated`
     (terminal — it leaves the source's live set and can never re-migrate). (Rust:
     `Cell::migrate_commit` → `CellLifecycle.Migrated`.)

## Safety properties PROVED at n > 1 (single-machine n = 1 is the scales-to-zero special case)

  1. **No-double-existence** (`handoff_unique_home`, `accept_refuses_double` + `liveHomes` is a
     SINGLETON after a committed handoff): after a full `prepare → accept → commit` between TWO
     DISTINCT federations, the migrated cell is live at EXACTLY ONE federation (the destination),
     and the destination's `accept` REFUSES to install a second copy. A cell never has two live
     homes.

  2. **Authority-conservation** (`handoff_conserves_balance` / `handoff_conserves_caps`): the cell's
     balance and capability set at its new home equal those at its old home — the migration neither
     mints nor burns authority. This is the per-cell image of `recTotalAsset` conservation: moving a
     cell's whole authority across the federation boundary is value-neutral.

  3. **Anti-replay / terminality** (`migrated_cannot_reprepare`): a tombstoned cell cannot be
     PREPAREd again, so a committed migration is final (the `is_terminal` gate, Rust:
     `MigrationError::NotMigratable`).

Scope: federations are modelled as an INDEX (`FedId := ℕ`) and custody as a `Finset CellId`
per federation — a faithful PROJECTION of `Ledger`'s `cells`/`sovereign_commitments` maps onto "which
cells are live here." The cell's transferable authority is modelled as `(bal : ℤ, caps : Finset CapId)`
— the conserved quantity (`bal` ↔ `recTotalAsset`/`CellState.balance`; `caps` ↔ the c-list
`CapabilitySet`). The cryptographic `voucher_hash`/`attestation` binding is modelled as STRUCTURAL
equality of the committed `(bal, caps)` (the Rust uses BLAKE3 commitments — a named, standard
collision-resistance assumption stands between the two here: the Lean proves the protocol
LOGIC given that the commitment binds, exactly as `EntangledJoint` proves over `JointId` equality).

Pure, computable, `#eval`/`#guard`-able. No `sorry`, no `native_decide`.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Distributed.CellMigration

/-! ## 1. The carriers: federations, cells, the transferable authority a cell carries. -/

/-- A federation identifier (its genesis/charter hash, modelled as an index). `n > 1` means at
least two DISTINCT `FedId`s. -/
abbrev FedId := Nat

/-- A cell identifier (content-addressed; preserved across the move). -/
abbrev CellId := Nat

/-- A capability identifier (a c-list entry the cell holds). -/
abbrev CapId := Nat

/-- **`Authority`** — the transferable contents of a cell that MUST be conserved across a migration:
its `bal` (the conserved balance, `CellState.balance` / `recTotalAsset` column for this cell) and its
`caps` (the c-list `CapabilitySet`). This is exactly what the Rust voucher's `state_commitment`
binds. -/
structure Authority where
  /-- The conserved balance (signed to mirror `recTotalAsset : … → ℤ`). -/
  bal  : Int
  /-- The capability set (the cell's c-list). -/
  caps : Finset CapId
deriving DecidableEq

/-! ## 2. The voucher / receipt (the PREPARE / ACCEPT artifacts). -/

/-- **`Voucher`** — the PREPARE artifact (`cell/src/migration.rs::MigrationVoucher`). Binds the cell
identity, the EXACT committed authority (the `state_commitment`), and the `(from, to)` federation
pair. Modelled structurally; the Rust binds via a BLAKE3 `voucher_hash` (CR assumption). -/
structure Voucher where
  /-- The cell being relocated. -/
  cell   : CellId
  /-- The authority committed at PREPARE (the `state_commitment` contents). -/
  auth   : Authority
  /-- The source federation that locked the cell. -/
  «from» : FedId
  /-- The destination federation taking custody. -/
  «to»   : FedId
deriving DecidableEq

/-- **`Receipt`** — the ACCEPT attestation (`MigrationReceipt`): the voucher accepted + who accepted.
-/
structure Receipt where
  /-- The voucher this receipt accepts (echoing its `voucher_hash`, here structural equality). -/
  voucher    : Voucher
  /-- The destination federation that installed the cell. -/
  acceptedBy : FedId
deriving DecidableEq

/-! ## 3. The world: per-federation custody + the in-flight locks + the tombstones. -/

/-- **`World`** — the global custody state across federations.

  * `live f`   — the set of cells LIVE at federation `f` (`Ledger.cells ∪ sovereign_commitments`,
    projected to "is this cell hosted here"). A cell's HOME is the `f` with `c ∈ live f`.
  * `authAt f c` — the authority a cell `c` carries at federation `f` (its `bal`/`caps` there).
  * `locked`   — the cells with an in-flight migration (PREPAREd, not yet COMMITted): quiescent.
  * `tombstone f c`— the destination cell `c` was COMMIT-finalized as `Migrated` *away from
    federation `f`* (the `CellLifecycle.Migrated.to` recorded in `f`'s ledger). Keyed by
    `(f, c)`: a tombstone at the SOURCE `f` does NOT brick the cell at its new home — only `f` sees
    it as terminal. This mirrors the Rust per-ledger `Cell::lifecycle` (the source ledger's copy
    becomes `Migrated`, the destination's copy stays `Live`). A cell cannot re-migrate AWAY from a
    federation where it is tombstoned. -/
structure World where
  /-- Cells live at each federation. -/
  live      : FedId → Finset CellId
  /-- The authority a cell carries at a federation (only meaningful where the cell is live). -/
  authAt    : FedId → CellId → Authority
  /-- Cells with an in-flight (PREPAREd-not-COMMITted) migration. -/
  locked    : Finset CellId
  /-- Per-(federation, cell) `Migrated` tombstone, recording the destination the cell went to. -/
  tombstone : FedId → CellId → Option FedId

/-- A cell is **live** at federation `f` in world `w`. -/
def liveAt (w : World) (f : FedId) (c : CellId) : Prop := c ∈ w.live f

/-- A cell is **terminal at federation `f`** (tombstoned `Migrated` there) in `w` — it cannot be
migrated again AWAY from `f`. -/
def isTerminal (w : World) (f : FedId) (c : CellId) : Prop := (w.tombstone f c).isSome

/-- The set of federations (within a given index bound `N`) where cell `c` is live — its "homes".
We bound the search by `N` (the federation count) to keep `liveHomes` a `Finset`; this is the
faithful projection (`Ledger` has finitely many federations). -/
def liveHomes (w : World) (N : Nat) (c : CellId) : Finset FedId :=
  (Finset.range N).filter (fun f => c ∈ w.live f)

/-! ## 4. The three transitions (the two-step handoff: PREPARE → ACCEPT → COMMIT). -/

/-- **PREPARE** (`Ledger::migrate_prepare`). Source `s` mints a voucher to send `c` to `d` and
records a lock. Defined as a partial transition: it PRODUCES `(some (voucher, w'))` iff `c` is live
at `s`, not already locked, and not terminal; else `none` (rejected). The world is unchanged except
`c` joins `locked` (the cell stays live in `s` but quiescent). -/
def prepare (w : World) (s d : FedId) (c : CellId) : Option (Voucher × World) :=
  if c ∈ w.live s ∧ c ∉ w.locked ∧ (w.tombstone s c) = none then
    let v : Voucher := { cell := c, auth := w.authAt s c, «from» := s, «to» := d }
    let w' : World :=
      { w with locked := insert c w.locked }
    some (v, w')
  else
    none

/-- **ACCEPT** (`Ledger::migrate_accept`). Destination `v.to` installs the cell live with the
voucher's committed authority — but ONLY if it does not ALREADY hold the cell (the no-double-
existence gate, Rust `DestinationOccupied`). Produces `(some (receipt, w'))` on success, else `none`.
The carried authority is exactly `v.auth` (the commitment binds it — no inflation in transit). -/
def accept (w : World) (v : Voucher) : Option (Receipt × World) :=
  if v.cell ∉ w.live v.to then
    let w' : World :=
      { w with
        live   := fun f => if f = v.to then insert v.cell (w.live f) else w.live f
        authAt := fun f c => if f = v.to ∧ c = v.cell then v.auth else w.authAt f c }
    some ({ voucher := v, acceptedBy := v.to }, w')
  else
    none  -- destination already holds the cell — refuse (no double-existence)

/-- **COMMIT** (`Cell::migrate_commit` → `CellLifecycle.Migrated`). Source `r.voucher.from`
tombstones the cell: it LEAVES the source's live set, the lock is cleared, and a terminal tombstone
to `r.voucher.to` is recorded. Produces `(some w')` iff the cell is currently locked (a migration is
in flight) and the receipt's voucher targets this source; else `none`. -/
def commit (w : World) (r : Receipt) : Option World :=
  let s := r.voucher.«from»
  let c := r.voucher.cell
  if c ∈ w.locked ∧ c ∈ w.live s ∧ r.acceptedBy = r.voucher.«to» then
    some
      { w with
        live      := fun f => if f = s then (w.live f).erase c else w.live f
        locked    := w.locked.erase c
        tombstone := fun f x => if f = s ∧ x = c then some r.voucher.«to» else w.tombstone f x }
  else
    none

/-- **`handoff`** — the full atomic arc: PREPARE at `s` → ACCEPT at `d` → COMMIT back at `s`. Returns
the final world iff every step commits (the all-or-none face of the 2-phase handoff). -/
def handoff (w : World) (s d : FedId) (c : CellId) : Option World := do
  let (v, w1) ← prepare w s d c
  let (r, w2) ← accept w1 v
  commit w2 r

/-! ## 5. KEYSTONE 1 — no-double-existence. -/

/-- **`accept_refuses_double`.** ACCEPT refuses to install a cell the destination already
holds — the core no-double-existence gate. If `v.cell` is already live at `v.to`, `accept` is `none`.
-/
theorem accept_refuses_double (w : World) (v : Voucher)
    (hlive : v.cell ∈ w.live v.to) :
    accept w v = none := by
  unfold accept
  rw [if_neg (by simpa using hlive)]

/-- After ACCEPT, the cell is live at the destination. -/
theorem accept_installs (w : World) (v : Voucher) (r : Receipt) (w' : World)
    (hok : accept w v = some (r, w')) :
    v.cell ∈ w'.live v.to := by
  unfold accept at hok
  by_cases h : v.cell ∉ w.live v.to
  · rw [if_pos h] at hok
    obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hok)
    simp
  · rw [if_neg h] at hok; exact absurd hok (by simp)

/-- After COMMIT, the cell is NOT live at the source (it left the source's live set). -/
theorem commit_removes_source (w : World) (r : Receipt) (w' : World)
    (hok : commit w r = some w') :
    r.voucher.cell ∉ w'.live r.voucher.«from» := by
  unfold commit at hok
  by_cases h : r.voucher.cell ∈ w.locked ∧ r.voucher.cell ∈ w.live r.voucher.«from»
        ∧ r.acceptedBy = r.voucher.«to»
  · rw [if_pos h] at hok
    rw [← Option.some.inj hok]
    simp
  · rw [if_neg h] at hok; exact absurd hok (by simp)

/-- After COMMIT, the cell is tombstoned (terminal) at the SOURCE federation. -/
theorem commit_tombstones (w : World) (r : Receipt) (w' : World)
    (hok : commit w r = some w') :
    isTerminal w' r.voucher.«from» r.voucher.cell := by
  unfold commit at hok
  by_cases h : r.voucher.cell ∈ w.locked ∧ r.voucher.cell ∈ w.live r.voucher.«from»
        ∧ r.acceptedBy = r.voucher.«to»
  · rw [if_pos h] at hok
    rw [← Option.some.inj hok]
    unfold isTerminal
    simp
  · rw [if_neg h] at hok; exact absurd hok (by simp)

/-- **`handoffWorld`** — the EXPLICIT final world a successful `handoff w s d c` produces (with
`s ≠ d`). The cell is inserted live at `d` (carrying the voucher's `auth = authAt s c`), erased from
`s`, and the source's tombstone records the destination. Every keystone reads its conclusion off this
one canonical post-state. -/
def handoffWorld (w : World) (s d : FedId) (c : CellId) : World :=
  let a := w.authAt s c
  -- `liveAccept` is the post-ACCEPT live map (insert `c` at the destination `d`); `handoffWorld`
  -- then applies the post-COMMIT source-erase on top of it. Written as this literal composition so
  -- `handoff_eq`'s final commit step closes definitionally.
  let liveAccept : FedId → Finset CellId := fun f => if f = d then insert c (w.live f) else w.live f
  { live      := fun f => if f = s then (liveAccept f).erase c else liveAccept f
    authAt    := fun f cc => if f = d ∧ cc = c then a else w.authAt f cc
    locked    := (insert c w.locked).erase c
    tombstone := fun f x => if f = s ∧ x = c then some d else w.tombstone f x }

/-- **`handoff_eq`.** Under the n > 1 preconditions (`s ≠ d`, cell live only at `s`, not
locked, not terminal at `s`), the full `prepare → accept → commit` arc reduces to exactly
`handoffWorld`. The single reduction lemma every keystone builds on. -/
theorem handoff_eq (w : World) (s d : FedId) (c : CellId)
    (hsd : s ≠ d)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none) :
    handoff w s d c = some (handoffWorld w s d c) := by
  have hprep : prepare w s d c
      = some ({ cell := c, auth := w.authAt s c, «from» := s, «to» := d },
              { w with locked := insert c w.locked }) := by
    unfold prepare; rw [if_pos ⟨hs, hlk, htomb⟩]
  set v : Voucher := { cell := c, auth := w.authAt s c, «from» := s, «to» := d } with hv
  set w1 : World := { w with locked := insert c w.locked } with hw1
  have hd1 : v.cell ∉ w1.live v.to := by simpa [hv, hw1] using hd
  have hacc : accept w1 v = some ({ voucher := v, acceptedBy := v.to },
      { w1 with
        live   := fun f => if f = d then insert c (w1.live f) else w1.live f
        authAt := fun f cc => if f = d ∧ cc = c then v.auth else w1.authAt f cc }) := by
    unfold accept; rw [if_pos hd1]
  set w2 : World :=
    { w1 with
      live   := fun f => if f = d then insert c (w1.live f) else w1.live f
      authAt := fun f cc => if f = d ∧ cc = c then v.auth else w1.authAt f cc } with hw2
  have hc_lives : c ∈ w2.live s := by
    simp only [hw2]; rw [if_neg hsd]; simpa [hw1] using hs
  have hclock : c ∈ w2.locked := by simp [hw2, hw1]
  have hcom : commit w2 ({ voucher := v, acceptedBy := v.to } : Receipt)
      = some (handoffWorld w s d c) := by
    unfold commit handoffWorld
    -- `w2.live = liveAccept` and `w2.{authAt,locked,tombstone}` match `handoffWorld`'s fields by
    -- construction, so after the guard fires the two record literals are definitionally equal.
    rw [if_pos ⟨hclock, hc_lives, rfl⟩]
  -- Assemble the do-block by reducing each `some _ >>= f`.
  show (prepare w s d c) >>= (fun p => (accept p.2 p.1) >>= fun r => commit r.2 r.1) = _
  rw [hprep]
  show (accept w1 v) >>= (fun r => commit r.2 r.1) = _
  rw [hacc]
  exact hcom

/-- **`handoff_unique_home` (the n > 1 no-double-existence keystone).** After a full
`prepare → accept → commit` handoff of cell `c` between two DISTINCT federations `s ≠ d`, starting
from a world where `c` was live ONLY at `s` (a single home), the cell is live at the DESTINATION `d`
and NOT at the source `s`. So the migrated cell has exactly one live home — it never doubles.

The hypotheses are the honest n > 1 preconditions: `s ≠ d` (two distinct federations), `c` live at
`s`, `c` not already at `d`, `c` not locked, `c` not terminal at `s`. -/
theorem handoff_unique_home (w : World) (s d : FedId) (c : CellId)
    (hsd : s ≠ d)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none) :
    ∃ w', handoff w s d c = some w' ∧ c ∈ w'.live d ∧ c ∉ w'.live s := by
  refine ⟨handoffWorld w s d c, handoff_eq w s d c hsd hs hd hlk htomb, ?_, ?_⟩
  · -- live at `d`: the `f = d` insert-branch fires (and `d ≠ s` skips the erase).
    simp [handoffWorld, Ne.symm hsd]
  · -- NOT live at `s`: the `f = s` erase-branch fires; `c ∉ (·).erase c`.
    simp [handoffWorld, Finset.mem_erase]

/-- The handoff leaves `c`'s liveness UNCHANGED at every federation other than `s` and `d`. -/
theorem handoffWorld_live_other (w : World) (s d : FedId) (c : CellId)
    (f : FedId) (hfs : f ≠ s) (hfd : f ≠ d) :
    c ∈ (handoffWorld w s d c).live f ↔ c ∈ w.live f := by
  simp only [handoffWorld]
  rw [if_neg hfs, if_neg hfd]

/-- **`handoff_singleton_home`.** Strengthening of `handoff_unique_home` to the `liveHomes`
SINGLETON statement: if, additionally, `s` and `d` are the ONLY federations within the index bound
`N` where `c` could be live (everywhere else `c` was absent and stays absent — the handoff touches
only `s` and `d`), then after the handoff `c`'s live-home set is the SINGLETON `{d}`. -/
theorem handoff_singleton_home (w : World) (s d : FedId) (c : CellId) (N : Nat)
    (hsd : s ≠ d) (hsN : s < N) (hdN : d < N)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none)
    (honly : ∀ f, f < N → f ≠ d → f ≠ s → c ∉ w.live f) :
    ∃ w', handoff w s d c = some w' ∧ liveHomes w' N c = {d} := by
  obtain ⟨w', hh, hd', hs'⟩ := handoff_unique_home w s d c hsd hs hd hlk htomb
  have hweq : w' = handoffWorld w s d c := by
    rw [handoff_eq w s d c hsd hs hd hlk htomb] at hh; exact (Option.some.inj hh).symm
  refine ⟨w', hh, ?_⟩
  ext f
  simp only [liveHomes, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hfN, hflive⟩
    by_contra hfd
    by_cases hfs : f = s
    · subst hfs; exact hs' hflive
    · rw [hweq, handoffWorld_live_other w s d c f hfs hfd] at hflive
      exact (honly f hfN hfd hfs) hflive
  · rintro rfl; exact ⟨hdN, hd'⟩

/-! ## 6. KEYSTONE 2 — authority-conservation. -/

/-- **`handoff_full_auth`.** The single fact behind both conservation keystones: after a
handoff, the cell's FULL authority (`bal` AND `caps`) at its new home `d` equals its authority at its
old home `s` before the move. The destination installs exactly the voucher's committed `auth =
authAt s c`, and the source-erase at COMMIT does not touch `authAt`. -/
theorem handoff_full_auth (w : World) (s d : FedId) (c : CellId)
    (hsd : s ≠ d)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none) :
    ∃ w', handoff w s d c = some w' ∧ w'.authAt d c = w.authAt s c := by
  refine ⟨handoffWorld w s d c, handoff_eq w s d c hsd hs hd hlk htomb, ?_⟩
  simp [handoffWorld]

/-- **`handoff_conserves_balance` (the n > 1 authority-conservation keystone).** The cell's
balance at its NEW home `d` equals its balance at its OLD home `s` before the move. Migration neither
mints nor burns balance — the per-cell image of `recTotalAsset` conservation. -/
theorem handoff_conserves_balance (w : World) (s d : FedId) (c : CellId)
    (hsd : s ≠ d)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none) :
    ∃ w', handoff w s d c = some w' ∧ (w'.authAt d c).bal = (w.authAt s c).bal := by
  obtain ⟨w', hh, hauth⟩ := handoff_full_auth w s d c hsd hs hd hlk htomb
  exact ⟨w', hh, by rw [hauth]⟩

/-- **`handoff_conserves_caps`.** The capability set (c-list) is likewise conserved across
the move: `w'.authAt d c |>.caps = w.authAt s c |>.caps`. Authority (capabilities) is neither forged
nor dropped by migration. -/
theorem handoff_conserves_caps (w : World) (s d : FedId) (c : CellId)
    (hsd : s ≠ d)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none) :
    ∃ w', handoff w s d c = some w' ∧ (w'.authAt d c).caps = (w.authAt s c).caps := by
  obtain ⟨w', hh, hauth⟩ := handoff_full_auth w s d c hsd hs hd hlk htomb
  exact ⟨w', hh, by rw [hauth]⟩

/-! ## 7. KEYSTONE 3 — anti-replay / terminality. -/

/-- **`migrated_cannot_reprepare`.** A tombstoned (already-migrated) cell cannot be
PREPAREd again: `prepare` returns `none`. A committed migration is final — the cell cannot fork off
a second handoff from its old home. -/
theorem migrated_cannot_reprepare (w : World) (s d : FedId) (c : CellId)
    (hterm : isTerminal w s c) :
    prepare w s d c = none := by
  unfold prepare
  rw [if_neg]
  rintro ⟨_, _, htomb⟩
  unfold isTerminal at hterm
  rw [htomb] at hterm
  simp at hterm

/-! ## 8. Connection to the verified executor (conserved-quantity bridge).

Authority-conservation above is the per-cell image of the kernel's global balance conservation: a
migration moves a cell's `bal` from federation `s`'s column to federation `d`'s column, changing NO
total. We state the cross-federation aggregate that mirrors `recTotalAsset`: the sum of a cell's
balance over its live homes is invariant under the handoff (it was `bal` at `s`, it is `bal` at `d`).
-/

/-- A cell's balance summed over its live homes within bound `N`. Mirrors `recTotalAsset` (a sum over
the live index set). For a uniquely-homed cell this is just its single home's balance. -/
def aggBalance (w : World) (N : Nat) (c : CellId) : Int :=
  ∑ f ∈ liveHomes w N c, (w.authAt f c).bal

/-- **`handoff_aggBalance_conserved`.** Under the singleton-home hypotheses, the cell's
aggregate balance over its live homes is the SAME before (`= bal at s`) and after (`= bal at d`) the
handoff — and those are equal by `handoff_conserves_balance`. The conserved-quantity bridge to the
executor: migrating a cell is balance-neutral at the federation-aggregate level. -/
theorem handoff_aggBalance_conserved (w : World) (s d : FedId) (c : CellId) (N : Nat)
    (hsd : s ≠ d) (hsN : s < N) (hdN : d < N)
    (hs : c ∈ w.live s) (hd : c ∉ w.live d)
    (hlk : c ∉ w.locked) (htomb : w.tombstone s c = none)
    (honly : ∀ f, f < N → f ≠ d → f ≠ s → c ∉ w.live f)
    (hsrc_only : ∀ f, f < N → f ≠ s → c ∉ w.live f) :
    ∃ w', handoff w s d c = some w' ∧
      aggBalance w' N c = aggBalance w N c := by
  obtain ⟨w', hh, hsingle⟩ := handoff_singleton_home w s d c N hsd hsN hdN hs hd hlk htomb honly
  obtain ⟨w'2, hh2, hbal⟩ := handoff_conserves_balance w s d c hsd hs hd hlk htomb
  have hww : w' = w'2 := by rw [hh] at hh2; exact (Option.some.injEq _ _).mp hh2
  subst hww
  refine ⟨w', hh, ?_⟩
  unfold aggBalance
  -- After: liveHomes = {d} ⇒ sum is `authAt d c |>.bal`.
  rw [hsingle, Finset.sum_singleton]
  -- Before: liveHomes = {s} (the cell was live ONLY at s) ⇒ sum is `authAt s c |>.bal`.
  have hbefore : liveHomes w N c = {s} := by
    ext f
    simp only [liveHomes, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hfN, hflive⟩
      by_contra hfs
      exact (hsrc_only f hfN hfs) hflive
    · rintro rfl; exact ⟨hsN, hs⟩
  rw [hbefore, Finset.sum_singleton, hbal]

/-! ## 9. Axiom-hygiene tripwires (`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms accept_refuses_double
#assert_axioms accept_installs
#assert_axioms commit_removes_source
#assert_axioms commit_tombstones
#assert_axioms handoff_unique_home
#assert_axioms handoff_singleton_home
#assert_axioms handoff_conserves_balance
#assert_axioms handoff_conserves_caps
#assert_axioms migrated_cannot_reprepare
#assert_axioms handoff_aggBalance_conserved

/-! ## 10. It runs (`#guard`) + the Rust DIFFERENTIAL.

A concrete n = 3 world: cell `100` lives at federation `0` with balance `500` and caps `{1,2}`;
federations `1` and `2` are empty. We migrate `100` from `0` to `1` and check the Lean transitions
reproduce the EXACT `prepare/accept/commit` arc of `cell/src/migration.rs` +
`cell/src/ledger.rs::{migrate_prepare, migrate_accept, migrate_commit}`. -/

/-- The n = 3 starting world. -/
def w0 : World :=
  { live      := fun f => if f = 0 then {100} else ∅
    authAt    := fun _ _ => { bal := 500, caps := {1, 2} }
    locked    := ∅
    tombstone := fun _ _ => none }

-- n > 1: three federations, cell live at exactly one (federation 0).
#guard (decide (100 ∈ w0.live 0))
#guard (decide (100 ∉ w0.live 1))
#guard (liveHomes w0 3 100 = {0})

-- PREPARE: source 0 locks the cell, mints a voucher binding bal=500, caps={1,2}.
#guard ((prepare w0 0 1 100).map (fun p => p.1.auth.bal)) == some 500
#guard ((prepare w0 0 1 100).map (fun p => p.1.«to»)) == some 1
#guard ((prepare w0 0 1 100).map (fun p => decide (100 ∈ p.2.locked))) == some true

-- Full handoff 0 → 1 commits, and the cell ends up live at EXACTLY federation 1.
#guard (handoff w0 0 1 100).isSome
#guard ((handoff w0 0 1 100).map (fun w => liveHomes w 3 100)) == some {1}
-- No-double-existence: NOT live at source 0 after commit.
#guard ((handoff w0 0 1 100).map (fun w => decide (100 ∈ w.live 0))) == some false
-- Authority-conservation: balance 500 carried to the new home.
#guard ((handoff w0 0 1 100).map (fun w => (w.authAt 1 100).bal)) == some 500
#guard ((handoff w0 0 1 100).map (fun w => (w.authAt 1 100).caps)) == some ({1, 2} : Finset CapId)
-- Terminality (per-federation): the migrated cell is tombstoned AT THE SOURCE 0, to federation 1;
-- the destination 1 sees NO tombstone (its copy is Live, can re-migrate onward).
#guard ((handoff w0 0 1 100).map (fun w => w.tombstone 0 100)) == some (some 1)
#guard ((handoff w0 0 1 100).map (fun w => w.tombstone 1 100)) == some none
-- Anti-replay: a re-prepare from the OLD home 0 is refused (tombstoned there + not live there).
#guard ((handoff w0 0 1 100).map (fun w => (prepare w 0 2 100).isNone)) == some true
-- ...but the NEW home 1 CAN prepare an onward migration (the destination copy is Live).
#guard ((handoff w0 0 1 100).map (fun w => (prepare w 1 2 100).isSome)) == some true

-- DIFFERENTIAL (no-double-existence gate): accept at a destination that ALREADY holds the cell is
-- refused — mirrors Rust `MigrationError::DestinationOccupied`.
#guard (accept w0 { cell := 100, auth := { bal := 0, caps := ∅ }, «from» := 1, «to» := 0 }).isNone

-- Onward migration 1 → 2 after the first handoff: still exactly one home, balance still conserved.
#guard ((handoff w0 0 1 100).bind (fun w => handoff w 1 2 100)).isSome
#guard (((handoff w0 0 1 100).bind (fun w => handoff w 1 2 100)).map
          (fun w => liveHomes w 3 100)) == some {2}
#guard (((handoff w0 0 1 100).bind (fun w => handoff w 1 2 100)).map
          (fun w => (w.authAt 2 100).bal)) == some 500

end Dregg2.Distributed.CellMigration
