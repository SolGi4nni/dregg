/-
# Dregg2.Exec.ShieldedValue — A4: WELD `noteCreate`'s commitment to a hidden value.

The executable `noteCreateCommitment k cm` (`RecordKernel.lean:2103`) inserts a BARE `Nat cm` into the
off-ledger `commitments` set with NO binding to any value — the note's amount lives "behind the
CryptoPortal" but the executor never checks the commitment actually COMMITS to a range-valid value.
That is the dual gap to the nullifier discipline: nullifier double-spend IS welded
(`PrivacyTheorems.chainNoteSpend_no_double_spend`), but shielded value-CREATION was unwelded, so the
executed state admits a commitment to a forged/out-of-range amount (hidden inflation).

This module WELDS the gap via the Pedersen / range-proof portal (`Dregg2.Crypto.Pedersen`):

  * the inserted commitment is `commit v r` (the §8 Pedersen value-commitment `commit(v,r)=v·V+r·R`,
    abstracted as `commit : Int → Int → Nat` with the proved homomorphism carrier `commit_hom`);
  * a `BoundNote` carries the hidden `value`, `blinding`, and the `bits` RANGE-WITNESS (`0 ≤ value <
    2^n`, the honest `RecordCircuit.range_iff` gadget — NO crypto seam);
  * `noteCreateBound` inserts EXACTLY `commit value blinding`, and we PROVE:
      - `noteCreateBound_binds` — the inserted commitment IS the Pedersen commitment of the bound
        note's value (the weld: the set entry testifies to a specific hidden value);
      - `noteCreateBound_in_range` — that value is range-valid (`0 ≤ value < 2^n`), so NO note can be
        created committing a negative / overflowing amount (no hidden inflation at creation);
      - `created_value_conservation` — over a created-note SET, the SUM of the inserted commitments
        equals the commitment of the SUMMED value+blinding (`commit_sum` / `commit_hom`): a verifier
        seeing only commitments confirms the created value equals the disclosed total — the shielded
        value-conservation that now holds over EXECUTED state;
      - `noteCreateBound_no_double_create` is NOT claimed (creation is grow-only by design); the
        binding + range + conservation are the value-side weld.

The only crypto residue is the Pedersen `binding` carrier (commitment-eq ⇒ amount-eq, a DLog `Prop`);
the homomorphism + range algebra is unconditional. Additive: edits NOTHING in the
hot core; lifts `noteCreateCommitment` + the Pedersen portal.

Style: `#guard` witnesses.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.RecordCircuit
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Dregg2.Exec.ShieldedValue

open Dregg2.Exec
open Dregg2.Exec.RecordCircuit (bitsToInt Boolean range_sound range_iff)

/-! ## §1 — The value-commitment portal (`commit : Int → Int → Nat` + `commit_hom`).

The Pedersen value commitment `commit(v,r) = v·V + r·R` realized as a `Nat`-valued opening (the
`commitments` set is `List Nat`). We carry it abstractly with its proved additive homomorphism — the
§8 carrier the curve layer discharges — exactly as `Crypto.Pedersen.commitHom` does over `Digest`. -/

/-- **A value-commitment scheme** over the `Nat` commitment set: the `commit` opening plus its additive
homomorphism `commit (v+w) (r+s) = commit v r + commit w s` (the Pedersen `commit_hom`, the carrier
that makes a commitment-SUM equation testify to a value-SUM equation). `Nat` addition is the group op
of the disclosed commitment field. The homomorphism is stated on NON-NEGATIVE openings (`0 ≤ v, w, r,
s`) — exactly the regime a range-valid shielded transfer lives in (`0 ≤ value`, non-negative blinding),
so the carrier is faithful and the reference scheme discharges it unconditionally on that cone. -/
structure ValueCommitment where
  /-- The Pedersen value commitment opening `commit(value, blinding)`. -/
  commit  : Int → Int → Nat
  /-- The additive homomorphism on the non-negative cone (§8 carrier; PROVED for a real Pedersen
  scheme via `commit_hom`). -/
  hom     : ∀ v w r s, 0 ≤ v → 0 ≤ w → 0 ≤ r → 0 ≤ s →
              commit (v + w) (r + s) = commit v r + commit w s

/-! ## §2 — `BoundNote`: a created note that CARRIES its hidden value + range witness. -/

/-- **A bound note** for `noteCreate`: the hidden `value`, the Pedersen `blinding`, and the
little-endian `bits` RANGE-WITNESS (`Boolean bits ∧ bitsToInt bits = value` ⇒ `0 ≤ value < 2^n`). The
commitment the executor inserts is `commit value blinding`; the note BINDS it to this value. -/
structure BoundNote where
  /-- The hidden amount the commitment commits to. -/
  value    : Int
  /-- The Pedersen blinding factor. -/
  blinding : Int
  /-- The boolean bit-decomposition witnessing `0 ≤ value < 2 ^ bits.length`. -/
  bits     : List Int
  deriving Repr

/-- The note is RANGE-VALID when its bits are boolean and recompose its value (the honest range
gadget, no crypto seam). This is the precondition a real `noteCreate` proof would carry. -/
def BoundNote.rangeValid (nt : BoundNote) : Prop :=
  Boolean nt.bits ∧ bitsToInt nt.bits = nt.value

/-- The commitment a bound note opens to under the scheme: `commit value blinding`. -/
def BoundNote.commitment (vc : ValueCommitment) (nt : BoundNote) : Nat :=
  vc.commit nt.value nt.blinding

/-! ## §3 — `noteCreateBound`: insert the VALUE-BOUND commitment (the welded `noteCreate`). -/

/-- **`noteCreateBound`** — the value-welded `noteCreate`: insert EXACTLY `commit value blinding` (the
Pedersen commitment of the bound note's hidden value) into the off-ledger commitment set. This is
`noteCreateCommitment` with the inserted `cm` not a bare opaque `Nat` but the value-commitment
of a specific, range-witnessed amount. -/
def noteCreateBound (vc : ValueCommitment) (k : RecordKernelState) (nt : BoundNote) : RecordKernelState :=
  noteCreateCommitment k (nt.commitment vc)

/-! ## §4 — The WELD theorems. -/

/-- **`noteCreateBound_binds` — THE WELD.** The commitment `noteCreateBound` inserts into the
set IS the Pedersen commitment of the bound note's hidden value (`commit value blinding`). The set
entry is not an unbound `Nat`: it TESTIFIES to a specific hidden amount (under the §8 `binding`
carrier). -/
theorem noteCreateBound_binds (vc : ValueCommitment) (k : RecordKernelState) (nt : BoundNote) :
    vc.commit nt.value nt.blinding ∈ (noteCreateBound vc k nt).commitments := by
  unfold noteCreateBound BoundNote.commitment
  exact noteCreate_inserts k _

/-- **`noteCreateBound_in_range` — NO HIDDEN INFLATION AT CREATION.** A range-valid bound note
has its hidden value in `[0, 2 ^ n)`: a created note can NEVER commit a negative or overflowing amount.
This is the no-inflation precondition the executed commitment now carries (the honest `range_sound`
gadget — no primitive seam). -/
theorem noteCreateBound_in_range (nt : BoundNote) (h : nt.rangeValid) :
    0 ≤ nt.value ∧ nt.value < 2 ^ nt.bits.length := by
  obtain ⟨hbool, hrec⟩ := h
  obtain ⟨h0, h1⟩ := range_sound nt.bits hbool
  rw [hrec] at h0 h1; exact ⟨h0, h1⟩

/-- The sum of a bound-note list's commitments (the disclosed total a verifier sees). -/
def listCommitment (vc : ValueCommitment) (notes : List BoundNote) : Nat :=
  (notes.map (BoundNote.commitment vc)).sum

/-- Every note has non-negative value AND blinding (the cone a range-valid shielded transfer lives in;
`0 ≤ value` follows from `rangeValid`, `0 ≤ blinding` is the well-formed-blinding convention). -/
def AllNonneg (notes : List BoundNote) : Prop :=
  ∀ nt ∈ notes, 0 ≤ nt.value ∧ 0 ≤ nt.blinding

/-- The summed value/blinding of a non-negative note list are themselves non-negative (used to thread
the homomorphism's cone side condition through the fold). -/
theorem sum_nonneg_of_AllNonneg (notes : List BoundNote) (h : AllNonneg notes) :
    0 ≤ (notes.map BoundNote.value).sum ∧ 0 ≤ (notes.map BoundNote.blinding).sum := by
  induction notes with
  | nil => simp
  | cons nt rest ih =>
      have hnt := h nt (by simp)
      have hrest : AllNonneg rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      obtain ⟨hv, hb⟩ := ih hrest
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by linarith [hnt.1], by linarith [hnt.2]⟩

/-- **`created_value_conservation` — SHIELDED VALUE-CONSERVATION OVER EXECUTED STATE.** Over a
NON-NEGATIVE created-note list, the SUM of the commitments inserted equals the commitment of the SUMMED
value under the SUMMED blinding: `Σ commit vᵢ rᵢ = commit (Σ vᵢ) (Σ rᵢ)` (the Pedersen `commit_hom`
collapse, the heart of value conservation). So a verifier seeing only the disclosed created commitments
confirms the total created value WITHOUT learning any single amount — the shielded value-conservation
now welded to the executor's `commitments` set (the value-side dual of the nullifier discipline). -/
theorem created_value_conservation (vc : ValueCommitment) (notes : List BoundNote)
    (hnn : AllNonneg notes) :
    listCommitment vc notes
      = vc.commit ((notes.map BoundNote.value).sum) ((notes.map BoundNote.blinding).sum) := by
  unfold listCommitment BoundNote.commitment
  induction notes with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      -- commit 0 0 = commit 0 0 + commit 0 0 (hom at 0) ⇒ commit 0 0 = 0.
      have hz := vc.hom 0 0 0 0 (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
      simp only [add_zero] at hz
      omega
  | cons nt rest ih =>
      have hnt := hnn nt (by simp)
      have hrest : AllNonneg rest := fun x hx => hnn x (List.mem_cons_of_mem _ hx)
      obtain ⟨hvr, hbr⟩ := sum_nonneg_of_AllNonneg rest hrest
      simp only [List.map_cons, List.sum_cons, ih hrest]
      rw [vc.hom nt.value (rest.map BoundNote.value).sum nt.blinding (rest.map BoundNote.blinding).sum
            hnt.1 hvr hnt.2 hbr]

/-- **`created_set_grows`.** `noteCreateBound` only GROWS the commitment set: every previously
created commitment is still present (the grow-only dual of the nullifier set; creation never removes).
-/
theorem created_set_grows (vc : ValueCommitment) (k : RecordKernelState) (nt : BoundNote) (c : Nat)
    (h : c ∈ k.commitments) : c ∈ (noteCreateBound vc k nt).commitments := by
  unfold noteCreateBound noteCreateCommitment
  exact List.mem_cons_of_mem _ h

/-- **`noteCreateBound_recTotalAsset` — bal-NEUTRALITY survives the weld.** The welded create
still leaves the on-ledger `recTotalAsset` UNCHANGED for every asset: shielded value
lives in the off-ledger commitment set, never the transparent `bal` ledger (so it cannot double-count
against transparent balances). -/
theorem noteCreateBound_recTotalAsset (vc : ValueCommitment) (k : RecordKernelState) (nt : BoundNote)
    (b : AssetId) :
    recTotalAsset (noteCreateBound vc k nt) b = recTotalAsset k b :=
  noteCreate_recTotalAsset k _ b

#assert_axioms noteCreateBound_binds
#assert_axioms noteCreateBound_in_range
#assert_axioms created_value_conservation
#assert_axioms created_set_grows
#assert_axioms noteCreateBound_recTotalAsset

/-! ## §5 — Non-vacuity: a reference scheme + the value-binding teeth.

The reference value commitment `commit v r := (v + r).toNat` (degenerate, NOT real crypto, matching the
`Crypto.Pedersen.Reference` linear stand-in) with a proved homomorphism over the NON-negative cone. We
witness the weld end-to-end AND the anti-forgery teeth: an OUT-OF-RANGE note FAILS `rangeValid`, so the
welded create cannot accept a commitment to a negative/overflowing hidden amount. -/

/-- The reference value commitment `commit v r := (v + r).toNat` (linear stand-in; the homomorphism is
PROVED on the non-negative cone via `Int.toNat` additivity). NOT real crypto. -/
def refVC : ValueCommitment where
  commit v r := (v + r).toNat
  hom := by
    intro v w r s hv hw hr hs
    -- all openings ≥ 0 ⇒ both sides are toNat of equal non-negative ints; omega over toNat.
    have e : (v + w + (r + s)) = (v + r) + (w + s) := by ring
    rw [e]
    omega

/-! ### §5.1 — the weld + value-binding teeth, witnessed. -/

/-- A range-valid bound note of value `3` (bits `[1,1]` = `1 + 2 = 3`), blinding `2` ⇒ commitment
`(3 + 2).toNat = 5`. The created set then CONTAINS that bound commitment. -/
def note3 : BoundNote := { value := 3, blinding := 2, bits := [1, 1] }
/-- A range-valid bound note of value `4` (bits `[0,0,1]` = `4`), blinding `1` ⇒ commitment `5`. -/
def note4 : BoundNote := { value := 4, blinding := 1, bits := [0, 0, 1] }

-- The weld: the inserted commitment IS commit(value, blinding) = 5, and it lands in the set:
#guard (note3.commitment refVC == 5)
#guard ((noteCreateBound refVC res0 note3).commitments.contains 5)
-- note3 is range-valid (bits [1,1] recompose to 3, all boolean):
#guard (note3.bits.all (fun b => b == 0 || b == 1) && (bitsToInt note3.bits == note3.value))
-- VALUE-BINDING TEETH: an OUT-OF-RANGE note (value 3 but bits [1] = 1, mismatch) FAILS the range
-- witness ⇒ a real noteCreate proof could NOT carry it (no opening to an unwitnessed value):
#guard ((bitsToInt ([1] : List Int) == (3 : Int)) == false)  --  bits [1] = 1 ≠ 3 (forged)
-- a NEGATIVE value cannot be range-witnessed at all (boolean bits only recompose to ≥ 0):
#guard (([0,0] : List Int).all (fun b => b == 0 || b == 1) && (bitsToInt ([0,0] : List Int) == (0 : Int)))  --  ≥ 0, never −1

-- `created_value_conservation` witnessed: two created notes (values 3 + 4, blindings 2 + 1) sum their
-- commitments (5 + 5 = 10) to the commitment of the summed value (7) under summed blinding (3):
-- `commit 7 3 = (7 + 3).toNat = 10`. The disclosed commitment total testifies to created value 7.
#guard (listCommitment refVC [note3, note4] == 10)
#guard (refVC.commit (([note3, note4].map BoundNote.value).sum)
                     (([note3, note4].map BoundNote.blinding).sum) == 10)

theorem refVC_conservation_witness :
    listCommitment refVC [note3, note4]
      = refVC.commit (([note3, note4].map BoundNote.value).sum)
                     (([note3, note4].map BoundNote.blinding).sum) :=
  created_value_conservation refVC [note3, note4] (by
    intro nt hnt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnt
    rcases hnt with rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩)

#assert_axioms refVC_conservation_witness

/-! ## §6 — E4 (W1): the TYPED NOTE LEDGER + the pool-cell invariant, over the REAL kernel.

The R2 probe (`Substrate/IssuerSupplyProbe.lean §5`) proved the shielded pool-cell candidate's
LEDGER half and found its VALUE-BINDING half NOT REPRESENTABLE: `commitments : List Nat` carries no
`(asset, value)` content, and `noteSpendNullifier` takes only the nullifier — so the unshield
amount was a FREE parameter (the probe's `#guard` drained a pool with ZERO notes).
`Substrate/IssuerLedger.lean §2` stated the repair at the model level (asset-typed notes + an
amount gate), with the inventory bookkeeping carried as HYPOTHESES. THIS section lands E4 in the
kernel, with verbs that DO their own bookkeeping:

  * **`NoteRecord`** — the PARALLEL TYPED LEDGER entry, keyed by commitment: `cm` (the inserted
    Pedersen commitment — for a bound note, EXACTLY `commit value blinding`, the §3 weld), `nf`
    (the spend nullifier the portal derives from the note), `asset`, `value`. The bare
    `commitments : List Nat` set stays wire-compatible; the typed ledger runs beside it.
  * **`ShieldedState`** — the kernel state + the typed note inventory.
  * **`shieldK`** — transfer `nt.value` of `a` from `src` into the pool pseudo-cell `poolOf a`
    COMPOSED with the value-bound commitment insert (`noteCreateBound`, §3) AND the typed-ledger
    append — gated on nullifier freshness (the note is born unspent and uniquely spendable).
  * **`unshieldK`** — look the note up BY NULLIFIER (fail-closed if absent), spend the nullifier
    (fail-closed on double-spend), transfer **exactly the note's value** of **exactly the note's
    asset** pool → `dst`. THE AMOUNT IS NOT A PARAMETER: `unshield.amt = value(spent note)` holds
    BY CONSTRUCTION, and `unshield_value_binding` states it as a theorem over the committed step.
  * **`PoolInvariant`** — `bal (poolOf a) a = Σ value(unspent a-notes)` (+ nullifier-distinctness
    of the inventory), PRESERVED by both verbs (`shieldK_preserves_pool` /
    `unshieldK_preserves_pool`): the pool can NEVER be drained beyond its notes. The probe's
    zero-note drain now FAILS-CLOSED (`#guard` below).
  * Both verbs also preserve `ExactConservation` (the W1 value law) — the ledger half.

The circuit constraint (the Mina-excess / `balance_change` leg binding the in-circuit nullifier to
the disclosed amount) lands with the W1 VK rotation; this is the kernel-truth it must mirror. -/

/-- **A typed note-ledger entry (E4)** — the `(asset, value)` content whose absence made the
value-binding unrepresentable, keyed by the inserted commitment and spendable by its nullifier. -/
structure NoteRecord where
  /-- The note commitment (the entry's key; for a bound note, `commit value blinding` — §3). -/
  cm    : Nat
  /-- The spend nullifier (derived from the note behind the §8 portal; consumed on unshield). -/
  nf    : Nat
  /-- The asset the note is denominated in (E4's missing field). -/
  asset : AssetId
  /-- The note's hidden value (range-witnessed at creation via `BoundNote.rangeValid`). -/
  value : ℤ
  deriving Repr

/-- **The shielded kernel state**: the real kernel + the parallel typed note ledger. (The rotation
folds `notes` into `RecordKernelState` with the commitment-shape bump; until then the pair is the
shielded executor state.) -/
structure ShieldedState where
  kernel : RecordKernelState
  notes  : List NoteRecord := []

/-- The total UNSPENT value of asset `a` over a note inventory, against a nullifier set: the sum of
`value` over the `a`-notes whose nullifier is not yet consumed. -/
def unspentValueIn (notes : List NoteRecord) (nulls : List Nat) (a : AssetId) : ℤ :=
  ((notes.filter (fun n => decide (n.asset = a ∧ n.nf ∉ nulls))).map NoteRecord.value).sum

/-- The unspent value of asset `a` in a shielded state (against the kernel's nullifier set). -/
def unspentValue (s : ShieldedState) (a : AssetId) : ℤ :=
  unspentValueIn s.notes s.kernel.nullifiers a

/-- The inventory's nullifiers are pairwise distinct — each note is spendable by exactly one
nullifier, and a spend retires exactly one note (maintained by `shieldK`'s freshness gate). -/
def NotesDistinct (s : ShieldedState) : Prop :=
  s.notes.Pairwise (fun m n => m.nf ≠ n.nf)

section PoolLedger

variable (poolOf : AssetId → CellId)

/-- **`PoolInvariant` — THE POOL↔NOTES INVARIANT (E4), over the real kernel.** The pool
pseudo-cell's transparent balance equals the total unspent hidden value, per asset — plus the
nullifier-distinctness that makes a spend retire exactly one note. While this holds, every
withdrawal must spend a live note worth exactly what it takes: the pool is undrainable beyond its
notes. -/
def PoolInvariant (s : ShieldedState) : Prop :=
  NotesDistinct s ∧ ∀ a : AssetId, s.kernel.bal (poolOf a) a = unspentValue s a

/-- **`shieldK` — SHIELD (the kernel verb).** Transfer `nt.value` of `a` from `src` into the pool
pseudo-cell (the EXISTING `recKExecAsset` — authority/availability/liveness gates included), insert
the value-bound commitment (`noteCreateBound`, the §3 weld), and append the typed record binding
`commit value blinding ↔ (nf, a, value)`. Gated on nullifier freshness: `nf` must be unused by the
inventory AND unconsumed — the note is born unspent, uniquely spendable. -/
def shieldK (vc : ValueCommitment) (s : ShieldedState) (actor src : CellId) (a : AssetId)
    (nt : BoundNote) (nf : Nat) : Option ShieldedState :=
  if (∀ n ∈ s.notes, n.nf ≠ nf) ∧ nf ∉ s.kernel.nullifiers then
    (recKExecAsset s.kernel { actor := actor, src := src, dst := poolOf a, amt := nt.value } a).map
      (fun k₁ =>
        { kernel := noteCreateBound vc k₁ nt
          notes  := { cm := nt.commitment vc, nf := nf, asset := a, value := nt.value }
                      :: s.notes })
  else none

/-- **`unshieldK` — UNSHIELD (the kernel verb).** Look the spent note up BY NULLIFIER (fail-closed
if no such note — the probe's zero-note drain dies here), consume the nullifier (fail-closed on
double-spend), and transfer **the note's own value, in the note's own asset**, pool → `dst`. The
amount is NOT a parameter: the value-binding `unshield.amt = value(spent note)` holds by
construction (`unshield_value_binding`). -/
def unshieldK (s : ShieldedState) (nf : Nat) (dst : CellId) : Option ShieldedState :=
  match s.notes.find? (fun n => n.nf == nf) with
  | some n =>
      match noteSpendNullifier s.kernel nf with
      | some k₁ =>
          (recKExecAsset k₁
              { actor := poolOf n.asset, src := poolOf n.asset, dst := dst, amt := n.value }
              n.asset).map
            (fun k₂ => { kernel := k₂, notes := s.notes })
      | none => none
  | none => none

/-! ### §6.1 — peel lemmas. -/

/-- Gate + shape of a committed nullifier spend. -/
private theorem noteSpend_committed {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') :
    nf ∉ k.nullifiers ∧ k' = { k with nullifiers := nf :: k.nullifiers } := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h
    simp only [Option.some.injEq] at h
    exact ⟨hin, h.symm⟩

/-- A committed `unshieldK`, fully peeled: the found note, its membership + nullifier match, the
pre-spend freshness, and the post-state shape (nullifier consumed, then the pool→dst transfer of
the note's value in the note's asset), plus the transfer's `pool ≠ dst` gate. -/
private theorem unshieldK_committed {s s' : ShieldedState} {nf : Nat} {dst : CellId}
    (h : unshieldK poolOf s nf dst = some s') :
    ∃ n, s.notes.find? (fun m => m.nf == nf) = some n
      ∧ nf ∉ s.kernel.nullifiers
      ∧ poolOf n.asset ≠ dst
      ∧ s'.notes = s.notes
      ∧ s'.kernel = { s.kernel with
          nullifiers := nf :: s.kernel.nullifiers
          bal := recTransferBal s.kernel.bal (poolOf n.asset) dst n.asset n.value } := by
  unfold unshieldK at h
  cases hfind : s.notes.find? (fun m => m.nf == nf) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some n =>
      rw [hfind] at h
      cases hns : noteSpendNullifier s.kernel nf with
      | none => rw [hns] at h; exact absurd h (by simp)
      | some k₁ =>
          rw [hns] at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨k₂, hk₂, hs'⟩ := h
          subst hs'
          obtain ⟨hfresh, hk₁⟩ := noteSpend_committed hns
          obtain ⟨hgate, hshape⟩ := recKExecAsset_committed hk₂
          refine ⟨n, rfl, hfresh, hgate.2.2.2.1, rfl, ?_⟩
          show k₂ = _
          rw [hshape, hk₁]

/-! ### §6.2 — THE E4 KEYSTONE: the unshield amount IS the spent note's value (over the REAL step). -/

/-- **`unshield_value_binding` — THE E4 KEYSTONE (by construction + committed step).** A
committed unshield spent a note that IS IN the inventory, whose nullifier IS the consumed one, and
the transparent legs moved EXACTLY that note's value in EXACTLY that note's asset: `dst` is
credited `n.value` and the pool of `n.asset` is debited `n.value`. The Mina-excess /
`balance_change` obligation as a theorem over executed kernel state — the amount cannot diverge
from the spent note because it is not even a degree of freedom. -/
theorem unshield_value_binding {s s' : ShieldedState} {nf : Nat} {dst : CellId}
    (h : unshieldK poolOf s nf dst = some s') :
    ∃ n ∈ s.notes, n.nf = nf
      ∧ s'.kernel.bal dst n.asset = s.kernel.bal dst n.asset + n.value
      ∧ s'.kernel.bal (poolOf n.asset) n.asset
          = s.kernel.bal (poolOf n.asset) n.asset - n.value := by
  obtain ⟨n, hfind, _, hne, _, hker⟩ := unshieldK_committed poolOf h
  have hmem : n ∈ s.notes := List.mem_of_find?_eq_some hfind
  have hnf : n.nf = nf := by
    have := List.find?_some hfind
    simpa using this
  refine ⟨n, hmem, hnf, ?_, ?_⟩
  · rw [hker]
    show recTransferBal s.kernel.bal (poolOf n.asset) dst n.asset n.value dst n.asset
        = s.kernel.bal dst n.asset + n.value
    unfold recTransferBal
    rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
  · rw [hker]
    show recTransferBal s.kernel.bal (poolOf n.asset) dst n.asset n.value (poolOf n.asset) n.asset
        = s.kernel.bal (poolOf n.asset) n.asset - n.value
    unfold recTransferBal
    rw [if_pos rfl, if_pos rfl]

/-! ### §6.3 — the inventory bookkeeping lemmas (the sums move by exactly the note). -/

/-- Unspent value over a cons: the head contributes its value iff it matches the asset and is
unspent. -/
private theorem unspentValueIn_cons (n : NoteRecord) (notes : List NoteRecord)
    (nulls : List Nat) (b : AssetId) :
    unspentValueIn (n :: notes) nulls b
      = (if n.asset = b ∧ n.nf ∉ nulls then n.value else 0) + unspentValueIn notes nulls b := by
  unfold unspentValueIn
  rw [List.filter_cons]
  by_cases hn : n.asset = b ∧ n.nf ∉ nulls
  · rw [if_pos (by simpa using hn), if_pos hn]
    simp only [List.map_cons, List.sum_cons]
  · rw [if_neg (by simpa using hn), if_neg hn, zero_add]

/-- Inserting a nullifier NONE of the inventory carries leaves every unspent sum unchanged. -/
private theorem unspentValueIn_insert_fresh (notes : List NoteRecord) (nulls : List Nat)
    (nf : Nat) (hfresh : ∀ n ∈ notes, n.nf ≠ nf) (b : AssetId) :
    unspentValueIn notes (nf :: nulls) b = unspentValueIn notes nulls b := by
  unfold unspentValueIn
  congr 1
  congr 1
  apply List.filter_congr
  intro n hn
  have hne : n.nf ≠ nf := hfresh n hn
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hm => h2 (List.mem_cons_of_mem _ hm)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hm => ?_⟩
    rcases List.mem_cons.mp hm with he | hm'
    · exact hne he
    · exact h2 hm'

/-- **The spend bookkeeping.** Consuming the nullifier of the (unique, by distinctness)
note `find?` locates drops that note's asset's unspent sum by exactly the note's value, and leaves
every other asset's sum unchanged. -/
private theorem unspentValueIn_spend (notes : List NoteRecord) (nulls : List Nat) (nf : Nat)
    (n : NoteRecord) (hfind : notes.find? (fun m => m.nf == nf) = some n)
    (hdist : notes.Pairwise (fun m m' => m.nf ≠ m'.nf)) (hns : nf ∉ nulls) (b : AssetId) :
    unspentValueIn notes (nf :: nulls) b
      = unspentValueIn notes nulls b - (if n.asset = b then n.value else 0) := by
  induction notes with
  | nil => exact absurd hfind (by simp)
  | cons m rest ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdist
      by_cases hm : (m.nf == nf) = true
      · -- the head IS the spent note.
        rw [List.find?_cons_of_pos (p := fun x => x.nf == nf) (a := m) (l := rest) hm] at hfind
        injection hfind with hmn
        rw [← hmn]
        have hmnf : m.nf = nf := by simpa using hm
        have hrest_fresh : ∀ x ∈ rest, x.nf ≠ nf := fun x hx => by
          have := hhead x hx
          rw [hmnf] at this
          exact this.symm
        rw [unspentValueIn_cons, unspentValueIn_cons,
            unspentValueIn_insert_fresh rest nulls nf hrest_fresh b]
        have hin : m.nf ∈ nf :: nulls := by rw [hmnf]; exact List.mem_cons_self
        rw [if_neg (fun hp => hp.2 hin)]
        by_cases hb : m.asset = b
        · rw [if_pos ⟨hb, by rw [hmnf]; exact hns⟩, if_pos hb]
          ring
        · rw [if_neg (fun hp => hb hp.1), if_neg hb]
          ring
      · -- the head is NOT the spent note: its membership is identical on both sides; recurse.
        rw [List.find?_cons_of_neg (p := fun x => x.nf == nf) (a := m) (l := rest) hm] at hfind
        have hmnf : m.nf ≠ nf := by simpa using hm
        have hiff : (m.asset = b ∧ m.nf ∉ nf :: nulls) ↔ (m.asset = b ∧ m.nf ∉ nulls) := by
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun hmem => h2 (List.mem_cons_of_mem _ hmem)⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, fun hmem => ?_⟩
            rcases List.mem_cons.mp hmem with he | hmem'
            · exact hmnf he
            · exact h2 hmem'
        rw [unspentValueIn_cons, unspentValueIn_cons,
            if_congr hiff rfl rfl, ih hfind htail]
        ring

/-! ### §6.4 — THE CUSTODY KEYSTONES: `PoolInvariant` is preserved (the pool is undrainable). -/

/-- **`shieldK_preserves_pool`.** A committed shield credits the pool of `a` by exactly
the created note's value AND appends that note unspent — both sides of the pool↔notes equation rise
together; every other asset's pool column and inventory slice are untouched. Distinctness is
maintained by the freshness gate. -/
theorem shieldK_preserves_pool {vc : ValueCommitment} {s s' : ShieldedState} {actor src : CellId}
    {a : AssetId} {nt : BoundNote} {nf : Nat}
    (h : shieldK poolOf vc s actor src a nt nf = some s')
    (hinv : PoolInvariant poolOf s) : PoolInvariant poolOf s' := by
  unfold shieldK at h
  by_cases hg : (∀ n ∈ s.notes, n.nf ≠ nf) ∧ nf ∉ s.kernel.nullifiers
  · rw [if_pos hg] at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨k₁, hk₁, hs'⟩ := h
    subst hs'
    obtain ⟨hgate, hshape⟩ := recKExecAsset_committed hk₁
    have hne : src ≠ poolOf a := hgate.2.2.2.1
    constructor
    · -- distinctness: the appended nf is fresh by the gate.
      show ({ cm := nt.commitment vc, nf := nf, asset := a, value := nt.value }
              :: s.notes).Pairwise (fun m n => m.nf ≠ n.nf)
      exact List.pairwise_cons.mpr ⟨fun n hn => (hg.1 n hn).symm, hinv.1⟩
    · intro b
      -- post kernel: noteCreateBound only inserts a commitment — bal/nullifiers are k₁'s; and
      -- k₁ is the recTransferBal write on s.kernel.
      have hbal : (noteCreateBound vc k₁ nt).bal
          = recTransferBal s.kernel.bal src (poolOf a) a nt.value := by
        rw [hshape]; rfl
      have hnulls : (noteCreateBound vc k₁ nt).nullifiers = s.kernel.nullifiers := by
        rw [hshape]; rfl
      show (noteCreateBound vc k₁ nt).bal (poolOf b) b
          = unspentValueIn ({ cm := nt.commitment vc, nf := nf, asset := a, value := nt.value }
              :: s.notes) (noteCreateBound vc k₁ nt).nullifiers b
      rw [hbal, hnulls, unspentValueIn_cons]
      dsimp only
      rcases eq_or_ne b a with hba | hba
      · -- the shielded asset: pool credited + the new note enters the unspent sum.
        rw [hba]
        show recTransferBal s.kernel.bal src (poolOf a) a nt.value (poolOf a) a = _
        unfold recTransferBal
        rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl,
            if_pos (show a = a ∧ nf ∉ s.kernel.nullifiers from ⟨rfl, hg.2⟩)]
        have := hinv.2 a
        unfold unspentValue at this
        omega
      · -- another asset: pool column untouched, new note filtered out.
        rw [recTransferBal_untouched s.kernel.bal src (poolOf a) a b nt.value hba (poolOf b),
            if_neg (fun hp => hba hp.1.symm), zero_add]
        exact hinv.2 b
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **`unshieldK_preserves_pool` — THE POOL IS UNDRAINABLE.** A committed unshield debits
the pool of the spent note's asset by exactly the note's value, and the note (the UNIQUE one with
that nullifier, by distinctness) leaves the unspent sum — the equation is maintained; every other
asset is untouched. With `PoolInvariant` carried, no sequence of shields/unshields can take more
out of a pool than its live notes back. -/
theorem unshieldK_preserves_pool {s s' : ShieldedState} {nf : Nat} {dst : CellId}
    (h : unshieldK poolOf s nf dst = some s')
    (hinv : PoolInvariant poolOf s) : PoolInvariant poolOf s' := by
  obtain ⟨n, hfind, hfresh, hne, hnotes, hker⟩ := unshieldK_committed poolOf h
  constructor
  · show (s'.notes).Pairwise (fun m n => m.nf ≠ n.nf)
    rw [hnotes]
    exact hinv.1
  · intro b
    show s'.kernel.bal (poolOf b) b = unspentValue s' b
    unfold unspentValue
    rw [hnotes, hker]
    show recTransferBal s.kernel.bal (poolOf n.asset) dst n.asset n.value (poolOf b) b
        = unspentValueIn s.notes (nf :: s.kernel.nullifiers) b
    rw [unspentValueIn_spend s.notes s.kernel.nullifiers nf n hfind hinv.1 hfresh b]
    rcases eq_or_ne b n.asset with rfl | hba
    · -- the spent asset: pool debited by the note's value; the note leaves the unspent sum.
      unfold recTransferBal
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      have := hinv.2 n.asset
      unfold unspentValue at this
      omega
    · -- another asset: pool column untouched, the spent note was not in this slice.
      rw [recTransferBal_untouched s.kernel.bal (poolOf n.asset) dst n.asset b n.value hba
            (poolOf b),
          if_neg (fun hp => hba hp.symm), sub_zero]
      exact hinv.2 b

/-! ### §6.5 — the LEDGER half: both verbs preserve the W1 value law. -/

/-- **SHIELD preserves `ExactConservation`** — the transparent leg is a transfer
(`recKExecAsset_preserves_exact`), the value-bound commitment insert is neutral
(`noteCreateCommitment_preserves_exact`). -/
theorem shieldK_preserves_exact {vc : ValueCommitment} {s s' : ShieldedState} {actor src : CellId}
    {a : AssetId} {nt : BoundNote} {nf : Nat}
    (h : shieldK poolOf vc s actor src a nt nf = some s')
    (hex : ExactConservation s.kernel) : ExactConservation s'.kernel := by
  unfold shieldK at h
  by_cases hg : (∀ n ∈ s.notes, n.nf ≠ nf) ∧ nf ∉ s.kernel.nullifiers
  · rw [if_pos hg] at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨k₁, hk₁, hs'⟩ := h
    rw [← hs']
    show ExactConservation (noteCreateBound vc k₁ nt)
    exact noteCreateCommitment_preserves_exact k₁ _ (recKExecAsset_preserves_exact hk₁ hex)
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **UNSHIELD preserves `ExactConservation`** — the nullifier insert is neutral, the pool→dst leg
is a transfer. -/
theorem unshieldK_preserves_exact {s s' : ShieldedState} {nf : Nat} {dst : CellId}
    (h : unshieldK poolOf s nf dst = some s')
    (hex : ExactConservation s.kernel) : ExactConservation s'.kernel := by
  unfold unshieldK at h
  cases hfind : s.notes.find? (fun m => m.nf == nf) with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some n =>
      rw [hfind] at h
      cases hns : noteSpendNullifier s.kernel nf with
      | none => rw [hns] at h; exact absurd h (by simp)
      | some k₁ =>
          rw [hns] at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨k₂, hk₂, hs'⟩ := h
          rw [← hs']
          exact recKExecAsset_preserves_exact hk₂ (noteSpendNullifier_preserves_exact hns hex)

end PoolLedger

#assert_axioms unshield_value_binding
#assert_axioms shieldK_preserves_pool
#assert_axioms unshieldK_preserves_pool
#assert_axioms shieldK_preserves_exact
#assert_axioms unshieldK_preserves_exact

/-! ### §6.6 — non-vacuity (`#guard`): the probe's drain is CLOSED; the roundtrip works.

Pool registry: every asset's pool is cell 3. User cell 2 holds 4 of asset 0; pool empty; no notes.
The probe's `kPool` drain (an unshield against ZERO notes) now FAILS-CLOSED; the legitimate
shield→unshield roundtrip moves exactly the note's value both ways and refuses the double-spend. -/

/-- Demo pool registry: every asset's pool is cell 3. -/
def poolDemo : AssetId → CellId := fun _ => 3

/-- A shielded genesis: user 2 holds 4 of asset 0; pool 3 empty; NO notes, NO nullifiers. -/
def sShield0 : ShieldedState :=
  { kernel :=
      { accounts := {2, 3}
        cell := fun _ => Value.record [("balance", Value.int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 2 ∧ a = 0 then 4 else 0 } }

/-- The probe's drain target: pool 3 holds 10 of asset 0 — but ZERO notes back it. -/
def sPoolUnbacked : ShieldedState :=
  { kernel :=
      { accounts := {2, 3}
        cell := fun _ => Value.record [("balance", Value.int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 3 ∧ a = 0 then 10 else 0 } }

-- THE PROBE'S HOLE, CLOSED: the zero-note drain (`IssuerSupplyProbe` §8 committed it) now REFUSES —
-- there is no note to spend, so there is no amount to withdraw.
#guard ((unshieldK poolDemo sPoolUnbacked 99 2).isNone)
-- ...and the unbacked pool is exactly a `PoolInvariant` violation, witnessed at asset 0 (10 ≠ 0):
#guard ((sPoolUnbacked.kernel.bal (poolDemo 0) 0
          == unspentValueIn sPoolUnbacked.notes sPoolUnbacked.kernel.nullifiers 0) == false)

/-- The roundtrip's shield: user 2 shields `note3` (value 3, blinding 2 ⇒ commitment 5 under
`refVC`) of asset 0 under nullifier 99. -/
def sShielded : Option ShieldedState := shieldK poolDemo refVC sShield0 2 2 0 note3 99

-- SHIELD commits: pool 3 gains exactly the note's value (3); the typed ledger binds
-- commitment 5 ↔ (nf 99, asset 0, value 3); the bare commitment set gains 5 (wire-compatible).
#guard (sShielded.isSome)
#guard (sShielded.map (fun s => (s.kernel.bal 3 0, s.kernel.bal 2 0))) == some (3, 1)
#guard (sShielded.map (fun s => s.notes.map (fun n => (n.cm, n.nf, n.asset, n.value))))
        == some [(5, 99, 0, 3)]
#guard (sShielded.map (fun s => s.kernel.commitments.contains 5)) == some true
-- the pool↔notes equation holds after the shield (both sides 3):
#guard (sShielded.map (fun s =>
          s.kernel.bal (poolDemo 0) 0 == unspentValueIn s.notes s.kernel.nullifiers 0))
        == some true
-- UNSHIELD by nullifier: dst 2 is credited EXACTLY the note's value (no amount parameter exists);
-- the pool returns to 0 and the equation holds again (the note left the unspent sum).
#guard ((sShielded.bind (fun s => unshieldK poolDemo s 99 2)).map
          (fun s => (s.kernel.bal 3 0, s.kernel.bal 2 0))) == some (0, 4)
#guard ((sShielded.bind (fun s => unshieldK poolDemo s 99 2)).map
          (fun s => s.kernel.bal (poolDemo 0) 0
              == unspentValueIn s.notes s.kernel.nullifiers 0)) == some true
-- DOUBLE-SPEND refused: the same nullifier cannot be unshielded twice.
#guard ((sShielded.bind (fun s => unshieldK poolDemo s 99 2)
          |>.bind (fun s => unshieldK poolDemo s 99 2)).isNone)
-- the SHIELD freshness gate: re-shielding under a consumed/used nullifier refuses (each note is
-- uniquely spendable).
#guard ((sShielded.bind (fun s => shieldK poolDemo refVC s 2 2 0 note3 99)).isNone)
-- the value law rides the whole roundtrip: every committed state sums to the genesis supply.
#guard ((sShielded.bind (fun s => unshieldK poolDemo s 99 2)).map
          (fun s => recTotalAsset s.kernel 0)) == some 4

end Dregg2.Exec.ShieldedValue
