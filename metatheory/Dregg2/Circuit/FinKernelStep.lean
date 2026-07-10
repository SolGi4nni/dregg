/-
# Dregg2.Circuit.FinKernelStep — DEBT-B lane R3: the finite-state EFFECT STEP + the commuting square.

Lane R1 (`Dregg2/Circuit/FinKernelState.lean`) built the finite-map refinement `FinKernelState`, its
`denote : FinKernelState → RecordKernelState`, the load-bearing `denote_injective`, and it left the
SURJECTIVITY honesty gate `denote_surjective_on_reachable` PARAMETRIC over a per-effect commuting square
`hpres : ∀ e f, denote (finStep e f) = recStep e (denote f)` — an EXPLICIT hypothesis for R3 to discharge.

This file discharges it. It builds `finStep : FullAction → FinKernelState → FinKernelState` over the tree's
REAL full op-set `FullAction` (`Exec/TurnExecutorFull.lean:301`: `balance`/`delegate`/`revoke`/`mint`/`burn`),
matching the verified record-model executors (`recKExec`/`recKDelegate`/`recKRevokeTarget`/`recKMint`/
`recKBurn`), and PROVES the commuting square `finStep_denote` over the REAL effect semantics — every one of the
five variants. There is NO carrier and NO toy step: each finite step performs the SAME point update the record
step performs, expressed as a `CanonMap` insert/erase rather than a `Function.update` on an infinite-domain
function.

THE KEY LEMMA (`CanonMap.get_set_eq` / `CanonMap.get_insertNZ`): a canonical-map write denotes to a POINT
function-update — `(cm.set k v).get x = if x = k then v else cm.get x`. The Canonical (sparse) invariant is
PRESERVED by construction: writing the field default ERASES (never stores a default), writing a non-default
INSERTS. Reducing each record step's field update to this lemma lands the square; instantiating R1's gate with
the PROVED square makes `reachable_states_are_finite` UNCONDITIONAL — every reachable real kernel state has a
finite representative.

NOTE (why two writers): `cell`'s value type `Value` has no `DecidableEq` in-tree, so the default-deciding `set`
is unavailable there — but the record cell writers (`setBalance …`) provably NEVER produce the default
`Value.record []` (`setBalance_ne_default`), so `cell` uses the insert-only `insertNZ` carrying that proof.
`caps` (`List Cap`, `DecidableEq` present) uses `set`, and REVOKE genuinely writes the default `[]` ⇒ ERASE.
-/
import Dregg2.Circuit.FinKernelState
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.FinKernelState

open Dregg2.Exec Dregg2.Authority
open Dregg2.Exec.TurnExecutorFull (FullAction recKMint recKBurn recCreditCell)
open Dregg2.Exec.TurnExecutor (Action)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

universe u v

/-! ## §1 — `SortedMap.erase` + the insert/erase LOOKUP laws (the missing sorted-map primitives R3 needs).

R1 gave `SortedMap.insert` (overwrite, order-preserving) but no `erase` and no lookup-after-update law. Both are
needed to reduce a record field update to a point function-update. `erase` drops every entry at a key (there is
at most one, by the nodup-keys invariant); it preserves sortedness because it is a SUBLIST of the input. -/

namespace SortedMap

variable {K : Type u} {V : Type v} [LinearOrder K]

/-- Raw-list erase: drop every entry whose key is `k`. -/
def eraseList (k : K) : List (K × V) → List (K × V)
  | [] => []
  | (k', v') :: rest => if k' = k then eraseList k rest else (k', v') :: eraseList k rest

/-- `eraseList` is a sublist of the input (it only drops entries). -/
theorem eraseList_sublist (k : K) : ∀ l : List (K × V), List.Sublist (eraseList k l) l
  | [] => List.Sublist.refl _
  | (k', v') :: rest => by
      unfold eraseList
      by_cases h : k' = k
      · rw [if_pos h]; exact (eraseList_sublist k rest).cons _
      · rw [if_neg h]; exact (eraseList_sublist k rest).cons₂ _

/-- Membership in an erase implies membership in the input (via the sublist). -/
theorem mem_eraseList {k : K} {p : K × V} {l : List (K × V)} (h : p ∈ eraseList k l) : p ∈ l :=
  (eraseList_sublist k l).mem h

/-- The lookup-after-erase law: absence at `k`, unchanged elsewhere. -/
theorem lookupList_eraseList (k x : K) (l : List (K × V)) :
    lookupList x (eraseList k l) = if x = k then none else lookupList x l := by
  induction l with
  | nil => simp [eraseList, lookupList]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      simp only [eraseList]
      by_cases hkk : k' = k
      · simp only [if_pos hkk, ih, lookupList]
        by_cases hx : x = k
        · simp [hx]
        · have : ¬ k' = x := by rw [hkk]; exact fun h => hx h.symm
          simp [hx, this]
      · simp only [if_neg hkk, lookupList, ih]
        by_cases hk'x : k' = x
        · have hxk : ¬ x = k := by rw [← hk'x]; exact hkk
          simp [hk'x, hxk]
        · by_cases hx : x = k <;> simp [hk'x, hx, hkk]

/-- The lookup-after-insert law: `some v` at `k`, unchanged elsewhere. -/
theorem lookupList_insertList (k : K) (v : V) (x : K) (l : List (K × V)) :
    lookupList x (insertList k v l) = if x = k then some v else lookupList x l := by
  induction l with
  | nil =>
      simp only [insertList, lookupList]
      by_cases hx : x = k
      · simp [hx]
      · have : ¬ k = x := fun h => hx h.symm
        simp [hx, this]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      unfold insertList
      by_cases hlt : k < k'
      · simp only [if_pos hlt, lookupList]
        by_cases hx : x = k
        · simp [hx]
        · have : ¬ k = x := fun h => hx h.symm
          simp [hx, this]
      · by_cases hkx : k = k'
        · simp only [if_neg hlt, if_pos hkx, lookupList]
          by_cases hx : x = k
          · simp [hx]
          · have h1 : ¬ k = x := fun h => hx h.symm
            have h2 : ¬ k' = x := by rw [← hkx]; exact h1
            simp [hx, h1, h2]
        · simp only [if_neg hlt, if_neg hkx, lookupList, ih]
          by_cases hx : x = k
          · have h2 : ¬ k' = k := fun h => hkx h.symm
            simp [hx, h2]
          · by_cases hk'x : k' = x <;> simp [hx, hk'x]

/-- `erase` on `SortedMap`: drop `k`, preserving the strictly-increasing-key invariant (sublist ⇒ pairwise). -/
def erase (m : SortedMap K V) (k : K) : SortedMap K V :=
  ⟨eraseList k m.entries,
   m.sortedKeys.sublist ((eraseList_sublist k m.entries).map Prod.fst)⟩

@[simp] theorem lookup_erase (m : SortedMap K V) (k x : K) :
    (m.erase k).lookup x = if x = k then none else m.lookup x :=
  lookupList_eraseList k x m.entries

@[simp] theorem lookup_insert (m : SortedMap K V) (k : K) (v : V) (x : K) :
    (m.insert k v).lookup x = if x = k then some v else m.lookup x :=
  lookupList_insertList k v x m.entries

/-- A pair in an insert is either the new pair or an old pair (value-level membership). -/
theorem mem_insertList (k : K) (v : V) (p : K × V) :
    ∀ l : List (K × V), p ∈ insertList k v l → p = (k, v) ∨ p ∈ l
  | [], h => by simp only [insertList, List.mem_singleton] at h; exact Or.inl h
  | (k', v') :: rest, h => by
      unfold insertList at h
      by_cases hlt : k < k'
      · rw [if_pos hlt] at h
        rcases List.mem_cons.mp h with rfl | h2
        · exact Or.inl rfl
        · exact Or.inr h2
      · rw [if_neg hlt] at h
        by_cases hkx : k = k'
        · rw [if_pos hkx] at h
          rcases List.mem_cons.mp h with rfl | h2
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ h2)
        · rw [if_neg hkx] at h
          rcases List.mem_cons.mp h with rfl | h2
          · exact Or.inr List.mem_cons_self
          · rcases mem_insertList k v p rest h2 with heq | h3
            · exact Or.inl heq
            · exact Or.inr (List.mem_cons_of_mem _ h3)

end SortedMap

/-! ## §2 — the canonical-map writers `insertNZ` / `set`, and the KEY point-update lemmas.

`insertNZ` inserts a value KNOWN to be non-default (proof carried) — used for `cell`, whose writes provably never
produce the default. `set` DECIDES equality with the default (`[DecidableEq V]`) and ERASES on a default write —
used for `caps`, where revoke genuinely empties a slot. Both carry the Canonical proof, and both read back as a
POINT function-update. -/

namespace CanonMap

variable {K : Type u} {V : Type v} [LinearOrder K] {d : V}

/-- Inserting a NON-default value preserves the "no entry stores the default" invariant. -/
theorem canon_insert {m : SortedMap K V} (hc : SortedMap.Canonical d m) {v : V} (hv : v ≠ d) (k : K) :
    SortedMap.Canonical d (m.insert k v) := by
  intro p hp
  rcases SortedMap.mem_insertList k v p m.entries hp with rfl | hmem
  · exact hv
  · exact hc p hmem

/-- Erasing preserves the "no entry stores the default" invariant (erase only drops entries). -/
theorem canon_erase {m : SortedMap K V} (hc : SortedMap.Canonical d m) (k : K) :
    SortedMap.Canonical d (m.erase k) :=
  fun p hp => hc p (SortedMap.mem_eraseList hp)

/-- **`insertNZ`** — insert a value proven non-default (no `DecidableEq V` needed). Stays canonical. -/
def insertNZ (cm : CanonMap K V d) (k : K) (v : V) (hv : v ≠ d) : CanonMap K V d :=
  ⟨cm.toMap.insert k v, canon_insert cm.canon hv k⟩

/-- **`set`** — the sparse write: ERASE the key when writing the default (stay canonical), INSERT otherwise. -/
def set [DecidableEq V] (cm : CanonMap K V d) (k : K) (v : V) : CanonMap K V d :=
  if hv : v = d then
    ⟨cm.toMap.erase k, canon_erase cm.canon k⟩
  else
    ⟨cm.toMap.insert k v, canon_insert cm.canon hv k⟩

/-- **KEY LEMMA (insert-only writer).** `insertNZ` denotes to a point function-update. -/
theorem get_insertNZ (cm : CanonMap K V d) (k : K) (v : V) (hv : v ≠ d) (x : K) :
    (cm.insertNZ k v hv).get x = if x = k then v else cm.get x := by
  unfold CanonMap.insertNZ CanonMap.get SortedMap.get
  simp only [SortedMap.lookup_insert]
  by_cases hx : x = k <;> simp [hx]

/-- **KEY LEMMA (default-deciding writer).** `set` denotes to a point function-update — the erase (default) and
insert (non-default) cases coincide with the single point-update, because a default write reads back the
default. -/
theorem get_set_eq [DecidableEq V] (cm : CanonMap K V d) (k : K) (v : V) (x : K) :
    (cm.set k v).get x = if x = k then v else cm.get x := by
  unfold CanonMap.set CanonMap.get SortedMap.get
  by_cases hv : v = d
  · rw [dif_pos hv]
    simp only [SortedMap.lookup_erase]
    by_cases hx : x = k
    · simp [hx, hv]
    · simp [hx]
  · rw [dif_neg hv]
    simp only [SortedMap.lookup_insert]
    by_cases hx : x = k
    · simp [hx]
    · simp [hx]

end CanonMap

/-! ## §3 — `denote` unfolding helpers + `setBalance_ne_default` (the `cell`-writer non-default fact). -/

@[simp] theorem denote_cell (f : FinKernelState) : (denote f).cell = fun c => f.cell.get c := rfl
@[simp] theorem denote_caps (f : FinKernelState) : (denote f).caps = fun l => f.caps.get l := rfl

/-- A `cell`-field update denotes field-wise: only the `cell` total-function changes, to the map's `get`. -/
theorem denote_with_cell (f : FinKernelState) (M : CanonMap CellId Value (Value.record [])) :
    denote { f with cell := M } = { denote f with cell := fun c => M.get c } := rfl

/-- A `caps`-field update denotes field-wise. -/
theorem denote_with_caps (f : FinKernelState) (M : CanonMap Label (List Cap) []) :
    denote { f with caps := M } = { denote f with caps := fun l => M.get l } := rfl

/-- Reduce a `cell`-field structure equality (over the same `denote f` base) to the field function equality.
(`congr` cannot pierce the `have __src := …`-desugared `with`-update, so we bridge it explicitly.) -/
theorem cell_update_ext (f : FinKernelState) {A B : CellId → Value} (h : A = B) :
    ({ denote f with cell := A } : RecordKernelState) = { denote f with cell := B } := by rw [h]

/-- Reduce a `caps`-field structure equality to the field function equality. -/
theorem caps_update_ext (f : FinKernelState) {A B : Caps} (h : A = B) :
    ({ denote f with caps := A } : RecordKernelState) = { denote f with caps := B } := by rw [h]

/-- **`setBalance_ne_default`** — a record-cell balance write NEVER produces the default `Value.record []`
(it always yields a `.record` with at least the `balance` field). This is why `cell` can use the insert-only
`insertNZ` without a `DecidableEq Value`: the sparse invariant is never threatened by a cell write. -/
theorem setBalance_ne_default (cell : Value) (v : Int) : setBalance cell v ≠ Value.record [] := by
  unfold setBalance
  cases cell with
  | record fs =>
      cases fs with
      | nil => simp [setBalance.setBalanceList]
      | cons hd tl =>
          obtain ⟨k, x⟩ := hd
          simp only [setBalance.setBalanceList]
          by_cases hk : (k == balanceField) = true
          · rw [if_pos hk]; simp
          · rw [if_neg hk]; simp
  | int a => simp
  | dig a => simp
  | sym a => simp

/-! ## §4 — the SHAPE lemmas: a committed record step is exactly a field point-update. -/

/-- A committed transfer sets the `cell` field to `recTransfer` (the two-cell balance move). -/
theorem recKExec_shape {k k' : RecordKernelState} {turn : Turn} (h : recKExec k turn = some k') :
    k' = { k with cell := recTransfer k.cell turn.src turn.dst turn.amt } := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact h.symm
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed mint credits `cell`'s `balance` field (a single-cell `recCreditCell`). -/
theorem recKMint_shape {k k' : RecordKernelState} {actor cell : CellId} {amt : ℤ}
    (h : recKMint k actor cell amt = some k') :
    k' = { k with cell := recCreditCell k.cell cell amt } := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact h.symm
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed burn debits `cell`'s `balance` field (`recCreditCell … (-amt)`). -/
theorem recKBurn_shape {k k' : RecordKernelState} {actor cell : CellId} {amt : ℤ}
    (h : recKBurn k actor cell amt = some k') :
    k' = { k with cell := recCreditCell k.cell cell (-amt) } := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ balOf (k.cell cell)
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact h.symm
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed delegation grants (into `caps` at `recipient`) the delegator's held `t`-conferring cap. -/
theorem recKDelegate_shape {k k' : RecordKernelState} {delegator recipient t : Label}
    (h : recKDelegate k delegator recipient t = some k') :
    k' = { k with caps := grant k.caps recipient (heldCapTo k.caps delegator t) } := by
  unfold recKDelegate at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact h.symm
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §5 — `recStep` (real record step, dispatching recKExec/recKMint/…) and `finStep` over the 5-PRIMITIVE `FullAction` CORE. ⚠ SCOPE: this covers balance/cap/delegation (fields cell/caps/delegations); the deployed 33-effect set's CELL-LIFECYCLE/FACTORY/HEAP/FIELD effects (CreateCell, SetField, CellSeal, IncrementNonce, NoteSpend, …) that mutate cell/lifecycle/slotCaveats/heaps/deathCert are NOT yet covered — they are the R3-continuation, and `reachable_states_are_finite` is correspondingly scoped to FullAction-reachable states. Each remaining effect follows the SAME commuting-square shape (target of the `refine_commutes` tactic). -/

/-- **`recStep`** — the REAL record-model step made total (identity on reject). `balance` = transfer
(`recKExec`), the rest the verified authority/supply executors. -/
def recStep : FullAction → RecordKernelState → RecordKernelState
  | .balance a,        k => (recKExec k a.move).getD k
  | .delegate d r t,   k => (recKDelegate k d r t).getD k
  | .revoke h t,       k => recKRevokeTarget k h t
  | .mint actor c amt, k => (recKMint k actor c amt).getD k
  | .burn actor c amt, k => (recKBurn k actor c amt).getD k

/-- The finite transfer: on the SAME admissibility (evaluated on `denote f`), move the two `cell` balances as a
pair of `insertNZ`s (a balance write is never the default); identity on reject. -/
def finTransfer (turn : Turn) (f : FinKernelState) : FinKernelState :=
  match recKExec (denote f) turn with
  | some _ =>
      { f with cell :=
          ((f.cell.insertNZ turn.dst (setBalance (f.cell.get turn.dst) (balOf (f.cell.get turn.dst) + turn.amt))
              (setBalance_ne_default _ _)).insertNZ
            turn.src (setBalance (f.cell.get turn.src) (balOf (f.cell.get turn.src) - turn.amt))
              (setBalance_ne_default _ _)) }
  | none => f

/-- The finite delegation: grant into `caps` at `recipient` (prepend the held cap); identity on reject. -/
def finDelegate (delegator recipient t : CellId) (f : FinKernelState) : FinKernelState :=
  match recKDelegate (denote f) delegator recipient t with
  | some _ =>
      { f with caps := (f.caps.set recipient
          (heldCapTo (fun l => f.caps.get l) delegator t :: f.caps.get recipient)) }
  | none => f

/-- The finite revocation: filter `holder`'s `caps` slot; ALWAYS commits. When the filter empties the slot the
write is the field default `[]`, so `CanonMap.set` ERASES it — the sparse discipline in action. -/
def finRevoke (holder t : CellId) (f : FinKernelState) : FinKernelState :=
  { f with caps := f.caps.set holder ((f.caps.get holder).filter (fun cap => ¬ confersEdgeTo t cap)) }

/-- The finite mint: credit `cell`'s `balance` field; identity on reject. -/
def finMint (actor cell : CellId) (amt : ℤ) (f : FinKernelState) : FinKernelState :=
  match recKMint (denote f) actor cell amt with
  | some _ => { f with cell := (f.cell.insertNZ cell
      (setBalance (f.cell.get cell) (balOf (f.cell.get cell) + amt)) (setBalance_ne_default _ _)) }
  | none => f

/-- The finite burn: debit `cell`'s `balance` field; identity on reject. -/
def finBurn (actor cell : CellId) (amt : ℤ) (f : FinKernelState) : FinKernelState :=
  match recKBurn (denote f) actor cell amt with
  | some _ => { f with cell := (f.cell.insertNZ cell
      (setBalance (f.cell.get cell) (balOf (f.cell.get cell) + (-amt))) (setBalance_ne_default _ _)) }
  | none => f

/-- **`finStep`** — the finite EFFECT STEP over the REAL `FullAction` op-set. -/
def finStep : FullAction → FinKernelState → FinKernelState
  | .balance a,        f => finTransfer a.move f
  | .delegate d r t,   f => finDelegate d r t f
  | .revoke h t,       f => finRevoke h t f
  | .mint actor c amt, f => finMint actor c amt f
  | .burn actor c amt, f => finBurn actor c amt f

/-! ## §6 — `finStep_canonical`: every field of a finite step stays Canonical (sparse) by construction. -/

theorem finStep_canonical (e : FullAction) (f : FinKernelState) :
    SortedMap.Canonical (Value.record []) (finStep e f).cell.toMap
    ∧ SortedMap.Canonical ([] : List Cap) (finStep e f).caps.toMap :=
  ⟨(finStep e f).cell.canon, (finStep e f).caps.canon⟩

/-! ## §7 — the COMMUTING SQUARE, per effect, over the REAL semantics.

THE REUSABLE REWRITE SET (a follow-up lane can lift this into a `refine_commutes` tactic / a `@[finDenote]` simp
set once it lives in an imported module — `register_simp_attr` is not usable in its own defining file): the four
BRIDGE lemmas `CanonMap.get_insertNZ`, `CanonMap.get_set_eq`, `denote_cell`, `denote_caps`. Every case below is
UNIFORM: `cases` the guard (none ⇒ `Option.getD_none`), rewrite by the record `_shape` lemma, `refine
cell/caps_update_ext`, `funext`, then `simp only [<the four bridge lemmas>]` + `unfold <record field-op>` +
`by_cases` on the touched key(s). The record field-ops (`recTransfer`/`recCreditCell`/`grant`/the revoke filter)
supply the ONLY per-effect residue — the point-update itself is always the same bridge.

NAMED NON-UNIFORMITIES (the honest signal, surfaced not smoothed):
  * `cell` writes use the insert-only `insertNZ` (bridge `get_insertNZ`) because `Value` has no `DecidableEq`;
    `caps` writes use the default-deciding `set` (bridge `get_set_eq`). Two writers, two bridges.
  * REVOKE is the ONLY arm that can write the field DEFAULT (`[]`): its `set` takes the ERASE leg of
    `get_set_eq`, where every other arm takes the INSERT leg. (This is the sparse-map tooth, exercised in §9.)
  * The guard/reject (`none`) branch is uniform: `finStep = id`, matching `Option.getD_none` on the record side.
  * `bal` (the two-level `CellId ×ₗ AssetId` field) is untouched by all five `FullAction` arms, so its two-level
    bridge is not needed here; it is left for the lane that adds a `bal`-writing effect (per-asset transfer). -/

/-- Transfer commutes. -/
theorem finTransfer_denote (turn : Turn) (f : FinKernelState) :
    denote (finTransfer turn f) = (recKExec (denote f) turn).getD (denote f) := by
  unfold finTransfer
  cases h : recKExec (denote f) turn with
  | none => simp only [h, Option.getD_none]
  | some k' =>
      simp only [h, Option.getD_some]
      rw [recKExec_shape h, denote_with_cell]
      refine cell_update_ext f ?_
      funext c
      simp only [CanonMap.get_insertNZ, CanonMap.get_set_eq, denote_cell, denote_caps]
      unfold recTransfer
      by_cases h1 : c = turn.src
      · subst h1; simp
      · by_cases h2 : c = turn.dst
        · subst h2; simp [h1]
        · simp [h1, h2]

/-- Mint commutes. -/
theorem finMint_denote (actor cell : CellId) (amt : ℤ) (f : FinKernelState) :
    denote (finMint actor cell amt f) = (recKMint (denote f) actor cell amt).getD (denote f) := by
  unfold finMint
  cases h : recKMint (denote f) actor cell amt with
  | none => simp only [h, Option.getD_none]
  | some k' =>
      simp only [h, Option.getD_some]
      rw [recKMint_shape h, denote_with_cell]
      refine cell_update_ext f ?_
      funext c
      simp only [CanonMap.get_insertNZ, CanonMap.get_set_eq, denote_cell, denote_caps]
      unfold recCreditCell
      by_cases h1 : c = cell
      · subst h1; simp
      · simp [h1]

/-- Burn commutes. -/
theorem finBurn_denote (actor cell : CellId) (amt : ℤ) (f : FinKernelState) :
    denote (finBurn actor cell amt f) = (recKBurn (denote f) actor cell amt).getD (denote f) := by
  unfold finBurn
  cases h : recKBurn (denote f) actor cell amt with
  | none => simp only [h, Option.getD_none]
  | some k' =>
      simp only [h, Option.getD_some]
      rw [recKBurn_shape h, denote_with_cell]
      refine cell_update_ext f ?_
      funext c
      simp only [CanonMap.get_insertNZ, CanonMap.get_set_eq, denote_cell, denote_caps]
      unfold recCreditCell
      by_cases h1 : c = cell
      · subst h1; simp
      · simp [h1]

/-- Delegate commutes. -/
theorem finDelegate_denote (delegator recipient t : CellId) (f : FinKernelState) :
    denote (finDelegate delegator recipient t f)
      = (recKDelegate (denote f) delegator recipient t).getD (denote f) := by
  unfold finDelegate
  cases h : recKDelegate (denote f) delegator recipient t with
  | none => simp only [h, Option.getD_none]
  | some k' =>
      simp only [h, Option.getD_some]
      rw [recKDelegate_shape h, denote_with_caps]
      refine caps_update_ext f ?_
      funext l
      simp only [CanonMap.get_insertNZ, CanonMap.get_set_eq, denote_cell, denote_caps]
      unfold grant
      by_cases h1 : l = recipient
      · subst h1; simp
      · simp [h1]

/-- Revoke commutes (it always commits, so the record side is `recKRevokeTarget` directly). -/
theorem finRevoke_denote (holder t : CellId) (f : FinKernelState) :
    denote (finRevoke holder t f) = recKRevokeTarget (denote f) holder t := by
  unfold finRevoke recKRevokeTarget
  rw [denote_with_caps]
  refine caps_update_ext f ?_
  funext l
  simp only [CanonMap.get_insertNZ, CanonMap.get_set_eq, denote_cell, denote_caps]
  by_cases h1 : l = holder
  · subst h1; simp
  · simp [h1]

/-- **THE HEADLINE — `finStep_denote` (the commuting square, R1's `hpres`):**
`∀ e f, denote (finStep e f) = recStep e (denote f)` — over the 5-PRIMITIVE `FullAction` CORE (balance/delegate/revoke/mint/burn), PROVED per
effect by reducing each record field update to the canonical-map point-update. -/
theorem finStep_denote (e : FullAction) (f : FinKernelState) :
    denote (finStep e f) = recStep e (denote f) := by
  cases e with
  | balance a        => exact finTransfer_denote a.move f
  | delegate d r t   => exact finDelegate_denote d r t f
  | revoke h t       => exact finRevoke_denote h t f
  | mint actor c amt => exact finMint_denote actor c amt f
  | burn actor c amt => exact finBurn_denote actor c amt f

/-! ## §8 — THE PAYOFF: R1's surjectivity honesty gate, now UNCONDITIONALLY discharged. -/

/-- **`reachable_states_are_finite` — the discharged gate.** Every real kernel state reachable from
`denote finInit` under `recStep` has a FINITE representative — R1's honesty gate, closed by `finStep_denote`
(no hypothesis remains). This is the object the R2 frame hash binds. -/
theorem reachable_states_are_finite (k : RecordKernelState)
    (hr : RecReachable recStep (denote finInit) k) : ∃ f : FinKernelState, denote f = k :=
  denote_surjective_on_reachable finStep recStep finStep_denote k hr

/-! ## §9 — TEETH (`#guard`): a concrete transfer commutes; Canonical survives; a default write ERASES. -/

section Teeth

/-- A concrete finite state: cells `0` (balance 100) and `1` (balance 5), empty caps. -/
private def fT : FinKernelState :=
  { finInit with
    accounts := {0, 1}
    cell := (CanonMap.empty.insertNZ 0 (Value.record [("balance", Value.int 100)]) (by simp)).insertNZ 1
              (Value.record [("balance", Value.int 5)]) (by simp) }

/-- Actor `0` transfers 30 from `0` to `1` (self-src ⇒ authorized with empty caps). -/
private def tT : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

-- The finite transfer commits and produces the right balances (70 and 35):
#guard balOf ((denote (finTransfer tT fT)).cell 0) == 70
#guard balOf ((denote (finTransfer tT fT)).cell 1) == 35
-- … and denote COMMUTES with the record step at each moved cell (the square, concretely):
#guard balOf ((denote (finTransfer tT fT)).cell 0)
        == balOf (((recKExec (denote fT) tT).getD (denote fT)).cell 0)
#guard balOf ((denote (finTransfer tT fT)).cell 1)
        == balOf (((recKExec (denote fT) tT).getD (denote fT)).cell 1)

-- A `Nat` canonical map (default 0): the CANONICAL (sparse) invariant survives `set`, and a DEFAULT write ERASES.
private def cmN : CanonMap CellId Nat 0 := CanonMap.set (CanonMap.set CanonMap.empty 1 7) 2 9
#guard cmN.toMap.entries == [(1, 7), (2, 9)]              -- non-default writes INSERT (stay sorted)
#guard cmN.get 1 == 7                                     -- present
#guard cmN.get 3 == 0                                     -- absent ⇒ default
#guard (CanonMap.set cmN 1 0).toMap.entries == [(2, 9)]   -- a DEFAULT (0) write ERASES key 1 — stays SPARSE
#guard (CanonMap.set cmN 1 0).get 1 == 0                  -- and reads back the default
#guard (CanonMap.set cmN 2 5).toMap.entries == [(1, 7), (2, 5)]  -- non-default OVERWRITE keeps one entry

end Teeth

end Dregg2.Circuit.FinKernelState
