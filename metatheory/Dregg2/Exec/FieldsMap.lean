/-
# Dregg2.Exec.FieldsMap — the committed user-field MAP (`fields_root`), Stage 0 beachhead.

`_RECORD-LAYER-UPGRADE.md` §B. The Rust cell has a FIXED number of `FieldElement` slots
(`cell/src/state.rs:STATE_SLOTS`, **16**; it was 8 when this file was written and this header said
so for a while after it was not). The Lean record (`Exec/Value.lean:65`,
`record : List (FieldName × Value)`) is, by contrast, **already an unbounded name-keyed map** — the
cap is a Rust `[FieldElement; STATE_SLOTS]` + circuit artifact, NOT a Lean constraint.

This module adds the Lean witness for the **hybrid** unsqueeze: keep `fields[0..reservedKeys-1]` as
reserved low keys (existing access byte-identical), and commit the **map tail** (keys
`≥ reservedKeys`) under a single `fields_root` = `ListCommit.listDigest` — the SAME accumulator the
side-table roots use (`Circuit/ListCommit.lean`). Strictly additive: no existing `Value`/`scalar`/`setField`
def changes; the keystone `stateStepGuarded_eq` (`EffectsState.lean`) is untouched and lifts
verbatim, because field access here is name-keyed exactly as it already was.

The new content is:
  * `userTail v` — the record fields whose key is a user-map key (`≥ reservedKeys`).
  * `fieldsRoot v` — `ListCommit.listDigest` over `userTail` (the committed root, one circuit column).
  * `fieldsRoot_membership` — reading a user key returns `x` ⟺ `(k,x)` is in the committed tail
    (the present/absent read law). Discharged off `ListCommit`; not a new axiom.
  * the VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): a POSITIVE `#guard` (present key reads its
    value) AND a NEGATIVE `#guard` (absent key does not) — `fields_root := 0` is forbidden; the root
    commits the data (off `ListDigestBindsList` injectivity).

Pure, computable, `#eval`/`#guard`-able (no `native_decide`). Imports `Exec.Program` (for the
name-keyed `Value`/`scalar`) and `Circuit.ListCommit` (the injective accumulator portal).
-/
import Dregg2.Exec.Program
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.ListCommitRegrounded

namespace Dregg2.Exec.FieldsMap

open Dregg2.Circuit.ListCommitRegrounded (ListColl listDigest_binds_of_noColl)
open Dregg2.Exec
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.ListCommit

/-! ## §1 — the reserved/user key split (the hybrid: low keys fixed, tail mapped). -/

/-- ⚑ **16, NOT 8.** This tracks Rust's `cell/src/state.rs::STATE_SLOTS`, which is 16 and has
been since the record-layer upgrade. While this read 8, keys 8..15 were FIXED CELLS in Rust and
COMMITTED USER-MAP TAIL KEYS in Lean — the two `fields_root` preimages split over an eight-key
band, and it was a `def` driving `isUserTailKey` below, not merely a stale comment.

Rust states the boundary three times and all three agree: `STATE_SLOTS = 16`
("Number of user-defined state slots per cell"); `REFUSAL_AUDIT_EXT_KEY` is documented as
`>= STATE_SLOTS` *so that it lands in the committed `fields_map` / `fields_root`, NOT a
user-addressable `fields[0..15]` indexed slot*; and `N_SYSTEM_ROOTS` is "parallel to (and
disjoint from) the 16 user `fields[0..15]` and the `fields_root` map". -/
def reservedKeys : Nat := 16

/-- **`userKey n`** — the canonical `FieldName` for user map key `n` (a numeric key, base-10
encoded). Reserved low keys `0..reservedKeys-1` use the same encoding so the fixed cell `fields[i]`
≡ map key `i` (the §B.2 "fixed cell `idx` = map key `idx`" identity). User-addressable keys are
`n ≥ reservedKeys`. Injective on `Nat` (decimal encoding is injective). -/
def userKey (n : Nat) : FieldName := toString n

/-- **The weld to the heap-keyed constraint atoms**: `Exec.Program`'s `heapKey` (the field name
the `HeapAtom.lift` constraint atoms address) IS this encoding — one canonical heap addressing
across the commitment layer and the constraint language. -/
theorem userKey_eq_heapKey : userKey = Dregg2.Exec.heapKey := rfl

#assert_axioms userKey_eq_heapKey

/-- **`isUserTailKey k`** — `k` names a user-map key `≥ reservedKeys`. A field key is in the
committed tail iff it parses as a numeral `≥ reservedKeys`. Decidable (drives the `#guard`s). -/
def isUserTailKey (k : FieldName) : Bool :=
  match k.toNat? with
  | some n => decide (reservedKeys ≤ n)
  | none   => false

/-- **`witnessKey n`** — the `n`-th key GUARANTEED to lie in the committed user tail, written
relative to the band (`reservedKeys + n`) instead of as a literal. Every `#guard` fixture that means
to exercise the TAIL is keyed with this, here and in the four downstream witness modules, so a
future `reservedKeys` move carries them instead of swallowing them (§5). -/
def witnessKey (n : Nat) : FieldName := userKey (reservedKeys + n)

/-- **`reservedProbeKey`** — the HIGHEST reserved key (`reservedKeys - 1`), also band-relative. A
record keyed here has an EMPTY user tail by construction: it is exactly the shape the pre-2026-07-28
fixtures degenerated into, and §5 tests `separatesOnTail` against it as the negative pole. -/
def reservedProbeKey : FieldName := userKey (reservedKeys - 1)

/-! ## §2 — the user tail + its committed digest (`fields_root`). -/

/-- **`userTail v`** — the record fields whose key is a user-map key (`≥ reservedKeys`), as a
`List (FieldName × Value)`. The reserved low keys `0..reservedKeys-1` (and any non-numeric kernel
fields like `"balance"`) are filtered out — they are carried by the fixed cells, not the map.
Order-preserving on the record's field list. -/
def userTail (v : Value) : List (FieldName × Value) :=
  match v with
  | .record fs => fs.filter (fun p => isUserTailKey p.1)
  | _          => []

/-- **`tailLeaf`** — the injective leaf encoder for a `(key, value)` tail entry. Pairs the key's
decimal `Nat` with the value's canonical scalar/digest/symbol `Int`, packed by a Cantor-style
positional fold so distinct entries get distinct leaves. Reuses the `ListCommit` leaf-encoder
slot; the only carried crypto is `ListCommit`'s injectivity hypotheses (never an axiom). -/
def tailLeaf (compress2 : Int → Int → Int) (p : FieldName × Value) : Int :=
  let kZ : Int := (p.1.toNat?.getD 0 : Int)
  let vZ : Int :=
    match p.2 with
    | .int i  => i
    | .dig d  => (d : Int)
    | .sym s  => (s : Int)
    | .record _ => 0
  compress2 kZ vZ

/-- **`tailPopulated v`** — `v` has a NON-EMPTY committed user tail. Everything a `fields_root`
witness claims to distinguish is carried by the tail; an empty tail digests to the fixed
`emptyTailRoot` for EVERY cell (`fieldsRoot_empty_legacy` below), so a witness over an empty-tail
fixture distinguishes nothing, whatever it computes. Guard the completeness duals with this. -/
def tailPopulated (v : Value) : Bool := !(userTail v).isEmpty

/-- **`separatesOnTail compress2 v w`** — the predicate a tail-separation witness should `#guard`
instead of a bare `≠`: `v` and `w` each carry a POPULATED tail AND their tails DIFFER under the
injective `tailLeaf` projection. FALSE when the two sides coincide, and FALSE when either side's
tail is empty — so a `reservedKeys` bump that swallows a fixture's keys turns the witness RED rather
than leaving it green and toothless (§5). -/
def separatesOnTail (compress2 : Int → Int → Int) (v w : Value) : Bool :=
  tailPopulated v && tailPopulated w
    && !((userTail v).map (tailLeaf compress2) == (userTail w).map (tailLeaf compress2))

/-- **`fieldsRoot compress2 compressN v`** — the committed digest of the user-field MAP: the
`ListCommit.listDigest` over `userTail v` under the `tailLeaf` encoder. This is the SINGLE root
column the circuit carries instead of 8 value columns; the side-table roots use the same
`listDigest` mechanism (`_RECORD-LAYER-UPGRADE.md` §B.4). A legacy cell with no user keys has
`userTail = []`, so its `fields_root` is the FIXED empty-tail digest `compressN []` — a constant,
independent of the cell — which is why legacy commitments are unchanged (§2 backward-compat). -/
def fieldsRoot (compress2 : Int → Int → Int) (compressN : List Int → Int) (v : Value) : Int :=
  listDigest (tailLeaf compress2) compressN (userTail v)

/-- **`emptyTailRoot`** — the fixed `fields_root` of a cell with no user-map keys: `compressN []`.
A legacy cell's `fields_root` is provably exactly this constant (next lemma), so folding it into a
commitment is a no-op for legacy cells (the Stage 0 backward-compat keystone). -/
def emptyTailRoot (compressN : List Int → Int) : Int := compressN []

/-- **`fieldsRoot_empty_legacy`** — a record with NO user-tail keys (every key is reserved
/ non-numeric, i.e. a legacy 8-fixed-field cell) has `fields_root = emptyTailRoot`, the fixed
constant. This is the Stage 0 backward-compat keystone in Lean: legacy cells' `fields_root` does
not depend on the cell, so absorbing it into any commitment leaves legacy commitments UNCHANGED. -/
theorem fieldsRoot_empty_legacy (compress2 : Int → Int → Int) (compressN : List Int → Int)
    (fs : List (FieldName × Value)) (h : fs.filter (fun p => isUserTailKey p.1) = []) :
    fieldsRoot compress2 compressN (.record fs) = emptyTailRoot compressN := by
  unfold fieldsRoot userTail emptyTailRoot listDigest
  simp only [h, List.map_nil]

/-! ## §3 — the membership read law (present/absent), discharged off `ListCommit`. -/

/-- **`tailLookup v k`** — read user-map key `k` out of the committed tail: the value `(k, x)` if
present, else `none`. The map-side analog of `Value.scalar`; agrees with `Value.field` restricted to
the user tail. -/
def tailLookup (v : Value) (k : FieldName) : Option Value :=
  ((userTail v).find? (fun p => p.1 == k)).map (·.2)

/-- **`fieldsRoot_membership` (the §B.4 read law).** A user-map key `k` reads value `x` out
of the committed tail (`tailLookup v k = some x`) **iff** the FIRST tail entry keyed `k` is `(k, x)`.
Reading IS membership against the committed tail (`userTail v` — the list the `fields_root` digest
commits): a present key returns its committed value, an absent key returns `none`. The digest's
injectivity (`fieldsRoot_binds_tail`, off `ListDigestBindsList`) then guarantees two records with the
SAME `fields_root` have the SAME tail, so the read-back value is committed (no `:= 0` stub
survives). -/
theorem fieldsRoot_membership (v : Value) (k : FieldName) (x : Value) :
    tailLookup v k = some x ↔ (userTail v).find? (fun p => p.1 == k) = some (k, x) := by
  unfold tailLookup
  constructor
  · intro h
    cases hf : (userTail v).find? (fun p => p.1 == k) with
    | none => rw [hf] at h; simp at h
    | some p =>
        obtain ⟨a, b⟩ := p
        rw [hf] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hk : a = k := by simpa using List.find?_some hf
        subst h; subst hk; rfl
  · intro h; rw [h]; rfl

/-- **Binding corollary (⚙ S3 CUTOVER)** — two records whose `fields_root` agree have the SAME
user tail, hence read back the SAME value at every user key — under the per-instance `¬ ListColl`
side condition at the named tail pair (endpoint `ListCommitRegrounded.listDigest_binds_of_noColl`;
the refuted universal-injectivity floors are GONE from this statement). This is the
"the root commits the data" guarantee that rules out a `:= 0` stub. -/
theorem fieldsRoot_binds_tail (compress2 : Int → Int → Int) (compressN : List Int → Int)
    (v w : Value) (h : fieldsRoot compress2 compressN v = fieldsRoot compress2 compressN w)
    (hno : ¬ ListColl (tailLeaf compress2) compressN (userTail v) (userTail w)) :
    userTail v = userTail w :=
  listDigest_binds_of_noColl (tailLeaf compress2) compressN _ _ hno h

/-! ## §4 — VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): pos + neg, no `native_decide`. -/

-- A concrete pair of cells to exercise membership: a legacy cell (keys 0,7 reserved) plus a cell
-- that overflows onto the first two USER-map keys. Those keys are `witnessKey 0`/`witnessKey 1`,
-- NOT literals: they were literal `"8"`/`"9"` until `reservedKeys` moved 8 → 16 underneath them.
private def legacyCell : Value :=
  .record [("0", .int 11), ("7", .int 99), ("balance", .int 500)]
private def overflowCell : Value :=
  .record [("0", .int 11), ("7", .int 99), (witnessKey 0, .int 1234), (witnessKey 1, .dig 42)]

-- `Value` carries no `BEq`, so read-back is checked via the canonical `Int` leaf of the looked-up
-- value (and `isSome`/`isNone` for presence). This is the same encoding `tailLeaf` commits.
private def valInt : Value → Int
  | .int i => i | .dig d => (d : Int) | .sym s => (s : Int) | .record _ => 0
private def tailLookupInt (v : Value) (k : FieldName) : Option Int := (tailLookup v k).map valInt

-- POSITIVE: a present user key reads exactly its value out of the committed tail.
#guard tailLookupInt overflowCell (witnessKey 0) == some 1234
#guard tailLookupInt overflowCell (witnessKey 1) == some 42

-- NEGATIVE: an ABSENT user key does NOT read a value (the tail does not commit it).
#guard (tailLookup overflowCell (witnessKey 2)).isNone
#guard (tailLookup legacyCell (witnessKey 0)).isNone

-- The user tail filters out reserved low keys and the `balance` field (carried by fixed cells):
#guard (userTail overflowCell).map (fun p => (p.1, valInt p.2))
         == [(witnessKey 0, (1234 : Int)), (witnessKey 1, 42)]
#guard (userTail legacyCell).isEmpty   -- a legacy fixed-field-only cell has an EMPTY user tail.
#guard tailPopulated overflowCell      -- ...and the overflow cell's tail is POPULATED (§5).

-- BACKWARD-COMPAT: a legacy cell's `fields_root` equals the fixed empty-tail constant, INDEPENDENT
-- of the cell — so absorbing it into a commitment leaves legacy commitments unchanged.
private def cNC : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)
private def c2C : Int → Int → Int := fun a b => a * 1000003 + b

#guard decide (fieldsRoot c2C cNC legacyCell = emptyTailRoot cNC)               -- legacy = empty const
#guard decide (fieldsRoot c2C cNC (.record [("balance", .int 7)]) = emptyTailRoot cNC) -- another legacy
-- ANTI-VACUITY: a cell WITH user-map data has a root DIFFERENT from the empty-tail constant
-- (a `:= 0`/empty stub would collapse this — forbidden).
#guard decide (fieldsRoot c2C cNC overflowCell = emptyTailRoot cNC) == false
-- A tampered user value flips the root (the digest commits the map tail):
private def overflowTampered : Value :=
  .record [("0", .int 11), ("7", .int 99), (witnessKey 0, .int 9999), (witnessKey 1, .dig 42)]
#guard separatesOnTail c2C overflowCell overflowTampered   -- §5: the tamper MOVES a populated tail
#guard decide (fieldsRoot c2C cNC overflowCell = fieldsRoot c2C cNC overflowTampered) == false
-- Two cells with the SAME user tail have the SAME root (completeness dual). The `tailPopulated`
-- guard is what stops this from passing on `[] = []` after a `reservedKeys` move (§5).
#guard tailPopulated (.record [(witnessKey 0, .int 1234), (witnessKey 1, .dig 42)])
#guard decide (fieldsRoot c2C cNC overflowCell
             = fieldsRoot c2C cNC (.record [(witnessKey 0, .int 1234), (witnessKey 1, .dig 42)]))

/-! ## §5 — WITNESS HYGIENE: band-relative fixture keys, and the guard that REDS when a witness
stops separating.

⚑ Why this section exists, measured 2026-07-28. `reservedKeys` moved 8 → 16 (§1: the Lean band had
been behind Rust's `STATE_SLOTS`). Four downstream modules carried their non-vacuity / anti-ghost
teeth on records keyed `"8"` — `Exec/RecordCommit §4`, `Circuit/CommitmentCrossBind §5`,
`Verify/ReceiptContract §4a`, `Circuit/Argus/Receipt §4`. Under the corrected band those keys are
FIXED CELLS, so both sides of every distinction acquired an EMPTY user tail, `fieldsRoot` collapsed
to the cell-independent `emptyTailRoot` on both, and:

  * the SEPARATING guards went red (three in `RecordCommit`, and the rest behind them in the
    dependency order) — visible, and the reason this file is being read;
  * the COMPLETENESS DUALS kept passing, now comparing `[] = []`. That is the dangerous half: a
    witness that no longer distinguishes anything but still reports green.

Both halves are the same class — a witness whose two sides coincide. `witnessKey`/`reservedProbeKey`
(§1) and `tailPopulated`/`separatesOnTail` (§2) remove it in both directions: fixtures are written
RELATIVE to the band, so a future bump CARRIES them instead of swallowing them, and a separation
guard is FALSE when a side's tail is empty, so a degenerate witness REDS rather than passing on
nothing. The `#guard`s below are the guard's own teeth: it must accept a real separation and refuse
BOTH degeneracies. -/

-- The band-relative keys land on the right side of the split, and the reserved probe does not.
#guard isUserTailKey (witnessKey 0) && isUserTailKey (witnessKey 1)
#guard isUserTailKey reservedProbeKey == false
#guard tailPopulated (.record [(witnessKey 0, .int 50)])
#guard tailPopulated (.record [(reservedProbeKey, .int 50)]) == false

-- POSITIVE pole: a genuine tail separation passes.
#guard separatesOnTail c2C (.record [(witnessKey 0, .int 50)]) (.record [(witnessKey 0, .int 999)])
-- NEGATIVE pole — THE 2026-07-28 CLASS, caught in the act: two records that plainly DIFFER, on a
-- RESERVED key. Their tails are both empty; the old witness shape would compare `[] ≠ []`. REFUSED.
#guard separatesOnTail c2C (.record [(reservedProbeKey, .int 50)])
                           (.record [(reservedProbeKey, .int 999)]) == false
-- NEGATIVE pole — the ordinary way to fail to separate: the two sides coincide on a populated tail.
#guard separatesOnTail c2C (.record [(witnessKey 0, .int 50)])
                           (.record [(witnessKey 0, .int 50)]) == false

#assert_axioms fieldsRoot_membership
#assert_axioms fieldsRoot_empty_legacy
#assert_axioms fieldsRoot_binds_tail

end Dregg2.Exec.FieldsMap
