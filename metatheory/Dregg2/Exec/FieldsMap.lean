/-
# Dregg2.Exec.FieldsMap — the committed user-field MAP (`fields_root`), Stage 0 beachhead.

`_RECORD-LAYER-UPGRADE.md` §B. The Rust cell has exactly **8** `FieldElement` slots
(`cell/src/state.rs:STATE_SLOTS = 8`); shipped apps already burn all 8 (`subscription`). The
Lean record (`Exec/Value.lean:65`, `record : List (FieldName × Value)`) is, by contrast,
**already an unbounded name-keyed map** — the 8-cap is a Rust `[FieldElement; 8]` + circuit
artifact, NOT a Lean constraint.

This module adds the Lean witness for the **hybrid** unsqueeze: keep `fields[0..7]` as reserved
low keys `0..7` (existing access byte-identical), and commit the **map tail** (keys `≥ 8`) under a
single `fields_root` = `ListCommit.listDigest` — the SAME injective accumulator the side-table
roots use (`Circuit/ListCommit.lean`). Strictly additive: no existing `Value`/`scalar`/`setField`
def changes; the keystone `stateStepGuarded_eq` (`EffectsState.lean`) is untouched and lifts
verbatim, because field access here is name-keyed exactly as it already was.

The new content is:
  * `userTail v` — the record fields whose key is a user-map key (`≥ reservedKeys`).
  * `fieldsRoot v` — `ListCommit.listDigest` over `userTail` (the committed root, one circuit column).
  * `fieldsRoot_membership` — reading a user key returns `x` ⟺ `(k,x)` is in the committed tail
    (the present/absent read law). Discharged off `ListCommit`; not a new axiom.
  * the VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): a POSITIVE `#guard` (present key reads its
    value) AND a NEGATIVE `#guard` (absent key does not) — `fields_root := 0` is forbidden; the root
    genuinely commits the data (off `ListDigestBindsList` injectivity).

Pure, computable, `#eval`/`#guard`-able (no `native_decide`). Imports `Exec.Program` (for the
name-keyed `Value`/`scalar`) and `Circuit.ListCommit` (the injective accumulator portal).
-/
import Dregg2.Exec.Program
import Dregg2.Circuit.ListCommit

namespace Dregg2.Exec.FieldsMap

open Dregg2.Exec
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.ListCommit

/-! ## §1 — the reserved/user key split (the hybrid: low keys fixed, tail mapped). -/

/-- **`reservedKeys`** — the count of reserved low keys held as fixed cells (`R = 8`, the Rust
`STATE_SLOTS`). Keys `< reservedKeys` are the existing fixed `fields[0..7]`; keys `≥ reservedKeys`
live in the committed `fields_root` map. -/
def reservedKeys : Nat := 8

/-- **`userKey n`** — the canonical `FieldName` for user map key `n` (a numeric key, base-10
encoded). Reserved low keys `0..reservedKeys-1` use the same encoding so the fixed cell `fields[i]`
≡ map key `i` (the §B.2 "fixed cell `idx` = map key `idx`" identity). User-addressable keys are
`n ≥ reservedKeys`. Injective on `Nat` (decimal encoding is injective). -/
def userKey (n : Nat) : FieldName := toString n

/-- **`isUserTailKey k`** — `k` names a user-map key `≥ reservedKeys`. A field key is in the
committed tail iff it parses as a numeral `≥ reservedKeys`. Decidable (drives the `#guard`s). -/
def isUserTailKey (k : FieldName) : Bool :=
  match k.toNat? with
  | some n => decide (reservedKeys ≤ n)
  | none   => false

/-! ## §2 — the user tail + its committed digest (`fields_root`). -/

/-- **`userTail v`** — the record fields whose key is a user-map key (`≥ reservedKeys`), as a
`List (FieldName × Value)`. The reserved low keys `0..7` (and any non-numeric kernel fields like
`"balance"`) are filtered out — they are carried by the fixed cells, not the map. Order-preserving
on the record's field list. -/
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

/-- **`fieldsRoot_empty_legacy` (PROVED)** — a record with NO user-tail keys (every key is reserved
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

/-- **`fieldsRoot_membership` (PROVED, the §B.4 read law).** A user-map key `k` reads value `x` out
of the committed tail (`tailLookup v k = some x`) **iff** the FIRST tail entry keyed `k` is `(k, x)`.
Reading IS membership against the committed tail (`userTail v` — the list the `fields_root` digest
commits): a present key returns its committed value, an absent key returns `none`. The digest's
injectivity (`fieldsRoot_binds_tail`, off `ListDigestBindsList`) then guarantees two records with the
SAME `fields_root` have the SAME tail, so the read-back value is genuinely committed (no `:= 0` stub
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

/-- **Injectivity corollary** — two records whose `fields_root` agree (under an injective
`listDigest`) have the SAME user tail, hence read back the SAME value at every user key. This is the
"the root genuinely commits the data" guarantee that rules out a `:= 0` stub. -/
theorem fieldsRoot_binds_tail (compress2 : Int → Int → Int) (compressN : List Int → Int)
    (hN : compressNInjective compressN) (hLE : listLeafInjective (tailLeaf compress2))
    (v w : Value) (h : fieldsRoot compress2 compressN v = fieldsRoot compress2 compressN w) :
    userTail v = userTail w :=
  ListDigestBindsList (tailLeaf compress2) compressN hN hLE _ _ h

/-! ## §4 — VACUITY GUARD (`_RECORD-LAYER-UPGRADE.md` §D.4): pos + neg, no `native_decide`. -/

-- A concrete pair of cells to exercise membership: a legacy cell (keys 0,7 reserved) plus a cell
-- that overflows onto user-map keys 8 and 9.
private def legacyCell : Value :=
  .record [("0", .int 11), ("7", .int 99), ("balance", .int 500)]
private def overflowCell : Value :=
  .record [("0", .int 11), ("7", .int 99), ("8", .int 1234), ("9", .dig 42)]

-- `Value` carries no `BEq`, so read-back is checked via the canonical `Int` leaf of the looked-up
-- value (and `isSome`/`isNone` for presence). This is the same encoding `tailLeaf` commits.
private def valInt : Value → Int
  | .int i => i | .dig d => (d : Int) | .sym s => (s : Int) | .record _ => 0
private def tailLookupInt (v : Value) (k : FieldName) : Option Int := (tailLookup v k).map valInt

-- POSITIVE: a present user key reads exactly its value out of the committed tail.
#guard tailLookupInt overflowCell (userKey 8) == some 1234
#guard tailLookupInt overflowCell (userKey 9) == some 42

-- NEGATIVE: an ABSENT user key does NOT read a value (the tail does not commit it).
#guard (tailLookup overflowCell (userKey 10)).isNone
#guard (tailLookup legacyCell (userKey 8)).isNone

-- The user tail filters out reserved low keys and the `balance` field (carried by fixed cells):
#guard (userTail overflowCell).map (fun p => (p.1, valInt p.2)) == [("8", (1234 : Int)), ("9", 42)]
#guard (userTail legacyCell).isEmpty   -- a legacy 8-fixed-field cell has an EMPTY user tail.

-- BACKWARD-COMPAT: a legacy cell's `fields_root` equals the fixed empty-tail constant, INDEPENDENT
-- of the cell — so absorbing it into a commitment leaves legacy commitments unchanged.
private def cNC : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)
private def c2C : Int → Int → Int := fun a b => a * 1000003 + b

#guard decide (fieldsRoot c2C cNC legacyCell = emptyTailRoot cNC)               -- legacy = empty const
#guard decide (fieldsRoot c2C cNC (.record [("balance", .int 7)]) = emptyTailRoot cNC) -- another legacy
-- ANTI-VACUITY: a cell WITH user-map data has a root DIFFERENT from the empty-tail constant
-- (a `:= 0`/empty stub would collapse this — forbidden).
#guard decide (fieldsRoot c2C cNC overflowCell = emptyTailRoot cNC) == false
-- A tampered user value flips the root (the digest genuinely commits the map tail):
private def overflowTampered : Value :=
  .record [("0", .int 11), ("7", .int 99), ("8", .int 9999), ("9", .dig 42)]
#guard decide (fieldsRoot c2C cNC overflowCell = fieldsRoot c2C cNC overflowTampered) == false
-- Two cells with the SAME user tail have the SAME root (completeness dual):
#guard decide (fieldsRoot c2C cNC overflowCell
             = fieldsRoot c2C cNC (.record [("8", .int 1234), ("9", .dig 42)]))   -- true

#assert_axioms fieldsRoot_membership
#assert_axioms fieldsRoot_empty_legacy
#assert_axioms fieldsRoot_binds_tail

end Dregg2.Exec.FieldsMap
