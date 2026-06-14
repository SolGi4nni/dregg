/-
# Dregg2.Exec.Collections — NAMED COLLECTIONS + AGGREGATE predicates (the data-model rung).

**The "screaming toy" fix: a cell can model REAL data (named fields, COLLECTIONS) and predicate
over them, instead of hand-rolling per-index slot names (`q0`,`q1`,`q2`,…) or being capped at the
fixed-slot ceiling.** Today the cell-program language (`Exec.Program`) reads ONE named scalar field
at a time; a quorum is either a hand-enumerated `anyOf [senderIs a, senderIs b, …]` (which an N-member
board widens BY HAND each time a member joins — `docs/CELL-PROGRAM-LANGUAGE.md` gap 9) or the
`countGe` witnessed-set atom (a committed blob, not the cell's OWN named data). The
`QuantifiedPredicate` bounded-∀/∃ already folds a per-INDEX family `P : ι → RelPred` — but the
collection it ranges over is IMPLICIT in the per-index name construction `s!"q{i}"`; there is no
first-class COLLECTION the program references by NAME.

This module adds that rung, fully ADDITIVELY (`Exec.Value`/`Exec.Program` untouched):

  * **`Collection := List Value`** — a named, ordered collection of ELEMENT records (an approver
    list, an order book, a queue of entries). It is read out of the record substrate by NAME
    (`Value.collectionField`), the data-model dual of `Value.scalar` reading one field; the
    canonical on-chain home of a large collection is the cell's `heap_root` openable sorted-Poseidon2
    map (`Substrate.Heap` — cited, not imported: this module is state-free), with a small inline
    collection living directly under a named record field. Each ELEMENT is itself a record read by
    field NAME (`elemScalar`/`elemSym`), so the language references the data by name end-to-end.

  * **Aggregate / quantified predicates over a collection** (`CollPred`): `countSatGe` (≥ m elements
    satisfy a per-element predicate — in-data M-of-N), `sumOfLe`/`sumOfGe` (Σ of a named element
    field is bounded — a treasury/supply cap), `allMembers` (∀ element P — every entry obeys the
    invariant), `existsMember` (∃ element P — some entry matches). Each is a decidable `Bool`
    function of the collection ALONE (collection-local, the `flatten`/`RelPred.eval` record-locality
    discipline lifted to the collection), fail-closed.

  * **THE COUNCIL LIFT — arbitrary-N M-of-N**: `mOfNDistinct m keyField approved` = "≥ m elements
    whose `keyField` identities are DISTINCT satisfy `approved`". This is the council gate at ANY N —
    the N≤3 fixed-slot cap (`docs/CELL-PROGRAM-LANGUAGE.md` gaps 7/11.1, the documented lamesauce) is
    a SLOT-LAYOUT artifact, and a collection has no fixed width. The DISTINCTNESS is structural
    (`eraseDups` on the key field — the `countGe` anti-fake design): a DUPLICATE-PADDED forge (the
    same approver listed `m` times) collapses to ONE distinct key and REFUSES; an UNBOUND forge (a
    padding element that does not actually approve) fails `approved` and REFUSES. Both biting teeth,
    both polarities, no laundered vacuity.

  * **§NON-VACUITY** — a concrete 3-of-5 council: 3 distinct approvers ACCEPT; a sub-quorum (2)
    REFUSES; a duplicate-padded forge (one approver listed 3×) REFUSES; an unbound forge (a non-member
    padding element) REFUSES. Each a `decide` witness AND a proved theorem.

LAW #1: emitted from Lean. NEW file only — does NOT edit `Exec.Value`, `Exec.Program`,
`Authority.QuantifiedPredicate`, `Substrate.Heap`, or `Dregg2.lean`. Reuses `Exec.Value.scalar`
(the fail-closed named-field reader) and `Exec.Value.field`. Every keystone `#assert_axioms`-pinned —
no sorry, no `:= True`, no `native_decide`.
-/
import Dregg2.Exec.Program
import Dregg2.Tactics

namespace Dregg2.Exec.Collections

open Dregg2.Exec

/-! ## §0 — `eraseDups` plumbing lemmas (the distinctness machinery).

The distinct-approver count rides `List.eraseDups` (the `decide`-reducible `BEq` dedup `Program.lean`'s
`countGe` already uses). Lean core ships its `mem`/`cons` lemmas but not the `Nodup`/`Sublist`/`length`
facts the council teeth need (those are Mathlib's, only for the `DecidableEq` `dedup`), so we prove the
three over `eraseDups` from the core `eraseDups_cons`/`mem_eraseDups`, plus a `filterMap` length bound.
General over any `LawfulBEq`; instantiated at `Nat` (the approver-id key type). -/

/-- `l.eraseDups` is a SUBLIST of `l` (the dedup only drops elements). -/
theorem eraseDups_sublist' {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.Sublist l
  | [] => by simp
  | a :: t => by
      rw [List.eraseDups_cons]
      refine List.Sublist.cons_cons a ?_
      exact (eraseDups_sublist' _).trans (List.filter_sublist)
  termination_by l => l.length
  decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- `l.eraseDups` is no longer than `l` (a dedup never grows the list). -/
theorem length_eraseDups_le' {α : Type _} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length ≤ l.length :=
  (eraseDups_sublist' l).length_le

/-- `l.eraseDups` has NO duplicates — the distinctness the council quorum relies on. -/
theorem nodup_eraseDups' {α : Type _} [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.Nodup
  | [] => by simp
  | a :: t => by
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, nodup_eraseDups' _⟩
      rw [List.mem_eraseDups]; intro hmem; rw [List.mem_filter] at hmem
      obtain ⟨_, hb⟩ := hmem; simp at hb
  termination_by l => l.length
  decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- `l.filterMap f` is no longer than `l` (each element contributes at most one). -/
theorem length_filterMap_le' {α β : Type _} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons]
    cases f a with
    | none   => simpa using Nat.le_succ_of_le ih
    | some b => simp; omega

/-! ## §1 — The collection abstraction: a named, ordered list of element records.

A **`Collection`** is `List Value` — an ordered collection of ELEMENT records. It is read out of a
cell's record state by NAME, the data-model dual of `Value.scalar` reading one scalar field. A
collection lives EITHER directly under a named record field (a small inline collection, modeled as a
sub-record whose successive index keys `"0"`,`"1"`,… hold the elements — the in-record realization)
OR in the cell's `heap_root` openable sorted-Poseidon2 map for large collections (the `Substrate.Heap`
precedent, cited here, opened by the circuit's gates — this module stays state-free). Either way the
program names the collection and aggregates over it; element fields are read BY NAME. -/

/-- **`Collection`** — an ordered list of element `Value`s (an approver list, an order book, a queue).
The first-class collection the cell-program language references by name. -/
abbrev Collection := List Value

/-- Read the contiguous index-keyed elements `"i"`, `"i+1"`, … out of an element-record `elems`,
stopping at the first absent index. `fuel` bounds the recursion at the field count (no element index
exceeds it). A top-level structural recursion on `fuel` so `decide` reduces it. -/
def readIndexed (elems : Value) (i : Nat) : Nat → Collection
  | 0          => []
  | fuel' + 1  =>
      match elems.field (toString i) with
      | some e => e :: readIndexed elems (i + 1) fuel'
      | none   => []

/-- **`collectionField v name`** — read the collection stored under the named field `name` as the
ordered list of its index-keyed elements `"0"`, `"1"`, `"2"`, … (the in-record realization of a
collection: a sub-record whose keys are the decimal indices). Stops at the first absent index, so the
collection is exactly the contiguous prefix present (a hole TRUNCATES — fail-closed: a collection
cannot have a phantom tail beyond a gap). `none` if `name` is absent or not a record. The data-model
dual of `Value.scalar`; the canonical large-collection home is the heap (`Substrate.Heap`), this is
the small inline form.

Declared on the `Dregg2.Exec.Value` namespace so it dot-projects on a `Value` (`v.collectionField`). -/
def _root_.Dregg2.Exec.Value.collectionField (v : Value) (name : FieldName) : Option Collection :=
  match v.field name with
  | some (.record fs) => some (readIndexed (.record fs) 0 fs.length)
  | _ => none

/-! ## §2 — Element field access (the data is named END-TO-END).

Each ELEMENT of a collection is itself a record; its fields are read BY NAME — exactly
`Value.scalar`/`Value.field` lifted to an element. So `coll[i].approved` is `elemScalar (coll[i])
"approved"`, never a bit position. -/

/-- **`elemScalar e f`** — read named scalar field `f` of element record `e` (`Value.scalar` on the
element; fail-closed `none` if absent/ill-typed). The element's data is read by NAME. -/
def elemScalar (e : Value) (f : FieldName) : Option Int := e.scalar f

/-- **`elemSym e f`** — read named field `f` of element `e` as an interned identity (`Value.sym`,
the approver/member id key). `none` if absent or not a symbol. Fail-closed. -/
def elemSym (e : Value) (f : FieldName) : Option Nat :=
  match e.field f with
  | some (.sym s) => some s
  | _             => none

/-! ## §3 — Aggregate / quantified predicates over a collection (`CollPred`).

A **per-element predicate** `ElemPred := Value → Bool` decides one element (built from `elemScalar`
/`elemSym`; e.g. "this element's `approved` field is 1", "this order's `price` ≤ band"). The
aggregates fold it over the collection:

  * `countSat` — HOW MANY elements satisfy it (the M-of-N count statistic).
  * `sumOfField` — Σ of a named element field (a treasury/supply total).
  * `allMembers` / `existsMember` — bounded ∀/∃ over the collection (the `QuantifiedPredicate`
    fold, here over a FIRST-CLASS collection rather than a per-index name family).

These are decidable `Bool` functions of the collection ALONE (collection-local). -/

/-- A per-element decision predicate (built from `elemScalar`/`elemSym`). -/
abbrev ElemPred := Value → Bool

/-- **`countSat p coll`** — the number of elements of `coll` satisfying `p` (the count statistic
behind in-data M-of-N). `List.countP`. -/
def countSat (p : ElemPred) (coll : Collection) : Nat := coll.countP p

/-- **`sumOfField f coll`** — Σ of named scalar field `f` over the elements (absent/ill-typed reads
contribute `0` — total, like the relational closure's `fieldOf`; a missing element field does not
abort the aggregate, it just adds nothing). A treasury balance, a token supply, a vote weight total. -/
def sumOfField (f : FieldName) (coll : Collection) : Int :=
  (coll.map (fun e => (elemScalar e f).getD 0)).foldr (· + ·) 0

/-- **`collAll p coll`** — bounded universal `∀ e ∈ coll, p e` (`List.all`). Every entry obeys the
invariant. The first-class-collection form of `QuantifiedPredicate.forall_` (the `CollPred.allMembers`
shape's evaluator). -/
def collAll (p : ElemPred) (coll : Collection) : Bool := coll.all p

/-- **`collAny p coll`** — bounded existential `∃ e ∈ coll, p e` (`List.any`). Some entry matches. The
first-class-collection form of `QuantifiedPredicate.exists_` (the `CollPred.existsMember` evaluator). -/
def collAny (p : ElemPred) (coll : Collection) : Bool := coll.any p

/-- **`CollPred`** — the AGGREGATE predicate fragment over a collection. Each shape is a decidable
`Bool` function of the collection, fail-closed. The data-model dual of the per-field `StateConstraint`
catalog: where `StateConstraint` predicates over ONE named field, `CollPred` predicates over a named
COLLECTION. -/
inductive CollPred where
  /-- **≥ m elements satisfy `p`** — the in-data M-of-N count statistic (NOT distinct; the distinct
  council gate is `mOfNDistinct` below). -/
  | countSatGe (m : Nat) (p : ElemPred)
  /-- **Σ of named field `f` ≤ bound** — a treasury/supply ceiling over the collection. -/
  | sumOfLe    (f : FieldName) (bound : Int)
  /-- **Σ of named field `f` ≥ bound** — a treasury/supply floor over the collection. -/
  | sumOfGe    (f : FieldName) (bound : Int)
  /-- **∀ element, `p`** — every entry obeys the invariant (bounded universal). -/
  | allMembers (p : ElemPred)
  /-- **∃ element, `p`** — some entry matches (bounded existential). -/
  | existsMember (p : ElemPred)

/-- **`CollPred.eval cp coll`** — the decidable evaluator over the collection. Fail-closed by
construction. -/
def CollPred.eval : CollPred → Collection → Bool
  | .countSatGe m p,   coll => decide (m ≤ countSat p coll)
  | .sumOfLe f bound,  coll => decide (sumOfField f coll ≤ bound)
  | .sumOfGe f bound,  coll => decide (bound ≤ sumOfField f coll)
  | .allMembers p,     coll => collAll p coll
  | .existsMember p,   coll => collAny p coll

/-! ## §3.1 — Aggregate admit-characterizations (each PROVED). -/

/-- **`countSatGe` admit-char.** Admits IFF at least `m` elements satisfy `p`. -/
theorem eval_countSatGe_iff (m : Nat) (p : ElemPred) (coll : Collection) :
    (CollPred.countSatGe m p).eval coll = true ↔ m ≤ countSat p coll := by
  simp [CollPred.eval]

/-- **`sumOfLe` admit-char.** Admits IFF the named-field sum is ≤ the bound. -/
theorem eval_sumOfLe_iff (f : FieldName) (bound : Int) (coll : Collection) :
    (CollPred.sumOfLe f bound).eval coll = true ↔ sumOfField f coll ≤ bound := by
  simp [CollPred.eval]

/-- **`sumOfGe` admit-char.** Admits IFF the named-field sum is ≥ the bound. -/
theorem eval_sumOfGe_iff (f : FieldName) (bound : Int) (coll : Collection) :
    (CollPred.sumOfGe f bound).eval coll = true ↔ bound ≤ sumOfField f coll := by
  simp [CollPred.eval]

/-- **`allMembers` admit-char.** Admits IFF EVERY element satisfies `p` (`List.all_eq_true`). -/
theorem eval_allMembers_iff (p : ElemPred) (coll : Collection) :
    (CollPred.allMembers p).eval coll = true ↔ ∀ e ∈ coll, p e = true := by
  simp [CollPred.eval, collAll]

/-- **`existsMember` admit-char.** Admits IFF SOME element satisfies `p` (`List.any_eq_true`). -/
theorem eval_existsMember_iff (p : ElemPred) (coll : Collection) :
    (CollPred.existsMember p).eval coll = true ↔ ∃ e ∈ coll, p e = true := by
  simp [CollPred.eval, collAny]

/-- **`countSat` is bounded by the collection size** — a count can never exceed N
(`List.countP_le_length`). So an M-of-N with `m > N` is UNSATISFIABLE: you cannot fake more satisfying
elements than the collection has. -/
theorem countSat_le_size (p : ElemPred) (coll : Collection) : countSat p coll ≤ coll.length :=
  List.countP_le_length

/-! ## §4 — THE COUNCIL LIFT: arbitrary-N M-of-N over a collection, distinctness-enforced.

The council gate at ANY N. An approver list is a `Collection`; each element carries an identity field
(`keyField`, e.g. `"voter"`, a `sym`) and an approval predicate (`approved`, e.g. "this element's
`vote` field is 1"). `mOfNDistinct m keyField approved` admits IFF at least `m` elements that BOTH
satisfy `approved` AND carry DISTINCT `keyField` identities are present.

WHY THE DISTINCTNESS IS LOAD-BEARING (the anti-fake teeth, the `countGe` discipline): a naive
`countSatGe m approved` over the collection would be FOOLED by a DUPLICATE-PADDED forge — list the same
approver `m` times and the count hits `m` from ONE real approval. `mOfNDistinct` counts DISTINCT
identities (`eraseDups` on the satisfying elements' key fields), so a duplicate-padded forge collapses
to ONE distinct key and REFUSES. An UNBOUND forge (a padding element that does NOT satisfy `approved`)
is filtered out before the count, so it cannot inflate the quorum either. Both biting teeth.

The N≤3 fixed-slot cap (`docs/CELL-PROGRAM-LANGUAGE.md` gaps 7/11.1, the documented lamesauce) was a
SLOT-LAYOUT artifact — `STATE_SLOTS = 16` baked the approval array; a `Collection` has no fixed width,
so the SAME gate serves a council of 3, 7, or 70. -/

/-- **`distinctApproverKeys keyField approved coll`** — the list of DISTINCT identity keys among the
elements that satisfy `approved`. Filters to the approving elements, reads each one's `keyField`
identity (dropping any whose key is absent/ill-typed — fail-closed: an approval with no identity does
NOT count), then `eraseDups` so a repeated identity is counted ONCE. The distinct-approver multiset
the quorum measures. -/
def distinctApproverKeys (keyField : FieldName) (approved : ElemPred) (coll : Collection) :
    List Nat :=
  ((coll.filter approved).filterMap (fun e => elemSym e keyField)).eraseDups

/-- **`mOfNDistinct m keyField approved`** — the arbitrary-N M-of-N council gate: ≥ `m` DISTINCT
identities approve. Admits IFF `distinctApproverKeys` has length ≥ `m`. The duplicate-padded forge
collapses (one distinct key); the unbound forge is filtered (fails `approved`). -/
def mOfNDistinct (m : Nat) (keyField : FieldName) (approved : ElemPred) (coll : Collection) : Bool :=
  decide (m ≤ (distinctApproverKeys keyField approved coll).length)

/-- **`mOfNDistinct` admit-char (the council keystone).** Admits IFF at least `m` DISTINCT approver
identities are present among the satisfying elements. The quorum is over DISTINCT identities, so it is
the genuine M-of-N. -/
theorem mOfNDistinct_iff (m : Nat) (keyField : FieldName) (approved : ElemPred) (coll : Collection) :
    mOfNDistinct m keyField approved coll = true ↔
      m ≤ (distinctApproverKeys keyField approved coll).length := by
  simp [mOfNDistinct]

/-- **`mOfNDistinct_sound` (the consumable quorum bound).** An admitted council gate YIELDS the
distinct-quorum bound — the form an app keystone consumes (the `MultisigVote` tally point, here purely
in the cell-program data layer). -/
theorem mOfNDistinct_sound (m : Nat) (keyField : FieldName) (approved : ElemPred) (coll : Collection)
    (h : mOfNDistinct m keyField approved coll = true) :
    m ≤ (distinctApproverKeys keyField approved coll).length :=
  (mOfNDistinct_iff m keyField approved coll).mp h

/-- **`distinct_keys_nodup` (the distinctness is REAL).** The distinct-approver key list has NO
duplicates (`List.nodup_eraseDups`). So the quorum genuinely counts distinct identities — a
duplicate-padded approver list cannot inflate it. -/
theorem distinct_keys_nodup (keyField : FieldName) (approved : ElemPred) (coll : Collection) :
    (distinctApproverKeys keyField approved coll).Nodup :=
  nodup_eraseDups' _

/-- **`mOfNDistinct_le_countSat` (the duplicate-padding TOOTH, structurally).** The distinct-approver
count NEVER exceeds the raw satisfying-count — and is STRICTLY smaller exactly when duplicates or
keyless approvals are padded in. So a forge that pads `approved` elements to hit a raw count of `m`
does NOT get a distinct count of `m` unless the identities are genuinely distinct: distinctness is the
binding gate. (The bound: `eraseDups` of a `filterMap` of `filter approved` is ≤ `countP approved`.) -/
theorem mOfNDistinct_le_countSat (keyField : FieldName) (approved : ElemPred) (coll : Collection) :
    (distinctApproverKeys keyField approved coll).length ≤ countSat approved coll := by
  unfold distinctApproverKeys countSat
  calc (((coll.filter approved).filterMap (fun e => elemSym e keyField)).eraseDups).length
      ≤ ((coll.filter approved).filterMap (fun e => elemSym e keyField)).length :=
        length_eraseDups_le' _
    _ ≤ (coll.filter approved).length := length_filterMap_le' _ _
    _ = countSat approved coll := (List.countP_eq_length_filter).symm

/-! ## §5 — The collection is referenced BY NAME from the record (the end-to-end name path).

`collectionAggregate name cp v` reads the collection at named field `name` out of the cell record `v`
and evaluates the aggregate `cp` over it. Fail-closed: a missing/ill-typed collection field REJECTS
(an aggregate over an absent collection is unevaluable, like a `Value.scalar` over a missing field).
This closes the loop: the cell-program names a COLLECTION the way it names a field, and aggregates. -/

/-- **`collectionAggregate name cp v`** — evaluate aggregate `cp` over the collection stored under
named field `name` in record `v`. Fail-closed (`false`) if the collection field is absent/ill-typed.
The named entry point — a cell program references a collection by name and predicates over it. -/
def collectionAggregate (name : FieldName) (cp : CollPred) (v : Value) : Bool :=
  match v.collectionField name with
  | some coll => cp.eval coll
  | none      => false

/-- **`collectionCouncil name m keyField approved v`** — the named-entry council gate: read the
approver collection at field `name`, require ≥ `m` distinct approvers. Fail-closed on an absent
collection. The arbitrary-N council a cell program installs by NAME. -/
def collectionCouncil (name : FieldName) (m : Nat) (keyField : FieldName) (approved : ElemPred)
    (v : Value) : Bool :=
  match v.collectionField name with
  | some coll => mOfNDistinct m keyField approved coll
  | none      => false

/-- **`collectionAggregate_absent_refuses`.** A missing/ill-typed collection field FAILS CLOSED — an
aggregate over an absent collection cannot be satisfied. -/
theorem collectionAggregate_absent_refuses (name : FieldName) (cp : CollPred) (v : Value)
    (h : v.collectionField name = none) : collectionAggregate name cp v = false := by
  simp [collectionAggregate, h]

/-- **`collectionCouncil_absent_refuses`.** A missing approver collection FAILS CLOSED — no quorum
without a collection to count. -/
theorem collectionCouncil_absent_refuses (name : FieldName) (m : Nat) (keyField : FieldName)
    (approved : ElemPred) (v : Value) (h : v.collectionField name = none) :
    collectionCouncil name m keyField approved v = false := by
  simp [collectionCouncil, h]

/-- **`collectionCouncil_iff` (the named council admit-char).** The named-entry council admits IFF the
collection reads AND ≥ `m` distinct approvers satisfy `approved`. The end-to-end statement: name the
collection, the quorum is the distinct count. -/
theorem collectionCouncil_iff (name : FieldName) (m : Nat) (keyField : FieldName)
    (approved : ElemPred) (v : Value) :
    collectionCouncil name m keyField approved v = true ↔
      ∃ coll, v.collectionField name = some coll ∧
        m ≤ (distinctApproverKeys keyField approved coll).length := by
  unfold collectionCouncil
  cases h : v.collectionField name with
  | none      => simp
  | some coll => simp [mOfNDistinct_iff]

/-! ## §6 — §NON-VACUITY: a concrete 3-of-5 council, BOTH polarities, the two forges REFUSED.

The §8 bar (`feedback-dont-launder-vacuity-as-honest`): the council bites both ways. Five approver
elements, each a record `{voter : sym, vote : int}`; `approved e` = "`e.vote = 1`"; `keyField =
"voter"`; threshold 3. We exhibit:

  * ACCEPT — 3 DISTINCT approvers vote 1 ⇒ admits.
  * REFUSE (sub-quorum) — only 2 vote 1 ⇒ refuses (2 < 3).
  * REFUSE (DUPLICATE-PADDED forge) — the SAME approver listed 3× (all vote 1) ⇒ ONE distinct key ⇒
    refuses. The padding does not buy the quorum.
  * REFUSE (UNBOUND forge) — 2 genuine approvers + a padding element that votes 0 (does NOT approve)
    ⇒ the padding is filtered ⇒ 2 distinct ⇒ refuses. An element that does not approve cannot pad. -/

/-- The approval predicate: element `e` approves iff its `vote` field is `1`. -/
def votedYes : ElemPred := fun e => elemScalar e "vote" == some 1

/-- An approver element `{voter = id, vote = v}`. -/
def approver (id : Nat) (v : Int) : Value := .record [("voter", .sym id), ("vote", .int v)]

/-- A GOOD 3-of-5: voters 0,1,2 vote YES (distinct); 3,4 vote NO. 3 distinct approvers ⇒ quorum. -/
def council3of5 : Collection :=
  [approver 0 1, approver 1 1, approver 2 1, approver 3 0, approver 4 0]

/-- A SUB-QUORUM: only voters 0,1 vote YES. 2 distinct approvers ⇒ below threshold 3. -/
def councilSub : Collection :=
  [approver 0 1, approver 1 1, approver 2 0, approver 3 0, approver 4 0]

/-- The DUPLICATE-PADDED FORGE: voter 0 listed THREE times, all YES. The raw satisfying-count is 3,
but there is ONLY ONE distinct identity ⇒ the distinct quorum is 1 ⇒ REFUSES. -/
def councilDupForge : Collection :=
  [approver 0 1, approver 0 1, approver 0 1, approver 3 0, approver 4 0]

/-- The UNBOUND FORGE: voters 0,1 genuinely vote YES; a THIRD padding element votes NO (does not
approve). It is filtered before the count ⇒ 2 distinct approvers ⇒ REFUSES. A non-approving element
cannot pad the quorum. -/
def councilUnboundForge : Collection :=
  [approver 0 1, approver 1 1, approver 7 0]

-- ACCEPT: 3 distinct approvers reach the threshold-3 quorum.
#guard mOfNDistinct 3 "voter" votedYes council3of5 == true
-- REFUSE (sub-quorum): only 2 distinct approvers.
#guard mOfNDistinct 3 "voter" votedYes councilSub == false
-- REFUSE (duplicate-padded forge): one approver listed 3×, ONE distinct key.
#guard mOfNDistinct 3 "voter" votedYes councilDupForge == false
-- REFUSE (unbound forge): a non-approving padding element is filtered out.
#guard mOfNDistinct 3 "voter" votedYes councilUnboundForge == false

-- The forge's RAW count IS 3 (so a naive countSatGe WOULD be fooled) — but the DISTINCT count is 1.
#guard countSat votedYes councilDupForge == 3
#guard (distinctApproverKeys "voter" votedYes councilDupForge).length == 1
-- The honest council's distinct count is exactly 3.
#guard (distinctApproverKeys "voter" votedYes council3of5).length == 3

/-- **`council_accepts` (TEETH — the positive direction).** A 3-of-5 with 3 distinct YES voters
ADMITS. -/
theorem council_accepts : mOfNDistinct 3 "voter" votedYes council3of5 = true := by decide

/-- **`council_subquorum_refuses` (TEETH — sub-quorum).** Only 2 distinct approvers ⇒ REFUSES. -/
theorem council_subquorum_refuses : mOfNDistinct 3 "voter" votedYes councilSub = false := by decide

/-- **`council_dup_forge_refuses` (TEETH — the duplicate-padding forge, the anti-fake keystone).**
The same approver listed THREE times (raw count 3) yields ONE distinct identity, so the distinct
quorum is 1 < 3 and the gate REFUSES. The padding does not buy the quorum — distinctness bites. -/
theorem council_dup_forge_refuses : mOfNDistinct 3 "voter" votedYes councilDupForge = false := by
  decide

/-- **`council_unbound_forge_refuses` (TEETH — the unbound forge).** A padding element that does NOT
approve (votes 0) is filtered before the count, so 2 genuine approvers stay 2 distinct < 3 and the gate
REFUSES. A non-approving element cannot pad the quorum. -/
theorem council_unbound_forge_refuses :
    mOfNDistinct 3 "voter" votedYes councilUnboundForge = false := by decide

/-- **`council_dup_forge_raw_vs_distinct` (the forge's anatomy, as a theorem).** The duplicate-padded
forge has RAW satisfying-count 3 (a naive `countSatGe 3` would ADMIT it) but DISTINCT-approver count 1
(`mOfNDistinct 3` REFUSES it). This is the precise statement that distinctness — not the raw count — is
the load-bearing gate, and that the naive aggregate is genuinely fooled where the council is not. -/
theorem council_dup_forge_raw_vs_distinct :
    countSat votedYes councilDupForge = 3 ∧
    (distinctApproverKeys "voter" votedYes councilDupForge).length = 1 ∧
    (CollPred.countSatGe 3 votedYes).eval councilDupForge = true ∧
    mOfNDistinct 3 "voter" votedYes councilDupForge = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **`council_discriminates_arbitraryN` (non-vacuity — the gate is a genuine discriminator at N=5).**
The SAME council gate at threshold 3 ADMITS the honest 5-element collection and REFUSES the sub-quorum
— different bits, a real discriminator, not a vacuous `:= true`. And N is 5, past the documented N≤3
fixed-slot cap: the collection abstraction lifts the ceiling. -/
theorem council_discriminates_arbitraryN :
    mOfNDistinct 3 "voter" votedYes council3of5 = true ∧
    mOfNDistinct 3 "voter" votedYes councilSub = false :=
  ⟨by decide, by decide⟩

/-! ## §6.1 — The OTHER aggregates discriminate too (sum cap / ∀ / ∃ over the collection). -/

/-- A treasury collection: three line-items with `amount` fields. -/
def ledger : Collection :=
  [.record [("amount", .int 40)], .record [("amount", .int 30)], .record [("amount", .int 20)]]

-- sumOfLe: the line-item total (90) is within a 100 cap, but exceeds an 80 cap.
#guard (CollPred.sumOfLe "amount" 100).eval ledger == true
#guard (CollPred.sumOfLe "amount" 80).eval ledger == false
#guard sumOfField "amount" ledger == 90

-- allMembers: every line-item is positive (≤-bounded the other way: amount ≥ 1) — holds here.
#guard (CollPred.allMembers (fun e => decide (1 ≤ (elemScalar e "amount").getD 0))).eval ledger == true
-- ∀ fails once one item is zeroed.
#guard (CollPred.allMembers (fun e => decide (1 ≤ (elemScalar e "amount").getD 0))).eval
        (.record [("amount", .int 0)] :: ledger) == false

-- existsMember: some line-item exceeds 35 (the 40) — holds; none exceeds 100 — fails.
#guard (CollPred.existsMember (fun e => decide (35 < (elemScalar e "amount").getD 0))).eval ledger == true
#guard (CollPred.existsMember (fun e => decide (100 < (elemScalar e "amount").getD 0))).eval ledger == false

/-- **`sumCap_discriminates` (non-vacuity — the supply/treasury cap).** The collection sum-cap admits
the within-budget total and refuses the over-budget one — a genuine discriminator over arbitrary-N
data. -/
theorem sumCap_discriminates :
    (CollPred.sumOfLe "amount" 100).eval ledger = true ∧
    (CollPred.sumOfLe "amount" 80).eval ledger = false :=
  ⟨by decide, by decide⟩

/-! ## §7 — The collection reads BY NAME out of a record (the named entry, end-to-end). -/

/-- A governance cell record carrying its approver collection inline under field `"council"` (a
sub-record whose index keys `"0"`,`"1"`,… hold the approver elements) plus an ordinary `state` field. -/
def govCellOk : Value :=
  .record
    [ ("state", .int 1)
    , ("council", .record
        [ ("0", approver 0 1), ("1", approver 1 1), ("2", approver 2 1)
        , ("3", approver 3 0), ("4", approver 4 0) ]) ]

/-- The SAME cell but the council holds a duplicate-padded forge (voter 0 listed 3×). -/
def govCellForge : Value :=
  .record
    [ ("state", .int 1)
    , ("council", .record
        [ ("0", approver 0 1), ("1", approver 0 1), ("2", approver 0 1)
        , ("3", approver 3 0), ("4", approver 4 0) ]) ]

-- The collection reads back by name out of the record (5 elements).
#guard (govCellOk.collectionField "council").map (·.length) == some 5
-- The named-entry council admits the honest cell, refuses the forged one — fail-closed end to end.
#guard collectionCouncil "council" 3 "voter" votedYes govCellOk == true
#guard collectionCouncil "council" 3 "voter" votedYes govCellForge == false
-- A cell with NO council collection fails closed.
#guard collectionCouncil "council" 3 "voter" votedYes (.record [("state", .int 1)]) == false

/-- **`namedCouncil_accepts_and_refuses_forge` (the end-to-end teeth).** Reading the approver
collection BY NAME out of the cell record, the council ADMITS the honest 3-of-5 and REFUSES the
duplicate-padded forge — the data-model rung working through the named record path, both polarities. -/
theorem namedCouncil_accepts_and_refuses_forge :
    collectionCouncil "council" 3 "voter" votedYes govCellOk = true ∧
    collectionCouncil "council" 3 "voter" votedYes govCellForge = false :=
  ⟨by decide, by decide⟩

/-- **`namedCouncil_absent_collection_refuses` (fail-closed entry).** A cell with no `council`
collection field REFUSES — an aggregate over an absent collection is unevaluable. -/
theorem namedCouncil_absent_collection_refuses :
    collectionCouncil "council" 3 "voter" votedYes (.record [("state", .int 1)]) = false := by decide

/-! ## §8 — Axiom-hygiene tripwires (the honesty pins over every keystone). -/

#assert_all_clean [
  eval_countSatGe_iff,
  eval_sumOfLe_iff,
  eval_sumOfGe_iff,
  eval_allMembers_iff,
  eval_existsMember_iff,
  countSat_le_size,
  mOfNDistinct_iff,
  mOfNDistinct_sound,
  distinct_keys_nodup,
  mOfNDistinct_le_countSat,
  collectionAggregate_absent_refuses,
  collectionCouncil_absent_refuses,
  collectionCouncil_iff,
  council_accepts,
  council_subquorum_refuses,
  council_dup_forge_refuses,
  council_unbound_forge_refuses,
  council_dup_forge_raw_vs_distinct,
  council_discriminates_arbitraryN,
  sumCap_discriminates,
  namedCouncil_accepts_and_refuses_forge,
  namedCouncil_absent_collection_refuses
]

end Dregg2.Exec.Collections
