/-
# Dregg2.Circuit.Emit.PastaMsmBound — the slice CONTENTS, forced by the EMITTED constraints.

## Substrate, said out loud

**Lean-authored AIR.** Every constraint here is produced by a `def` returning `VmConstraint2`, and
every theorem is about that ACTUALLY EMITTED list. Rust hand-writes no constraint, no builder
gadget and no `air_accepts` predicate: it parses the emitted descriptor, fills trace CELLS and runs
the deployed prover. The row template is **not re-authored** — `boundRowDesc_extends_sliced` proves
`PastaMsmSliced.slicedRowDesc`'s 78 constraints are still a PREFIX of the emitted 82.

## The hole this file closes

`PastaMsmSliced` §7.1 stated it exactly: *the slice DECLARATION is bound; the slice CONTENTS are
not.* `sliceDecl_forces_bounds` pins `[lo, hi)` into the emitted gates and `outPi_publishes` puts
the partial on the wire, but **nothing in the emitted constraints said the row's `SRC` columns carry
`srs.g[lo + t]`**. An adversary could declare `[0, 8192)` and fill the rows with any 8,192 points,
so even a full-size run would have proved a SHAPE, not the Mina claim.

The fix that file named is what this one builds: an EXACT-PUBLIC table of
`(row key, absolute generator index, digit, generator limbs)` plus a THREADED index column, with a
per-row lookup. `TableSem.exactPublicRows` is the primitive — and read at the right resolution it is
stronger than a subset lookup: `DescriptorIR2.PublicLookupBalanced` demands the trace's lookup
multiset be a PERMUTATION of the descriptor-carried manifest, not merely contained in it. So the
manifest does not only say "these generators are available"; it says **these rows and no others**.

## What that buys, and it is more than the generators

Because the manifest is keyed by the THREADED ROW INDEX and the doubling rows are the manifest's
all-zero rows, the emitted lookup forces, row by row and with no schedule hypothesis:

  * `bound_forces_source_limbs` — a conditional-add row's limb columns are the limbs of
    `gens[lo + t]`, the generator at the ABSOLUTE index the manifest names;
  * `bound_forces_digit` — its `BIT` column is the declared digit;
  * `bound_forces_gidx` — its `GIDX` column is that absolute index;
  * `bound_forces_dbl_off` / `bound_forces_doubling` — **the `DBL` PATTERN itself**, which
    `PastaMsmWindowed` §6.1 left as an explicit hypothesis and named as a buildable rung. A row at a
    plane boundary MUST double and a row inside a plane MUST NOT.

## What it does NOT buy — read §7 before citing this

The row count is bounded by the DEPLOYED exact-public tooth, not by this file: `descriptor_ir2.rs`
caps a manifest at `MAX_EXACT_PUBLIC_ROWS = 128` rows / `MAX_EXACT_PUBLIC_CELLS = 4096` cells, and
`instance_airs` spends ONE batch AIR instance per manifest row. Since the balance is a PERMUTATION,
the manifest row count IS the trace height — so a contents-bound instance is at most 128 rows tall.
**The theorems below are row-count-independent; the DEMONSTRATION is not.** §7.1 prices it.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`s reduce in the kernel. Imports read-only. Import line:
`import Dregg2.Circuit.Emit.PastaMsmBound`
-/
import Dregg2.Circuit.Emit.PastaMsmSliced

namespace Dregg2.Circuit.Emit.PastaMsmBound

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2 WindowExpr WindowConstraint
  TableId TableDef Lookup VmTrace zeroAsg exactPublicTable lookupLog PublicLookupBalanced)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN numLimbs limbBits fpVal)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP PointIsZ)
open Dregg2.Circuit.Emit.PastaMsmWindowed (WTrace envOf cw
  SRCX SRCY SRCZ BIT DBL fpVal_as_sum)
open Dregg2.Circuit.Emit.PastaMsmSliced (sliceLo slicedRowDesc PI_COUNT)

set_option autoImplicit false

/-! ## §0 — TWO LIST TOOLS, used everywhere below.

Both are about `List.range`-maps, which is what makes the forcing POINTWISE without ever indexing
into a concatenation. -/

/-- A `range`-map equality is pointwise. -/
theorem range_map_pointwise {α : Type} (n : Nat) (f g : Nat → α)
    (h : (List.range n).map f = (List.range n).map g) : ∀ j, j < n → f j = g j := by
  intro j hj
  have hc := congrArg (fun L => L[j]?) h
  simpa [List.getElem?_map, List.getElem?_range, hj] using hc

/-- …and conversely. -/
theorem range_map_congr {α : Type} (n : Nat) (f g : Nat → α)
    (h : ∀ j, j < n → f j = g j) : (List.range n).map f = (List.range n).map g :=
  List.map_congr_left (fun j hj => h j (List.mem_range.mp hj))

/-! ## §1 — THE TWO ADDED COLUMNS, and the table.

`PastaMsmSliced` ended at width 527 (`WS`). Two columns are added:

  * `TIDX` — the THREADED ROW INDEX. Pinned to `0` on the first row by an emitted
    `.boundary .first`, and advanced by one per row by an emitted `windowGate`. It is what ties a
    trace row to a manifest row: without it the multiset would say WHICH tuples occur but not WHERE.
  * `GIDX` — the ABSOLUTE generator index the row consumes (meaningful iff `DBL = 0`). It resets to
    `lo` after every doubling row and advances by one otherwise, so the emitted object itself says
    "this row is term `GIDX` of the slice", and the manifest ties `GIDX` to the limbs. -/

/-- The threaded ROW index. -/
def TIDX : Nat := 527
/-- The ABSOLUTE generator index this row consumes (meaningful iff `DBL = 0`). -/
def GIDX : Nat := 528
/-- The contents-bound row template's width: `PastaMsmSliced.WS = 527` plus the two index columns. -/
def WB : Nat := 529

/-- ⚑ **The generator table's wire id, PER SLICE.** `custom (40 + k)` renders as wire id `45 + k`,
above every reserved id (`descriptor_ir2.rs` refuses an exact-public table at
`id ≤ TID_P2_STATE16 = 9`).

⚠ **The `k` is load-bearing and is not cosmetic.** `descriptor_ir2.rs::exact_public_bus_name` keys
the LogUp bus on the TABLE ID ALONE, and LogUp balance in a batch STARK is GLOBAL. Four co-batched
slices declaring ONE id would share ONE bus: their queries and their manifest capacity would POOL,
so slice 0 consuming slice 2's generator could be cancelled by slice 2 consuming slice 0's and the
global sum would still balance. That is exactly the CROSS-PAIRING hazard `PastaMsmSliced` §3
exhibits, re-entering through the bus rather than through the arithmetic. A distinct id per slice
gives each slice its own bus and its own exact multiset. -/
def GEN_TID (k : Nat) : TableId := .custom (40 + k)

/-- The number of limb columns a point occupies (`SRCX .. SRCX + 26`). -/
def PTLIMBS : Nat := 3 * numLimbs

/-- The lookup tuple's arity: row key, absolute generator index, digit, and the limb columns. -/
def TUP : Nat := 3 + PTLIMBS

/-! ## §2 — THE EMITTED GATES.

Four objects: the first-row pin on `TIDX`, the two index threads, and the lookup. All are `def`s
producing `VmConstraint2`; §4 states what each one FORCES. -/

/-- `1 − DBL`, as an emitted expression: the doubling-row GUARD. A doubling row's `SRC` is the
ACCUMULATOR (`PastaMsmWindowed.dblRow_forces`), which is not a public generator — so its tuple is
multiplied to the all-zero row, which the manifest carries once per plane. -/
def notDbl : EmittedExpr := .add (.const 1) (.mul (.const (-1)) (.var DBL))

/-- The guard's VALUE on a row. -/
def guardV (a : Assignment) : ℤ := 1 + (-1) * a DBL

/-- ⚑ **The emitted lookup tuple.** Every entry is guarded, so a doubling row emits the all-zero
tuple and a conditional-add row emits `(TIDX+1, GIDX+1, BIT, SRC limbs)`. The `+1` on the two index
fields is what keeps the zero tuple OUT of the conditional-add key space. -/
def genTuple : List EmittedExpr :=
  (.mul notDbl (.add (.var TIDX) (.const 1)))
    :: (.mul notDbl (.add (.var GIDX) (.const 1)))
    :: (.mul notDbl (.var BIT))
    :: (List.range PTLIMBS).map (fun j => EmittedExpr.mul notDbl (.var (SRCX + j)))

/-- `TIDX = 0` on the FIRST row (an emitted `.boundary .first`). -/
def tidxStartGate : VmConstraint2 := .base (.boundary .first (.var TIDX))

/-- `nxt TIDX − (loc TIDX + 1)` — the row index advances by one, every row. -/
def tidxThreadGate : VmConstraint2 :=
  cw (.add (.nxt TIDX) (.mul (.const (-1)) (.add (.loc TIDX) (.const 1))))

/-- `nxt GIDX − (DBL·lo + (1−DBL)·(GIDX+1))` — the term index RESETS to the slice's own `lo` after
a doubling row and advances otherwise. `lo` is a LITERAL in the emitted gate, so instance `k`'s
thread cannot be instance `j`'s. -/
def gidxThreadGate (lo : Nat) : VmConstraint2 :=
  cw (.add (.nxt GIDX)
      (.mul (.const (-1))
        (.add (.mul (.loc DBL) (.const (lo : ℤ)))
              (.mul (.add (.const 1) (.mul (.const (-1)) (.loc DBL)))
                    (.add (.loc GIDX) (.const 1))))))

/-- The three index gates. -/
def boundGates (lo : Nat) : List VmConstraint2 :=
  [ tidxStartGate, tidxThreadGate, gidxThreadGate lo ]

/-- The single emitted lookup into slice `k`'s OWN generator table. -/
def genLookup (k : Nat) : VmConstraint2 := .lookup ⟨GEN_TID k, genTuple⟩

/-! ## §3 — THE MANIFEST: `(row key, absolute index, digit, generator limbs)`.

The manifest is a `def` over the generator list, so what it declares is the SAME object the kernel
`decide` of rung 5h evaluates (`MinaWrapSgCore.SRS_G`) — not a re-transcription. -/

/-- A projective point as three `Nat` coordinates (the shape `MinaWrapSrsG` carries). -/
abbrev Pt := Nat × Nat × Nat

/-- The `i`-th `limbBits`-bit limb of `v` (the `Nat` twin of `PastaField.Ref.limbOf`). -/
def limbNat (v i : Nat) : Nat := (v / 2 ^ (limbBits * i)) % 2 ^ limbBits

/-- The limb at LIMB-COLUMN `j` of a point: `X` for `j < 9`, `Y` for `9 ≤ j < 18`, `Z` above —
exactly the row layout's `SRCX`/`SRCY`/`SRCZ` block order. -/
def coordLimb (P : Pt) (j : Nat) : Nat :=
  if j < numLimbs then limbNat P.1 j
  else if j < 2 * numLimbs then limbNat P.2.1 (j - numLimbs)
  else limbNat P.2.2 (j - 2 * numLimbs)

/-- A point's `3 · numLimbs` limb columns, in the row layout's order. -/
def limbsOfPt (P : Pt) : List Nat := (List.range PTLIMBS).map (coordLimb P)

/-- The scalar digit term `idx` contributes at bit plane `plane`, MSB-first over `planes` planes —
the same schedule `PastaMsmWindowed.HornerSchedule` names. -/
def scalarDigit (scal : List Nat) (planes idx plane : Nat) : Nat :=
  ((scal.getD idx 0) / 2 ^ (planes - 1 - plane)) % 2

/-- The term index trace row `i` consumes (junk on a doubling row, where the guard kills it). -/
def termAt (w i : Nat) : Nat := i % (w + 1) - 1

/-- The bit plane trace row `i` belongs to. -/
def planeAt (w i : Nat) : Nat := i / (w + 1)

/-- ⚑ **The manifest row for TRACE ROW `i`.** The plane-boundary rows (`i % (w+1) = 0`) are the
doubling rows and get the ALL-ZERO row; every other row gets its own key `i+1`, the ABSOLUTE
generator index `lo + t`, the digit, and the generator's limbs. -/
def manifestRow (lo w planes : Nat) (gens : List Pt) (scal : List Nat) (i : Nat) : List Nat :=
  if i % (w + 1) = 0 then List.replicate TUP 0
  else
    (i + 1) :: (lo + termAt w i + 1)
      :: scalarDigit scal planes (lo + termAt w i) (planeAt w i)
      :: limbsOfPt (gens.getD (lo + termAt w i) (0, 0, 0))

/-- The whole manifest: one row per trace row. Its LENGTH is the trace height — that is forced by
the exact-public semantics being a PERMUTATION, and §7.1 prices it. -/
def genManifest (lo w planes : Nat) (gens : List Pt) (scal : List Nat) : List (List Nat) :=
  (List.range (planes * (w + 1))).map (manifestRow lo w planes gens scal)

/-- The declared table. -/
def genTableDef (k lo w planes : Nat) (gens : List Pt) (scal : List Nat) : TableDef :=
  ⟨GEN_TID k, "pasta_sg_generators", TUP, .exactPublicRows (genManifest lo w planes gens scal)⟩

/-- ⚑ **The CONTENTS-BOUND sliced descriptor.** `PastaMsmSliced.slicedRowDesc`'s constraints
verbatim, plus the three index gates and the one lookup; plus the declared manifest. -/
def boundRowDesc (n k w planes : Nat) (gens : List Pt) (scal : List Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-rcb-sg-bound-" ++ toString k ++ "-of-" ++ toString n ++ "::v1"
  , traceWidth  := WB
  , piCount     := PI_COUNT
  , tables      := [genTableDef k (sliceLo w k) w planes gens scal]
  , constraints := (slicedRowDesc n k w).constraints
                     ++ boundGates (sliceLo w k) ++ [genLookup k]
  , hashSites   := []
  , ranges      := [] }

/-- ⚑ **`boundRowDesc_extends_sliced`** — the emitted list still has the SLICED descriptor's 78
constraints as a PREFIX. Nothing was re-authored. -/
theorem boundRowDesc_extends_sliced (n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (slicedRowDesc n k w).constraints <+: (boundRowDesc n k w planes gens scal).constraints :=
  ⟨boundGates (sliceLo w k) ++ [genLookup k], by simp [boundRowDesc, List.append_assoc]⟩

/-- The emitted constraint count: 78 from the sliced descriptor, 3 index gates, 1 lookup. Still a
CONSTANT — independent of the slice width, the plane count and the row count. -/
theorem boundRowDesc_constraints_length (n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (boundRowDesc n k w planes gens scal).constraints.length = 82 := by
  simp [boundRowDesc, boundGates,
    Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc_constraints_length]

/-! ### §3b — the deployed checker's OWN predicates, over the arms THIS file adds.

`PastaMsmSliced.sMaxVar` has no `.lookup` arm — correct for a file that emits none, and a SILENT
HOLE for one that does. `bMaxVar` covers it. -/

/-- The largest column index a constraint addresses, over every arm this file emits — including the
`.lookup` tuple, which `PastaMsmSliced.sMaxVar` cannot see. -/
def bMaxVar : VmConstraint2 → Nat
  | .base (.gate e)            => Dregg2.Circuit.Emit.PastaMsmWindowed.eMaxVar e
  | .base (.boundary _ e)      => Dregg2.Circuit.Emit.PastaMsmWindowed.eMaxVar e
  | .base (.piBinding _ col _) => col + 1
  | .windowGate w              => Dregg2.Circuit.Emit.PastaMsmWindowed.wMaxVar w.body
  | .lookup l                  =>
      (l.tuple.map Dregg2.Circuit.Emit.PastaMsmWindowed.eMaxVar).foldl max 0
  | _                          => 0

set_option maxRecDepth 100000 in
/-- ⚑ **`boundRowDesc_columns_in_bounds`** — every column every emitted constraint addresses,
INCLUDING the lookup tuple's, is `≤ traceWidth`. This is `descriptor_ir2.rs`'s `chk` closure. -/
theorem boundRowDesc_columns_in_bounds :
    (boundRowDesc 4 0 31 4 [] []).constraints.all
        (fun c => decide (bMaxVar c ≤ (boundRowDesc 4 0 31 4 [] []).traceWidth)) = true := by decide

set_option maxRecDepth 100000 in
/-- ⚑ **`boundRowDesc_pi_indices_in_bounds`** — every `pi_binding` names a declared public input
(`descriptor_ir2.rs:1581`). -/
theorem boundRowDesc_pi_indices_in_bounds :
    (boundRowDesc 4 0 31 4 [] []).constraints.all
        (fun c => decide (Dregg2.Circuit.Emit.PastaMsmSliced.sMaxPi c
                            ≤ (boundRowDesc 4 0 31 4 [] []).piCount)) = true := by decide

#guard (boundRowDesc 4 0 31 4 [] []).traceWidth == 529
#guard (boundRowDesc 4 0 31 4 [] []).piCount == 29
#guard (boundRowDesc 4 0 31 4 [] []).constraints.length == 82
#guard (boundRowDesc 4 2 31 4 [] []).name == "dregg-pasta-rcb-sg-bound-2-of-4::v1"
#guard TUP == 30
#guard PTLIMBS == 27

-- ⚑ The DEPLOYED exact-public bound, discharged here so a re-parameterisation cannot silently
-- exceed it: `MAX_EXACT_PUBLIC_ROWS = 128`, `MAX_EXACT_PUBLIC_ARITY = 64`,
-- `MAX_EXACT_PUBLIC_CELLS = 4096` (`circuit/src/descriptor_ir2.rs:403-405`).
#guard 4 * (31 + 1) == 128
#guard 4 * (31 + 1) * TUP == 3840
#guard 4 * (31 + 1) ≤ 128 && TUP ≤ 64 && 4 * (31 + 1) * TUP ≤ 4096
-- ⚑ The four slices' table ids are DISTINCT, so their LogUp buses are distinct. Same shape as
-- `TableId.wireId_injective`, but the thing at stake is the CROSS-SLICE bus pooling above.
#guard ((List.range 4).map (fun k => (GEN_TID k).wireId)).dedup.length == 4
#guard (List.range 4).all (fun k => 9 < (GEN_TID k).wireId)

/-! ## §4 — THE FORCING.

Three separate denotations, because the deployed AIR treats the families differently and one
predicate would blur them:

  * the row template's `.gate`s land in `acceptB` (the ℤ model every `Pasta*` rung uses);
  * the two index threads are `windowGate`s, stated against `WindowExpr.eval`;
  * the lookup is stated against `DescriptorIR2.PublicLookupBalanced` — the IR's OWN exact-public
    denotation, the one `demoPublic_duplicate_omission_refused` exercises in both polarities. -/

/-- The content of the emitted index `windowGate`s at row `i`. -/
def BoundWindowAccepted (lo : Nat) (T : WTrace) (i : Nat) : Prop :=
  ∀ wc : WindowConstraint, VmConstraint2.windowGate wc ∈ boundGates lo →
    wc.body.eval (envOf T i) = 0

/-- The content of the emitted first-row `.boundary` gate, in the ℤ model (§7.3: the deployed
prover reads it mod BabyBear, the inherited K1 residual). -/
def BoundStartAccepted (lo : Nat) (T : WTrace) : Prop :=
  ∀ e : EmittedExpr, VmConstraint2.base (.boundary .first e) ∈ boundGates lo →
    e.eval (T 0) = 0

/-- ⚑ **`tidxStart_forces`** — the emitted first-row boundary pins the thread's origin. -/
theorem tidxStart_forces (lo : Nat) (T : WTrace) (h : BoundStartAccepted lo T) : T 0 TIDX = 0 := by
  have := h (.var TIDX) (by simp [boundGates, tidxStartGate])
  simpa [EmittedExpr.eval] using this

/-- ⚑ **`tidxThread_forces`** — the emitted `windowGate` advances the row index by exactly one. -/
theorem tidxThread_forces (lo : Nat) (T : WTrace) (i : Nat) (h : BoundWindowAccepted lo T i) :
    T (i + 1) TIDX = T i TIDX + 1 := by
  have hw := h ⟨.add (.nxt TIDX) (.mul (.const (-1)) (.add (.loc TIDX) (.const 1))), true⟩
    (by simp [boundGates, tidxThreadGate, cw])
  simp only [WindowExpr.eval, envOf] at hw
  linarith

/-- ⚑ **`gidxThread_forces`** — the emitted `windowGate` resets the term index to the slice's own
`lo` after a doubling row and advances it otherwise. -/
theorem gidxThread_forces (lo : Nat) (T : WTrace) (i : Nat) (h : BoundWindowAccepted lo T i) :
    T (i + 1) GIDX
      = T i DBL * (lo : ℤ) + (1 + (-1) * T i DBL) * (T i GIDX + 1) := by
  have hw := h ⟨.add (.nxt GIDX)
      (.mul (.const (-1))
        (.add (.mul (.loc DBL) (.const (lo : ℤ)))
              (.mul (.add (.const 1) (.mul (.const (-1)) (.loc DBL)))
                    (.add (.loc GIDX) (.const 1))))), true⟩
    (by simp [boundGates, gidxThreadGate, cw])
  simp only [WindowExpr.eval, envOf] at hw
  linarith

/-- ⚑ **`tidx_is_the_row_index`** — the emitted origin pin plus the emitted thread make `TIDX` the
row's own index, for every row. `H` is universally quantified and occurs only as the induction
bound: the statement at `H = 128` is the statement at `H = 1,056,896`. -/
theorem tidx_is_the_row_index (lo : Nat) (T : WTrace) (H : Nat)
    (h0 : BoundStartAccepted lo T) (h : ∀ i, i + 1 < H → BoundWindowAccepted lo T i) :
    ∀ i, i < H → T i TIDX = (i : ℤ) := by
  intro i
  induction i with
  | zero => intro _; simpa using tidxStart_forces lo T h0
  | succ m ih =>
    intro hm
    have hstep := tidxThread_forces lo T m (h m hm)
    rw [hstep, ih (by omega)]
    push_cast
    ring

#assert_axioms tidxStart_forces
#assert_axioms tidxThread_forces
#assert_axioms gidxThread_forces
#assert_axioms tidx_is_the_row_index

/-! ### §4b — the lookup, against the IR's OWN exact-public denotation. -/

/-- The emitted tuple, evaluated on a row. -/
def tupleOf (a : Assignment) : List ℤ := genTuple.map (fun e => e.eval a)

/-- The tuple in explicit form. -/
theorem tupleOf_cons (a : Assignment) :
    tupleOf a =
      (guardV a * (a TIDX + 1))
        :: (guardV a * (a GIDX + 1))
        :: (guardV a * a BIT)
        :: ((List.range PTLIMBS).map (fun j => guardV a * a (SRCX + j))) := by
  simp [tupleOf, genTuple, guardV, notDbl, EmittedExpr.eval, List.map_map, Function.comp_def]

/-- The tuple's KEY. -/
theorem tupleOf_head (a : Assignment) :
    (tupleOf a).head? = some (guardV a * (a TIDX + 1)) := by rw [tupleOf_cons]; rfl

/-- The manifest row's KEY: `0` on a plane-boundary (doubling) row, `i+1` otherwise. -/
theorem manifestRow_head (lo w planes : Nat) (gens : List Pt) (scal : List Nat) (i : Nat) :
    (manifestRow lo w planes gens scal i).head?
      = some (if i % (w + 1) = 0 then 0 else i + 1) := by
  unfold manifestRow
  split <;> simp_all [TUP, PTLIMBS, numLimbs]

/-- ⚑ **`manifest_key_unique`** — two manifest rows with the same KEY ARE the same row. This is
what turns multiset membership into a POINTWISE statement, and it is proved from the manifest's
`def` rather than decided at a row count, so it holds at every `(w, planes)`. -/
theorem manifest_key_unique (lo w planes : Nat) (gens : List Pt) (scal : List Nat)
    {r s : List Nat} (hr : r ∈ genManifest lo w planes gens scal)
    (hs : s ∈ genManifest lo w planes gens scal) (hk : r.head? = s.head?) : r = s := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
  rw [manifestRow_head, manifestRow_head] at hk
  by_cases hi : i % (w + 1) = 0 <;> by_cases hj : j % (w + 1) = 0
  · simp [manifestRow, hi, hj]
  · rw [if_pos hi, if_neg hj] at hk; simp at hk
  · rw [if_neg hi, if_pos hj] at hk; simp at hk
  · rw [if_neg hi, if_neg hj] at hk
    have : i = j := by simpa using hk
    rw [this]

/-- ⚑ A manifest row whose KEY is a SUCCESSOR is the conditional-add row at that very index. -/
theorem manifest_key_succ (lo w planes : Nat) (gens : List Pt) (scal : List Nat)
    {m : List Nat} (hm : m ∈ genManifest lo w planes gens scal) {v : Nat}
    (hv : m.head? = some (v + 1)) :
    m = manifestRow lo w planes gens scal v ∧ v % (w + 1) ≠ 0 := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
  rw [manifestRow_head] at hv
  by_cases hj : j % (w + 1) = 0
  · rw [if_pos hj] at hv; simp at hv
  · rw [if_neg hj] at hv
    have hjv : j = v := by simpa using hv
    subst hjv
    exact ⟨rfl, hj⟩

/-- A constraint that is not a lookup. -/
def isNotLookup : VmConstraint2 → Bool
  | .lookup _ => false
  | _         => true

/-- A `flatMap` of singletons IS a `map`. -/
theorem flatMap_singleton_map {α β : Type} (f : α → List β) (g : α → β) (l : List α)
    (h : ∀ x, f x = [g x]) : l.flatMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons _ rest ih => simp [h, ih]

/-- A lookup-free constraint list contributes nothing to any lookup log. Stated over an ABSTRACT
`f` so it applies to `lookupLog`'s own anonymous matcher (which is a different constant from any
`match` written here — the reason this file cannot simply `rw` the log open). -/
theorem filterMap_of_noLookup {β : Type} (f : VmConstraint2 → Option β) (l : List VmConstraint2)
    (hnl : ∀ c, isNotLookup c = true → f c = none) (h : l.all isNotLookup = true) :
    l.filterMap f = [] := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [hnl a h.1, ih h.2]

/-- The lookup log of the emitted descriptor IS the per-row tuple map: there is exactly one emitted
lookup, and it targets the generator table. -/
theorem lookupLog_is_rowMap (n k w planes : Nat) (gens : List Pt) (scal : List Nat) (t : VmTrace) :
    lookupLog (boundRowDesc n k w planes gens scal) t (GEN_TID k) = t.rows.map tupleOf := by
  unfold lookupLog
  refine flatMap_singleton_map _ tupleOf t.rows (fun row => ?_)
  rw [show (boundRowDesc n k w planes gens scal).constraints
        = (slicedRowDesc n k w).constraints ++ boundGates (sliceLo w k) ++ [genLookup k]
      from rfl, List.filterMap_append, List.filterMap_append,
    filterMap_of_noLookup _ (slicedRowDesc n k w).constraints
      (fun c hc => by cases c <;> simp_all [isNotLookup]) (by rfl),
    filterMap_of_noLookup _ (boundGates (sliceLo w k))
      (fun c hc => by cases c <;> simp_all [isNotLookup]) (by rfl)]
  simp [genLookup, tupleOf]

/-- The exact-public balance the descriptor's declaration demands, unfolded at THIS table. -/
theorem bound_balance (n k w planes : Nat) (gens : List Pt) (scal : List Nat) (t : VmTrace)
    (hbal : PublicLookupBalanced (boundRowDesc n k w planes gens scal) t) :
    (t.rows.map tupleOf).Perm
      (exactPublicTable (genManifest (sliceLo w k) w planes gens scal)) := by
  have h := hbal (genTableDef k (sliceLo w k) w planes gens scal) (by simp [boundRowDesc])
  simpa [genTableDef, ← lookupLog_is_rowMap n k w planes gens scal t] using h

/-! ### §4c — ⚑⚑ THE CONTENTS FORCING.

The argument is pure MEMBERSHIP — no counting, no pigeonhole. In one direction the manifest row for
trace row `i` is IN the manifest, so by the permutation it is the tuple of SOME trace row; in the
other, row `i`'s tuple IS some manifest row. Either way the KEY — `(1 − DBL)·(TIDX + 1)`, with
`TIDX` the row's own index by §4 — plus key-uniqueness pins the row. -/

/-- Trace row `j`. -/
def rowAt (t : VmTrace) (j : Nat) : Assignment := t.rows.getD j zeroAsg

/-- `Int.ofNat` IS the `ℕ → ℤ` coercion (`exactPublicTable` is written with the former, every cast
lemma with the latter). -/
theorem ofNat_eq_cast (v : Nat) : Int.ofNat v = (v : ℤ) := rfl

/-- Trace row `j` is the `j`-th entry (below the length). -/
theorem rowAt_eq (t : VmTrace) (j : Nat) (hj : j < t.rows.length) : rowAt t j = t.rows[j] := by
  simp [rowAt, List.getElem?_eq_getElem hj]

/-- Trace row `j` is a row of the trace. -/
theorem rowAt_mem (t : VmTrace) (j : Nat) (hj : j < t.rows.length) : rowAt t j ∈ t.rows := by
  rw [rowAt_eq t j hj]; exact List.getElem_mem hj

/-- ⚑⚑ **`row_tuple_is_its_manifest_row`** — **the deliverable.** On a trace whose emitted lookup
multiset balances against the emitted manifest, whose `TIDX` column is the threaded row index and
whose `DBL` column is a bit, ROW `i`'s tuple IS the manifest's row `i` — for every `i`.

`i`, `w` and `planes` are universally quantified and occur in no bound. The statement at
`planes*(w+1) = 128` is the same theorem as at `1,056,896`. -/
theorem row_tuple_is_its_manifest_row (n k w planes : Nat) (gens : List Pt) (scal : List Nat)
    (t : VmTrace) (i : Nat)
    (hbal : PublicLookupBalanced (boundRowDesc n k w planes gens scal) t)
    (hlen : t.rows.length = planes * (w + 1))
    (htidx : ∀ j, j < t.rows.length → rowAt t j TIDX = (j : ℤ))
    (hdbl : ∀ j, rowAt t j DBL = 0 ∨ rowAt t j DBL = 1)
    (hi : i < planes * (w + 1)) :
    tupleOf (rowAt t i)
      = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat := by
  have hperm := bound_balance n k w planes gens scal t hbal
  have hiL : i < t.rows.length := by omega
  have hmiM : manifestRow (sliceLo w k) w planes gens scal i
      ∈ genManifest (sliceLo w k) w planes gens scal :=
    List.mem_map_of_mem (List.mem_range.mpr hi)
  by_cases hb : i % (w + 1) = 0
  · -- DOUBLING index: row `i`'s OWN tuple must be a manifest row, and only the zero row fits.
    have htupmem : tupleOf (rowAt t i)
        ∈ exactPublicTable (genManifest (sliceLo w k) w planes gens scal) :=
      hperm.mem_iff.mp (List.mem_map_of_mem (rowAt_mem t i hiL))
    obtain ⟨m, hmM, hmEq⟩ := List.mem_map.mp htupmem
    have hhead : Option.map Int.ofNat m.head?
        = some (guardV (rowAt t i) * ((i : ℤ) + 1)) := by
      rw [← List.head?_map, hmEq, tupleOf_head, htidx i hiL]
    obtain ⟨v, hv⟩ : ∃ v, m.head? = some v := by
      cases hmh : m.head? with
      | none => rw [hmh] at hhead; simp at hhead
      | some v => exact ⟨v, rfl⟩
    rw [hv] at hhead
    have hval : ((v : Nat) : ℤ) = guardV (rowAt t i) * ((i : ℤ) + 1) := by
      simpa [ofNat_eq_cast] using hhead
    have hdi : rowAt t i DBL = 1 := by
      rcases hdbl i with h0 | h1
      · exfalso
        have hg : guardV (rowAt t i) = 1 := by simp [guardV, h0]
        rw [hg, one_mul] at hval
        have hvi : v = i + 1 := by exact_mod_cast hval
        exact (manifest_key_succ _ _ _ _ _ hmM (by rw [hv, hvi])).2 hb
      · exact h1
    have hme : m = manifestRow (sliceLo w k) w planes gens scal i := by
      refine manifest_key_unique _ _ _ _ _ hmM hmiM ?_
      have hg : guardV (rowAt t i) = 0 := by simp [guardV, hdi]
      rw [hg, zero_mul] at hval
      have hv0 : v = 0 := by exact_mod_cast hval
      rw [hv, hv0, manifestRow_head, if_pos hb]
    rw [← hmEq, hme]
  · -- CONDITIONAL-ADD index: the manifest's row `i` must be SOME trace row's tuple, and its key
    -- pins that row to be row `i`.
    have hmiL : (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat
        ∈ t.rows.map tupleOf :=
      hperm.mem_iff.mpr (List.mem_map_of_mem hmiM)
    obtain ⟨r, hr, hrEq⟩ := List.mem_map.mp hmiL
    obtain ⟨j, hj, hjr⟩ : ∃ j, j < t.rows.length ∧ rowAt t j = r := by
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hr
      exact ⟨j, hj, by rw [rowAt_eq t j hj]; exact hje⟩
    have hkey : guardV (rowAt t j) * ((j : ℤ) + 1) = ((i : ℤ) + 1) := by
      have h1 : (tupleOf (rowAt t j)).head?
          = ((manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat).head? := by
        rw [hjr, hrEq]
      rw [tupleOf_head, htidx j hj, List.head?_map, manifestRow_head, if_neg hb] at h1
      have h2 := Option.some.inj h1
      simpa [ofNat_eq_cast] using h2
    have hji : j = i := by
      rcases hdbl j with h0 | h1
      · have hg : guardV (rowAt t j) = 1 := by simp [guardV, h0]
        rw [hg, one_mul] at hkey
        have : (j : ℤ) = (i : ℤ) := by linarith
        exact_mod_cast this
      · exfalso
        have hg : guardV (rowAt t j) = 0 := by simp [guardV, h1]
        rw [hg, zero_mul] at hkey
        have hpos : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
        linarith
    subst hji
    rw [hjr]
    exact hrEq

#assert_axioms manifest_key_unique
#assert_axioms manifest_key_succ
#assert_axioms lookupLog_is_rowMap
#assert_axioms bound_balance
#assert_axioms row_tuple_is_its_manifest_row

/-! ## §5 — WHAT THE FORCED TUPLE SAYS, component by component. -/

section Extract
variable (k w planes : Nat) (gens : List Pt) (scal : List Nat) (t : VmTrace) (i : Nat)

/-- The forced tuple, split into its four components. -/
theorem forced_components
    (h : tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (hb : i % (w + 1) ≠ 0) :
    guardV (rowAt t i) * (rowAt t i TIDX + 1) = ((i + 1 : Nat) : ℤ)
      ∧ guardV (rowAt t i) * (rowAt t i GIDX + 1)
          = ((sliceLo w k + termAt w i + 1 : Nat) : ℤ)
      ∧ guardV (rowAt t i) * rowAt t i BIT
          = ((scalarDigit scal planes (sliceLo w k + termAt w i) (planeAt w i) : Nat) : ℤ)
      ∧ (List.range PTLIMBS).map (fun j => guardV (rowAt t i) * rowAt t i (SRCX + j))
          = (limbsOfPt (gens.getD (sliceLo w k + termAt w i) (0, 0, 0))).map Int.ofNat := by
  rw [tupleOf_cons] at h
  rw [manifestRow, if_neg hb] at h
  simp only [List.map_cons] at h
  obtain ⟨h1, h2, h3, h4⟩ := by
    simpa [List.cons.injEq, and_assoc] using h
  exact ⟨h1, h2, h3, h4⟩

/-- ⚑ **`bound_forces_dbl_off`** — a row INSIDE a plane cannot be a doubling row. Half of the `DBL`
pattern `PastaMsmWindowed` §6.1 left hypothesised. -/
theorem bound_forces_dbl_off
    (h : tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (hb : i % (w + 1) ≠ 0)
    (htidx : rowAt t i TIDX = (i : ℤ))
    (hdbl : rowAt t i DBL = 0 ∨ rowAt t i DBL = 1) :
    rowAt t i DBL = 0 := by
  obtain ⟨h1, -, -, -⟩ := forced_components k w planes gens scal t i h hb
  rcases hdbl with h0 | h1'
  · exact h0
  · exfalso
    rw [guardV, h1', htidx] at h1
    push_cast at h1
    have hpos : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    linarith

/-- ⚑ **`bound_forces_doubling`** — a row AT a plane boundary MUST double. The other half. -/
theorem bound_forces_doubling
    (h : tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (hb : i % (w + 1) = 0)
    (htidx : rowAt t i TIDX = (i : ℤ))
    (hdbl : rowAt t i DBL = 0 ∨ rowAt t i DBL = 1) :
    rowAt t i DBL = 1 := by
  rcases hdbl with h0 | h1
  · exfalso
    have hk : (tupleOf (rowAt t i)).head? = some ((i : ℤ) + 1) := by
      rw [tupleOf_head, guardV, h0, htidx]; norm_num
    rw [h, List.head?_map, manifestRow_head, if_pos hb] at hk
    have hz : (i : ℤ) + 1 = 0 := by simpa using hk.symm
    have hpos : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    linarith
  · exact h1

/-- ⚑ **`bound_forces_source_limbs`** — **the theorem this rung exists for.** A conditional-add
row's `SRC` limb columns ARE the limbs of the generator at the ABSOLUTE index `lo + t`. -/
theorem bound_forces_source_limbs
    (h : tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (hb : i % (w + 1) ≠ 0) (hd : rowAt t i DBL = 0) :
    ∀ j, j < PTLIMBS →
      rowAt t i (SRCX + j)
        = ((coordLimb (gens.getD (sliceLo w k + termAt w i) (0, 0, 0)) j : Nat) : ℤ) := by
  obtain ⟨-, -, -, h4⟩ := forced_components k w planes gens scal t i h hb
  rw [limbsOfPt, List.map_map] at h4
  have := range_map_pointwise PTLIMBS _ _ h4
  intro j hj
  have hj' := this j hj
  rw [guardV, hd] at hj'
  simpa [Function.comp_def] using hj'

/-- ⚑ **`bound_forces_digit`** — the row's conditional bit is the DECLARED digit of the declared
scalar at the declared index. -/
theorem bound_forces_digit
    (h : tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (hb : i % (w + 1) ≠ 0) (hd : rowAt t i DBL = 0) :
    rowAt t i BIT
      = ((scalarDigit scal planes (sliceLo w k + termAt w i) (planeAt w i) : Nat) : ℤ) := by
  obtain ⟨-, -, h3, -⟩ := forced_components k w planes gens scal t i h hb
  rw [guardV, hd] at h3
  linarith

/-- ⚑ **`bound_forces_gidx`** — the row's own term-index column carries the ABSOLUTE index. -/
theorem bound_forces_gidx
    (h : tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (hb : i % (w + 1) ≠ 0) (hd : rowAt t i DBL = 0) :
    rowAt t i GIDX = ((sliceLo w k + termAt w i : Nat) : ℤ) := by
  obtain ⟨-, h2, -, -⟩ := forced_components k w planes gens scal t i h hb
  rw [guardV, hd] at h2
  push_cast at h2 ⊢
  linarith

end Extract

#assert_axioms forced_components
#assert_axioms bound_forces_dbl_off
#assert_axioms bound_forces_doubling
#assert_axioms bound_forces_source_limbs
#assert_axioms bound_forces_digit
#assert_axioms bound_forces_gidx

/-! ## §5b — FROM LIMBS TO THE POINT.

The forced limbs are the DIGITS of the generator's coordinates. That the digits RECONSTRUCT the
coordinate is a canonicality fact about the generator list, not about the AIR — it is exactly the
`Ref.foldLimbs v = v` predicate, and it is a `decide` on the instance's own generators (`§6b`),
never an assumption about arbitrary `Nat`s. -/

/-- The generator list is limb-CANONICAL: every coordinate is recovered by its own 9×30 digits. -/
def LimbCanonical (gens : List Pt) : Prop :=
  ∀ P ∈ gens, Dregg2.Circuit.Emit.PastaField.Ref.foldLimbs P.1 = P.1
    ∧ Dregg2.Circuit.Emit.PastaField.Ref.foldLimbs P.2.1 = P.2.1
    ∧ Dregg2.Circuit.Emit.PastaField.Ref.foldLimbs P.2.2 = P.2.2

/-- A limb block whose columns carry `v`'s digits reconstructs `foldLimbs v`. -/
theorem fpVal_of_limbs (a : Assignment) (base v : Nat)
    (h : ∀ j, j < numLimbs → a (base + j) = ((limbNat v j : Nat) : ℤ)) :
    fpVal a base = ((Dregg2.Circuit.Emit.PastaField.Ref.foldLimbs v : Nat) : ℤ) := by
  rw [fpVal_as_sum, Dregg2.Circuit.Emit.PastaField.Ref.foldLimbs, Nat.cast_list_sum,
    List.map_map]
  refine congrArg List.sum (range_map_congr numLimbs _ _ ?_)
  intro j hj
  rw [h j hj]
  simp [limbNat]
  ring

#assert_axioms fpVal_of_limbs

/-! ## §5c — ⚑⚑ THE COMPOSITION: the manifests TILE the real generator list.

`PastaMsmSliced.slices_compose` composes `n` partials into `msmN as ps` provided partial `k` is
`slicePartial w k as ps` — the SAME index on both lists. What was missing was any reason to believe
slice `k`'s ROWS carry `sliceAt w k ps`. These two theorems supply it: the emitted manifest of slice
`k` names ABSOLUTE index `lo + t = w·k + t` at its `(plane, t)` row, and that is exactly the `t`-th
entry of `sliceAt w k gens`. So the generator list the emitted constraints force IS the one
`slices_compose` pairs against. -/

/-- ⚑ **`manifest_names_slice_index`** — the manifest row at position `(plane, t)` of the schedule
names the ABSOLUTE generator index `lo + t`, for every plane. -/
theorem manifest_names_slice_index (lo w planes : Nat) (gens : List Pt) (scal : List Nat)
    (plane t : Nat) (ht : t < w) :
    manifestRow lo w planes gens scal (plane * (w + 1) + (t + 1))
      = (plane * (w + 1) + (t + 1) + 1) :: (lo + t + 1)
          :: scalarDigit scal planes (lo + t) plane
          :: limbsOfPt (gens.getD (lo + t) (0, 0, 0)) := by
  have hcomm : plane * (w + 1) + (t + 1) = (t + 1) + (w + 1) * plane := by ring
  have hmod : (plane * (w + 1) + (t + 1)) % (w + 1) = t + 1 := by
    rw [hcomm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (plane * (w + 1) + (t + 1)) / (w + 1) = plane := by
    rw [hcomm, Nat.add_mul_div_left _ _ (by omega : 0 < w + 1),
      Nat.div_eq_of_lt (by omega : t + 1 < w + 1)]
    omega
  have hne : (plane * (w + 1) + (t + 1)) % (w + 1) ≠ 0 := by omega
  rw [manifestRow, if_neg hne]
  simp only [termAt, planeAt, hmod, hdiv]
  norm_num

/-- ⚑ **`slice_generator_is_sliceAt`** — the generator at ABSOLUTE index `w·k + t` IS the `t`-th
entry of `PastaMsmSliced.sliceAt w k gens`, the list `slicePartial w k` pairs with slice `k`'s
scalars. This is the join between the CONTENTS forcing and the composition. -/
theorem slice_generator_is_sliceAt (w k t : Nat) (gens : List Pt) (d : Pt) (ht : t < w) :
    gens.getD (sliceLo w k + t) d
      = (Dregg2.Circuit.Emit.PastaMsmSliced.sliceAt w k gens).getD t d := by
  simp [Dregg2.Circuit.Emit.PastaMsmSliced.sliceAt, sliceLo, List.getD,
    List.getElem?_drop, ht]

#assert_axioms manifest_names_slice_index
#assert_axioms slice_generator_is_sliceAt

/-! ## §5d — ⚑ THE TABLE BITES: SATISFIABLE and REFUTABLE, in the kernel.

A forcing theorem whose hypothesis nothing satisfies is TRUE AND EMPTY, and a tamper that the
denotation cannot see is not a tooth. Both polarities are exhibited here over the ACTUALLY EMITTED
manifest and the ACTUALLY EMITTED tuple, at `w = 1, planes = 1` (two rows: one doubling, one
conditional add). -/

/-- The exhibited generator. Not on-curve and not meant to be: what is under test is the CONTENTS
binding, which is a multiset fact about limbs. -/
def katG : List Pt := [(5, 7, 1)]
/-- The exhibited scalar (one plane, digit 1). -/
def katS : List Nat := [1]
/-- Another generator, for the SUBSTITUTION tamper. -/
def katG' : List Pt := [(6, 7, 1)]

/-- The honest doubling row: `DBL = 1`, `TIDX = 0`. -/
def katRow0 : Assignment := fun c => if c = DBL then 1 else 0

/-- The honest conditional-add row: `DBL = 0`, `TIDX = 1`, `GIDX = 0`, `BIT = 1`, and the `SRC`
limb columns carrying the generator. -/
def katRowOf (P : Pt) : Assignment := fun c =>
  if c = TIDX then 1
  else if c = BIT then 1
  else if SRCX ≤ c ∧ c < SRCX + PTLIMBS then ((coordLimb P (c - SRCX) : Nat) : ℤ)
  else 0

/-- The honest two-row trace. -/
def katRows : List Assignment := [katRow0, katRowOf (5, 7, 1)]

-- SATISFIABLE — the honest trace's lookup multiset IS the emitted manifest.
#guard decide ((katRows.map tupleOf).Perm (exactPublicTable (genManifest 0 1 1 katG katS)))

-- ⚑ REFUTABLE — **THE SUBSTITUTED GENERATOR.** One coordinate changed, and the balance breaks.
-- This is the tamper this whole rung exists to catch.
#guard decide (¬ (([katRow0, katRowOf (6, 7, 1)].map tupleOf).Perm
                    (exactPublicTable (genManifest 0 1 1 katG katS))))

-- ⚑ REFUTABLE — the manifest of a DIFFERENT generator list does not accept the honest trace.
#guard decide (¬ ((katRows.map tupleOf).Perm (exactPublicTable (genManifest 0 1 1 katG' katS))))

-- ⚑ REFUTABLE — **DROPPING a term by declaring the row a doubling.** The conditional-add row is
-- turned into a doubling row (its tuple collapses to the zero row); the multiset then has two zero
-- rows where the manifest has one, and the balance breaks. This is what makes the `DBL` PATTERN
-- forced rather than hypothesised.
#guard decide (¬ (([katRow0, fun c => if c = DBL then 1 else 0].map tupleOf).Perm
                    (exactPublicTable (genManifest 0 1 1 katG katS))))

-- ⚑ REFUTABLE — the DIGIT is bound too: flipping the conditional bit breaks the balance.
#guard decide (¬ (([katRow0, fun c => if c = BIT then 0 else katRowOf (5, 7, 1) c].map tupleOf).Perm
                    (exactPublicTable (genManifest 0 1 1 katG katS))))

-- ⚑ REFUTABLE — the ROW KEY is bound: the same generator consumed at the WRONG row index breaks
-- the balance. The manifest is keyed by the THREADED row index, so WHERE a generator is consumed is
-- pinned, not merely THAT it is — which is what closes the mispairing hazard `PastaMsmSliced` §3
-- exhibits, at the level of individual generators rather than whole slices.
#guard decide (¬ (([katRow0, fun c => if c = TIDX then 2 else katRowOf (5, 7, 1) c].map tupleOf).Perm
                    (exactPublicTable (genManifest 0 1 1 katG katS))))
-- ⚑ …and REORDERING the honest rows is HARMLESS — a multiset forgets order, exactly as
-- `PastaMsmSliced.permutation_is_harmless` says. The thread, not the multiset, pins position.
#guard decide (([katRowOf (5, 7, 1), katRow0].map tupleOf).Perm
                 (exactPublicTable (genManifest 0 1 1 katG katS)))

/-! ## §6 — THE PRICE OF THE TABLE, at the deployed tooth's own limits. -/

/-- The exact-public row cap (`descriptor_ir2.rs:403`). -/
def MAX_ROWS : Nat := 128
/-- The exact-public arity cap (`descriptor_ir2.rs:404`). -/
def MAX_ARITY : Nat := 64
/-- The exact-public cell cap (`descriptor_ir2.rs:405`). -/
def MAX_CELLS : Nat := 4096

/-- The manifest's row count IS the trace height: the balance is a PERMUTATION, and the emitted
descriptor carries exactly one lookup, fired on every row. -/
theorem manifest_length (lo w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (genManifest lo w planes gens scal).length = planes * (w + 1) := by
  simp [genManifest]

/-- The manifest's CELL count. -/
def manifestCells (w planes : Nat) : Nat := planes * (w + 1) * TUP

-- ⚑ THE BINDING LIMIT, said in numbers: the row cap is what binds, and it caps a CONTENTS-BOUND
-- instance at 128 rows — 124 real generators across four slices at `(w, planes) = (31, 4)`.
#guard manifestCells 31 4 == 3840
#guard 4 * (31 + 1) == MAX_ROWS
#guard manifestCells 31 4 ≤ MAX_CELLS && TUP ≤ MAX_ARITY
-- …and the REAL cut does not fit by four orders of magnitude. 8,192 generators at 128 planes is
-- 1,048,704 rows at this layout (`PastaIpaDeferral`'s `sliceRows` adds the slice's own `w`
-- accumulation rows on top, 1,056,896), so a per-row exact-public balance would need 1,048,704
-- manifest rows — 8,193× the deployed cap, and one batch AIR INSTANCE each. §7.1.
#guard 128 * (8192 + 1) == 1048704
#guard 1048704 / MAX_ROWS == 8193
-- The EIGHT-way cut (4,096 generators, 528,512 rows, padding to `2^20`) is the cut with real
-- headroom, and it does not change this: it needs 528,512 manifest rows, 4,129× the cap.
#guard 128 * (4096 + 1) == 524416
#guard 524416 / MAX_ROWS == 4097

end Dregg2.Circuit.Emit.PastaMsmBound
