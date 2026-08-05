/-
# Dregg2.Circuit.Emit.KimchiConditionalCircuit — A CONDITIONAL, AUTHORED

## ⚑ WHAT THIS ANSWERS

`KimchiPreimageCircuit` was the tree's first non-`wrap_main` circuit, and it deliberately **uses no
conditional and no boolean** — which is why it was the right smallest thing and why the next
circuit needed a gadget rail. This is that next circuit, and it is the shortest honest answer to
"can someone author a conditional in our Lean now":

    prove that the ONE PUBLIC WORD is `if b then t else e`, for a secret boolean `b`.

Its entire gate list is **one gadget call** — `packHalvesPG (selectChecked b ⟨t,e,d,m,out⟩)` — and
its variables are **allocated, not picked**: no `internal 0` appears anywhere in this file.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** Gates, variables, placement and witness are authored/derived in
Lean; `proof-systems` would be the Rust prover that RUNS it. House Law #1.

## §0 — the circuit, row by row (3 rows, 1 public)

| abs row | gate | halves | what it does |
|---|---|---|---|
| 0 | `Generic` (from `place`) | — | `w₀ − out = 0`, kimchi's `public_poly` supplies `−out` |
| 1 | `Generic` | `boolHalf b`, `subHalf t e d` | `b² − b = 0` and `d = t − e` |
| 2 | `Generic` | `mulHalf b d m`, `addHalf e m out` | `m = b·d` and `out = e + m` |

and **one copy-permutation class carries the statement**: `out` at `(0,0)` and `(2,5)` — the public
word IS the mux output. §4a is the control where that wire is absent.

⚠ `t`, `e` and `b` are witnesses; `b` is the secret whose branch the proof does not reveal, which is
the only reason a conditional is interesting in a circuit at all.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.KimchiGadgets
import Dregg2.Circuit.Emit.KimchiAssertEqual
import Dregg2.Circuit.Emit.KimchiPreimageCircuit

namespace Dregg2.Circuit.Emit.KimchiConditionalCircuit

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiArena
open Dregg2.Circuit.Emit.KimchiGadgets
open Dregg2.Circuit.Emit.KimchiAssertEqual (Merges rootVar mergedPositions)

set_option autoImplicit false
-- `decide` here evaluates `place` THROUGH the arena lookup, which is a deeper reduction than the
-- hand-picked circuits needed. ⚠ A `set_option` does not cross an import; this is file-local.
set_option maxRecDepth 100000

/-! ## §1 — the variables, ALLOCATED.

A `deriving DecidableEq` slot enum: a misspelled slot is an elaboration error, and exhaustiveness
over the slots is `decide`-able because the enum is finite. -/

/-- The circuit's variable roles. -/
inductive CSlot where
  /-- the public word: the selected value -/
  | out
  /-- the secret selector -/
  | b
  /-- the `then_` branch -/
  | t
  /-- the `else_` branch -/
  | e
  /-- auxiliary: the sealed difference `t − e` -/
  | d
  /-- auxiliary: the masked difference `b·(t − e)` -/
  | m
  deriving Repr, DecidableEq, Inhabited

/-- Every slot, for the exhaustiveness check. -/
def allSlots : List CSlot := [.out, .b, .t, .e, .d, .m]

/-- ⚑ **THE ALLOCATION.** `out` is pinned to `external 0` because kimchi's public-input rows are
positional (`place` wires `external i` at `{i,0}`); everything else is FRESH. The two auxiliaries
`d`/`m` are the cells a hand-written mux has to invent ids for — here they are `internal 0` and
`internal 1` because the allocator said so, not because anyone counted. -/
def condClaims : List (Claim CSlot) :=
  [ .extAt .out 0, .ext .b, .ext .t, .ext .e, .int .d, .int .m ]

/-- The arena. -/
def condArena : Arena CSlot := (alloc condClaims).toOption.getD {}

/-- ⚑ **THE ALLOCATION IS ACCEPTED** — no slot and no variable was claimed twice. -/
theorem condArena_allocates : alloc condClaims = .ok condArena := by decide

/-- Every slot resolves. -/
theorem condArena_covers : condArena.covers allSlots = true := by decide

/-- Slot → variable. -/
def V (s : CSlot) : PVar := condArena.v s

/-- What the allocator handed out. Recorded so the ids are READABLE, not so anything depends on
them: nothing below mentions a literal `internal 0`. -/
theorem condArena_assignment :
    (V .out, V .b, V .t, V .e, V .d, V .m)
      = (PVar.external 0, PVar.external 1, PVar.external 2, PVar.external 3,
         PVar.internal 0, PVar.internal 1) := by decide

/-! ## §2 — the circuit: ONE gadget call. -/

/-- One public word: the selected value. -/
def PUB : Nat := 1

/-- The mux's five wires. -/
def condMux : MuxWires := ⟨V .t, V .e, V .d, V .m, V .out⟩

/-- **THE CIRCUIT'S HALVES** — `Field.if_` with its selector pinned. -/
def condHalves : List Half := selectChecked (V .b) condMux

/-- **THE CIRCUIT.** `place` prepends the public-input row. -/
def condGates : List PGate := packHalvesPG condHalves

/-- The placed circuit. -/
def condPlaced : List PlacedGate := place PUB condGates

theorem cond_half_count : condHalves.length = 4 := rfl
theorem cond_gate_count : condGates.length = 2 := by
  simp [condGates, packHalvesPG_length, condHalves, rowsOfHalves, selectChecked, selectHalves]

/-- Two circuit rows plus the public row. -/
def NROWS : Nat := 3

theorem cond_placed_count : condPlaced.length = NROWS := by decide

/-- The emitted `typ` ordinals: three `Generic`. -/
theorem cond_gate_ordinals : condPlaced.map (·.kind.ordinal) = [1, 1, 1] := by decide

/-- The emitted coefficients, row by row — `cBool ++ cSub` then `cMul ++ cAdd`, with `place`'s own
public row in front. **This is the printed diff of the emitted object.** -/
theorem cond_coefficients :
    condPlaced.map (·.coeffs)
      = [ [1, 0, 0, 0, 0]
        , [-1, 0, 0, 1, 0,  1, -1, -1, 0, 0]
        , [ 0, 0, -1, 1, 0, 1,  1, -1, 0, 0] ] := by decide

/-! ## §3 — ⚑ NO UNINTENTIONAL ALIAS, at the emitted object.

`alloc_injective` says distinct slots never share a variable, for every claim list. These two say
the CIRCUIT respects that: every variable it mentions came from the arena, and it contains exactly
as many distinct variables as the arena handed out. A collision drops that count by one and the
theorem goes red.

⚠ On its own that check does NOT survive the merge seam — a merge lowers the count too, innocently.
§3b is the version that does. -/

/-- ⚑ **CLOSURE.** Every variable in the circuit's placement positions was allocated. A hand-picked
`.internal 0` written inline would not be, and this goes false. -/
theorem cond_closes : condArena.closes (circuitPositions PUB condGates) = true := by decide

/-- ⚑ **THE LEDGER.** Six distinct variables in the emitted circuit, six slots in the arena. -/
theorem cond_no_unintended_alias : circuitVarCount PUB condGates = condArena.size := by decide

theorem cond_variable_count : circuitVarCount PUB condGates = 6 := by decide

/-! ### §3a — the ledger BITES.

A circuit whose author collided two roles has one fewer variable, and the ledger says so. This is
the `exposedVars` shape at the emitted object rather than at the claim list. -/

/-- The same circuit with the `then_` and `else_` branches accidentally given ONE variable — the
collision an allocator refuses and a hand-picked layout does not. -/
def aliasedGates : List PGate :=
  packHalvesPG (selectChecked (V .b) ⟨V .t, V .t, V .d, V .m, V .out⟩)

/-- ⚑ **AND THE COUNT DROPS.** Five distinct variables where the arena has six. -/
theorem aliased_ledger_drops : circuitVarCount PUB aliasedGates = 5 := by decide

theorem aliased_ledger_disagrees_with_the_arena :
    circuitVarCount PUB aliasedGates ≠ condArena.size := by decide

/-! ### §3b — ⚑ AND THE LEDGER SURVIVES THE MERGE SEAM.

`KimchiAssertEqual` landed the zero-row `assertEqual`: merging is a RENAME of `PVar`s composed into
`circuitPositions` (`assertEqual_is_naming_the_same_variable`). So merging DOES lower the
distinct-variable count — which is the whole difficulty, because it makes a lower count innocent.

The resolution is that the drop must be **attributable**. After merges `ms`, the circuit's distinct
variables plus the number of arena variables `ms` actually absorbed must equal the arena's size. It
balances exactly when every shared copy class is either ONE SLOT or ONE NAMED MERGE EDGE.

⚠ This is the honest boundary: the ledger detects an alias the merge list does not explain. It
cannot detect a *wrong* merge — an `assertEqual` the author wrote and should not have. That is a
statement about intent, and no allocator can reach it. -/

/-- Distinct variables in the emitted circuit AFTER the authored equalities. -/
def mergedVarCount (ms : Merges) (pub : Nat) (gates : List PGate) : Nat :=
  ((mergedPositions ms (circuitPositions pub gates)).map Prod.fst).dedup.length

/-- How many of the arena's variables the equalities actually absorbed — merges that unioned two
DISTINCT roots. An `assertEqual x x` counts zero, which is right. -/
def effectiveMerges (ms : Merges) (a : Arena CSlot) : Nat :=
  a.size - (a.vars.map (rootVar ms)).dedup.length

/-- ⚑ **THE ACCOUNTING.** Emitted distinct variables + absorbed variables = allocated variables. -/
def ledgerBalances (ms : Merges) (a : Arena CSlot) (pub : Nat) (gates : List PGate) : Bool :=
  mergedVarCount ms pub gates + effectiveMerges ms a == a.size

/-- With no equalities, the clean circuit balances. -/
theorem ledger_balances_with_no_merges :
    ledgerBalances [] condArena PUB condGates = true := by decide

/-- An INTENTIONAL alias — an explicit `assertEqual t e` edge. -/
def condMerges : Merges := [(V .t, V .e)]

/-- It genuinely merges: the emitted circuit loses a variable. -/
theorem the_merge_drops_a_variable :
    mergedVarCount condMerges PUB condGates = 5 := by decide

/-- ⚑ **AND THE LEDGER STILL BALANCES**, because the drop is attributable to the named edge. -/
theorem ledger_balances_with_an_intentional_merge :
    ledgerBalances condMerges condArena PUB condGates = true := by decide

/-- ⚑ **THE UNINTENTIONAL ALIAS DOES NOT BALANCE.** `aliasedGates` loses exactly the same variable —
same count, `5` — with NO merge edge to account for it. **That is the answer to "can an
unintentional alias still be detected once merging exists": yes, and this is the theorem.** The two
circuits are indistinguishable by variable count alone and distinguished by the ledger. -/
theorem ledger_catches_the_unintentional_alias :
    ledgerBalances [] condArena PUB aliasedGates = false := by decide

/-- The pair, side by side: identical emitted variable counts, opposite verdicts. -/
theorem the_ledger_separates_intended_from_unintended :
    mergedVarCount condMerges PUB condGates = mergedVarCount [] PUB aliasedGates
      ∧ ledgerBalances condMerges condArena PUB condGates
          ≠ ledgerBalances [] condArena PUB aliasedGates := by
  refine ⟨by decide, by decide⟩

/-! ## §4 — THE BINDING CLAIM, read out of `place`'s output. -/

/-- The σ target of cell `(r, c)`. -/
def wireAt (r c : Nat) : Cell := KimchiPreimageCircuit.wiresOf condPlaced r c

/-- **THE BINDING.** The public cell and the mux output are ONE copy class, so a proof that
verifies against public input `out` is a proof that the circuit's conditional produced `out`. -/
theorem the_public_cell_wires_to_the_mux_output : wireAt 0 0 = ⟨2, 5⟩ := by decide

/-- …and back, closing the 2-cycle. -/
theorem the_mux_output_wires_to_the_public_cell : wireAt 2 5 = ⟨0, 0⟩ := by decide

/-- **The selector's class is closed and PRIVATE.** `b` occupies three cells — the two squared
slots of its booleanity half and the multiplier slot of the mux — and they cycle among themselves:
`(1,0) → (1,1) → (2,0) → (1,0)`. None of them is the public cell, so the branch taken is not
disclosed. That is what makes this a conditional rather than a disclosure. -/
theorem the_selector_class_is_closed_and_private :
    wireAt 1 0 = ⟨1, 1⟩ ∧ wireAt 1 1 = ⟨2, 0⟩ ∧ wireAt 2 0 = ⟨1, 0⟩ := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The sealed difference is WIRED.** `d`'s defining cell `(1,5)` and its use as the mux's
multiplicand `(2,1)` are one class; without this the multiply would take an unrelated cell and the
"conditional" would mask nothing. -/
theorem the_sealed_difference_is_wired :
    wireAt 1 5 = ⟨2, 1⟩ ∧ wireAt 2 1 = ⟨1, 5⟩ := by
  refine ⟨by decide, by decide⟩

/-- **And the `else_` branch reaches the final add.** `e` at `(1,4)` (its subtraction) and `(2,3)`
(the add that produces `out`). -/
theorem the_else_branch_is_wired :
    wireAt 1 4 = ⟨2, 3⟩ ∧ wireAt 2 3 = ⟨1, 4⟩ := by
  refine ⟨by decide, by decide⟩

/-! ### §4a — the CONTROL: the binding is a wire, and it can be absent. -/

/-- Identical except the output half exposes no variable in the result column. -/
def unboundGates : List PGate :=
  packHalvesPG [ boolHalf (V .b), subHalf (V .t) (V .e) (V .d)
               , mulHalf (V .b) (V .d) (V .m)
               , ([some (V .e), some (V .m), none], cAdd) ]

def unboundPlaced : List PlacedGate := place PUB unboundGates

/-- In the control the public cell is a singleton: the public input is tied to nothing. -/
theorem the_control_public_cell_is_a_singleton :
    KimchiPreimageCircuit.wiresOf unboundPlaced 0 0 = ⟨0, 0⟩ := by decide

/-- **This is what makes the binding theorem a claim rather than a description.** -/
theorem the_binding_wire_is_not_automatic :
    KimchiPreimageCircuit.wiresOf unboundPlaced 0 0 ≠ wireAt 0 0 := by decide

/-- The control differs ONLY in that one wire: same gate kinds, same coefficients. -/
theorem the_control_differs_only_in_the_output_wire :
    unboundPlaced.map (·.kind.ordinal) = condPlaced.map (·.kind.ordinal)
      ∧ unboundPlaced.map (·.coeffs) = condPlaced.map (·.coeffs) := by
  refine ⟨by decide, by decide⟩

/-! ## §5 — the witness, and the FALSIFIER.

`halfEvalInt` over `ℤ`, so a satisfying assignment is `decide`-able; `halfEval_ofInt` is why an
integer witness is evidence about the field circuit. The values are chosen non-negative so no
modular reduction hides in the check. -/

/-- Slot values: `b = 1`, so the conditional must select `t`. -/
def condVals : CSlot → Int
  | .out => 22 | .b => 1 | .t => 22 | .e => 11 | .d => 11 | .m => 11

/-- Slot values with the selector OFF: `b = 0`, so it must select `e`. -/
def elseVals : CSlot → Int
  | .out => 11 | .b => 0 | .t => 22 | .e => 11 | .d => 11 | .m => 0

/-- ⚑ **THE FALSIFIER.** `b = 2` — not a boolean. The mux still computes `e + b·(t − e) = 33`,
which is NEITHER branch. -/
def escapeVals : CSlot → Int
  | .out => 33 | .b => 2 | .t => 22 | .e => 11 | .d => 11 | .m => 22

/-- A slot assignment, as the `PVar → Int` the evaluator wants. -/
def wOf (f : CSlot → Int) : PVar → Int := fun p =>
  match allSlots.find? (fun s => decide (V s = p)) with
  | some s => f s
  | none   => 0

/-- The `then_` witness satisfies every half. -/
theorem then_witness_satisfies :
    (condHalves.map (halfEvalInt (wOf condVals))).all (fun z => decide (z = 0)) = true := by decide

/-- The `else_` witness satisfies every half — the conditional genuinely takes both branches. -/
theorem else_witness_satisfies :
    (condHalves.map (halfEvalInt (wOf elseVals))).all (fun z => decide (z = 0)) = true := by decide

/-- The two witnesses put DIFFERENT values in the public word, which is the whole content of
"the circuit computes a conditional". -/
theorem the_branches_differ : condVals .out ≠ elseVals .out := by decide

/-! ### §5a — ⚑ the booleanity gate is LOAD-BEARING, proved by exhibiting what it refuses. -/

/-- The three halves of the mux WITHOUT its selector pinned — Snarky's `Field.if_` and gnark's
`api.Select` as they actually are. -/
def uncheckedHalves : List Half := selectHalves (V .b) condMux

/-- ⚑ **THE UNCHECKED MUX ACCEPTS `b = 2`.** Every one of its halves vanishes. -/
theorem escape_satisfies_the_unchecked_mux :
    (uncheckedHalves.map (halfEvalInt (wOf escapeVals))).all (fun z => decide (z = 0)) = true := by
  decide

/-- ⚑ **AND THE CHECKED ONE REFUSES IT** — at the booleanity half, and only there. -/
theorem escape_violates_booleanity :
    halfEvalInt (wOf escapeVals) (boolHalf (V .b)) ≠ 0 := by decide

/-- The escape output is neither branch, so this is a real forgery and not a relabelling. -/
theorem escape_is_neither_branch :
    escapeVals .out ≠ escapeVals .t ∧ escapeVals .out ≠ escapeVals .e := by
  refine ⟨by decide, by decide⟩

/-- ⚠ **AND THE UNCHECKED MUX COSTS THE SAME NUMBER OF ROWS.** Three halves and four halves both
pack into two `Generic` rows, so the booleanity gate is FREE in rows and paid for only in a
coefficient. A row-count comparison against o1js would not have noticed its absence. -/
theorem booleanity_is_free_in_rows :
    rowsOfHalves uncheckedHalves = rowsOfHalves condHalves := by
  simp [rowsOfHalves, uncheckedHalves, condHalves, selectHalves, selectChecked]

/-! ## §6 — ⚑ THE EMITTED OBJECT DID NOT MOVE: the allocator reproduces a hand-picked circuit.

`KimchiPreimageCircuit` was authored with `external 0`, `internal 0`, `internal 1` written by hand.
Allocating the same three roles gives the same three variables and the same `permVars` — so
adopting the allocator is not a re-emission. -/

/-- The preimage circuit's three variable roles. -/
inductive PSlot where
  | digest | idle1 | idle2
  deriving Repr, DecidableEq, Inhabited

def preimageClaims : List (Claim PSlot) := [.extAt .digest 0, .int .idle1, .int .idle2]

def preimageArena : Arena PSlot := (alloc preimageClaims).toOption.getD {}

theorem preimageArena_allocates : alloc preimageClaims = .ok preimageArena := by decide

/-- ⚑ **THE SAME VARIABLES.** -/
theorem preimage_arena_reproduces_the_hand_picked_ids :
    (preimageArena.v .digest, preimageArena.v .idle1, preimageArena.v .idle2)
      = (PVar.external 0, PVar.internal 0, PVar.internal 1) := by decide

/-- ⚑ **AND THE SAME EMITTED ROWS.** The three `permVars` lists `KimchiPreimageCircuit` wrote by
hand, rebuilt from the arena, are equal — so the circuit whose 12 σ-wire theorems and 94.7 ms
prove/verify already exist would emit byte-identically under the allocator. -/
theorem preimage_arena_reproduces_the_emitted_rows :
    ([none, some (preimageArena.v .idle1), some (preimageArena.v .idle2), none, none, none, none]
       = KimchiPreimageCircuit.poseidonRow0Vars)
    ∧ ([some (preimageArena.v .digest), none, none, none, none, none, none]
       = KimchiPreimageCircuit.outputRowVars)
    ∧ ([some (preimageArena.v .idle1), none, none, some (preimageArena.v .idle2), none, none, none]
       = KimchiPreimageCircuit.zeroAssertVars) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The preimage circuit's own ledger: three distinct variables, three slots. -/
theorem preimage_no_unintended_alias :
    circuitVarCount KimchiPreimageCircuit.PUB KimchiPreimageCircuit.preimageGates
      = preimageArena.size := by decide

/-! ## §7 — what this artifact is worth, at CURRENT resolution.

* The gate list, the placement and the witness are Lean values with named theorems over them. **No
  proof has been produced for this circuit** — `pickles-preimage-harness` is the shape that would
  run it, and making one emit driver serve both is explicitly the NEXT lane's item, not this one.
* The coefficient vectors are pinned against o1js 2.15.0's own emission
  (`bridge/mina-zkapp/scripts/kimchi-gadget-oracle.mjs`). That is differential fidelity, **not** a
  soundness proof of `proof-systems`' `generic.rs`, whose constraint polynomial is trusted here.
* `selectChecked_sound` and `boolHalf_zero_iff` are field-general theorems about `halfEval`, which
  is dregg's transcription of the double-generic gate — not `proof-systems`' own code.
-/

#assert_axioms condArena_allocates
#assert_axioms cond_closes
#assert_axioms cond_no_unintended_alias
#assert_axioms aliased_ledger_drops
#assert_axioms the_public_cell_wires_to_the_mux_output
#assert_axioms the_binding_wire_is_not_automatic
#assert_axioms then_witness_satisfies
#assert_axioms else_witness_satisfies
#assert_axioms escape_satisfies_the_unchecked_mux
#assert_axioms escape_violates_booleanity
#assert_axioms preimage_arena_reproduces_the_emitted_rows
#assert_axioms ledger_balances_with_an_intentional_merge
#assert_axioms ledger_catches_the_unintentional_alias
#assert_axioms the_ledger_separates_intended_from_unintended
#assert_axioms preimage_no_unintended_alias

end Dregg2.Circuit.Emit.KimchiConditionalCircuit
