/-
# Dregg2.Circuit.Emit.KimchiPreimageCircuit — a ZKAPP-SHAPED circuit authored in Lean

## ⚑ WHAT THIS IS, AND WHAT IT IS NOT

Every Lean-authored kimchi circuit in this tree so far exists to REPRODUCE a fixed Pickles shape:
`KimchiWrapMain`/`KimchiStepMain` are `wrap_main`/`step_main`, `KimchiRenderPoseidon` is a bare
permutation with `public_input_size = 0` and no statement at all, `KimchiRender` is `p = a·b ∧ p = 35`.
**None of them is a circuit someone would write.** This file is the first one that is: the shape of
a zkApp method body —

    prove I know `x` such that `Poseidon.hash([x]) = c`,  with `c` the ONE PUBLIC INPUT.

That is `Poseidon.hash([x])` in the o1js sense, over Pasta **Fp** — the field an o1js `Field` lives
in and the field a Mina STEP proof is native to (`Vesta`/`Fp`; `wrap_main` is the other side,
`Pallas`/`Fq`). The digest is `PastaPoseidon.Ref.hash [x]`, the same reference that reproduces the
published o1js `Poseidon.hash` KATs, and the gate coefficients are `KimchiCustomGates`'
`poseidonRowCoeffs` — the 165 round constants byte-pinned against o1js.

⚠ **IT IS NOT A MINA-VALID PROOF AND NOT A ZKAPP.** What the companion harness produces is an INNER
kimchi proof on Vesta, verified by `kimchi::verifier`. A Mina account's verification key is a
**wrap-side Pallas** key over a `wrap_main` that bakes per-branch step commitments as constants
(`wrap_main.ml:215-219`), and this circuit has no wrap around it, no `AccountUpdate`, and no
`SmartContract`. Read §6 for the exact list of what stands between the two.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate list (`preimageGates`), the copy-permutation variables,
the placement (`KimchiPlacement.place`, imported read-only) and the witness (`preimageWitness`,
computed from `PastaPoseidon.Ref.permFrom`) are all authored/derived in Lean. `proof-systems`
(tag 0.3.0) is the Rust PROVER that RUNS the emitted artifact; it authors no constraint. House Law #1.

## §0 — the circuit, row by row (14 rows, 1 public)

| abs row | gate | what it does |
|---|---|---|
| 0 | `Generic` (emitted by `place`, coeffs `[1,0,0,0,0]`) | `w₀ − c = 0`; kimchi's `public_poly` supplies the `−c` (`prover.rs:268-271`, `f += &public_poly`), and `verify_generic` subtracts `public[row]` only at `coeffs_offset = 0` (`generic.rs:296-299`) |
| 1..11 | `Poseidon` ×11 | the 55 rounds, 5 per row, coefficients `poseidonRowCoeffs 0..10` |
| 12 | `Zero` | holds `s(55)`; the row-11 gate's `Next` reference is what CONSTRAINS cols 0,1,2 here |
| 13 | `Generic` | `w₀ = 0 ∧ w₃ = 0` — the two IDLE sponge lanes |

and **three copy-permutation classes** carry the whole statement:

* `external 0` = `{(0,0), (12,0)}` — the public word IS the permutation output. Without this the
  circuit proves nothing about `c` at all.
* `internal 0` = `{(1,1), (13,0)}` and `internal 1` = `{(1,2), (13,3)}` — the input state's lanes 1
  and 2 are pinned to `0`. ⚠ Without these the statement WEAKENS to "I know a full 3-lane state `s`
  with `perm(s)₀ = c`", which is not preimage resistance of `hash [·]`; §4 proves the wires are there
  and §4a exhibits the control where they are not.

`x` itself is deliberately UNWIRED — it is the secret, a free witness cell at `(1,0)`.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson
import Dregg2.Circuit.Emit.KimchiAssertEqual
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.KimchiTyp
import Dregg2.Circuit.Emit.PastaPoseidon

namespace Dregg2.Circuit.Emit.KimchiPreimageCircuit

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson
open Dregg2.Circuit.Emit.KimchiAssertEqual
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.PastaPoseidon

set_option autoImplicit false

/-! ## §1 — the statement: what `Poseidon.hash [x]` IS, as a general fact.

The circuit's rows compute one permutation of `[x, 0, 0]`. That is only the right circuit for
`Ref.hash [x]` because of this theorem — which is GENERAL in `x`, not an instance. It is the
sponge's one-block path unfolded: absorb `x` into lane 0 of the zero state (lane counter `0 ≠ rate`),
then squeeze, which permutes once. -/

/-- **The statement this circuit implements.** For every `x`, `Ref.hash [x]` — dregg's reference
for o1js `Poseidon.hash([x])` — is lane 0 of ONE permutation of the state `[x mod p, 0, 0]`. -/
theorem hash_singleton_is_one_permutation (x : Nat) :
    Ref.hash [x] = (Ref.perm [x % PastaField.pN, 0, 0]).getD 0 0 := by
  simp [Ref.hash, Ref.absorbAll, Ref.absorbFrom, Ref.absorbAt, rate, Ref.perm]

/-- The canonical-representative corollary: for a secret already reduced, the padded state carries
`x` itself, which is what the emitted witness puts in cell `(1,0)`. -/
theorem hash_singleton_of_canonical (x : Nat) (hx : x < PastaField.pN) :
    Ref.hash [x] = (Ref.perm [x, 0, 0]).getD 0 0 := by
  rw [hash_singleton_is_one_permutation, Nat.mod_eq_of_lt hx]

/-! ## §2 — the instance: a concrete secret and its digest. -/

/-- The secret preimage. Any canonical field element works; this one is a date. -/
def xSecret : Nat := 20260805

theorem xSecret_is_canonical : xSecret < PastaField.pN := by decide +kernel

/-- The permutation input state: the zero sponge with `xSecret` absorbed into lane 0. -/
def inputState : List Nat := [xSecret, 0, 0]

/-- The Poseidon state after `k` rounds (`PastaPoseidon.Ref.permFrom` — sbox `x⁷`, the `fp_kimchi`
MDS, round constants `rcsN[r]`). -/
def stateAt (k : Nat) : List Nat := Ref.permFrom 0 k inputState

/-- The claimed digest: the ONE public word of this circuit. -/
def digest : Nat := (stateAt 55).getD 0 0

/-- Lane `j` of state `s(k)` as an `Int` (states are `Nat` in `[0, p)`). -/
def laneI (k j : Nat) : Int := ((stateAt k).getD j 0 : Int)

/-! ## §3 — the gate list and its placement.

⚑ **THE PUBLIC INTERFACE IS DERIVED FROM A TYPE, NOT WRITTEN.** `PUB`, the public-input vector
(§5's `preimagePublic`) and the variable each public word occupies all come out of `preimageTyp`
below through `KimchiTyp`. Before that layer existed, all three were hand-written — `PUB := 1`,
`preimagePublic := [(digest : Int)]`, and `external 0` chosen by an author to sit at `{0,0}` — and
nothing compared them to anything. -/

/-- **THE CIRCUIT'S PUBLIC INTERFACE, AS A TYPE.** One field element, named `digest`.

⚠ `felt 255` and not `word 255`: `El (.felt _)` is `Nat`, so the layout carries the SLOT WIDTH and
not the value's range. `digest` is `(stateAt 55).getD 0 0` and its canonicity is a fact about
`PastaPoseidon.Ref.perm` that nothing here proves; a `word 255` would have demanded that proof at
the kernel, through 55 Poseidon rounds. Said rather than hidden — this is exactly the seam
`KimchiTyp`'s header names. -/
def preimageTyp : KimchiTyp.Typ := .tag (.lbl "digest") (.felt 255)

/-- One public word: the claimed digest — **DERIVED**, `(layout preimageTyp).length`. -/
def PUB : Nat := KimchiTyp.pubSize preimageTyp

/-- …and it is the one the hand-written constant asserted. -/
theorem PUB_is_one : PUB = 1 := by rfl

/-- ⚑ **THE PUBLIC WORD'S VARIABLE IS DERIVED TOO.** The layout's one slot claims `external 0` —
the id §4's binding theorem reads at cell `(0,0)`, which an author used to pick. `KimchiArena`
accepts the claim (`KimchiTyp.derived_layouts_always_allocate` says it always will) and
`alloc_injective` makes it the only slot that variable can serve. -/
theorem the_public_word_variable_is_derived :
    KimchiArena.alloc (KimchiTyp.claims preimageTyp 0)
      = .ok ⟨[([KimchiTyp.Step.lbl "digest"], .external 0)], 1, 0⟩ := by decide

/-- ⚑ **AND A DECLARED INTERFACE THAT IS NOT THIS ONE IS REFUSED.** A wrong width — the shape of the
endo-lift defect, where a slot carried a 255-bit lift in a 128-bit prechallenge's place. -/
theorem a_wrong_public_width_is_refused :
    KimchiTyp.check [⟨[KimchiTyp.Step.lbl "digest"], 128⟩] preimageTyp
      = .error (.width 0 [KimchiTyp.Step.lbl "digest"] 128 255) := by decide

/-- …a wrong NAME at the right width — the shape of the `alpha β γ ζ` defect, which no width
signature can see. -/
theorem a_wrong_public_slot_name_is_refused :
    KimchiTyp.check [⟨[KimchiTyp.Step.lbl "commitment"], 255⟩] preimageTyp
      = .error (.order 0 [KimchiTyp.Step.lbl "commitment"] [KimchiTyp.Step.lbl "digest"]) := by
  decide

/-- …and a public word nobody declared. -/
theorem a_wrong_public_arity_is_refused :
    KimchiTyp.check [⟨[KimchiTyp.Step.lbl "digest"], 255⟩, ⟨[KimchiTyp.Step.lbl "salt"], 255⟩]
        preimageTyp
      = .error (.arity 2 1) := by decide

def sevenNones : List (Option PVar) := List.replicate 7 none

/-- Poseidon row 0 additionally EXPOSES its two idle input lanes as copy variables, so the
zero-assert row below can pin them. Col 0 stays `none`: that cell is the secret. -/
def poseidonRow0Vars : List (Option PVar) :=
  [none, some (.internal 0), some (.internal 1), none, none, none, none]

/-- The `Zero` row that receives `s(55)`: col 0 is the public word — ⚑ looked up **by name** out of
`preimageTyp`'s layout, not typed in as `external 0`.

⚑ The `Option` is the refusal, not an inconvenience: `KimchiTyp.varOf` returns `none` for a path the
type does not contain, `permVars` takes `Option PVar` already, and an unwired public cell is exactly
what `placeChecked`'s H2 refuses as `inertPublicWord`. So a misspelled wire cannot reach an
artifact, and it needed no new check to stop it (`a_misnamed_public_wire_does_not_resolve`). -/
def outputRowVars : List (Option PVar) :=
  [KimchiTyp.varOf preimageTyp 0 [.lbl "digest"], none, none, none, none, none, none]

/-- …and it is the id the hand-picked one asserted. -/
theorem the_binding_cell_resolves_to_external_zero :
    outputRowVars = [some (.external 0), none, none, none, none, none, none] := by decide

/-- ⚑ **A MISSPELLED SLOT NAME RESOLVES TO NOTHING** — so the cell goes unwired and the existing H2
refusal, not a new one, is what stops it. `the_control_is_refused_as_an_inert_public_word` (§7a) is
that refusal, exhibited on the object an unwired output row produces. -/
theorem a_misnamed_public_wire_does_not_resolve :
    KimchiTyp.varOf preimageTyp 0 [KimchiTyp.Step.lbl "digets"] = none := by decide

/-- The zero-assert row: `w₀` is the input state's lane 1, `w₃` its lane 2. -/
def zeroAssertVars : List (Option PVar) :=
  [some (.internal 0), none, none, some (.internal 1), none, none, none]

/-- `w₀ = 0` on the first generic sub-gate and `w₃ = 0` on the second
(`c₀·w₀ + … + c₄` and `c₅·w₃ + … + c₉`, `generic.rs:80-110`). -/
def zeroAssertCoeffs : List Int := [1, 0, 0, 0, 0,  1, 0, 0, 0, 0]

/-- **THE CIRCUIT.** 11 Poseidon rows, the `Zero` row that carries the output, and the row that
pins the two idle sponge lanes. `place` prepends the public-input row. -/
def preimageGates : List PGate :=
  ({ kind := .poseidon, permVars := poseidonRow0Vars, coeffs := poseidonRowCoeffs 0 } ::
      (List.range 10).map (fun j =>
        { kind := .poseidon, permVars := sevenNones, coeffs := poseidonRowCoeffs (j + 1) }))
    ++ [ { kind := .zero,    permVars := outputRowVars,  coeffs := [] }
       , { kind := .generic, permVars := zeroAssertVars, coeffs := zeroAssertCoeffs } ]

/-- The placed circuit: `place`'s byte-verified copy-permutation pass at `public_input_size = 1`. -/
def preimagePlaced : List PlacedGate := place PUB preimageGates

/-- Total emitted rows = 1 public + 13 circuit. -/
def NROWS : Nat := 14

theorem preimage_gate_count : preimageGates.length = 13 := by rfl
theorem preimage_placed_count : preimagePlaced.length = NROWS := by rfl

/-- The emitted `typ` ordinals, in row order: the public `Generic`, eleven `Poseidon`, the `Zero`
that carries the output, and the `Generic` that pins the idle lanes. -/
theorem preimage_gate_ordinals :
    preimagePlaced.map (·.kind.ordinal) = [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1] := by rfl

/-! ## §4 — THE BINDING CLAIM, at the emitted object.

These are the theorems that say the circuit means what §0 says it means. They read the σ wires OUT
OF `place`'s output — not out of `preimageGates`, which is the input — so a placement that dropped a
class would show up here. -/

/-- The σ target of cell `(r, c)` in the emitted circuit. -/
def wiresOf (placed : List PlacedGate) (r c : Nat) : Cell :=
  ((placed.getD r ⟨.zero, [], []⟩).wires).getD c ⟨r, c⟩

/-- Shorthand at this circuit. -/
def wireAt (r c : Nat) : Cell := wiresOf preimagePlaced r c

/-- **THE BINDING.** The public cell's σ target is the permutation-output cell: the one public word
and lane 0 of `s(55)` are ONE copy-permutation class, so a proof that verifies against public input
`c` is a proof that the circuit's Poseidon output IS `c`. -/
theorem the_public_cell_wires_to_the_permutation_output : wireAt 0 0 = ⟨12, 0⟩ := by decide

/-- …and back, closing the 2-cycle. -/
theorem the_permutation_output_wires_to_the_public_cell : wireAt 12 0 = ⟨0, 0⟩ := by decide

/-- Idle lane 1 of the input state is in a class with the zero-assert row's first sub-gate. -/
theorem idle_lane1_wires_to_the_zero_assert : wireAt 1 1 = ⟨13, 0⟩ := by decide
theorem the_zero_assert_wires_back_to_idle_lane1 : wireAt 13 0 = ⟨1, 1⟩ := by decide

/-- Idle lane 2 of the input state is in a class with the zero-assert row's SECOND sub-gate
(`w₃`, register offset 3). -/
theorem idle_lane2_wires_to_the_zero_assert : wireAt 1 2 = ⟨13, 3⟩ := by decide
theorem the_zero_assert_wires_back_to_idle_lane2 : wireAt 13 3 = ⟨1, 2⟩ := by decide

/-- **The secret is FREE.** Cell `(1,0)` — where `x` lives — is in no class: it self-wires. That is
the difference between a witness and a public input, at the emitted object. -/
theorem the_secret_cell_is_unconstrained_by_copy : wireAt 1 0 = ⟨1, 0⟩ := by decide

/-! ### §4a — the CONTROL: the binding is a wire, and it can be absent.

A theorem that a cell IS wired says nothing until an object exists where it is NOT. -/

/-- Identical to `preimageGates` except the output row exposes NO variable — so `s(55)` lane 0 is a
singleton and the public word is tied to nothing the circuit computes. -/
def unboundGates : List PGate :=
  ({ kind := .poseidon, permVars := poseidonRow0Vars, coeffs := poseidonRowCoeffs 0 } ::
      (List.range 10).map (fun j =>
        { kind := .poseidon, permVars := sevenNones, coeffs := poseidonRowCoeffs (j + 1) }))
    ++ [ { kind := .zero,    permVars := sevenNones,    coeffs := [] }
       , { kind := .generic, permVars := zeroAssertVars, coeffs := zeroAssertCoeffs } ]

def unboundPlaced : List PlacedGate := place PUB unboundGates

/-- In the control, the output cell self-wires: nothing ties it to the public word. -/
theorem the_control_output_cell_is_a_singleton : wiresOf unboundPlaced 12 0 = ⟨12, 0⟩ := by decide

/-- …and the public cell too, so the control's public input is free. **This is what makes
`the_public_cell_wires_to_the_permutation_output` a claim rather than a description.** -/
theorem the_control_public_cell_is_a_singleton : wiresOf unboundPlaced 0 0 = ⟨0, 0⟩ := by decide

theorem the_binding_wire_is_not_automatic :
    wiresOf unboundPlaced 0 0 ≠ wireAt 0 0 := by decide

/-- The control differs from the circuit ONLY in the output row's variables: the gate kinds, the
coefficients and every other row are identical. So the Rust differential's accept/reject split is
attributable to the wire and to nothing else. -/
theorem the_control_differs_only_in_the_output_row :
    unboundPlaced.map (·.kind.ordinal) = preimagePlaced.map (·.kind.ordinal)
      ∧ unboundPlaced.map (·.coeffs) = preimagePlaced.map (·.coeffs) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-! ## §5 — the witness.

`poseidon.rs::generate_witness`' layout, offset by the one public row: Poseidon row `j` (absolute
row `j+1`) holds `s(5j)` at cols 0,1,2; `s(5j+4)` at 3,4,5; `s(5j+1)` at 6,7,8; `s(5j+2)` at 9,10,11;
`s(5j+3)` at 12,13,14. The final state `s(55)` lands at absolute row 12, cols 0,1,2. -/

/-- Column `col`, absolute row `row` of the 15 × `NROWS` witness grid. -/
def witAt (col row : Nat) : Int :=
  if row = 0 then (if col = 0 then (digest : Int) else 0)
  else if row ≤ 11 then
    let j := row - 1
    if col < 3 then laneI (5 * j) col
    else if col < 6 then laneI (5 * j + 4) (col - 3)
    else if col < 9 then laneI (5 * j + 1) (col - 6)
    else if col < 12 then laneI (5 * j + 2) (col - 9)
    else laneI (5 * j + 3) (col - 12)
  else if row = 12 then (if col < 3 then laneI 55 col else 0)
  else 0

/-- The Lean-computed witness: 15 columns, each `NROWS` long. -/
def preimageWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range NROWS).map (fun row => witAt col row))

/-- The public input vector the verifier is handed — **`store` of the circuit's declared type**, not
a list literal. -/
def preimagePublic : List Int := KimchiTyp.store preimageTyp digest

/-- ⚑ **AND IT IS THE LITERAL IT REPLACES, TERM FOR TERM.** `by rfl`: `store` of a one-leaf `Typ` at
`digest` reduces to `[(digest : Int)]` without ever forcing `digest`, so this is a byte pin on the
emitted vector and not a re-computation of the Poseidon digest. Everything downstream — the JSON's
`public_input` array, the harness's public input, the verification key — is unmoved. -/
theorem the_derived_public_vector_is_the_literal : preimagePublic = [(digest : Int)] := by rfl

/-- The verifier's vector is exactly `readAll`-able back to the value it came from, at this circuit,
cited from the general round trip rather than re-decided. -/
theorem the_public_vector_round_trips :
    KimchiTyp.readAll preimageTyp preimagePublic = some digest :=
  KimchiTyp.readAll_store preimageTyp digest

theorem witness_column_count : preimageWitness.length = 15 := by rfl
theorem witness_row_count : (preimageWitness.getD 0 []).length = NROWS := by rfl
theorem public_vector_length : preimagePublic.length = PUB := by rfl

/-- The secret sits in the free cell, unreduced, exactly as the placement says. -/
theorem the_secret_is_in_the_free_cell : witAt 0 1 = (xSecret : Int) := by decide +kernel

/-- **The witness satisfies the copy constraints the binding rests on** — stated as the equality of
the CELLS, which is what the permutation argument checks. Cheap: all three are structural. -/
theorem the_witness_respects_the_idle_lane_copies :
    witAt 1 1 = witAt 0 13 ∧ witAt 2 1 = witAt 3 13 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The zero-assert row's two constrained registers are `0`, so `c₀·w₀ + c₄ = 0` and
`c₅·w₃ + c₉ = 0` hold at `zeroAssertCoeffs`. -/
theorem the_zero_assert_row_is_satisfied :
    zeroAssertCoeffs.getD 0 0 * witAt 0 13 + zeroAssertCoeffs.getD 4 0 = 0
      ∧ zeroAssertCoeffs.getD 5 0 * witAt 3 13 + zeroAssertCoeffs.getD 9 0 = 0 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-! ## §6 — what the emitted artifact is worth, said at CURRENT resolution.

* The proof the harness produces is an **inner kimchi proof on Vesta/Fp**, accepted by
  `kimchi::verifier::batch_verify`. It is not wrapped, so no Mina verifier has seen it.
* The SRS is kimchi's `new_index_for_test` SRS, **not** Mina's `SRS::<Vesta>::create(2^16)`. A
  verification key derived here is therefore not comparable to a deployed one; `pickles-vk-derive`
  is the crate that uses Mina's own SRS, and it is **Pallas-only** — the wrap side.
* A Mina account's verification key is a **wrap** key. Getting there needs `wrap_main` around this
  circuit with THIS circuit's commitments baked in as `Inner_curve.constant`
  (`wrap_main.ml:215-219`), which is why per-zkApp wrap keys and side-loaded VKs exist at all.
* The Poseidon round constants are byte-pinned against o1js (`KimchiCustomGates` §2a) and the
  digest is dregg's own reference; neither is a claim about the GATE's constraint polynomial, which
  is `proof-systems`' (`poseidon.rs`) and is trusted here, not proved.
-/

#assert_axioms PUB_is_one
#assert_axioms the_binding_cell_resolves_to_external_zero
#assert_axioms a_misnamed_public_wire_does_not_resolve
#assert_axioms the_public_word_variable_is_derived
#assert_axioms a_wrong_public_width_is_refused
#assert_axioms a_wrong_public_slot_name_is_refused
#assert_axioms a_wrong_public_arity_is_refused
#assert_axioms the_derived_public_vector_is_the_literal
#assert_axioms the_public_vector_round_trips
#assert_axioms hash_singleton_is_one_permutation
#assert_axioms hash_singleton_of_canonical
#assert_axioms the_public_cell_wires_to_the_permutation_output
#assert_axioms the_permutation_output_wires_to_the_public_cell
#assert_axioms idle_lane1_wires_to_the_zero_assert
#assert_axioms idle_lane2_wires_to_the_zero_assert
#assert_axioms the_secret_cell_is_unconstrained_by_copy
#assert_axioms the_control_output_cell_is_a_singleton
#assert_axioms the_binding_wire_is_not_automatic
#assert_axioms the_control_differs_only_in_the_output_row
#assert_axioms preimage_gate_ordinals
#assert_axioms the_zero_assert_row_is_satisfied

/-! ## §7 — ⚑ THE SAME BINDING, RE-AUTHORED THROUGH `assertEqual`.

§4's binding is authored the only way that was available: the output row NAMES `external 0`, the
public word's variable, so the two cells are one class because they carry one variable. That works
only because the same author owns both cells. `KimchiAssertEqual` is the primitive that does not need
that, and this section re-authors the binding through it:

  * the output row exposes its OWN variable, `internal 2` — it names nothing of the public interface;
  * the equality `assertEqual (external 0) (internal 2)` is appended as a VALUE.

`internal 2` has `varIx 5`; the public word has `varIx 0`, the global minimum — so the class roots at
the public word and `placeCheckedMerged`'s `publicWordDemoted` check passes rather than being
tiptoed around. The emitted object is then proved BYTE-IDENTICAL to §4's, and the harness measures
the same identity on the two emitted files. -/

/-- The output row, re-authored: it exposes `internal 2`, a variable of its own, and names no part of
the public interface. -/
def outputRowVarsAE : List (Option PVar) :=
  [some (.internal 2), none, none, none, none, none, none]

/-- The re-authored gate list: `preimageGates` with ONLY the output row's variable changed. -/
def preimageGatesAE : List PGate :=
  preimageGates.set 11 { kind := .zero, permVars := outputRowVarsAE, coeffs := [] }

/-- ⚑ **THE EQUALITY, AS A VALUE.** This is the whole re-authoring: one appended pair. -/
def preimageMerges : Merges := [(.external 0, .internal 2)]

/-- The declared census of every binding this circuit makes — AUTHORED. The public word bound to the
permutation output, and the two idle sponge lanes pinned to the zero-assert row. -/
def preimageAliases : List (PVar × Nat) :=
  [(.external 0, 2), (.internal 0, 2), (.internal 1, 2)]

/-- The variable-numbering contract: one public word at `external 0`, and the circuit allocates its
own `external` ids from 1 upward (it allocates none — every variable it owns is `internal`).

⚑ **DERIVED**, like the rest of the interface: `KimchiTyp.contractOf` reads both numbers off the
layout, so `auxBase` is the aux floor rather than a typed-in `1`, and the dead-gap range
`pubSize ≤ i < auxBase` is empty by construction. -/
def preimageContract : Contract := KimchiTyp.contractOf preimageTyp

/-- …and it is the pair the hand-written contract asserted. -/
theorem the_derived_contract_is_the_hand_written_pair : preimageContract = ⟨1, 1⟩ := by rfl

def preimagePlacedAE : List PlacedGate := placeWith preimageMerges PUB preimageGatesAE

/-- ⚑ **THE COMPATIBILITY CLAIM, MEASURED ON THE EMITTED OBJECT.** The circuit whose binding is an
`assertEqual` between two independently-named variables and the circuit whose binding is one variable
written at two cells are **the same placed circuit** — every gate, every coefficient, every one of
the 98 σ cells. -/
theorem the_reauthored_circuit_is_byte_identical : preimagePlacedAE = preimagePlaced := by
  decide +kernel

/-- …and it cost no row, cited from the general theorem rather than re-measured. -/
theorem the_reauthored_binding_costs_zero_rows :
    preimagePlacedAE.length = (place PUB preimageGatesAE).length :=
  assertEqual_costs_zero_rows _ _ _

/-- **The fail-closed merged entry ACCEPTS the re-authored circuit** — closure, no aliased public
words, no demoted public word, the census exactly as declared, and `placeChecked`'s H1/gap/H2 on the
post-merge gate list. -/
theorem the_reauthored_circuit_is_accepted :
    placeCheckedMerged preimageContract [] ⟨preimageMerges, preimageAliases⟩ preimageGatesAE
      = .ok preimagePlaced := by decide +kernel

/-- ⚑ …and the ORIGINAL circuit passes the SAME declaration under no equalities, so the census is a
statement about the circuit and not about the authoring style. -/
theorem the_original_circuit_passes_the_same_declaration :
    placeCheckedMerged preimageContract [] ⟨[], preimageAliases⟩ preimageGates
      = .ok preimagePlaced := by decide +kernel

/-! ### §7a — the CONTROL, re-authored: REMOVE the equality and nothing else.

§4a's control had to DELETE the output row's variable. Through the primitive the control is the
honest one: the same gate list, the same declared shape, with the `assertEqual` **removed** — which
is the counterfactual the negative actually wants. It emits the SAME object as §4a's control, so the
Rust harness's measured teeth (the forgery accepted, the VK digest moving) transfer to it exactly. -/

/-- The control census: without the equality, `external 0` and `internal 2` are singletons, so the
only bindings left are the two idle-lane pins. -/
def unboundAliases : List (PVar × Nat) := [(.internal 0, 2), (.internal 1, 2)]

def unboundPlacedAE : List PlacedGate := placeWith [] PUB preimageGatesAE

/-- **Removing the `assertEqual` IS the control.** Same gates, same coefficients, same witness — and
the public cell and the permutation-output cell are singletons again. -/
theorem removing_the_assertEqual_is_the_control : unboundPlacedAE = unboundPlaced := by
  decide +kernel

/-- ⚑ **THE EQUALITY IS LOAD-BEARING, at the emitted object.** Two placed circuits, one appended pair
apart, and σ differs at exactly the binding cell. -/
theorem the_assertEqual_is_not_automatic : unboundPlacedAE ≠ preimagePlacedAE := by decide

/-- ⚑ …and H2 CATCHES THE MISSING EQUALITY WITHOUT ANY WITNESS OR PROVER. With the equality gone, no
gate reads public word 0: it is an inert, unconstrained input, and the merged entry refuses. **This
is the negative caught statically** — §4a's control could only be caught by the prover. -/
theorem the_control_is_refused_as_an_inert_public_word :
    placeCheckedMerged preimageContract [] ⟨[], unboundAliases⟩ preimageGatesAE
      = .error (.place (.inertPublicWord 0)) := by decide +kernel

#assert_axioms the_derived_contract_is_the_hand_written_pair
#assert_axioms the_reauthored_circuit_is_byte_identical
#assert_axioms the_reauthored_binding_costs_zero_rows
#assert_axioms the_reauthored_circuit_is_accepted
#assert_axioms the_original_circuit_passes_the_same_declaration
#assert_axioms removing_the_assertEqual_is_the_control
#assert_axioms the_assertEqual_is_not_automatic
#assert_axioms the_control_is_refused_as_an_inert_public_word

/-! ## §8 — the JSON render (the shape `pickles-r4-harness`/`pickles-poseidon-harness` parse,
plus the `public_input` vector the wrap harness's shape carries). -/

/-! ⚑ **ONE RENDERER, AND IT TAKES THE PUBLIC VECTOR.** The copy this module carried was written
because none of the seven `pubSize = 0` copies took a `public_input`. Presence is now a field of the
`KimchiCircuit` VALUE (`publicInput := some pub`), not a choice of which copy to call, and
`renderCircuit_public_is_the_open_coded_shape` pins over EVERY argument that
`KimchiCircuitJson.renderCircuit` emits the chain this module's copy emitted.

⚠ `some []` is NOT `none`: the empty vector still emits `"public_input":[],`. That is what the wrap
and step rungs below their closing rung emit, and it is why presence is carried rather than inferred
from emptiness (`optField_some_nil_still_emits_the_key`). -/
/-- The emitted preimage circuit. -/
def preimageJson : String :=
  renderCircuit { name := "poseidonPreimage", pubSize := PUB, numRows := NROWS
                , gates := preimagePlaced, witness := preimageWitness
                , publicInput := some preimagePublic }

/-- The CONTROL circuit: same gates, same coefficients, same witness, **no binding wire**. -/
def unboundJson : String :=
  renderCircuit { name := "poseidonPreimageUNBOUND", pubSize := PUB, numRows := NROWS
                , gates := unboundPlaced, witness := preimageWitness
                , publicInput := some preimagePublic }

/-- The circuit with its binding re-authored through `assertEqual`. Emitted under the SAME name, so
the harness's byte-diff against `preimage.json` is a diff of two independently-produced artifacts and
not of two names. -/
def preimageJsonAE : String :=
  renderCircuit { name := "poseidonPreimage", pubSize := PUB, numRows := NROWS
                , gates := preimagePlacedAE, witness := preimageWitness
                , publicInput := some preimagePublic }

/-- Its control: the same gate list with the `assertEqual` REMOVED. -/
def unboundJsonAE : String :=
  renderCircuit { name := "poseidonPreimageUNBOUND", pubSize := PUB, numRows := NROWS
                , gates := unboundPlacedAE, witness := preimageWitness
                , publicInput := some preimagePublic }

/-- ⚑ **BYTE-IDENTICAL EMISSIONS**, not merely equal placements: the two render calls agree
character for character, so the harness's `assert_eq!` on the raw files is measuring the same fact
this theorem states. -/
theorem the_reauthored_json_is_byte_identical : preimageJsonAE = preimageJson := by
  unfold preimageJsonAE preimageJson
  rw [the_reauthored_circuit_is_byte_identical]

theorem the_reauthored_control_json_is_byte_identical : unboundJsonAE = unboundJson := by
  unfold unboundJsonAE unboundJson
  rw [removing_the_assertEqual_is_the_control]

#assert_axioms the_reauthored_json_is_byte_identical
#assert_axioms the_reauthored_control_json_is_byte_identical

end Dregg2.Circuit.Emit.KimchiPreimageCircuit
