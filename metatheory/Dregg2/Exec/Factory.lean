/-
# Dregg2.Exec.Factory — the FactoryDescriptor and constructor transparency.

`STORAGE-AS-CELL-PROGRAMS.md §1–§2` / `cand-A` / `gaps-1(e)`: the EROS-style **constructor**
that `gaps-1` flagged MISSING. It is the delivery mechanism for the whole *storage-as-cell-
programs* thesis: a storage primitive (`CapInbox`, `ProgrammableQueue`, `PubSubTopic`, …) is
NOT a new `Effect` — it is a **published, content-addressed contract** (a `FactoryDescriptor`)
that mints conforming cells. The descriptor carries a `Schema` (the child cell's field layout)
and a `RecordProgram` (the `StateConstraint` set every child carries for its *whole life*),
content-addressed by a `vk`. `createFromFactory` mints a cell whose program **IS** the factory's
program.

The keystone is **constructor transparency** (`STORAGE-AS-CELL-PROGRAMS.md §1.2`, last ¶ of §2):
*"anyone with the `factory_vk` can read the descriptor and know exactly what invariants the cell
will carry over its lifetime."* In Lean that becomes two proved facts HERE plus one that this file
is the wrong place for:
  1. `factory_mints_conforming` — the minted cell's `program` is EXACTLY the descriptor's
     `program` (no hidden behavior: what you publish is what the child runs);
  2. `factory_cell_step_admitted` — EVERY transition on a minted cell is gated by the factory's
     `StateConstraint`s (lift `RecordCell.recExec_admitted` to the minted cell), so the published
     invariants hold over the cell's whole life;
  3. the CONTENT-ADDRESS leg — *equal `vk` ⇒ equal `(schema, program)`* — is NOT stated here. It
     used to be, as `vk_determines_invariants` / `vk_determines_program` conditioned on
     `HashInjective`; that hypothesis is FALSE at BLAKE3's width, so both were vacuous and are
     DELETED (see the TOMBSTONE § near the end of this file). The live statement is a
     concrete-security one:
     `Crypto.FactoryBindingFloorRegrounded.vk_determines_invariants_binds_rom` — every
     query-bounded factory forger has negligible advantage — with the collision-floor sibling
     `vk_determines_invariants_advantage_bound` beside it.

Pure, computable, `#eval`-able; imports only `Exec.RecordCell` (which pulls `Program`/`Value`),
so it type-checks fast. Reuses `recExec` / `recExec_admitted` unchanged — the factory is the
*publisher* of the program that `recExec` gates by.
-/
import Dregg2.Exec.RecordCell

namespace Dregg2.Exec.Factory

open Dregg2.Exec
open Dregg2.Exec.RecordCell

/-! ## `FactoryVk` — the content-hash identity of a factory (abstract, and NOT an injective id). -/

/-- **`FactoryVk`** — the factory's content-addressed identity (`STORAGE-AS-CELL-PROGRAMS.md §2`:
*"`factory_vk`: BLAKE3 of the descriptor"*). Kept as an opaque `Nat`. A content hash is an abstract
id but NOT an injective one: at BLAKE3's 256-bit width it cannot be, and this file no longer
pretends otherwise (see `HashInjective` and the TOMBSTONE §). Its *collision-resistance* — that
colliding contracts are hard to FIND — is a §8 crypto-interface obligation, discharged by the hash
circuit and stated as a game in `Crypto.FactoryBindingFloorRegrounded`, never by a Lean law and
never as a hypothesis here. -/
abbrev FactoryVk := Nat

/-! ## The content-hash of `(schema, program)` — abstract, and NOT injective.

An injective map `(Schema × RecordProgram) → FactoryVk` would state the content-address leg
directly. There is no such map at the deployed parameters: `Schema × RecordProgram` is INFINITE
and `factory_vk` is a 256-bit BLAKE3 digest, so pigeonhole refutes injectivity outright
(`Crypto.FactoryBindingFloorRegrounded.hashInjective_false_blake3`). We therefore keep the hash
**opaque** (a parameter), keep `HashInjective` below as the NAMED, REFUTED carrier so the
refutation has something to point at, and state the content-address leg where it can be true — as
a concrete-security bound over a collision game, in `Crypto.FactoryBindingFloorRegrounded`. What
lives in this file is what needs no crypto at all: minting, the lifetime gate, and the FUNCTIONAL
direction (`same_content_same_vk`). -/

/-- **`factoryHash`** — the abstract content-hash of a factory's published content
`(schema, program)`. Modeled as an opaque function; we do NOT unfold it. The only fact anything in
this file uses about it is that it IS a function (`same_content_same_vk`). Its *content-address
binding* — the §8 obligation, collision-resistance of BLAKE3 in the real system — is stated over
this same `factoryHash` in `Crypto.FactoryBindingFloorRegrounded` (the `factoryHashFamily` /
`factoryRomFamily` games), never as a hypothesis here. -/
opaque factoryHash : Schema → RecordProgram → FactoryVk

/-- **`HashInjective` (§8 OBLIGATION)** — ⚠ **REFUTED AT BLAKE3's REAL OUTPUT WIDTH. NOTHING MAY
CONSUME IT.** Stated as injectivity of the content hash, which is FALSE by cardinality
(`Crypto.FactoryBindingFloorRegrounded.hashInjective_false_blake3`): the published content
`Schema × RecordProgram` is INFINITE while `factory_vk` is *"BLAKE3 of the descriptor"*
(`STORAGE-AS-CELL-PROGRAMS.md §2`) — a 256-bit digest — so pigeonhole forces two distinct contracts to
share a `vk`. Its two consumers — `vk_determines_invariants` / `vk_determines_program`, which were the
formal content of CONSTRUCTOR TRANSPARENCY — were therefore VACUOUSLY TRUE at deployed parameters and
are DELETED (see the TOMBSTONE § below). `#assert_axioms` was blind to it: the proofs were
clean; the *hypothesis* was the flaw. KEPT for the record (`VACUITY-SWEEP.md` FINDING 2), and kept as
a `Verify.FloorCensus` SENTINEL: the def is the thing the refutation names, so deleting it would
delete the proof that it is false.

⚑ The docstring below was always RIGHT about the KIND of assumption ("collision-resistance of the content
hash") and wrong about its SHAPE: collision-resistance means collisions are hard to FIND, never that they
do not EXIST. Honest replacement:
`Crypto.FactoryBindingFloorRegrounded.vk_determines_invariants_advantage_bound` — a factory forger
(two WELL-FORMED descriptors, one `vk`, different contracts) reduces to a genuine `factoryHash` collision,
negligible under `FloorGames.HashCRHardQuant _ Eff` at an EXPLICIT adversary class. NOT
`HashFloorHonesty.CollisionResistant`, which is that floor at `⊤` and itself false
(`FloorGames.hashCRHardQuant_top_false_of_compressing`).

The INTENT, preserved: content-addressing means the hash binds its preimage — two factories with the same
`vk` published the same `(schema, program)`. That is a crypto-interface obligation (the hash *circuit's*
extractability), NOT a Lean theorem, and the original was right to refuse to merge crypto-soundness into
the Lean law (`REORIENT.md §6`). Where it went wrong was the next step: surfacing the obligation as a
LOCAL HYPOTHESIS on the theorems that wanted it, which converts "not proved here" into "proved of nothing".
The obligation now lives as a GAME with an adversary and an advantage, where it can be false without being
silent. -/
def HashInjective : Prop :=
  ∀ s₁ s₂ p₁ p₂, factoryHash s₁ p₁ = factoryHash s₂ p₂ → s₁ = s₂ ∧ p₁ = p₂

/-! ## `FactoryDescriptor` — the published, content-addressed contract. -/

/-- **`FactoryDescriptor`** — a PUBLISHED contract that mints conforming cells. `schema` is the
child cell's field layout; `program` is the `StateConstraint` set every child carries for its
whole life; `vk` is the content-hash of `(schema, program)`. A descriptor is *well-formed*
(`WellFormed`) when its `vk` really is the hash of its content — i.e. it is
content-addressed, not a forged label. (`STORAGE-AS-CELL-PROGRAMS.md §2 Step 1`.) -/
structure FactoryDescriptor where
  schema  : Schema
  program : RecordProgram
  vk      : FactoryVk
  deriving Repr

/-- **`FactoryDescriptor.WellFormed d`** — the descriptor is content-addressed: its
`vk` is the content-hash of its `(schema, program)`. The `mkDescriptor` smart constructor builds
only well-formed descriptors; an arbitrary `⟨s, p, v⟩` may carry a forged `vk` and is rejected by
this predicate. -/
def FactoryDescriptor.WellFormed (d : FactoryDescriptor) : Prop :=
  d.vk = factoryHash d.schema d.program

/-- **`mkDescriptor schema program`** — the smart constructor: publish a factory by content-
hashing `(schema, program)`. Always produces a `WellFormed` descriptor. -/
def mkDescriptor (schema : Schema) (program : RecordProgram) : FactoryDescriptor :=
  { schema := schema, program := program, vk := factoryHash schema program }

/-- Every `mkDescriptor`-published factory is well-formed (definitional). -/
theorem mkDescriptor_wellFormed (schema : Schema) (program : RecordProgram) :
    (mkDescriptor schema program).WellFormed := rfl

/-! ## `Cell` — the minted child cell (state + the program it runs for life). -/

/-- **`Cell`** — a cell minted by a factory: its mutable `state` (a `Value`) plus the `program`
(the `RecordProgram` / `StateConstraint` set) it carries for its whole life. The `program` is the
coalgebra structure-map this cell runs every turn (`RecordCell.recExec`). Constructor transparency
is the claim that, for a factory-minted cell, `program` is *exactly* the factory's declared one. -/
structure Cell where
  state   : Value
  program : RecordProgram
  deriving Repr

/-! ## `createFromFactory` — mint a cell carrying the factory's program. -/

/-- **`createFromFactory d initial`** — mint a child cell from descriptor `d` with initial state
`initial`. Rejects (`none`) if `initial` does not conform to the factory's `schema`
(`Value.conforms`, fail-closed); otherwise mints a cell whose `program` IS the factory's
`program`. This is `Effect::CreateCellFromFactory` (`STORAGE-AS-CELL-PROGRAMS.md §2 Step 3`): the
app asks for "a cell that satisfies *this published contract*", and gets exactly that. -/
def createFromFactory (d : FactoryDescriptor) (initial : Value) : Option Cell :=
  if conforms initial (.record d.schema) = true then
    some { state := initial, program := d.program }
  else
    none

/-! ## `cellStep` — a transition on a minted cell, gated by the cell's (= factory's) program. -/

/-- **`cellStep cell method op`** — advance a minted cell one turn: run the gated record-arrow
`RecordCell.recExec` with the *cell's own program* as the admissibility filter. Commits
(`some cell'` with `cell'.program = cell.program`) iff the program admits the candidate; otherwise
`none` (fail-closed). The program a cell runs every turn is the one it was minted with — there is
no way to swap it (no constructor here rebinds `program`), which is what makes the factory's
published invariants *lifetime* invariants. -/
def cellStep (cell : Cell) (method : Nat) (op : RecOp) : Option Cell :=
  match recExec cell.program method cell.state op with
  | some new => some { state := new, program := cell.program }
  | none     => none

/-! ## THE KEYSTONE — constructor transparency. -/

/-- **`factory_mints_conforming` / `constructor_transparency` (THE KEYSTONE).** Every
cell a factory mints carries EXACTLY the factory's declared `program`. So anyone who knows the
factory's `vk` (and can read the descriptor) knows the cell's lifetime invariants — there is no
hidden behavior. (`STORAGE-AS-CELL-PROGRAMS.md §1.2`: *"anyone with the `factory_vk` … knows
exactly what invariants the cell will carry."*) The minted cell additionally conforms to the
schema, so its state is well-shaped from birth. -/
theorem factory_mints_conforming
    {d : FactoryDescriptor} {initial : Value} {cell : Cell}
    (h : createFromFactory d initial = some cell) :
    cell.program = d.program ∧ cell.state = initial
      ∧ conforms cell.state (.record d.schema) = true := by
  unfold createFromFactory at h
  by_cases hc : conforms initial (.record d.schema) = true
  · rw [if_pos hc, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, hc⟩
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- Alias for the keystone under its `cand-A` name. -/
theorem constructor_transparency
    {d : FactoryDescriptor} {initial : Value} {cell : Cell}
    (h : createFromFactory d initial = some cell) :
    cell.program = d.program :=
  (factory_mints_conforming h).1

/-- **`createFromFactory_rejects_nonconforming`** — minting fails-closed: a non-
conforming initial value never mints a cell. The schema is a creation-time gate (it is the
`field_constraints` half of the descriptor, `STORAGE-AS-CELL-PROGRAMS.md §2 Step 1`). -/
theorem createFromFactory_rejects_nonconforming
    (d : FactoryDescriptor) (initial : Value)
    (h : conforms initial (.record d.schema) = false) :
    createFromFactory d initial = none := by
  unfold createFromFactory
  rw [if_neg (by rw [h]; simp)]

/-! ## The lifetime invariant — every transition on a minted cell is gated by the factory. -/

/-- **`cellStep_admitted`** — a committed transition on ANY cell was admitted by that
cell's program: if `cellStep cell method op = some cell'`, then `cell.program` admits the new
state. This is `RecordCell.recExec_admitted` lifted through the `Cell` wrapper — the cell's
program gates its arrow. -/
theorem cellStep_admitted
    {cell : Cell} {method : Nat} {op : RecOp} {cell' : Cell}
    (h : cellStep cell method op = some cell') :
    cell.program.admits method cell.state cell'.state = true := by
  unfold cellStep at h
  cases hr : recExec cell.program method cell.state op with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some new =>
      rw [hr, Option.some.injEq] at h
      subst h
      -- `cell'.state = new`, and `recExec … = some new`, so `recExec_admitted hr` applies.
      exact recExec_admitted hr

/-- **`cellStep_preserves_program`** — a transition never changes the cell's program: the
program a minted cell carries is the program it keeps. (No constructor rebinds it.) Together with
`factory_mints_conforming` this gives the *lifetime* claim: the factory's program governs every
state the cell ever reaches. -/
theorem cellStep_preserves_program
    {cell : Cell} {method : Nat} {op : RecOp} {cell' : Cell}
    (h : cellStep cell method op = some cell') :
    cell'.program = cell.program := by
  unfold cellStep at h
  cases hr : recExec cell.program method cell.state op with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some new =>
      rw [hr, Option.some.injEq] at h
      subst h; rfl

/-- **`factory_cell_step_admitted` (THE LIFETIME KEYSTONE).** Every transition on a
*factory-minted* cell is gated by the FACTORY's declared `program` (the descriptor's
`StateConstraint`s). Combining `factory_mints_conforming` (the cell runs the factory's program)
with `cellStep_admitted` (every step is gated by the cell's program): the published contract holds
over the cell's whole life. Anyone with the `vk` knows — for every turn the cell will ever take —
exactly which `StateConstraint`s must have held. This is the record-cell shadow of
`StepComplete.cexec_attests`, scoped to a factory's published contract. -/
theorem factory_cell_step_admitted
    {d : FactoryDescriptor} {initial : Value} {cell cell' : Cell}
    {method : Nat} {op : RecOp}
    (hmint : createFromFactory d initial = some cell)
    (hstep : cellStep cell method op = some cell') :
    d.program.admits method cell.state cell'.state = true := by
  have hprog : cell.program = d.program := (factory_mints_conforming hmint).1
  have hadm := cellStep_admitted hstep
  rw [hprog] at hadm
  exact hadm

/-! ## TOMBSTONE — the content-address leg was VACUOUS here, and lives elsewhere now.

**DELETED 2026-08-01: `vk_determines_invariants` and `vk_determines_program`.**

WHAT THEY CLAIMED. Both took `hinj : HashInjective` and concluded, of two WELL-FORMED descriptors
with equal `vk`, that they published the same `(schema, program)` (`vk_determines_program` was
literally the `.2` of `vk_determines_invariants`). Read as English that is CONSTRUCTOR TRANSPARENCY
itself — *"anyone with the `factory_vk` knows exactly what invariants the cell will carry"* — which
is why they were the file's advertised third keystone.

WHY THEY WERE VACUOUS. `HashInjective` is FALSE at the deployed parameters, and that is not a gap in
our knowledge but a proved fact:
`Crypto.FactoryBindingFloorRegrounded.hashInjective_false_blake3` derives `¬ HashInjective` from
nothing more than `factory_vk` being a 256-bit BLAKE3 digest, since the published content
`Schema × RecordProgram` is infinite (the general form is `hashInjective_false_of_finite_range`).
A theorem whose hypothesis is refutable at the parameters it is quoted about states nothing about
those parameters. Both proofs were kernel-clean and `#assert_axioms` would have passed them
forever: it audits the PROOF, never the HYPOTHESIS. The error in the original was one of SHAPE, not
of kind — collision-resistance, which is what the §8 note always said it wanted, means collisions
are hard to FIND, never that they do not EXIST.

WHAT TO CONSUME INSTEAD (both in `Dregg2/Crypto/FactoryBindingFloorRegrounded.lean`; prefer the
first):
  * `vk_determines_invariants_binds_rom` (§6b) — **the discharged one.** Every query-bounded
    factory forger has negligible advantage in `factoryRomGame` over the sampled keyed ROM. It
    carries NO floor hypothesis and NO cost model: only query-boundedness (`RomOpenEff … Q`) and a
    `PolyBounded` query count, concluding `Negl`. Non-vacuity is pinned by
    `factoryRom_class_inhabited_pos` (the class is inhabited with positive advantage).
  * `vk_determines_invariants_advantage_bound` (§3) — the collision-floor sibling, if you need the
    statement against `factoryHash` itself rather than a ROM. It conditions on
    `HashCRHardQuant (factoryHashFamily …) Eff` at an EXPLICIT adversary class and carries an
    UNDISCHARGED `hEff`; that is the honest state, not a defect to hide. It is NOT conditioned on
    `HashFloorHonesty.CollisionResistant`, which is that same floor at `⊤` and itself false
    (`FloorGames.hashCRHardQuant_top_false_of_compressing`).
The reduction connecting them to this file is `forgerToFactoryHashAdv` / `factory_wins_imp` — the
deleted `vk_determines_invariants`, contraposed, with `WellFormed` doing the real work of turning a
shared `vk` into a shared digest. So nothing was lost in the move: the content that was true was
re-derived on a floor that can hold it.

`HashInjective` itself is KEPT above, on purpose. It is a `Verify.FloorCensus` sentinel; deleting
the def would delete the target of its own refutation and the ratchet's grip on it. -/

/-- **`same_content_same_vk`** — the FUNCTIONAL direction, requiring NO crypto hypothesis:
publishing the same content yields the same `vk`. (A hash is a *function* of its input — this is
pure determinism, not collision-resistance.) This is the half of the "bidirectional handle" that
survives at deployed parameters; the other half — equal `vk` ⇒ equal content — is not a theorem
here at all but the negligible-advantage bound named in the tombstone above. -/
theorem same_content_same_vk
    {d₁ d₂ : FactoryDescriptor}
    (hw₁ : d₁.WellFormed) (hw₂ : d₂.WellFormed)
    (hs : d₁.schema = d₂.schema) (hp : d₁.program = d₂.program) :
    d₁.vk = d₂.vk := by
  unfold FactoryDescriptor.WellFormed at hw₁ hw₂
  rw [hw₁, hw₂, hs, hp]

/-! ## It runs (`#guard`) — a counter factory mints a counter cell; a bad turn is rejected. -/

/-- The canonical living-cell example as a PUBLISHED contract: a factory whose schema is one
scalar field `count`, and whose lifetime program is `monotonic "count"` (count only ever
increases). Anyone with `counterFactory.vk` knows every child counter will satisfy this forever. -/
def counterFactory : FactoryDescriptor :=
  mkDescriptor [("count", .scalar)] (.predicate [.simple (.monotonic "count")])

/-- A conforming initial counter state. -/
def counterInit : Value := .record [("count", .int 5)]

/-- A non-conforming initial value (wrong shape — not even a record). -/
def badInit : Value := .int 7

-- Minting from the counter factory with a conforming initial value succeeds, and the minted cell
-- carries EXACTLY the factory's program:
#guard ((createFromFactory counterFactory counterInit).isSome)  --  true
-- (`RecordProgram` is a nested-`List` inductive, so it has no `DecidableEq`; we compare via the
-- derived `Repr` — the minted program prints identically to the factory's, witnessing the keystone
-- `constructor_transparency` is true at this datum.)
#guard (match createFromFactory counterFactory counterInit with
      | some c => reprStr c.program == reprStr counterFactory.program   -- the keystone, computed: true
      | none   => false)

-- A non-conforming initial value is rejected at mint time (fail-closed):
#guard ((createFromFactory counterFactory badInit).isSome) == false  --  false

-- The minted cell, stepped: an increment commits; a decrement is rejected by the factory's
-- monotonic program (the lifetime invariant, enforced on a *minted* cell):
#guard (match createFromFactory counterFactory counterInit with
      | some c => (cellStep c 0 (.addScalar "count" 3)).map (fun (c' : Cell) => (c'.state).scalar "count")   -- some (record [count := 8])
      | none   => none) == some (some 8)
#guard (match createFromFactory counterFactory counterInit with
      | some c => (cellStep c 0 (.addScalar "count" (-2))).isSome       -- false (8↛3 violates monotonic)
      | none   => false) == false

-- Content-addressing: re-publishing the same contract yields the same `vk`; the descriptor is
-- well-formed (its `vk` is the hash of its content):
#guard (decide (counterFactory.vk
  = (mkDescriptor [("count", .scalar)] (.predicate [.simple (.monotonic "count")])).vk))  --  true

end Dregg2.Exec.Factory
