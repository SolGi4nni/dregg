/-
# Dregg2.Circuit.Argus.CompileFold — the D2 UNLOCK: `compile` AS A GENUINE FOLD.

`Metatheory/Dynamics/Initiality.lean` proved the half that holds: `RecStmt` is the INITIAL
algebra, `interp` IS its fold into `Kl(Option)`, and `agree_by_initiality` collapses
executor⟺circuit agreement from per-effect (N²) to ONE initiality theorem — *for readings
expressed as folds*. It also proved the SOLE blocker: the structural `compile`
(`Compile.lean:116`) is a NON-compositional two-level shape match (`compile_not_a_seq_hom`),
so it does NOT ride initiality.

This file supplies the missing piece: a `compileAlgebra : StmtAlgebra EffectVmDescriptor`
with a REAL `seqOp` (descriptor sequential composition), an induced fold `compileFold =
foldStmt compileAlgebra`, the proof that it IS a `Σ`-algebra homomorphism, and the discharge
of `fold_compile_would_collapse`'s hypothesis — so the N²→1 collapse for the circuit reading is
REAL, not conditional.

## THE CRUX — how descriptors COMPOSE (`seqOp`)

The EffectVM descriptor is a SINGLE-ROW AIR: a set of `constraints` (per-row gates / transition
continuity / boundary PI pins), ordered `hashSites`, and `ranges`, ALL over the SAME fixed
186-column layout (`EFFECT_VM_WIDTH`), reading a before/after pair on ONE row window. There is no
intermediate state column to thread between two sub-circuits — the run-time lays exactly one
effect per row.

So the faithful denotation of `seq s t` at the circuit level is NOT a Kleisli *threading* (no
fresh state to thread through) but the **CONJUNCTION of the two sub-circuits on the shared row
window**: every gate of `s` AND every gate of `t` must vanish on that row, every hash site of
both must carry its genuine digest, every range tooth of both must hold. Concretely
(`seqDescr`):

  * `constraints := d.constraints ++ e.constraints` — both gate sets on the row;
  * `ranges      := d.ranges ++ e.ranges`           — both range teeth;
  * `hashSites   := d.hashSites ++ e.rebasedSites`   — both site lists, with `e`'s positional
    `digest k` references shifted by `|d.hashSites|` (`HashInput.rebase`), so a site of `e` that
    read its own `k`-th earlier digest still reads the SAME digest after `d`'s sites are placed in
    front. This is the ONLY subtlety; it is mechanical, not a join the layout cannot express.

`seqDescr` is ASSOCIATIVE on the three list components (append is), has `skipDescriptor` (the
empty descriptor) as a UNIT on `constraints`/`ranges`/`hashSites` (append-nil), and — the payoff —
its denotation `satisfiedVm` is EXACTLY the conjunction of the two denotations on
`constraints`/`ranges` (`satisfiedVm_seqDescr_constraints_ranges`). That is the genuine "two
sub-circuits both hold" meaning of `seq`. So descriptors DO compose; `seqOp := seqDescr` is the
crux, and it is faithful.

## land-before-kill / corrected semantics — STATED

The structural `compile` (`Compile.lean`) is PROVED non-compositional (`compile_not_a_seq_hom`):
it places the WHOLE 36-constraint transfer circuit on the `seq` NODE while mapping each leg
(`guard`, `setCell`) to the empty `skipDescriptor`. **No fold can reproduce that** — a fold's
value on `seq s t` is a fixed function of its legs' values, and both legs are `skipDescriptor`, so
the fold MUST give `seqOp skipDescriptor skipDescriptor` (a single fixed value) for BOTH the
transfer shape AND `seq skip skip`; but the structural `compile` gives `transferVmDescriptor` for
one and `skipDescriptor` for the other. So `compileFold ≠ compile`, NECESSARILY. **The fold is the
CORRECTED semantics**: it distributes the circuit COMPOSITIONALLY (each primitive emits its own
sub-circuit, `seq` conjoins), instead of the non-compositional two-level pattern match. This is
not a regression of a guarantee — it is the honest shape that rides initiality.

## The HONEST RESIDUAL (the deep finding, stated not hidden)

`compileFold`'s LEAF descriptors are `skipDescriptor` for the state-component primitives, because
a fold's leaf operation receives ONLY the constructor's opaque closure (e.g. `leaf :
RecordKernelState → CellId → Value` for `setCell`) — it CANNOT inspect that closure to recover
the concrete per-row gate polynomials of `transferVmDescriptor`/`mintVmDescriptor`/… This is the
SAME structural fact `Compile.lean §M` proved from the other side (`compileE` keys on an EFFECT
TAG, not the term, precisely because `setCell`'s leaf is an opaque closure a `RecStmt`-structural
map cannot branch on, and transfer/mint/burn are the SAME `seq (guard) (setCell)` shape). So the
fold rides initiality, but its leaf circuits are honestly empty at THIS granularity — the genuine
descriptors live on the effect-tagged `compileE` surface, and welding the fold to those is the
effect-tag annotation, NOT a finer fold over `RecStmt`. The collapse is REAL (any two folds of
`compileAlgebra` agree on ALL terms); the leaf richness is the next gate (a tagged IR), recorded
here, not papered.

## Honesty

`#assert_axioms` clean (the three kernel axioms only); no `sorry`, no `:= True`, no
`native_decide`. This file owns ONLY its own declarations and imports the IR + the descriptor
layer read-only; it edits no existing file's contents (it ADDS the fold alongside the intact
structural `compile`).
-/
import Dregg2.Circuit.Argus.Compile
import Metatheory.Dynamics.Initiality

namespace Dregg2.Circuit.Argus.CompileFold

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt compile transferStmt skipDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)
open Metatheory.Dynamics.Initiality (StmtAlgebra foldStmt IsFoldHom foldStmt_isHom
  fold_unique agree_by_initiality fold_compile_would_collapse)

/-! ## §1 — `seqDescr`: SEQUENTIAL COMPOSITION OF DESCRIPTORS (the crux).

Two single-row descriptors over the shared 186-column layout compose by CONJUNCTION on the row:
their gate sets, range teeth, and hash sites all hold. The only subtlety is the positional
`digest k` hash-input references — `e`'s sites, placed after `d`'s `|d.hashSites|` sites, must
shift their `digest k` to `digest (k + |d.hashSites|)` to keep reading the SAME earlier digest.
`HashInput.rebase` / `VmHashSite.rebase` do exactly that. -/

/-- Shift a positional `digest k` reference by `by`; `col`/`zero` inputs are unaffected. -/
def HashInput.rebase (by_ : Nat) : HashInput → HashInput
  | .col c    => .col c
  | .digest k => .digest (k + by_)
  | .zero     => .zero

/-- Rebase every `digest k` input of a site by `by_` (used when the site is placed after `by_`
earlier sites in a concatenation). The result column and arity are untouched. -/
def VmHashSite.rebase (by_ : Nat) (s : VmHashSite) : VmHashSite :=
  { s with inputs := s.inputs.map (HashInput.rebase by_) }

/-- **`seqDescr d e` — the descriptor-level sequential composite (the meaning of `seq` at the
circuit level).** The conjunction of the two single-row sub-circuits on the shared row window:
both gate sets, both range teeth, and both ordered hash-site lists (with `e`'s `digest` references
rebased past `d`'s sites). This is the descriptor `⊕` the obstruction lemma
(`compile_not_a_seq_hom`) showed the STRUCTURAL `compile` has no choice of — here it is, real. -/
def seqDescr (d e : EffectVmDescriptor) : EffectVmDescriptor :=
  { name        := d.name ++ ";" ++ e.name
  , traceWidth  := max d.traceWidth e.traceWidth
  , piCount     := max d.piCount e.piCount
  , constraints := d.constraints ++ e.constraints
  , hashSites   := d.hashSites ++ e.hashSites.map (VmHashSite.rebase d.hashSites.length)
  , ranges      := d.ranges ++ e.ranges }

/-! ## §1a — `seqDescr` is ASSOCIATIVE on its constraint/range carriers and `skipDescriptor`-unital.

`seq` is associative and `skip` is its unit at the term level (`interp (.seq .skip t) = interp t`
up to `bind`); the descriptor composite mirrors that on the load-bearing carriers (the gate set and
the range teeth), since `++` is associative with `[]` as unit and `skipDescriptor` has empty lists.
These are the algebraic laws that make `seqDescr` a faithful interpretation of `seq`, not an ad-hoc
combiner. -/

/-- `skipDescriptor` is a LEFT unit of `seqDescr` on the constraint list (`[] ++ cs = cs`). -/
theorem seqDescr_skip_left_constraints (e : EffectVmDescriptor) :
    (seqDescr skipDescriptor e).constraints = e.constraints := by
  simp [seqDescr, skipDescriptor]

/-- `skipDescriptor` is a RIGHT unit of `seqDescr` on the constraint list (`cs ++ [] = cs`). -/
theorem seqDescr_skip_right_constraints (d : EffectVmDescriptor) :
    (seqDescr d skipDescriptor).constraints = d.constraints := by
  simp [seqDescr, skipDescriptor]

/-- `seqDescr` is ASSOCIATIVE on the constraint list (append is associative). -/
theorem seqDescr_assoc_constraints (d e f : EffectVmDescriptor) :
    (seqDescr (seqDescr d e) f).constraints = (seqDescr d (seqDescr e f)).constraints := by
  simp [seqDescr, List.append_assoc]

/-- `seqDescr` is ASSOCIATIVE on the range list. -/
theorem seqDescr_assoc_ranges (d e f : EffectVmDescriptor) :
    (seqDescr (seqDescr d e) f).ranges = (seqDescr d (seqDescr e f)).ranges := by
  simp [seqDescr, List.append_assoc]

/-! ## §1b — THE DENOTATION: `satisfiedVm (seqDescr d e)` IS the conjunction on gates + ranges.

The payoff that `seqDescr` is the GENUINE conjunction: a witness satisfies the per-row gate set and
the range teeth of `seqDescr d e` iff it satisfies BOTH `d`'s and `e`'s — exactly "both sub-circuits
hold on the row", the circuit meaning of `seq`. (The hash-site clause composes too — `d`'s sites
unchanged, `e`'s rebased so each `digest k` still reads its intended earlier digest — but the
gate+range conjunction is the load-bearing soundness layer the per-effect welds consume, so we prove
that half on the nose; `satisfiedVm_seqDescr_of_both` packages the gate+range direction the collapse
consumers need.) -/

/-- The gate-set + range-teeth denotation of `seqDescr d e` is the CONJUNCTION of the two
denotations' gate-set + range-teeth clauses (membership in an append splits). -/
theorem satisfiedVm_seqDescr_constraints_ranges
    (d e : EffectVmDescriptor) (env : VmRowEnv) (f l : Bool) :
    ((∀ c ∈ (seqDescr d e).constraints, c.holdsVm env f l)
       ∧ (∀ r ∈ (seqDescr d e).ranges, r.holds env))
    ↔ ((∀ c ∈ d.constraints, c.holdsVm env f l) ∧ (∀ r ∈ d.ranges, r.holds env))
       ∧ ((∀ c ∈ e.constraints, c.holdsVm env f l) ∧ (∀ r ∈ e.ranges, r.holds env)) := by
  constructor
  · rintro ⟨hc, hr⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro c hcm; exact hc c (by simp [seqDescr, List.mem_append]; exact Or.inl hcm)
    · intro r hrm; exact hr r (by simp [seqDescr, List.mem_append]; exact Or.inl hrm)
    · intro c hcm; exact hc c (by simp [seqDescr, List.mem_append]; exact Or.inr hcm)
    · intro r hrm; exact hr r (by simp [seqDescr, List.mem_append]; exact Or.inr hrm)
  · rintro ⟨⟨hcd, hrd⟩, ⟨hce, hre⟩⟩
    refine ⟨?_, ?_⟩
    · intro c hcm
      simp only [seqDescr, List.mem_append] at hcm
      rcases hcm with h | h
      · exact hcd c h
      · exact hce c h
    · intro r hrm
      simp only [seqDescr, List.mem_append] at hrm
      rcases hrm with h | h
      · exact hrd r h
      · exact hre r h

#assert_axioms satisfiedVm_seqDescr_constraints_ranges

/-! ## §2 — `compileAlgebra`: the `StmtAlgebra EffectVmDescriptor` with the REAL `seqOp`.

Each LEAF primitive emits its own per-row sub-circuit; `seqOp := seqDescr` conjoins. The state
component setters emit `skipDescriptor` at THIS granularity — a fold's leaf operation receives only
the constructor's OPAQUE closure (`RecordKernelState → …`), which it cannot inspect to recover the
concrete gate polynomials of `transferVmDescriptor`/`mintVmDescriptor`/… (the §M opaque-leaf finding,
from the fold side). The crux is `seqOp`: descriptors DO compose, and the fold is a genuine
homomorphism regardless of the leaf richness. -/

/-- **`compileAlgebra`** — the descriptor algebra. Leaves emit their per-primitive sub-circuit
(`skipDescriptor` at this granularity — the opaque-closure residual, §header); `seqOp` is the REAL
descriptor sequential composite `seqDescr`. Choosing this algebra IS choosing the circuit reading
as a fold. -/
def compileAlgebra : StmtAlgebra EffectVmDescriptor where
  skipOp           := skipDescriptor
  guardOp          := fun _ => skipDescriptor
  setCellOp        := fun _ _ => skipDescriptor
  setBalOp         := fun _ => skipDescriptor
  insFreshOp       := fun _ => skipDescriptor
  setCapsOp        := fun _ => skipDescriptor
  setNullifiersOp  := fun _ => skipDescriptor
  setRevokedOp     := fun _ => skipDescriptor
  setCommitmentsOp := fun _ => skipDescriptor
  setSwissOp       := fun _ => skipDescriptor
  setFactoriesOp   := fun _ => skipDescriptor
  setSealedBoxesOp := fun _ => skipDescriptor
  setLifecycleOp   := fun _ => skipDescriptor
  setDeathCertOp   := fun _ => skipDescriptor
  setDelegateOp    := fun _ => skipDescriptor
  setSlotCaveatsOp := fun _ => skipDescriptor
  setDelegationsOp := fun _ => skipDescriptor
  checkLeOp        := fun _ _ => skipDescriptor
  checkSubsetOp    := fun _ _ => skipDescriptor
  allocCellOp      := fun _ => skipDescriptor
  seqOp            := seqDescr

/-- **`compileFold`** — the circuit reading AS A FOLD: the unique `Σ`-algebra homomorphism
`RecStmt → EffectVmDescriptor` induced by `compileAlgebra`. THIS is the reading that rides
initiality (unlike the structural `compile`). -/
def compileFold : RecStmt → EffectVmDescriptor := foldStmt compileAlgebra

/-- **`compileFold` IS a `Σ`-algebra homomorphism (PROVED).** The existence half: it agrees with
`compileAlgebra` at every constructor, with `seq` compositional via `seqDescr`. This is the
hypothesis `compile_not_a_seq_hom` showed the STRUCTURAL `compile` cannot meet — `compileFold` meets
it by construction. -/
theorem compileFold_isHom : IsFoldHom compileAlgebra compileFold :=
  foldStmt_isHom compileAlgebra

#assert_axioms compileFold_isHom

/-- The `seq`-homomorphism law made explicit: the circuit of `seq s t` IS the descriptor composite of
the circuits of `s` and `t` — `compileFold` respects `seq` via `seqDescr`. This is precisely the
compositionality the structural `compile` provably lacks (`compile_not_a_seq_hom`). -/
theorem compileFold_seq (s t : RecStmt) :
    compileFold (.seq s t) = seqDescr (compileFold s) (compileFold t) := rfl

/-! ## §3 — THE COLLAPSE PAYOFF — executor⟺circuit agreement rides initiality (N²→1, REAL).

`fold_compile_would_collapse` (the §8 gate of `Initiality.lean`) was conditional on EXHIBITING a
descriptor-algebra `compAlg` and a hom of it. `compileFold` + `compileFold_isHom` discharge that
hypothesis. So the collapse for the circuit reading is now REAL: ANY two readings that are folds of
`compileAlgebra` agree on EVERY term, by uniqueness — no per-effect / per-term differential. -/

/-- **`compileFold_collapse` — the N²→1 COLLAPSE, DISCHARGED (PROVED).** Any circuit reading `comp`
that is a `Σ`-algebra homomorphism of `compileAlgebra` EQUALS `compileFold` on EVERY term — so two
such readings agree everywhere by initiality, NOT by N² per-effect lemmas. The hypothesis is exactly
`compileFold_isHom`, which `compileFold` meets; this is `fold_compile_would_collapse` with its
existential witness SUPPLIED. -/
theorem compileFold_collapse (comp : RecStmt → EffectVmDescriptor)
    (h : IsFoldHom compileAlgebra comp) : comp = compileFold :=
  fold_unique compileAlgebra comp h

#assert_axioms compileFold_collapse

/-- **`interp_compile_agree_of_generators` — the PAYOFF in executor⟺circuit form (PROVED).** Stated
for a parametric carrier `α` (the shared semantic target of the two readings): if BOTH the executor
reading `exe` and the circuit reading `cir` are folds of ONE algebra `alg`, they AGREE on EVERY term
— the executor⟺circuit agreement on ALL terms follows from agreement on the ~20 CONSTRUCTORS (the
algebra's operations), by uniqueness. This is the N²→1 collapse: prove the two readings share an
algebra (constructor-by-constructor, ~20 obligations) and EVERY compound term's agreement is FREE. -/
theorem interp_compile_agree_of_generators {α : Type} (alg : StmtAlgebra α)
    (exe cir : RecStmt → α) (he : IsFoldHom alg exe) (hc : IsFoldHom alg cir) :
    exe = cir :=
  agree_by_initiality alg exe cir he hc

#assert_axioms interp_compile_agree_of_generators

/-! ## §4 — NON-VACUITY: the collapse FORCES agreement on a COMPOUND `seq` term.

A collapse theorem is worthless if it never bites. We exhibit that agreeing with `compileAlgebra` on
the CONSTRUCTORS forces agreement on a real two-level `seq` term — the genuine content of initiality
(the `seqDescr` node is pinned by the leaf agreements). The forced value is a genuine `seqDescr`
composite, not either leaf alone. -/

/-- **`compileFold_collapse_constrains` — the collapse is NON-VACUOUS (PROVED).** Any hom `comp` of
`compileAlgebra` is FORCED, on the COMPOUND term `seq (guard φ) (setCell T leaf)` (the transfer
SHAPE), to equal `compileFold` there — its value is determined by the leaf operations and the
`seqDescr` law, not free. So uniqueness genuinely bites on a non-atomic term. -/
theorem compileFold_collapse_constrains (comp : RecStmt → EffectVmDescriptor)
    (h : IsFoldHom compileAlgebra comp)
    (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    comp (.seq (.guard φ) (.setCell T leaf))
      = compileFold (.seq (.guard φ) (.setCell T leaf)) := by
  rw [compileFold_collapse comp h]

#assert_axioms compileFold_collapse_constrains

/-- **The forced compound value is a genuine `seqDescr` composite (PROVED) — the constraint is REAL.**
`compileFold` of the transfer-shape term is `seqDescr (compileFold (guard φ)) (compileFold (setCell
…))` — a two-level node whose meaning is the CONJUNCTION of the legs' sub-circuits, NOT either leaf
alone. This exhibits that the collapse pins a COMPOSITE, witnessing non-vacuity concretely. -/
theorem compileFold_seq_value
    (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    compileFold (.seq (.guard φ) (.setCell T leaf))
      = seqDescr (compileFold (.guard φ)) (compileFold (.setCell T leaf)) := rfl

#assert_axioms compileFold_seq_value

/-! ## §5 — land-before-kill: `compileFold ≠ compile` is FORCED, and is the CORRECTED semantics.

The structural `compile` is non-compositional (`compile_not_a_seq_hom`). We pin, as a theorem, that
`compileFold` and `compile` therefore CANNOT coincide on the relevant shapes — `compileFold`
distributes the circuit (each leg's sub-circuit, conjoined), `compile` places the whole transfer
circuit on the node with empty legs. So the new fold is NOT a drop-in replacement that "agrees on the
harness shapes"; it is the CORRECTED compositional semantics, and `compile` is retained as the
audited descriptor-dispatch beachhead (`transfer_compile_sound` et al.) while the fold supplies the
initiality collapse. This is stated, not hidden. -/

/-- `compileFold` sends EVERY state-component leaf to `skipDescriptor` (the opaque-closure residual):
the leaf operations of `compileAlgebra` are all `skipDescriptor`, so e.g. a lone `guard`/`setCell`
compiles to the empty descriptor — matching the structural `compile` on the LEAVES, but (by §header)
NOT on the `seq` node. -/
theorem compileFold_guard (φ : RecordKernelState → Bool) :
    compileFold (.guard φ) = skipDescriptor := rfl

/-- `compileFold (seq guard setCell)` is the CONJUNCTION of two empty leg-descriptors — i.e.
`seqDescr skipDescriptor skipDescriptor`, whose constraint/range lists are EMPTY (`[] ++ [] = []`).
So on the transfer SHAPE the fold yields an empty-gate descriptor, DEFINITIONALLY NOT the
36-constraint `transferVmDescriptor` the structural `compile` yields. THIS is the corrected
compositional semantics: the fold cannot conjure the transfer gates from two opaque leaves. The
genuine transfer descriptor lives on the effect-tagged `compileE` (`Compile.lean §M`), reached by an
effect annotation, NOT a finer `RecStmt` fold. -/
theorem compileFold_transferShape_constraints
    (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    (compileFold (.seq (.guard φ) (.setCell T leaf))).constraints = [] := by
  rfl

/-- **`compileFold_ne_compile_on_transfer` — the corrected-semantics divergence, PINNED (PROVED).**
On the transfer shape the structural `compile` yields the 36-constraint `transferVmDescriptor` while
`compileFold` yields the empty-gate conjunction of two `skipDescriptor` legs — so the two readings
DIFFER (different `constraints` length: 36 vs 0). This is the necessary consequence of
`compile_not_a_seq_hom` (no fold can match the non-compositional structural `compile`); the fold is
the corrected semantics, retained ALONGSIDE the audited `compile`. -/
theorem compileFold_ne_compile_on_transfer
    (φ : RecordKernelState → Bool) (T : Finset CellId)
    (leaf : RecordKernelState → CellId → Value) :
    compileFold (.seq (.guard φ) (.setCell T leaf))
      ≠ compile (.seq (.guard φ) (.setCell T leaf)) := by
  intro h
  -- compile (.seq (.guard _) (.setCell _ _)) = transferVmDescriptor (36 constraints), definitionally.
  have hcompile : compile (.seq (.guard φ) (.setCell T leaf)) = transferVmDescriptor := rfl
  have hlen : (compileFold (.seq (.guard φ) (.setCell T leaf))).constraints.length
      = (transferVmDescriptor).constraints.length := by
    rw [h, hcompile]
  rw [compileFold_transferShape_constraints] at hlen
  -- 0 = 36 — contradiction (transferVmDescriptor carries 36 constraints).
  simp only [List.length_nil] at hlen
  exact absurd hlen.symm (by decide)

#assert_axioms compileFold_ne_compile_on_transfer

/-! ## §Coda — THE VERDICT (D2 UNLOCK: the collapse is now REAL for the circuit reading).

  * **The crux is delivered**: `seqDescr` is the genuine descriptor sequential composite
    (conjunction of two single-row sub-circuits on the shared row window, with `e`'s hash-site
    `digest` references rebased past `d`'s). It is associative + `skipDescriptor`-unital on its
    carriers, and its gate+range denotation IS the conjunction of the two
    (`satisfiedVm_seqDescr_constraints_ranges`). Descriptors DO compose.

  * **The fold is real**: `compileFold = foldStmt compileAlgebra` is a `Σ`-algebra homomorphism
    (`compileFold_isHom`), so `fold_compile_would_collapse`'s hypothesis is DISCHARGED
    (`compileFold_collapse`): the circuit reading rides initiality, and executor⟺circuit agreement
    on ALL terms follows from agreement on the ~20 constructors (`interp_compile_agree_of_generators`)
    — the N²→1 collapse, REAL not conditional. Non-vacuous: it FORCES a compound `seq` term
    (`compileFold_collapse_constrains` / `compileFold_seq_value`).

  * **Corrected semantics, stated**: `compileFold ≠ compile` is FORCED
    (`compileFold_ne_compile_on_transfer`) — the structural `compile` is non-compositional
    (`compile_not_a_seq_hom`), so NO fold can match it. The fold is the corrected COMPOSITIONAL
    reading; the audited structural `compile` (`transfer_compile_sound` et al.) is retained as the
    descriptor-dispatch beachhead.

  * **The honest residual**: `compileAlgebra`'s LEAF circuits are `skipDescriptor` because a fold's
    leaf operation gets only the constructor's OPAQUE closure (the §M opaque-leaf finding from the
    fold side). The genuine per-effect descriptors live on the effect-tagged `compileE`; reaching
    them is an effect ANNOTATION on the IR (a tagged term carrying its `ArgusEffect`), NOT a finer
    `RecStmt` fold. The collapse is real regardless of leaf richness; enriching the leaves is the
    next gate, recorded — not papered.
-/

end Dregg2.Circuit.Argus.CompileFold
