/-
# Dregg2.Circuit.Emit.KimchiAssertEqual — `assert_equal` as a ZERO-ROW union-find over `PVar`

## ⚑ THE MISSING PRIMITIVE, AND WHY IT WAS MISSING

`KimchiPlacement` §3 named the seam and left it empty: *"`mergeRoots` is the seam where an
`assert_equal` remap would compose; identity for R1."* There was no `mergeRoots`. The consequence is
not cosmetic. Without it the ONLY way to bind two cells is to **author the same `PVar` in both** —
which works when you write both gates and does **not** work when two already-placed values, produced
by two fragments neither of which names the other's variables, must be equated. Every circuit above
the size of a fixture needs the second thing.

**This file is that primitive.** `assertEqual a b` unions `a` and `b`'s equivalence classes; the
equality is then carried by the **copy permutation**, not by a constraint row.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The union-find, the root map, the composition into
`circuitPositions` and every refusal below are authored in Lean, transcribed from Mina's Snarky
backend (o1js vendored `plonk_constraint_system.ml`, READ-ONLY):

  * `Constraint.Equal (x, y)` → `union_find`-union of the two variables' classes
    (`plonk_constraint_system.ml:764`, `add_constraint`'s `Equal` case) — **it emits no row.**
  * `equivalence_classes_to_hashtbl` (`:917-943`) then merges classes **by union-find root** before
    sorting and rotating. So a union is invisible to the gate list and visible only in σ.

⚑ **MEASURED, not relayed** (2026-08-05, o1js 2.15.0, `Provable.constraintSystem`, read-only —
`bridge/mina-zkapp/scripts/assert-equal-row-cost-oracle.mjs`, which exits non-zero if this ever stops
holding):

  * two constrained witnesses, with and without `a.assertEquals(b)` — **2 rows both ways**,
    `[Generic, Generic]` both ways;
  * the preimage shape, `Poseidon.hash([x])` against a separately-allocated claim, with and without
    `h.assertEquals(c)` — **14 rows both ways**, `[Poseidon ×11, Zero, Generic, Generic]` both ways.

**Delta 0 in both.** §5 makes that a theorem here, general in the map and in the gate list.

## ⚑ THE ROOT IS THE MINIMUM `varIx` OF THE CLASS — and that is load-bearing

`ufUnion` always points the LARGER `varIx` at the SMALLER, so a class's root is its minimum `varIx`,
independent of the order the equalities were authored in. Two consequences:

  * `ufRoot`'s parent chain is **strictly decreasing**, so bounded iteration at `par.size` is enough
    (`ufRootFuel`); no well-founded recursion, so everything still reduces in the KERNEL and §9's
    byte pins are `by decide`, not `native_decide`.
  * `external 0 .. pubSize-1` are the SMALLEST `varIx`es a coherent circuit has (`placeChecked`'s H1
    already forces the circuit's own ids above the public words), so merging a public word with a
    circuit variable **roots at the public word** — which is what makes §6's equivalence with
    naming-the-variable hold. Where it does NOT hold, §8 REFUSES (`publicWordDemoted`) rather than
    emitting an object no authoring could have produced. ⚠ `varIx` interleaves the two namespaces
    (`internal n ↦ 2n+1`), so an `internal` id below the public range CAN outrank a public word;
    that is the case the refusal names, and the author's fix is to allocate the internal above it.

## ⚑ WHAT IS PROVED, AND WHAT IS CHECKED — said at current resolution

* **PROVED, general in the gate list**: merging emits no row and moves no coefficient (§5); a merged
  placement IS `place` of the renamed gate list, hence inherits every existing byte pin and refusal
  (§6); no merges is the placement pass unchanged (§6).
* **CHECKED, not proved**: that the union-find actually unions. There is no general theorem here that
  `(a,b) ∈ ms → rootVar ms a = rootVar ms b`; that needs the union-find's own invariant and is not
  discharged. Instead §8's entry **recomputes closure on its own output and REFUSES** when an
  authored equality did not land (`mergeNotClosed`), and `the_accepted_merge_is_closed` inverts that
  refusal into a guarantee about everything it emits. A dropped equality cannot pass; it is detected,
  not merely documented. The general theorem is a named residual.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no `native_decide`.
NEW file. Imports `KimchiPlacement` only, and CHANGES NOTHING in it.
-/
import Dregg2.Circuit.Emit.KimchiPlacement

namespace Dregg2.Circuit.Emit.KimchiAssertEqual

open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiPlacement

set_option autoImplicit false

/-! ## §1 — `varIx` is a bijection onto its image, and here is the inverse.

`KimchiPlacement.varIx` (`external n ↦ 2n`, `internal n ↦ 2n+1`) is the bucket index the whole
placement index rests on. The union-find lives in that index space, so it needs the way back. -/

/-- The inverse of `varIx`: even indices are `external`, odd are `internal`. -/
def ixVar (i : Nat) : PVar :=
  if i % 2 == 0 then .external (i / 2) else .internal (i / 2)

/-- **`ixVar` inverts `varIx`.** Everything below moves a variable into index space, works there, and
comes back; without this that round trip is a rename. -/
theorem ixVar_varIx (v : PVar) : ixVar (varIx v) = v := by
  cases v with
  | external n => simp [ixVar, varIx, Nat.mul_mod_right]
  | internal n =>
      have h1 : (2 * n + 1) % 2 = 1 := by omega
      have h2 : (2 * n + 1) / 2 = n := by omega
      simp [ixVar, varIx, h1, h2]

/-! ## §2 — the union-find, in `varIx` space.

INVARIANT, maintained by construction: `par[i] ≤ i`. `ufUnion` only ever writes the SMALLER root
into the LARGER root's slot, so a parent chain strictly decreases and the class root is the class's
minimum `varIx`. That makes bounded iteration sound at `fuel = par.size` and makes the partition —
and the root — independent of the order the equalities were authored in. -/

/-- Chase parents, at most `fuel` steps. `j < i` is BOTH the "not yet a root" test and the strict
decrease: under the invariant a root has `par[i] = i`, and an out-of-bounds index reads back as
itself. Structural on `fuel`, so it reduces in the kernel. -/
def ufRootFuel (par : Array Nat) : Nat → Nat → Nat
  | 0,      i => i
  | fuel+1, i => let j := par.getD i i; if j < i then ufRootFuel par fuel j else i

/-- The class root of index `i`. `par.size` steps is always enough: the chain from `i` is strictly
decreasing in `Nat`, and it starts below `par.size` for any in-bounds `i` (an out-of-bounds `i` is
its own root at step 0). -/
def ufRoot (par : Array Nat) (i : Nat) : Nat := ufRootFuel par par.size i

/-- ⚑ **The fuel is enough.** `ufRootFuel par f i` lands on a FIXPOINT of the parent map whenever
`i ≤ f` — i.e. the bounded chase is the real chase, never a truncated one. (Under the `par[i] ≤ i`
invariant, `par[r] ≥ r` means `par[r] = r`, which is what "root" means.) -/
theorem ufRootFuel_reaches_a_root (par : Array Nat) :
    ∀ (f i : Nat), i ≤ f → par.getD (ufRootFuel par f i) (ufRootFuel par f i)
                             ≥ ufRootFuel par f i := by
  intro f
  induction f with
  | zero =>
      intro i hi
      have hz : i = 0 := Nat.le_zero.mp hi
      subst hz
      simp [ufRootFuel]
  | succ f ih =>
      intro i hi
      simp only [ufRootFuel]
      by_cases h : par.getD i i < i
      · simp only [h, if_true]
        exact ih _ (by omega)
      · simp only [h, if_false]
        omega

/-- The identity forest on `n` indices: every index its own root. -/
def ufInit (n : Nat) : Array Nat := (List.range n).toArray

/-- Union the classes of `a` and `b`, pointing the LARGER root at the SMALLER. `Array.modify` is a
no-op out of bounds, so an index outside the forest silently stays its own root — which is exactly
right: it was never merged with anything. -/
def ufUnion (par : Array Nat) (a b : Nat) : Array Nat :=
  let ra := ufRoot par a
  let rb := ufRoot par b
  if ra < rb then par.modify rb (fun _ => ra)
  else if rb < ra then par.modify ra (fun _ => rb)
  else par

/-! ## §3 — the authored equalities, and the root map they induce. -/

/-- **The authored equalities.** `(a, b) ∈ ms` is one `assertEqual a b`. Order is irrelevant to the
partition and to the root (§2); it is kept as a list because that is how a circuit author appends. -/
abbrev Merges := List (PVar × PVar)

/-- One past the largest `varIx` any equality mentions — the forest size. A variable no equality
mentions is outside it and is its own class, at zero cost. -/
def mergeBound (ms : Merges) : Nat :=
  ms.foldl (fun m ab => Nat.max m (Nat.max (varIx ab.1) (varIx ab.2) + 1)) 0

/-- **THE UNION-FIND, BUILT ONCE.** Fold the authored equalities into the identity forest. -/
def mergeParents (ms : Merges) : Array Nat :=
  ms.foldl (fun par ab => ufUnion par (varIx ab.1) (varIx ab.2)) (ufInit (mergeBound ms))

/-- **THE ROOT MAP** — `mergeRoots`, the declaration `KimchiPlacement` §3 named and did not have.
Every variable to the canonical representative of its class. -/
def rootVar (ms : Merges) (v : PVar) : PVar := ixVar (ufRoot (mergeParents ms) (varIx v))

/-- **No equalities is the identity map.** The whole existing tree is this case. -/
theorem rootVar_nil (v : PVar) : rootVar [] v = v := by
  simp [rootVar, ufRoot, mergeParents, mergeBound, ufInit, ufRootFuel, ixVar_varIx]

/-- Every authored equality is CLOSED under the root map — i.e. the union-find actually unioned.
Decidable, so §8 can refuse on it and §10 can pin it. -/
def mergesClosed (ms : Merges) : Bool :=
  ms.all (fun ab => decide (rootVar ms ab.1 = rootVar ms ab.2))

/-! ## §4 — composition into `circuitPositions`, and the placement pass over it.

`place` is UNCHANGED and untouched. `placeFrom` is its body with the position list abstracted —
`place_is_placeFrom` is `rfl`, so this is a lens on the existing function, not a fork of it. -/

/-- `place`'s body, with the `(variable, cell)` position list as an argument. -/
def placeFrom (pubSize : Nat) (gates : List PGate) (poss : List (PVar × Cell)) : List PlacedGate :=
  let rowIdx := pairsByRow (pubSize + gates.length) (permPairs poss)
  (List.range pubSize).map
      (fun i => { kind := .generic, wires := placedWiresAt rowIdx i, coeffs := [1, 0, 0, 0, 0] })
    ++ (gates.zip (List.range gates.length)).map
        (fun ggi => { kind := ggi.1.kind
                    , wires := placedWiresAt rowIdx (pubSize + ggi.2)
                    , coeffs := ggi.1.coeffs })

/-- **`placeFrom` IS `place`.** Not a re-implementation: the same term, with one argument named. -/
theorem place_is_placeFrom (pubSize : Nat) (gates : List PGate) :
    place pubSize gates = placeFrom pubSize gates (circuitPositions pubSize gates) := rfl

/-- ⚑ **THE COMPOSITION POINT.** Every recorded `(variable, cell)` position — public-input cells
included — with its variable replaced by its class root. This is `equivalence_classes_to_hashtbl`'s
"merge classes by union-find root" (`:917-943`), and it is the ONLY thing merging does. -/
def mergedPositions (ms : Merges) (poss : List (PVar × Cell)) : List (PVar × Cell) :=
  let par := mergeParents ms
  poss.map (fun p => (ixVar (ufRoot par (varIx p.1)), p.2))

theorem mergedPositions_is_rootVar (ms : Merges) (poss : List (PVar × Cell)) :
    mergedPositions ms poss = poss.map (fun p => (rootVar ms p.1, p.2)) := rfl

/-- Rename a gate's permutation variables. The gate's KIND and COEFFICIENTS are untouched — that is
the whole content of "zero rows". -/
def renameGate (f : PVar → PVar) (g : PGate) : PGate :=
  { g with permVars := g.permVars.map (Option.map f) }

/-- Placement under an arbitrary variable-identification map. -/
def placeBy (f : PVar → PVar) (pubSize : Nat) (gates : List PGate) : List PlacedGate :=
  placeFrom pubSize gates ((circuitPositions pubSize gates).map (fun p => (f p.1, p.2)))

/-- **THE MERGED PLACEMENT PASS.** `place`, with the authored equalities folded into the classes. -/
def placeWith (ms : Merges) (pubSize : Nat) (gates : List PGate) : List PlacedGate :=
  placeFrom pubSize gates (mergedPositions ms (circuitPositions pubSize gates))

theorem placeWith_is_placeBy (ms : Merges) (pubSize : Nat) (gates : List PGate) :
    placeWith ms pubSize gates = placeBy (rootVar ms) pubSize gates := rfl

/-- Apply the equalities to a gate list, building the forest ONCE. -/
def applyMerges (ms : Merges) (gates : List PGate) : List PGate :=
  let par := mergeParents ms
  gates.map (fun g =>
    { g with permVars := g.permVars.map (Option.map (fun v => ixVar (ufRoot par (varIx v)))) })

theorem applyMerges_is_renameGate (ms : Merges) (gates : List PGate) :
    applyMerges ms gates = gates.map (renameGate (rootVar ms)) := rfl

/-! ## §5 — ⚑ IT COSTS ZERO ROWS. General in the map and in the gate list.

This is the measurement to match: o1js spends no row on `assertEquals` between two allocated values.
Nothing weaker than "the emitted `(typ, coeffs)` sequence is UNCHANGED" says that, because a row
appended anywhere would move it. -/

/-- The emitted gate SEQUENCE — kind and coefficients, in row order — does not depend on the
position list at all. -/
theorem placeFrom_kinds_and_coeffs_ignore_positions
    (pubSize : Nat) (gates : List PGate) (poss poss' : List (PVar × Cell)) :
    (placeFrom pubSize gates poss).map (fun g => (g.kind, g.coeffs))
      = (placeFrom pubSize gates poss').map (fun g => (g.kind, g.coeffs)) := by
  simp [placeFrom, List.map_append, List.map_map, Function.comp_def]

/-- ⚑ **MERGING EMITS NO ROW AND MOVES NO COEFFICIENT.** For EVERY identification map and EVERY gate
list, the merged circuit's `(typ, coeffs)` sequence is the unmerged one's. An `assertEqual` that cost
a `Generic` row could not satisfy this. -/
theorem merging_emits_no_row (f : PVar → PVar) (pubSize : Nat) (gates : List PGate) :
    (placeBy f pubSize gates).map (fun g => (g.kind, g.coeffs))
      = (place pubSize gates).map (fun g => (g.kind, g.coeffs)) := by
  rw [place_is_placeFrom, placeBy]
  exact placeFrom_kinds_and_coeffs_ignore_positions _ _ _ _

/-- The row-count corollary, said plainly. -/
theorem merging_costs_zero_rows (f : PVar → PVar) (pubSize : Nat) (gates : List PGate) :
    (placeBy f pubSize gates).length = (place pubSize gates).length := by
  have h := merging_emits_no_row f pubSize gates
  simpa using congrArg List.length h

/-- …and for the authored form. -/
theorem assertEqual_costs_zero_rows (ms : Merges) (pubSize : Nat) (gates : List PGate) :
    (placeWith ms pubSize gates).length = (place pubSize gates).length :=
  merging_costs_zero_rows (rootVar ms) pubSize gates

theorem assertEqual_emits_no_row (ms : Merges) (pubSize : Nat) (gates : List PGate) :
    (placeWith ms pubSize gates).map (fun g => (g.kind, g.coeffs))
      = (place pubSize gates).map (fun g => (g.kind, g.coeffs)) :=
  merging_emits_no_row (rootVar ms) pubSize gates

/-! ## §6 — ⚑ THE COMPATIBILITY ARGUMENT: merging IS naming the same variable at both cells.

The existing binding style — author one `PVar` in two cells — must be the special case. It is, and
the statement is stronger than "the σ classes agree": the merged placement is **literally `place` of
the renamed gate list**. So every byte pin, every refusal and every theorem already proved about
`place` transfers verbatim; there is no second placement pass to keep honest.

The hypothesis is exactly the one §2 explains: the map must FIX the public words, because the
public-input prefix `(external i, {i,0})` is generated by `place` and cannot be renamed by authoring.
§8 refuses the emissions where it fails. -/

/-- `map` commutes with `take`. (Stated locally rather than fished out of the library so the import
surface stays `KimchiPlacement`.) -/
theorem map_take_comm {α β : Type} (g : α → β) :
    ∀ (n : Nat) (l : List α), (l.take n).map g = (l.map g).take n
  | 0,   _       => rfl
  | _+1, []      => rfl
  | n+1, _ :: l  => by simp [List.take_succ_cons, map_take_comm g n l]

theorem rowPositionsFrom_rename (f : PVar → PVar) (r : Nat) :
    ∀ (c : Nat) (pv : List (Option PVar)),
      rowPositionsFrom r c (pv.map (Option.map f))
        = (rowPositionsFrom r c pv).map (fun p => (f p.1, p.2))
  | _, []            => rfl
  | c, none :: rest  => by simp [rowPositionsFrom, rowPositionsFrom_rename f r (c+1) rest]
  | c, some v :: rest => by simp [rowPositionsFrom, rowPositionsFrom_rename f r (c+1) rest]

theorem rowPositions_rename (f : PVar → PVar) (r : Nat) (pv : List (Option PVar)) :
    rowPositions r (pv.map (Option.map f))
      = (rowPositions r pv).map (fun p => (f p.1, p.2)) := by
  unfold rowPositions
  rw [← map_take_comm, rowPositionsFrom_rename]

/-- **Renaming the variables and recording the positions commute** — provided the map fixes the
public words, which `place` records structurally and no gate list can express. -/
theorem circuitPositions_rename (f : PVar → PVar) (pubSize : Nat) (gates : List PGate)
    (hpub : ∀ i, i < pubSize → f (.external i) = .external i) :
    (circuitPositions pubSize gates).map (fun p => (f p.1, p.2))
      = circuitPositions pubSize (gates.map (renameGate f)) := by
  simp only [circuitPositions, List.map_append, List.map_map, List.length_map,
    List.map_flatMap, List.zip_map_left, List.flatMap_map, Function.comp_def]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left ?_
    intro i hi
    simp [hpub i (List.mem_range.mp hi)]
  · refine List.flatMap_congr ?_
    intro ggi _
    simp [renameGate, rowPositions_rename]

/-- `placeFrom` reads only the gates' KIND, COEFFICIENTS and COUNT — none of which renaming moves. -/
theorem placeFrom_rename (f : PVar → PVar) (pubSize : Nat) (gates : List PGate)
    (poss : List (PVar × Cell)) :
    placeFrom pubSize (gates.map (renameGate f)) poss = placeFrom pubSize gates poss := by
  simp [placeFrom, List.length_map, List.zip_map_left, List.map_map, renameGate,
    Function.comp_def]

/-- ⚑ **`assertEqual` IS NAMING THE SAME VARIABLE AT BOTH CELLS.** General in the gate list: a
merged placement is `place` of the gate list with each variable replaced by its class root. The
existing authoring style is therefore the special case where that renaming is already done by hand,
and every result already proved about `place` applies to a merged circuit unchanged. -/
theorem merging_is_naming_the_same_variable (f : PVar → PVar) (pubSize : Nat) (gates : List PGate)
    (hpub : ∀ i, i < pubSize → f (.external i) = .external i) :
    placeBy f pubSize gates = place pubSize (gates.map (renameGate f)) := by
  rw [placeBy, circuitPositions_rename f pubSize gates hpub, place_is_placeFrom,
    placeFrom_rename]

/-- The authored form of the same statement. -/
theorem assertEqual_is_naming_the_same_variable (ms : Merges) (pubSize : Nat) (gates : List PGate)
    (hpub : ∀ i, i < pubSize → rootVar ms (.external i) = .external i) :
    placeWith ms pubSize gates = place pubSize (applyMerges ms gates) := by
  rw [placeWith_is_placeBy, applyMerges_is_renameGate]
  exact merging_is_naming_the_same_variable (rootVar ms) pubSize gates hpub

/-- ⚑ **NO EQUALITIES IS THE PLACEMENT PASS, UNCHANGED.** Nothing in the existing tree moves by the
existence of this file — not a wire, not a byte. -/
theorem no_merges_is_the_placement_pass (pubSize : Nat) (gates : List PGate) :
    placeWith [] pubSize gates = place pubSize gates := by
  rw [placeWith, place_is_placeFrom]
  congr 1
  simp [mergedPositions_is_rootVar, rootVar_nil]

/-! ## §7 — ⚑ THE ALIAS CENSUS: a merge primitive makes aliasing INTENTIONAL, so an UNINTENTIONAL
alias must be DETECTABLE.

The tree has already paid for the alternative: *"`KimchiStepMainCore`'s `exposedVars` once gave two
of Step's 67 public words the same variable, invisible because the smoke shape's `take 12` cut before
it."* That alias was invisible because **nothing enumerated the bindings**. A binding IS a copy class
of more than one cell, and that is enumerable off the emitted positions.

⚠ The declaration is an INPUT, authored, never derived from the gates. A caller that computed its
declaration from `aliasSizes` of the same circuit would have written a check that cannot go red —
the same laundering `inertPublicWordsBeyond`'s docblock exists to make visible. -/

/-- **Every binding the circuit makes**: each copy class of MORE THAN ONE cell, keyed by its root
variable, cells sorted. A singleton class binds nothing. -/
def aliasCensus (poss : List (PVar × Cell)) : List (PVar × List Cell) :=
  let bs := varBuckets poss
  (distinctVars poss).filterMap (fun v =>
    let cs := (bs.getD (varIx v) []).dedup
    if cs.length > 1 then some (v, sortCells cs) else none)

/-- The census as `(root, class size)` — the compact form a declaration is written in. -/
def aliasSizes (poss : List (PVar × Cell)) : List (PVar × Nat) :=
  (aliasCensus poss).map (fun e => (e.1, e.2.length))

/-- The census of a circuit, after its authored equalities. -/
def circuitAliases (ms : Merges) (pubSize : Nat) (gates : List PGate) : List (PVar × List Cell) :=
  aliasCensus (mergedPositions ms (circuitPositions pubSize gates))

def circuitAliasSizes (ms : Merges) (pubSize : Nat) (gates : List PGate) : List (PVar × Nat) :=
  aliasSizes (mergedPositions ms (circuitPositions pubSize gates))

/-! ## §8 — the FAIL-CLOSED merged entry.

⚑ It does not re-implement `placeChecked`'s refusals — it **calls** `placeCheckedWith` on the
renamed gate list, so H1, the dead-gap refusal and H2 bite on the POST-MERGE variable set and cannot
be weakened here by construction. That also makes H2 compose for free: a public word bound only by an
`assertEqual` genuinely appears in the renamed gates, so it is READ, not inert. -/

/-- Why a merged placement was REFUSED. `place` wraps the existing `PlaceRefusal` unchanged. -/
inductive MergeRefusal where
  /-- One of `placeChecked`'s refusals, on the post-merge gate list. -/
  | place : PlaceRefusal → MergeRefusal
  /-- ⚑ An authored equality did not land: `a` and `b` are still in different classes. The
  union-find is not proved correct in general; this is the check that stands in for that proof, and
  nothing that carries it can be emitted. -/
  | mergeNotClosed (a b : PVar) : MergeRefusal
  /-- Two DISTINCT public words ended up in one class — the `exposedVars` shape, now named. -/
  | publicWordsAliased (i j : Nat) : MergeRefusal
  /-- A public word is not its class's root. The emitted σ would still be the right partition, but
  the object is one NO authoring could produce, so §6's equivalence stops holding for it. Allocate
  the merged partner above the public range instead. -/
  | publicWordDemoted (i : Nat) (root : PVar) : MergeRefusal
  /-- ⚑ A binding the circuit makes and the author did not declare. -/
  | undeclaredAlias (v : PVar) (size : Nat) : MergeRefusal
  /-- A binding the author declared and the circuit does not make. -/
  | declaredAliasAbsent (v : PVar) (size : Nat) : MergeRefusal
  deriving Repr, DecidableEq, Inhabited

/-- What the author claims about the identifications: the equalities, and the FULL census of
bindings the emitted circuit is expected to contain. -/
structure MergeContract where
  merges : Merges
  /-- The DECLARED `(root, class size)` census. Authored. -/
  aliases : List (PVar × Nat)
  deriving Repr, Inhabited

/-- The first pair of distinct public words sharing a class. -/
def firstAliasedPublicPair (pubSize : Nat) (ms : Merges) : Option (Nat × Nat) :=
  ((List.range pubSize).flatMap (fun i =>
      (List.range pubSize).filterMap (fun j =>
        if i < j && decide (rootVar ms (.external i) = rootVar ms (.external j)) then some (i, j)
        else none))).head?

/-- **THE FAIL-CLOSED MERGED PLACEMENT ENTRY.** -/
def placeCheckedMerged (c : Contract) (inertOk : List Nat) (mc : MergeContract)
    (gates : List PGate) : Except MergeRefusal (List PlacedGate) :=
  match mc.merges.find? (fun ab => !decide (rootVar mc.merges ab.1 = rootVar mc.merges ab.2)) with
  | some ab => .error (.mergeNotClosed ab.1 ab.2)
  | none =>
    match firstAliasedPublicPair c.pubSize mc.merges with
    | some ij => .error (.publicWordsAliased ij.1 ij.2)
    | none =>
      match (List.range c.pubSize).find?
              (fun i => !decide (rootVar mc.merges (.external i) = .external i)) with
      | some i => .error (.publicWordDemoted i (rootVar mc.merges (.external i)))
      | none =>
        let census := circuitAliasSizes mc.merges c.pubSize gates
        match census.find? (fun e => !(mc.aliases.contains e)) with
        | some e => .error (.undeclaredAlias e.1 e.2)
        | none =>
          match mc.aliases.find? (fun e => !(census.contains e)) with
          | some e => .error (.declaredAliasAbsent e.1 e.2)
          | none =>
            match placeCheckedWith c inertOk (applyMerges mc.merges gates) with
            | .error e => .error (.place e)
            | .ok placed => .ok placed

/-- ⚑ **EVERY EMISSION THIS ENTRY MAKES HAS EVERY AUTHORED EQUALITY UNIONED.** The general
correctness of the union-find is not proved; this inverts the refusal into the guarantee that
matters, for every contract and every gate list. A dropped equality cannot reach an artifact. -/
theorem the_accepted_merge_is_closed (c : Contract) (inertOk : List Nat) (mc : MergeContract)
    (gates : List PGate) (placed : List PlacedGate)
    (h : placeCheckedMerged c inertOk mc gates = .ok placed) :
    mergesClosed mc.merges = true := by
  unfold placeCheckedMerged at h
  cases hf : mc.merges.find? (fun ab => !decide (rootVar mc.merges ab.1 = rootVar mc.merges ab.2)) with
  | some ab => rw [hf] at h; exact absurd h (by simp)
  | none =>
      simp only [mergesClosed, List.all_eq_true]
      intro ab hab
      have h2 : rootVar mc.merges ab.1 = rootVar mc.merges ab.2 := by
        simpa using List.find?_eq_none.mp hf ab hab
      simp [h2]

/-- ⚑ **AND WHAT IT EMITS IS THE MERGED PLACEMENT.** The entry's own `.ok` value is `placeWith`'s
object — so §5's zero-row theorem and §6's equivalence are about the thing that ships, not about a
sibling definition. (The `publicWordDemoted` check is what discharges §6's hypothesis.) -/
theorem the_accepted_placement_is_placeWith (c : Contract) (inertOk : List Nat) (mc : MergeContract)
    (gates : List PGate) (placed : List PlacedGate)
    (h : placeCheckedMerged c inertOk mc gates = .ok placed) :
    placed = placeWith mc.merges c.pubSize gates := by
  unfold placeCheckedMerged at h
  cases hf : mc.merges.find? (fun ab => !decide (rootVar mc.merges ab.1 = rootVar mc.merges ab.2)) with
  | some ab => rw [hf] at h; exact absurd h (by simp)
  | none =>
    rw [hf] at h
    cases hp : firstAliasedPublicPair c.pubSize mc.merges with
    | some ij => rw [hp] at h; exact absurd h (by simp)
    | none =>
      rw [hp] at h
      cases hd : (List.range c.pubSize).find?
                   (fun i => !decide (rootVar mc.merges (.external i) = .external i)) with
      | some i => rw [hd] at h; exact absurd h (by simp)
      | none =>
        rw [hd] at h
        have hpub : ∀ i, i < c.pubSize → rootVar mc.merges (.external i) = .external i := by
          intro i hi
          simpa using List.find?_eq_none.mp hd i (List.mem_range.mpr hi)
        simp only at h
        cases hu : (circuitAliasSizes mc.merges c.pubSize gates).find?
                     (fun e => !(mc.aliases.contains e)) with
        | some e => rw [hu] at h; exact absurd h (by simp)
        | none =>
          rw [hu] at h
          cases hv : mc.aliases.find? (fun e => !((circuitAliasSizes mc.merges c.pubSize gates).contains e)) with
          | some e => rw [hv] at h; exact absurd h (by simp)
          | none =>
            rw [hv] at h
            cases hq : placeCheckedWith c inertOk (applyMerges mc.merges gates) with
            | error e => rw [hq] at h; exact absurd h (by simp)
            | ok q =>
              rw [hq] at h
              have hpq : q = place c.pubSize (applyMerges mc.merges gates) := by
                unfold placeCheckedWith at hq
                split at hq
                · exact absurd hq (by simp)
                · split at hq
                  · exact absurd hq (by simp)
                  · split at hq
                    · exact absurd hq (by simp)
                    · exact (Except.ok.inj hq).symm
              have : placed = q := (Except.ok.inj h).symm
              rw [this, hpq, assertEqual_is_naming_the_same_variable mc.merges c.pubSize gates hpub]

/-! ## §9 — ⚑ CAN TWO ALREADY-PLACED VALUES BE EQUATED? The demonstration, not the claim.

This is the thing naming-a-variable cannot do. Two gate fragments are authored SEPARATELY; neither
names a variable of the other; they are concatenated by a third party who owns neither. The equality
is then authored as a VALUE appended to a list — with no edit to either fragment. -/

set_option maxRecDepth 20000

/-- Fragment A, authored on its own: a `Generic` row producing its result into `internal 0`. -/
def fragA : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.internal 0),
                   none, none, none, none]
    , coeffs := [1, 1, -1, 0, 0] } ]

/-- Fragment B, authored on its own: a `Generic` row CONSUMING `internal 1`. -/
def fragB : List PGate :=
  [ { kind := .generic
    , permVars := [some (.internal 1), some (.external 2), some (.external 3),
                   none, none, none, none]
    , coeffs := [1, 1, -1, 0, 0] } ]

def composed : List PGate := fragA ++ fragB

/-- Every variable a gate list references in its permutation columns. -/
def gateVars (gs : List PGate) : List PVar :=
  (gs.flatMap (fun g => (g.permVars.take K_PERMUTS).filterMap id)).dedup

/-- ⚑ **NEITHER FRAGMENT NAMES A VARIABLE OF THE OTHER.** Without this the demonstration is
naming-the-same-variable wearing a costume. -/
theorem the_fragments_share_no_variable :
    (gateVars fragA).filter (fun v => (gateVars fragB).contains v) = [] := by decide

/-- The equality: fragment A's output IS fragment B's input. -/
def theSeam : Merges := [(.internal 0, .internal 1)]

/-- **BEFORE the equality**, every cell self-wires: A's output `(0,2)` and B's input `(1,0)` are
singletons and nothing relates the two fragments. -/
theorem before_the_equality_the_fragments_are_unrelated :
    (place 0 composed).map (·.wires)
      = [ [⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨0,4⟩, ⟨0,5⟩, ⟨0,6⟩]
        , [⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,5⟩, ⟨1,6⟩] ] := by decide

/-- ⚑ **AFTER IT, σ CARRIES A 2-CYCLE ACROSS THE FRAGMENTS**: `(0,2) ↦ (1,0) ↦ (0,2)`. The two
already-placed values are equated, and the equality lives in the copy permutation. -/
theorem the_equality_wires_the_two_fragments_together :
    (placeWith theSeam 0 composed).map (·.wires)
      = [ [⟨0,0⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨0,3⟩, ⟨0,4⟩, ⟨0,5⟩, ⟨0,6⟩]
        , [⟨0,2⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,5⟩, ⟨1,6⟩] ] := by decide

/-- ⚑ **AND IT COST ZERO ROWS** — cited from the general theorems, not re-measured here. -/
theorem the_seam_costs_zero_rows :
    (placeWith theSeam 0 composed).length = (place 0 composed).length
    ∧ (placeWith theSeam 0 composed).map (fun g => (g.kind, g.coeffs))
        = (place 0 composed).map (fun g => (g.kind, g.coeffs)) :=
  ⟨assertEqual_costs_zero_rows _ _ _, assertEqual_emits_no_row _ _ _⟩

/-- σ is still a PERMUTATION of the circuit's cells after merging: the merged wiring neither drops,
duplicates nor invents a cell. (The copy argument is unsound without this.) -/
theorem the_merged_sigma_is_a_permutation :
    sortCells (allWires (placeWith theSeam 0 composed)) = sortCells (allCells 2) := by decide

/-- The equality is CLOSED: the union-find actually unioned it. -/
theorem the_seam_is_closed : mergesClosed theSeam = true := by decide

/-! ## §10 — the refusals BITE, on a public-input circuit.

`mProbe` reads public words 0,1,2 and allocates its own variables from `external 10` — the coherent
shape `placeChecked` was built for. Note what the census contains: a public word READ by a gate is
itself a 2-cell class (the public row cell, and the gate cell), so the declaration states "each of
public words 0,1,2 is read at exactly one cell" as well as the circuit's own `external 10` copy. -/

def mProbe : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.external 10),
                   none, none, some (.external 10), none]
    , coeffs := [] }
  , { kind := .generic
    , permVars := [some (.external 2), some (.external 11), none,
                   some (.external 12), none, none, none]
    , coeffs := [] } ]

/-- The honest declaration of every binding `mProbe` makes — AUTHORED, not derived from the gates. -/
def mProbeDecl : List (PVar × Nat) :=
  [(.external 0, 2), (.external 1, 2), (.external 2, 2), (.external 10, 2)]

/-- The unmerged circuit passes its own declaration and emits exactly `place`'s object. -/
theorem the_probe_with_no_equalities_is_the_placement_pass :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨[], mProbeDecl⟩ mProbe = .ok (place 3 mProbe) := by decide

/-- ⚑ **TWO ALREADY-PLACED VALUES OF THE SAME CIRCUIT, EQUATED AND DECLARED.** `external 11` at
`(4,1)` and `external 12` at `(4,3)` become one class. -/
def mProbeMerges : Merges := [(.external 11, .external 12)]

theorem an_authored_equality_is_accepted_when_declared :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨mProbeMerges, (.external 11, 2) :: mProbeDecl⟩ mProbe
      = .ok (placeWith mProbeMerges 3 mProbe) := by decide

/-- …and the σ it emits really does wire the two cells to each other — against the unmerged control,
where both self-wire. -/
theorem the_authored_equality_is_in_sigma :
    ((placeWith mProbeMerges 3 mProbe).map (·.wires)).getD 4 []
        = [⟨2,0⟩, ⟨4,3⟩, ⟨4,2⟩, ⟨4,1⟩, ⟨4,4⟩, ⟨4,5⟩, ⟨4,6⟩]
    ∧ ((place 3 mProbe).map (·.wires)).getD 4 []
        = [⟨2,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨4,3⟩, ⟨4,4⟩, ⟨4,5⟩, ⟨4,6⟩] := by
  refine ⟨by decide, by decide⟩

/-- **An UNDECLARED equality refuses.** The author merged and did not say so. -/
theorem an_undeclared_equality_refuses :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨mProbeMerges, mProbeDecl⟩ mProbe
      = .error (.undeclaredAlias (.external 11) 2) := by decide

/-- ⚑ **THE UNINTENTIONAL ALIAS, DETECTED.** This is the `exposedVars` shape: no equality is
authored at all, and the ALLOCATOR hands `external 11` to a second cell. The gate list still places,
every gate still holds, σ is still a permutation — and the census gains a binding the declaration
does not contain. -/
def mProbeAliased : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.external 10),
                   none, none, some (.external 10), none]
    , coeffs := [] }
  , { kind := .generic
    , permVars := [some (.external 2), some (.external 11), none,
                   some (.external 11), none, none, none]   -- ⚠ the accident: 12 became 11
    , coeffs := [] } ]

theorem an_unintentional_alias_in_the_gates_is_detected :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨[], mProbeDecl⟩ mProbeAliased
      = .error (.undeclaredAlias (.external 11) 2) := by decide

/-- ⚑ …and the SAME declaration accepts the unaliased circuit, so the check is discriminating and
not a refusal of everything. One accidental cell apart: green and red. -/
theorem the_same_declaration_accepts_the_unaliased_circuit :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨[], mProbeDecl⟩ mProbe = .ok (place 3 mProbe) := by decide

/-- A declared binding the circuit does NOT make refuses too — the declaration is an equality, not a
permission slip, so it cannot be padded to pass. -/
theorem a_declared_binding_the_circuit_does_not_make_refuses :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨[], (.external 11, 2) :: mProbeDecl⟩ mProbe
      = .error (.declaredAliasAbsent (.external 11) 2) := by decide

/-- **Two public words merged into one class** — the way a 67-word statement silently becomes a
66-word one. Named, and refused. -/
theorem merging_two_public_words_refuses :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨[(.external 0, .external 1)], []⟩ mProbe
      = .error (.publicWordsAliased 0 1) := by decide

/-- **A demoted public word refuses.** `internal 1` has `varIx 3 < 4 = varIx (external 2)`, so the
class would root at the internal and `place`'s public prefix cell would join ITS class — a correct
partition, but one no gate list could have authored, so §6's equivalence would stop covering the
emitted object. Refused rather than emitted. -/
theorem demoting_a_public_word_refuses :
    placeCheckedMerged ⟨3, 10⟩ [] ⟨[(.external 2, .internal 1)], []⟩ mProbe
      = .error (.publicWordDemoted 2 (.internal 1)) := by decide

/-- ⚑ **THE EXISTING REFUSALS ARE NOT WEAKENED — THEY ARE THE ONES RUNNING.** H1 bites through the
merged entry unchanged. -/
theorem h1_still_bites_through_the_merged_entry :
    placeCheckedMerged ⟨3, 0⟩ [] ⟨[], mProbeDecl⟩ mProbe
      = .error (.place (.auxOverlapsPublic 0 3)) := by decide

/-- ⚑ **AND MERGING CAN CREATE A DEAD-GAP REFERENCE — WHICH THE EXISTING GATE CATCHES.** Equating an
aux variable with `external 5` (neither a public word nor a declared aux id) renames the aux cells
into the gap. Because the merged entry routes through `placeCheckedWith` on the POST-MERGE gate
list, this needs no new check at all — and note the declaration was updated to match, so the refusal
is the gap one and not the census one. -/
theorem a_merge_into_the_dead_gap_is_refused_by_the_existing_gate :
    placeCheckedMerged ⟨3, 10⟩ []
        ⟨[(.external 5, .external 10)],
         [(.external 0, 2), (.external 1, 2), (.external 2, 2), (.external 5, 2)]⟩ mProbe
      = .error (.place (.referenceInGap 5)) := by decide

/-! ### §10a — ⚑ H2 COMPOSES FOR FREE: binding a public word to an already-placed value.

This is the use the primitive exists for. Declare a FOURTH public word: no gate reads it, so it is
inert and `placeChecked` refuses (H2). Bind it to an already-placed value with one `assertEqual` —
and it is read, at ZERO ROWS, with no edit to any gate. -/

theorem a_public_word_no_gate_reads_is_inert_and_refused :
    placeCheckedMerged ⟨4, 10⟩ [] ⟨[], mProbeDecl⟩ mProbe
      = .error (.place (.inertPublicWord 3)) := by decide

/-- ⚑ **THE HEADLINE.** One appended equality binds public word 3 to the already-placed value at
`external 12`, and the emission is ACCEPTED. -/
def bindPublicWord : Merges := [(.external 3, .external 12)]

theorem an_assertEqual_binds_the_public_word_and_it_is_accepted :
    placeCheckedMerged ⟨4, 10⟩ [] ⟨bindPublicWord, (.external 3, 2) :: mProbeDecl⟩ mProbe
      = .ok (placeWith bindPublicWord 4 mProbe) := by decide

/-- …and the binding is IN σ: the public cell `(3,0)` and the value cell `(5,3)` form a 2-cycle. -/
theorem the_public_word_is_wired_to_the_value :
    ((placeWith bindPublicWord 4 mProbe).map (·.wires)).getD 3 []
        = [⟨5,3⟩, ⟨3,1⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨3,6⟩]
    ∧ (((placeWith bindPublicWord 4 mProbe).map (·.wires)).getD 5 []).getD 3 ⟨0,0⟩ = ⟨3,0⟩ := by
  refine ⟨by decide, by decide⟩

/-- …at ZERO rows, cited from the general theorem. -/
theorem binding_the_public_word_costs_zero_rows :
    (placeWith bindPublicWord 4 mProbe).length = (place 4 mProbe).length :=
  assertEqual_costs_zero_rows _ _ _

#assert_axioms the_fragments_share_no_variable
#assert_axioms before_the_equality_the_fragments_are_unrelated
#assert_axioms the_equality_wires_the_two_fragments_together
#assert_axioms the_seam_costs_zero_rows
#assert_axioms the_merged_sigma_is_a_permutation
#assert_axioms the_seam_is_closed
#assert_axioms the_probe_with_no_equalities_is_the_placement_pass
#assert_axioms an_authored_equality_is_accepted_when_declared
#assert_axioms the_authored_equality_is_in_sigma
#assert_axioms an_undeclared_equality_refuses
#assert_axioms an_unintentional_alias_in_the_gates_is_detected
#assert_axioms the_same_declaration_accepts_the_unaliased_circuit
#assert_axioms a_declared_binding_the_circuit_does_not_make_refuses
#assert_axioms merging_two_public_words_refuses
#assert_axioms demoting_a_public_word_refuses
#assert_axioms h1_still_bites_through_the_merged_entry
#assert_axioms a_merge_into_the_dead_gap_is_refused_by_the_existing_gate
#assert_axioms a_public_word_no_gate_reads_is_inert_and_refused
#assert_axioms an_assertEqual_binds_the_public_word_and_it_is_accepted
#assert_axioms the_public_word_is_wired_to_the_value
#assert_axioms binding_the_public_word_costs_zero_rows

#assert_axioms ixVar_varIx
#assert_axioms ufRootFuel_reaches_a_root
#assert_axioms rootVar_nil
#assert_axioms merging_emits_no_row
#assert_axioms merging_costs_zero_rows
#assert_axioms merging_is_naming_the_same_variable
#assert_axioms assertEqual_is_naming_the_same_variable
#assert_axioms no_merges_is_the_placement_pass
#assert_axioms the_accepted_merge_is_closed
#assert_axioms the_accepted_placement_is_placeWith

end Dregg2.Circuit.Emit.KimchiAssertEqual
