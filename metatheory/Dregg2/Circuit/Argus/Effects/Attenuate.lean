/-
# Dregg2.Circuit.Argus.Effects.Attenuate — the capability ATTENUATE effect welded into the Argus IR,
in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone). THE CROWN weld:
attenuate is where capability NON-AMPLIFICATION (`granted.rights ≤ held.rights`) must be enforced.

`Argus/Stmt.lean` laid the cornerstone (`interp (transferStmt …) = recKExec`): the executor IS the
meaning of the IR term, by construction. It also built `checkSubset (a b : RecordKernelState → ExecAuth)`,
the FINITE-LATTICE gate — a pure domain-restrictor that commits IFF `a k ⊆ b k` over the genuine
`ExecAuth = Finset Auth` order (the FULL in-band realization of non-amplification, superseding the
cardinality-only `checkLe (… → Int)`). This module welds the cap-graph ATTENUATE effect onto an Argus
term that INTERNALIZES the FULL `granted.rights ⊆ held.rights` non-amplification in-band via `checkSubset`,
and binds it against the audited GENUINE class-A cap-root descriptor.

## The executor target — the kernel ATTENUATE step (faithful, named, not re-invented)

The running kernel-level attenuate step is `attenuateStep` (`Exec/Handlers/Authority.lean:247`):

    attenuateStep k a = some { k with caps := attenuateSlotF k.caps a.actor a.idx a.keep }

i.e. it narrows the actor's OWN `idx`-th held cap to `keep` IN PLACE (`attenuateSlotF`), edits ONLY
`caps`, and ALWAYS commits (attenuation cannot fail — at worst the identity, still narrower-or-equal).
This is the SAME `attenuateSlotF s.kernel.caps args.actor args.idx args.keep` post cap-table the genuine
descriptor's `unify_attenuate` already targets (`EffectVmEmitAttenuateA §8`). The narrowing primitive is
`attenuate keep c` (`Exec/Caps.lean:79`): for an `endpoint t rights` cap it FILTERS `rights` to those in
`keep`; a `node`/`null` cap is unchanged. So the conferred-rights of the result are a genuine SUBLIST
(hence ⊆) of the parent's (`attenuate_subset`) — the real `is_attenuation`, NOT a `()≤()` collapse.

## ⚑ THE RIGHTS-LATTICE FINDING — RESOLVED (`checkSubset`, the finite-lattice primitive, now in the IR)

The non-amplification order is `confRights granted ≤ confRights held` over `ExecAuth := Finset Auth`
ordered by `⊆` (`Exec/Caps.lean:57-66`), a SUBSET relation over the 7-atom powerset of
`Auth = {read,write,grant,call,reply,reset,control}` (`Authority/Positional.lean:37`). This is a PARTIAL
order: `{read}` and `{write}` are INCOMPARABLE. The PRIOR weld gated on `checkLe (a b : … → Int)`, which
compares two SCALAR `Int` read-outs with the TOTAL order `a k ≤ b k` — and there is NO order-embedding of
`(Finset Auth, ⊆)` into `(Int, ≤)`: any bitmask encoding makes `Int ≤` DISAGREE with `⊆` (e.g. `{write}` =
bit 2² = 2 and `{read}` = bit 2⁰ = 1 give `1 ≤ 2`, yet `{read} ⊄ {write}`). So `checkLe` could carry only
the rights-CARDINALITY shadow (`granted ⊆ held ⟹ |granted| ≤ |held|`), NECESSARY but NOT SUFFICIENT for
the subset (`checkLe_card_necessary_not_sufficient`, retained below: two equal-cardinality rights sets can
be non-subset / incomparable). **RESOLUTION: `Argus/Stmt.lean` now provides `RecStmt.checkSubset (a b :
RecordKernelState → ExecAuth)` — the domain-restrictor over the genuine `Finset Auth` `⊆` (= `≤`) order
(`Auth` has `DecidableEq`, so the gate is computable). This module's `attenuateStmt` GATES ON IT: the term
is `seq (checkSubset (granted.rights) (held.rights)) (setCaps …)`, so the FULL `granted.rights ⊆
held.rights` non-amplification is now enforced IN-BAND — rejecting BOTH a strict superset AND an
incomparable pair (`checkSubset_rejects_overbroad_grant` / `checkSubset_rejects_incomparable_grant`, §6).
The cardinality gap is closed.**

## HOW NON-AMPLIFICATION IS WITNESSED IN-BAND — the three legs, stated precisely (leg 1 now FULL subset)

  1. **`checkSubset` in the term (in-band, executor-side, FULL subset):** the term is
     `seq (checkSubset (granted.rights) (held.rights)) (setCaps <install attenuated slot>)`. The
     `checkSubset` gate is the in-band non-amplification check over the GENUINE rights lattice: it admits
     IFF the installed cap's conferred-rights SET is `⊆` the parent's. It REJECTS a superset AND an
     incomparable pair, proven two-valued below — the FULL order, not the cardinality shadow.
  2. **the descriptor binds WHICH rights were installed (circuit-side):** `attenuateGenuine_sound` forces
     `post.capRoot = hash[ hash[holder,target,RIGHTS,op], pre.capRoot ]` — the GENUINE in-row cap-root
     recompute (NOT an opaque parameter), and `attenuateGenuine_binds_edge` anti-ghosts the `RIGHTS`
     param (and holder/target/op + old root) through the published `state_commit`: a tampered installed
     `RIGHTS` digest MOVES `cap_root`, MOVES `state_commit` ⇒ UNSAT. So the circuit PINS which rights
     digest landed in the cap table.
  3. **the executor STRUCTURALLY attenuates (the full subset):** `attenuate keep c` filters the rights,
     so `confRights (attenuate keep c) ≤ confRights c` over the genuine `Finset Auth ⊆` order
     (`attenuate_subset` / `attenuate_confRights_le`) — the FULL subset, which is exactly why the in-band
     `checkSubset` gate (leg 1) admits on every genuine attenuation (`grantedRightsSet_le_held`).

Together: the descriptor pins WHICH rights digest was installed (leg 2); the in-term `checkSubset` proves
the installed rights SET is `⊆` the parent's IN-BAND, the FULL order (leg 1); and the executor's
`attenuate` structurally produces that same subset (leg 3). Leg 1 and leg 3 now state the SAME full
subset — the prior cardinality/subset gap is closed.

## HONEST SURFACE — exactly the cap-family per-cell weld surface (do NOT over-read)

The circuit side is the audited CLASS-A genuine descriptor `attenuateVmDescriptorGenuine` +
`attenuateGenuine_sound` (`EffectVmEmitAttenuateA §G`). The weld concludes the SAME per-cell surface the
cap family lives on: a SINGLE-ROW AIR whose `CapCellSpecGenuine` pins ONE cell's transition — the
`cap_root` GENUINELY RECOMPUTED `hash[edge_leaf, pre.capRoot]` (FORCED, not opaque), every other column
(balance limbs / nonce / 8 fields / reserved) FROZEN — bound into the published `state_commit`. What it
does NOT claim: it does NOT assert the circuit row's cap-table FUNCTION equals the executor's
`attenuateSlotF …` as a whole `Caps` function (the EffectVM row carries the `cap_root` DIGEST, not the
function — they agree only up to the cap-root, the `cap_root` connector); the executor produces the real
`Caps` function (the cornerstone), the circuit produces the genuine recompute of its digest. That
digest-not-function boundary is faithful, stated, not hidden — the SAME boundary the cap-graph keystone
carries. Cross-row composition is the turn layer (`TurnEmit`), cited not claimed.

## Honesty

`#assert_axioms` on both welds ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via
the named `Poseidon2SpongeCR` hypothesis (inside the cited anti-ghost `attenuateGenuine_binds_edge`, not
the welds here). No `sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge. Non-vacuity:
`checkSubset` REJECTS an over-broad grant (rights SET ⊄ parent ⇒ `none`) AND an INCOMPARABLE pair (the
gain over `checkLe`), and ADMITS a genuine attenuation; the genuine descriptor is the non-trivial class-A
circuit, not the placeholder. This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Exec.Handlers.Authority

namespace Dregg2.Circuit.Argus.Effects.Attenuate

open Dregg2.Exec
open Dregg2.Authority (Auth Cap Caps capAuthConferred)
-- `VmRowEnv` / `satisfiedVm` / `prmCol` / `saCol` / `sbCol` are the unqualified EffectVM IR names
-- (exactly as `Argus/Compile.lean` and the sibling `Effects/*` modules open them).
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Argus
  (RecStmt interp interp_checkLe checkLe_admits_iff interp_checkSubset checkSubset_admits_iff kC)
-- The kernel-level ATTENUATE step + its slot-narrowing primitive (the refinement target).
open Dregg2.Exec.TurnExecutorFull (attenuateSlotF)
open Dregg2.Exec.Handlers.Authority (attenuateStep AttenuateArgs)
-- The AUDITED genuine class-A cap-root descriptor + its soundness + the genuine per-cell spec.
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuine attenuateGenuineRowGates attenuateGenuineHashSites
   attenuateGenuine_sound CapCellSpecGenuine CapRowEncodes gFieldFixAll)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds capRecomputeSites)

set_option linter.unnecessarySeqFocus false

/-! ## §0 — the rights-CARDINALITY read-outs (the in-band SCALAR shadow of non-amplification).

`checkLe` restricts on `Int ≤`, so the in-band non-amplification gate reads two `Int` scalars: the
rights-COUNT of the parent (held) cap and of the attenuated (granted) cap, both read off the kernel
state. `heldCapAt actor idx k` is the actor's `idx`-th held cap (the slot `attenuateSlotF` narrows); the
two read-outs are the conferred-rights LENGTHs of that cap and of its `keep`-attenuation. -/

/-- The actor's `idx`-th held cap on kernel state `k` (the slot `attenuateSlotF` narrows in place); the
parent cap whose authority the attenuation must not exceed. `Cap.null` when the slot is absent (a
`null` cap confers no rights — the safe floor). -/
def heldCapAt (actor : CellId) (idx : Nat) (k : RecordKernelState) : Cap :=
  (k.caps actor).getD idx Cap.null

/-- The HELD-rights cardinality read-out (the parent cap's conferred-rights COUNT), as an `Int`. -/
def heldRightsCard (actor : CellId) (idx : Nat) : RecordKernelState → Int :=
  fun k => ((capAuthConferred (heldCapAt actor idx k)).length : Int)

/-- The GRANTED-rights cardinality read-out (the attenuated cap's conferred-rights COUNT), as an `Int`.
This is the value the attenuate move would install — its rights-count must not exceed the parent's. -/
def grantedRightsCard (actor : CellId) (idx : Nat) (keep : List Auth) : RecordKernelState → Int :=
  fun k => ((capAuthConferred (attenuate keep (heldCapAt actor idx k))).length : Int)

/-- **`grantedRightsCard_le_held` — the in-band gate ALWAYS admits a genuine attenuation (PROVED).**
The attenuated cap's conferred-rights COUNT is `≤` the parent's, for EVERY cap shape: the `endpoint`
filter shrinks the rights list (`List.length_filter_le`); `node`/`null` caps are unchanged. So the
`checkLe` non-amplification gate (granted-count ≤ held-count) commits on every genuine attenuate — it is
fail-closed, never fail-stuck. (The genuine *subset* is the stronger `attenuate_subset`; this is its
cardinality shadow, the scalar `checkLe` can carry.) -/
theorem grantedRightsCard_le_held (actor : CellId) (idx : Nat) (keep : List Auth)
    (k : RecordKernelState) :
    grantedRightsCard actor idx keep k ≤ heldRightsCard actor idx k := by
  unfold grantedRightsCard heldRightsCard
  have hlen : (capAuthConferred (attenuate keep (heldCapAt actor idx k))).length
                ≤ (capAuthConferred (heldCapAt actor idx k)).length := by
    cases h : heldCapAt actor idx k with
    | endpoint t r => simp only [attenuate, capAuthConferred]; exact List.length_filter_le _ _
    | node t => simp [attenuate, capAuthConferred]
    | null => simp [attenuate, capAuthConferred]
  exact_mod_cast hlen

/-! ### §0′ — the FULL rights-SET read-outs (the genuine `Finset Auth` non-amplification carrier).

The cardinality read-outs above are the SCALAR shadow `checkLe` carries; the FULL non-amplification gate
reads the genuine rights LATTICE element `confRights c = (capAuthConferred c).toFinset : ExecAuth`
(`Exec/Caps.lean:66`), ordered by `⊆`. These two read-outs are the conferred-rights SETS of the held
(parent) cap and of its `keep`-attenuation — the values the FULL `granted.rights ⊆ held.rights` gate
(`checkSubset`) compares. -/

/-- The HELD-rights SET read-out (the parent cap's conferred rights as a `Finset Auth` lattice element).
The authority the attenuation must not exceed, now in its genuine `⊆`-ordered carrier (not a scalar). -/
def heldRightsSet (actor : CellId) (idx : Nat) : RecordKernelState → ExecAuth :=
  fun k => confRights (heldCapAt actor idx k)

/-- The GRANTED-rights SET read-out (the attenuated cap's conferred rights as a `Finset Auth`). The value
the attenuate move would install — its rights SET must be `⊆` the parent's (full non-amplification). -/
def grantedRightsSet (actor : CellId) (idx : Nat) (keep : List Auth) : RecordKernelState → ExecAuth :=
  fun k => confRights (attenuate keep (heldCapAt actor idx k))

/-- **`grantedRightsSet_le_held` — the FULL in-band gate ALWAYS admits a genuine attenuation (PROVED).**
The attenuated cap's conferred-rights SET is `⊆` (= `≤`) the parent's, over the genuine `ExecAuth =
Finset Auth` order — directly `attenuate_confRights_le` (the executor's `attenuate` STRUCTURALLY narrows,
`attenuate_subset` lifted to `Finset`). So the `checkSubset` non-amplification gate (granted ⊆ held)
commits on every genuine attenuate: fail-closed, never fail-stuck. This is the FULL subset, NOT the
cardinality shadow `grantedRightsCard_le_held` carries — the gain the `checkSubset` upgrade buys. -/
theorem grantedRightsSet_le_held (actor : CellId) (idx : Nat) (keep : List Auth)
    (k : RecordKernelState) :
    grantedRightsSet actor idx keep k ≤ heldRightsSet actor idx k :=
  attenuate_confRights_le keep (heldCapAt actor idx k)

/-! ## §1 — THE IR TERM: the in-band FULL-SUBSET non-amplification `checkSubset` gate, then the install.

`attenuateStmt = seq (checkSubset (granted.rights) (held.rights)) (setCaps <attenuateSlotF install>)`.
The leading `checkSubset` is the in-band non-amplification gate over the GENUINE rights lattice
(`ExecAuth = Finset Auth`, ordered by `⊆`): the installed cap's conferred-rights SET must be `⊆` the
parent's. This is the FULL `granted.rights ⊆ held.rights` rule INTERNALIZED in the term — not merely its
cardinality shadow (the `checkLe` of the prior weld, which `checkLe_card_necessary_not_sufficient`
showed could not reject an incomparable pair). The `setCaps` is the EXACT executor cap-table write
(`attenuateSlotF k.caps actor idx keep`). This is the whole point of the crown weld: the FULL
non-amplification order is now an in-band IR gate. -/

/-- **The attenuate effect as an Argus IR term (FULL in-band non-amplification).** Gate on the genuine
subset check `granted.rights ⊆ held.rights` over `ExecAuth = Finset Auth` (via `checkSubset`), then
install the in-place narrowed actor slot (`attenuateSlotF` — the EXACT executor cap-table write). The
`checkSubset` leg is the in-band realization of the FULL `granted.rights ⊆ held.rights` partial order
(rejecting BOTH a superset AND an incomparable pair — the thing the prior `checkLe` cardinality gate
could not); the `setCaps` leg is the verified executor move. -/
def attenuateStmt (actor : CellId) (idx : Nat) (keep : List Auth) : RecStmt :=
  RecStmt.seq
    (RecStmt.checkSubset (grantedRightsSet actor idx keep) (heldRightsSet actor idx))
    (RecStmt.setCaps (fun k => attenuateSlotF k.caps actor idx keep))

/-! ## §2 — THE CORNERSTONE: `interp` of the attenuate term IS the kernel ATTENUATE step.

The SAME shape as the transfer/escrow cornerstones, with the leading gate being the `checkSubset` FULL
non-amplification domain-restrictor instead of a `guard`. Because a genuine attenuation NEVER amplifies —
the executor's `attenuate` STRUCTURALLY produces a subset (`grantedRightsSet_le_held`, i.e.
`attenuate_confRights_le`) — the `checkSubset` gate ALWAYS fires (`some k`), so the `bind` runs the
`setCaps` install — which is exactly `attenuateStep`'s `some { k with caps := attenuateSlotF … }`. The
executor IS the meaning of the term, INCLUDING that the in-term FULL-subset `checkSubset` gate matches
the executor's (always-admitting) attenuation discipline. The full subset is now enforced IN-BAND. -/

/-- **The cornerstone (crown).** `interp` of the attenuate term IS the kernel ATTENUATE step
`attenuateStep` — the same partial function, by construction, exactly as the transfer/mint/burn/escrow
cornerstones. The in-term FULL `checkSubset` non-amplification gate is shown to MATCH the executor: it
admits on every genuine attenuation (`grantedRightsSet_le_held` — the genuine `granted.rights ⊆
held.rights`, via `attenuate_subset`/`attenuate_confRights_le`), so the term commits exactly when
(always) `attenuateStep` does, installing the SAME `attenuateSlotF` cap table. -/
theorem interp_attenuateStmt_eq_attenuateStep (actor : CellId) (idx : Nat) (keep : List Auth)
    (k : RecordKernelState) :
    interp (attenuateStmt actor idx keep) k = attenuateStep k ⟨actor, idx, keep⟩ := by
  simp only [attenuateStmt, interp, Option.bind]
  -- the in-band FULL non-amplification `checkSubset` admits (granted.rights ⊆ held.rights) on every
  -- attenuation — the executor's `attenuate` structurally narrows the rights set.
  rw [if_pos (grantedRightsSet_le_held actor idx keep k)]
  -- the `setCaps` install IS `attenuateStep`'s `some { k with caps := attenuateSlotF … }`.
  rfl

#assert_axioms interp_attenuateStmt_eq_attenuateStep

/-! ## §3 — the `checkSubset` non-amplification gate is GENUINELY TWO-VALUED over the FULL subset order
(the in-band tooth, now closing the cardinality gap).

The gate is worthless if it admitted everything. It does not: `checkSubset` REJECTS (fails closed) any
move whose installed cap's rights SET is NOT `⊆` the parent's (`checkSubset_admits_iff`, the §L′
keystone) — and crucially that rejection covers an INCOMPARABLE pair, not just a strict superset. This is
the FULL `granted.rights ⊆ held.rights` enforced in-band, closing the gap the prior `checkLe` cardinality
gate left open (`checkLe_card_necessary_not_sufficient`, retained below as the precise record of WHY the
upgrade was needed). -/

/-- **`attenuateStmt_admits_iff` — the in-band gate is exactly the FULL non-amplification SUBSET check.**
The attenuate term COMMITS (its `checkSubset` leg admits) IFF the installed cap's conferred-rights SET is
`⊆` the parent's, over the genuine `ExecAuth = Finset Auth` order. So the in-band gate genuinely REJECTS
(fails closed) a move that is NOT a subset — a strict superset OR an incomparable pair: two-valued,
non-vacuous, and the FULL partial order (not the cardinality shadow). -/
theorem attenuateStmt_admits_iff (actor : CellId) (idx : Nat) (keep : List Auth)
    (k : RecordKernelState) :
    (interp (attenuateStmt actor idx keep) k).isSome = true ↔
      grantedRightsSet actor idx keep k ≤ heldRightsSet actor idx k := by
  -- the `checkSubset` leg gates the whole term: if it rejects, the `bind` short-circuits to `none`; if
  -- it admits, the `setCaps` install always commits (`some`). So the term is `some` iff the gate admits.
  constructor
  · intro hsome
    by_contra hgt
    -- if the gate rejected, the leading `checkSubset` is `none`, so the whole term is `none`.
    rw [attenuateStmt, interp, interp_checkSubset, if_neg hgt] at hsome
    simp at hsome
  · intro hle
    rw [interp_attenuateStmt_eq_attenuateStep]
    -- `attenuateStep` always commits (`some`).
    rfl

/-- **⚑ `checkLe_card_necessary_not_sufficient` — the FINDING, pinned as a theorem.** Rights-cardinality
`≤` (what `checkLe`'s `Int ≤` carries in-band) is NECESSARY but NOT SUFFICIENT for the genuine
non-amplification subset order over `Finset Auth`: here are two rights sets of EQUAL cardinality (`1`)
that are NOT subset-related (`{read} ⊄ {write}`). So `checkLe` over the cardinality scalar CANNOT, by
itself, enforce the full `granted.rights ⊆ held.rights`; the IR needs a `checkSubset` (finite-lattice
`≤`) primitive to internalize the full subset gate in-band. (The executor's `attenuate` structurally
gives the full subset — `attenuate_subset`; this theorem isolates precisely what `checkLe` cannot.) -/
theorem checkLe_card_necessary_not_sufficient :
    -- equal cardinality …
    ([Auth.read].length = [Auth.write].length)
    -- … yet NOT subset-related (neither way), so cardinality `≤` does not imply the subset order.
    ∧ ¬ (({Auth.read} : Finset Auth) ⊆ ({Auth.write} : Finset Auth))
    ∧ ¬ (({Auth.write} : Finset Auth) ⊆ ({Auth.read} : Finset Auth)) := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

#assert_axioms attenuateStmt_admits_iff
#assert_axioms checkLe_card_necessary_not_sufficient

/-! ## §4 — bridges from `satisfiedVm` of the genuine descriptor to its two ingredients.

`attenuateGenuine_sound` consumes the frame-freeze row gates and the cap-root recompute SEPARATELY (not
a packed `satisfiedVm`). `satisfiedVm hash attenuateVmDescriptorGenuine env true true` IS (definitionally)
`(∀ c ∈ constraints, c.holdsVm env true true) ∧ siteHoldsAll hash env hashSites`, with
`constraints = attenuateGenuineRowGates ++ …` and `hashSites = capRecomputeSites ++ attenuateHashSites`.
We split it into the two ingredients the soundness needs. -/

/-- **`satisfied_gives_row_gates`.** A satisfying genuine-descriptor witness gives the frame-freeze row
gates (the row gates are pure `.gate` bodies, so the boundary flags `true true` collapse to `false
false`). The first `++`-summand of the descriptor's constraint list. -/
theorem satisfied_gives_row_gates (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hsat : satisfiedVm hash attenuateVmDescriptorGenuine env true true) :
    ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false := by
  obtain ⟨hcon, _hsites⟩ := hsat
  intro c hc
  -- `constraints = (attenuateGenuineRowGates ++ transitionAll) ++ boundaryFirstPins`; lift `hc` through both.
  have hmem : c ∈ attenuateVmDescriptorGenuine.constraints :=
    List.mem_append_left _ (List.mem_append_left _ hc)
  have hh := hcon c hmem
  -- every entry of the frame-freeze gates is a `.gate _`, whose `holdsVm` ignores the boundary flags.
  unfold attenuateGenuineRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simp only [VmConstraint.holdsVm] at hh ⊢ <;> exact hh

/-- **`satisfied_gives_capRootHolds`.** A satisfying genuine-descriptor witness gives the cap-root
recompute (`capRootHolds = siteHoldsAll … capRecomputeSites`): the first two hash-sites of the
descriptor's site list (`capRecomputeSites ++ attenuateHashSites`). The two recompute sites read only
param/state columns (never earlier digests), so their holds-conditions are the SAME prefix whether or not
the GROUP-4 commitment sites follow. -/
theorem satisfied_gives_capRootHolds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hsat : satisfiedVm hash attenuateVmDescriptorGenuine env true true) :
    capRootHolds hash env := by
  obtain ⟨_hcon, hsites, _⟩ := hsat
  -- `hashSites = attenuateGenuineHashSites = capRecomputeSites ++ attenuateHashSites`.
  show capRootHolds hash env
  unfold capRootHolds capRecomputeSites siteHoldsAll
  have hs : siteHoldsAll hash env attenuateGenuineHashSites := hsites
  unfold attenuateGenuineHashSites capRecomputeSites at hs
  simp only [siteHoldsAll, siteHoldsAll.go, List.cons_append, List.nil_append] at hs ⊢
  exact ⟨hs.1, hs.2.1, trivial⟩

#assert_axioms satisfied_gives_row_gates
#assert_axioms satisfied_gives_capRootHolds

/-! ## §5 — THE WELD: a satisfying witness of the GENUINE descriptor agrees, per cell, with the
post-state the IR term's executor interpretation produces — AND genuinely recomputes the bound cap edge.

Unlike `Argus/Compile.lean` (which routes through the central `compileE`), this module welds DIRECTLY
against the audited class-A `attenuateVmDescriptorGenuine` (the genuine cap-root recompute). The circuit
side is `attenuateGenuine_sound` (the §G class-A soundness, fed via the §4 bridges); the executor side is
the §2 cornerstone. The non-amplification in-band leg is the §1/§3 `checkLe` carried by the IR term. -/

/-- **`attenuate_compile_sound` — the welded soundness (attenuate slice, the crown).**

Suppose, for the Argus attenuate term `attenuateStmt actor idx keep`:
  * the audited class-A circuit `attenuateVmDescriptorGenuine` is SATISFIED by `(env, true, true)` under
    the abstract Poseidon carrier `hash`, and its `CapRowEncodes` decoding NAMES the `(pre, post)` cell
    states with the post-cap-digest `capDigestNew` (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (attenuateStmt actor idx keep) k = some k'`
    (`hexec`) — which, by the §2 cornerstone, IS the kernel step `attenuateStep` installing
    `attenuateSlotF k.caps actor idx keep`.

Then the circuit's pinned post-cell state is the GENUINE `CapCellSpecGenuine`: `post.capRoot` is the
FORCED in-row recompute `hash[ hash[holder,target,rights,op], pre.capRoot ]` (NOT an opaque parameter —
the cap-root is genuinely recomputed from the bound cap-edge mutation + the old root), every other column
(balance limbs / nonce / 8 fields / reserved) FROZEN.

PRECISELY (do NOT over-read): the descriptor PINS *which* cap-edge digest (holder/target/RIGHTS/op) landed
in `cap_root` and binds it into `state_commit` (`attenuateGenuine_binds_edge`, cited: a tampered `RIGHTS`
digest moves `cap_root` ⇒ UNSAT) — that is leg 2 of non-amplification. The IN-BAND `checkSubset` of the
term (leg 1) now proves the installed rights SET is `⊆` the parent's — the FULL `granted.rights ⊆
held.rights` order (the cardinality gap of the prior `checkLe` weld is CLOSED in-band); the executor's
`attenuate` (leg 3, `attenuate_subset`/`attenuate_confRights_le`) STRUCTURALLY produces that same subset,
which is exactly why the `checkSubset` gate always admits a genuine attenuation. The descriptor itself
does NOT re-derive the subset order (it binds WHICH rights digest landed); the FULL non-amplification is
supplied by the in-band `checkSubset` gate + the executor's structural attenuation — both now the genuine
subset, not a scalar shadow. The executor produces the real `Caps` FUNCTION; the circuit produces the
genuine recompute of its `cap_root` DIGEST (the digest-not-function boundary, faithful, stated). -/
theorem attenuate_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hsat : satisfiedVm hash attenuateVmDescriptorGenuine env true true)
    (hexec : interp (attenuateStmt actor idx keep) k = some k') :
    -- the GENUINE per-cell post-state: `post.capRoot` is the FORCED cap-root recompute, frame frozen …
    CapCellSpecGenuine hash env pre post
    -- … and the EXECUTOR committed the kernel ATTENUATE step, installing the narrowed actor slot.
    ∧ attenuateStep k ⟨actor, idx, keep⟩ = some k'
    ∧ k'.caps = attenuateSlotF k.caps actor idx keep := by
  -- circuit side: split the satisfying witness into its two ingredients, feed the audited class-A soundness.
  have hgates := satisfied_gives_row_gates hash env hsat
  have hrec := satisfied_gives_capRootHolds hash env hsat
  have hspec := attenuateGenuine_sound hash env pre post capDigestNew henc hgates hrec
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the kernel step `attenuateStep`.
  rw [interp_attenuateStmt_eq_attenuateStep] at hexec
  refine ⟨hspec, hexec, ?_⟩
  -- the committed `attenuateStep` installs `attenuateSlotF k.caps actor idx keep` into `caps`.
  unfold attenuateStep at hexec
  simp only [Option.some.injEq] at hexec
  rw [← hexec]

#assert_axioms attenuate_compile_sound

/-! ## §6 — NON-VACUITY: the genuine descriptor is the real class-A circuit; the in-band `checkSubset`
genuinely admits a valid attenuation and REJECTS a non-subset — INCLUDING an incomparable pair.

The weld would be worthless if (a) the descriptor were the inert placeholder, or (b) the in-band gate
admitted everything. Neither: the genuine descriptor carries 12 frame gates + the cap-root recompute (the
opaque `gCapMove` is GONE), and the `checkSubset` gate is two-valued over the FULL subset order (admits a
real narrowing of a 2-rights cap to 1; rejects a synthetic widening AND — the gain over the prior `checkLe`
cardinality gate — rejects an INCOMPARABLE pair). -/

/-- A concrete kernel state: actor `0` holds one `endpoint 9 [read, write]` cap (2 conferred rights), on
the §C two-cell `kC` base. The slot `attenuateSlotF 0 0` narrows. -/
def kAtten : RecordKernelState :=
  { kC with caps := fun l => if l = 0 then [Cap.endpoint 9 [Auth.read, Auth.write]] else [] }

/-- **NON-VACUITY (witness TRUE — the in-band gate ADMITS a genuine attenuation).** Narrowing actor `0`'s
held `[read, write]` cap (rights `{read,write}`) to `[read]` (rights `{read}`) has granted-set `{read} ⊆
{read,write} =` held-set, so the `checkSubset` FULL non-amplification gate COMMITS and the term installs
the narrowed slot (`isSome`). -/
theorem attenuateStmt_admits_valid :
    (interp (attenuateStmt 0 0 [Auth.read]) kAtten).isSome = true := by
  rw [attenuateStmt_admits_iff]
  -- granted-rights-set ({read}) ⊆ held-rights-set ({read,write}) on `kAtten`.
  decide

/-- **NON-VACUITY (witness FALSE / the in-band anti-amplification tooth — superset).** A synthetic move
whose installed cap's rights SET is a strict SUPERSET of the parent's (`{read,write} ⊄ {read}`) is
REJECTED by the `checkSubset` gate (`interp = none`) — the in-band FULL non-amplification check fails
closed on amplification. (We exhibit the rejection directly on `checkSubset`, the term's gating leg, with
an explicit over-broad granted-vs-held pair.) -/
theorem checkSubset_rejects_overbroad_grant :
    interp (RecStmt.checkSubset (fun _ => ({Auth.read, Auth.write} : Finset Auth))
              (fun _ => ({Auth.read} : Finset Auth))) kC = none := by
  rw [interp_checkSubset]; decide

/-- **⚑ NON-VACUITY (the GAIN over `checkLe` — the in-band gate rejects an INCOMPARABLE pair).** The
thing the prior cardinality `checkLe` could NEVER do (`checkLe_card_necessary_not_sufficient`): a move
granting `{write}` against a parent holding only `{read}` (EQUAL cardinality `1`, but NEITHER a subset of
the other) is REJECTED by `checkSubset` (`interp = none`). This is the FULL `granted.rights ⊆ held.rights`
partial order enforced in-band — the crown upgrade, demonstrated on the actual gating leg of the term. -/
theorem checkSubset_rejects_incomparable_grant :
    interp (RecStmt.checkSubset (fun _ => ({Auth.write} : Finset Auth))
              (fun _ => ({Auth.read} : Finset Auth))) kC = none := by
  rw [interp_checkSubset]; decide

/-- **NON-VACUITY (the descriptor is the genuine class-A circuit, not the placeholder).** The genuine
attenuate descriptor carries 12 frame-freeze gates + 14 transition + 4 boundary = 30 constraints, and 6
hash-sites (2 cap-root-recompute + 4 GROUP-4 commitment) — the opaque `gCapMove` parameter gate is GONE.
So `attenuate_compile_sound` is a statement about a REAL genuinely-recomputed cap-root circuit. -/
theorem attenuateVmDescriptorGenuine_nontrivial :
    attenuateVmDescriptorGenuine.constraints.length = 12 + 14 + 4
    ∧ attenuateVmDescriptorGenuine.hashSites.length = 6 := by
  refine ⟨by decide, by decide⟩

#assert_axioms attenuateStmt_admits_valid
#assert_axioms checkSubset_rejects_overbroad_grant
#assert_axioms checkSubset_rejects_incomparable_grant
#assert_axioms attenuateVmDescriptorGenuine_nontrivial

/-! ## §W — THE MAGNESIUM CROWN re-exported for the attenuate weld (FULL 17-field RUNNABLE binding).

The §-genuine descriptor binds the per-cell block. The shared cap-graph WIDE descriptor
(`EffectVmEmitAttenuateA §W`, `attenuateVmDescriptorWide`) lifts the RUNNABLE binding to the FULL
17-field post-state: the per-cell `cap_root` MOVE + frame freeze AND the 8 side-table roots (frozen — a
caps-only effect). `cap_runnable_full_sound` is that crown; `cap_runnable_rejects_root_tamper` /
`cap_runnable_rejects_cap_root_tamper` are the whole-state anti-ghost teeth. We re-export the crown for
the attenuate weld so the magnesium full-state property is visible at this layer. -/

/-- **`attenuate_runnable_full_sound` — the attenuate MAGNESIUM crown (re-exported).** A row satisfying
the wide runnable cap-graph descriptor pins the FULL 17-field post-state. The shared
`cap_runnable_full_sound` at the attenuate cap-digest. -/
theorem attenuate_runnable_full_sound (capDigestNew : ℤ)
    (preRoots : Dregg2.Exec.SystemRoots.SysRoots) (hash : List ℤ → ℤ)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (postRoots : Dregg2.Exec.SystemRoots.SysRoots)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.IsAttenRow env)
    (henc : Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapRowEncodes env pre post capDigestNew)
    (hroots : postRoots = preRoots)
    (hsat : Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash
              Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptorWide env true true) :
    Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapFullClause capDigestNew preRoots pre post postRoots :=
  Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.cap_runnable_full_sound
    capDigestNew preRoots hash env pre post postRoots hrow henc hroots hsat

#assert_axioms attenuate_runnable_full_sound

end Dregg2.Circuit.Argus.Effects.Attenuate
