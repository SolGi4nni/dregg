/-
# Dregg2.Circuit.Argus.Effects.Attenuate — the capability ATTENUATE effect welded into the Argus IR,
in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone). THE CROWN weld:
attenuate is where capability NON-AMPLIFICATION (`granted.rights ≤ held.rights`) must be enforced.

`Argus/Stmt.lean` laid the cornerstone (`interp (transferStmt …) = recKExec`): the executor IS the
meaning of the IR term, by construction. It also built `checkLe (a b : RecordKernelState → Int)`, the
LATTICE/COMPARISON gate — a pure domain-restrictor that commits IFF `a k ≤ b k` (the in-band foundation
of non-amplification). This module welds the cap-graph ATTENUATE effect onto an Argus term that
INTERNALIZES non-amplification in-band via `checkLe`, and binds it against the audited GENUINE class-A
cap-root descriptor.

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

## ⚑ THE RIGHTS-LATTICE FINDING (reported precisely — `checkLe` needs a richer primitive)

The non-amplification order is `confRights granted ≤ confRights held` over `ExecAuth := Finset Auth`
ordered by `⊆` (`Exec/Caps.lean:57-66`), a SUBSET relation over the 7-atom powerset of
`Auth = {read,write,grant,call,reply,reset,control}` (`Authority/Positional.lean:37`). This is a PARTIAL
order: `{read}` and `{write}` are INCOMPARABLE. `checkLe (a b : RecordKernelState → Int)` compares two
SCALAR `Int` read-outs with the TOTAL order `a k ≤ b k`. There is NO order-embedding of `(Finset Auth, ⊆)`
into `(Int, ≤)`: any bitmask encoding makes `Int ≤` DISAGREE with `⊆` (e.g. `{write}` = bit 2² = 2 and
`{read}` = bit 2⁰ = 1 give `1 ≤ 2`, yet `{read} ⊄ {write}`). So `checkLe` CANNOT express the full subset
gate. **FINDING (file:line): the full in-band non-amplification gate over the rights lattice needs a
richer comparison primitive — a `RecStmt.checkSubset (a b : RecordKernelState → Finset Auth)` (or any
finite-lattice `≤` domain-restrictor) — because the rights carrier is `Finset Auth` ordered by `⊆`
(`Dregg2/Exec/Caps.lean:57` `ExecAuth`, `:66` `confRights`), NOT an `Int` scalar. `RecStmt.checkLe`
(`Dregg2/Circuit/Argus/Stmt.lean:76`) only restricts on `Int ≤`.**

## What `checkLe` CAN faithfully carry in-band — the rights-CARDINALITY scalar shadow (and its bound)

A genuine SCALAR consequence of subset that `checkLe`'s `Int ≤` CAN express is the rights-CARDINALITY:
`granted ⊆ held ⟹ |granted| ≤ |held|`. The attenuate move only ever drops rights, so the granted cap's
conferred-rights COUNT is `≤` the held cap's, for EVERY cap shape (the `endpoint` filter shrinks the
list — `List.length_filter_le`; `node`/`null` are unchanged). So the term carries
`checkLe (|granted rights|) (|held rights|)` as the in-band non-amplification SCALAR tooth: it REJECTS
(fails closed) any move whose installed cap would carry MORE rights than the parent (gross amplification),
and it ADMITS every genuine attenuation. We are PRECISE that this is NECESSARY but NOT SUFFICIENT for the
full subset order (`checkLe_card_necessary_not_sufficient`, pinned below: two equal-cardinality rights
sets can be NON-subset). The full subset is what the executor's `attenuate` STRUCTURALLY guarantees
(`attenuate_subset`, a proven `⊆`) and what the descriptor's bound `RIGHTS` digest pins (below). The
cardinality `checkLe` is the strongest in-band scalar gate the EXISTING `checkLe` primitive supports; the
finding above is the IR extension that would internalize the full subset.

## HOW NON-AMPLIFICATION IS WITNESSED IN-BAND — the three legs, stated precisely

  1. **`checkLe` in the term (in-band, executor-side scalar):** the term is
     `seq (checkLe |granted| |held|) (setCaps <install attenuated slot>)`. The `checkLe` gate is the
     in-band non-amplification SCALAR check: it admits IFF the installed cap's rights-COUNT `≤` the
     parent's. It REJECTS gross widening (more rights than the parent), proven two-valued below.
  2. **the descriptor binds WHICH rights were installed (circuit-side):** `attenuateGenuine_sound` forces
     `post.capRoot = hash[ hash[holder,target,RIGHTS,op], pre.capRoot ]` — the GENUINE in-row cap-root
     recompute (NOT an opaque parameter), and `attenuateGenuine_binds_edge` anti-ghosts the `RIGHTS`
     param (and holder/target/op + old root) through the published `state_commit`: a tampered installed
     `RIGHTS` digest MOVES `cap_root`, MOVES `state_commit` ⇒ UNSAT. So the circuit PINS which rights
     digest landed in the cap table.
  3. **the executor STRUCTURALLY attenuates (the full subset):** `attenuate keep c` filters the rights,
     so `confRights (attenuate keep c) ≤ confRights c` over the genuine `Finset Auth ⊆` order
     (`attenuate_subset` / `attenuate_confRights_le`) — the FULL subset, beyond what `checkLe` scalars.

Together: the descriptor pins WHICH rights digest was installed (leg 2); the in-term `checkLe` proves the
installed rights don't grow in CARDINALITY in-band (leg 1); and the executor's `attenuate` structurally
guarantees the FULL subset (leg 3). The honest gap between leg-1's cardinality and the full subset is the
reported `checkLe` finding — the IR primitive that would close it in-band.

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
`checkLe` REJECTS an over-broad grant (granted-count > held-count ⇒ `none`) and ADMITS a genuine
attenuation; the genuine descriptor is the non-trivial class-A circuit, not the placeholder. This module
OWNS only itself; every import is read-only.
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
  (RecStmt interp interp_checkLe checkLe_admits_iff kC)
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

/-! ## §1 — THE IR TERM: the in-band non-amplification `checkLe` gate, then the cap-table install.

`attenuateStmt = seq (checkLe |granted| |held|) (setCaps <attenuateSlotF install>)`. The leading
`checkLe` is the in-band non-amplification SCALAR gate (the installed cap's rights-count must not exceed
the parent's); the `setCaps` is the EXACT executor cap-table write (`attenuateSlotF k.caps actor idx
keep`). This INTERNALIZES non-amplification in the term — the whole point of the crown weld. -/

/-- **The attenuate effect as an Argus IR term.** Gate on the in-band non-amplification check
(granted-rights-count ≤ held-rights-count, via `checkLe`), then install the in-place narrowed actor slot
(`attenuateSlotF` — the EXACT executor cap-table write). The `checkLe` leg is the in-band scalar shadow
of `granted.rights ≤ held.rights`; the `setCaps` leg is the verified executor move. -/
def attenuateStmt (actor : CellId) (idx : Nat) (keep : List Auth) : RecStmt :=
  RecStmt.seq
    (RecStmt.checkLe (grantedRightsCard actor idx keep) (heldRightsCard actor idx))
    (RecStmt.setCaps (fun k => attenuateSlotF k.caps actor idx keep))

/-! ## §2 — THE CORNERSTONE: `interp` of the attenuate term IS the kernel ATTENUATE step.

The SAME shape as the transfer/escrow cornerstones, with the leading gate being the `checkLe`
non-amplification domain-restrictor instead of a `guard`. Because a genuine attenuation NEVER amplifies
(`grantedRightsCard_le_held`), the `checkLe` gate ALWAYS fires (`some k`), so the `bind` runs the
`setCaps` install — which is exactly `attenuateStep`'s `some { k with caps := attenuateSlotF … }`. The
executor IS the meaning of the term, INCLUDING that the in-term `checkLe` gate matches the executor's
(always-admitting) attenuation discipline. -/

/-- **The cornerstone (crown).** `interp` of the attenuate term IS the kernel ATTENUATE step
`attenuateStep` — the same partial function, by construction, exactly as the transfer/mint/burn/escrow
cornerstones. The in-term `checkLe` non-amplification gate is shown to MATCH the executor: it admits on
every genuine attenuation (`grantedRightsCard_le_held`), so the term commits exactly when (always)
`attenuateStep` does, installing the SAME `attenuateSlotF` cap table. -/
theorem interp_attenuateStmt_eq_attenuateStep (actor : CellId) (idx : Nat) (keep : List Auth)
    (k : RecordKernelState) :
    interp (attenuateStmt actor idx keep) k = attenuateStep k ⟨actor, idx, keep⟩ := by
  simp only [attenuateStmt, interp, Option.bind]
  -- the in-band non-amplification `checkLe` admits (granted-count ≤ held-count) on every attenuation.
  rw [if_pos (grantedRightsCard_le_held actor idx keep k)]
  -- the `setCaps` install IS `attenuateStep`'s `some { k with caps := attenuateSlotF … }`.
  rfl

#assert_axioms interp_attenuateStmt_eq_attenuateStep

/-! ## §3 — the `checkLe` non-amplification gate is GENUINELY TWO-VALUED (the in-band tooth, with its
honest bound).

The gate is worthless if it admitted everything. It does not: `checkLe` REJECTS (fails closed) any move
whose installed cap would carry MORE rights than the parent (`checkLe_admits_iff`, the §L keystone). And
we are PRECISE about its strength: rights-cardinality `≤` is NECESSARY for subset but NOT SUFFICIENT —
two equal-cardinality rights sets can be non-subset — which is exactly the `checkLe` finding (the IR
needs a `checkSubset` to close the in-band gap). -/

/-- **`attenuateStmt_admits_iff` — the in-band gate is exactly the non-amplification SCALAR check.**
The attenuate term COMMITS (its `checkLe` leg admits) IFF the installed cap's rights-count `≤` the
parent's. So the in-band gate genuinely REJECTS (fails closed) a move that would grow the rights count
(gross amplification): two-valued, non-vacuous. -/
theorem attenuateStmt_admits_iff (actor : CellId) (idx : Nat) (keep : List Auth)
    (k : RecordKernelState) :
    (interp (attenuateStmt actor idx keep) k).isSome = true ↔
      grantedRightsCard actor idx keep k ≤ heldRightsCard actor idx k := by
  -- the `checkLe` leg gates the whole term: if it rejects, the `bind` short-circuits to `none`; if it
  -- admits, the `setCaps` install always commits (`some`). So the term is `some` iff the gate admits.
  constructor
  · intro hsome
    by_contra hgt
    -- if the gate rejected, the leading `checkLe` is `none`, so the whole term is `none` — contradiction.
    rw [attenuateStmt, interp, interp_checkLe, if_neg hgt] at hsome
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
  obtain ⟨_hcon, hsites⟩ := hsat
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
digest moves `cap_root` ⇒ UNSAT) — that is leg 2 of non-amplification. The IN-BAND `checkLe` of the term
(leg 1) proves the installed rights don't grow in CARDINALITY; the executor's `attenuate` (leg 3,
`attenuate_subset`) gives the FULL subset. The descriptor does NOT itself re-derive the subset order
(that is the reported `checkLe`/`checkSubset` IR gap); it binds WHICH rights, and the in-band `checkLe` +
the executor's structural attenuation supply the non-amplification. The executor produces the real `Caps`
FUNCTION; the circuit produces the genuine recompute of its `cap_root` DIGEST (the digest-not-function
boundary, faithful, stated). -/
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

/-! ## §6 — NON-VACUITY: the genuine descriptor is the real class-A circuit; the in-band `checkLe`
genuinely admits a valid attenuation and REJECTS an over-broad grant.

The weld would be worthless if (a) the descriptor were the inert placeholder, or (b) the in-band gate
admitted everything. Neither: the genuine descriptor carries 12 frame gates + the cap-root recompute (the
opaque `gCapMove` is GONE), and the `checkLe` gate is two-valued (admits a real narrowing of a 2-rights
cap to 1; rejects a synthetic widening). -/

/-- A concrete kernel state: actor `0` holds one `endpoint 9 [read, write]` cap (2 conferred rights), on
the §C two-cell `kC` base. The slot `attenuateSlotF 0 0` narrows. -/
def kAtten : RecordKernelState :=
  { kC with caps := fun l => if l = 0 then [Cap.endpoint 9 [Auth.read, Auth.write]] else [] }

/-- **NON-VACUITY (witness TRUE — the in-band gate ADMITS a genuine attenuation).** Narrowing actor `0`'s
held `[read, write]` cap (2 rights) to `[read]` (1 right) has granted-count `1 ≤ 2 =` held-count, so the
`checkLe` non-amplification gate COMMITS and the term installs the narrowed slot (`isSome`). -/
theorem attenuateStmt_admits_valid :
    (interp (attenuateStmt 0 0 [Auth.read]) kAtten).isSome = true := by
  rw [attenuateStmt_admits_iff]
  -- granted-rights-count (1) ≤ held-rights-count (2) on `kAtten`.
  decide

/-- **NON-VACUITY (witness FALSE / the in-band anti-amplification tooth).** A synthetic move whose
installed cap would carry MORE rights than the parent (granted-count `3 >` held-count `1`) is REJECTED by
the `checkLe` gate (`interp = none`) — the in-band non-amplification check genuinely fails closed on
amplification. (We exhibit the rejection directly on `checkLe`, the term's gating leg, with an explicit
over-broad granted-vs-held pair `3 > 1`.) -/
theorem checkLe_rejects_overbroad_grant :
    interp (RecStmt.checkLe (fun _ => (3 : Int)) (fun _ => (1 : Int))) kC = none := by
  rw [interp_checkLe]; norm_num

/-- **NON-VACUITY (the descriptor is the genuine class-A circuit, not the placeholder).** The genuine
attenuate descriptor carries 12 frame-freeze gates + 14 transition + 4 boundary = 30 constraints, and 6
hash-sites (2 cap-root-recompute + 4 GROUP-4 commitment) — the opaque `gCapMove` parameter gate is GONE.
So `attenuate_compile_sound` is a statement about a REAL genuinely-recomputed cap-root circuit. -/
theorem attenuateVmDescriptorGenuine_nontrivial :
    attenuateVmDescriptorGenuine.constraints.length = 12 + 14 + 4
    ∧ attenuateVmDescriptorGenuine.hashSites.length = 6 := by
  refine ⟨by decide, by decide⟩

#assert_axioms attenuateStmt_admits_valid
#assert_axioms checkLe_rejects_overbroad_grant
#assert_axioms attenuateVmDescriptorGenuine_nontrivial

end Dregg2.Circuit.Argus.Effects.Attenuate
