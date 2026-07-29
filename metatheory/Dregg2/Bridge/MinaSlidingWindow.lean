/-
# Dregg2.Bridge.MinaSlidingWindow — Samasika's sliding DENSITY WINDOW, in Lean.

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. It is pure `Nat`/`Bool` Lean.
The window update has two lives in Mina: an **in-circuit** one
(`Min_window_density.Checked.update_min_window_density`, `proof_of_stake.ml:1338-1438`, which the
blockchain SNARK proves for every block) and an **unchecked** one (`:1221-1335`) used by the node
and by `select`. What is authored here is the *unchecked* one — the decision procedure a light
client would run. It is NOT a `Builder` gadget and nothing here belongs in Rust. Were a lane to
want this IN-CIRCUIT on our side, that object is a Lean-authored `def`-generator plus forcing
lemmas (House Law #1); it does not exist, and this file does not pretend to be it.

**What a light client ends up trusting, precisely.** Mina already proves the window update inside
the blockchain SNARK, so a client that verifies the Pickles proof inherits "this block's densities
were computed by *this rule* from its parent's". This file lets a client instead check the rule
*directly*, from the parent and child consensus states, with no proof — which is what our
`LightClientMina` anchored-segment verifier is positioned to do. Either way the client must still
hold the parent state; the window is a fold, not a self-certifying value.

## What this is, and what the sibling already has

`Dregg2.Bridge.MinaChainSelection` (sibling lane) authors `select` / `isShortRange` and, for them,
the DENSITY HALF of the update — `projectedWindow` and `updateMinWindowDensity` — because
`select` calls the update with `~incr_window:false` and needs only the scalar. Its own doc-comment
says the "next window" half "is block production and is not part of chain selection".

This file is that other half, and the mechanism underneath both: the **next window**
(`~incr_window:true`), the genesis window, the per-block step, the chain replay, the invariants,
and a DIFFERENTIAL against real Mina devnet blocks. It **imports and reuses** the sibling's
`Constants` / `globalSubWindow` / `relativeSubWindow` / `projectedWindow` rather than minting a
second copy of them: two shapes that agree today are two shapes that disagree later.

## SOURCES — every line below is cited to a real implementation

Canonical (OCaml daemon), `~/dev/mina`:

| object | file:line |
|---|---|
| `Min_window_density.update_min_window_density` (unchecked) | `src/lib/consensus/proof_of_stake.ml:1221-1335` |
| the same, in-circuit | `src/lib/consensus/proof_of_stake.ml:1338-1438` |
| the OCaml's OWN reference implementation (test-only) | `src/lib/consensus/proof_of_stake.ml:1449-1486` |
| call site, block production (`~incr_window:true`) | `src/lib/consensus/proof_of_stake.ml:1999-2007` |
| genesis / `negative_one` window seed | `src/lib/consensus/proof_of_stake.ml:2085-2090` |
| strict slot increase, unchecked | `src/lib/consensus/proof_of_stake.ml:1976-1987` |
| strict slot increase, IN-CIRCUIT | `src/lib/consensus/proof_of_stake.ml:2201-2207` |
| `Global_sub_window.of_global_slot` / `.sub_window` | `src/lib/consensus/global_sub_window.ml:10-18` |
| `grace_period_end` | `src/lib/consensus/constants.ml:239-241` |

Second, independent rendering (openmina / `~/dev/mina-rust`): in-circuit
`crates/ledger/src/proofs/block.rs:1108-1235`; native block producer
`crates/node/src/block_producer/block_producer_reducer.rs:514-593`; sub-window arithmetic
`crates/core/src/consensus.rs:223-232`; genesis seed `crates/core/src/block/genesis.rs:202-208`.
Both renderings agree with the OCaml branch-for-branch, and this file agrees with both.

Written spec: `~/dev/mina/docs/specs/consensus/README.md` §5.4 (`:564-925`).

## CONSTANTS — real values, cited, never invented

Inherited from the sibling's `MinaChainSelection.mainnet`, which is
`~/dev/mina/src/config/mainnet.mlh:15-20`, byte-identical in `devnet.mlh:15-20`:
`slots_per_sub_window = 7` (`:18`), `sub_windows_per_window = 11` (`:19`),
`grace_period_slots = 2160` (`:20`), `slots_per_epoch = 7140` (`:17`), `k = 290` (`:15`),
`delta = 0` (`:16`); derived `slots_per_window = 77` (`constants.ml:227`) and
`grace_period_end = 2237` (`constants.ml:239-241`).

⚑ `sub_windows_per_window` is a CONSTRAINT constant (`genesis_constants.ml:91`), i.e. baked into
the circuit; the other four are protocol constants carried in the block
(`genesis_constants.ml:372-380`). That asymmetry is why `sub_window_densities` has a fixed length
of 11 while `slots_per_sub_window` is read from the state.
-/
import Dregg2.Bridge.MinaChainSelection
import Dregg2.Tactics

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.MinaSlidingWindow

open Dregg2.Bridge.MinaChainSelection

/-! ## §1 — The mechanism: the NEXT window.

`update_min_window_density` returns a PAIR. The sibling has the first component (the scalar
`min_window_density`). This is the second: the window the new block carries, obtained from the
projected window by resetting the block's own sub-window and counting the block into it. -/

/-- The `within_range` conjunct of `projected_window`, `proof_of_stake.ml:1293-1301`, named so it
can be reasoned about. §3 proves it is exactly the sibling's inlined copy. -/
def withinRange (prevRel nextRel i : Nat) : Bool :=
  let gtPrev := i > prevRel
  let ltNext := i < nextRel
  if prevRel < nextRel then gtPrev && ltNext else gtPrev || ltNext

/-- **`nextWindow`** — the second component of `update_min_window_density`
(`proof_of_stake.ml:1323-1333`). Take the projected window; at the block's own relative
sub-window, keep the running count if the block is in the SAME sub-window as its parent and reset
to zero otherwise, then add one for the block itself when `incrWindow`.

`incrWindow` is `true` at block production (`:2001`) and `false` when `select` evaluates a
*virtual* window (`:3052`) — which is why the sibling never needed this component. -/
def nextWindow (C : Constants) (incrWindow : Bool) (prevGlobalSlot nextGlobalSlot : Nat)
    (prevSub : List Nat) : List Nat :=
  let same := globalSubWindow C prevGlobalSlot = globalSubWindow C nextGlobalSlot
  let nextRel := relativeSubWindow C (globalSubWindow C nextGlobalSlot)
  mapIdxFrom 0
    (fun i d => if i = nextRel then (if same then d else 0) + (if incrWindow then 1 else 0) else d)
    (projectedWindow C prevGlobalSlot nextGlobalSlot prevSub)

/-! ## §2 — The window half of a `Consensus_state`, and the chain step. -/

/-- The three fields of `Consensus_state` the window mechanism reads and writes
(`proof_of_stake.ml:1743-1746`). `slot` is `curr_global_slot_since_hard_fork.slot_number` —
since the HARD FORK, not since genesis; `global_sub_window` divides that one
(`global_sub_window.ml:10-15`). -/
structure WindowState where
  /-- `curr_global_slot_since_hard_fork.slot_number`. -/
  slot : Nat
  /-- `min_window_density`. -/
  minWindowDensity : Nat
  /-- `sub_window_densities`, length `sub_windows_per_window`. -/
  subWindowDensities : List Nat
  deriving Repr, DecidableEq

/-- **One block.** The whole window mechanism as block production runs it
(`proof_of_stake.ml:1999-2013`): both components of `update_min_window_density`, with
`~incr_window:true`, and the new slot recorded. -/
def step (C : Constants) (s : WindowState) (nextSlot : Nat) : WindowState :=
  { slot := nextSlot
    minWindowDensity :=
      updateMinWindowDensity C s.slot nextSlot s.subWindowDensities s.minWindowDensity
    subWindowDensities := nextWindow C true s.slot nextSlot s.subWindowDensities }

/-- The density of the projected window — the quantity `min_window_density` is a running minimum
OF (`proof_of_stake.ml:1306-1308`). Order-insensitive, as the spec notes (`README.md:613`). -/
def currentWindowDensity (C : Constants) (prevGlobalSlot nextGlobalSlot : Nat)
    (prevSub : List Nat) : Nat :=
  (projectedWindow C prevGlobalSlot nextGlobalSlot prevSub).foldl (· + ·) 0

/-- **The genesis window**, `negative_one` (`proof_of_stake.ml:2085-2090`): `min_window_density`
starts at the MAXIMUM (`slots_per_window = 77`), and the densities are `0` followed by
`sub_windows_per_window - 1` copies of `slots_per_sub_window`. Spec §5.4.10-5.4.11
(`README.md:846-889`) derives the same seed from imaginary pre-genesis sub-windows.

⚑ Note the genesis densities sum to `70`, not `77`: index 0 is the genesis block's own sub-window
and is seeded EMPTY. The `77` in `min_window_density` is `negative_one`'s value, not this sum. -/
def genesisWindow (C : Constants) : WindowState :=
  { slot := 0
    minWindowDensity := C.slotsPerWindow
    subWindowDensities := 0 :: List.replicate (C.subWindowsPerWindow - 1) C.slotsPerSubWindow }

/-- Replay a chain: fold `step` over the successive blocks' global slots. -/
def replay (C : Constants) (s : WindowState) : List Nat → WindowState
  | [] => s
  | t :: ts => replay C (step C s t) ts

/-! ## §3 — THE SLIDE LAW.

The one place a plausible implementation goes subtly wrong is the ring bookkeeping: which entries
of an 11-slot ring still belong to the window after advancing `diff` sub-windows. The OCaml does
it with two comparisons and a wrap (`gt_prev_sub_window`, `lt_next_sub_window`, and a
`prev < next` test that flips `&&` to `||`), and nothing in the source says what that computes.

This says what it computes, and proves it.

Index `i` of the ring carries the density of the sub-window `prevGsw - age i`, where
`age i = (prevRel + W - i) % W` is how many sub-windows back from the parent's own sub-window
index `i` sits. After advancing to `nextGsw = prevGsw + diff`, the projected window covers
`[nextGsw - W, nextGsw)`, so index `i` survives exactly when `prevGsw - age i ≥ nextGsw - W`,
i.e. when `age i + diff ≤ W`. -/

/-- How many sub-windows back from the parent's own sub-window the ring index `i` sits. -/
def age (W prevRel i : Nat) : Nat := (prevRel + W - i) % W

/-- **THE SLIDE LAW**, at the deployed `sub_windows_per_window = 11`. The ring predicate zeroes an
entry exactly when that entry's sub-window has fallen OUT of the projected window. Checked
exhaustively over every reachable `(prevRel, shift, index)` — all 11 ring positions, all 11
possible non-zero shifts, all 11 indices.

This is the theorem that a mis-transcribed `>` / `≥`, a wrong modulus, or an off-by-one in the
wrap would break, and it is the reason the two comparisons are correct rather than merely
plausible. -/
theorem withinRange_iff_out_of_window :
    ∀ prevRel < 11, ∀ d < 11, ∀ i < 11,
      withinRange prevRel ((prevRel + (d + 1)) % 11) i
        = decide (11 < age 11 prevRel i + (d + 1)) := by decide

/-- The count consequence: advancing `diff` sub-windows retains exactly `W - diff + 1` entries —
the `W - diff` that were already in the window plus the one the new block starts. -/
theorem projected_retains_count :
    ∀ d < 11,
      ((List.range 11).filter
        (fun i => !withinRange 0 ((0 + (d + 1)) % 11) i)).length = 11 - (d + 1) + 1 := by decide

/-- `withinRange` really is the sibling's inlined predicate: `projectedWindow` is `mapIdxFrom` of
it. Definitional, so this is `rfl` — but it is stated so §3 is about the deployed code and not
about a lookalike. -/
theorem projectedWindow_eq_withinRange (C : Constants) (p n : Nat) (ds : List Nat) :
    projectedWindow C p n ds =
      mapIdxFrom 0
        (fun i d =>
          if globalSubWindow C p = globalSubWindow C n then d
          else if globalSubWindow C p + C.subWindowsPerWindow ≥ globalSubWindow C n
                  && !withinRange (relativeSubWindow C (globalSubWindow C p))
                       (relativeSubWindow C (globalSubWindow C n)) i
               then d else 0)
        ds := rfl

/-! ## §4 — Structural facts. -/

theorem mapIdxFrom_length (f : Nat → Nat → Nat) :
    ∀ (l : List Nat) (i : Nat), (mapIdxFrom i f l).length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih => intro i; simp [mapIdxFrom, ih]

/-- **The array length never drifts.** `sub_window_densities` is hashed into the state
(`proof_of_stake.ml:1856-1859`) and consumed positionally by the in-circuit update; a length
change is a consensus break, not a cosmetic one. -/
theorem mapIdxFrom_getElem (f : Nat → Nat → Nat) :
    ∀ (l : List Nat) (b i : Nat) (h : i < (mapIdxFrom b f l).length),
      (mapIdxFrom b f l)[i] = f (b + i) (l[i]'(by rwa [mapIdxFrom_length] at h)) := by
  intro l
  induction l with
  | nil => intro _ i h; simp [mapIdxFrom] at h
  | cons x xs ih =>
      intro b i h
      cases i with
      | zero => simp [mapIdxFrom]
      | succ j =>
          have hj : j < (mapIdxFrom (b + 1) f xs).length := by
            simp only [mapIdxFrom, List.length_cons, mapIdxFrom_length] at h ⊢
            omega
          simp only [mapIdxFrom, List.getElem_cons_succ]
          rw [ih (b + 1) j hj]
          congr 1
          omega

theorem projectedWindow_length (C : Constants) (p n : Nat) (ds : List Nat) :
    (projectedWindow C p n ds).length = ds.length := by
  simp [projectedWindow, mapIdxFrom_length]

theorem nextWindow_length (C : Constants) (b : Bool) (p n : Nat) (ds : List Nat) :
    (nextWindow C b p n ds).length = ds.length := by
  simp [nextWindow, mapIdxFrom_length, projectedWindow_length]

theorem step_length (C : Constants) (s : WindowState) (t : Nat) :
    (step C s t).subWindowDensities.length = s.subWindowDensities.length := by
  simp [step, nextWindow_length]

theorem replay_length (C : Constants) :
    ∀ (ts : List Nat) (s : WindowState),
      (replay C s ts).subWindowDensities.length = s.subWindowDensities.length := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t rest ih => intro s; simp [replay, ih, step_length]

/-- **`min_window_density` is non-increasing along a chain** — spec §5.4.6 (`README.md:691`)
states this as the defining property, and the long-range fork rule is built on it. Both branches
of the update give it: the guarded branch keeps the previous value, the other takes a `min` with
it. -/
theorem updateMinWindowDensity_le (C : Constants) (p n : Nat) (ds : List Nat) (m : Nat) :
    updateMinWindowDensity C p n ds m ≤ m := by
  simp only [updateMinWindowDensity]
  split
  · exact Nat.le_refl m
  · exact Nat.min_le_right _ m

theorem step_minWindowDensity_le (C : Constants) (s : WindowState) (t : Nat) :
    (step C s t).minWindowDensity ≤ s.minWindowDensity :=
  updateMinWindowDensity_le _ _ _ _ _

theorem replay_minWindowDensity_le (C : Constants) :
    ∀ (ts : List Nat) (s : WindowState),
      (replay C s ts).minWindowDensity ≤ s.minWindowDensity := by
  intro ts
  induction ts with
  | nil => intro _; exact Nat.le_refl _
  | cons t rest ih =>
      intro s
      exact Nat.le_trans (ih (step C s t)) (step_minWindowDensity_le C s t)

/-- **The grace period really is a hold, not a discount.** Before `grace_period_end = 2237` the
running minimum is not touched at all, whatever the density is. This is what stops the sparse
first hours of a chain from permanently poisoning `min_window_density` — and it is the branch
openmina's `relative_min_window_density` gets wrong by hardcoding `1440` (`consensus.rs:15`). -/
theorem updateMinWindowDensity_in_grace (C : Constants) (p n : Nat) (ds : List Nat) (m : Nat)
    (h : n < C.gracePeriodEnd) : updateMinWindowDensity C p n ds m = m := by
  simp [updateMinWindowDensity, h]

/-- Within one sub-window the minimum is likewise untouched, at any slot. -/
theorem updateMinWindowDensity_same_subwindow (C : Constants) (p n : Nat) (ds : List Nat)
    (m : Nat) (h : globalSubWindow C p = globalSubWindow C n) :
    updateMinWindowDensity C p n ds m = m := by
  simp [updateMinWindowDensity, h]

/-! ## §5 — The density bound, and the precondition it actually needs.

The invariant one expects is `d[i] ≤ slots_per_sub_window` for every entry: a sub-window holds
`slots_per_sub_window` slots and at most one block per slot.

**It is NOT an invariant of the update function.** `step` alone will happily produce `8` on
mainnet constants — see §7. What preserves it is `step` COMPOSED WITH the strict slot increase
that block validity enforces (`proof_of_stake.ml:1976-1987` unchecked, and as a circuit constraint
at `:2201-2207`: `Boolean.Assert.any [global_slot_increased; is_genesis]`). Stating the bound
without that hypothesis would be stating something false.

The invariant that IS preserved is sharper, and it is what makes the induction go through: the
block's own sub-window can only have accumulated as many blocks as there are slots so far within
it. -/

/-- The preserved invariant: every entry is at most `slots_per_sub_window`, and the entry for the
state's OWN sub-window is at most one more than the number of slots elapsed within it. -/
def WindowOk (C : Constants) (s : WindowState) : Prop :=
  ∀ i, (h : i < s.subWindowDensities.length) →
    s.subWindowDensities[i] ≤
      (if i = relativeSubWindow C (globalSubWindow C s.slot)
       then s.slot % C.slotsPerSubWindow + 1
       else C.slotsPerSubWindow)

/-- `keep-or-zero` never increases a value, whatever the two guards decide. -/
theorem keep_or_zero_le (c1 c2 : Prop) [Decidable c1] [Decidable c2] (x : Nat) :
    (if c1 then x else if c2 then x else 0) ≤ x := by
  by_cases h1 : c1
  · simp [h1]
  · by_cases h2 : c2 <;> simp [h1, h2]

/-- The projected window never increases an entry: each is kept or zeroed. -/
theorem projectedWindow_le (C : Constants) (p n : Nat) (ds : List Nat) (i : Nat)
    (h : i < (projectedWindow C p n ds).length) :
    (projectedWindow C p n ds)[i] ≤ ds[i]'(by rwa [projectedWindow_length] at h) := by
  simp only [projectedWindow] at h ⊢
  rw [mapIdxFrom_getElem _ ds 0 i h]
  exact keep_or_zero_le _ _ _

theorem step_getElem (C : Constants) (s : WindowState) (t i : Nat)
    (h : i < (step C s t).subWindowDensities.length) :
    (step C s t).subWindowDensities[i]
      = (if i = relativeSubWindow C (globalSubWindow C t) then
           (if globalSubWindow C s.slot = globalSubWindow C t
            then (projectedWindow C s.slot t s.subWindowDensities)[i]'(by
                    simpa [step, nextWindow, mapIdxFrom_length] using h)
            else 0) + 1
         else (projectedWindow C s.slot t s.subWindowDensities)[i]'(by
                simpa [step, nextWindow, mapIdxFrom_length] using h)) := by
  show (nextWindow C true s.slot t s.subWindowDensities)[i]'(by simpa [step] using h) = _
  simp only [nextWindow]
  rw [mapIdxFrom_getElem _ _ 0 i (by simpa [step, nextWindow] using h)]
  split <;> simp_all

/-- **The density bound is preserved by a VALID block, and only by a valid block.** With the
strict slot increase that block validity enforces, `WindowOk` is an invariant of `step`. -/
theorem WindowOk_step (C : Constants) (s : WindowState) (t : Nat)
    (hsps : 0 < C.slotsPerSubWindow) (hlt : s.slot < t) (h : WindowOk C s) :
    WindowOk C (step C s t) := by
  intro i hi
  have hlen : (step C s t).subWindowDensities.length = s.subWindowDensities.length :=
    step_length C s t
  have hi' : i < s.subWindowDensities.length := by rwa [hlen] at hi
  have hprev := h i hi'
  have hpl : i < (projectedWindow C s.slot t s.subWindowDensities).length := by
    rwa [projectedWindow_length]
  have hproj := projectedWindow_le C s.slot t s.subWindowDensities i hpl
  have hslot : (step C s t).slot = t := rfl
  rw [step_getElem C s t i hi, hslot]
  by_cases hown : i = relativeSubWindow C (globalSubWindow C t)
  · rw [if_pos hown, if_pos hown]
    by_cases hsame : globalSubWindow C s.slot = globalSubWindow C t
    · rw [if_pos hsame]
      have hri : i = relativeSubWindow C (globalSubWindow C s.slot) := by rw [hown, hsame]
      rw [if_pos hri] at hprev
      have h1 : s.slot / C.slotsPerSubWindow = t / C.slotsPerSubWindow := hsame
      have hs := Nat.div_add_mod s.slot C.slotsPerSubWindow
      have ht := Nat.div_add_mod t C.slotsPerSubWindow
      rw [h1] at hs
      omega
    · rw [if_neg hsame]; omega
  · rw [if_neg hown, if_neg hown]
    refine Nat.le_trans hproj ?_
    by_cases hir2 : i = relativeSubWindow C (globalSubWindow C s.slot)
    · rw [if_pos hir2] at hprev
      have : s.slot % C.slotsPerSubWindow < C.slotsPerSubWindow := Nat.mod_lt _ hsps
      omega
    · rw [if_neg hir2] at hprev; exact hprev

/-- **The bound one wanted**, as a consequence. -/
theorem WindowOk_bound (C : Constants) (s : WindowState) (hsps : 0 < C.slotsPerSubWindow)
    (h : WindowOk C s) (i : Nat) (hi : i < s.subWindowDensities.length) :
    s.subWindowDensities[i] ≤ C.slotsPerSubWindow := by
  have hb := h i hi
  have hm : s.slot % C.slotsPerSubWindow < C.slotsPerSubWindow := Nat.mod_lt _ hsps
  split at hb <;> omega

/-- The genesis window satisfies the invariant, so a whole-chain replay from genesis does. -/
theorem WindowOk_genesis (C : Constants) (hsps : 0 < C.slotsPerSubWindow) :
    WindowOk C (genesisWindow C) := by
  intro i hi
  have hrel : relativeSubWindow C (globalSubWindow C (genesisWindow C).slot) = 0 := by
    simp [genesisWindow, globalSubWindow, relativeSubWindow]
  cases i with
  | zero => rw [hrel]; simp [genesisWindow]
  | succ j =>
      rw [hrel]
      have : (genesisWindow C).subWindowDensities[j + 1] = C.slotsPerSubWindow := by
        simp only [genesisWindow, List.getElem_cons_succ]
        simp [List.getElem_replicate]
      simp [this]

/-- "these blocks' slots strictly increase, starting after `s`" — the block-validity condition
Mina enforces (`proof_of_stake.ml:1976-1987`, and in-circuit at `:2201-2207`). Written out rather
than reached for in a library so the hypothesis is visibly the one the OCaml checks. -/
def SlotsIncreasing : Nat → List Nat → Prop
  | _, [] => True
  | s, t :: ts => s < t ∧ SlotsIncreasing t ts

theorem WindowOk_replay (C : Constants) (hsps : 0 < C.slotsPerSubWindow) :
    ∀ (ts : List Nat) (s : WindowState), WindowOk C s →
      SlotsIncreasing s.slot ts → WindowOk C (replay C s ts) := by
  intro ts
  induction ts with
  | nil => intro s h _; exact h
  | cons t rest ih =>
      intro s h hch
      obtain ⟨h1, h2⟩ := hch
      have hstep : (step C s t).slot = t := rfl
      exact ih (step C s t) (WindowOk_step C s t hsps h1 h) (by rw [hstep]; exact h2)

/-! ## §6 — DIFFERENTIAL against real Mina devnet blocks.

291 consecutive canonical devnet blocks, heights 539482..539772 (epoch 56, global slots
402849..403360 since the hard fork), pulled 2026-07-29. Each triple is a block's OWN reported
`(curr_global_slot_since_hard_fork.slot_number, min_window_density, sub_window_densities)`.

Provenance and the extractor are IN THIS TREE:
`metatheory/fixtures/samasika-density/fetch_devnet_window.py` and `devnet_window_run.json`.
Canonical order and state hashes come from `api.minascan.io/node/devnet/v1/graphql` (`bestChain`,
read-only, no keys); the consensus states come verbatim from Mina's public precomputed-block
archive `gs://mina_network_block_data`.

⚑ **The daemon GraphQL cannot answer this question.** Introspected 2026-07-29, the
`ConsensusState` type exposes `minWindowDensity` but NOT `subWindowDensities` (16 fields, listed
in the extractor's docstring; the resolver is `proof_of_stake.ml:2440-2536`). A light client
speaking only GraphQL therefore cannot even seed a window replay — it must read the block body. -/

/-- `(slot_number, min_window_density, sub_window_densities)` for each block, parent first. -/
def devnetRun : List (Nat × Nat × List Nat) :=
  -- height 539482 .. 539772, slots 402849 .. 403360, epoch-56 devnet, pulled 2026-07-29.
  [
  (402849, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 5, 1]),
  (402852, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 1, 1]),
  (402854, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 2, 1]),
  (402856, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 3, 1]),
  (402858, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 3, 1]),
  (402861, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402865, 3, [1, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402866, 3, [2, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402867, 3, [3, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402868, 3, [4, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402870, 3, [5, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402872, 3, [5, 1, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402874, 3, [5, 2, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402875, 3, [5, 3, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402876, 3, [5, 4, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402877, 3, [5, 5, 5, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402880, 3, [5, 5, 1, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402882, 3, [5, 5, 2, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402883, 3, [5, 5, 3, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402884, 3, [5, 5, 4, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402885, 3, [5, 5, 4, 1, 4, 4, 3, 3, 6, 3, 2]),
  (402889, 3, [5, 5, 4, 2, 4, 4, 3, 3, 6, 3, 2]),
  (402890, 3, [5, 5, 4, 3, 4, 4, 3, 3, 6, 3, 2]),
  (402892, 3, [5, 5, 4, 3, 1, 4, 3, 3, 6, 3, 2]),
  (402893, 3, [5, 5, 4, 3, 2, 4, 3, 3, 6, 3, 2]),
  (402894, 3, [5, 5, 4, 3, 3, 4, 3, 3, 6, 3, 2]),
  (402897, 3, [5, 5, 4, 3, 4, 4, 3, 3, 6, 3, 2]),
  (402902, 3, [5, 5, 4, 3, 4, 1, 3, 3, 6, 3, 2]),
  (402905, 3, [5, 5, 4, 3, 4, 2, 3, 3, 6, 3, 2]),
  (402906, 3, [5, 5, 4, 3, 4, 2, 1, 3, 6, 3, 2]),
  (402908, 3, [5, 5, 4, 3, 4, 2, 2, 3, 6, 3, 2]),
  (402910, 3, [5, 5, 4, 3, 4, 2, 3, 3, 6, 3, 2]),
  (402911, 3, [5, 5, 4, 3, 4, 2, 4, 3, 6, 3, 2]),
  (402912, 3, [5, 5, 4, 3, 4, 2, 5, 3, 6, 3, 2]),
  (402917, 3, [5, 5, 4, 3, 4, 2, 5, 1, 6, 3, 2]),
  (402918, 3, [5, 5, 4, 3, 4, 2, 5, 2, 6, 3, 2]),
  (402923, 3, [5, 5, 4, 3, 4, 2, 5, 2, 1, 3, 2]),
  (402924, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 3, 2]),
  (402927, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 1, 2]),
  (402928, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 2, 2]),
  (402929, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 3, 2]),
  (402930, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 4, 2]),
  (402931, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 2]),
  (402934, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 1]),
  (402935, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 2]),
  (402936, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 3]),
  (402937, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 4]),
  (402938, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 5]),
  (402939, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402942, 3, [1, 5, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402943, 3, [2, 5, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402944, 3, [3, 5, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402945, 3, [4, 5, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402946, 3, [5, 5, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402953, 3, [5, 1, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402954, 3, [5, 2, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402955, 3, [5, 2, 1, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402956, 3, [5, 2, 2, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402957, 3, [5, 2, 3, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402960, 3, [5, 2, 4, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402961, 3, [5, 2, 5, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402963, 3, [5, 2, 5, 1, 4, 2, 5, 2, 2, 5, 6]),
  (402964, 3, [5, 2, 5, 2, 4, 2, 5, 2, 2, 5, 6]),
  (402966, 3, [5, 2, 5, 3, 4, 2, 5, 2, 2, 5, 6]),
  (402967, 3, [5, 2, 5, 4, 4, 2, 5, 2, 2, 5, 6]),
  (402968, 3, [5, 2, 5, 5, 4, 2, 5, 2, 2, 5, 6]),
  (402969, 3, [5, 2, 5, 5, 1, 2, 5, 2, 2, 5, 6]),
  (402971, 3, [5, 2, 5, 5, 2, 2, 5, 2, 2, 5, 6]),
  (402974, 3, [5, 2, 5, 5, 3, 2, 5, 2, 2, 5, 6]),
  (402975, 3, [5, 2, 5, 5, 4, 2, 5, 2, 2, 5, 6]),
  (402976, 3, [5, 2, 5, 5, 4, 1, 5, 2, 2, 5, 6]),
  (402977, 3, [5, 2, 5, 5, 4, 2, 5, 2, 2, 5, 6]),
  (402978, 3, [5, 2, 5, 5, 4, 3, 5, 2, 2, 5, 6]),
  (402981, 3, [5, 2, 5, 5, 4, 4, 5, 2, 2, 5, 6]),
  (402985, 3, [5, 2, 5, 5, 4, 4, 1, 2, 2, 5, 6]),
  (402986, 3, [5, 2, 5, 5, 4, 4, 2, 2, 2, 5, 6]),
  (402988, 3, [5, 2, 5, 5, 4, 4, 3, 2, 2, 5, 6]),
  (402989, 3, [5, 2, 5, 5, 4, 4, 4, 2, 2, 5, 6]),
  (402991, 3, [5, 2, 5, 5, 4, 4, 4, 1, 2, 5, 6]),
  (402992, 3, [5, 2, 5, 5, 4, 4, 4, 2, 2, 5, 6]),
  (402993, 3, [5, 2, 5, 5, 4, 4, 4, 3, 2, 5, 6]),
  (402994, 3, [5, 2, 5, 5, 4, 4, 4, 4, 2, 5, 6]),
  (402999, 3, [5, 2, 5, 5, 4, 4, 4, 4, 1, 5, 6]),
  (403002, 3, [5, 2, 5, 5, 4, 4, 4, 4, 2, 5, 6]),
  (403003, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 5, 6]),
  (403006, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 1, 6]),
  (403008, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 2, 6]),
  (403010, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 3, 6]),
  (403011, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 3, 1]),
  (403014, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 3, 2]),
  (403015, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403018, 3, [1, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403019, 3, [2, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403020, 3, [3, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403021, 3, [4, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403022, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403025, 3, [5, 1, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403026, 3, [5, 2, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403027, 3, [5, 3, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403028, 3, [5, 4, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403030, 3, [5, 5, 5, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403033, 3, [5, 5, 1, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403035, 3, [5, 5, 2, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403036, 3, [5, 5, 3, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403038, 3, [5, 5, 4, 5, 4, 4, 4, 4, 3, 3, 3]),
  (403039, 3, [5, 5, 4, 1, 4, 4, 4, 4, 3, 3, 3]),
  (403040, 3, [5, 5, 4, 2, 4, 4, 4, 4, 3, 3, 3]),
  (403041, 3, [5, 5, 4, 3, 4, 4, 4, 4, 3, 3, 3]),
  (403044, 3, [5, 5, 4, 4, 4, 4, 4, 4, 3, 3, 3]),
  (403046, 3, [5, 5, 4, 4, 1, 4, 4, 4, 3, 3, 3]),
  (403047, 3, [5, 5, 4, 4, 2, 4, 4, 4, 3, 3, 3]),
  (403049, 3, [5, 5, 4, 4, 3, 4, 4, 4, 3, 3, 3]),
  (403051, 3, [5, 5, 4, 4, 4, 4, 4, 4, 3, 3, 3]),
  (403052, 3, [5, 5, 4, 4, 5, 4, 4, 4, 3, 3, 3]),
  (403054, 3, [5, 5, 4, 4, 5, 1, 4, 4, 3, 3, 3]),
  (403056, 3, [5, 5, 4, 4, 5, 2, 4, 4, 3, 3, 3]),
  (403059, 3, [5, 5, 4, 4, 5, 3, 4, 4, 3, 3, 3]),
  (403060, 3, [5, 5, 4, 4, 5, 3, 1, 4, 3, 3, 3]),
  (403061, 3, [5, 5, 4, 4, 5, 3, 2, 4, 3, 3, 3]),
  (403062, 3, [5, 5, 4, 4, 5, 3, 3, 4, 3, 3, 3]),
  (403065, 3, [5, 5, 4, 4, 5, 3, 4, 4, 3, 3, 3]),
  (403066, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 3, 3]),
  (403068, 3, [5, 5, 4, 4, 5, 3, 5, 1, 3, 3, 3]),
  (403069, 3, [5, 5, 4, 4, 5, 3, 5, 2, 3, 3, 3]),
  (403070, 3, [5, 5, 4, 4, 5, 3, 5, 3, 3, 3, 3]),
  (403071, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 3, 3]),
  (403074, 3, [5, 5, 4, 4, 5, 3, 5, 4, 1, 3, 3]),
  (403079, 3, [5, 5, 4, 4, 5, 3, 5, 4, 2, 3, 3]),
  (403080, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 3, 3]),
  (403084, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 1, 3]),
  (403085, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 2, 3]),
  (403088, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 2, 1]),
  (403089, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 2, 2]),
  (403091, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 2, 3]),
  (403094, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403097, 3, [1, 5, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403098, 3, [2, 5, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403099, 3, [3, 5, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403100, 3, [4, 5, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403101, 3, [5, 5, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403102, 3, [5, 1, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403105, 3, [5, 2, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403108, 3, [5, 3, 4, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403110, 3, [5, 3, 1, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403111, 3, [5, 3, 2, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403114, 3, [5, 3, 3, 4, 5, 3, 5, 4, 3, 2, 4]),
  (403118, 3, [5, 3, 3, 1, 5, 3, 5, 4, 3, 2, 4]),
  (403119, 3, [5, 3, 3, 2, 5, 3, 5, 4, 3, 2, 4]),
  (403121, 3, [5, 3, 3, 3, 5, 3, 5, 4, 3, 2, 4]),
  (403124, 3, [5, 3, 3, 3, 1, 3, 5, 4, 3, 2, 4]),
  (403127, 3, [5, 3, 3, 3, 2, 3, 5, 4, 3, 2, 4]),
  (403128, 3, [5, 3, 3, 3, 3, 3, 5, 4, 3, 2, 4]),
  (403130, 3, [5, 3, 3, 3, 3, 1, 5, 4, 3, 2, 4]),
  (403132, 3, [5, 3, 3, 3, 3, 2, 5, 4, 3, 2, 4]),
  (403133, 3, [5, 3, 3, 3, 3, 3, 5, 4, 3, 2, 4]),
  (403135, 3, [5, 3, 3, 3, 3, 4, 5, 4, 3, 2, 4]),
  (403136, 3, [5, 3, 3, 3, 3, 5, 5, 4, 3, 2, 4]),
  (403138, 3, [5, 3, 3, 3, 3, 5, 1, 4, 3, 2, 4]),
  (403142, 3, [5, 3, 3, 3, 3, 5, 2, 4, 3, 2, 4]),
  (403143, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 2, 4]),
  (403144, 3, [5, 3, 3, 3, 3, 5, 3, 1, 3, 2, 4]),
  (403146, 3, [5, 3, 3, 3, 3, 5, 3, 2, 3, 2, 4]),
  (403147, 3, [5, 3, 3, 3, 3, 5, 3, 3, 3, 2, 4]),
  (403150, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 2, 4]),
  (403151, 3, [5, 3, 3, 3, 3, 5, 3, 4, 1, 2, 4]),
  (403152, 3, [5, 3, 3, 3, 3, 5, 3, 4, 2, 2, 4]),
  (403156, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 2, 4]),
  (403158, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 1, 4]),
  (403160, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 2, 4]),
  (403161, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 4]),
  (403165, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 1]),
  (403166, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 2]),
  (403168, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 3]),
  (403169, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 4]),
  (403170, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403173, 3, [1, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403174, 3, [2, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403175, 3, [3, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403177, 3, [4, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403178, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403180, 3, [5, 1, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403181, 3, [5, 2, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403183, 3, [5, 3, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403184, 3, [5, 4, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403187, 3, [5, 4, 1, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403191, 3, [5, 4, 2, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403192, 3, [5, 4, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403193, 3, [5, 4, 3, 1, 3, 5, 3, 4, 3, 3, 5]),
  (403194, 3, [5, 4, 3, 2, 3, 5, 3, 4, 3, 3, 5]),
  (403195, 3, [5, 4, 3, 3, 3, 5, 3, 4, 3, 3, 5]),
  (403197, 3, [5, 4, 3, 4, 3, 5, 3, 4, 3, 3, 5]),
  (403198, 3, [5, 4, 3, 5, 3, 5, 3, 4, 3, 3, 5]),
  (403199, 3, [5, 4, 3, 6, 3, 5, 3, 4, 3, 3, 5]),
  (403201, 3, [5, 4, 3, 6, 1, 5, 3, 4, 3, 3, 5]),
  (403202, 3, [5, 4, 3, 6, 2, 5, 3, 4, 3, 3, 5]),
  (403203, 3, [5, 4, 3, 6, 3, 5, 3, 4, 3, 3, 5]),
  (403204, 3, [5, 4, 3, 6, 4, 5, 3, 4, 3, 3, 5]),
  (403208, 3, [5, 4, 3, 6, 4, 1, 3, 4, 3, 3, 5]),
  (403211, 3, [5, 4, 3, 6, 4, 2, 3, 4, 3, 3, 5]),
  (403212, 3, [5, 4, 3, 6, 4, 3, 3, 4, 3, 3, 5]),
  (403213, 3, [5, 4, 3, 6, 4, 4, 3, 4, 3, 3, 5]),
  (403215, 3, [5, 4, 3, 6, 4, 4, 1, 4, 3, 3, 5]),
  (403216, 3, [5, 4, 3, 6, 4, 4, 2, 4, 3, 3, 5]),
  (403217, 3, [5, 4, 3, 6, 4, 4, 3, 4, 3, 3, 5]),
  (403218, 3, [5, 4, 3, 6, 4, 4, 4, 4, 3, 3, 5]),
  (403219, 3, [5, 4, 3, 6, 4, 4, 5, 4, 3, 3, 5]),
  (403220, 3, [5, 4, 3, 6, 4, 4, 6, 4, 3, 3, 5]),
  (403221, 3, [5, 4, 3, 6, 4, 4, 6, 1, 3, 3, 5]),
  (403222, 3, [5, 4, 3, 6, 4, 4, 6, 2, 3, 3, 5]),
  (403223, 3, [5, 4, 3, 6, 4, 4, 6, 3, 3, 3, 5]),
  (403224, 3, [5, 4, 3, 6, 4, 4, 6, 4, 3, 3, 5]),
  (403225, 3, [5, 4, 3, 6, 4, 4, 6, 5, 3, 3, 5]),
  (403226, 3, [5, 4, 3, 6, 4, 4, 6, 6, 3, 3, 5]),
  (403227, 3, [5, 4, 3, 6, 4, 4, 6, 7, 3, 3, 5]),
  (403228, 3, [5, 4, 3, 6, 4, 4, 6, 7, 1, 3, 5]),
  (403229, 3, [5, 4, 3, 6, 4, 4, 6, 7, 2, 3, 5]),
  (403231, 3, [5, 4, 3, 6, 4, 4, 6, 7, 3, 3, 5]),
  (403234, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 3, 5]),
  (403235, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 1, 5]),
  (403238, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 2, 5]),
  (403239, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 3, 5]),
  (403240, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 5]),
  (403242, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 1]),
  (403243, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 2]),
  (403245, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 3]),
  (403246, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 4]),
  (403247, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 5]),
  (403248, 3, [5, 4, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403249, 3, [1, 4, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403250, 3, [2, 4, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403255, 3, [3, 4, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403256, 3, [3, 1, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403257, 3, [3, 2, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403261, 3, [3, 3, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403262, 3, [3, 4, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403263, 3, [3, 4, 1, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403265, 3, [3, 4, 2, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403266, 3, [3, 4, 3, 6, 4, 4, 6, 7, 4, 4, 6]),
  (403271, 3, [3, 4, 3, 1, 4, 4, 6, 7, 4, 4, 6]),
  (403273, 3, [3, 4, 3, 2, 4, 4, 6, 7, 4, 4, 6]),
  (403274, 3, [3, 4, 3, 3, 4, 4, 6, 7, 4, 4, 6]),
  (403275, 3, [3, 4, 3, 4, 4, 4, 6, 7, 4, 4, 6]),
  (403279, 3, [3, 4, 3, 4, 1, 4, 6, 7, 4, 4, 6]),
  (403281, 3, [3, 4, 3, 4, 2, 4, 6, 7, 4, 4, 6]),
  (403284, 3, [3, 4, 3, 4, 2, 1, 6, 7, 4, 4, 6]),
  (403285, 3, [3, 4, 3, 4, 2, 2, 6, 7, 4, 4, 6]),
  (403286, 3, [3, 4, 3, 4, 2, 3, 6, 7, 4, 4, 6]),
  (403288, 3, [3, 4, 3, 4, 2, 4, 6, 7, 4, 4, 6]),
  (403289, 3, [3, 4, 3, 4, 2, 5, 6, 7, 4, 4, 6]),
  (403290, 3, [3, 4, 3, 4, 2, 6, 6, 7, 4, 4, 6]),
  (403292, 3, [3, 4, 3, 4, 2, 6, 1, 7, 4, 4, 6]),
  (403294, 3, [3, 4, 3, 4, 2, 6, 2, 7, 4, 4, 6]),
  (403295, 3, [3, 4, 3, 4, 2, 6, 3, 7, 4, 4, 6]),
  (403296, 3, [3, 4, 3, 4, 2, 6, 4, 7, 4, 4, 6]),
  (403299, 3, [3, 4, 3, 4, 2, 6, 4, 1, 4, 4, 6]),
  (403302, 3, [3, 4, 3, 4, 2, 6, 4, 2, 4, 4, 6]),
  (403304, 3, [3, 4, 3, 4, 2, 6, 4, 3, 4, 4, 6]),
  (403305, 3, [3, 4, 3, 4, 2, 6, 4, 3, 1, 4, 6]),
  (403309, 3, [3, 4, 3, 4, 2, 6, 4, 3, 2, 4, 6]),
  (403310, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 4, 6]),
  (403312, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 1, 6]),
  (403313, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 2, 6]),
  (403315, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 3, 6]),
  (403316, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 4, 6]),
  (403317, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 5, 6]),
  (403322, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 5, 1]),
  (403324, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403326, 3, [1, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403327, 3, [2, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403329, 3, [3, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403331, 3, [4, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403332, 3, [5, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403334, 3, [5, 1, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403336, 3, [5, 2, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403337, 3, [5, 3, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403338, 3, [5, 4, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403339, 3, [5, 5, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403340, 3, [5, 5, 1, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403341, 3, [5, 5, 2, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403342, 3, [5, 5, 3, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403343, 3, [5, 5, 4, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403345, 3, [5, 5, 5, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403347, 3, [5, 5, 5, 1, 2, 6, 4, 3, 3, 5, 2]),
  (403348, 3, [5, 5, 5, 2, 2, 6, 4, 3, 3, 5, 2]),
  (403349, 3, [5, 5, 5, 3, 2, 6, 4, 3, 3, 5, 2]),
  (403352, 3, [5, 5, 5, 4, 2, 6, 4, 3, 3, 5, 2]),
  (403353, 3, [5, 5, 5, 5, 2, 6, 4, 3, 3, 5, 2]),
  (403355, 3, [5, 5, 5, 5, 1, 6, 4, 3, 3, 5, 2]),
  (403356, 3, [5, 5, 5, 5, 2, 6, 4, 3, 3, 5, 2]),
  (403359, 3, [5, 5, 5, 5, 3, 6, 4, 3, 3, 5, 2]),
  (403360, 3, [5, 5, 5, 5, 4, 6, 4, 3, 3, 5, 2]) ]

/-- Replay driven ONLY by the slot sequence, seeded once from the FIRST block's reported state:
every later block's own reported `min_window_density` and `sub_window_densities` must come back
out. This is the strong form — a single seed, 290 real transitions, nothing else fed in. -/
def foldMatches (C : Constants) : WindowState → List (Nat × Nat × List Nat) → Bool
  | _, [] => true
  | s, (t, m, ds) :: rest =>
      let s' := step C s t
      s'.minWindowDensity == m && s'.subWindowDensities == ds && foldMatches C s' rest

/-- Seed from the head block's own reported state, then replay the tail. -/
def runMatches (C : Constants) : List (Nat × Nat × List Nat) → Bool
  | [] => true
  | (t, m, ds) :: rest =>
      foldMatches C { slot := t, minWindowDensity := m, subWindowDensities := ds } rest

/-- **THE DIFFERENTIAL.** The window mechanism authored above reproduces 290 consecutive real
Mina devnet blocks' own reported `min_window_density` and 11-entry `sub_window_densities`, from
one seed and the slot sequence alone. -/
theorem mina_window_replays_real_devnet : runMatches mainnet devnetRun = true := by decide

/-- The run is what it claims to be: 291 blocks, every density array 11 long. -/
theorem devnetRun_shape :
    devnetRun.length = 291 ∧ devnetRun.all (fun b => b.2.2.length == 11) = true := by decide

/-- The observed density bound is TIGHT on real data: some real sub-window holds all 7 slots,
so `WindowOk_bound`'s `slots_per_sub_window` is the exact bound and not a slack one. -/
theorem devnetRun_hits_the_bound :
    devnetRun.any (fun b => b.2.2.any (fun d => d == 7)) = true := by decide

/-! ### §6.1 — The differential can go red.

A gate that cannot fail is not a gate. Each mutation below is a plausible mis-transcription; each
is REFUTED by the same 290 real blocks. -/

/-- Mutation A: never zero anything — i.e. read the ring as if parent and child were always in the
same sub-window. This is what an implementation that forgets the projection does. -/
def stepNoZeroing (C : Constants) (s : WindowState) (nextSlot : Nat) : WindowState :=
  let nextRel := relativeSubWindow C (globalSubWindow C nextSlot)
  { slot := nextSlot
    minWindowDensity :=
      updateMinWindowDensity C s.slot nextSlot s.subWindowDensities s.minWindowDensity
    subWindowDensities :=
      mapIdxFrom 0 (fun i d => if i = nextRel then d + 1 else d) s.subWindowDensities }

/-- Mutation B: the block is counted into the sub-window NEXT to its own — an off-by-one in the
ring index, the single most likely transcription slip. -/
def stepOffByOne (C : Constants) (s : WindowState) (nextSlot : Nat) : WindowState :=
  let same := globalSubWindow C s.slot = globalSubWindow C nextSlot
  let nextRel := (relativeSubWindow C (globalSubWindow C nextSlot) + 1) % C.subWindowsPerWindow
  { slot := nextSlot
    minWindowDensity :=
      updateMinWindowDensity C s.slot nextSlot s.subWindowDensities s.minWindowDensity
    subWindowDensities :=
      mapIdxFrom 0 (fun i d => if i = nextRel then (if same then d else 0) + 1 else d)
        (projectedWindow C s.slot nextSlot s.subWindowDensities) }

def foldMatchesWith (f : Constants → WindowState → Nat → WindowState) (C : Constants) :
    WindowState → List (Nat × Nat × List Nat) → Bool
  | _, [] => true
  | s, (t, m, ds) :: rest =>
      let s' := f C s t
      s'.minWindowDensity == m && s'.subWindowDensities == ds && foldMatchesWith f C s' rest

def runMatchesWith (f : Constants → WindowState → Nat → WindowState) (C : Constants) :
    List (Nat × Nat × List Nat) → Bool
  | [] => true
  | (t, m, ds) :: rest =>
      foldMatchesWith f C { slot := t, minWindowDensity := m, subWindowDensities := ds } rest

/-- The differential REFUTES the no-projection mutation. -/
theorem devnet_refutes_no_zeroing :
    runMatchesWith stepNoZeroing mainnet devnetRun = false := by decide

/-- The differential REFUTES the off-by-one ring index. -/
theorem devnet_refutes_off_by_one :
    runMatchesWith stepOffByOne mainnet devnetRun = false := by decide

/-- And it accepts the real one — stated next to the refutations so both polarities are witnessed
by the SAME data. -/
theorem devnet_accepts_the_real_rule :
    runMatchesWith (fun C s t => step C s t) mainnet devnetRun = true := by decide

/-! ⚑ **What the differential does NOT cover, stated rather than implied.** Epoch-56 devnet is
dense: across all 290 transitions the sub-window advance is only ever `0` (217 of them) or `1`
(73), so the multi-sub-window shift and the disjoint-window (whole-window zeroing) branches are
NOT exercised by this data, and `min_window_density` is constant at `3` throughout, so the run
pins the `min` update only as an inequality. §3's slide law covers every shift `1..11`
exhaustively but abstractly; §7 covers the disjoint branch by construction. The grace-period
branch is unreachable on any modern block (every slot here is `> 402000` against
`grace_period_end = 2237`), so it is covered only by `updateMinWindowDensity_in_grace`. -/

/-! ## §7 — Teeth: the two things that are NOT true, and the one precondition that is load-bearing.

Both are stated as REFUTATIONS, not as prose, so that a future edit that "fixes" them fails. -/

/-- **The density bound is NOT an invariant of `step` alone.** A parent whose own sub-window is
already full, extended by a block in the SAME sub-window, produces `8 > slots_per_sub_window = 7`.
This state is unreachable on a valid chain — it needs an 8th block in a 7-slot sub-window — which
is exactly why §5's `WindowOk_step` carries `s.slot < t` and the density bound is a fact about
VALIDATED chains, not about the update function.

⚑ For a light client this is the operational content: replaying the window is not enough. The
client must ALSO check `parent.slot < child.slot`, which Mina enforces in the block circuit
(`proof_of_stake.ml:2201-2207`) and which nothing in the density arithmetic re-checks. -/
theorem density_bound_is_not_a_step_invariant :
    ((step mainnet
        { slot := 6, minWindowDensity := 77,
          subWindowDensities := [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] } 6).subWindowDensities.getD 0 0)
      = 8 := by decide

/-- **A backwards slot is not refused, it is mis-computed.** `update_min_window_density`'s own
comment (`proof_of_stake.ml:1271-1273`) names `next_global_sub_window ≥ prev_global_sub_window` as
a PRECONDITION. Feed it a child whose slot is *behind* its parent and the function still returns:
`overlapping_window` is vacuously true, so the ring keeps stale entries instead of zeroing them,
and the density is inflated. Here a genuine 11-sub-window regression retains the full window. -/
theorem backwards_slot_inflates_the_window :
    currentWindowDensity mainnet 154 7 [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] = 77 := by decide

/-- The same regression, if the slots had been in the honest order, would have zeroed the window
to nothing at all (the gap is 21 sub-windows, so the windows are disjoint). The contrast is the
whole point: the difference between
`77` and `0` is decided by an ordering check that lives OUTSIDE this function. -/
theorem forwards_same_gap_zeroes_the_window :
    currentWindowDensity mainnet 7 154 [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] = 0 := by decide

/-- The disjoint-window branch, by construction since real data does not reach it: a gap of more
than `sub_windows_per_window` sub-windows zeroes everything, and the block starts a fresh window
at density 1. Spec §5.4.9 (`README.md:799`): "B's entire window is zeroed". -/
theorem disjoint_window_zeroes_everything :
    (step mainnet
       { slot := 7, minWindowDensity := 77,
         subWindowDensities := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] } 3000).subWindowDensities
      = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by decide

/-- …and drives `min_window_density` to `0`, which is the attack the spec's own security note
(`README.md:924`) calls out: `sub_windows_per_window` consecutive empty sub-windows make the
canonical chain long-forkable. -/
theorem disjoint_window_zeroes_the_minimum :
    (step mainnet
       { slot := 7, minWindowDensity := 77,
         subWindowDensities := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] } 3000).minWindowDensity
      = 0 := by decide

/-- …but only PAST the grace period. The same gap at slot `1000 < grace_period_end = 2237` leaves
the minimum untouched at `77`, which is `updateMinWindowDensity_in_grace` on real numbers. -/
theorem disjoint_window_inside_grace_keeps_the_minimum :
    (step mainnet
       { slot := 7, minWindowDensity := 77,
         subWindowDensities := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] } 1000).minWindowDensity
      = 77 := by decide

/-! ## §8 — The seam a light client would call. -/

/-- Decide whether a child's reported window is the one the rule produces from its parent's,
INCLUDING the slot-ordering precondition of §7 that the arithmetic does not itself enforce. This
is the whole mechanism as a single accept/refuse. -/
def windowTransitionOk (C : Constants) (parent child : WindowState) : Bool :=
  parent.slot < child.slot &&
  parent.subWindowDensities.length == C.subWindowsPerWindow &&
  (step C parent child.slot).minWindowDensity == child.minWindowDensity &&
  (step C parent child.slot).subWindowDensities == child.subWindowDensities

/-- The seam accepts every real transition in the run. -/
theorem windowTransitionOk_accepts_real_devnet :
    (devnetRun.zip devnetRun.tail).all (fun p =>
      windowTransitionOk mainnet
        { slot := p.1.1, minWindowDensity := p.1.2.1, subWindowDensities := p.1.2.2 }
        { slot := p.2.1, minWindowDensity := p.2.2.1, subWindowDensities := p.2.2.2 }) = true := by
  decide

/-- The seam REFUSES a backwards child, which §7 shows the arithmetic alone would not. -/
theorem windowTransitionOk_refuses_backwards :
    windowTransitionOk mainnet
      { slot := 154, minWindowDensity := 77,
        subWindowDensities := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
      { slot := 7, minWindowDensity := 77,
        subWindowDensities := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] } = false := by decide

/-- The seam REFUSES a forged density array on an otherwise well-formed transition. -/
theorem windowTransitionOk_refuses_forged_density :
    windowTransitionOk mainnet
      { slot := 7, minWindowDensity := 77,
        subWindowDensities := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }
      { slot := 14, minWindowDensity := 77,
        subWindowDensities := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9] } = false := by decide

/-- `@[export]` seam for the node side. Takes the parent and child window fields flat. -/
@[export dregg_mina_window_transition_ok]
def dregg_mina_window_transition_ok
    (parentSlot parentMin : Nat) (parentDensities : List Nat)
    (childSlot childMin : Nat) (childDensities : List Nat) : Bool :=
  windowTransitionOk mainnet
    { slot := parentSlot, minWindowDensity := parentMin, subWindowDensities := parentDensities }
    { slot := childSlot, minWindowDensity := childMin, subWindowDensities := childDensities }

/-! ## §9 — Hygiene. Nothing here rests on anything but the three standard axioms. -/

#assert_axioms withinRange_iff_out_of_window
#assert_axioms mina_window_replays_real_devnet
#assert_axioms devnet_refutes_no_zeroing
#assert_axioms devnet_refutes_off_by_one
#assert_axioms WindowOk_step
#assert_axioms WindowOk_replay
#assert_axioms updateMinWindowDensity_le
#assert_axioms density_bound_is_not_a_step_invariant
#assert_axioms windowTransitionOk_accepts_real_devnet
#assert_axioms windowTransitionOk_refuses_backwards

#print axioms mina_window_replays_real_devnet
#print axioms withinRange_iff_out_of_window
#print axioms WindowOk_step

end Dregg2.Bridge.MinaSlidingWindow
