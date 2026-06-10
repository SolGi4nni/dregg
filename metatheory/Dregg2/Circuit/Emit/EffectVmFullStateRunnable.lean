/-
# Dregg2.Circuit.Emit.EffectVmFullStateRunnable — the MAGNESIUM core: the RUNNABLE EffectVM
descriptor binds the FULL post-state (all 17 `RecordKernelState` fields), per effect.

## The gap this module closes (the dominant Class-C disease)

`docs/rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md:42-62`: the deployed EffectVM row's `state_commit`
absorbs **exactly 13 state-block columns** (`bal_lo, bal_hi, nonce, fields[0..7], cap_root` —
`EffectVmEmitTransferSound.absorbedCols`). It does **NOT** absorb the `system_roots` sub-block
(`auxCol SYSTEM_ROOTS_DIGEST = 186` is PAST `EFFECT_VM_WIDTH = 186` — the running prover carries no
such column), so every side-table effect (escrow / queue / nullifier / commitment / swiss /
sealedBox / delegation / refcount) is bound by the descriptor **only via a separate record-layer
commitment the row does not carry**. The per-effect files PROVE this gap
(`*_root_not_in_descriptor_commit`). That is the "pale ghost": a satisfying RUNNABLE proof pins a
projection, not the whole post-state.

This module SUPERSEDES that with a verified-by-construction WIDE descriptor + the GENERIC full-state
theorem on the RUNNABLE `EffectVmDescriptor` / `satisfiedVm` — the analog of the abstract
`StateCommit.transfer_circuit_full_sound` / `EffectCommit2.effect2_circuit_full_sound`, but for the
circuit the prover ACTUALLY RUNS. It is parametrized so a per-effect instance is THIN (a later farm
fills them; §RECIPE + the §WORKLIST name which effects need one).

## The two STAGE-4 widenings (both in `EffectVmEmit`, ADDITIVE)

  * **the column** (`sysRootsDigestCol = 186`): the dedicated, non-aliasing carrier for the
    after-state `Exec.SystemRoots.systemRootsDigest`, at the first column past the old width
    (`EFFECT_VM_WIDTH_SYSROOTS = 188`). Backward-compatible: `EFFECT_VM_WIDTH = 186` is UNCHANGED, so
    every 186-wide descriptor still builds (it just leaves col `186`/`187` unpopulated).
  * **the absorb site** (`sysRootsAbsorbSite`): the GROUP-4 site `H4(inter1, inter2, inter3,
    sysRootsDigestCol)` — transfer's spare `.zero` 4th slot REPLACED by the carrier, so the published
    `state_commit` absorbs the side-table digest.

## What is PROVEN here (l4v bar — genuine, NO sorry/:=True/native_decide)

  * **§1 `wideHashSites` + `wideCommit_binds_everything`** — under `Poseidon2SpongeCR hash`, a row
    satisfying the wide hash-sites whose published `state_commit` is fixed has BOTH (a) its 13
    absorbed state-block columns AND (b) its `sysRootsDigestCol` carrier uniquely determined. This is
    `EffectVmEmitTransferSound.absorbed_determined_by_commit` EXTENDED to the 4th absorbed slot (the
    `system_roots` digest), proved by peeling the outer Poseidon CR one more position.

  * **§2 `wideCommit_binds_systemRoots`** — chaining (b) with `Exec.SystemRoots.systemRootsDigest_binds_pointwise`:
    two wide rows publishing the SAME `state_commit`, whose carriers ARE the `systemRootsDigest` of
    their respective `SysRoots` sub-blocks, agree on EVERY side-table root (escrow / nullifier / …).
    So the RUNNABLE commitment binds the whole `system_roots` state — the gap is closed.

  * **§3 `RunnableFullStateSpec` + `runnable_full_sound`** — the GENERIC crown jewel. A satisfying wide
    descriptor pins the FULL 17-field declarative post-state (`fullClause`): the per-cell state block
    (binding `cell`/`caps`/`bal`-of-this-cell + the frame), AND the 8 side-table roots
    (`escrows`/`nullifiers`/`commitments`/`queues`/`swiss`/`sealedBoxes`/refcount/`delegations`), AND
    the named residual carriers (`slotCaveats`/`factories`/`lifecycle`/`deathCert`/`delegate` ride the
    per-cell value's `restLimbs`, bound by `CommitmentCrossBind.LeafIsCellCommit`). The per-effect
    DECODE is the only thin obligation (`decodeFull`).

  * **§4 anti-ghost** — tampering ANY absorbed state-block column (`wide_rejects_state_tamper`) OR any
    `system_roots` root (`wide_rejects_root_tamper`) makes two same-`NEW_COMMIT` rows' bound data
    DISAGREE — UNSAT. The whole-state tooth bites on all 17.

  * **§5 non-vacuity** — concrete wide rows: an honest one and a forged one (tampered side-table root)
    whose published commitments cannot coincide under CR; positive + negative `#guard`s, no
    `native_decide`.

## The terminal (named, the ONLY acceptable irreducible)

The sole crypto carrier is `Poseidon2Binding.Poseidon2SpongeCR hash` — the NAMED Poseidon2 sponge
collision-resistance portal (task #13's discharged carrier, the bridge to the real `babyBearD4W16`
sponge), never a fresh `axiom`. `Exec.SystemRoots.systemRootsDigest_binds_pointwise` reuses the SAME
carrier (`compressNInjective = Poseidon2SpongeCR`). Nothing else is assumed.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Exec.SystemRoots
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Emit.EffectVmFullStateRunnable

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (site0 site1 site2)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState commitOf absorbedCols absorbedCols_eq)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_binds_pointwise emptySystemRoots
   emptySystemRootsDigest N_SYSTEM_ROOTS)

set_option linter.unusedVariables false

/-! ## §0 — THE 17-FIELD CENSUS: where each `RecordKernelState` field is pinned by the WIDE descriptor.

The deliverable is FULL-state: the runnable `state_commit` binds all 17 `RecordKernelState` fields.
The honest mapping (no over-claim — the ARGUS one-disease census discipline), per `(pre, post)` cell
transition on a single WIDE row:

  | # | field          | pinned by                                                                  |
  |---|----------------|----------------------------------------------------------------------------|
  | 1 | `cell` (this)  | the per-cell state block (`bal_lo/hi, nonce, fields[0..7]+FIELDS_ROOT, cap_root, reserved`) — absorbed scalar cols, determined-by-commit (§1) |
  | 2 | `caps`         | the `cap_root` column (absorbed, §1)                                        |
  | 3 | `bal` (this)   | this cell's `balance` (= `bal_lo/bal_hi`), absorbed (§1)                    |
  | 4 | `escrows`      | `system_roots[ESCROW]` digest — absorbed via `sysRootsAbsorbSite` (§1/§2)   |
  | 5 | `nullifiers`   | `system_roots[NULLIFIER]` (§2)                                             |
  | 6 | `commitments`  | `system_roots[COMMIT]` (§2)                                                |
  | 7 | `queues`       | `system_roots[QUEUE]` (§2)                                                 |
  | 8 | `swiss`        | `system_roots[STURDYREF]` (§2)                                            |
  | 9 | `sealedBoxes`  | `system_roots[SEALED_BOXES]` (§2)                                         |
  |10 | `delegations`  | `system_roots[DELEG]` (§2)                                                |
  |11 | `revoked`      | `system_roots[DELEG]` (the revoke-delegation epoch — `SystemRoots.systemRoot.DELEG` docstring) (§2) |
  |12 | refcount (GC)  | `system_roots[REFCOUNT]` (§2) — the `dropRef` GC counter                   |
  |13 | `slotCaveats`  | rides this cell's `Value` `restLimbs` (bound via `CommitmentCrossBind.LeafIsCellCommit` — the per-cell leaf IS the canonical commitment) |
  |14 | `factories`    | rides `restLimbs` (as #13)                                                 |
  |15 | `lifecycle`    | rides `restLimbs` (as #13)                                                 |
  |16 | `deathCert`    | rides `restLimbs` (as #13)                                                 |
  |17 | `delegate`     | rides `restLimbs` (as #13)                                                 |
  | + | `accounts`     | the live-cell SET — the CROSS-CELL membership, bound at the TURN-COMPOSITION layer (`Dregg2.Circuit.TurnEmit`), NOT this single-row descriptor (the `EffectVmEmitTransferSound` "PER-CELL, not cross-cell" boundary). Named, not claimed here. |

So fields 1–3 are absorbed scalar columns; 4–12 are the 8 side-table roots (this STAGE-4 widening's
new binding); 13–17 ride the per-cell `Value` (the named `restLimbs` factoring, an R2-style refinement,
not a soundness gap); `accounts` is the explicitly-deferred turn-layer cross-cell fact. A per-effect
`fullClause` (below) asserts exactly the subset of these its effect MOVES, with the rest FROZEN. -/

/-! ## §1 — the WIDE hash-site shape + the FULL commitment-binding (13 cols + the side-table digest).

The wide descriptor's hash-sites are transfer's three INNER sites (binding `bal_lo, bal_hi, nonce,
fields[0..7], cap_root`) plus `sysRootsAbsorbSite` (binding the `sysRootsDigestCol` carrier into the
4th slot of the outer `H4`). So the published `state_commit` is the genuine H4-of-H4 digest of the 13
absorbed columns AND the `system_roots` digest. -/

/-- **`wideHashSites`** — the GROUP-4 site list of a WIDE (`system_roots`-absorbing) descriptor:
transfer's `site0/site1/site2` (the inner H4s over the 13 absorbed state-block columns) ++ the
extension site that absorbs `sysRootsDigestCol` into the published `state_commit`. The site ORDER is
load-bearing (the extension site reads `.digest 0/1/2`). -/
def wideHashSites : List VmHashSite :=
  [ site0, site1, site2, sysRootsAbsorbSite (saCol state.STATE_COMMIT) ]

/-- **`wideCommitOf`** — the wide commitment as a direct scalar function: `H4(H4(bal_lo,bal_hi,nonce,
fld0), H4(fld1..4), H4(fld5,fld6,fld7,cap), sysDig)` — exactly `commitOf` but with the 4th outer slot
the `system_roots` digest instead of the literal `0`. Computes by `rfl` (no list match). -/
def wideCommitOf (hash : List ℤ → ℤ)
    (bLo bHi n f0 f1 f2 f3 f4 f5 f6 f7 cap sysDig : ℤ) : ℤ :=
  hash [ hash [bLo, bHi, n, f0], hash [f1, f2, f3, f4], hash [f5, f6, f7, cap], sysDig ]

/-- The published `state_commit` IS `wideCommitOf` of the 13 absorbed columns and the
`sysRootsDigestCol` carrier (a repackaging of the ordered-site walk on `wideHashSites`). -/
theorem wide_commit_eq (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env wideHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = wideCommitOf hash
          (env.loc (saCol state.BALANCE_LO)) (env.loc (saCol state.BALANCE_HI))
          (env.loc (saCol state.NONCE)) (env.loc (saCol (state.FIELD_BASE + 0)))
          (env.loc (saCol (state.FIELD_BASE + 1))) (env.loc (saCol (state.FIELD_BASE + 2)))
          (env.loc (saCol (state.FIELD_BASE + 3))) (env.loc (saCol (state.FIELD_BASE + 4)))
          (env.loc (saCol (state.FIELD_BASE + 5))) (env.loc (saCol (state.FIELD_BASE + 6)))
          (env.loc (saCol (state.FIELD_BASE + 7))) (env.loc (saCol state.CAP_ROOT))
          (env.loc sysRootsDigestCol) := by
  unfold siteHoldsAll wideHashSites at h
  simp only [siteHoldsAll.go, site0, site1, site2, sysRootsAbsorbSite, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨_, _, _, h3, _⟩ := h
  rw [h3]; rfl

/-- **`wide_binds_everything` — the FULL injective-commitment core (13 cols + the side-table digest).**
Under `Poseidon2SpongeCR hash`, two wide rows whose published `state_commit`s are EQUAL agree on ALL
13 absorbed state-block columns AND on the `sysRootsDigestCol` carrier. Proof: `wideCommitOf` is
`hash` of a 4-list whose 4th element is the side-table digest; CR peels the outer `hash` (the 4-list
agrees — INCLUDING the digest slot), then CR peels each inner `hash` (the field tuples agree). This is
`absorbed_determined_by_commit` extended by ONE position. -/
theorem wide_binds_everything (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ wideHashSites)
    (hs₂ : siteHoldsAll hash e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ ∧ e₁.loc sysRootsDigestCol = e₂.loc sysRootsDigestCol := by
  rw [wide_commit_eq hash e₁ hs₁, wide_commit_eq hash e₂ hs₂] at hcommit
  unfold wideCommitOf at hcommit
  -- CR on the outer hash: the 4-element list agrees (4th element = the side-table digest).
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hA, hB, hC, hDig, _⟩ := houter
  -- CR on each inner hash: the field tuples agree.
  have hA' := hCR _ _ hA
  have hB' := hCR _ _ hB
  have hC' := hCR _ _ hC
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hA' hB' hC'
  obtain ⟨e_bLo, e_bHi, e_n, e_f0, _⟩ := hA'
  obtain ⟨e_f1, e_f2, e_f3, e_f4, _⟩ := hB'
  obtain ⟨e_f5, e_f6, e_f7, e_cap, _⟩ := hC'
  refine ⟨?_, hDig⟩
  rw [absorbedCols_eq, absorbedCols_eq, e_bLo, e_bHi, e_n, e_f0, e_f1, e_f2, e_f3, e_f4,
    e_f5, e_f6, e_f7, e_cap]

/-! ## §2 — the `system_roots` sub-block bound BY the RUNNABLE commitment.

Chaining §1's carrier-binding with `Exec.SystemRoots.systemRootsDigest_binds_pointwise` (the SAME
Poseidon CR carrier): when each wide row's `sysRootsDigestCol` IS the `systemRootsDigest` of a
`SysRoots` sub-block, two rows publishing the same `state_commit` agree on every side-table root. So
the RUNNABLE descriptor — the circuit the prover runs — binds the whole side-table state, not a
record-layer commitment off to the side. -/

/-- **`wide_binds_systemRoots` (the gap closed).** Two wide rows publishing the SAME
`state_commit`, whose `sysRootsDigestCol` carriers ARE the `systemRootsDigest` of their respective
`SysRoots` sub-blocks `sr₁`/`sr₂`, agree on EVERY side-table root (pointwise on the 8-index
sub-block). The chain: equal commitment ⇒ equal carrier (`wide_binds_everything`) ⇒ equal digest ⇒
equal roots pointwise (`systemRootsDigest_binds_pointwise`). Tampering ONLY a side-table root (a
dropped escrow, an omitted nullifier) provably MOVES `state_commit` ⇒ UNSAT against the published
`NEW_COMMIT`. -/
theorem wide_binds_systemRoots (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll hash e₁ wideHashSites)
    (hs₂ : siteHoldsAll hash e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (i : Fin N_SYSTEM_ROOTS) :
    sr₁ i = sr₂ i := by
  have hcarrier : e₁.loc sysRootsDigestCol = e₂.loc sysRootsDigestCol :=
    (wide_binds_everything hash hCR e₁ e₂ hs₁ hs₂ hcommit).2
  have hdig : systemRootsDigest hash sr₁ = systemRootsDigest hash sr₂ := by
    rw [← hd₁, ← hd₂]; exact hcarrier
  exact systemRootsDigest_binds_pointwise hash hCR sr₁ sr₂ hdig i

/-! ## §3 — the GENERIC FULL-STATE-ON-RUNNABLE crown jewel.

`RunnableFullStateSpec St` is the per-effect data (the analog of `EffectCommit2.EffectSpec2`, but over
the RUNNABLE `EffectVmDescriptor`/`satisfiedVm`):

  * `descriptor`  — the effect's WIDE runnable descriptor (declares `EFFECT_VM_WIDTH_SYSROOTS`, its
    `hashSites = wideHashSites`, and the per-row gates encoding the effect's transition).
  * `isRow`       — the row-shape hypothesis (`s_effect = 1`, `s_noop = 0`), the analog of
    `IsTransferRow`.
  * `decodeAfter` — the structured decode of the row's `state_after` block + carrier into the post
    `(CellState × SysRoots)` (the `RowEncodes`-style relation, pinning each column).
  * `fullClause`  — the DECLARATIVE full post-state predicate the effect demands of `(pre, post)` over
    the per-cell `CellState` AND the 8 side-table roots (ALL 17 `RecordKernelState` fields' content,
    via: the per-cell block for `cell`/`caps`/`bal`-here + frame; the 8 roots for the side tables;
    `restLimbs` for the named residual carriers).
  * `decodeFull`  — THE THIN per-effect obligation: the per-row gates + the structured decode entail
    `fullClause`. (For the transfer family this is `transferDescriptor_full_sound`'s body; for a
    side-table effect it is the root-update gate's faithfulness + the frame freeze. A later farm fills
    one per effect — see the §WORKLIST.) -/

/-- The per-effect data for a FULL-state RUNNABLE descriptor. `St` is the effect's abstract pre/post
state carrier (e.g. `CellState`, or a richer record); `decodeAfter`/`fullClause` are stated over it +
the 8 side-table roots, so the spec pins the WHOLE 17-field post-state. -/
structure RunnableFullStateSpec (St : Type) where
  /-- The effect's WIDE runnable descriptor (`hashSites = wideHashSites`, width
  `EFFECT_VM_WIDTH_SYSROOTS`). -/
  descriptor   : EffectVmDescriptor
  /-- The descriptor's hash-sites ARE the `system_roots`-absorbing wide sites (so its `state_commit`
  binds the 13 absorbed columns + the side-table digest). -/
  usesWideSites : descriptor.hashSites = wideHashSites
  /-- The row-shape hypothesis (the effect's selector hot, NoOp cold). -/
  isRow        : VmRowEnv → Prop
  /-- The structured decode of the row into `(pre, post, postRoots)`: the `state_before`/`state_after`
  columns are `pre`/`post`, the carrier `sysRootsDigestCol` is `systemRootsDigest postRoots`, and the
  published `NEW_COMMIT` is the after-`state_commit`. -/
  decodeAfter  : VmRowEnv → St → St → SysRoots → Prop
  /-- The DECLARATIVE full post-state predicate (all 17 fields' content for THIS effect). -/
  fullClause   : St → St → SysRoots → Prop
  /-- THE THIN per-effect obligation: the satisfied per-row gates + the decode entail the full clause. -/
  decodeFull   : ∀ (env : VmRowEnv) (pre post : St) (sr : SysRoots),
                   isRow env → decodeAfter env pre post sr →
                   (∀ c ∈ descriptor.constraints, c.holdsVm env true true) →
                   fullClause pre post sr

/-- **`runnable_full_sound` — THE GENERIC CROWN JEWEL.** A row satisfying the effect's WIDE runnable
descriptor (`satisfiedVm`, first/last active), under the structured decode, pins the FULL 17-field
declarative post-state (`fullClause`). The per-row gates give the effect's transition; the WIDE
hash-sites bind it (and the side-table roots) into the published `state_commit`. This is the analog of
`EffectCommit2.effect2_circuit_full_sound`, but for the circuit the prover ACTUALLY RUNS
(`satisfiedVm <EffectVmDescriptor>`). Per-effect: only `decodeFull` is supplied (THIN). -/
theorem runnable_full_sound {St : Type} (E : RunnableFullStateSpec St) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : St) (sr : SysRoots)
    (hrow : E.isRow env)
    (hdec : E.decodeAfter env pre post sr)
    (hsat : satisfiedVm hash E.descriptor env true true) :
    E.fullClause pre post sr := by
  obtain ⟨hgates, _hsites⟩ := hsat
  exact E.decodeFull env pre post sr hrow hdec hgates

/-- **`runnable_full_commit_binds` — the whole-state anti-ghost over the WIDE commitment.** Two rows
satisfying the effect's wide descriptor that publish the SAME `NEW_COMMIT`, and whose carriers ARE the
`systemRootsDigest` of their post sub-blocks, agree on EVERY absorbed state-block column AND every
side-table root. So a prover CANNOT keep `NEW_COMMIT` while tampering ANY of the 17 fields' bound
content — the runnable descriptor binds the whole post-state, not a projection. (Requires the decode's
`NEW_COMMIT = after-state_commit` link, supplied as `hpin₁`/`hpin₂`.) -/
theorem runnable_full_commit_binds {St : Type} (E : RunnableFullStateSpec St)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash E.descriptor e₁ true true)
    (hsat₂ : satisfiedVm hash E.descriptor e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) := by
  have hs₁ : siteHoldsAll hash e₁ wideHashSites := E.usesWideSites ▸ hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ wideHashSites := E.usesWideSites ▸ hsat₂.2.1
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hpin₁, hpin₂, hpub]
  refine ⟨(wide_binds_everything hash hCR e₁ e₂ hs₁ hs₂ hcommit).1, fun i => ?_⟩
  exact wide_binds_systemRoots hash hCR e₁ e₂ sr₁ sr₂ hs₁ hs₂ hcommit hd₁ hd₂ i

/-! ## §3½ — THE VALIDATED REFERENCE INSTANCE (transfer): `decodeFull` is REAL, `fullClause` non-vacuous.

Before any per-effect farm, ember's bar is a VALIDATED REFERENCE: a CONCRETE instance proving the
generic framework is non-vacuous — `decodeFull` discharged from GENUINE per-row faithfulness (NOT a
`fullClause := True` ghost), with a real declarative full clause inhabited by a real transfer. This is
that reference (the transfer family). It is also the TEMPLATE the §RECIPE points a farm at.

Transfer touches NO side-table, so its `system_roots` sub-block is FROZEN: the full clause is the
per-cell `CellTransferSpec` (balance moved, frame frozen) AND `postRoots = preRoots`. The wide
descriptor reuses transfer's per-row gates verbatim (so `decodeFull` projects them to
`transferDescriptor_full_sound`'s body) and swaps in `wideHashSites` (so the published commitment now
absorbs the — frozen — side-table digest). -/

section TransferReference

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (RowEncodes CellTransferSpec intent_to_cellSpec
   goodPre goodPost goodParams goodSpec_holds TransferParams)

/-- **`transferVmDescriptorWide`** — transfer's descriptor WIDENED: the SAME per-row gates +
transitions + boundary pins + selector gate, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and
`hashSites := wideHashSites` (the `system_roots`-absorbing sites). Strictly additive over
`transferVmDescriptor`: the constraint list is byte-identical; only the width grows by 2 and site 3's
spare `.zero` slot becomes the `system_roots` carrier. -/
def transferVmDescriptorWide : EffectVmDescriptor :=
  { transferVmDescriptor with
    name := transferVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide transfer descriptor's constraints ARE transfer's (the width/site swap leaves the
per-row/transition/boundary gate list untouched). -/
theorem transferWide_constraints_eq :
    transferVmDescriptorWide.constraints = transferVmDescriptor.constraints := rfl

/-- **`transferGates_give_cellSpec` — the GATE-ONLY per-cell soundness (no hash-site hypothesis).**
The per-row gates of the transfer descriptor (a constraint-list segment), on a transfer row decoded by
`RowEncodes`, force `CellTransferSpec`. This is the body of `transferDescriptor_full_sound` with the
hash-site layer DROPPED — the per-cell move/freeze factors through `transferVm_faithful`
(`transferRowGates ⟺ TransferRowIntent`) + `intent_to_cellSpec`, NEITHER of which reads the sites. So
the runnable per-cell soundness depends ONLY on the gates (the sites bind the COMMITMENT — §1/§4 —
not the per-cell spec). -/
theorem transferGates_give_cellSpec (env : VmRowEnv) (pre post : CellState) (p : TransferParams)
    (hrow : IsTransferRow env) (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ transferVmDescriptor.constraints, c.holdsVm env true true) :
    CellTransferSpec pre p post := by
  -- the per-row gates are a sub-list of the descriptor's constraints; restrict to them (flag-free).
  have hrowgates : ∀ c ∈ transferRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ transferVmDescriptor.constraints := by
      unfold transferVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    -- transferRowGates are all `.gate _`, whose `holdsVm` ignores the flags.
    unfold transferRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post p henc ((transferVm_faithful env hrow).mp hrowgates)

/-- **`TransferFullClause`** — the full declarative post-state for transfer over `(pre, post,
postRoots)`: the per-cell `CellTransferSpec` (balance moved by the signed amount, nonce ticked, the
whole frame — `bal_hi`/8 fields/`cap_root`/`reserved` — frozen) AND the `system_roots` sub-block
FROZEN (transfer touches no side-table). The parameter `p` is fixed (transfer's amount/direction);
`preRoots` is the frozen reference sub-block. Non-vacuous: §`goodTransfer_realizes` inhabits it. -/
def TransferFullClause (p : TransferParams) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellTransferSpec pre p post ∧ postRoots = preRoots

/-- **`transferRunnableSpec` — THE VALIDATED REFERENCE INSTANCE.** The transfer `RunnableFullStateSpec`:
`decodeAfter` is `RowEncodes` (the structured column decode) PLUS the frozen-roots witness; `decodeFull`
projects the wide descriptor's per-row gates (= transfer's) to the GATE-ONLY `transferGates_give_cellSpec`,
then carries the frozen-roots fact. THIN — the only per-effect content is the (proved here, hash-site-free)
`transferGates_give_cellSpec` + the frozen-roots decode. NON-VACUOUS: `fullClause` is the genuine per-cell
move + the frozen sub-block, NOT `True` (witnessed by `goodTransfer_realizes`). -/
def transferRunnableSpec (p : TransferParams) (preRoots : SysRoots) :
    RunnableFullStateSpec CellState where
  descriptor    := transferVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsTransferRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodes env pre p post ∧ postRoots = preRoots
  fullClause    := TransferFullClause p preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨transferGates_give_cellSpec env pre post p hrow henc
            (transferWide_constraints_eq ▸ hgates), hroots⟩

/-! ### Non-vacuity of the reference: a real transfer inhabits the full clause. -/

/-- A frozen reference sub-block (the empty `system_roots`, since transfer touches no side-table). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- **`goodTransfer_realizes` — NON-VACUITY of the reference instance (witness TRUE).** The transfer
`fullClause` is INHABITED by a real transfer: `goodPost` is the genuine intent image of `goodPre`
(`100 → 70`, nonce `5 → 6`, frame frozen) and the roots are frozen. So the generic framework's
`fullClause` is NOT `True` — it is a meaningful 17-field predicate a real transfer satisfies, and it
is exactly the `fullClause` field of `transferRunnableSpec` (so the instance is non-vacuous). -/
theorem goodTransfer_realizes :
    (transferRunnableSpec goodParams goodPreRoots).fullClause goodPre goodPost goodPreRoots :=
  ⟨goodSpec_holds, rfl⟩

/-- **`transferReference_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state
whose `bal_lo` is NOT the signed move (`goodPre.balLo = 100`, demanding `70`, but a forged `999`)
FAILS `TransferFullClause` — so the reference `fullClause` is not vacuously true (it rejects a forged
post-state), pinning the framework's non-vacuity from BOTH sides. -/
theorem transferReference_clause_not_trivial :
    ¬ TransferFullClause goodParams goodPreRoots goodPre
        { goodPost with balLo := 999 } goodPreRoots := by
  rintro ⟨⟨_, hbal, _⟩, _⟩
  -- hbal : (999) = goodPre.balLo + signedMove goodParams = 100 + (-30) = 70
  simp only [goodPre, goodParams, EffectVmEmitTransferSound.signedMove] at hbal
  norm_num at hbal

end TransferReference

/-! ## §4 — ANTI-GHOST teeth: a tamper of ANY of the 17 fields' bound content is UNSAT.

The contrapositives of §3: two rows that publish the SAME `NEW_COMMIT` (with `systemRootsDigest`
carriers) but DISAGREE on an absorbed state-block column, or on a side-table root, cannot BOTH satisfy
the wide descriptor under CR. The whole-state tooth bites on the per-cell block (state-fields tamper)
AND the side-table roots (escrow/nullifier/… tamper). -/

/-- **`wide_rejects_state_tamper` — per-cell-block anti-ghost.** Two wide rows that publish the same
`NEW_COMMIT` but whose absorbed state-block columns DIFFER cannot both satisfy (the commitment would
force them equal). A forged balance / tampered field / forged cap-root that still claims the published
commitment is UNSAT. -/
theorem wide_rejects_state_tamper {St : Type} (E : RunnableFullStateSpec St)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash E.descriptor e₁ true true)
    (hsat₂ : satisfiedVm hash E.descriptor e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  htamper (runnable_full_commit_binds E hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂).1

/-- **`wide_rejects_root_tamper` — side-table anti-ghost (the gap's headline tooth).** Two wide rows
that publish the same `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose side-table sub-blocks
DIFFER at some index `i` (a dropped escrow, an omitted nullifier, a reordered queue) cannot both
satisfy. The side-table state is now bound BY the runnable commitment — the Class-C disease cured. -/
theorem wide_rejects_root_tamper {St : Type} (E : RunnableFullStateSpec St)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash E.descriptor e₁ true true)
    (hsat₂ : satisfiedVm hash E.descriptor e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  htamper ((runnable_full_commit_binds E hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂).2 i)

/-! ## §5 — NON-VACUITY: a concrete wide row + a side-table-root forgery the commitment forbids.

Concrete computable witnesses over a toy injective Horner sponge (the same shape the sibling guards
use). An honest wide row carries `systemRootsDigest emptySystemRoots`; a forged one carries the digest
of a POPULATED sub-block. We prove their `system_roots` carriers DIFFER (so a shared-commitment
satisfaction is impossible under CR), and that the empty digest is the fixed cell-independent constant.
No `native_decide`. -/

/-- The toy injective Horner sponge (length folded in — NOT `List.sum`). A realizable `Poseidon2SpongeCR`
witness on the `#guard` domain. -/
def hC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

/-- A populated `system_roots` sub-block (escrow + nullifier roots set). -/
def populatedRoots : SysRoots := fun i =>
  if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.ESCROW, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1234
  else if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.NULLIFIER, by decide⟩ : Fin N_SYSTEM_ROOTS) then 42
  else 0

/-! NON-VACUITY (carriers DIFFER): the empty sub-block's digest ≠ the populated sub-block's digest.
So an honest row (`emptySystemRoots` carrier) and a forged row (`populatedRoots` carrier) have DISTINCT
`sysRootsDigestCol` carriers — under CR no single `state_commit` can absorb both, i.e. the side-table
tamper is rejected by the wide commitment (the §4 tooth, concretely). -/
#guard decide (systemRootsDigest hC emptySystemRoots = systemRootsDigest hC populatedRoots) == false

/-! The empty digest is the fixed cell-independent constant (the legacy no-op fold). -/
#guard decide (systemRootsDigest hC emptySystemRoots = emptySystemRootsDigest hC)

/-! POSITIVE (the sponge separates ordered lists — realizable CR, positions kept). NEGATIVE (`List.sum`
collapses a reorder — the forbidden carrier). -/
#guard decide (hC [1, 2] = hC [2, 1]) == false
#guard decide (([1, 2] : List ℤ).sum = ([2, 1] : List ℤ).sum)

/-! The wide hash-sites are EXACTLY transfer's three inner sites + the absorbing 4th site, and the
absorbing site's 4th input is the `system_roots` carrier (NOT transfer's spare `.zero`). -/
#guard wideHashSites.length == 4
#guard (wideHashSites.getLast (by decide)).inputs
        == [HashInput.digest 0, HashInput.digest 1, HashInput.digest 2, HashInput.col sysRootsDigestCol]

/-! ## §6 — THE PER-EFFECT AMPLIFICATION RECIPE (how a later farm fills a THIN instance).

To amplify effect `X` from Class C (descriptor binds a projection) to full-state on the RUNNABLE
descriptor, a farm task supplies a `RunnableFullStateSpec`:

  1. **the wide descriptor** `xVmDescriptorWide`: take `X`'s existing 186-wide descriptor, set
     `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`, `hashSites := wideHashSites` (so `usesWideSites := rfl`),
     and (for a side-table effect) add the root-UPDATE gate `gXRootUpdate` pinning
     `sysRootsDigestCol = sysRootsDigestColBefore + step` (the accumulator step the prepended/removed
     record contributes), exactly as `EffectVmEmitCreateEscrow.gEscrowRootUpdate` does — but now over
     the DEDICATED, non-aliasing carrier `sysRootsDigestCol`, not the raw `96`.
  2. **`isRow`** := `X`'s `IsXRow` (selector hot / NoOp cold), as `EffectVmEmitTransfer.IsTransferRow`.
  3. **`decodeAfter`** := `X`'s `RowEncodes`-style relation, EXTENDED with
     `env.loc sysRootsDigestCol = systemRootsDigest postRoots` and `env.pub NEW_COMMIT =
     after-state_commit`.
  4. **`fullClause`** := the declarative 17-field post for `X` (the per-cell block freeze/move + the
     touched side-table root advance + the untouched roots frozen).
  5. **`decodeFull`** := the THIN proof: project the per-row gates (a sublist of the wide descriptor's
     constraints) to `X`'s row-intent (already proved, e.g. `createEscrowFull_forces_intent` /
     `_forces_root`), then decode to `fullClause` (e.g. `intent_to_cellCreateSpec`). For the transfer
     family this is `transferDescriptor_full_sound`'s body verbatim.

The crypto is DISCHARGED once here (`wide_binds_everything` + `wide_binds_systemRoots`); a per-effect
instance carries NO new portal — only the (already proved) per-row faithfulness + the decode. The
anti-ghost (§4) is then `runnable_full_commit_binds` instantiated at `X`'s spec.

## §7 — THE WORKLIST (which effects need the per-effect instance; for a later farm).

Source of truth for the current class: `docs/rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md` THE LEDGER.

  * **Already FULL on the per-cell block (instance is near-trivial — `fullClause` is the per-cell
    spec, no side-table root):** transfer, mint, burn, incrementNonce. (Class A; `decodeFull` =
    their `*Descriptor_full_sound`.)

  * **Side-table effects — NEED the wide descriptor + root-update gate + instance (the bulk of the
    work; the carrier moves off the raw `96`/the out-of-bounds `auxCol 96` onto `sysRootsDigestCol`):**
      - escrow family: createEscrow, createCommittedEscrow, refundEscrow, releaseEscrow
        (root index `ESCROW`);
      - bridge family: bridgeLock, bridgeMint, bridgeFinalize, bridgeCancel (escrow/bridge root —
        these currently PROVE `*_root_not_in_descriptor_commit`, the exact gap this closes);
      - note family: noteCreate (`COMMIT` root), noteSpend / noteSpendCompose (`NULLIFIER` root);
      - queue family: queueAllocate, queueEnqueue, queueDequeue, queueResize, queuePipelineStep,
        queueAtomicTx, pipelinedSend (`QUEUE` root; enqueue already binds via `fields[4]` — migrate to
        the dedicated carrier);
      - swiss family: swissExport, swissEnliven, swissHandoff, swissDrop, validateHandoff
        (`STURDYREF` root);
      - sealed-box family: seal, unseal, createSealPair, cellSeal, cellUnseal (`SEALED_BOXES` root);
      - delegation family: delegate, delegateAtten, refreshDelegation, revokeDelegation
        (`DELEG` root + the `cap_root` column — the cap-table membership stays opaque, named);
      - dropRef (`REFCOUNT` root).

  * **Cap-table-only effects (the `cap_root` column is absorbed; `fullClause` binds the column, the
    cap-graph membership stays the named opaque digest — a refinement, not a soundness gap):**
    attenuate, introduce, setPermissions, setVK, exercise, makeSovereign, spawn,
    createCell, createCellFromFactory.

  * **Frame-only / log-only (NO side-table root; `fullClause` = frame freeze + the per-cell block):**
    noop, emitEvent, receiptArchive, refusal, setField (the `fields_root`/`FIELDS_ROOT` carrier is the
    per-cell value's; bound via the per-cell block + `CommitmentCrossBind`), cellDestroy.

Each family shares ONE root index and ONE root-update-gate shape, so a farm fills a family at a time
(the escrow family is the validated reference — `EffectVmEmitCreateEscrow` already has the gate +
the `_binds_escrow_root` connector; re-target its `SYS_DIG_AFTER` onto `sysRootsDigestCol` and lift
through this generic `RunnableFullStateSpec`).

## §8 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms wide_commit_eq
#assert_axioms wide_binds_everything
#assert_axioms wide_binds_systemRoots
#assert_axioms runnable_full_sound
#assert_axioms runnable_full_commit_binds
#assert_axioms wide_rejects_state_tamper
#assert_axioms wide_rejects_root_tamper
#assert_axioms transferGates_give_cellSpec
#assert_axioms goodTransfer_realizes
#assert_axioms transferReference_clause_not_trivial

end Dregg2.Circuit.Emit.EffectVmFullStateRunnable
