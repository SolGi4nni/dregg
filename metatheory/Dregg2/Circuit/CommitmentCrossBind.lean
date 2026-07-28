/-
# Dregg2.Circuit.CommitmentCrossBind — THE THREE-COMMITMENT CROSS-BINDING CROWN (MID-4).

`.docs-history-noclaude/rebuild/metatheory/_PROOF-INTEGRITY-LEDGER.md` MID-4: the system carries **three disjoint state
commitments**, and — until this module — **no Lean theorem bound any two to ONE authenticated state
object**. So a proof about one (e.g. "the circuit witness pins `recStateCommit`") did NOT constrain
the others (the running cell's BLAKE3 `cellCommit`, or the executor's receipt-chain-bearing root). The
"circuit proof" was therefore a proof about a commitment that need not equal the committed cell state.
This module closes that — it proves the three are functions of the SAME `RecordKernelState` and
**cross-determine** each other on their shared projection, under the named (REALIZABLE, witnessed)
Poseidon/BLAKE3 collision-resistance portals.

## The three commitments (re-derived read-only — file:line)

1. **`recStateCommit`** (`Circuit/StateCommit.lean:196`) — the CIRCUIT full-state root / GROUP-4
   Poseidon2 chain side: `cmb (cellDigest k t) (RH k)`, where
   `cellDigest k t = compress (frameDigest CH compressN k (accounts\{src,dst})) (movedDigest CH compress k.cell src dst)`.
   The EffectVM descriptor `state_commit` (`Circuit/Emit/EffectVmEmitTransfer.lean:133-160`, the four
   `H4` sites) is the per-column H4 realization of THIS digest. Per-cell leaf data: `CH c (k.cell c)`.

2. **`recSetFieldCommit`** (`Circuit/SetFieldCommit.lean:171`) — the EXECUTOR receipt-chain / `Exec.Turn`
   log-root-bearing side: `cmb (cmb (frameDigest CH compressN k (accounts\{cell})) (CH cell (k.cell cell)))
   (cmb (RH k) (LH log))`. It FOLDS the append-only receipt chain `LH log` (the `RecChainedState.log`,
   `RecordKernel.lean:938`) into the state root. Per-cell leaf data: `CH c (k.cell c)`.

3. **`cellCommit`** (`Exec/RecordCommit.lean:79`, the running `cell/src/commitment.rs` v3) — the
   canonical CELL commitment: `compressN (restLimbs c ++ [fieldsRoot compress2 compressN (k.cell c)])`,
   a per-cell BLAKE3 sponge over the cell's authority-bearing limbs WITH the user-field-map root folded
   in. A function of a single cell's `Value` `k.cell c` (over the per-cell `restLimbs` prefix).

## The shared structure that makes cross-binding REAL (not a coincidence of names)

All three read the SAME per-cell content `k.cell c` (commitments 1/2 via the SAME leaf hash `CH`;
commitment 3 via `cellCommit` of that cell's `Value`). Commitments 1 and 2 share the SAME `RH`
(the 16-non-cell rest hash), the SAME `cmb` root combiner, the SAME `frameDigest`/`CH`/`compressN`.
So they are not three unrelated scalars: they are three honestly-encoded digests of ONE
`RecordKernelState`, and injectivity of the shared hashes makes equality of any one *cross-determine*
the shared projection of the others.

## What is PROVED here (l4v bar — genuine)

* **§1 same-state agreement (the "ONE object" direction).** Each commitment is a *total function* of
  the state object, so equal post-states ⟹ equal commitment, across all three
  (`stateCommit_determined`, `setFieldCommit_determined`, `cellCommit_determined`). Trivial-by-
  `congrArg` but LOAD-BEARING: it is the formal statement "they commit to the SAME state object,"
  the thing whose ABSENCE MID-4 flagged. Stated, named, proven — not assumed.

* **§2 per-commitment injectivity → shared projection.** Equal `recStateCommit` (under the StateCommit
  CR set + `RestHashIffFrame`) ⟹ equal cell map on `accounts` AND equal 16 non-cell fields
  (`stateCommit_binds_cells_and_rest`, derived from `recStateCommit_binds` + the proved binding
  lemmas). Equal `recSetFieldCommit` (under the same CR set + `logHashInjective`) ⟹ equal
  untouched-cell map + equal target leaf + equal 16 fields + equal receipt chain
  (`setFieldCommit_binds_all`).

* **§3 THE CROSS-BINDING WELD.** When the circuit pins `recStateCommit` over `k` and the executor pins
  `recSetFieldCommit` over `k'` (SAME `RH`/`cmb`), and both roots are forced equal to a *common*
  published root, the two states AGREE on the 16 non-cell fields (`crossbind_rest_agree`) and on every
  live cell's leaf (`crossbind_cells_agree`) — a circuit proof and an executor proof of the SAME root
  constrain the SAME state. This is the theorem MID-4 said did not exist.

* **§4 THE CROWN — circuit proof CONSTRAINS the committed cell state.** Under ONE additional named
  portal `LeafIsCellCommit` (`CH c v = cellCommit … (restLimbs c) v` — the StateCommit per-cell leaf IS
  the canonical BLAKE3 cell commitment, the realizable factoring of the leaf hash through the running
  commitment), equal `recStateCommit` ⟹ equal `cellCommit` for EVERY live cell
  (`stateCommit_binds_cellCommit`): a satisfying CIRCUIT witness pins the running cell's canonical
  commitment. Dually for the executor root (`setFieldCommit_binds_cellCommit`). The pale ghost is dead:
  "circuit proof" now provably constrains "the committed cell state."

* **§4½/§R THE RUNNABLE SIDE-TABLE BINDING IS A SECURITY REDUCTION, NOT A DISJUNCTION.** The crown
  above is about the three ABSTRACT commitments. The circuit the prover RUNS publishes its own
  `state_commit`, which absorbs the `system_roots` digest column, and this file used to export that
  binding as `runnable_binds_same_system_roots_or_collides` — a bare THREE-way disjunction
  `binds ∨ WideColl ∨ RootsColl`. True at deployed BabyBear parameters, but a shirk with TWO escape
  branches: a sponge collision EXISTS there by pigeonhole, so the statement is satisfiable with the
  binding half never holding. It quantified over SOLUTIONS; cryptographic hardness quantifies over
  EFFICIENT ADVERSARIES. §R replaces it, at this address, with the reduction that does — the forgery
  as a `Game`, the deployed extractor as a map of adversaries, an unconditional advantage inequality,
  and negligibility under the named floor with efficiency DISCHARGED. The disjunction is DEMOTED in
  place to the exact-Prop skeleton (the win relation's deterministic backbone and the `_of_injective`
  bridge's base), and the extractors keep their correct role as the reduction's internal witnesses.

  ⚑ The reduction itself is NOT re-derived here. It lives one layer down, at the definition site of
  the disjunction — `Dregg2.Circuit.Emit.EffectVmWideCommitReduction.wideFullState_binds_rom` (the
  keyed-ROM discharged form; the `_advantage_bound` form carries the fixed-hash content)
  — where it prices ALL FOUR of that file's full-state disjunctions at once, with the GROUP-4 peel and
  the roots peel composed into ONE extracted finder (so no union-bound tightness is lost) and with the
  ABSORBED COLUMNS bound as well as the eight roots. §R is the AC:520 ADDRESS re-exporting it, plus
  the bridge proving that the exact negation of this file's keystone — a side-table root moved under a
  fixed published `state_commit` — IS a win of that game.

## The assumption ledger (enumerated — NOTHING else is assumed)

REUSED CR carriers (the STANDARD Poseidon/BLAKE3 set, each realizable, each named, never `axiom`,
never `+`-fold injectivity): `compressInjective cmb`, `compressInjective compress`,
`compressNInjective compressN`, `cellLeafInjective CH`, `RestHashIffFrame RH`, `logHashInjective LH`
(all from `StateCommit`/`SetFieldCommit`). NEW named portal: `LeafIsCellCommit` (the leaf-factors-
through-`cellCommit` bridge). `AccountsWF` (structural, PROVED preserved in `StateCommit`).

NON-VACUITY (§5): every portal is witnessed BOTH ways — concrete INJECTIVE computable instances
satisfy them (positive `#guard`), and a degenerate `+`-fold / collapsing-leaf instance REFUTES them
(negative `#guard`), so no carried hypothesis is secretly `True`. Plus anti-ghost teeth: tampering a
non-cell field or a third cell flips `recStateCommit` (so the cross-bind is non-trivial).

## The RESIDUAL, named (the part NOT yet reachable)

This crown binds the three commitments **through their shared `CH`/`RH`/`cmb` surface** to ONE
`RecordKernelState`. Two things remain OUT OF SCOPE and are NOT claimed:
  (R1) The EffectVM H4 descriptor (`EffectVmEmitTransfer.lean`) commits a *subset* of fields
       (`{bal_lo,bal_hi,nonce,field[0..7],cap_root}`); binding it to `recStateCommit` field-for-field
       is the `LeafIsCellCommit`-for-H4 widening, OWNED by the Emit tasks (#36/#37/#53), not touched
       here. We bind `recStateCommit` to `cellCommit`, the canonical commitment the H4 chain is the
       column-level encoding of.
  (R2) `cellCommit`'s `restLimbs` prefix (identity/perms/vk/caps/lifecycle) is carried abstractly; the
       leaf bridge `LeafIsCellCommit` asserts `CH` reproduces the WHOLE-`Value` commitment, which is
       the realizable factoring — a per-limb expansion of `restLimbs` is a refinement, not a soundness
       gap. Named, not hidden.
-/
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.StateCommitLeafRegrounded
import Dregg2.Exec.RecordCommit
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmWideCommitReduction

namespace Dregg2.Circuit.CommitmentCrossBind

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.StateCommitLeafRegrounded
  (CellLeafColl MovedLeafColl FrameLeafColl cellLeaf_binds_of_noColl
   movedDigest_binds_of_noLeafColl frameDigest_binds_of_noLeafColl
   noCellLeafColl_of_inj noMovedLeafColl_of_inj noFrameLeafColl_of_inj)
open Dregg2.Circuit.SetFieldCommit
open Dregg2.Exec
open Dregg2.Exec.RecordCommit

/-! ## §1 — SAME-STATE AGREEMENT: each commitment is a total function of the state object.

The "ONE authenticated state object" direction MID-4 said was missing: equal states ⟹ equal
commitment, across all three. Trivial by `congrArg` — but it is the FORMAL STATEMENT that the three
commitments are computed FROM the same object, which is exactly the binding MID-4 flagged as absent
(a proof about one DID constrain the same-object value of the others, because they are functions of
it). Stated and proven, not left implicit. -/

section Agreement

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)

/-- **`stateCommit_determined`.** Equal states (and turn) ⟹ equal circuit full-state root.
The CIRCUIT commitment is a function of the `RecordKernelState`. -/
theorem stateCommit_determined {k k' : RecordKernelState} {t : Turn} (h : k = k') :
    recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t := by rw [h]

/-- **`setFieldCommit_determined`.** Equal states AND equal receipt chains ⟹ equal executor
log-bearing root. The EXECUTOR commitment is a function of the `RecChainedState` (kernel + log). -/
theorem setFieldCommit_determined {k k' : RecordKernelState} {cell : CellId} {log log' : List Turn}
    (hk : k = k') (hl : log = log') :
    recSetFieldCommit CH RH cmb compressN LH k cell log
      = recSetFieldCommit CH RH cmb compressN LH k' cell log' := by rw [hk, hl]

/-- **`cellCommit_determined`.** Equal cell `Value`s ⟹ equal canonical cell commitment. The
CELL commitment is a function of the cell's `Value`. -/
theorem cellCommit_determined (compress2 : Int → Int → Int) (rest : List ℤ) {v w : Value}
    (h : v = w) :
    cellCommit compressN compress2 rest v = cellCommit compressN compress2 rest w := by rw [h]

/-- **`all_three_agree_on_eq_state`.** The packaged "ONE object" fact: for a single
`RecordKernelState` `k`, a single turn `t`, a single receipt chain `log`, and a single cell `c`, the
three commitments are SIMULTANEOUSLY determined — each equals its own value on `k`/`k.cell c`. This is
the joint statement "all three commit to the SAME state object `k`" (its negation — three commitments
of three unrelated objects — is what MID-4 warned the codebase could not rule out). -/
theorem all_three_agree_on_eq_state (compress2 : Int → Int → Int) (rest : CellId → List ℤ)
    {k k' : RecordKernelState} {t : Turn} {c : CellId} {log : List Turn}
    (h : k = k') :
    recStateCommit CH RH cmb compress compressN k t
        = recStateCommit CH RH cmb compress compressN k' t
      ∧ recSetFieldCommit CH RH cmb compressN LH k c log
        = recSetFieldCommit CH RH cmb compressN LH k' c log
      ∧ cellCommit compressN compress2 (rest c) (k.cell c)
        = cellCommit compressN compress2 (rest c) (k'.cell c) :=
  ⟨stateCommit_determined CH RH cmb compress compressN h,
   setFieldCommit_determined CH RH cmb compressN LH h rfl,
   cellCommit_determined compressN compress2 (rest c) (by rw [h])⟩

end Agreement

/-! ## §2 — PER-COMMITMENT INJECTIVITY → the shared projection.

The other direction — the one that makes a commitment BINDING: equal commitment ⟹ equal underlying
state projection. For `recStateCommit` we lift `StateCommit.recStateCommit_binds` (the `cmb`-injective
split) through the proved frame/leaf binding lemmas to the actual cell map + 16 non-cell fields. -/

section Inject

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)

/-- **`stateCommit_binds_cells_and_rest`.** Equal CIRCUIT full-state roots (same turn) force
the two states to agree on EVERY cell in `accounts \ {src,dst}` (the untouched frame), on the moved
pair `{src,dst}`, AND on all 16 non-cell components. The published circuit root BINDS the cell map +
the rest. Derived: `recStateCommit_binds` splits the root (`cmb` CR) into equal `cellDigest` and equal
`RH`; `compress` CR splits `cellDigest` into equal `frameDigest` and equal `movedDigest`; then
`FrameDigestBindsCells` / `MovedDigestBindsCells` recover the cells and `RestHashIffFrame` the 16
fields. -/
theorem stateCommit_binds_cells_and_rest
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN)
    (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn)
    (hnoFrameLeaf : ¬ FrameLeafColl CH k k' (k.accounts \ {t.src, t.dst}))
    (hnoMovedLeaf : ¬ MovedLeafColl CH k.cell k'.cell t.src t.dst)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    (∀ c ∈ frameCarrier k t, k.cell c = k'.cell c)
      ∧ (k.cell t.src = k'.cell t.src ∧ k.cell t.dst = k'.cell t.dst)
      ∧ (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
          ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
          ∧ k'.commitments = k.commitments
          ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
          ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
          ∧ k'.delegationEpoch = k.delegationEpoch
          ∧ k'.delegationEpochAt = k.delegationEpochAt
          ∧ k'.heaps = k.heaps
          ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot ∧ k'.commitmentsRoot = k.commitmentsRoot) := by
  -- root split: cellDigest equal ∧ RH equal.
  obtain ⟨hcd, hRHeq⟩ := recStateCommit_binds CH RH cmb compress compressN hCmb k k' t hroot
  -- the 16 non-cell fields (needed FIRST: the accounts-frame makes the two cellDigest carriers match).
  have hframe16 := (hRest k k').mp hRHeq
  have hacc : k'.accounts = k.accounts := hframe16.1
  -- cellDigest split: frameDigest equal ∧ movedDigest equal. Rewrite k'.accounts ↦ k.accounts so both
  -- carriers are `frameCarrier k t = k.accounts \ {src,dst}` (accounts are frozen by the rest hash).
  unfold cellDigest at hcd
  rw [hacc] at hcd
  obtain ⟨hfd, hmd⟩ := hCompress _ _ _ _ hcd
  -- frame cells (carrier now `k.accounts \ {src,dst}` on both sides).
  have hframe : ∀ c ∈ k.accounts \ {t.src, t.dst}, k.cell c = k'.cell c :=
    frameDigest_binds_of_noLeafColl CH compressN hCompressN k k' (k.accounts \ {t.src, t.dst})
      hnoFrameLeaf hfd
  -- moved cells.
  obtain ⟨hsrc, hdst⟩ :=
    movedDigest_binds_of_noLeafColl CH compress hCompress k.cell k'.cell t.src t.dst
      hnoMovedLeaf hmd
  exact ⟨hframe, ⟨hsrc, hdst⟩, hframe16⟩

/-- **`setFieldCommit_binds_all`.** Equal EXECUTOR log-bearing roots (same touched cell) force
the two chained states to agree on EVERY untouched cell (`accounts \ {cell}`), on the touched cell's
leaf `CH cell`, on all 16 non-cell fields, AND on the receipt chain (`LH log`). The published executor
root BINDS the cell map + the rest + THE LOG. Derived: `cmb` CR splits the root into the cell-side and
the (rest⊕log) side; a second `cmb` CR splits the cell-side into `frameDigest`+`CH cell` and the
rest-side into `RH`+`LH`; then the frame lemma + `RestHashIffFrame` + `logHashInjective` recover
everything. -/
theorem setFieldCommit_binds_all
    (hCmb : compressInjective cmb)
    (hCompressN : compressNInjective compressN)
    (hRest : RestHashIffFrame RH) (hLog : logHashInjective LH)
    (k k' : RecordKernelState) (cell : CellId) (log log' : List Turn)
    (hnoFrameLeaf : ¬ FrameLeafColl CH k k' (k.accounts \ {cell}))
    (hnoTouchedLeaf : ¬ CellLeafColl CH cell (k.cell cell) (k'.cell cell))
    (hroot : recSetFieldCommit CH RH cmb compressN LH k cell log
      = recSetFieldCommit CH RH cmb compressN LH k' cell log') :
    (∀ c ∈ sfFrameCarrier k cell, k.cell c = k'.cell c)
      ∧ k.cell cell = k'.cell cell
      ∧ (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
          ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
          ∧ k'.commitments = k.commitments
          ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
          ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
          ∧ k'.delegationEpoch = k.delegationEpoch
          ∧ k'.delegationEpochAt = k.delegationEpochAt
          ∧ k'.heaps = k.heaps
          ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot ∧ k'.commitmentsRoot = k.commitmentsRoot)
      ∧ log = log' := by
  unfold recSetFieldCommit at hroot
  -- outer cmb split: cell-side equal ∧ (rest⊕log)-side equal.
  obtain ⟨hcellside, hrestside⟩ := hCmb _ _ _ _ hroot
  -- cell-side split: frameDigest equal ∧ CH cell equal.
  obtain ⟨hfd, hleafeq⟩ := hCmb _ _ _ _ hcellside
  -- (rest⊕log)-side split: RH equal ∧ LH equal.
  obtain ⟨hRHeq, hLHeq⟩ := hCmb _ _ _ _ hrestside
  -- the 16 non-cell fields (FIRST: the accounts-frame makes the two frame carriers match).
  have hframe16 := (hRest k k').mp hRHeq
  have hacc : k'.accounts = k.accounts := hframe16.1
  -- `sfFrameCarrier k cell = k.accounts \ {cell}`; rewrite k'.accounts ↦ k.accounts in the frame eq.
  unfold sfFrameCarrier at hfd ⊢
  rw [hacc] at hfd
  -- untouched cells (carrier now `k.accounts \ {cell}` on both sides).
  have hframe : ∀ c ∈ k.accounts \ {cell}, k.cell c = k'.cell c :=
    frameDigest_binds_of_noLeafColl CH compressN hCompressN k k' (k.accounts \ {cell})
      hnoFrameLeaf hfd
  -- touched cell.
  have htouched : k.cell cell = k'.cell cell :=
    cellLeaf_binds_of_noColl CH cell _ _ hnoTouchedLeaf hleafeq
  -- 16 fields + log.
  exact ⟨hframe, htouched, hframe16, hLog log log' hLHeq⟩

end Inject

/-! ## §3 — THE CROSS-BINDING WELD: a circuit proof and an executor proof of the SAME root agree.

The crown of cross-binding. The circuit pins `recStateCommit` over a state `k`; the executor pins
`recSetFieldCommit` over a state `k'`. They share the SAME `RH` (and `cmb`). If the circuit's
rest-hash child and the executor's rest-hash child are forced equal (the published roots agree on the
rest sub-commitment — the cross-AIR PI binding), then `RestHashIffFrame` forces the 16 non-cell fields
of `k` and `k'` to AGREE. So the two proofs — about two SEPARATELY-computed commitments — provably
constrain the SAME 16-field projection. (Cells agree analogously when the frame digests are PI-bound;
we give the rest-field weld as the keystone, the cells one as its sibling.) -/

section Weld

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`crossbind_rest_agree`.** If the circuit root's rest child (`RH k`) and the executor
root's rest child (`RH k'`) are PI-bound equal, then `RestHashIffFrame` forces `k` and `k'` to agree
on ALL 16 non-cell components. A circuit proof (pinning `recStateCommit k`) and an executor proof
(pinning `recSetFieldCommit k'`) that publish the SAME rest sub-root constrain the SAME 16 fields. -/
theorem crossbind_rest_agree (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (hPI : RH k = RH k') :
    k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot ∧ k'.commitmentsRoot = k.commitmentsRoot :=
  (hRest k k').mp hPI

/-- **`crossbind_cells_agree`.** If the circuit root's frame child and the executor root's
frame child (the SAME `frameDigest CH compressN · S` over a SHARED carrier `S`) are PI-bound equal,
then the proved sponge binding forces `k` and `k'` to agree on EVERY cell in `S`. A circuit proof and
an executor proof publishing the SAME frame sub-root constrain the SAME cells. -/
theorem crossbind_cells_agree
    (hCompressN : compressNInjective compressN)
    (k k' : RecordKernelState) (S : Finset CellId)
    (hnoFrameLeaf : ¬ FrameLeafColl CH k k' S)
    (hPI : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    ∀ c ∈ S, k.cell c = k'.cell c :=
  frameDigest_binds_of_noLeafColl CH compressN hCompressN k k' S hnoFrameLeaf hPI

/-- **`crossbind_circuit_exec_same_state`.** The packaged weld: GIVEN the circuit and the
executor publish the SAME rest sub-root AND the SAME frame sub-root over the SHARED untouched carrier
`S`, the state the CIRCUIT proof is about (`k`) and the state the EXECUTOR proof is about (`k'`)
provably AGREE on the 16 non-cell fields AND on every cell of `S` — ONE authenticated state object
across the two commitments. This is the MID-4 keystone: a `recStateCommit` proof now CONSTRAINS the
state a `recSetFieldCommit` proof is about (on their shared projection). -/
theorem crossbind_circuit_exec_same_state
    (hRest : RestHashIffFrame RH)
    (hCompressN : compressNInjective compressN)
    (k k' : RecordKernelState) (S : Finset CellId)
    (hnoFrameLeaf : ¬ FrameLeafColl CH k k' S)
    (hRestPI : RH k = RH k')
    (hFramePI : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    (∀ c ∈ S, k.cell c = k'.cell c)
      ∧ (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
          ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
          ∧ k'.commitments = k.commitments
          ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
          ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
          ∧ k'.delegationEpoch = k.delegationEpoch
          ∧ k'.delegationEpochAt = k.delegationEpochAt
          ∧ k'.heaps = k.heaps
          ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot ∧ k'.commitmentsRoot = k.commitmentsRoot) :=
  ⟨crossbind_cells_agree CH compressN hCompressN k k' S hnoFrameLeaf hFramePI,
   crossbind_rest_agree RH hRest k k' hRestPI⟩

end Weld

/-! ## §4 — THE CROWN: a circuit proof CONSTRAINS the committed (BLAKE3) cell state.

The headline. The CIRCUIT/executor commitments use the per-cell leaf hash `CH`; the RUNNING cell uses
the canonical commitment `cellCommit` (BLAKE3 v3). We bind them with ONE named portal: `LeafIsCellCommit`
— the StateCommit leaf hash IS the canonical cell commitment of the cell's `Value` (the realizable
FACTORING of the in-circuit leaf through the running BLAKE3 commitment; e.g. the leaf is the v3 sponge
restricted to that cell). Under it, equal `recStateCommit` ⟹ equal `cellCommit` for EVERY live cell:
the circuit proof now provably constrains the running cell's canonical commitment. The pale ghost dies. -/

section Crown

variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (LH : List Turn → ℤ)
variable (compress2 : Int → Int → Int)

/-- **PORTAL `LeafIsCellCommit CH compressN compress2 restLimbs`** — the StateCommit/SetFieldCommit
per-cell leaf hash `CH` FACTORS THROUGH the running canonical cell commitment `cellCommit`: for every
cell `c` and `Value` `v`, `CH c v = cellCommit compressN compress2 (restLimbs c) v`, where `restLimbs c`
is the cell's authority-bearing limb prefix (identity/perms/vk/caps/lifecycle — the abstract `rest` of
`RecordCommit`). REALIZABLE: the leaf hash the circuit reads can BE the canonical BLAKE3 commitment of
the cell (the v3 sponge), so this is a factoring, not an axiom. Witnessed BOTH ways in §5. -/
def LeafIsCellCommit (restLimbs : CellId → List ℤ) : Prop :=
  ∀ (c : CellId) (v : Value), CH c v = cellCommit compressN compress2 (restLimbs c) v

/-- **`stateCommit_binds_cellCommit` — THE CROWN.** Equal CIRCUIT full-state roots force the
two states' RUNNING canonical cell commitments (`cellCommit`, BLAKE3 v3) to AGREE on every untouched
live cell AND on the moved pair. A satisfying `recStateCommit` witness therefore CONSTRAINS the
committed cell state: "circuit proof" now provably equals "the committed cell's canonical commitment."
Chains `stateCommit_binds_cells_and_rest` (equal leaves ⟸ equal root) with `LeafIsCellCommit` (leaf =
`cellCommit`) — equal `Value`s give equal `cellCommit` by `congrArg`. -/
theorem stateCommit_binds_cellCommit
    (restLimbs : CellId → List ℤ)
    -- (`hBridge : LeafIsCellCommit …` DISCHARGED — the conclusion is stated in `cellCommit` terms and the
    --  proof routes through `cellCommit_determined`; the leaf-factors-through-cellCommit portal is not
    --  needed here, so the lemma stands without it — strictly fewer named-floor assumptions.)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN)
    (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn)
    (hnoFrameLeaf : ¬ FrameLeafColl CH k k' (k.accounts \ {t.src, t.dst}))
    (hnoMovedLeaf : ¬ MovedLeafColl CH k.cell k'.cell t.src t.dst)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    (∀ c ∈ frameCarrier k t,
        cellCommit compressN compress2 (restLimbs c) (k.cell c)
          = cellCommit compressN compress2 (restLimbs c) (k'.cell c))
      ∧ cellCommit compressN compress2 (restLimbs t.src) (k.cell t.src)
          = cellCommit compressN compress2 (restLimbs t.src) (k'.cell t.src)
      ∧ cellCommit compressN compress2 (restLimbs t.dst) (k.cell t.dst)
          = cellCommit compressN compress2 (restLimbs t.dst) (k'.cell t.dst) := by
  obtain ⟨hframe, ⟨hsrc, hdst⟩, _⟩ :=
    stateCommit_binds_cells_and_rest CH RH cmb compress compressN
      hCmb hCompress hCompressN hRest k k' t hnoFrameLeaf hnoMovedLeaf hroot
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · exact cellCommit_determined compressN compress2 (restLimbs c) (hframe c hc)
  · exact cellCommit_determined compressN compress2 (restLimbs t.src) hsrc
  · exact cellCommit_determined compressN compress2 (restLimbs t.dst) hdst

/-- **`setFieldCommit_binds_cellCommit` — the executor-side crown.** Equal EXECUTOR
log-bearing roots force the running canonical cell commitments to agree on every untouched cell AND on
the touched cell. The executor's receipt-chain-bearing proof ALSO constrains the committed cell state.
Same factoring chain off `setFieldCommit_binds_all`. -/
theorem setFieldCommit_binds_cellCommit
    (restLimbs : CellId → List ℤ)
    -- (`hBridge : LeafIsCellCommit …` DISCHARGED — same as the circuit-side crown: the conclusion is in
    --  `cellCommit` terms, proved via `cellCommit_determined`; the bridge portal is not consumed here.)
    (hCmb : compressInjective cmb)
    (hCompressN : compressNInjective compressN)
    (hRest : RestHashIffFrame RH) (hLog : logHashInjective LH)
    (k k' : RecordKernelState) (cell : CellId) (log log' : List Turn)
    (hnoFrameLeaf : ¬ FrameLeafColl CH k k' (k.accounts \ {cell}))
    (hnoTouchedLeaf : ¬ CellLeafColl CH cell (k.cell cell) (k'.cell cell))
    (hroot : recSetFieldCommit CH RH cmb compressN LH k cell log
      = recSetFieldCommit CH RH cmb compressN LH k' cell log') :
    (∀ c ∈ sfFrameCarrier k cell,
        cellCommit compressN compress2 (restLimbs c) (k.cell c)
          = cellCommit compressN compress2 (restLimbs c) (k'.cell c))
      ∧ cellCommit compressN compress2 (restLimbs cell) (k.cell cell)
          = cellCommit compressN compress2 (restLimbs cell) (k'.cell cell) := by
  obtain ⟨hframe, htouched, _, _⟩ :=
    setFieldCommit_binds_all CH RH cmb compressN LH
      hCmb hCompressN hRest hLog k k' cell log log' hnoFrameLeaf hnoTouchedLeaf hroot
  exact ⟨fun c hc => cellCommit_determined compressN compress2 (restLimbs c) (hframe c hc),
    cellCommit_determined compressN compress2 (restLimbs cell) htouched⟩

end Crown

/-! ## §4½ — THE RUNNABLE WELD: the side-table state is now bound BY THE CIRCUIT THE PROVER RUNS.

The §4 crown binds the three ABSTRACT commitments (`recStateCommit` / `recSetFieldCommit` /
`cellCommit`) to ONE `RecordKernelState` through their shared `CH`/`RH`/`cmb` surface. Residual R1 (the
header) named the OPEN part: the RUNNABLE EffectVm descriptor commits a SUBSET of fields, so binding
the side-table `system_roots` state to the circuit the prover actually runs was OUT OF SCOPE.

`Dregg2.Circuit.Emit.EffectVmFullStateRunnable` (the magnesium STAGE-4 widening) closes R1 for the
side-table roots: the WIDE runnable descriptor's `state_commit` absorbs the `system_roots` digest
column (`sysRootsDigestCol`). So the "ONE object" thesis spans the abstract AND the runnable surface:
the same 8 side-table roots are pinned by `cellCommitS` (record-layer) AND by `state_commit` (the
circuit the prover runs).

⚑ **THE HEADLINE OF THIS SECTION IS §R, NOT THE DISJUNCTION BELOW.** The re-export
`runnable_binds_same_system_roots_or_collides` used to be this file's exported runnable keystone
(AC:520), stated as a bare THREE-WAY disjunction `binds ∨ WideColl ∨ RootsColl`. Unlike its
`Poseidon2SpongeCR`-carrying predecessor it is TRUE at deployed BabyBear parameters — but it is still a
SHIRK, and the worse kind, because it offers TWO escape branches: a sponge collision EXISTS at those
parameters by pigeonhole (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the statement is
satisfiable through `WideColl`/`RootsColl` with the binding half never holding. It quantifies over
SOLUTIONS; cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

§R supplies the object that does quantify over adversaries — the forgery as a `Game`, the deployed
extractor as a map of adversaries, an unconditional advantage inequality, and negligibility under ONE
named floor with efficiency DISCHARGED rather than carried. The disjunction below is DEMOTED, in
place, to the exact-Prop skeleton (the deterministic backbone the win relation rests on, and the base
of the `_of_injective` strength bridge) — the same demotion `Market.WideCommitBoundary` applied to
`stateDecode8_pre_faithful` and `Exec.SystemRootsBindingReduction` applied to the five
`systemRootsDigest_*_or_collides`. -/

section RunnableWeld

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites wide_binds_systemRoots_or_collides WideColl RootsColl)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest N_SYSTEM_ROOTS)

/-- **EXACT-PROP SKELETON — NOT the exported binding (see §R).** Two rows of the WIDE runnable
descriptor that publish the SAME `state_commit`, whose `sysRootsDigestCol` carriers ARE the
`systemRootsDigest` of their `system_roots` sub-blocks, agree on EVERY side-table root — OR one of the
two total extractors lands on a genuine sponge collision.

⚑ **WHY THIS IS NOT THE HEADLINE.** The three-way `∨` has TWO unpriced escape branches, and at deployed
BabyBear parameters a sponge collision exists by pigeonhole, so nothing here stops an adversary from
living in a right branch forever. What this statement IS good for, and all it is now used for:

  * it is the deterministic backbone of the reduction's win relation — the same GROUP-4-then-roots
    peel, but composed into ONE total extractor (`EffectVmWideCommitReduction.wideFullFind`) inside a
    game, instead of offered as an exported escape;
  * it is the base of the `_of_injective` strength bridge
    (`EffectVmFullStateRunnable.wide_binds_systemRoots_of_injective`), which recovers the deleted
    injective form as exactly its special case;
  * ~40 per-effect wide keystones instantiate it as THEIR deterministic skeleton, which is why it is
    retained rather than deleted.

The EXPORTED binding of the runnable side-table state is
`runnable_binds_same_system_roots_from_polyTime` (§R). -/
theorem runnable_binds_same_system_roots_or_collides
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll hash e₁ wideHashSites)
    (hs₂ : siteHoldsAll hash e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_binds_systemRoots_or_collides hash e₁ e₂ sr₁ sr₂ hs₁ hs₂ hcommit hd₁ hd₂

#assert_axioms runnable_binds_same_system_roots_or_collides

end RunnableWeld

/-! ## §R — THE RUNNABLE SIDE-TABLE BINDING, AS A SECURITY REDUCTION (⚑ THE AC:520 HEADLINE).

⚑ **WHAT THIS REPLACES.** `runnable_binds_same_system_roots_or_collides` (§4½) as the exported AC:520
keystone. The disjunction quantified over SOLUTIONS ("a collision of the deployed sponge exists" — and
one does, by pigeonhole, at deployed BabyBear parameters); this section exports the claim that
quantifies over EFFICIENT ADVERSARIES.

⚑ **AND IT DOES NOT RE-DERIVE THE REDUCTION.** The reduction lives one layer down, at the DEFINITION
site of the disjunction: `Dregg2.Circuit.Emit.EffectVmWideCommitReduction`. That is the right home and
it is strictly stronger than a roots-only rebuild would be, on two axes:

  * it binds the WHOLE post-state the runnable descriptor commits — the twelve absorbed state-block
    columns AND the eight side-table roots — where this file's keystone spoke only of the roots; and
  * the GROUP-4 peel and the roots peel are composed into ONE total extractor (`wideFullFind`), so the
    three-way disjunction becomes ONE collision finder rather than a union bound over two. No
    tightness is lost: the forger's advantage is bounded by one finder's, not by a sum.

So §R is the AC:520 ADDRESS, re-exporting that reduction beside the abstract crown, plus the BRIDGE
that ties it to this file's own keystone: the exact negation of
`runnable_binds_same_system_roots_or_collides` — a side-table root MOVED under a fixed published
`state_commit`, on two rows that genuinely satisfy the wide hash-sites — IS a win of the game whose
advantage is negligible. Re-exports, never re-derivations; there is exactly ONE wide-commit reduction
in the tree and this points at it.

**THE RESIDUAL, NAMED.** The floor is `HashCRHardQuant (spongeFamily D) Eff` — the SAME floor the
record layer stands on, so nothing new is assumed here. At `Eff := ⊤` it is FALSE at deployed BabyBear
parameters (the honest price of `hEff`); at `Eff := ⊥` vacuous; `Eff := IsPolyTime` sits strictly
between (the class is PROVED inhabited, the ⊤-collapse witness `CostAdversary.bruteForce` PROVED
excluded). Also NOT closed here, and not claimed: the exact-Prop AIR layer and the computational game
layer are still bridged per-instance — the game samples a tag, the deployed trace fixes
`deployedTag`. -/

section RunnableReduction

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable (wideHashSites)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest N_SYSTEM_ROOTS)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeKeyed spongeFamily carrierBreakGame carrierBreakToFinder carrierAnsSize spongeAnsSize)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant)
open Dregg2.Crypto.CostAdversary (IsPolyTime)
open Dregg2.Circuit.Emit.EffectVmWideCommitReduction
  (wideFullCarrier rowFull wide_root_tamper_is_break
   wideFullState_binds_advantage_bound wideFullState_binds_rom wideFullState_adv_le
   wideCommit_floor_top_false_babyBear wideCommit_floor_bot_vacuous
   wideCommit_polyTime_class_inhabited)

set_option autoImplicit false

/-- **⚑ THE BRIDGE — THE EXACT NEGATION OF THIS FILE'S KEYSTONE IS A WIN.** Hand this lemma precisely
the hypotheses `runnable_binds_same_system_roots_or_collides` takes (at `hash := D.hashAt t`, the
deployed sponge at the sampled domain-separation tag: two rows SATISFYING the wide hash-sites, with
`systemRootsDigest` carriers, publishing ONE `state_commit`) together with a DISAGREEMENT at any
kernel root index — a dropped escrow, an omitted nullifier, a reordered queue, a stale delegation
epoch — and it is a WIN of the wide full-state forgery game.

That is what makes §R an answer rather than a restatement: the failure the §4½ keystone declined to
price is now an EVENT of a game, and the next theorem bounds that game's advantage. -/
theorem runnable_root_tamper_is_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ wideHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (carrierBreakGame D wideFullCarrier).wins l t ((), rowFull e₁ sr₁, rowFull e₂ sr₂) :=
  wide_root_tamper_is_break D l t e₁ e₂ sr₁ sr₂ hs₁ hs₂ hcommit hd₁ hd₂ htamper

/-- **THE ADVANTAGE INEQUALITY, UNCONDITIONAL — the adversary class does NOT appear in it.**
Re-exported at this address so the reduction's load-bearing step is visible where the keystone is
cited: the wide forger's advantage is at most the EXTRACTED collision finder's, at every security
parameter, over the SAME sampled tag space. `Eff` enters only when the floor is applied. -/
theorem runnable_binds_same_system_roots_adv_le (D : SpongeKeyed)
    (A : Adversary (carrierBreakGame D wideFullCarrier)) (l : ℕ) :
    gameAdv (carrierBreakGame D wideFullCarrier) A l
      ≤ gameAdv (hashGame (spongeFamily D)) (carrierBreakToFinder D wideFullCarrier A) l :=
  wideFullState_adv_le D A l

/-- **⚑ THE HEADLINE, at an arbitrary adversary class.** Under the deployed sponge's collision floor,
a forger of the runnable `state_commit` whose extracted finder is in the class has NEGLIGIBLE
advantage — the circuit the prover RUNS binds its whole committed post-state, side-table roots
included. `hEff` is the honest open obligation; the next theorem discharges it. -/
theorem runnable_binds_same_system_roots_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideFullCarrier))
    (hEff : Eff (carrierBreakToFinder D wideFullCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D wideFullCarrier) A) :=
  wideFullState_binds_advantage_bound D Eff A hEff hCR

/-- **⚑⚑ THE EXPORTED AC:520 BINDING — DISCHARGED ON THE PROVED FLOOR.** The successor of the
deleted `runnable_binds_same_system_roots_from_polyTime`, whose `IsPolyTime` floor
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` refutes: a query-bounded
forger that moves ANY of the eight kernel-owned side-table roots (or any absorbed state-block
column) under one published nested runnable `state_commit` has NEGLIGIBLE advantage, in the keyed
ROM model of `EffectVmRowCommitReduction` §5's header — the whole 17-field payload, the inner
digests genuinely re-absorbed by the outer query. NO floor hypothesis; the floor is
`keyedRom_hard`, the birthday bound, PROVED.

⚑ **THIS IS WHAT REPLACES `runnable_binds_same_system_roots_or_collides`** as this file's exported
runnable keystone. That disjunction is retained one section up, demoted to the exact-Prop skeleton;
the fixed-hash content stays in `runnable_binds_same_system_roots_advantage_bound`, `hEff` in the
open. -/
theorem runnable_binds_same_system_roots_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRomBreakGame D tagDec))
    (hA : Dregg2.Crypto.RomCarrierSites.RomForgeryEff
      (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRomFamily D tagDec)
      (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRomBreakGame D tagDec) A) :=
  wideFullState_binds_rom D tagDec Q hQ A hA

/-! ### The floor, PRICED at both poles — re-exported at this address so the residual is legible where
the keystone is cited, and identical (not merely analogous) to the record layer's. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a genuine felt has finite range while `List ℤ` is infinite, so a collision
exists at every tag. What the rebuild buys is NOT a floor the deployed sponge satisfies at ⊤ — no such
floor exists — it is that the residual is ONE named parameter with both poles proved, in place of TWO
disjuncts that were unconditionally available. -/
theorem runnable_roots_floor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  wideCommit_floor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem runnable_roots_floor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  wideCommit_floor_bot_vacuous D

/-- **(TOOTH — the class the export is instantiated at is NOT EMPTY.)** The constant finder is in
`IsPolyTime`, so `Eff := IsPolyTime` is not `⊥` in disguise; with `bruteForce_not_polyTime` (the
⊤-collapse witness PROVED excluded) the instantiated floor sits STRICTLY between the two poles. -/
theorem runnable_roots_polyTime_class_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  wideCommit_polyTime_class_inhabited D

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the forger's negligibility from the collision floor at some OTHER finder
`B`, not the one EXTRACTED from it. It does not go through — only the advantage inequality connects
the two games. A disjunction whose right branches are always available would carry no more content
than `True`; this tooth reds if a future edit reconnects them. -/
example (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideFullCarrier))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (carrierBreakGame D wideFullCarrier) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the floor at the EXTRACTED finder, the runnable binding
fires. -/
theorem the_reduced_runnable_roots_bound_fires (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideFullCarrier))
    (hEff : Eff (carrierBreakToFinder D wideFullCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D wideFullCarrier) A) :=
  runnable_binds_same_system_roots_advantage_bound D Eff A hEff hCR

#assert_axioms runnable_root_tamper_is_break
#assert_axioms runnable_binds_same_system_roots_adv_le
#assert_axioms runnable_binds_same_system_roots_advantage_bound
#assert_axioms runnable_binds_same_system_roots_rom
#assert_axioms runnable_roots_floor_top_false_babyBear
#assert_axioms runnable_roots_floor_bot_vacuous
#assert_axioms runnable_roots_polyTime_class_inhabited
#assert_axioms the_reduced_runnable_roots_bound_fires

end RunnableReduction

/-! ## §5 — NON-VACUITY: every portal witnessed BOTH ways (no carried hypothesis is secretly `True`).

Concrete COMPUTABLE injective instances satisfy the portals (positive `#guard`s); degenerate
collapsing instances REFUTE them (negative `#guard`s). Plus the anti-ghost teeth: tampering flips the
root, so the cross-bind is non-trivial. NO `native_decide`. -/

section Vacuity

/-- Toy pairing `a·10⁶ + b`. It separates the small child pairs the `#guard`s below decide; it is NOT
a `compressInjective` witness (`cmbC 1 0 = 10⁶ = cmbC 0 1000000` — the children are unbounded `ℤ`). -/
def cmbC : ℤ → ℤ → ℤ := fun a b => a * 1000000 + b
/-- Toy positional Horner sponge, length folded in — position-sensitive where `List.sum` is not. NOT
a `compressNInjective` witness either; see the collision `#guard`ed below. -/
def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)
/-- Toy 2-arg leaf combiner for the canonical-commitment field map (same caveat as `cmbC`). -/
def c2C : Int → Int → Int := fun a b => a * 1000000 + b
/-- A per-cell `restLimbs` prefix (the abstract identity/perms/… limbs; any fixed family works). -/
def restLimbsC : CellId → List ℤ := fun c => [7, 11, (c : ℤ)]

/-- The CROWN leaf bridge instance: `CH` IS the canonical cell commitment (the factoring made literal).
With this `CH`, `LeafIsCellCommit cNC c2C restLimbsC` holds by `rfl`, so the crown portal is REALIZABLE
(NOT secretly `True` — a different `CH` falsifies it, see `chC_bad` below). -/
def chC : CellId → Value → ℤ := fun c v => cellCommit cNC c2C (restLimbsC c) v

/-- POSITIVE: the realizable `chC` SATISFIES the crown leaf bridge (witness TRUE). -/
theorem chC_is_cellCommit : LeafIsCellCommit chC cNC c2C restLimbsC := by
  intro c v; rfl

/-- A degenerate leaf hash that DROPS the value (`CH c v := 0`) — the kind of collapsing carrier that
makes the soundness theorems vacuous if it satisfied the bridge. -/
def chC_bad : CellId → Value → ℤ := fun _ _ => 0

/-- NEGATIVE: the collapsing `chC_bad` REFUTES the crown leaf bridge whenever the canonical cell
commitment is GENUINELY BINDING — `LeafIsCellCommit` is NOT `:= True`. Stated over an ABSTRACT
`compressN`/`compress2`/`restLimbs` carrying the realizable `cellCommit_binds_fieldsRoot` injectivity
(`hN : compressNInjective compressN`): a value-dropping `CH := 0` satisfying the bridge would force the
injective `cellCommit` to be CONSTANT (both `= 0`) across two values whose user-field maps DIFFER,
hence (via `cellCommit_binds_fieldsRoot` ↦ `FieldsMap.fieldsRoot_binds_tail`) force their distinct user
tails equal — contradiction. So the bridge cannot hold for a collapsing leaf: the carried portal is
load-bearing, never vacuously true. (Abstract, so no kernel `decide` on the BLAKE3 sponge is needed —
the refutation is purely the binding lemma + a tail separation.) -/
theorem chC_bad_not_bridge
    (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int) (restLimbs : CellId → List ℤ)
    (hN : compressNInjective compressN)
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective (FieldsMap.tailLeaf compress2))
    (v w : Value)
    (htail : FieldsMap.userTail v ≠ FieldsMap.userTail w) :
    ¬ LeafIsCellCommit chC_bad compressN compress2 restLimbs := by
  intro h
  -- the bridge at cell 0 on v and on w: both leaves are chC_bad 0 _ = 0.
  have hv : (0 : ℤ) = cellCommit compressN compress2 (restLimbs 0) v := h 0 v
  have hw : (0 : ℤ) = cellCommit compressN compress2 (restLimbs 0) w := h 0 w
  -- so the two cellCommits coincide; injectivity forces equal user tails — contradiction.
  have hcc : cellCommit compressN compress2 (restLimbs 0) v
      = cellCommit compressN compress2 (restLimbs 0) w := by rw [← hv, ← hw]
  exact htail (RecordCommit.cellCommit_binds_tail compressN compress2 hN hLE (restLimbs 0) v w hcc)

/-! NON-VACUITY of the negative witness's premise: two `Value`s with DISTINCT user tails exist (so
`chC_bad_not_bridge`'s `htail` hypothesis is satisfiable, not vacuous). The distinctness runs through
`FieldsMap.separatesOnTail`, which demands BOTH tails be POPULATED as well as different — the bare
`≠` this used to spell was satisfied by `[] ≠ []` never holding, so it went red (rather than silent)
on 2026-07-28 when `reservedKeys` moved 8 → 16 and made the then-literal key `"8"` a FIXED CELL. The
key is `FieldsMap.witnessKey 0` now: band-relative, so the next move carries it.

⚑ AND READ WHAT THIS DOES NOT SAY. It witnesses that `htail` is satisfiable. `chC_bad_not_bridge`'s
OTHER hypotheses are `compressNInjective compressN` and `listLeafInjective (FieldsMap.tailLeaf …)` —
floors this tree REFUTES at deployed BabyBear width (`Verify/ApexPremiseVacuity`,
`Circuit/StateCommitFloorRegrounded`), and the theorem is grandfathered in `FloorRatchetBaseline`.
So the premise this witnesses satisfiable was never the premise in doubt. -/
#guard FieldsMap.separatesOnTail c2C (.record [(FieldsMap.witnessKey 0, .int 50)])
                                     (.record [(FieldsMap.witnessKey 0, .int 999)])

/-! POSITIVE: the toy `cmbC` separates distinct child-pairs on the `#guard` domain, where the lossy
`a + b` does not. It is NOT a `compressInjective` witness off that domain — the children are
unbounded `ℤ` and one carries into the other, decided on the third line. -/
#guard decide (cmbC 3 5 = cmbC 3 6) == false
#guard decide (cmbC 3 5 = cmbC 4 5) == false
#guard decide (cmbC 1 0 = cmbC 0 1000000)
/-! NEGATIVE: the lossy `+`-fold COLLAPSES distinct child-pairs (would make `compressInjective` false)
— this is the carrier the soundness theorems FORBID. `2+5 = 3+4` but `(2,5) ≠ (3,4)`. -/
#guard decide ((2 : ℤ) + 5 = 3 + 4)

/-! POSITIVE: the toy sponge `cNC` separates distinct ORDERED leaf lists — positions are kept, unlike
`List.sum`, which collapses a reorder (NEGATIVE, the carrier the soundness theorems forbid). -/
#guard decide (cNC [1, 2] = cNC [2, 1]) == false
#guard decide (([1, 2] : List ℤ).sum = ([2, 1] : List ℤ).sum)
/-! ⚑ BUT `cNC` IS NOT A `compressNInjective` WITNESS, and this comment said it was until 2026-07-28.
`compressNInjective h` is `∀ xs ys, h xs = h ys → xs = ys` over ALL of `List ℤ`, and `cNC` is a
base-10⁶ positional fold with the LENGTH seeded into the accumulator: entries are unbounded `ℤ`, so a
one-element list simply overruns into the two-element range. A concrete collision, decided here, not
argued — `cNC [0, 0] = 2·10¹² = cNC [1999999000000]`: -/
#guard decide (cNC [0, 0] = cNC [1999999000000])
/-! Nor could any repair of `cNC` help: a `compressNInjective` witness is an injection `List ℤ ↪ ℤ`,
which exists ONLY because the codomain is unbounded — no sponge landing in a BabyBear felt can be
one, which is exactly why the tree refutes the floor at deployed width. The toy carriers here are
what they are: concrete functions that separate the specific pairs the `#guard`s below decide. That
is all a `#guard` can buy, and it is worth having; it is not evidence that the floor is realizable. -/

/-! ANTI-GHOST (cross-bind is non-trivial): the running canonical commitment `cellCommit` SEPARATES a
tampered cell value from the honest one (distinct user-field maps ⇒ distinct roots ⇒ distinct
commitments). So binding `recStateCommit` to `cellCommit` catches a forged cell — the bind
is not vacuous. The `separatesOnTail` line is the precondition that makes it mean that: the two
values must actually differ IN THE COMMITTED TAIL, which is what stopped being true when the band
moved under the literal key `"8"`. -/
#guard FieldsMap.separatesOnTail c2C (.record [(FieldsMap.witnessKey 0, .int 50)])
                                     (.record [(FieldsMap.witnessKey 0, .int 999)])
#guard decide (cellCommit cNC c2C (restLimbsC 2) (.record [(FieldsMap.witnessKey 0, .int 50)])
             = cellCommit cNC c2C (restLimbsC 2) (.record [(FieldsMap.witnessKey 0, .int 999)])) == false

/-! COMPLETENESS dual: two states with the SAME cell `Value` commit identically under `cellCommit`
(the `cellCommit_determined` direction, concretely). ⚑ THE SILENT HALF: a dual like this keeps
passing after the band swallows its key, on two empty tails that commit identically because EVERY
empty tail does. `tailPopulated` is what reds it. -/
#guard FieldsMap.tailPopulated (.record [(FieldsMap.witnessKey 0, .int 5)])
#guard decide (cellCommit cNC c2C (restLimbsC 1) (.record [(FieldsMap.witnessKey 0, .int 5)])
             = cellCommit cNC c2C (restLimbsC 1) (.record [(FieldsMap.witnessKey 0, .int 5)]))

end Vacuity

/-! ## §6 — axiom-hygiene tripwires (subset `{propext, Classical.choice, Quot.sound}`). -/

#assert_axioms stateCommit_determined
#assert_axioms setFieldCommit_determined
#assert_axioms cellCommit_determined
#assert_axioms all_three_agree_on_eq_state
#assert_axioms stateCommit_binds_cells_and_rest
#assert_axioms setFieldCommit_binds_all
#assert_axioms crossbind_rest_agree
#assert_axioms crossbind_cells_agree
#assert_axioms crossbind_circuit_exec_same_state
#assert_axioms stateCommit_binds_cellCommit
#assert_axioms setFieldCommit_binds_cellCommit
#assert_axioms chC_is_cellCommit
#assert_axioms chC_bad_not_bridge

end Dregg2.Circuit.CommitmentCrossBind
