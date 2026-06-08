/-
# Dregg2.Circuit.Argus.Effects.BridgeMint — the INBOUND-BRIDGE-MINT weld: bridgeMint as an Argus IR term.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and `Argus/
Compile.lean` welded it to the circuit for transfer/mint/burn (single-cell) and createEscrow/refund/
release (the side-table escrow legs). This module welds the §8-PORTAL supply effect **bridgeMint** —
the inbound-bridge twin of mint — in its own disjoint file, replicating the mint/burn weld method
without touching any shared Argus file.

## Why bridgeMint targets the PER-ASSET ledger (the genuine interface difference from mint/burn)

mint/burn (`Argus/Compile.lean §M`) refine their IR terms to the RECORD-CELL supply executors
`recKMint`/`recKBurn` (`Exec/TurnExecutorFull.lean`), which credit/debit ONE cell's `balance` *field*
(via `recCreditCell`/`setCell`), projected by the transfer keystone's `cellProj` (reading `balOf`/
`nonceOf` of the cell record).

`bridgeMintA`, by contrast, is the §8-portal twin of the PER-ASSET mint: `execFullA`'s `.bridgeMintA`
arm dispatches to `recCMintAsset` verbatim (`Spec/supplycreation.lean`, `execFullA_bridgeMintA`), whose
kernel step is `recKMintAsset` — a credit on the per-ASSET ledger `bal : CellId → AssetId → ℤ` (via
`recBalCredit`), projected by the descriptor's own `cellProjA` (reading `k.bal c a`). So the faithful
IR term writes the `bal` ledger with the §A `setBal` primitive (the same shape createEscrow/refund use),
NOT the record-cell `setCell` mint/burn use. The executor the term refines to is therefore the per-asset
kernel step `recKMintAsset` — the exact `RecordKernelState → Option RecordKernelState` step the
descriptor's connector (`EffectVmEmitBridgeMint §7`, `cellProjA`) projects.

## What this module proves (the same two theorems as the mint weld, on the per-asset bridge shape)

  1. `interp_bridgeMintStmt_eq_recKMintAsset` — the executor IS the term: `interp` of the bridgeMint IR
     term is, on the nose, the verified per-asset kernel step `recKMintAsset` (= the `.bridgeMintA` arm's
     kernel image, `recCMintAsset`).
  2. `bridgeMint_compile_sound` — the weld: a satisfying witness of the AUDITED descriptor
     `bridgeMintVmDescriptor` (`EffectVmEmitBridgeMint`) agrees, per cell, with the post-state the IR
     term's executor produces, with the documented nonce-tick divergence carried explicitly.

## HONEST SURFACE (precise — do NOT over-read)

  * **PER-CELL / PER-(cell,asset) (the credited leg).** The runnable descriptor is a SINGLE-ROW AIR; its
    soundness pins ONE `(cell, asset)` ledger entry's transition + that row's commitment binding. We weld
    on `cellProjA k' cell a`, exactly the surface the descriptor's `§7` connector supports. The cross-cell
    global supply total (`recKMintAsset_delta`: asset `a`'s supply rises by `value`, every other asset
    frozen) is the executor's keystone, cited — NOT re-claimed per row here.

  * **The BRIDGE CryptoPortal proof (the inbound-value attestation) is NOT internalized in-circuit.** It
    is enforced at `execFullA`'s ADMISSION — the descriptor pins the ledger credit the arm commits,
    *conditional on the arm having committed* (the `= some k'` carries the portal, the conservation
    keystone). This module welds against the kernel STEP `recKMintAsset` (the local credit), so the portal
    is exactly the unmodelled boundary the descriptor already flags (`EffectVmEmitBridgeMint`, HONEST
    BOUNDARY) — stated, not hidden. (memory: bridgeMint's portal is enforced at executor admission.)

  * **The NONCE-TICK divergence is REAL and carried** (not papered): the descriptor's `CellBridgeMintSpec`
    TICKS the row nonce (`post.nonce = pre.nonce + 1`), while the per-asset ledger executor freezes the
    ledger entry's nonce — and `cellProjA` projects BOTH pre and post nonce to `0`, so the descriptor pins
    `0 + 1 = 1` against the executor's frozen `0`. `bridgeMint_compile_sound` exposes both facts as a final
    conjunct, identical to the burn/transfer welds (descriptor ticks the runtime counter; the ledger image
    freezes).

  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding, carried by the
    descriptor — cited, not re-claimed).

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `:= True`
vacuity, no weakening-that-just-typechecks: the conclusion is the genuine per-cell agreement the reused
descriptor soundness proves. Imports are read-only; this file owns only itself and edits no other Argus
module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint

namespace Dregg2.Circuit.Argus.Effects.BridgeMint

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState CellId AssetId mintAuthorizedB)
-- The per-asset privileged supply kernel step the bridgeMint arm refines to (`recKMintAsset`) + its
-- ledger-credit helper (`recBalCredit`) live in `TurnExecutorFull`. `mintAuthorizedB` is the
-- privileged-supply gate (`Dregg2.Exec.Generators`, reached via `open Dregg2.Exec`).
open Dregg2.Exec.TurnExecutorFull (recKMintAsset recBalCredit)

-- The bridge-mint gate is asset-AGNOSTIC (it checks privileged supply authority over the cell, not the
-- asset), so the asset arg `a` is deliberately unread in `bridgeMintGuard` — it is the credit BODY that
-- writes `(cell, a)`. Match the descriptor module's convention rather than rename the faithful signature.
set_option linter.unusedVariables false

/-! ## §1 — the gate + the body (the per-asset credit shape: gate, then a `setBal` ledger credit).

`recKMintAsset k actor cell a value` (`TurnExecutorFull.lean:686`) commits IFF the privileged-supply gate
holds (a `node`/`control` mint cap over `cell`, non-negative `value`, `cell` live), and on commit credits
the per-ASSET ledger entry `(cell, a)` by `value` (`bal := recBalCredit k.bal cell a value`). We render the
gate as a `Bool` over `k` and the credit as the §A `setBal` primitive (the per-asset write, exactly the
shape createEscrow/refund use) — NOT the record-cell `setCell` mint/burn use. -/

/-- The bridge-mint admissibility gate as a `Bool` — exactly `recKMintAsset`'s `if` (the privileged supply
gate: a `node`/`control` mint cap over `cell`, non-negative `value`, `cell` a live account). Identical to
the scalar `mintGuard`, because `recKMintAsset` checks the SAME conjunction as `recKMint` — the bridge
inbound credit is privileged supply. The foreign-finality portal is NOT a row of this gate (it is the
executor-admission/conservation-keystone hypothesis the descriptor flags). -/
def bridgeMintGuard (actor cell : CellId) (a : AssetId) (value : ℤ) (k : RecordKernelState) : Bool :=
  mintAuthorizedB k.caps actor cell
    && decide (0 ≤ value)
    && decide (cell ∈ k.accounts)

/-- The bridgeMint effect as an IR term: gate, then CREDIT the per-asset ledger entry `(cell, a)` by
`value` (a single `setBal` write). The per-asset analog of `mintStmt` — gate, then credit — but the move
writes the `bal` ledger (`recBalCredit`), the surface the descriptor's `cellProjA` reads. -/
def bridgeMintStmt (actor cell : CellId) (a : AssetId) (value : ℤ) : RecStmt :=
  RecStmt.seq (RecStmt.guard (bridgeMintGuard actor cell a value))
    (RecStmt.setBal (fun k => recBalCredit k.bal cell a value))

/-! ## §2 — the gate decodes to `recKMintAsset`'s admission, and `interp` of the term IS `recKMintAsset`.

Two ingredients, exactly as the mint cornerstone: (a) the `Bool` gate equals the kernel step's `if`
condition, and (b) the single-component `setBal` body reduces to the kernel's commit post-state
`{ k with bal := recBalCredit k.bal cell a value }`. -/

/-- The bridge-mint `Bool` gate decodes to `recKMintAsset`'s admissibility proposition (the SAME
conjunction `recKMint`/`mintGuard` use — privileged supply authority ∧ non-negativity ∧ cell-liveness). -/
theorem bridgeMintGuard_iff (actor cell : CellId) (a : AssetId) (value : ℤ) (k : RecordKernelState) :
    bridgeMintGuard actor cell a value k = true ↔
      (mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ k.accounts) := by
  simp only [bridgeMintGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **The cornerstone (per-asset bridge inbound).** `interp` of the bridgeMint term IS the verified
per-asset supply kernel step `recKMintAsset` — the same partial function, by construction, exactly as the
transfer/mint/burn cornerstones, now over the per-ASSET ledger (the surface the bridgeMint arm
`execFullA_bridgeMintA = recCMintAsset` projects, whose kernel step is `recKMintAsset`).

The proof opens the gate `if` on the IR side and `recKMintAsset`'s `if` on the executor side against the
SAME decoded conjunction (`bridgeMintGuard_iff`): on admit, the `setBal` body writes `bal := recBalCredit
k.bal cell a value`, exactly the kernel's commit post-state; on reject, both sides are `none`. -/
theorem interp_bridgeMintStmt_eq_recKMintAsset
    (actor cell : CellId) (a : AssetId) (value : ℤ) (k : RecordKernelState) :
    interp (bridgeMintStmt actor cell a value) k = recKMintAsset k actor cell a value := by
  simp only [bridgeMintStmt, interp]
  unfold recKMintAsset
  by_cases hg : bridgeMintGuard actor cell a value k = true
  · rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((bridgeMintGuard_iff actor cell a value k).mp hg)]
  · rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((bridgeMintGuard_iff actor cell a value k).mpr hp))]

#assert_axioms interp_bridgeMintStmt_eq_recKMintAsset

/-! ## §3 — NON-VACUITY of the cornerstone: the bridge-mint term genuinely CREDITS the ledger.

The cornerstone would be hollow if `bridgeMintStmt` never committed, or if the credit were a no-op. We
witness BOTH valences on a one-account kernel that grants account `0` a privileged mint cap over itself:
a `value = 30` inbound bridge of asset `0` commits and raises `(0, 0)`'s ledger entry `0 → 30`, while an
UNAUTHORIZED actor (no mint cap) rejects (`none`) — non-vacuous, two-valued. -/

/-- A one-account kernel (account `0` Live) that grants account `0` a privileged `node`-mint cap over
ITSELF (`Cap.node 0`, the supply authority `mintAuthorizedB` accepts), with an empty per-asset ledger. So
a bridge-mint authorized by `0` commits; the `bal` move is the only thing the witness exercises. -/
def kBM : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Dregg2.Authority.Cap.node 0] else [] }

/-- **`bridgeMintStmt_credits` — the inbound credit is OBSERVABLE.** Running the bridgeMint term for an
authorized `value = 30` inbound of asset `0` on `kBM` commits and raises the `(0, 0)` per-asset ledger
entry from `0` to `30` (via `recBalCredit`): the ledger credit is a real, observable state edit, not a
no-op. -/
theorem bridgeMintStmt_credits :
    (interp (bridgeMintStmt 0 0 0 30) kBM).map (fun k => k.bal 0 0) = some 30 := by
  rw [interp_bridgeMintStmt_eq_recKMintAsset]
  decide

/-- **`bridgeMintStmt_rejects_unauthorized` — fail-closed without supply authority.** A bridge-mint
attempted by an UNAUTHORIZED actor (account `1`, which holds no mint cap over cell `0`) rejects (`none`):
the privileged-supply gate genuinely fails closed (the cornerstone's two-valued, non-vacuous reject side
— the bridge inbound is gated, the foreign half is the carried portal). -/
theorem bridgeMintStmt_rejects_unauthorized :
    interp (bridgeMintStmt 1 0 0 30) kBM = none := by
  rw [interp_bridgeMintStmt_eq_recKMintAsset]
  decide

#assert_axioms bridgeMintStmt_credits
#assert_axioms bridgeMintStmt_rejects_unauthorized

/-! ## §4 — THE WELD: the audited descriptor agrees, per cell, with the IR term's executor interpretation.

The SAME shape as the mint/burn welds (`Argus/Compile.lean §M.2`): route the circuit side through the
audited `bridgeMintDescriptor_full_sound` (`EffectVmEmitBridgeMint §5`, which forces `CellBridgeMintSpec`)
and the executor side through the §2 cornerstone + a per-(cell,asset) projection of `recKMintAsset` onto
the descriptor's own `cellProjA`. The honest surface is PER-CELL (`cellProjA` of the credited
`(cell, asset)` entry), exactly as the descriptor's `§7` connector. The nonce-tick divergence (descriptor
ticks the row nonce; the ledger image freezes — and `cellProjA` zeroes both) is carried as a final
conjunct, like burn/transfer. We weld DIRECTLY against the descriptor's full-state soundness
(`bridgeMintDescriptor_full_sound`), the per-effect-farm vehicle, exactly as mint/burn weld against
`mintDescriptor_full_sound`/`burnDescriptor_full_sound`. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
  (bridgeMintVmDescriptor bridgeMintDescriptor_full_sound CellBridgeMintSpec IsBridgeMintRow cellProjA
   RowEncodes)

/-! ### §4.0 — `compileBridgeMint` — the effect-keyed circuit interpretation of the bridgeMint term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape — a
structural match cannot separate same-shaped effects), we name the bridgeMint circuit directly as the
audited descriptor. `compileBridgeMint = bridgeMintVmDescriptor` by `rfl`, so the circuit interpretation
of the bridgeMint term is, on the nose, the descriptor the Rust prover runs for the inbound-bridge-mint
effect. -/

/-- The circuit interpretation of the bridgeMint IR term: the audited runnable descriptor (per-row credit
on `bal_lo` + frame freeze + nonce tick, the post-state bound into `state_commit`). -/
def compileBridgeMint : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor := bridgeMintVmDescriptor

/-- **`compileBridgeMint_eq` — `compileBridgeMint` IS the audited runnable bridge-mint descriptor.**
Definitional. -/
theorem compileBridgeMint_eq : compileBridgeMint = bridgeMintVmDescriptor := rfl

#assert_axioms compileBridgeMint_eq

/-! ### §4.1 — the EXECUTOR-side per-(cell,asset) projection of the kernel step `recKMintAsset`.

The §2 cornerstone refines the IR term to `recKMintAsset` (the `RecordKernelState → Option
RecordKernelState` per-asset kernel step). We need its projection onto the descriptor's own
`cellProjA … cell a` — the `recKMintAsset` analog of mint's `recKMint_proj_balLo`: a committed per-asset
mint CREDITS the projected `(cell, a)` ledger entry by exactly `value` (`cellProjA.balLo` reads
`k.bal c a`, the measure `recBalCredit` moves). The frozen frame (balHi/nonce/fields/capRoot/reserved) is
`0 = 0` on both projections (`cellProjA` sends every non-`balLo` limb to `0`, definitional). -/

/-- **`recKMintAsset_proj_balLo`.** A committed per-asset mint credits the affected `(cell, a)` entry's
projected balance by exactly `value` (`cellProjA`'s `balLo` reads `k.bal c a`, the measure `recBalCredit`
moves). The per-(cell,asset) conserved leg the weld pins. -/
theorem recKMintAsset_proj_balLo {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {value : ℤ}
    (h : recKMintAsset k actor cell a value = some k') :
    (cellProjA k' cell a).balLo = (cellProjA k cell a).balLo + value := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    -- `(cellProjA { k with bal := recBalCredit … } cell a).balLo = recBalCredit k.bal cell a value cell a`
    show recBalCredit k.bal cell a value cell a = k.bal cell a + value
    unfold recBalCredit; rw [if_pos ⟨rfl, rfl⟩]
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms recKMintAsset_proj_balLo

/-! ### §4.2 — THE WELD. -/

/-- **`bridgeMint_compile_sound` — the welded soundness (bridgeMint slice, the §8-portal inbound supply
effect).**

Suppose, for the Argus bridgeMint term `bridgeMintStmt actor cell a value`:
  * the circuit `compileBridgeMint` (= the audited `bridgeMintVmDescriptor`) is SATISFIED on a genuine
    bridge-mint row (`hrow`) by `(env, true, true)` under the abstract Poseidon carrier `hash`, and its
    `RowEncodes` decoding NAMES the post-state record `post` over the credited cell's projection
    `cellProjA k cell a` with the bridged `value` (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (bridgeMintStmt …) k = some k'` (`hexec`).

Then the circuit's pinned post-state `post` AGREES with the executor's CREDITED `(cell, a)` projection
`cellProjA k' cell a` — the conserved `balLo` (credited by `value`) AND the whole frozen frame
(balHi/fields/capRoot/reserved each frozen); and the ONE documented divergence — the descriptor TICKS the
row nonce (`post.nonce = pre.nonce + 1`, and `cellProjA` zeroes the pre nonce so `post.nonce = 1`) while
the per-asset ledger executor FREEZES it (`cellProjA k' cell a).nonce = 0`) — is reported as the final
conjunct.

The bridge CryptoPortal proof (the inbound-value attestation) is NOT internalized in this single-row AIR;
it is the executor-admission hypothesis the `= some k'` carries (the conservation keystone) — the
unmodelled boundary the descriptor flags, stated not hidden. So the bridge-mint circuit the prover runs
pins the per-(cell,asset) credited state the IR term's executor produces, modulo the carried nonce-tick. -/
theorem bridgeMint_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeMintRow env)
    (k k' : RecordKernelState) (actor cell : CellId) (a : AssetId) (value : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA k cell a) value post)
    (hsat : satisfiedVm hash compileBridgeMint env true true)
    (hexec : interp (bridgeMintStmt actor cell a value) k = some k') :
    -- the conserved balance + the whole frame agree with the executor's credited (cell, asset) entry …
    ( post.balLo = (cellProjA k' cell a).balLo
      ∧ post.balHi = (cellProjA k' cell a).balHi
      ∧ (∀ i, post.fields i = (cellProjA k' cell a).fields i)
      ∧ post.capRoot = (cellProjA k' cell a).capRoot
      ∧ post.reserved = (cellProjA k' cell a).reserved )
    -- … and the ONE divergence: descriptor TICKS the row nonce, the ledger executor FREEZES it
    -- (`cellProjA` zeroes both, so the descriptor pins `0 + 1 = 1` against the executor's frozen `0`).
    ∧ ( post.nonce = (cellProjA k cell a).nonce + 1
        ∧ (cellProjA k' cell a).nonce = (cellProjA k cell a).nonce ) := by
  -- circuit side: `compileBridgeMint` IS `bridgeMintVmDescriptor`; the audited soundness forces
  -- `CellBridgeMintSpec` (balLo credited by `value`, frame frozen, nonce ticked).
  rw [compileBridgeMint_eq] at hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ :=
    (bridgeMintDescriptor_full_sound hash env hrow (cellProjA k cell a) post value henc hsat).1
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified `recKMintAsset`; its
  -- per-(cell,asset) projection gives the credited balLo (the frozen limbs are `0 = 0`).
  rw [interp_bridgeMintStmt_eq_recKMintAsset] at hexec
  have heLo := recKMintAsset_proj_balLo hexec
  -- the frozen-frame clauses agree because BOTH `cellProjA k cell a` and `cellProjA k' cell a` project the
  -- non-balance limbs to `0` (definitional `rfl`), so each `hc_ : post.X = (cellProjA k cell a).X` chains
  -- to `(cellProjA k' cell a).X` by `rfl`.
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl⟩, ?_, ?_⟩
  · rw [hcLo, heLo]                       -- balLo: pre + value (circuit) = pre + value (executor)
  · exact hcN                            -- nonce: descriptor TICKS (post = (cellProjA k cell a).nonce + 1)
  · rfl                                   -- the ledger executor FREEZES the projected nonce (0 = 0)

#assert_axioms bridgeMint_compile_sound

/-! ### §4.3 — NON-VACUITY: `compileBridgeMint` is the genuine runnable descriptor, not a placeholder.

The weld would be worthless if `compileBridgeMint` were an inert/empty descriptor. It is the full runnable
`bridgeMintVmDescriptor`, carrying the 13 + 14 + 4 + 3 + 1 = 35 constraints (credit + frame freeze +
transition + boundary + selector gate), 4 hash sites, and 2 range checks (an empty placeholder would have
0 / 0 / 0). So `bridgeMint_compile_sound` is a statement about a REAL circuit, not a vacuous placeholder. -/

/-- The compiled bridgeMint circuit is the NON-trivial runnable descriptor: it carries the
13+14+4+3+1 = 35 bridge-mint constraints / 4 hash sites / 2 range checks of the audited
`bridgeMintVmDescriptor`. So `bridgeMint_compile_sound` is about a genuine circuit. -/
theorem compileBridgeMint_nontrivial :
    compileBridgeMint.constraints.length = 35
    ∧ compileBridgeMint.hashSites.length = 4
    ∧ compileBridgeMint.ranges.length = 2 := by
  rw [compileBridgeMint_eq]
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms compileBridgeMint_nontrivial

end Dregg2.Circuit.Argus.Effects.BridgeMint
