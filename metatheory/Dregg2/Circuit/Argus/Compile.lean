/-
# Dregg2.Circuit.Argus.Compile — the SECOND interpretation of the Argus IR: the circuit.

`Argus/Stmt.lean` laid the cornerstone: a `RecStmt` term carries an executable interpretation
`interp` (the reference executor), and `interp (transferStmt turn) = recKExec` — the executor IS
the meaning of the term, by construction. This file builds the term's OTHER interpretation:
`compile : RecStmt → EffectVmDescriptor`, the EffectVM circuit the running prover (`EffectVmP3Air`)
executes. The Argus thesis is that ONE term has TWO interpretations that cannot drift; here we
validate the compile side end-to-end for the TRANSFER slice.

## What this file does — and what it deliberately REUSES rather than re-builds

The transfer circuit and its full soundness already EXIST and are audited:

  * `EffectVmEmitTransfer.transferVmDescriptor` — the runnable EffectVM transfer descriptor the
    Rust prover executes byte-identically (`satisfiedVm` is its denotation).
  * `EffectVmEmitTransferSound.transferDescriptor_full_sound` — satisfying that descriptor (under the
    `RowEncodes` decoding) forces the WHOLE per-cell `CellTransferSpec` post-state (balance signed
    move, balHi/8-fields/cap_root/reserved each frozen, nonce ticked) + the published commitment.
  * `EffectVmEmitTransferUnify.descriptor_agrees_with_executor_debit` — that descriptor's pinned
    post-state AGREES with the real executor `recKExec k t = some k'` on the SRC cell's projection
    (`cellProj`), per-cell, with the ONE documented nonce-tick divergence carried as a separate
    conjunct (the executor FREEZES the cell nonce; the EffectVM row TICKS it — `Unify` §2).

`compile` returns exactly that runnable descriptor for the transfer term (`compile_transferStmt`),
and `transfer_compile_sound` WELDS the existing agreement theorem to the Argus IR term by routing
the executor side through the cornerstone `interp_transferStmt_eq_recKExec`. So the statement reads:
*a satisfying witness of the circuit `compile (transferStmt turn)` agrees with the per-cell
post-state that the IR term `interp (transferStmt turn)` produces* — the same term, two
interpretations, provably aligned.

## HONEST SCOPE (precise — do NOT over-read)

  * PER-CELL (the SRC/debit leg). The runnable descriptor is a SINGLE-ROW AIR; its soundness pins ONE
    cell's transition + that cell's commitment binding. `interp`/`recKExec` is the multi-cell whole
    `RecordKernelState` transformer. We weld on the SRC cell's projection `cellProj k' t.src`, exactly
    the surface `descriptor_agrees_with_executor_debit` supports. The cross-cell two-sided conservation
    (debit-row ⊕ credit-row, net-zero mint) is the TURN-COMPOSITION layer (`Dregg2.Circuit.TurnEmit`);
    we CITE it and do not claim it here. The credit leg is the symmetric `cellProj k' t.dst`
    statement (`EffectVmEmitTransferUnify.unify_credit`), available by the same route.

  * The NONCE-TICK divergence is REAL and carried (not papered): the circuit ticks the cell nonce, the
    executor freezes it. `transfer_compile_sound` exposes both facts as a final conjunct, identical to
    the form `descriptor_agrees_with_executor_debit` already proves.

  * `compile` is TOTAL. Non-transfer-shaped terms map to a trivial empty descriptor (`skipDescriptor`,
    satisfied by everything — the honest meaning of "no circuit emitted yet"); only the transfer slice
    carries a real descriptor + soundness. The weld theorem is stated ONLY for the transfer term, where
    `compile` IS the audited runnable descriptor (`compile_transferStmt`, by `rfl`).

## Honesty

`#assert_axioms transfer_compile_sound` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no
`:= True` vacuity, no weakening-that-just-typechecks: the conclusion is the genuine per-cell
agreement the reused theorem proves. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitTransferUnify
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmEmitBurn

namespace Dregg2.Circuit.Argus

open Dregg2.Exec
-- The verified record-cell SUPPLY executors (and the single-cell credit they share) — the targets the
-- `mint`/`burn` cornerstones (`interp_mintStmt_eq_recKMint` / `…_recKBurn`) refine the IR terms to.
open Dregg2.Exec.TurnExecutorFull (recKMint recKBurn recCreditCell)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor IsTransferRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitTransferUnify
  (cellProj nonceOf setBalance_nonceOf debitParams descriptor_agrees_with_executor_debit)
-- The class-A mint/burn runnable descriptors + their per-cell full-state soundness (§M targets). Opened
-- WITHOUT their `RowEncodes`/`CellState`/`cellProjA` (those collide with the transfer-keystone names
-- already open above); those are named with their full path at use sites.
open Dregg2.Circuit.Emit.EffectVmEmitMint (mintVmDescriptor mintDescriptor_full_sound)
open Dregg2.Circuit.Emit.EffectVmEmitBurn (burnVmDescriptor burnDescriptor_full_sound IsBurnRow)

/-! ## §1 — The placeholder descriptor for terms whose circuit is not (yet) emitted.

`compile` is total. A term outside the transfer slice maps to `skipDescriptor`: zero constraints,
zero hash sites, zero ranges — the empty AIR, satisfied by EVERY environment. This is the honest
denotation of "no circuit emitted for this term yet" (it pins nothing), kept DISTINCT from the
transfer slice which carries the real runnable descriptor + full soundness. Extending the Argus
compile to another effect = replacing that effect's `skipDescriptor` arm with its runnable
descriptor + a weld theorem of the `transfer_compile_sound` shape. -/

/-- The empty EffectVM descriptor: no constraints, no hash sites, no range checks. Its denotation
`satisfiedVm` is vacuously true on any environment (it enforces nothing) — the honest "no circuit
yet" placeholder for the constructors above the transfer beachhead. -/
def skipDescriptor : EffectVmDescriptor where
  name        := "dregg-argus-skip-v0"
  traceWidth  := EFFECT_VM_WIDTH
  piCount     := 0
  constraints := []
  hashSites   := []
  ranges      := []

/-! ## §2 — `compile` — the circuit interpretation of a `RecStmt` term.

The transfer slice is `RecStmt.seq (.guard _) (.setCell _ _)` — exactly the shape `transferStmt`
emits (gate, then move the two balances). `compile` returns the audited runnable
`transferVmDescriptor` for that shape, so `compile (transferStmt turn)` reduces DEFINITIONALLY to
the real transfer circuit (`compile_transferStmt`, by `rfl`). Every other term shape (`skip`,
`guard`, a lone `setCell`/`setBal`/`insFresh`, or a `seq` not of the transfer shape) maps to the
`skipDescriptor` placeholder, keeping `compile` total and honest. -/
def compile : RecStmt → EffectVmDescriptor
  | .seq (.guard _) (.setCell _ _) => transferVmDescriptor
  | _ => skipDescriptor

/-- **`compile (transferStmt turn)` IS the audited runnable transfer descriptor.** Definitional:
`transferStmt turn = .seq (.guard (transferGuard turn)) (.setCell {src,dst} …)` matches the
transfer arm of `compile`. So the circuit interpretation of the transfer term is, on the nose, the
descriptor the Rust prover runs. -/
theorem compile_transferStmt (turn : Turn) :
    compile (transferStmt turn) = transferVmDescriptor := rfl

/-! ## §3 — THE WELD: a satisfying witness of `compile (transferStmt turn)` agrees with the
post-state the IR term's executor interpretation `interp (transferStmt turn)` produces.

This is the Argus payoff for transfer: ONE term `transferStmt turn`, TWO interpretations —
`interp` (the executor, = `recKExec` by the cornerstone) and `compile` (the circuit, =
`transferVmDescriptor`) — that PROVABLY agree. The executor side is routed through
`interp_transferStmt_eq_recKExec` (so the hypothesis `interp (transferStmt turn) k = some k'`
becomes the `recKExec k turn = some k'` that the reused `…_agrees_with_executor_debit` consumes);
the circuit side is the audited full per-cell soundness. The nonce-tick divergence is carried in
the final conjunct exactly as the reused theorem proves it (executor freezes, circuit ticks). -/

/-- **`transfer_compile_sound` — the welded soundness (transfer slice).**

Suppose, for the Argus transfer term `transferStmt turn`:
  * the circuit `compile (transferStmt turn)` is SATISFIED by `(env, true, true)` under the abstract
    Poseidon carrier `hash`, and its `RowEncodes` decoding NAMES the post-state record `post` over the
    SRC cell's projection `cellProj k turn.src` with the debit param block (`hsat`, `henc`, `hrow`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (transferStmt turn) k = some k'` (`hexec`).

Then the circuit's pinned post-state record `post` AGREES with the executor's SRC post-cell
projection `cellProj k' turn.src` on the conserved balance and the WHOLE frame (balHi, all 8 fields,
cap_root, reserved each frozen); and the ONE documented divergence — the circuit TICKS the cell
nonce while the executor FREEZES it (`Unify` §2) — is reported as the final conjunct. So the circuit
the prover runs for transfer pins the per-cell state the IR term's executor produces. -/
theorem transfer_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (turn : Turn) (post : CellState)
    (henc : RowEncodes env (cellProj k turn.src) (debitParams turn) post)
    (hrow : IsTransferRow env)
    (hsat : satisfiedVm hash (compile (transferStmt turn)) env true true)
    (hexec : interp (transferStmt turn) k = some k') :
    -- the conserved balance + the whole frame agree with the executor's SRC post-cell …
    ( post.balLo = (cellProj k' turn.src).balLo
      ∧ post.balHi = (cellProj k' turn.src).balHi
      ∧ (∀ i, post.fields i = (cellProj k' turn.src).fields i)
      ∧ post.capRoot = (cellProj k' turn.src).capRoot
      ∧ post.reserved = (cellProj k' turn.src).reserved )
    -- … and the ONE divergence: circuit TICKS the cell nonce, executor FREEZES it (Unify §2).
    ∧ ( post.nonce = (cellProj k turn.src).nonce + 1
        ∧ (cellProj k' turn.src).nonce = (cellProj k turn.src).nonce ) := by
  -- circuit side: `compile (transferStmt turn)` IS `transferVmDescriptor`, so the satisfaction
  -- hypothesis is over the audited runnable descriptor.
  rw [compile_transferStmt] at hsat
  -- executor side: the cornerstone turns the IR term's `interp` into the verified `recKExec`.
  rw [interp_transferStmt_eq_recKExec] at hexec
  -- the reused per-cell circuit⟺executor agreement, with everything now over the right surfaces.
  exact descriptor_agrees_with_executor_debit hash env k k' turn post henc hrow hsat hexec

#assert_axioms transfer_compile_sound

/-! ## §4 — NON-VACUITY: `compile` does NOT collapse the transfer term to the empty placeholder.

The weld would be worthless if `compile (transferStmt turn)` were the inert `skipDescriptor`. It is
not: it is the full runnable transfer descriptor, which carries 14 + 14 + 4 + 3 + 1 = 36 constraints,
4 hash sites, and 2 range checks — none of which `skipDescriptor` has. So the soundness above is
about a REAL circuit, not the vacuous placeholder. -/

/-- The compiled transfer circuit is the NON-trivial runnable descriptor, not the empty placeholder:
it carries the 36 transfer constraints / 4 hash sites / 2 range checks (`skipDescriptor` has none).
So `transfer_compile_sound` is a statement about a genuine circuit. -/
theorem compile_transferStmt_nontrivial (turn : Turn) :
    (compile (transferStmt turn)).constraints.length = 36
    ∧ (compile (transferStmt turn)).hashSites.length = 4
    ∧ (compile (transferStmt turn)).ranges.length = 2
    ∧ (compile (transferStmt turn)).constraints ≠ skipDescriptor.constraints := by
  rw [compile_transferStmt]
  refine ⟨by decide, by decide, by decide, ?_⟩
  -- transferVmDescriptor has 36 constraints; skipDescriptor has 0 — different lengths ⇒ unequal.
  intro h
  have : (transferVmDescriptor.constraints).length = (skipDescriptor.constraints).length := by
    rw [h]
  simp only [skipDescriptor, List.length_nil] at this
  exact absurd this (by decide)

#assert_axioms compile_transferStmt_nontrivial

/-! ## §M — GENERALIZING THE WELD TEMPLATE TO THREE CLASS-A EFFECTS (mint, burn).

The transfer weld (§3) validated the template for ONE effect. This section validates that it is
MECHANICAL across class-A effects by replaying it for `mint` and `burn` — the two privileged-supply
effects whose runnable descriptors (`mintVmDescriptor`/`burnVmDescriptor`) and per-cell full-state
soundness (`mintDescriptor_full_sound`/`burnDescriptor_full_sound`) already exist and are audited
(`EffectVmEmitMint`/`EffectVmEmitBurn`), and whose IR cornerstones (`interp_mintStmt_eq_recKMint` /
`interp_burnStmt_eq_recKBurn`, `Stmt.lean §M`) already refine the terms to the verified record-cell
supply executors `recKMint`/`recKBurn`.

### A REAL INTERFACE FINDING — the structural `compile` cannot separate three same-shaped effects.

`transferStmt`, `mintStmt`, and `burnStmt` are ALL `RecStmt.seq (.guard _) (.setCell _ _)`: a gate,
then a `setCell` move (`Stmt.lean:119/191/198`). So the structural arm
`.seq (.guard _) (.setCell _ _) => transferVmDescriptor` of `compile` (§2) ALREADY matches the mint and
burn terms — `compile (mintStmt …)` and `compile (burnStmt …)` BOTH reduce to `transferVmDescriptor`
(verified: both hold by `rfl`). A pure structural `RecStmt → EffectVmDescriptor` cannot map them to
three distinct descriptors, because the three terms differ ONLY in their `guard` predicate and the
`setCell` leaf — opaque closures a `match` cannot branch on (mint vs burn differ solely by `+amt`
vs `+(-amt)` inside the leaf, indistinguishable for symbolic `amt`). This is faithful to the running
prover, which does NOT dispatch on raw statement shape either: `generate_effect_vm_trace` switches on a
per-effect SELECTOR (`sel.NOOP`/`selM.MINT`/`selB.BURN`, `columns.rs`). So the honest generalization
keys the compiler on the EFFECT, not the term shape.

`compileE : ArgusEffect → EffectVmDescriptor` is that effect-keyed compiler: it returns the audited
runnable descriptor for each effect tag, so `compileE .mint`/`.burn`/`.transfer` reduce DEFINITIONALLY
(`compile_mintStmt`/`compile_burnStmt`/`compileE_transfer`, by `rfl`) to the exact circuits the prover
runs. The structural `compile`/`transfer_compile_sound` above are LEFT INTACT as the transfer
beachhead; `compileE` is the per-effect-farm vehicle that scales to all class-A effects without the
collision. -/

/-- The class-A effect tags `compileE` dispatches on (the Lean image of the running prover's per-effect
selector). `other` is every constructor with no runnable descriptor emitted yet. -/
inductive ArgusEffect where
  | transfer
  | mint
  | burn
  | other

/-- **`compileE`** — the EFFECT-keyed circuit interpretation (the honest generalization of `compile`
past the transfer beachhead). Each tag maps to its audited runnable descriptor; `other` maps to the
`skipDescriptor` placeholder. Unlike the structural `compile`, this separates the three same-shaped
supply/transfer effects (which a `RecStmt`-structural match provably cannot — see §M header). -/
def compileE : ArgusEffect → EffectVmDescriptor
  | .transfer => transferVmDescriptor
  | .mint     => mintVmDescriptor
  | .burn     => burnVmDescriptor
  | .other    => skipDescriptor

/-- **`compile_mintStmt` — `compileE .mint` IS the audited runnable mint descriptor.** Definitional: the
mint tag maps to `mintVmDescriptor`, the descriptor the Rust prover runs for the supply-mint effect (the
`compileE` analog of `compile_transferStmt`). -/
theorem compile_mintStmt : compileE .mint = mintVmDescriptor := rfl

/-- **`compile_burnStmt` — `compileE .burn` IS the audited runnable burn descriptor.** Definitional. -/
theorem compile_burnStmt : compileE .burn = burnVmDescriptor := rfl

/-- `compileE .transfer` IS the audited runnable transfer descriptor — the §3 beachhead, re-exposed on
the effect-keyed compiler (so all three class-A effects sit on the SAME `compileE` surface). -/
theorem compileE_transfer : compileE .transfer = transferVmDescriptor := rfl

#assert_axioms compile_mintStmt
#assert_axioms compile_burnStmt
#assert_axioms compileE_transfer

/-! ### §M.1 — The EXECUTOR-side per-cell projections of `recKMint`/`recKBurn`.

The transfer weld routed its executor side through `EffectVmEmitTransferUnify`'s
`descriptor_agrees_with_executor_debit`, whose unification (`unify_debit`) projects `recKExec` onto one
cell via `cellProj`. There is NO such pre-built unify lemma for the RECORD-CELL supply executors
`recKMint`/`recKBurn` (the existing `EffectVmEmitMint/Burn.descriptor_agrees_with_executor` theorems
unify against the per-ASSET ledger executors `recCMintAsset`/`recCBurnAsset` over `cellProjA`, a DIFFERENT
executor + projection than the `recKMint`/`recKBurn` the IR cornerstone produces). So we supply the two
missing projection facts here — the `recKMint`/`recKBurn` analogs of `proj_src_balLo`/`proj_nonce_frozen`
— reusing the SAME `cellProj` the transfer weld uses (it reads `balOf`/`nonceOf` of the cell record,
exactly the measure `recCreditCell`/`setBalance` move/freeze). This is the only genuine interface
difference from transfer, adapted faithfully. -/

/-- **`recKMint_proj_balLo`.** A committed record mint credits the affected cell's projected balance by
exactly `amt` (`cellProj`'s `balLo` reads `balOf`, the measure `recCreditCell` moves). -/
theorem recKMint_proj_balLo {k k' : RecordKernelState} {actor cell : CellId} {amt : ℤ}
    (h : recKMint k actor cell amt = some k') :
    (cellProj k' cell).balLo = (cellProj k cell).balLo + amt := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show balOf (recCreditCell k.cell cell amt cell) = balOf (k.cell cell) + amt
    unfold recCreditCell; rw [if_pos rfl, setBalance_balOf]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`recKMint_proj_nonce`.** A committed record mint FREEZES the affected cell's projected nonce
(`recCreditCell` rewrites only the `balance` field; `setBalance_nonceOf` leaves the `nonce` field
untouched). This is why mint has NO nonce-tick divergence — the descriptor freezes too. -/
theorem recKMint_proj_nonce {k k' : RecordKernelState} {actor cell : CellId} {amt : ℤ}
    (h : recKMint k actor cell amt = some k') :
    (cellProj k' cell).nonce = (cellProj k cell).nonce := by
  unfold recKMint at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show nonceOf (recCreditCell k.cell cell amt cell) = nonceOf (k.cell cell)
    unfold recCreditCell; rw [if_pos rfl, setBalance_nonceOf]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`recKBurn_proj_balLo`.** A committed record burn DEBITS the affected cell's projected balance by
exactly `amt` (`recCreditCell … (-amt)`). -/
theorem recKBurn_proj_balLo {k k' : RecordKernelState} {actor cell : CellId} {amt : ℤ}
    (h : recKBurn k actor cell amt = some k') :
    (cellProj k' cell).balLo = (cellProj k cell).balLo - amt := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt
      ∧ amt ≤ balOf (k.cell cell) ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show balOf (recCreditCell k.cell cell (-amt) cell) = balOf (k.cell cell) - amt
    unfold recCreditCell; rw [if_pos rfl, setBalance_balOf]; ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`recKBurn_proj_nonce`.** A committed record burn FREEZES the affected cell's projected nonce
(`setBalance` touches only `balance`). The executor-side input to burn's nonce-tick divergence (the
descriptor TICKS, the executor FREEZES — carried explicitly in `burn_compile_sound`). -/
theorem recKBurn_proj_nonce {k k' : RecordKernelState} {actor cell : CellId} {amt : ℤ}
    (h : recKBurn k actor cell amt = some k') :
    (cellProj k' cell).nonce = (cellProj k cell).nonce := by
  unfold recKBurn at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt
      ∧ amt ≤ balOf (k.cell cell) ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show nonceOf (recCreditCell k.cell cell (-amt) cell) = nonceOf (k.cell cell)
    unfold recCreditCell; rw [if_pos rfl, setBalance_nonceOf]
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms recKMint_proj_balLo
#assert_axioms recKMint_proj_nonce
#assert_axioms recKBurn_proj_balLo
#assert_axioms recKBurn_proj_nonce

/-! ### §M.2 — THE WELDS: a satisfying witness of `compileE .mint`/`.burn` agrees, per cell, with the
post-state the IR term's executor interpretation produces.

The SAME shape as `transfer_compile_sound`: route the circuit side through `compile_mintStmt`/
`compile_burnStmt` + the audited `…Descriptor_full_sound`, and the executor side through the cornerstone
`interp_mintStmt_eq_recKMint` / `interp_burnStmt_eq_recKBurn` + the §M.1 projections. The honest surface
is PER-CELL (`cellProj` of the affected cell), exactly as transfer (the descriptors are single-row AIRs;
the global supply total is the TURN-COMPOSITION layer, cited by the Emit modules' §8½ — NOT a per-cell
gap). Mint MATCHES on the nonce (descriptor freezes, executor freezes — no divergence); burn carries the
nonce-tick divergence as a final conjunct (descriptor ticks, executor freezes — `Burn` §7, like
transfer). -/

/-- **`mint_compile_sound` — the welded soundness (mint slice).**

Suppose, for the Argus mint term `mintStmt actor cell amt`:
  * the circuit `compileE .mint` (= `mintVmDescriptor`) is SATISFIED by `(env, true, true)` under the
    abstract Poseidon carrier `hash`, and its `RowEncodes` decoding NAMES the post-state record `post`
    over the affected cell's projection `cellProj k cell` (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (mintStmt actor cell amt) k = some k'`.

Then the circuit's pinned post-state `post` AGREES with the executor's post-cell projection
`cellProj k' cell` on the conserved balance (credited by `amt`) AND the WHOLE frame (balHi, the 8
fields, cap_root, reserved each frozen) AND the nonce — mint has NO divergence (both the descriptor and
`recKMint` freeze the cell nonce, `Mint` §HONEST-BOUNDARY). So the circuit the prover runs for mint pins
the per-cell state the IR term's executor produces. -/
theorem mint_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ) (post : CellState)
    (henc : Dregg2.Circuit.Emit.EffectVmEmitMint.RowEncodes env (cellProj k cell) amt post)
    (hsat : satisfiedVm hash (compileE .mint) env true true)
    (hexec : interp (mintStmt actor cell amt) k = some k') :
    post.balLo = (cellProj k' cell).balLo
    ∧ post.balHi = (cellProj k' cell).balHi
    ∧ (∀ i, post.fields i = (cellProj k' cell).fields i)
    ∧ post.capRoot = (cellProj k' cell).capRoot
    ∧ post.reserved = (cellProj k' cell).reserved
    -- mint MATCHES on the nonce (no transfer-style divergence): both freeze the cell nonce.
    ∧ post.nonce = (cellProj k' cell).nonce := by
  -- circuit side: `compileE .mint` IS `mintVmDescriptor`, so the audited soundness forces `CellMintSpec`.
  rw [compile_mintStmt] at hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := (mintDescriptor_full_sound hash env (cellProj k cell)
    post amt henc hsat).1
  -- executor side: the cornerstone turns the IR term's `interp` into the verified `recKMint`.
  rw [interp_mintStmt_eq_recKMint] at hexec
  have heLo := recKMint_proj_balLo hexec
  have heN := recKMint_proj_nonce hexec
  -- the frozen-frame clauses agree because BOTH `cellProj k cell` and `cellProj k' cell` project the
  -- non-balance limbs to `0` (definitional `rfl`), so `hc_ : post.X = (cellProj k cell).X` chains to
  -- `(cellProj k' cell).X` by `rfl`.
  refine ⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl, ?_⟩
  · rw [hcLo, heLo]                       -- balLo: pre + amt (circuit) = pre + amt (executor)
  · rw [hcN, heN]                         -- nonce: post = pre.nonce (freeze) = (cellProj k' cell).nonce

/-- **`burn_compile_sound` — the welded soundness (burn slice).**

Suppose, for the Argus burn term `burnStmt actor cell amt`:
  * the circuit `compileE .burn` (= `burnVmDescriptor`) is SATISFIED on a genuine burn row (`hrow`) by
    `(env, true, true)` under `hash`, and its `RowEncodes` decoding NAMES `post` over `cellProj k cell`;
  * the IR term's executor COMMITS: `interp (burnStmt actor cell amt) k = some k'`.

Then `post` AGREES with the executor's post-cell `cellProj k' cell` on the conserved balance (DEBITED by
`amt`) and the whole frame (balHi/8 fields/cap_root/reserved each frozen); and the ONE divergence — the
descriptor TICKS the cell nonce while `recKBurn` FREEZES it (`Burn` §7, identical to transfer's §2) — is
reported as the final conjunct. So the burn circuit the prover runs pins the per-cell state the IR term's
executor produces, modulo the carried nonce-tick. -/
theorem burn_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (k k' : RecordKernelState) (actor cell : CellId) (amt : ℤ) (post : CellState)
    (henc : Dregg2.Circuit.Emit.EffectVmEmitBurn.RowEncodes env (cellProj k cell) amt post)
    (hsat : satisfiedVm hash (compileE .burn) env true true)
    (hexec : interp (burnStmt actor cell amt) k = some k') :
    ( post.balLo = (cellProj k' cell).balLo
      ∧ post.balHi = (cellProj k' cell).balHi
      ∧ (∀ i, post.fields i = (cellProj k' cell).fields i)
      ∧ post.capRoot = (cellProj k' cell).capRoot
      ∧ post.reserved = (cellProj k' cell).reserved )
    -- … and the ONE divergence: descriptor TICKS the cell nonce, executor FREEZES it (Burn §7).
    ∧ ( post.nonce = (cellProj k cell).nonce + 1
        ∧ (cellProj k' cell).nonce = (cellProj k cell).nonce ) := by
  -- circuit side: `compileE .burn` IS `burnVmDescriptor`; the audited soundness forces `CellBurnSpec`.
  rw [compile_burnStmt] at hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ :=
    (burnDescriptor_full_sound hash env hrow (cellProj k cell) post amt henc hsat).1
  -- executor side: the cornerstone turns the IR term's `interp` into the verified `recKBurn`.
  rw [interp_burnStmt_eq_recKBurn] at hexec
  have heLo := recKBurn_proj_balLo hexec
  have heN := recKBurn_proj_nonce hexec
  -- frozen frame: both projections send the non-balance limbs to `0`, so each `hc_` chains by `rfl`.
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl⟩, ?_, ?_⟩
  · rw [hcLo, heLo]                       -- balLo: pre − amt (circuit) = pre − amt (executor)
  · rw [hcN]                              -- the descriptor TICKS the nonce (post = pre.nonce + 1)
  · exact heN                             -- the executor FREEZES the nonce

#assert_axioms mint_compile_sound
#assert_axioms burn_compile_sound

/-! ### §M.3 — NON-VACUITY: `compileE` does NOT collapse mint/burn to the empty placeholder.

As with transfer (§4), the welds would be worthless if `compileE .mint`/`.burn` were the inert
`skipDescriptor`. They are not: each is the full runnable descriptor (mint: 13+14+4+3 = 34 constraints,
4 hash sites, 2 ranges; burn: + the selector gate = 35), none of which `skipDescriptor` has. So
`mint_compile_sound`/`burn_compile_sound` are about REAL circuits. -/

/-- The compiled mint/burn circuits are the NON-trivial runnable descriptors, not the empty placeholder
(mint carries 34 constraints / 4 hash sites / 2 ranges; burn 35 / 4 / 2; `skipDescriptor` has 0 / 0 / 0).
So the §M.2 welds are statements about genuine circuits, not the vacuous placeholder. -/
theorem compileE_mint_burn_nontrivial :
    (compileE .mint).constraints.length = 34
    ∧ (compileE .mint).hashSites.length = 4
    ∧ (compileE .burn).constraints.length = 35
    ∧ (compileE .burn).hashSites.length = 4
    ∧ (compileE .mint).constraints ≠ skipDescriptor.constraints
    ∧ (compileE .burn).constraints ≠ skipDescriptor.constraints := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro h
    have : (mintVmDescriptor.constraints).length = (skipDescriptor.constraints).length := by
      rw [show mintVmDescriptor.constraints = skipDescriptor.constraints from h]
    simp only [skipDescriptor, List.length_nil] at this
    exact absurd this (by decide)
  · intro h
    have : (burnVmDescriptor.constraints).length = (skipDescriptor.constraints).length := by
      rw [show burnVmDescriptor.constraints = skipDescriptor.constraints from h]
    simp only [skipDescriptor, List.length_nil] at this
    exact absurd this (by decide)

#assert_axioms compileE_mint_burn_nontrivial

/-- **The structural-collision finding, as a theorem (§M header).** The structural `compile` maps BOTH
the mint and burn IR terms to `transferVmDescriptor` — it CANNOT separate the three same-shaped effects
(`.seq (.guard _) (.setCell _ _)`). This is exactly why the effect-keyed `compileE` (not structural
`compile`) is the faithful generalization. Pinned so the finding cannot silently regress. -/
theorem compile_collapses_mint_burn_to_transfer (actor cell : CellId) (amt : ℤ) :
    compile (mintStmt actor cell amt) = transferVmDescriptor
    ∧ compile (burnStmt actor cell amt) = transferVmDescriptor :=
  ⟨rfl, rfl⟩

#assert_axioms compile_collapses_mint_burn_to_transfer

end Dregg2.Circuit.Argus
