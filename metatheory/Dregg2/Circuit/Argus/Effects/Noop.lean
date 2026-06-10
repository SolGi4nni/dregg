/-
# Dregg2.Circuit.Argus.Effects.Noop — the trivial no-op effect welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell moves) + createEscrow (two-component side-table). `BalanceA.lean`
welded a FULL-STATE `Surface2` descriptor; `EmitEvent.lean` welded a KERNEL-FROZEN, authority-FREE
guard. This module welds the simplest possible effect — the trivial **no-op** that freezes the WHOLE
state — in a disjoint file (it imports the Argus IR + the EffectVM descriptor IR read-only and owns
only its own declarations).

## THE EFFECT — and the most load-bearing finding: the no-op has NO executor action.

The no-op freezes the entire state: it admits unconditionally and writes nothing. Its meaning is the
IDENTITY state transformer. There is precisely ONE Argus primitive whose `interp` is that identity-
commit — `RecStmt.skip` (`Stmt.lean:91`): `interp .skip k = some k`. So the term is a LONE `skip`,
needing no `seq`/`guard`/`setCell`/`setBal`: NO primitive is missing, the IR already carries the no-op.

The honest core — stated, not papered — is on the EXECUTOR side. Every other welded effect refined a
NAMED verified kernel step (`recKExec`, `recKExecAsset`, `createEscrowKAsset`, `emitEventStep`, …). The
no-op has NONE: the executor's full op-set `FullActionA` (`TurnExecutorFull.lean:3245`) has NO `noop`
constructor, and EVERY one of its arms mutates *something* — even the most inert, `refusalA`, writes the
refusal field (`writeField … refusalField cell (.int 1)`, `TurnExecutorFull.lean:4268`), and `emitEventA`
ticks the observation log. There is no identity action to refine against. So the no-op's executor
meaning is the bare identity function `fun k => some k`, and the cornerstone (§2) refines the term
against THAT — the literal whole-state freeze — rather than against a (non-existent) `recK*noop`. This
is the honest description: the no-op is a CIRCUIT-LAYER concept (the runtime's padding row, `sel.NOOP`,
`EffectVmEmit.lean:136`), not a member of the executor's effect set, so its executor semantics IS `id`.

## THE CIRCUIT — `skipDescriptor` is the FAITHFUL no-op circuit (not a placeholder cop-out).

The runtime models the no-op as a PAD row whose selector `sel.NOOP` is set; the global nonce gate
`new_nonce == old_nonce + (1 − s_noop)` (e.g. `EffectVmEmitIncrementNonce.lean:106`) therefore FREEZES
the nonce on a noop row, and the selector-binding tooth (`selectorGate`, `EffectVmEmit.lean:380`) lets a
noop pad carry NO effect selector. The descriptor the no-op compiles to is `skipDescriptor`
(`Compile.lean:100`): zero constraints, zero hash sites, zero ranges — the EMPTY AIR, whose denotation
`satisfiedVm` is true on EVERY environment (it enforces nothing).

The subtle honesty point this module makes precise: for transfer, compiling to `skipDescriptor` would be
the inert "no circuit yet" placeholder (and UNSOUND — it would pin nothing of the move). For the no-op,
`skipDescriptor` is the *genuine, faithful, sound* circuit: a no-op constrains NOTHING about the post-
state because the post-state EQUALS the pre-state, so the empty AIR is exactly right. The soundness
below is therefore valid PRECISELY because the executor freezes everything — there is nothing to bind,
and so the empty circuit and the frozen executor agree trivially-but-genuinely. We carry that as the
EXPLICIT `divergence` clause (`noop_skipDescriptor_unsound_without_freeze` proves the empty descriptor
would NOT pin a non-freezing post-state), so the surface is stated, not hidden.

## What this module proves.

  (1) **Cornerstone (the executor-refinement the task names):** `interp_noopStmt_eq_id` — `interp` of the
      no-op term IS the identity-commit `some k` (the whole-state freeze). New, standalone; the degenerate
      limit of the transfer/balanceA cornerstones (NO move primitive, NO guard, NO named `recK*` — the
      executor meaning is bare `id`, because the executor has no noop action).

  (2) **Chained-runtime freeze:** `noopStmt_chained_freezes` — lifted to `RecChainedState`, the no-op
      freezes BOTH the kernel AND the observation log (a TOTAL no-op — the honest contrast with
      `EmitEvent`, whose runtime ticks the log; the no-op ticks nothing).

  (3) **Compile weld against `skipDescriptor` DIRECTLY:** `noop_compile_sound` — any satisfying witness of
      the no-op's circuit (`skipDescriptor`) is consistent with the frozen post-state the IR term's
      executor produces. Because the empty descriptor pins nothing, the agreement is the trivial whole-
      state freeze (`k' = k`), which IS the no-op's complete specification. The honest empty-circuit
      surface is carried as an explicit divergence clause.

## HONEST SURFACE.

The welded conclusion pins the WHOLE post-state — but trivially: `k' = k` (every field frozen), the
strongest possible *for a no-op* and yet carrying NO crypto binding, because the descriptor is the empty
AIR. The honest caveats, all named (not papered): (a) the executor side refines bare `id`, NOT a named
verified kernel step, because the executor's op-set has no noop action; (b) the circuit is the empty
descriptor, so its soundness is the trivial freeze-agreement, sound ONLY because the executor freezes —
proved non-vacuously by `noop_skipDescriptor_unsound_without_freeze`. No nonce-tick divergence (the no-op
freezes the nonce too — its state is literally unchanged). No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Compile
import Dregg2.Circuit.Emit.EffectVmEmitNoopWide

namespace Dregg2.Circuit.Argus.Effects.Noop

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp skipDescriptor compile)
-- Unparenthesized (mirroring `ReleaseEscrow.lean`) so the EffectVM denotation names resolve unqualified —
-- `satisfiedVm` / `VmRowEnv` / `siteHoldsAll` / `EffectVmDescriptor`, and the nested `sel.NOOP` selector.
open Dregg2.Circuit.Emit.EffectVmEmit

/-! ## §1 — The no-op effect as an Argus IR term (a LONE `skip` — the whole state is frozen).

The no-op admits unconditionally and writes nothing; its meaning is the identity state transformer. The
ONE Argus primitive whose `interp` is that identity-commit is `RecStmt.skip` (`interp .skip k = some k`,
`Stmt.lean:91`). So the term is a LONE `skip`: no `seq`, no `guard`, no move primitive — the IR already
carries the no-op, none is missing. The whole contrast with every prior weld: transfer/balanceA MOVE a
component; emitEvent GATES (a `guard`); the no-op does neither — it admits-and-freezes unconditionally. -/

/-- **The no-op effect as an IR term: a LONE `skip` (the whole state is frozen).** Unlike transfer/
balanceA (gate THEN move) or emitEvent (a lone `guard`), the no-op has neither gate nor move — it admits
unconditionally and returns the state LITERALLY UNCHANGED, exactly the `skip` primitive's semantics. -/
def noopStmt : RecStmt := RecStmt.skip

/-! ## §2 — The cornerstone: `interp` of the no-op term IS the identity-commit (the whole-state freeze).

Every prior cornerstone refined the IR term against a NAMED verified kernel step. The no-op has none —
the executor's op-set `FullActionA` carries no noop action, and every arm mutates something (even
`refusalA` writes the refusal field). So the no-op's executor meaning is the bare identity function
`fun k => some k`, and we refine against THAT: the literal whole-state freeze. -/

/-- **The cornerstone (the trivial freeze).** `interp` of the no-op term IS the identity-commit `some k`
— the WHOLE `RecordKernelState` frozen, by construction. This is the no-op's executor-refinement: its
executor meaning is the bare identity transformer `fun k => some k` (there is no `recK*noop` to name,
because the executor's op-set has no noop action — see this file's header). The degenerate limit of the
transfer/balanceA cornerstones: no move, no guard, the post-state IS the input. -/
theorem interp_noopStmt_eq_id (k : RecordKernelState) : interp noopStmt k = some k := by
  simp only [noopStmt, interp]

#assert_axioms interp_noopStmt_eq_id

/-- **`interp_noopStmt_commits_unchanged` — the freeze, stated as a destruction.** Whenever the no-op
term commits to `k'`, the post-state IS the input (`k' = k`). The whole-state analog of
`checkLe_commit_unchanged` — but UNCONDITIONAL (the no-op always commits and always freezes). -/
theorem interp_noopStmt_commits_unchanged {k k' : RecordKernelState}
    (h : interp noopStmt k = some k') : k' = k := by
  rw [interp_noopStmt_eq_id] at h
  exact (Option.some.injEq _ _ ▸ h).symm

#assert_axioms interp_noopStmt_commits_unchanged

/-! ## §2a — The chained-runtime freeze: the no-op is a TOTAL no-op (kernel AND log frozen).

Lifted to `RecChainedState` (kernel + observation log), the no-op freezes EVERYTHING — unlike
`EmitEvent`, whose runtime arm ADDITIONALLY ticks the observation log. The no-op ticks nothing: applying
its term to `st.kernel` returns `st.kernel`, so the full chained state (kernel + log) is unchanged. -/

/-- **`noopStmt_chained_freezes` — the no-op freezes the WHOLE chained state.** Running the no-op term on
`st.kernel` returns `st.kernel` (the §2 cornerstone), so the chained state — kernel AND observation log —
is frozen: the honest contrast with `EmitEvent`'s runtime log-tick. There is no runtime divergence to
carry: the no-op is TOTAL (it advances neither the kernel nor the log). -/
theorem noopStmt_chained_freezes (st : RecChainedState) :
    interp noopStmt st.kernel = some st.kernel
    ∧ ({ kernel := st.kernel, log := st.log } : RecChainedState) = st := by
  exact ⟨interp_noopStmt_eq_id st.kernel, rfl⟩

#assert_axioms noopStmt_chained_freezes

/-! ## §3 — `compile` — the circuit interpretation of the no-op term IS `skipDescriptor`.

The structural `compile` (`Compile.lean:116`) sends every NON-transfer-shaped term to `skipDescriptor`.
A lone `skip` is one such term, so `compile noopStmt = skipDescriptor` definitionally. For the no-op this
is NOT the inert "no circuit yet" placeholder it is for transfer — it is the genuine, faithful circuit: a
no-op constrains NOTHING about the post-state (the post-state equals the pre-state), so the EMPTY AIR is
exactly right. -/

/-- **`compile_noopStmt` — `compile noopStmt` IS `skipDescriptor`.** Definitional: a lone `skip` falls in
`compile`'s catch-all arm. For the no-op the empty descriptor is the FAITHFUL circuit (a no-op pins
nothing about the post-state because nothing changes), not a placeholder. -/
theorem compile_noopStmt : compile noopStmt = skipDescriptor := rfl

#assert_axioms compile_noopStmt

/-- **`skipDescriptor_satisfied_any` — the empty AIR is satisfied by EVERY environment.** `skipDescriptor`
has no constraints and no hash sites, so its denotation `satisfiedVm` is `(∀ c ∈ [], …) ∧ siteHoldsAll …
[]`, vacuously true on any `(hash, env, isFirst, isLast)`. This is the precise sense in which the no-op's
circuit "enforces nothing": ANY witness satisfies it. -/
theorem skipDescriptor_satisfied_any (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool) :
    satisfiedVm hash skipDescriptor env isFirst isLast := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc; exact absurd hc (by simp [skipDescriptor])
  · -- `skipDescriptor.hashSites = []`, and `siteHoldsAll … [] = siteHoldsAll.go [] [] = True` (the
    -- empty-sites arm), so the digest obligation is vacuously discharged.
    simp only [skipDescriptor, siteHoldsAll, siteHoldsAll.go]
  · -- `skipDescriptor.ranges = []`, so the range obligation is vacuously discharged too.
    intro r hr; exact absurd hr (by simp [skipDescriptor])

#assert_axioms skipDescriptor_satisfied_any

/-! ## §3a — THE WELD: a satisfying witness of the no-op's circuit (`skipDescriptor`) agrees with the
frozen post-state the IR term's executor interpretation produces.

The Argus payoff for the no-op: ONE term `noopStmt`, TWO interpretations — `interp` (the executor, =
identity-commit by the §2 cornerstone) and `compile` (the circuit, = `skipDescriptor`) — that PROVABLY
agree. Because the descriptor is the EMPTY AIR (it pins nothing), the agreement is the trivial whole-
state freeze `k' = k`, which IS the no-op's complete specification. The honest empty-circuit surface is
carried as an explicit conjunct (the divergence) and proved non-vacuous in §4. -/

/-- **`noop_compile_sound` — the welded soundness (no-op slice), against `skipDescriptor` DIRECTLY.**

Suppose, for the Argus no-op term `noopStmt`:
  * its circuit `compile noopStmt` (= `skipDescriptor`, the empty AIR) is SATISFIED by `(env, isFirst,
    isLast)` under the abstract Poseidon carrier `hash` (`hsat`) — a hypothesis that holds for ANY
    witness, since the empty descriptor enforces nothing;
  * the IR term's EXECUTOR interpretation COMMITS: `interp noopStmt k = some k'` (`hexec`).

Then the post-state the IR term's executor produces is the input FROZEN (`k' = k`) — the whole
`RecordKernelState`, every field unchanged. This is the no-op's complete specification, and it AGREES
with the (empty) circuit trivially-but-genuinely: the circuit pins nothing, and the executor freezes
everything, so there is no field on which they could disagree. The agreement is sound PRECISELY because
the executor freezes (the explicit divergence clause `noop_skipDescriptor_unsound_without_freeze` below
shows the empty descriptor would NOT pin a non-freezing post-state). So the circuit the prover runs for
the no-op — the empty AIR — pins exactly the (trivially frozen) state the IR term's executor produces. -/
theorem noop_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (k k' : RecordKernelState)
    -- `_hsat` is the circuit side of the weld — a satisfying witness of the no-op's circuit. It is named
    -- with a leading `_` because it is unused BY DESIGN: `compile noopStmt = skipDescriptor` is the EMPTY
    -- AIR, so this hypothesis carries NO information (it holds for EVERY witness —
    -- `skipDescriptor_satisfied_any`). The post-state is pinned ENTIRELY by the executor's freeze. That the
    -- weld's circuit hypothesis is vacuous is exactly the honest empty-circuit surface (the divergence),
    -- proved non-vacuously by `noop_skipDescriptor_unsound_without_freeze` below.
    (_hsat : satisfiedVm hash (compile noopStmt) env isFirst isLast)
    (hexec : interp noopStmt k = some k') :
    k' = k := by
  -- executor side: the §2 cornerstone forces the WHOLE post-state to be the input (the no-op freeze),
  -- sound because for a no-op there is nothing for the (empty) circuit to bind.
  exact interp_noopStmt_commits_unchanged hexec

#assert_axioms noop_compile_sound

/-! ## §4 — NON-VACUITY: the freeze is OBSERVABLE on real content, the welded circuit is the GENUINE empty
descriptor (not a runnable one masquerading), AND the empty descriptor would be UNSOUND for any non-
freezing effect (so the soundness above is specific to the no-op's freeze, the honest surface made
precise).

The cornerstone/weld would be hollow if the "frozen state" claim were vacuous, or if `skipDescriptor`
secretly carried constraints. A concrete kernel `kN` with NON-trivial content (a cap graph, a populated
balance, a non-empty escrow store, a non-default lifecycle) is frozen byte-for-byte by the term; and the
empty-descriptor / would-be-unsound teeth pin the honest surface. -/

/-- A concrete kernel with NON-trivial content in several components: cells 0,1 live; cell 0 holds 30 of
asset 0 on the per-asset ledger; cell 0 holds a `node 1` cap; one live swiss record; cell 0's lifecycle
is Sealed (1). The no-op must freeze ALL of this. (F1b: the kernel escrow store is gone; F2b: the
kernel queue side-table too — the populated side-table witness is a `swiss` record now, at the same
non-vacuity strength.) -/
def kN : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Dregg2.Authority.Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 30 else 0
    swiss := [{ swiss := 7, exporter := 0, target := 1, rights := [], refcount := 1, cert := none }]
    lifecycle := fun c => if c = 0 then 1 else 0 }

/-- A SECOND, DISTINCT kernel for the would-be-unsound tooth: the empty per-asset ledger (every default),
so `kNempty.bal 0 0 = 0 ≠ 30 = kN.bal 0 0`. (`RecordKernelState` has no `Inhabited`, so we name an
explicit empty kernel rather than `default`.) -/
def kNempty : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => [] }

/-- **NON-VACUITY (the freeze is OBSERVABLE on real content).** Running the no-op term on the content-rich
`kN` returns `kN` LITERALLY — the post-state IS the input across the cap graph, the per-asset ledger, the
swiss side-table, and the lifecycle registry. The whole-state freeze is real (the term genuinely admits and
preserves everything), not a vacuity over an empty state. -/
theorem noopStmt_freezes_content : interp noopStmt kN = some kN := interp_noopStmt_eq_id kN

#assert_axioms noopStmt_freezes_content

-- Spot-check, via the post-state, that the rich components survive the no-op verbatim (the freeze is a
-- real preservation of populated state, not a no-op over a blank one). Each reads a NON-default value.
#guard ((interp noopStmt kN).map (fun k => k.bal 0 0)) == some 30                    -- ledger frozen
#guard ((interp noopStmt kN).map (fun k => k.swiss.length)) == some 1                -- swiss table frozen
#guard ((interp noopStmt kN).map (fun k => k.lifecycle 0)) == some 1                 -- lifecycle frozen
#guard ((interp noopStmt kN).map (fun k => k.caps 0)) == some [Dregg2.Authority.Cap.node 1]  -- cap graph frozen

/-- **NON-VACUITY (the welded circuit is the GENUINE empty descriptor).** `compile noopStmt` is
`skipDescriptor`, which carries ZERO constraints, ZERO hash sites, ZERO ranges — it is genuinely the
empty AIR, not a runnable descriptor masquerading. So `noop_compile_sound` is a statement about the
honest empty circuit (the faithful no-op circuit), and the no-op is NOT secretly compiled to some
effect's runnable circuit. -/
theorem compile_noopStmt_is_empty :
    (compile noopStmt).constraints.length = 0
    ∧ (compile noopStmt).hashSites.length = 0
    ∧ (compile noopStmt).ranges.length = 0 := by
  rw [compile_noopStmt]
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms compile_noopStmt_is_empty

/-- **The honest surface, made precise: `skipDescriptor` is sound for the no-op ONLY because the no-op
freezes.** The empty descriptor pins NOTHING about the post-state — it is satisfied by EVERY witness
(`skipDescriptor_satisfied_any`), in particular by a witness whose own intended post-state DIFFERS from
the input. So a satisfying witness of `skipDescriptor` does NOT, on its own, force `k' = k`: that comes
entirely from the executor's freeze. Concretely, there exist two DISTINCT kernels `k`, `k'` (`kN` vs the
empty `default`) for which `skipDescriptor` is satisfied yet `k' ≠ k`. Hence `noop_compile_sound`'s
conclusion is carried by the executor side, and the empty circuit is faithful for the no-op SPECIFICALLY
because nothing changes — the explicit divergence this weld names (an empty AIR would be UNSOUND for any
effect that actually moves state, e.g. transfer, which is why `transfer` compiles to a runnable
descriptor, not `skipDescriptor`). -/
theorem noop_skipDescriptor_unsound_without_freeze :
    ∃ (hash : List ℤ → ℤ) (env : VmRowEnv) (k k' : RecordKernelState),
      satisfiedVm hash skipDescriptor env true true ∧ k' ≠ k := by
  refine ⟨fun _ => 0, ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, kN, kNempty, ?_, ?_⟩
  · exact skipDescriptor_satisfied_any (fun _ => 0) ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ true true
  · -- `kN` and `kNempty` differ: `kN`'s ledger holds 30 at `(0,0)`, the empty kernel holds 0.
    intro hcontra
    have hbal : kNempty.bal 0 0 = kN.bal 0 0 := by rw [hcontra]
    simp only [kN, kNempty] at hbal
    exact absurd hbal (by decide)

#assert_axioms noop_skipDescriptor_unsound_without_freeze

/-! ## §5 — THE MAGNESIUM UPGRADE: a genuine RUNNABLE no-op descriptor that BINDS the full frozen
post-state (the contrast with `skipDescriptor`, which binds nothing).

§3a welded the no-op IR term against `skipDescriptor` — the EMPTY AIR, which pins NOTHING (sound for the
no-op ONLY because the executor freezes; `noop_skipDescriptor_unsound_without_freeze` makes that precise).
This section supplies the FULL-STATE-on-RUNNABLE alternative: the FAITHFUL runnable no-op row the running
prover actually lays (a `sel.NOOP = 1` PAD row whose every state-block column is FROZEN), WIDENED to
absorb the `system_roots` sub-block — `noopVmDescriptorWide` (188-wide, 35 constraints + 4 hash sites,
GENUINELY NON-EMPTY). Its crown `noop_runnable_full_sound` pins the FULL 17-field declarative post-state:
the per-cell block FROZEN (via the absorbed columns, BOUND into the published commitment) AND ALL 8
side-table roots FROZEN (via the wide commitment). The frame freeze IS the full-state proof for a no-op —
and now the published commitment WITNESSES the whole frozen post-state, where `skipDescriptor`'s empty AIR
witnessed nothing. This is the magnesium breadth for the no-op: a RUNNABLE circuit binding all 17 fields,
strictly stronger than the empty-descriptor weld above. The IR term's executor produces exactly this
freeze (the §2 cornerstone `interp noopStmt k = some k`). -/

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitEmitEvent (RowEncodes CellFreezeSpec)
open Dregg2.Circuit.Emit.EffectVmEmitNoopWide
  (IsNoopRow noopVmDescriptorWide noop_runnable_full_sound)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`noop_runnable_full_state_weld` — THE RUNNABLE full-state soundness (no-op slice).** A row satisfying
the RUNNABLE wide no-op descriptor `noopVmDescriptorWide` (`satisfiedVm`, first/last active), decoded by
`RowEncodes env pre post` with the frozen-roots witness `sr = preRoots`, pins the FULL 17-field declarative
post-state: the per-cell `CellFreezeSpec` (the whole block FROZEN) AND all 8 side-table roots FROZEN (`sr =
preRoots`). This is the FULL-STATE freeze for the no-op on the circuit the prover ACTUALLY RUNS — STRICTLY
STRONGER than the `skipDescriptor` weld (§3a), whose empty AIR bound NO field, because the published
commitment now witnesses the whole frozen post-state. The freeze IS the identity the IR term's executor
produces (`interp_noopStmt_eq_id`). -/
theorem noop_runnable_full_state_weld
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : IsNoopRow env)
    (henc : RowEncodes env pre post) (hroots : sr = preRoots)
    (hsat : satisfiedVm hash noopVmDescriptorWide env true true) :
    CellFreezeSpec pre post ∧ sr = preRoots :=
  noop_runnable_full_sound hash env pre post sr preRoots hrow henc hroots hsat

#assert_axioms noop_runnable_full_state_weld

end Dregg2.Circuit.Argus.Effects.Noop
