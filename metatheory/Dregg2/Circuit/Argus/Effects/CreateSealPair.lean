/-
# Dregg2.Circuit.Argus.Effects.CreateSealPair — the CREATE-SEAL-PAIR capability effect welded into the
Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell moves) and on createEscrow (a two-component side-table move).
`Effects/Delegate.lean` welded the first CAP-GRAPH effect (a single `setCaps` write of a `grant …` map);
`Effects/BalanceA.lean` welded against a FULL-STATE Surface2 `*_full_sound` (the WHOLE 17-field
post-state). This module welds CREATE-SEAL-PAIR (`apply_create_seal_pair`, `apply.rs:2675`) — a second
CAP-GRAPH effect, and like balanceA it carries a genuine Surface2 full-state descriptor, so we PREFER the
stronger BalanceA surface (conclude the WHOLE `CreateSealPairSpec`), not the per-cell EffectVM projection.

## The executor primitive, unfolded (read off the CODE)

The chained arm `execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder)` is DIRECTLY
`createSealPairChainA s pid actor sealerHolder unsealerHolder` (`TurnExecutorFull.lean:3868` — NO
`acceptsEffects` pre-gate, unlike balanceA's `recCexecAsset`), which is (`TurnExecutorFull.lean:1837`):

    createSealPairChainA s pid actor sealerHolder unsealerHolder
      = if stateAuthB s.kernel.caps actor sealerHolder = true then
          some { kernel := { s.kernel with
                              caps := grant (grant s.kernel.caps sealerHolder (sealerCap pid))
                                            unsealerHolder (unsealerCap pid) },
                 log    := { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 }
                         :: s.log }
        else none

So a committed create-seal-pair:

  * **GUARD** `stateAuthB s.kernel.caps actor sealerHolder = true` — `actor` holds authority over
    `sealerHolder` (the writer of the pair).
  * **TOUCHED `caps`** ← `createSealPairCaps … pid sealerHolder unsealerHolder` (= the double `grant`):
    `sealerHolder` gains the sealer cap `sealerCap pid`, `unsealerHolder` gains the unsealer cap
    `unsealerCap pid` — TWO real c-list grants, a genuine sealer/unsealer KEYPAIR
    (`createSealPairCaps_correct`: the two caps are GENUINELY DISTINCT — `[grant]` vs `[reply]` rights).
  * **FRAME** every other `RecordKernelState` component literally unchanged (`caps` is the one touched
    field; in particular `sealedBoxes` is FRAMED — a fresh pair holds no box yet). So the IR body is
    `seq (guard …) (setCaps …)`, exactly the §A cap-graph write primitive (the `Delegate` shape).

This is the AUTHORITY-gated double grant the INDEPENDENT full-state spec
`Spec.SealPairCreation.CreateSealPairSpec` validates against `execFullA`/`createSealPairChainA` BOTH ways
(`createSealPair_iff_spec`); `createSealPairCaps caps pid sealerHolder unsealerHolder
:= grant (grant caps sealerHolder (sealerCap pid)) unsealerHolder (unsealerCap pid)` is its validated
post-`caps` map (`createSealPairCaps_correct`), which we reuse VERBATIM as the `setCaps` leaf.

## ⚑ THE KERNEL-vs-RUNTIME DIVERGENCE (the precise, carried report — NOT papered)

There are TWO create-seal-pair executor surfaces, and they DISAGREE on ONE conjunct:

  * **the CHAINED `createSealPairChainA`** (`TurnExecutorFull.lean:1837`) — the arm `execFullA` ACTUALLY
    routes to, and the one `CreateSealPairSpec`/`createSealPair_iff_spec` validates. It gates ONLY on
    `stateAuthB actor sealerHolder`. NO pid-freshness check.
  * **the kernel-layer `EffectHandler` step `createSealPairStep`** (`Exec/Handlers/Seal.lean:100`) — the
    R3-CLOSING wrapper, gates on `stateAuthB ∧ pidFresh` (`findSealedBox … = none`). This ADDS a conjunct
    the chained executor LACKS (the R3 hole: reusing a pid that already binds a box lets a stale unsealer
    open the new pair's box).

We refine the IR term against the CHAINED executor's kernel projection (gating ONLY on `stateAuthB`),
because that is what `execFullA` runs and what the audited Surface2 descriptor `createSealPairA_full_sound`
+ spec corner `createSealPair_iff_spec` speak about — matching the descriptor we weld to. The
pidFresh-ABSENT fact is carried as an explicit theorem (`createSealPairKStep_no_pidFresh_gate`, §6), so the
chained-vs-handler divergence is a WITNESSED divergence, not a hidden one. (Welding against the R3 handler
instead would have NO Surface2 descriptor of its own; the v2 descriptor is keyed on the chained executor.)

## The circuit side — the audited Surface2 FULL-STATE descriptor (the BalanceA surface)

The circuit is `Inst.CreateSealPairA.createSealPairE` (the v2 `EffectSpec2` whose touched component is the
WHOLE `caps` slot-function, a `funcComponent` full-function digest) + its soundness
`createSealPairA_full_sound : satisfiedE2 … (createSealPairE D hD) … ⟹ CreateSealPairSpec` — a FULL
17-field declarative post-state agreement, keyed on the CHAINED executor via the independent
`createSealPair_iff_spec`. So this weld concludes the WHOLE post-state `CreateSealPairSpec` (the double cap
grant + the log + every other kernel field frozen), strictly STRONGER than a per-cell EffectVM projection
— exactly the BalanceA surface. The post-`caps` clause is FULL function equality, so a tamper of ANY
holder's slot (a third party's authority) is REJECTED, not merely "the two recipients gained a cap".

## What the weld pins (HONEST SURFACE — do NOT over-read)

`createSealPair_compile_sound`: a satisfying witness of the Surface2 circuit `createSealPairE` (under the
realizable portals `RestIffNoCaps`/`logHashInjective`/`Function.Injective D`) and a COMMITTING executor
run of the IR term AGREE on the WHOLE chained post-state `st' = { kernel := k', log := receipt :: st.log }`
— all 17 kernel fields + the receipt log. The `caps`-component digest portal (`Function.Injective D`, the
realizable Poseidon-CR bar for the whole-`caps`-function hash) enters ONLY inside the reused
`createSealPairA_full_sound`, not in the welded conclusion's statement.

This effect has NO nonce-tick divergence at THIS (Surface2 universe-A) layer: `CreateSealPairSpec` is a
`RecChainedState` predicate with no per-cell nonce field, so the post-state is pinned EXACTLY (the
nonce-tick is purely the runtime EffectVM-cell-bookkeeping leg of the OTHER, per-cell descriptor universe,
which this module does not weld to). The ONLY carried divergence is the kernel-vs-runtime pidFresh gate
above.

## Honesty

`#assert_axioms` on the cornerstone + the weld ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR /
whole-`caps`-function digest enters ONLY inside the reused `createSealPairA_full_sound` (its
`Function.Injective D` hypothesis), never in the welded conclusion's statement. No `sorry`, no `:= True`,
no `native_decide`, no `rfl`-posing-as-bridge (the chained-kernel bridge is PROVED). Non-vacuity teeth: the
IR term genuinely INSTALLS the keypair (observable double cap-graph write), the two granted caps are
GENUINELY DISTINCT, it genuinely REJECTS an unauthorized writer (fail-closed), and the welded descriptor is
the genuine Surface2 full-state one (full `caps`-function equality), not the inert placeholder. Imports are
read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.createSealPairA

namespace Dregg2.Circuit.Argus.Effects.CreateSealPair

open Dregg2.Exec
open Dregg2.Authority (Caps Cap Auth Label)
-- The CHAINED create-seal-pair executor `createSealPairChainA`, the seal-cap helpers, AND the unified
-- action executor `execFullA` all live in `Dregg2.Exec.TurnExecutorFull`; opened broadly (as BalanceA
-- does) so the §0 bridge / §3 chained lift / IR leaf can name them unqualified. (`grant` is in
-- `Dregg2.Exec`, already opened above.)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/createSealPairA.lean` so the standalone-descriptor names resolve unqualified
-- (`logHashInjective` lives in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`).
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.SealPairCreation
  (CreateSealPairSpec CreateSealPairGuard createSealPairCaps createSealPairReceipt
   createSealPairCaps_correct createSealPair_iff_spec)
open Dregg2.Circuit.Inst.CreateSealPairA
  (CreateSealPairArgs RestIffNoCaps createSealPairE createSealPairA_full_sound)

set_option autoImplicit false

/-! ## §0 — THE KERNEL TARGET: the create-seal-pair kernel step, and its bridge to the audited chained
executor.

The Argus `interp` produces `Option RecordKernelState` (the bare kernel). The chained executor
`createSealPairChainA` lives over `RecChainedState` (kernel + receipt log). So — exactly as
`Effects/CreateCommittedEscrow.lean` re-founds its committed kernel step + PROVES the chained bridge — we
DEFINE the kernel projection here and prove (not assert) that the audited chained executor IS this step
(plus the receipt-log stamp). The kernel step gates ONLY on `stateAuthB` (the chained executor's gate; the
R3 pidFresh divergence is carried in §6), rewriting `caps` to `createSealPairCaps`. -/

/-- **`createSealPairKStep`** — the create-seal-pair KERNEL step: the authority gate `stateAuthB caps actor
sealerHolder` (the writer of the pair), then the double cap-grant `createSealPairCaps` (sealer cap to
`sealerHolder`, unsealer cap to `unsealerHolder`). bal-NEUTRAL (edits ONLY `caps`). This is the kernel
projection of the audited chained `createSealPairChainA` (bridge: `createSealPairChainA_kernelStep`); it
gates ONLY on `stateAuthB`, with NO pidFresh conjunct (the chained executor's shape — the R3-handler
divergence is §6). -/
def createSealPairKStep (k : RecordKernelState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) : Option RecordKernelState :=
  if stateAuthB k.caps actor sealerHolder = true then
    some { k with caps := createSealPairCaps k.caps pid sealerHolder unsealerHolder }
  else none

/-- **`createSealPairChainA_kernelStep` — the bridge (PROVED, not asserted).** The audited chained executor
`createSealPairChainA`, projected to the kernel, IS `createSealPairKStep` (and it stamps the chained `log`
by `createSealPairReceipt actor sealerHolder ::`). So the kernel target this module refines the IR term to
is the genuine kernel image of the running system's create-seal-pair — the `stateAuthB`-gated double cap
grant. -/
theorem createSealPairChainA_kernelStep (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) :
    createSealPairChainA s pid actor sealerHolder unsealerHolder
      = (createSealPairKStep s.kernel pid actor sealerHolder unsealerHolder).map
          (fun k' => { kernel := k', log := createSealPairReceipt actor sealerHolder :: s.log }) := by
  unfold createSealPairChainA createSealPairKStep createSealPairCaps createSealPairReceipt
  by_cases hg : stateAuthB s.kernel.caps actor sealerHolder = true
  · rw [if_pos hg, if_pos hg]; rfl
  · rw [if_neg hg, if_neg hg]; rfl

#assert_axioms createSealPairChainA_kernelStep

/-! ## §1 — THE IR TERM: gate on the authority, then the single cap-graph write.

`createSealPairStmt = seq (guard authGate) (setCaps createSealPairCaps)` — the authority premise as an
Argus `guard` domain-restrictor, then the SINGLE cap-graph write installing the validated double-grant map
`createSealPairCaps k.caps pid sealerHolder unsealerHolder`. Unlike createEscrow (two component writes), and
exactly like `Delegate`, create-seal-pair touches ONE component (`caps`) — the §A `setCaps` primitive, with
NO new constructor. The `setCaps` leaf re-reads `k.caps` (a pure function of `k`), so on commit it installs
the double grant on the CURRENT cap graph — exactly `createSealPairKStep`'s. -/

/-- **The create-seal-pair admissibility gate as a `Bool`** — exactly `createSealPairChainA`'s `if`
condition: `actor` holds authority over `sealerHolder` (`stateAuthB`, the writer of the pair). -/
def createSealPairGuardB (actor sealerHolder : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor sealerHolder

/-- **The create-seal-pair effect as an Argus IR term: gate, then the cap-graph write.** A single `setCaps`
move installing the validated double-grant map `createSealPairCaps k.caps pid sealerHolder unsealerHolder`
(= `grant (grant k.caps sealerHolder (sealerCap pid)) unsealerHolder (unsealerCap pid)`). Mirrors the
`Delegate` shape (gate, then ONE cap-graph write) — the double grant is a single `caps` overwrite. -/
def createSealPairStmt (pid : Nat) (actor sealerHolder unsealerHolder : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (createSealPairGuardB actor sealerHolder))
    (RecStmt.setCaps (fun k => createSealPairCaps k.caps pid sealerHolder unsealerHolder))

/-! ## §2 — THE CORNERSTONE: `interp` of the create-seal-pair term IS the kernel step `createSealPairKStep`. -/

/-- **The cornerstone (cap graph).** `interp` of the create-seal-pair term IS the create-seal-pair kernel
step `createSealPairKStep` — the same partial function, by construction, exactly as the
transfer/mint/burn/escrow/delegate cornerstones, now over the CAP-GRAPH double-grant effect (a single `caps`
write gated by the authority premise). The `setCaps` leaf's `createSealPairCaps k.caps …` is DEFINITIONALLY
the double `grant`, the exact map `createSealPairKStep` installs. -/
theorem interp_createSealPairStmt_eq_createSealPairKStep (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (k : RecordKernelState) :
    interp (createSealPairStmt pid actor sealerHolder unsealerHolder) k
      = createSealPairKStep k pid actor sealerHolder unsealerHolder := by
  simp only [createSealPairStmt, interp, createSealPairGuardB]
  unfold createSealPairKStep
  by_cases hg : stateAuthB k.caps actor sealerHolder = true
  · -- ADMIT: the guard fires (`some k`); the `bind` β-reduces and the `setCaps` write installs
    -- `createSealPairCaps k.caps …` (definitional). The RHS `if` opens on the SAME `stateAuthB`.
    rw [if_pos hg]
    simp only [Option.bind_some]
    rw [if_pos hg]
  · -- REJECT: the guard fails (`none`); the `bind` short-circuits ⇒ `none`. The RHS `if` also rejects.
    rw [if_neg hg]
    simp only [Option.bind_none]
    rw [if_neg hg]

#assert_axioms interp_createSealPairStmt_eq_createSealPairKStep

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `execFullA`.

The Surface2 descriptor (§4) is keyed on the CHAINED executor `execFullA`/`createSealPairChainA` over
`RecChainedState` (kernel + receipt log). The §2 cornerstone is over the kernel step `createSealPairKStep`.
Unlike balanceA (whose chained `recCexecAsset` adds an `acceptsEffects` dst-liveness pre-gate),
`execFullA (.createSealPairA …)` is DIRECTLY `createSealPairChainA` — NO extra pre-gate — so the lift is
CLEANER: no carried side-condition, just the §0 bridge + the receipt-log stamp. -/

/-- **`interp_createSealPairStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the §2 cornerstone commits on the kernel (`interp (createSealPairStmt …) st.kernel = some k'`), the unified
action executor `execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder)` commits to the
chained state `⟨k', createSealPairReceipt actor sealerHolder :: st.log⟩`. So the Argus term's kernel meaning
lifts to the chained executor the Surface2 descriptor speaks about — with NO side-condition (the
create-seal-pair arm has no `acceptsEffects` pre-gate). -/
theorem interp_createSealPairStmt_chained
    (st : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder : CellId)
    (k' : RecordKernelState)
    (hexec : interp (createSealPairStmt pid actor sealerHolder unsealerHolder) st.kernel = some k') :
    execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder)
      = some { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log } := by
  -- the §2 cornerstone turns the IR term into the kernel step `createSealPairKStep`.
  rw [interp_createSealPairStmt_eq_createSealPairKStep] at hexec
  -- `execFullA st (.createSealPairA …)` is DIRECTLY `createSealPairChainA st …`, and the §0 bridge rewrites
  -- THAT to `(createSealPairKStep …).map …`; `hexec` names the inner step as `some k'`.
  show createSealPairChainA st pid actor sealerHolder unsealerHolder
    = some { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log }
  rw [createSealPairChainA_kernelStep, hexec]
  rfl

#assert_axioms interp_createSealPairStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of create-seal-pair's OWN Surface2 circuit agrees with the
FULL post-state the IR term's executor interpretation produces.

This welds against create-seal-pair's GENUINE Surface2 descriptor `createSealPairE D hD` (whose soundness is
`createSealPairA_full_sound`, concluding the WHOLE `CreateSealPairSpec`) — the BalanceA full-state surface,
NOT the per-cell EffectVM projection. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and
the independent `createSealPair_iff_spec` (executor ⟺ `CreateSealPairSpec`); the circuit side is the audited
`createSealPairA_full_sound` (circuit ⟹ `CreateSealPairSpec`). Both name the SAME `CreateSealPairSpec`, so
they PROVABLY agree on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a create-seal-pair term: create-seal-pair's OWN audited Surface2 v2
circuit step — the full-state arithmetization `satisfiedE2 S (createSealPairE D hD) (encodeE2 …)` satisfied
on the encoded `(st, args, st')` triple. Its soundness `createSealPairA_full_sound` pins the complete
`CreateSealPairSpec`. The create-seal-pair analog of balanceA's `balanceACircuit`, in the descriptor universe
where create-seal-pair carries its OWN genuine FULL-STATE circuit (the whole-`caps`-function digest). -/
def createSealPairCircuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (st : RecChainedState) (args : CreateSealPairArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (createSealPairE D hD) (encodeE2 S (createSealPairE D hD) st args st')

/-- **`createSealPairSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CreateSealPairSpec st pid actor sealerHolder unsealerHolder ·` are equal. Rather than re-derive this
field-by-field, we route through the PROVEN executor⟺spec corner `createSealPair_iff_spec`: each
`CreateSealPairSpec` reconstructs the SAME committed value `execFullA st (.createSealPairA …) = some ·`, and
`some` is injective. This is exactly the sense in which `CreateSealPairSpec` is functional — it determines
the post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem createSealPairSpec_unique {st st₁ st₂ : RecChainedState} {pid : Nat}
    {actor sealerHolder unsealerHolder : CellId}
    (h₁ : CreateSealPairSpec st pid actor sealerHolder unsealerHolder st₁)
    (h₂ : CreateSealPairSpec st pid actor sealerHolder unsealerHolder st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder) = some st₁ :=
    (createSealPair_iff_spec st pid actor sealerHolder unsealerHolder st₁).mpr h₁
  have e₂ : execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder) = some st₂ :=
    (createSealPair_iff_spec st pid actor sealerHolder unsealerHolder st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`createSealPair_compile_sound` — the welded soundness (create-seal-pair slice), against its OWN
Surface2 descriptor.**

Suppose, for the Argus create-seal-pair term `createSealPairStmt pid actor sealerHolder unsealerHolder`:
  * the Surface2 circuit `createSealPairCircuit S D hD st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st'`
    (= `createSealPairE`'s full-state v2 arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-`caps`-function digest portals (`hRest : RestIffNoCaps S.RH`,
    `hLog : logHashInjective S.LH`, `hD : Function.Injective D`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (createSealPairStmt …) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log }`. I.e.
create-seal-pair's OWN circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (`caps` set to
the double grant `createSealPairCaps`, every other field frozen — including `sealedBoxes`, untouched) AND the
receipt log — the full `CreateSealPairSpec`, not a per-cell projection. So the circuit the prover runs for
create-seal-pair pins the complete state the IR term's executor produces. (NO nonce-tick divergence at this
Surface2 universe-A layer — `CreateSealPairSpec` has no per-cell nonce; the post-state is pinned exactly. The
ONLY carried divergence is the kernel-vs-handler pidFresh gate, §6.) -/
theorem createSealPair_compile_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder : CellId)
    (k' : RecordKernelState)
    (hcirc : createSealPairCircuit S D hD st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st')
    (hexec : interp (createSealPairStmt pid actor sealerHolder unsealerHolder) st.kernel = some k') :
    st' = { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log } := by
  -- circuit side: create-seal-pair's OWN audited soundness forces the FULL `CreateSealPairSpec` on the triple.
  have hspec : CreateSealPairSpec st pid actor sealerHolder unsealerHolder st' :=
    createSealPairA_full_sound S D hD hRest hLog st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.createSealPairA …) = some ⟨k', receipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `CreateSealPairSpec st … ⟨k', receipt :: log⟩`.
  have hspec' : CreateSealPairSpec st pid actor sealerHolder unsealerHolder
      { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log } :=
    (createSealPair_iff_spec st pid actor sealerHolder unsealerHolder _).mp
      (interp_createSealPairStmt_chained st pid actor sealerHolder unsealerHolder k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact createSealPairSpec_unique hspec hspec'

#assert_axioms createSealPair_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely INSTALLS the keypair (observable double cap-graph write), the
two granted caps are GENUINELY DISTINCT, it genuinely REJECTS an unauthorized writer (fail-closed), and the
welded descriptor is the genuine Surface2 full-state one (full `caps`-function equality), not a placeholder.

The cornerstone/weld would be hollow if create-seal-pair never committed, if the grant were a no-op, or if
the gate admitted everything. A concrete kernel `kSP0` (cell `0` Live, HOLDING a `node 1` cap so it has
authority over `sealerHolder := 0`) exercises a real keypair install; the rejection lemma shows the
authority gate fails closed. -/

/-- A concrete kernel for the witnesses: cells 0,1,2 are live accounts; cell `0` HOLDS a `node 0` cap (so
`stateAuthB caps 0 0` holds — `0` has authority over itself as `sealerHolder`). The unsealer holder (cell
`2`) holds nothing, so the keypair install is OBSERVABLE on its slot. -/
def kSP0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 0] else [] }

/-- **NON-VACUITY (the unsealer keypair leg is OBSERVABLE — the cap INSTALLS).** Running the create-seal-pair
term on `kSP0` (writer `0` authorized over `sealerHolder 0`, unsealer holder `2` holds nothing) commits, and
the unsealer holder cell `2`'s cap-slot GAINS the unsealer cap `unsealerCap 7` (`[]` → `[unsealerCap 7]`):
the `setCaps` double-grant write is a real, observable cap-graph mutation, not a no-op. -/
theorem createSealPairStmt_installs_unsealer :
    (interp (createSealPairStmt 7 0 0 2) kSP0).map (fun k => k.caps 2)
      = some [unsealerCap 7] := by
  rw [interp_createSealPairStmt_eq_createSealPairKStep]
  decide

/-- **NON-VACUITY (the unsealer holder was empty before).** Cell `2` held NO caps before the create — so the
unsealer install above is a genuine state change, not a pre-existing cap. -/
theorem createSealPairStmt_unsealer_empty_before : kSP0.caps 2 = [] := by decide

/-- **NON-VACUITY (the sealer leg is OBSERVABLE too — and the keypair is GENUINELY DISTINCT).** The committed
create installs a sealer cap conferring the seal authority for `pid` into `sealerHolder` and an unsealer cap
conferring the unseal authority for `pid` into `unsealerHolder`, and the two are GENUINELY DISTINCT (`[grant]`
vs `[reply]` rights — a real keypair, not one cap twice). Read off `createSealPairCaps_correct` against the
committed step the cornerstone refines to. A flag-flip could NEVER witness this. -/
theorem createSealPairStmt_grants_distinct_keypair (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (k k' : RecordKernelState)
    (hne : sealerHolder ≠ unsealerHolder)
    (h : interp (createSealPairStmt pid actor sealerHolder unsealerHolder) k = some k') :
    sealerCap pid ∈ k'.caps sealerHolder
    ∧ unsealerCap pid ∈ k'.caps unsealerHolder
    ∧ holdsSealCapFor pid (sealerCap pid) = true
    ∧ holdsSealCapFor pid (unsealerCap pid) = true
    ∧ sealerCap pid ≠ unsealerCap pid := by
  rw [interp_createSealPairStmt_eq_createSealPairKStep] at h
  -- the committed kernel step installs `k'.caps = createSealPairCaps k.caps pid sealerHolder unsealerHolder`.
  have hcaps : k'.caps = createSealPairCaps k.caps pid sealerHolder unsealerHolder := by
    unfold createSealPairKStep at h
    by_cases hg : stateAuthB k.caps actor sealerHolder = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨hms, hmu, hhs, hhu, hdne, _⟩ :=
    createSealPairCaps_correct k.caps pid sealerHolder unsealerHolder hne
  exact ⟨by rw [hcaps]; exact hms, by rw [hcaps]; exact hmu, hhs, hhu, hdne⟩

/-- **NON-VACUITY (fail-closed).** A create-seal-pair whose `actor` holds NO authority over `sealerHolder`
does NOT commit: from the empty cell `1` (which holds no `node`/`control` cap over `2`) writing the pair to
`sealerHolder 2` returns `none` — the authority gate fails closed; no keypair is conjured. -/
theorem createSealPairStmt_rejects_unauthorized :
    interp (createSealPairStmt 7 1 2 0) kSP0 = none := by
  rw [interp_createSealPairStmt_eq_createSealPairKStep]
  decide

#assert_axioms createSealPairStmt_installs_unsealer
#assert_axioms createSealPairStmt_unsealer_empty_before
#assert_axioms createSealPairStmt_grants_distinct_keypair
#assert_axioms createSealPairStmt_rejects_unauthorized

/-! ## §6 — THE CARRIED DIVERGENCE (the kernel-vs-runtime pidFresh gate, as a WITNESSED theorem).

The §0 kernel target gates ONLY on `stateAuthB` — the CHAINED `createSealPairChainA`'s shape (what
`execFullA` runs, what `createSealPairA_full_sound` + `createSealPair_iff_spec` validate). The R3-closing
kernel-layer handler `createSealPairStep` (`Exec/Handlers/Seal.lean:100`) ADDS a pid-freshness conjunct the
chained executor LACKS. We pin that divergence as a THEOREM (not a hidden assumption): the IR term COMMITS on
a state with a STALE (already-bound) pid — exactly the input the R3 handler would REJECT. So the
chained-vs-handler gap is witnessed, and the weld's surface is honest about which executor it refines. -/

/-- A kernel whose `sealedBoxes` ALREADY binds pid `7` (a box keyed under it), with cell `0` authorized over
itself. The R3 handler `createSealPairStep` would REJECT a create reusing pid `7` here (`pidFresh = false`);
the chained executor this module refines to does NOT — so the IR term still commits. -/
def kSPstale : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 0] else []
    sealedBoxes := [{ pairId := 7, sealer := 0, payload := Cap.node 0 }] }

/-- **`createSealPairKStep_no_pidFresh_gate` — the carried divergence (WITNESSED).** On `kSPstale` (pid `7`
ALREADY binds a sealed box), the IR term's executor COMMITS (`interp … = some …`), reusing pid `7` — the
chained `createSealPairChainA` (= `execFullA`'s arm, the audited Surface2 descriptor's executor) has NO
pid-freshness gate. The R3-CLOSING kernel-layer handler `createSealPairStep` (`Exec/Handlers/Seal.lean:100`)
would instead REJECT this exact input (`pidFresh kSPstale 7 = false`). This module HONESTLY refines against
the chained executor (the one the descriptor speaks about), and pins the divergence here rather than papering
it: the kernel-vs-runtime gap is a witnessed fact, not a hidden assumption. -/
theorem createSealPairKStep_no_pidFresh_gate :
    (interp (createSealPairStmt 7 0 0 1) kSPstale).isSome = true := by
  rw [interp_createSealPairStmt_eq_createSealPairKStep]
  decide

#assert_axioms createSealPairKStep_no_pidFresh_gate

end Dregg2.Circuit.Argus.Effects.CreateSealPair
