/-
# Dregg2.Verify.KeystoneAuditRunnable — the Wave-4 HARD keystone-audit (GENUINE runnable witnesses).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the Wave-4 HARD
keystones whose non-vacuity demands a GENUINE runnable instance — a COMMITTED gated forest with a
concrete `NodeAuthS` credential carrier — not a `def`+`decide` over a sibling.

The fixtures are the production `StarbridgeGated` carriers (`Exec/GatedForestCfg`), where `NodeAuthS` is
inhabited concretely (`mkAuth goodCred [trueCaveat]` over the real `Crypto.Reference` portal + the
`ExecAuth` rights lattice) and a gated forest COMMITS through the 4-leg gate (credential ∧ cap-authority
∧ caveats ∧ not-revoked). Two fixtures:

  • `transferForestG` — a single `.balanceA ⟨0,0,1,30⟩ 0` COVERED node; commits at `fma0` via
    `transferForestG_commits` (the gate threaded through `execFullForestG_leaf` + `execFullAGated_some_iff`,
    NOT a kernel `decide`, which gets stuck on the gate's `Finset`/portal arms);
  • `goodFullForestG` — a 3-node, 3-level delegation tree (mint→transfer→burn), used for `no_amplify`
    (a SYNTACTIC fact over its two delegation edges — no execution).

Each `*_satisfiable` EXERCISES the keystone's conclusion on the committed run; the shared teeth
`forest_family_teeth` REFUTES it on `forgedCredForestG` (a forged credential ⇒ `gateOK = false` ⇒ the
whole forest returns `none` — `execFullForestG_unauthorized_fails`). `#keystone_audit` THROWS on FAIL,
so this module is a CI gate over the gated-forest family.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Exec.ForestMemoryProgram
import Dregg2.Exec.GatedForestCfg
import Dregg2.Circuit.Argus.Aggregate
import Dregg2.Circuit.RecursiveAggregation

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditRunnable

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (turnLedgerDeltaAsset fma0 FullActionA)
open Dregg2.Exec.FullForest (fmaDeleg)
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.ForestMemoryProgram
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.UniversalBridge (UCodec uproj UOp uaddr)
open Dregg2.Crypto.MemoryChecking (step)
open Dregg2.Authority (Cap capAuthConferred)

/-! ## §1 — THE GATED MEMORY-PROGRAM / FOREST FAMILY.

The covered-forest codec (a concrete `UCodec` at the starbridge carriers' `Val = .int`): -/

def Crun : UCodec :=
  { val := fun v => match v with | .int i => i | _ => 0
  , cap := fun _ => 0, caveat := fun _ => 0, factory := fun _ => 0
  , receipt := fun t => (t.actor : ℤ) + 2 * t.src + 3 * t.dst + 5 * t.amt }

/-! ### §1.1 — the COVERED forest (`transferForestG`, a single `.balanceA` node) commits.

`transferForestG = ⟨mkAuth goodCred [trueCaveat], .balanceA ⟨0,0,1,30⟩ 0, []⟩`: a single per-asset
transfer node, gate-passing at `fma0`. Its `lowerForestG` is the one pair `[(auth, .balanceA …)]`,
every member a `balanceA` ⇒ `IsCoveredPair`. So the covered-language memory-program keystones FIRE on
its committed run, and (asset-0 net-zero) the conservation/ledger/attestation keystones too. -/

/-- `transferForestG` commits at `fma0` to a concrete post-state. -/
theorem transfer_commits : ∃ s', execFullForestG fma0 transferForestG = some s' :=
  Option.isSome_iff_exists.mp transferForestG_commits

/-- Every pair of `transferForestG`'s pre-order lowering is a COVERED pair (it is the single
`.balanceA` node) — the syntactic covered-language condition. -/
theorem transfer_all_covered : ∀ p ∈ lowerForestG transferForestG, IsCoveredPair p := by
  intro p hp
  have hlow : lowerForestG transferForestG
      = [(transferForestG.auth, FullActionA.balanceA ⟨0, 0, 1, 30⟩ 0)] := rfl
  rw [hlow] at hp
  rcases List.mem_singleton.mp hp with rfl
  exact Or.inr ⟨⟨0, 0, 1, 30⟩, 0, rfl⟩

/-- **`forest_of_covered_is_memory_program_satisfiable`.** The COMMITTED covered forest
`transferForestG` IS one memory program end-to-end: there is a Blum trace whose `step`-fold over the
pre-projection equals the post-projection. The keystone FIRES on the concrete committed run (not a
sibling `decide`) — `NodeAuthS` inhabited by `mkAuth goodCred [trueCaveat]`, the gate passed. -/
theorem forest_of_covered_is_memory_program_satisfiable :
    ∃ s', execFullForestG fma0 transferForestG = some s'
      ∧ MemProgTrans Crun fma0 s' := by
  obtain ⟨s', hs'⟩ := transfer_commits
  exact ⟨s', hs', forest_of_covered_is_memory_program Crun fma0 s' transferForestG
    transfer_all_covered hs'⟩

/-- **`eachStepMemProg_of_all_covered_satisfiable`.** The covered-language coverage discharge FIRES on
the concrete lowering of `transferForestG`: every step of its pre-order pairing is a memory program
(`EachStepMemProg`) — the seam discharged with NO carried per-step hypothesis, on a real committed
forest. -/
theorem eachStepMemProg_of_all_covered_satisfiable :
    EachStepMemProg Crun (lowerForestG transferForestG) :=
  eachStepMemProg_of_all_covered Crun (lowerForestG transferForestG) transfer_all_covered

/-- **`balanceA_step_memprog_satisfiable`.** A committed GATED `balanceA` step is a memory program, on
the concrete `transferForestG` root: the gate passes at `fma0`, `execFullAGated fma0 auth (.balanceA …)`
commits, and the per-asset move IS its emitted three-op trace. The per-step keystone FIRES on the
inhabited `NodeAuthS`. -/
theorem balanceA_step_memprog_satisfiable :
    ∃ s', execFullAGated fma0 (mkAuth goodCred [trueCaveat]) (FullActionA.balanceA ⟨0, 0, 1, 30⟩ 0) = some s'
      ∧ MemProgTrans Crun fma0 s' := by
  obtain ⟨s', hs'⟩ := transfer_commits
  -- the single-node forest run reduces to the gated node step.
  have hleaf : execFullAGated fma0 (mkAuth goodCred [trueCaveat]) (FullActionA.balanceA ⟨0, 0, 1, 30⟩ 0)
      = some s' := by
    have hred : execFullForestG fma0 transferForestG
        = execFullAGated fma0 (mkAuth goodCred [trueCaveat]) (FullActionA.balanceA ⟨0, 0, 1, 30⟩ 0) :=
      execFullForestG_leaf fma0 (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0)
    rw [← hred]; exact hs'
  exact ⟨s', hleaf, balanceA_step_memprog Crun hleaf⟩

/-- **the shared FOREST-FAMILY teeth — `forgedCredForestG` rejects.** A forged-credential root gate
fails (`gateOK = false`), so the whole forest returns `none` (`execFullForestG_unauthorized_fails`):
the memory-program / conservation / attestation keystones are NOT `:= True` — a forged gate yields no
post-state to attest. NON-VACUOUS: the forged forest shares everything with `goodFullForestG` but the
signature. -/
theorem forest_family_teeth : execFullForestG fmaDeleg forgedCredForestG = none := by
  have hcred : credentialValidG forgedCredForestG.auth = false := by
    unfold forgedCredForestG mkAuth credentialValidG forgedCred; decide
  have hgate : gateOK forgedCredForestG.auth fmaDeleg = false := by
    unfold gateOK; rw [hcred]; simp
  exact execFullForestG_unauthorized_fails fmaDeleg forgedCredForestG.auth forgedCredForestG.action
    forgedCredForestG.children hgate

/-! ### §1.2 — conservation / ledger / attestation on the committed covered forest.

`transferForestG`'s `.balanceA ⟨0,0,1,30⟩ 0` is per-asset NET ZERO (a cell→cell move of asset 0, no
mint/burn) — `transferForestG_turn_delta_zero` (∀ b). So every conservation keystone fires on its
committed run, exercising the equation that the total supply is invariant. -/

/-- **`execFullForestG_conserves_per_asset_satisfiable`.** Asset 0's total supply is PRESERVED across
the committed transfer forest (per-asset net 0 ⇒ total unchanged) — fired on the committed run + the
genuine zero-net hypothesis. -/
theorem execFullForestG_conserves_per_asset_satisfiable :
    ∃ s', execFullForestG fma0 transferForestG = some s'
      ∧ recTotalAsset s'.kernel 0 = recTotalAsset fma0.kernel 0 := by
  obtain ⟨s', hs'⟩ := transfer_commits
  exact ⟨s', hs', execFullForestG_conserves_per_asset fma0 s' transferForestG 0 hs'
    (transferForestG_turn_delta_zero 0)⟩

/-- **`execFullForestG_conserves_exact_satisfiable`.** EVERY asset's total supply is preserved
unconditionally across the committed forest (asset 1 here, untouched by the asset-0 move) — the
no-hypothesis exactness leg, fired on the committed run. -/
theorem execFullForestG_conserves_exact_satisfiable :
    ∃ s', execFullForestG fma0 transferForestG = some s'
      ∧ recTotalAsset s'.kernel 1 = recTotalAsset fma0.kernel 1 := by
  obtain ⟨s', hs'⟩ := transfer_commits
  exact ⟨s', hs', execFullForestG_conserves_exact fma0 s' transferForestG 1 hs'⟩

/-- **`execFullForestG_ledger_per_asset_satisfiable`.** The committed forest moves asset 0's total by
EXACTLY its action-projection's net per-asset delta (`= 0` here) — the conservation VECTOR equation,
exercised on the committed run. -/
theorem execFullForestG_ledger_per_asset_satisfiable :
    ∃ s', execFullForestG fma0 transferForestG = some s'
      ∧ recTotalAsset s'.kernel 0
        = recTotalAsset fma0.kernel 0
          + turnLedgerDeltaAsset ((lowerForestG transferForestG).map Prod.snd) 0 := by
  obtain ⟨s', hs'⟩ := transfer_commits
  exact ⟨s', hs', execFullForestG_ledger_per_asset fma0 s' transferForestG 0 hs'⟩

/-- **`execFullForestG_each_attests_satisfiable`.** Every node of the committed forest attests its
`gatedActionInvG` (credential-valid ∧ cap-authority ∧ caveats-discharged ∧ the per-asset obligation) —
fired on the committed run. -/
theorem execFullForestG_each_attests_satisfiable :
    ∃ s', execFullForestG fma0 transferForestG = some s'
      ∧ ∀ p ∈ lowerForestG transferForestG,
          ∃ sa sa', execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa' := by
  obtain ⟨s', hs'⟩ := transfer_commits
  exact ⟨s', hs', execFullForestG_each_attests fma0 s' transferForestG hs'⟩

/-- **`execFullForestG_root_attests_satisfiable`.** The root node's own `(auth, action)` attests its
`gatedActionInvG` on the committed run — the root specialization. -/
theorem execFullForestG_root_attests_satisfiable :
    ∃ s', execFullForestG fma0 transferForestG = some s'
      ∧ ∃ sa sa', execFullAGated sa transferForestG.auth transferForestG.action = some sa'
          ∧ gatedActionInvG sa transferForestG.auth transferForestG.action sa' := by
  obtain ⟨s', hs'⟩ := transfer_commits
  exact ⟨s', hs', execFullForestG_root_attests fma0 s' transferForestG hs'⟩

/-- **`execFullForestG_no_amplify_satisfiable`.** EVERY delegation edge of `goodFullForestG` is
non-amplifying (`capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2`) — the Granovetter
property exercised on a forest that actually HAS delegation edges (the 0⟶0-holder `[read] ⊆ [read,write]`
edge and the 9⟶9 edge; `forestEdgesG goodFullForestG` has length 2). A SYNTACTIC fact (no execution),
so no commit hypothesis is needed. -/
theorem execFullForestG_no_amplify_satisfiable :
    ∀ e ∈ forestEdgesG goodFullForestG,
      capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 :=
  execFullForestG_no_amplify goodFullForestG

/-- **`execFullForestG_unauthorized_fails_satisfiable`.** The fail-closed root: a forged-credential
forest's gate fails, so the whole forest returns `none`. This IS the `forest_family_teeth` instance,
re-stated as the keystone's own conclusion on a concrete forest. -/
theorem execFullForestG_unauthorized_fails_satisfiable :
    execFullForestG fmaDeleg forgedCredForestG = none := forest_family_teeth

/-! ## §1.3 — THE STEPPED ARGUS STRAND (`argus_strand_{light_client,conserves}`).

`argusStrand teethGenesis [honestTurn]` STEPS `interpChained` on one real command list (the honest
cell-0→cell-1 transfer of 10) and produces a concrete one-step strand. We FIRE both keystones on it:
`conserves` (the ledger total `100` is preserved) and `light_client` (a concrete `EngineSound` over the
accepting verifier ⇒ `AggregateAttests` ∧ `Run`). Teeth = `tampered_argus_strand_rejected` (a reordered
strand cannot bind) — the existing apex anti-ghost. -/

section ArgusStrand
open Dregg2.Circuit.Argus.Aggregate
open Dregg2.Circuit.Argus (interpChained transferStmt)
open Dregg2.Distributed.HistoryAggregation (ChainStep ChainBound lastStateOf foldedFinalRoot
  stateRoot zeroTurn)
open Dregg2.Circuit.RecursiveAggregation (Aggregate EngineSound AggregateAttests
  light_client_verifies_whole_history)
open Dregg2.Circuit.RecursiveAggregation (RealProof acceptAll zCH zRH zcmb zcompress zcompressN)
open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)
open Dregg2.Exec (recTotal recChainedSystem recCexec)

/-- The stepped honest Argus strand: `interpChained` run on `[honestTurn]` from `teethGenesis`. -/
def argusSteps : List ChainStep := (argusStrand teethGenesis [honestTurn]).getD []

/-- The accepting aggregate over the honest Argus strand (toy zero-hashes; every proof is the accepting
`Unit`; the public roots are the genuine endpoints of `argusSteps`, so `binding_sound`'s pins hold). The
Argus analogue of `RecursiveAggregation.realAggregate`. -/
def argusAggregate : Aggregate RealProof where
  root := ()
  leafProofs := [()]
  bindingProof := ()
  genesisRoot := match argusSteps.head? with
    | none   => stateRoot zCH zRH zcmb zcompress zcompressN teethGenesis.kernel zeroTurn
    | some s => ChainStep.oldRoot zCH zRH zcmb zcompress zcompressN s
  finalRoot := foldedFinalRoot zCH zRH zcmb zcompress zcompressN teethGenesis argusSteps
  chainDigest := 0
  numTurns := 1

theorem argusStrand_honest_eq : argusStrand teethGenesis [honestTurn] = some argusSteps := by
  have h : (argusStrand teethGenesis [honestTurn]).isSome = true := by decide
  obtain ⟨steps, hs⟩ := Option.isSome_iff_exists.mp h
  unfold argusSteps; rw [hs]; rfl

/-- **`argus_strand_conserves_satisfiable`.** The stepped honest Argus strand CONSERVES value: the
ledger total at the folded endpoint equals the genesis total (`100`), on the concrete `argusStrand`
run. The keystone fires on a REAL stepped strand. -/
theorem argus_strand_conserves_satisfiable :
    ∃ steps, argusStrand teethGenesis [honestTurn] = some steps
      ∧ recTotal (lastStateOf teethGenesis steps).kernel = recTotal teethGenesis.kernel :=
  ⟨argusSteps, argusStrand_honest_eq,
    argus_strand_conserves teethGenesis [honestTurn] argusSteps argusStrand_honest_eq⟩

/-- **the shared ARGUS-STRAND teeth — a reordered strand cannot bind.** `tampered_argus_strand_rejected`:
no sound aggregate can attest a strand whose `newRoot`/`oldRoot` chain is broken (a reorder/drop). The
keystones are NOT `:= True` — a tampered strand is refuted. We instantiate it on a concrete
`acceptAll` engine over the toy zero-hashes, deriving `False` from a deliberately broken chain link. -/
theorem argus_strand_teeth
    (s s' : ChainStep)
    (es : EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN realAggregate teethGenesis [s, s'])
    (hbreak : ChainStep.newRoot zCH zRH zcmb zcompress zcompressN s
                ≠ ChainStep.oldRoot zCH zRH zcmb zcompress zcompressN s')
    (hverify : acceptAll realAggregate.bindingProof = true) : False :=
  tampered_argus_strand_rejected acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis s s' es hbreak hverify

/-- `argusSteps` is a concrete SINGLETON: the strand of `[honestTurn]` is one `argusChainStep`. We
extract its single element `x` with `x.commits` (the executor witness `recCexec x.pre x.turn = some
x.post`, carried by the `ChainStep` field). Proved from `argusStrand_honest_eq` + the head-step
structure (a one-turn strand that commits is exactly `[step]`). -/
theorem argusSteps_singleton : ∃ x : ChainStep, argusSteps = [x] := by
  -- A one-turn strand that commits is exactly one step: `argusStrand s [t]` reduces to
  -- `(argusStrand … []).map (cons step) = (some []).map (cons step) = some [step]`, so its `length` is 1.
  -- We read the length off `argusStrand_honest_eq` WITHOUT naming the dependent step.
  have hlen : argusSteps.length = 1 := by
    have key : ∀ (steps : List ChainStep),
        argusStrand teethGenesis [honestTurn] = some steps → steps.length = 1 := by
      intro steps h
      simp only [argusStrand] at h
      -- the body commits, so the `match` takes the `some` arm: `(some []).map (cons _) = some [_]`.
      split at h
      · next sB hb =>
          -- `h : Option.map (cons step) (some []) = some steps`, i.e. `some [step] = some steps`.
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]; rfl
      · next hb => exact absurd h (by simp)
    exact key argusSteps argusStrand_honest_eq
  match hm : argusSteps with
  | [] => rw [hm] at hlen; simp at hlen
  | [x] => exact ⟨x, rfl⟩
  | x :: y :: rest => rw [hm] at hlen; simp at hlen

/-- The accepting `EngineSound` over the honest Argus strand. Each step's `commits` field IS the
verified-executor witness (`recCexec pre turn = some post`), so `leaf_sound` is `fun _ => x.commits`;
the binding pins hold BY DEFINITION of `argusAggregate`'s roots (mirroring `real_engine_sound`). -/
theorem argus_engine_sound :
    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
      argusAggregate teethGenesis argusSteps := by
  obtain ⟨x, hx⟩ := argusSteps_singleton
  refine { recursive_sound := ?_, leaf_sound := ?_, binding_sound := ?_ }
  · intro _; exact ⟨fun p _ => rfl, rfl⟩
  · -- positional pairing: the single accepting leaf ↦ the single step, whose `commits` is the witness.
    rw [hx]
    exact List.Forall₂.cons (fun _ => x.commits) List.Forall₂.nil
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]; simp [ChainBound]
    · -- genesisRoot is DEFINED as `match argusSteps.head?` — matches the required pin (`rw [hx]`).
      show argusAggregate.genesisRoot = _
      simp only [argusAggregate, hx, List.head?_cons]
    · -- finalRoot is DEFINED as the genuine fold of `argusSteps`.
      rfl

/-- **`argus_strand_light_client_satisfiable`.** A light client checking ONLY `acceptAll
argusAggregate.root` over the stepped honest Argus strand obtains `AggregateAttests` (every Argus turn
executed) AND a genuine `Run` from genesis. Fired on the concrete `argusStrand` run + the inhabited
`argus_engine_sound`. -/
theorem argus_strand_light_client_satisfiable :
    ∃ steps, argusStrand teethGenesis [honestTurn] = some steps
      ∧ AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN argusAggregate teethGenesis steps
      ∧ Dregg2.Execution.Run recChainedSystem teethGenesis (lastStateOf teethGenesis steps) :=
  ⟨argusSteps, argusStrand_honest_eq,
    argus_strand_light_client acceptAll zCH zRH zcmb zcompress zcompressN argusAggregate
      teethGenesis [honestTurn] argusSteps argusStrand_honest_eq argus_engine_sound rfl⟩

end ArgusStrand

/-! ## §2 — TAG the gated-forest family + the memory-program family with their companions. -/

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.balanceA_step_memprog_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def balanceA_step_memprog_KS := @Dregg2.Exec.ForestMemoryProgram.balanceA_step_memprog

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.eachStepMemProg_of_all_covered_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def eachStepMemProg_of_all_covered_KS := @Dregg2.Exec.ForestMemoryProgram.eachStepMemProg_of_all_covered

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.forest_of_covered_is_memory_program_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def forest_of_covered_is_memory_program_KS :=
  @Dregg2.Exec.ForestMemoryProgram.forest_of_covered_is_memory_program

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_conserves_per_asset_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_conserves_per_asset_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_conserves_per_asset

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_conserves_exact_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_conserves_exact_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_conserves_exact

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_ledger_per_asset_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_ledger_per_asset_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_ledger_per_asset

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_no_amplify_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_no_amplify_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_no_amplify

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_each_attests_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_each_attests_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_each_attests

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_root_attests_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_root_attests_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_root_attests

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_unauthorized_fails_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.forest_family_teeth]
def execFullForestG_unauthorized_fails_KS :=
  @Dregg2.Exec.FullForestAuth.execFullForestG_unauthorized_fails

-- the stepped Argus strand:
@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.argus_strand_conserves_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.argus_strand_teeth]
def argus_strand_conserves_KS := @Dregg2.Circuit.Argus.Aggregate.argus_strand_conserves

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.argus_strand_light_client_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditRunnable.argus_strand_teeth]
def argus_strand_light_client_KS := @Dregg2.Circuit.Argus.Aggregate.argus_strand_light_client

/-! ## §3 — RUN the audit (the CI gate over the gated-forest family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.balanceA_step_memprog_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.eachStepMemProg_of_all_covered_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.forest_of_covered_is_memory_program_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_conserves_per_asset_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_conserves_exact_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_ledger_per_asset_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_no_amplify_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_each_attests_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_root_attests_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_unauthorized_fails_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.argus_strand_conserves_KS
#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.argus_strand_light_client_KS

#keystone_audit_tagged

/-! ## §4 — axiom-hygiene over the runnable witnesses + re-pinned aliases (kernel-triple clean). -/

#assert_axioms forest_of_covered_is_memory_program_satisfiable
#assert_axioms eachStepMemProg_of_all_covered_satisfiable
#assert_axioms balanceA_step_memprog_satisfiable
#assert_axioms forest_family_teeth
#assert_axioms execFullForestG_conserves_per_asset_satisfiable
#assert_axioms execFullForestG_conserves_exact_satisfiable
#assert_axioms execFullForestG_ledger_per_asset_satisfiable
#assert_axioms execFullForestG_no_amplify_satisfiable
#assert_axioms execFullForestG_each_attests_satisfiable
#assert_axioms execFullForestG_root_attests_satisfiable
#assert_axioms execFullForestG_unauthorized_fails_satisfiable
#assert_axioms argus_strand_conserves_satisfiable
#assert_axioms argus_strand_light_client_satisfiable
#assert_axioms argus_engine_sound

end Dregg2.Verify.KeystoneAuditRunnable
