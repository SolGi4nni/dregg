/-
# `EffectVmEmitIvcStateTransitionRung2Full` — the attempted FULL discharge of the IVC multi-step
no-forgery residual, and the PROOF that it is not crypto-dischargeable (outcome: STILL_PARTIAL).

## The residual (from the committed PARTIAL)

`EffectVmEmitIvcStateTransitionRung2.lean` proves `ivc_multi_refines_chain` — the genuine multi-step
no-forgery `accept ⟹ pi[accumulated_hash] = ivcChain hash pi[seed] 1 (rootsOf t)` — but RE-ASSUMES two
residual hypotheses: `IvcContinuity t` (each row's `old_hash` is the previous row's `new_hash`) and
`IvcStepIncrement t` (`stepᵢ₊₁ = stepᵢ + 1`). These are exactly the two inter-row transition gates the
deployed `StateTransitionAir` OMITS (padding-safety: an ungated transition gate fires on the
STARK's duplicated last row). The task: push to FULL — discharge that residual UNCONDITIONALLY, or
anchor it to a genuine reference object as the DFA-routing template (`DfaRoutingRung2.lean`) does.

## Why the DFA route does NOT transfer — the residual is NOT crypto-dischargeable

`DfaRoutingRung2` discharges its terminal residual `hterm` by the ROUTE-COMMITMENT binding: the
deployed DFA descriptor keeps a GUARDED `copyForwardWindow` gate, so `Satisfied2` FORCES the trace's
last `running` column to be `runningFold tableCommitment (entryHashes (traceRows t))` — a running fold
over the WHOLE entry-hash chain — and B3 pins it to the public `route_commitment`. Because the public
commitment genuinely commits to every row, a CR anchor (a genuine reference run `g` matching the
disclosed `route_commitment`) forces `entryHashes t = entryHashes g` via `fold_inj`, hence the whole
run agrees, hence `hterm`.

The IVC descriptor has NO such committed fold. Its five constraints are `perRowHash` (each row's
`new_hash = hash[TAG, old_hash, new_root, step]` — a hash of the row's OWN triple), `firstStepIsOne`,
`firstSeedBind` (`old_hash₀ = pi[seed]`), `lastStepBind`, and `lastNewHashBind` (`new_hash_last =
pi[accumulated_hash]`). There is deliberately NO copy-forward gate, so every `old_hashᵢ` for `i > 0`
is a FREE column. `Satisfied2` therefore pins the public `accumulated_hash` to a hash of ONLY the last
triple `(old_hash_last, new_root_last, step_last)` — where `old_hash_last` is free — NOT to an enforced
fold over the trace's own roots. So the public commitment carries NO binding on the intermediate
roots, and NO CR anchor can recover them.

## What THIS file PROVES (the impossibility — a load-bearing STILL_PARTIAL)

`ivc_anchor_insufficient` — the strongest available Rung-2 hypothesis set is JOINTLY SATISFIABLE with a
FALSE conclusion. Concretely, over a REAL injective (CR) `hash`, a trace `arTrace`:

  * `Satisfied2`s the emitted `ivcStateTransitionDescriptor`  (`arTrace_satisfied2`),
  * rides a SOUND Poseidon2 chip table  (`arTf_sound`),
  * has `hash` injective — the CR carrier discharged from `Function.Injective` exactly as the DFA
    template's `collisionFree_of_injective` does, and
  * is matched by a GENUINE reference IVC run `g` (`honTrace`, a fully-threaded honest run meeting
    Satisfied2 + sound chip + BOTH transition gates — strictly stronger than the DFA anchor's genuine
    run) with the SAME disclosed public commitment (`accumulated_hash`, `seed`, `step_count`) and the
    same length  (`honAnchors_arTrace` : `IvcAnchor hash (arTrace hash)`),

YET `pi[accumulated_hash] ≠ ivcChain hash pi[seed] 1 (rootsOf arTrace)`. So no DFA-style Rung-2 for
IVC exists: even a genuine reference run matching the public commitment cannot discharge the residual.

`anchor_commits_to_g_roots` exhibits the MECHANISM: `arTrace`'s published `accumulated_hash` genuinely
IS `ivcChain hash pi[seed] 1 (rootsOf g)` — a real fold — but over the ANCHOR's roots `[7, 9]`, NOT
`arTrace`'s own roots `[999, 9]`. The commitment binds to the anchor's roots and leaves the trace's
free, precisely because `old_hash_last` is unconstrained.

`arTrace` is built by taking the honest run `honTrace` (roots `[7, 9]`, seed `100`) and REPLACING
row 0's `new_root` `7 ⇝ 999` while FORGING row 1's free `old_hash` to `honTrace`'s genuine intermediate
`hash[TAG, 100, 7, 1]` (breaking continuity, since row 0's `new_hash` is now `hash[TAG, 100, 999, 1]`).
Every row is still genuinely hashed (sound chip, `Satisfied2`), and the last row's hash — hence the
public `accumulated_hash` — is UNCHANGED from `honTrace`. So the same genuine `g = honTrace` anchors
both, yet `arTrace` reads roots `[999, 9]` and its true chain differs.

## Outcome: STILL_PARTIAL — the emit-fix, named precisely

The residual is an EMIT-GAP, not a crypto residual. The fix is in the descriptor, not a carrier: add
a GUARDED window gate (as DFA-routing's `copyForwardWindow`/`continuityWindow`) enforcing, on the
genuine→genuine transition only (never the genuine→padding clone),

  * `next.old_hash − loc.new_hash = 0`   (the copy-forward continuity that closes `IvcContinuity`), and
  * `next.step − loc.step − 1 = 0`        (the step-increment that closes `IvcStepIncrement`),

each carrying its padding-safety guard so it does not fire on the STARK's duplicated last row. With
those two gates emitted, `Satisfied2` supplies `IvcContinuity`/`IvcStepIncrement` directly and
`ivc_multi_refines_chain` concludes the multi-step no-forgery UNCONDITIONALLY — no residual, no anchor.
Until the descriptor gains them, the multi-step no-forgery is genuinely conditional on the omitted
gates (`ivc_multi_refines_chain`, the committed PARTIAL), and this file certifies that conditionality
is essential: a CR anchor cannot substitute for the missing gates.

## Axiom hygiene / non-vacuity

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 collision-resistance rides ONLY
the named `ChipTableSound` carrier and the reference `Function.Injective hash` realisation (as in the
DFA template), never as a Lean axiom. `ivc_anchor_insufficient` is non-vacuous by construction: its
hypothesis set is EXHIBITED satisfied on `arTrace`/`honTrace`, and the anchor `g` is a REAL genuine run
(`honAnchors_arTrace`) — not a `True` filter. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2

namespace Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2Full

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition
open Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRefine
open Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2

set_option autoImplicit false

/-! ## §1 — The DFA-style anchor, as a bundled genuine reference IVC run.

The exact analogue of the object `DfaRoutingRung2.dfaRouting_rung2` accepts: a GENUINE reference run
`g` matching the trace's disclosed public commitment. For DFA that run is a full
`DfaAcceptanceAir.Satisfies`; here it is a fully-threaded IVC run — one that `Satisfied2`s, rides a
sound chip table, AND meets BOTH omitted transition gates (so its OWN multi-step no-forgery holds via
`ivc_multi_refines_chain`) — matched to `t` on `accumulated_hash`, `seed`, `step_count`, and length.
This is at least as strong an anchor as the DFA template's. -/

/-- A DFA-style route-commitment anchor for the IVC descriptor: a genuine, fully-threaded reference
run `g` whose disclosed public commitment (accumulated hash, seed, step count) and length match `t`. -/
structure IvcAnchor (hash : List ℤ → ℤ) (t : VmTrace) where
  /-- the genuine reference IVC run (the honest anchor). -/
  g : VmTrace
  gNe : g.rows ≠ []
  /-- `g` rides a SOUND Poseidon2 chip table (genuine per-row hashing). -/
  gSound : ChipTableSound hash (g.tf .poseidon2)
  /-- `g` satisfies the emitted descriptor. -/
  gSat : Satisfied2 hash ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] g
  /-- `g` genuinely threads (copy-forward continuity) — the FULL genuine run, stronger than the DFA
  anchor's, which does not even need this stated because its descriptor keeps the gate. -/
  gCont : IvcContinuity g
  /-- `g` genuinely increments its step index. -/
  gStep : IvcStepIncrement g
  /-- the anchor matches `t`'s disclosed seed … -/
  matchSeed : g.pub Ivc.PI_INITIAL_HASH = t.pub Ivc.PI_INITIAL_HASH
  /-- … the disclosed public commitment `accumulated_hash` … -/
  matchAcc : g.pub Ivc.PI_ACC_HASH = t.pub Ivc.PI_ACC_HASH
  /-- … the disclosed `step_count` … -/
  matchStepCount : g.pub Ivc.PI_STEP_COUNT = t.pub Ivc.PI_STEP_COUNT
  /-- … and the trace length. -/
  matchLen : g.rows.length = t.rows.length

/-! ## §2 — The anchor-cheat trace: honest last-row hash, forged intermediate root.

`arTrace` is `honTrace` (the committed honest 2-row witness, roots `[7, 9]`, seed `100`) with row 0's
`new_root` changed `7 ⇝ 999` and row 1's FREE `old_hash` forged to `honTrace`'s genuine intermediate
`hash[TAG, 100, 7, 1]`. Row 1 (`honRow1`) and the public inputs (`honPub`) are REUSED unchanged from
`honTrace`, so the published `accumulated_hash`/`seed`/`step_count` are identical — the SAME genuine
`g = honTrace` anchors both. But `arTrace` reads roots `[999, 9]`, and its row-0 `new_hash` is now
`hash[TAG, 100, 999, 1] ≠ hash[TAG, 100, 7, 1] = arTrace`'s forged row-1 `old_hash` — continuity
BROKEN, invisibly to `Satisfied2` (no gate). -/

/-- Row 0 of the cheat: `step = 1`, `old = 100 (seed)`, `new_root = 999` (forged), genuine
`new_hash = hash[TAG, 100, 999, 1]`, chip lanes `0`. -/
def arRow0 (hash : List ℤ → ℤ) : Assignment :=
  rowOf [1, 100, 999, hash [IVC_DOMAIN_TAG, 100, 999, 1], 0, 0, 0, 0, 0, 0, 0]

/-- The cheat chip table: each row IS genuinely hashed (row 0's own triple, and `honRow1`'s). -/
def arTf (hash : List ℤ → ℤ) : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [ivcTupleAt (arRow0 hash), ivcTupleAt (honRow1 hash)]
  | _          => []

/-- The anchor-cheat trace: forged row 0, `honTrace`'s genuine row 1 and public inputs. -/
def arTrace (hash : List ℤ → ℤ) : VmTrace :=
  { rows := [arRow0 hash, honRow1 hash], pub := honPub hash, tf := arTf hash }

/-- **The cheat chip table is SOUND** — the forgery is in the (ungated) continuity/roots, NOT in the
hashing: every row is a genuine arity-4 `chipRow` of the permutation. -/
theorem arTf_sound (hash : List ℤ → ℤ) : ChipTableSound hash ((arTrace hash).tf .poseidon2) := by
  intro r hr
  simp only [arTrace, arTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[IVC_DOMAIN_TAG, 100, 999, 1], List.replicate 7 0, by simp [CHIP_RATE], by decide, rfl⟩
  · exact ⟨[IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2], List.replicate 7 0,
      by simp [CHIP_RATE], by decide, rfl⟩

/-- **The cheat trace `Satisfied2`s the descriptor** — the two per-row lookups by membership in the
sound chip table; the four boundaries (`step₀ = 1`, `old₀ = seed = 100`, `step_last = step_count = 2`,
`new_hash_last = accumulated_hash`) met by construction. The broken continuity is INVISIBLE (no gate
exists to catch it) — the whole point. -/
theorem arTrace_satisfied2 (hash : List ℤ → ℤ) :
    Satisfied2 hash ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] (arTrace hash) where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    clear hi
    simp only [ivcStateTransitionDescriptor, ivcConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        perRowHash, firstStepIsOne, firstSeedBind, lastStepBind, lastNewHashBind,
        arTrace, arTf, envAt, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq,
        reduceCtorEq] <;>
      first
        | exact List.mem_cons.mpr (Or.inl rfl)
        | exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | trivial
        | simp [arRow0, honRow1, honPub, rowOf, EmittedExpr.eval, Ivc.STEP_COL, Ivc.OLD_HASH_COL,
            Ivc.NEW_HASH_COL, Ivc.PI_INITIAL_HASH, Ivc.PI_STEP_COUNT, Ivc.PI_ACC_HASH]
  rowHashes := by
    intro i _
    rw [show ivcStateTransitionDescriptor.hashSites = ([] : List _) from rfl]
    exact True.intro
  rowRanges := by
    intro i _ r hr
    rw [show ivcStateTransitionDescriptor.ranges = ([] : List _) from rfl] at hr
    simp at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_ivc] at hop; simp at hop
  memDisciplined := by rw [memLog_ivc]; trivial
  memBalanced := by rw [memLog_ivc]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_ivc]; rfl
  mapTableFaithful := by rw [mapLog_ivc]; rfl

/-! ## §3 — `honTrace` genuinely anchors the cheat (the anchor is a REAL genuine run, not `True`). -/

/-- **The genuine honest run `honTrace` inhabits `IvcAnchor hash (arTrace hash)`.** It is a genuine,
fully-threaded IVC run (Satisfied2 + sound chip + BOTH transition gates, all committed in
`EffectVmEmitIvcStateTransitionRung2`), and it matches `arTrace`'s disclosed public commitment and
length by construction (they SHARE row 1 and the public inputs). So the DFA-style anchor is genuinely
present — the impossibility below is not a vacuous "no anchor exists". -/
def honAnchors_arTrace (hash : List ℤ → ℤ) : IvcAnchor hash (arTrace hash) where
  g := honTrace hash
  gNe := by simp [honTrace]
  gSound := honTf_sound hash
  gSat := honTrace_satisfied2 hash
  gCont := honTrace_continuity hash
  gStep := honTrace_stepinc hash
  matchSeed := rfl
  matchAcc := rfl
  matchStepCount := rfl
  matchLen := rfl

/-! ## §4 — THE MECHANISM: the public commitment binds the ANCHOR's roots, not the trace's. -/

/-- **`anchor_commits_to_g_roots` — why the anchor cannot close the gap.** `arTrace`'s published
`accumulated_hash` genuinely IS `ivcChain hash pi[seed] 1 (rootsOf g)` — a REAL fold — but over the
ANCHOR `g`'s roots `[7, 9]`, NOT `arTrace`'s own roots `[999, 9]`. The public commitment (a hash of
only the last triple, with `old_hash_last` free) carries no binding on the trace's intermediate roots;
it certifies the anchor's chain, which the forged trace re-uses wholesale for its last row. -/
theorem anchor_commits_to_g_roots (hash : List ℤ → ℤ) :
    (arTrace hash).pub Ivc.PI_ACC_HASH
        = ivcChain hash ((honTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (honTrace hash))
      ∧ rootsOf (honTrace hash) = [7, 9]
      ∧ rootsOf (arTrace hash) = [999, 9] := by
  refine ⟨?_, rfl, rfl⟩
  -- honTrace meets ALL of `ivc_multi_refines_chain`'s hypotheses, so its published acc IS the genuine
  -- chain of ITS OWN roots; and `arTrace`'s published acc is definitionally `honTrace`'s (shared pub).
  exact (ivc_multi_refines_chain hash (honTrace hash) (fun _ => 0) (fun _ => (0, 0)) []
    (by simp [honTrace]) (honTf_sound hash) (honTrace_satisfied2 hash)
    (honTrace_continuity hash) (honTrace_stepinc hash)).1

/-! ## §5 — THE IMPOSSIBILITY: the DFA-style anchor does NOT discharge the residual. -/

/-- **`ivc_anchor_insufficient` — the residual is NOT crypto-dischargeable.** Over a REAL injective
(CR) `hash`, the cheat trace `arTrace` simultaneously (i) `Satisfied2`s the emitted descriptor,
(ii) rides a SOUND Poseidon2 chip table, (iii) is matched by a GENUINE reference IVC run — the exact
DFA-style anchor, and stronger — via `IvcAnchor`, YET (iv) its published `accumulated_hash` is NOT the
genuine `ivcChain` of ITS OWN read roots. So no theorem of the DFA shape (`Satisfied2 ∧ soundChip ∧ CR
∧ genuine-reference-run ⟹ no-forgery`) can hold for the IVC descriptor: the omitted continuity gate
is genuinely irreplaceable by a collision-resistance anchor.

This is the sharp difference from `DfaRoutingRung2.dfaRouting_rung2`, whose identical hypothesis set
DOES conclude `final = classify` — because the DFA descriptor keeps the guarded `copyForwardWindow`
gate that makes the public `route_commitment` a whole-chain fold a CR anchor can bind. The IVC
descriptor omits its analogue, so the public `accumulated_hash` binds only the last triple. -/
theorem ivc_anchor_insufficient (hash : List ℤ → ℤ) (hinj : Function.Injective hash) :
    Satisfied2 hash ivcStateTransitionDescriptor (fun _ => 0) (fun _ => (0, 0)) [] (arTrace hash)
      ∧ ChipTableSound hash ((arTrace hash).tf .poseidon2)
      ∧ Nonempty (IvcAnchor hash (arTrace hash))
      ∧ (arTrace hash).pub Ivc.PI_ACC_HASH
          ≠ ivcChain hash ((arTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (arTrace hash)) := by
  refine ⟨arTrace_satisfied2 hash, arTf_sound hash, ⟨honAnchors_arTrace hash⟩, ?_⟩
  -- published = hash[TAG, hash[TAG,100,7,1], 9, 2] (the anchor's genuine last hash);
  -- genuine chain of arTrace's roots [999,9] = hash[TAG, hash[TAG,100,999,1], 9, 2].
  have hpub : (arTrace hash).pub Ivc.PI_ACC_HASH
      = hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 7, 1], 9, 2] := rfl
  have hchain : ivcChain hash ((arTrace hash).pub Ivc.PI_INITIAL_HASH) 1 (rootsOf (arTrace hash))
      = hash [IVC_DOMAIN_TAG, hash [IVC_DOMAIN_TAG, 100, 999, 1], 9, 2] := by
    simp [rootsOf, nextRoot, arTrace, arRow0, honRow1, rowOf, honPub, ivcChain,
      extendAccumulatedHash, Ivc.NEW_ROOT_COL, Ivc.PI_INITIAL_HASH]
  rw [hpub, hchain]
  intro heq
  have h1 := hinj heq
  simp only [List.cons.injEq, true_and] at h1
  have h2 := hinj h1.1
  simp only [List.cons.injEq] at h2
  omega

/-! ## §6 — axiom tripwires. -/

#assert_axioms arTf_sound
#assert_axioms arTrace_satisfied2
#assert_axioms honAnchors_arTrace
#assert_axioms anchor_commits_to_g_roots
#assert_axioms ivc_anchor_insufficient

end Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransitionRung2Full
