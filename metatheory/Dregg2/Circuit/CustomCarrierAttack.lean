/-
# Dregg2.Circuit.CustomCarrierAttack — ADVERSARIAL soundness audit of the two custom-effect carriers.

This module attacks `CustomApex`'s two named carriers (`StarkSoundCustom`, `EngineBinding`) head-on,
IN LEAN, importing everything read-only. It is a refutation file: the load-bearing arms are proved
WITHOUT `sorry`, and the conclusions are stated precisely (an honest "doesn't fully close because X"
is recorded where the opaque-verifier surface blocks a stronger claim).

## The target

`CustomApex.StarkSoundCustom hash E R` asserts a STAGED-AIR extraction:

    verifyBatch (vkOfRegistry R) pi π = accept ⟹
      ∃ … t, Satisfied2Staged hash E (R pi.effect) … t ∧ tracePublishedCommit t = pi.toPublished

`Satisfied2Staged` upgrades the deployed `Satisfied2` on exactly ONE row gate: the `proofBind` op,
whose deployed denotation `DescriptorIR2.VmConstraint2.holdsAt … (.proofBind _) = True` (`:570`,
vacuous) becomes `ProofBind.boundAt E env` (the column commits to a VERIFYING sub-proof). So the
DEPLOYED AIR is STRICTLY WEAKER than the staged AIR.

## What is proved here

§A `deployed_admits_unbacked` — the explicit FORGED TRACE. A concrete custom descriptor (`demoC`)
   and trace whose `custom_proof_commitment` column is `999` (a value NO verifying sub-proof of the
   demo engine exposes), with the Custom selector ON. It SATISFIES the deployed `Satisfied2` (the
   True-gate passes the forged row) yet is REJECTED by `Satisfied2Staged` (`boundAt` is false). The
   deployed AIR admits a trace the staged AIR rejects — the explicit forged custom proof.

§B `starkSoundCustom_unsound_over_deployed` — `StarkSoundCustom`'s staged extraction does NOT follow
   from the deployed `Satisfied2` extraction: there is NO uniform bridge `Satisfied2 ⇒
   Satisfied2Staged` (§A is the counterexample). So consuming `StarkSoundCustom` over the deployed
   True-gate AIR asserts strictly more than the deployed verifier enforces. The precise honest
   statement + its limits are documented at the theorem.

§C `vk_determined_or_encColl` — the engine binding, FLOOR-FREE. Two verifying sub-proofs exposing
   the same PI-commitment either attest the same program VK or their absorbed public-input lists
   are a NAMED collision of the deployed sponge. ⛑ This replaces `engineBinding_of_floor`, which
   derived the unqualified `EngineBinding E` from `Poseidon2SpongeCR` — a floor PROVED FALSE at
   deployed BabyBear parameters, and whose CONCLUSION is false there too (see §C's header).

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new axiom,
NO `sorry`, and as of the §C cutover no refuted-floor hypothesis either.
-/
import Dregg2.Circuit.CustomApex

namespace Dregg2.Circuit.CustomCarrierAttack

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.CustomApex
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §A — the forged trace: deployed `Satisfied2` accepts what staged `Satisfied2Staged` rejects.

We reuse the in-tree demo descriptor `DescriptorIR2.demoC` (one `proofBind ⟨.var 2, .var 0, .var 1⟩`:
guard = col 2, `custom_proof_commitment` = col 0, `custom_program_vk_hash` = col 1) and the toy
recursion engine `DescriptorIR2.demoEngine` (the ONLY verifying proof exposes commitment `123` /
vk `45`). The HONEST demo trace (`demoCTrace`, commit = 123) binds; the FORGED trace below sets the
commitment column to `999` while keeping the selector ON. -/

/-- The forged Custom row: `custom_proof_commitment` (col 0) = `999` — a commitment NO verifying
sub-proof of `demoEngine` exposes (the only verifying proof commits to `123`); `custom_program_vk_hash`
(col 1) = `45`; the Custom selector (col 2) = `1` (the binding gate is ACTIVE). -/
def forgedRow : Assignment := fun i => if i = 0 then 999 else if i = 1 then 45 else if i = 2 then 1 else 0

/-- The forged single-row witness: one main row, no auxiliary tables (proof binding rides the engine,
not a committed table) — byte-for-byte the shape of `demoCTrace`, only the commitment column moved. -/
def forgedTrace : VmTrace := { rows := [forgedRow], pub := zeroAsg, tf := fun _ => [] }

/-- **The deployed `proofBind` gate is literally `True` — it enforces NOTHING.** This is the root of
the forgery: the deployed AIR's per-row meaning of a `proofBind` op carries no content, so any column
values pass. (`DescriptorIR2.VmConstraint2.holdsAt … (.proofBind _) = True`, `:570`.) -/
theorem deployed_proofBind_gate_vacuous (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (m : ProofBind) :
    VmConstraint2.holdsAt hash tf env isFirst isLast (.proofBind m) := trivial

/-- **The forged trace SATISFIES the deployed `Satisfied2`.** Identical to `demoC_satisfied` minus the
proof-binding leg: the proofBind row passes via the vacuous True-gate, and every memory/hash/range leg
is empty. So the deployed verifier's extraction relation accepts a trace whose Custom row binds to no
verifying sub-proof. -/
theorem forged_satisfied2 :
    Satisfied2 (fun _ => 0) demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] forgedTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    simp only [demoC, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; trivial
  · intro i hi; trivial
  · intro i hi r hr; simp [demoC] at hr
  · intro op hop; rw [show memLog demoC forgedTrace = [] from rfl] at hop; cases hop
  · rw [show memLog demoC forgedTrace = [] from rfl]; exact by decide
  · rw [show memLog demoC forgedTrace = [] from rfl]; exact memCheck_nil _ _
  · rfl
  · rfl

/-- **The forged trace is REJECTED by the staged `Satisfied2Staged`.** The staged `proofBind` gate is
`ProofBind.boundAt demoEngine env`, which on the active row demands `demoEngine.boundTo 999 45` — a
VERIFYING sub-proof with commitment `999`. The only verifying proof of `demoEngine` commits to `123`,
so no such sub-proof exists: the staged constraint fails. -/
theorem forged_not_staged :
    ¬ Satisfied2Staged (fun _ => 0) demoEngine demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
        forgedTrace := by
  intro h
  -- the staged proofBind row constraint at row 0:
  have hrow := h.rowConstraints 0 (by decide) (.proofBind ⟨.var 2, .var 0, .var 1⟩) (by simp [demoC])
  -- holdsAtStaged (.proofBind m) ≡ ProofBind.boundAt demoEngine (envAt forgedTrace 0) m
  -- the guard (col 2 = 1) is active, so we obtain demoEngine.boundTo 999 45:
  have hbound := hrow (by decide)
  obtain ⟨p, hp, hpc, hpv⟩ := hbound
  -- demoEngine.piCommit p ≡ 123, the commit column ≡ 999 (defeq); 123 = 999 is false.
  have hcontra : (123 : ℤ) = 999 := hpc
  exact absurd hcontra (by decide)

/-- **§A keystone — `deployed_admits_unbacked`.** ∃ a concrete custom descriptor and trace satisfying
the DEPLOYED `Satisfied2` (True-gate) yet failing the STAGED `Satisfied2Staged` (`boundAt` false): the
deployed AIR admits a Custom trace whose proof-binding commitment is backed by NO verifying sub-proof.
This is the explicit forged custom proof the deployed circuit cannot detect. -/
theorem deployed_admits_unbacked :
    ∃ (E : ProofEngine) (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
      (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 (fun _ => 0) d minit mfin maddrs t ∧
      ¬ Satisfied2Staged (fun _ => 0) E d minit mfin maddrs t :=
  ⟨demoEngine, demoC, (fun _ => 0), (fun _ => ((0 : ℤ), 0)), [], forgedTrace,
    forged_satisfied2, forged_not_staged⟩

/-! ## §B — `StarkSoundCustom` is unsound over the deployed True-gate AIR. -/

/-- **§B keystone — `starkSoundCustom_unsound_over_deployed`.** There is NO uniform upgrade
`Satisfied2 ⇒ Satisfied2Staged`. Since `StarkSound`'s extraction payload is `Satisfied2` and
`StarkSoundCustom`'s is `Satisfied2Staged`, the ONLY way to discharge a `StarkSoundCustom` instance
from the deployed verifier (whose AIR-soundness yields the `Satisfied2` of `StarkSound`) is to compose
with such a bridge — which §A proves cannot exist. Hence `StarkSoundCustom` over the deployed registry
asserts strictly MORE than the deployed True-gate AIR enforces (the proof-binding leg), and is NOT a
consequence of the deployed `StarkSound` floor.

PRECISION / limits (honest): this does NOT prove `StarkSoundCustom hash E R → False` as a class —
`verifyBatch` is opaque and `extract` is existential, so if the deployed verifier never accepts (or
always re-extracts a DIFFERENT, backed trace) the class stays vacuously inhabited. What is rigorously
established is the per-witness fact that drives the apex: the deployed extraction's witness type is
STRICTLY WEAKER than the staged one, so the binding `lightclient_unfoolable_custom_binds` claims is
carried ENTIRELY by the `StarkSoundCustom`/`Satisfied2Staged` hypothesis, NOT by the deployed circuit.
Over the deployed True-gate AIR that hypothesis is ungrounded — the theorem is clean-but-vacuous as
deployed. The real binding must come from the SEPARATE staged AIR (the gated VK epoch) or the FOLD
(`AggAirSound`), never from consuming `StarkSoundCustom` against the deployed VK. -/
theorem starkSoundCustom_unsound_over_deployed :
    ¬ ∀ (hash : List ℤ → ℤ) (E : ProofEngine) (d : EffectVmDescriptor2)
        (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t →
        Satisfied2Staged hash E d minit mfin maddrs t := by
  intro hbridge
  exact forged_not_staged
    (hbridge (fun _ => 0) demoEngine demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] forgedTrace
      forged_satisfied2)

/-! ## §C — the ENGINE BINDING: determined, or a NAMED collision at THIS pair. FLOOR-FREE.

`EngineBinding E` says the engine's PI-commitment is collision-free across verifying proofs (two
verifying sub-proofs with the same `piCommit` agree on their program VK), once the commitment FACTORS
as the Poseidon2 sponge of the public inputs with the program VK among them.

⛑ **CUT OVER 2026-07-27 — `engineBinding_of_floor` DELETED.** It derived `EngineBinding E` from
`Poseidon2SpongeCR hash`, which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at
the deployed BabyBear parameters. So the reduction transported nothing to the shipping system, and
neither did the eight `*_binding_from_fold` carriers that consumed it.

⚑ **AND THE CONCLUSION WAS FALSE TOO, WHICH IS WHY WIDENING THE HYPOTHESIS IS NOT THE REPAIR.**
`EngineBinding (floorEngine hash)` says `hash [a,b] = hash [c,d] → a = c`; the diagonal
`n ↦ (n, 0)` is an injection of an infinite set into a range-bounded codomain, so two distinct `n`
share a digest and disagree on `vkOf`. A `∀ p q, ¬ EncColl …` hypothesis would be refuted for the
same reason. The honest object is therefore per-PAIR, at the pair the extraction actually hands
back:

  * `EncColl hash enc p q` — the collision event, stated at the two lists the sponge ABSORBS;
  * `vk_determined_or_encColl` — the unconditional dichotomy, NO hypothesis at all;
  * `vk_determined_of_noEncColl` — the per-instance form the fold carriers thread.

**WHAT WAS LOST:** nothing derives the UNQUALIFIED `EngineBinding E` from crypto any more, because
nothing could. `EngineBinding` survives as a per-pair consequence and, unconditionally, at a sponge
that is genuinely injective (`refFloorEngine_binding`, on `Poseidon2Binding.Reference.refSponge`
whose CR is PROVED). -/

/-- **`EncColl hash enc p q`** — the per-instance sponge collision the PI extraction produces at
THIS pair: two DISTINCT public-input encodings whose digests agree. Stated at exactly the two lists
the sponge absorbs, so it is an event at NAMED arguments — refutable at deployed parameters, rather
than (like injectivity over all of `List ℤ`) false there. -/
def EncColl {P : Type} (hash : List ℤ → ℤ) (enc : P → List ℤ) (p q : P) : Prop :=
  enc p ≠ enc q ∧ hash (enc p) = hash (enc q)

/-- **POLE 1 — DISCHARGEABLE.** A side condition that can never be discharged is a broken keystone,
not a repaired one: at a pair with equal encodings there is nothing to collide. -/
theorem encColl_self_false {P : Type} (hash : List ℤ → ℤ) (enc : P → List ℤ) (p : P) :
    ¬ EncColl hash enc p p := fun h => h.1 rfl

/-- **POLE 2 — REFUTABLE, so `¬ EncColl` is not free.** A constant hash collides at every pair of
distinct encodings. -/
theorem encColl_of_constant {P : Type} (enc : P → List ℤ) {p q : P} (h : enc p ≠ enc q) :
    EncColl (fun _ => 0) enc p q := ⟨h, rfl⟩

/-- **POLE 3 — THE PORT IS A WEAKENING, NOT A CHANGE OF SUBJECT.** The residual firing REFUTES the
deleted floor, i.e. the deleted floor implied `¬ EncColl` at every pair. Stated contrapositively so
it assumes no floor content and is a refutation rather than a carrier. -/
theorem encColl_refutes_poseidon2CR {P : Type} {hash : List ℤ → ℤ} {enc : P → List ℤ} {p q : P}
    (h : EncColl hash enc p q) : ¬ Poseidon2SpongeCR hash := fun hCR => h.1 (hCR _ _ h.2)

/-- **`vk_determined_or_encColl` — THE FLOOR-FREE DICHOTOMY.** Two verifying sub-proofs exposing the
SAME PI-commitment either attest the same program VK, or their two absorbed public-input lists are a
witnessed collision of the deployed sponge. NO cryptographic hypothesis: an adversary that ghosts the
attested VK has, by construction, produced the collision. -/
theorem vk_determined_or_encColl (hash : List ℤ → ℤ) (E : ProofEngine) (enc : E.Proof → List ℤ)
    -- FRI extraction: a VERIFYING proof's exposed PI-commitment IS the sponge of its genuine PIs.
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    -- structural: the program VK is one of the committed public inputs (recoverable from `enc`).
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (p q : E.Proof) (hp : E.verify p = true) (hq : E.verify q = true)
    (hpc : E.piCommit p = E.piCommit q) :
    E.vkOf p = E.vkOf q ∨ EncColl hash enc p q := by
  have hh : hash (enc p) = hash (enc q) := by
    rw [← hfactor p hp, ← hfactor q hq]; exact hpc
  by_cases henc : enc p = enc q
  · exact Or.inl (hvk p q hp hq henc)
  · exact Or.inr ⟨henc, hh⟩

/-- **`vk_determined_of_noEncColl` — the per-instance form.** The anti-ghost at ONE pair, off the
refutable side condition at THAT pair. This is what the `*_binding_from_fold` carriers thread in
place of the deleted floor. -/
theorem vk_determined_of_noEncColl (hash : List ℤ → ℤ) (E : ProofEngine) (enc : E.Proof → List ℤ)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    {p q : E.Proof} (hp : E.verify p = true) (hq : E.verify q = true)
    (hpc : E.piCommit p = E.piCommit q) (hno : ¬ EncColl hash enc p q) :
    E.vkOf p = E.vkOf q :=
  (vk_determined_or_encColl hash E enc hfactor hvk p q hp hq hpc).resolve_right hno

/-- **`vk_determined_of_noEncColl_vkHeaded` — the residual is EXACTLY the FRI factoring.** When the
PI encoding is vk-headed (`enc p = vkOf p :: tail p` — the program VK is the leading public input, as
the leaf wrap lays it), the structural `hvk` discharges internally (cons-injectivity), so the only
hypotheses left are `hfactor` and the per-pair non-collision. -/
theorem vk_determined_of_noEncColl_vkHeaded (hash : List ℤ → ℤ) (E : ProofEngine)
    (tailEnc : E.Proof → List ℤ)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (E.vkOf p :: tailEnc p))
    {p q : E.Proof} (hp : E.verify p = true) (hq : E.verify q = true)
    (hpc : E.piCommit p = E.piCommit q)
    (hno : ¬ EncColl hash (fun r => E.vkOf r :: tailEnc r) p q) :
    E.vkOf p = E.vkOf q := by
  refine vk_determined_of_noEncColl hash E (fun r => E.vkOf r :: tailEnc r) hfactor ?_ hp hq hpc hno
  intro p' q' _ _ henc
  injection henc with hvkeq _

/-! ### Non-vacuity: BOTH branches of the dichotomy are reachable, and neither is free.

`floorEngine hash` is an engine whose proofs are `(vk, statement)` pairs and whose PI-commitment IS
the sponge of `[vk, statement]` — the FRI factoring holds BY CONSTRUCTION (`rfl`). -/
def floorEngine (hash : List ℤ → ℤ) : ProofEngine where
  Proof    := ℤ × ℤ
  verify   := fun _ => true
  piCommit := fun p => hash [p.1, p.2]
  vkOf     := fun p => p.1

/-- The floor engine's vk-recovery is cons-injectivity. -/
theorem floorEngine_hvk (hash : List ℤ → ℤ) :
    ∀ p q, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
      [p.1, p.2] = [q.1, q.2] → (floorEngine hash).vkOf p = (floorEngine hash).vkOf q := by
  intro p q _ _ henc
  injection henc with h1 _

/-- **The dichotomy FIRES on the floor engine with NO hypothesis at all** — the reduction is a
theorem about the deployed sponge, not about an assumed one. -/
theorem floorEngine_binds_or_collides (hash : List ℤ → ℤ) (p q : ℤ × ℤ)
    (hpc : (floorEngine hash).piCommit p = (floorEngine hash).piCommit q) :
    (floorEngine hash).vkOf p = (floorEngine hash).vkOf q
      ∨ EncColl hash (fun r : ℤ × ℤ => [r.1, r.2]) p q :=
  vk_determined_or_encColl hash (floorEngine hash) (fun r => [r.1, r.2]) (fun _ _ => rfl)
    (floorEngine_hvk hash) p q rfl rfl hpc

/-- **THE LEFT BRANCH IS REACHABLE (positive non-vacuity), unconditionally.** On
`Poseidon2Binding.Reference.refSponge` — a sponge whose collision-resistance is PROVED, not assumed —
the floor engine satisfies the full `EngineBinding`. So `EngineBinding` is still DERIVABLE rather
than carried; what is gone is only the false claim that it is derivable at the deployed sponge. -/
theorem refFloorEngine_binding :
    EngineBinding (floorEngine Dregg2.Circuit.Poseidon2Binding.Reference.refSponge) := by
  refine ⟨fun p q hp hq hpc => ?_⟩
  refine vk_determined_of_noEncColl Dregg2.Circuit.Poseidon2Binding.Reference.refSponge
    (floorEngine Dregg2.Circuit.Poseidon2Binding.Reference.refSponge)
    (fun r : ℤ × ℤ => [r.1, r.2]) (fun _ _ => rfl) (floorEngine_hvk _) hp hq hpc ?_
  exact fun h => h.1 (Dregg2.Circuit.Poseidon2Binding.Reference.refSponge_CR _ _ h.2)

/-- **THE RIGHT BRANCH IS REACHABLE (the tooth), so the dichotomy is not a disguised equality.** On
the constant-zero sponge two distinct floor-engine proofs share a commitment and disagree on the
attested VK — the ghost the fold carriers exclude, exhibited. -/
theorem constFloorEngine_collides :
    EncColl (fun _ : List ℤ => (0 : ℤ)) (fun r : ℤ × ℤ => [r.1, r.2]) (0, 0) (1, 0) :=
  encColl_of_constant _ (by decide)

/-! ## Axiom audit — every load-bearing arm. -/

#assert_axioms deployed_proofBind_gate_vacuous
#assert_axioms forged_satisfied2
#assert_axioms forged_not_staged
#assert_axioms deployed_admits_unbacked
#assert_axioms starkSoundCustom_unsound_over_deployed
#assert_axioms encColl_self_false
#assert_axioms encColl_refutes_poseidon2CR
#assert_axioms vk_determined_or_encColl
#assert_axioms vk_determined_of_noEncColl
#assert_axioms vk_determined_of_noEncColl_vkHeaded
#assert_axioms floorEngine_binds_or_collides
#assert_axioms refFloorEngine_binding
#assert_axioms constFloorEngine_collides

end Dregg2.Circuit.CustomCarrierAttack
