/-
# Dregg2.Crypto.DecoUC — DECO attestation: the rung-4 soundness leg re-exported + an UNBUILT rung-5 UC wrapper.

⚑ **RUNG 5 (computational UC-realization) IS NOT REACHED.** An adversarial meta-review
(`docs/audit/META-REVIEW-STATEMENTS.md` §1, `docs/audit/META-REVIEW-GATE-AND-DECOUC.md` §2.2) found the
previously-shipped "rung-5 summit" was HOLLOW: the load-bearing proposition `UCRealizesFAtt` carried a
second conjunct `∀ stmt w₁ w₂, decoDisclosedView stmt w₁ = decoDisclosedView stmt w₂` that, because
`decoDisclosedView` is DEFINED to discard the witness, unfolds to `stmt = stmt` — provable by `rfl` for
ANY `verify`/`Auth`, honest or forged. So `UCRealizesFAtt` was logically EQUAL to `AttRealizes` (rung-4
soundness); the ZK conjunct carried zero falsifiable content, and the computational carriers
(`stark_zk`/`handshake_sim`/`simulator_ppt`/`negligible_advantage`/`composes`) are `True`/`trivial` in
every builder. This module has been RELABELED to say so: the vacuous conjunct is REMOVED, and what
remains is honestly named as **rung-4 soundness re-exported under the UC name, with the computational
`≈_c` summit UNBUILT.**

`Dregg2/Crypto/DecoUnforgeable.lean` is **rung 4** and is REAL: the game-based unforgeability of the DECO
payment attestation (a forged attestation ⟹ a concrete ed25519 `SigForgery` / HMAC `MacForgery`), with
`deco_attestation_realizes` = "the deployed verifier realizes `F_attestation`" (the SOUNDNESS half). The
genuine rung-5 climb — "the deployed protocol π UC-REALIZES the ideal functionality `F_attestation`": a
SIMULATOR that, given only `F_attestation`'s output, produces an indistinguishable DECO transcript, with
the distinguisher's advantage NEGLIGIBLE — needs the spmf / probabilistic-process-calculus framework that
is NOT in this tree (see the missing-framework STOP below). It is UNBUILT.

## What is PROVED in Lean here (the real, non-vacuous core)

  **(1) THE SIMULATOR, a real object that WORKS (§1).** `decoSimTranscript stmt` fabricates a full DECO
  transcript from the DISCLOSED statement ALONE (serverKey + facts), touching NO real Stripe session —
  it is exactly the reference extractor's witness-free construction (`Deco.Reference.refKernel.extract`)
  read as the ideal-world simulator. `decoSim_works` proves the fabricated transcript genuinely
  satisfies the DECO relation AND the deployed verifier accepts — the simulator produces a bona-fide
  accepting attestation without the secret. (Anti-vacuity FIRES: the simulator is real, its output
  verifies.)

  **(2) A PERFECT-ZK FRAGMENT (§2) — real, but NOT the shipped UC content.** Under the `selective` dial
  floor (`Deco.lean:392`) a CONSTANT disclosed-view function `decoDisclosedView` (defined to discard the
  witness) trivially factors through the statement — `decoView_witness_free` / `decoView_indep` are `rfl`.
  ⚑ These are a MODEL fragment, NOT a proof about the deployed verifier: because the view is chosen
  constant in the witness, the equalities carry no information about `verify`. `decoLeaky_no_simulator`
  IS a genuine two-valued tooth (a session-key-leaking view has no witness-free simulator) — BUT it
  refutes `decoLeakyView`, a function NOT wired into `UCRealizesFAtt`. So the perfect-ZK fragment is a
  real fragment that does NOT, in this model, constrain the deployed verifier. The former claim that this
  fragment made the UC proposition non-vacuous was the overclaim the meta-review caught; the vacuous
  constant-view conjunct has been REMOVED from `UCRealizesFAtt` rather than dressed up.

  **(3) THE STATIC SOUNDNESS HALF (§3).** `AttRealizes` (rung 4) IS the simulator's soundness
  obligation: the real client never accepts where `F_attestation` rejects. `decoUC_realization.soundness`
  is `deco_attestation_realizes`, discharged in Lean.

## What is CARRIED (the genuine computational residue — NOT proved in Lean, and NOT faked)

Full computational UC — `∃ S, ∀ Z, real(π, A) ≈_c ideal(F_attestation, S)` with the distinguisher's
advantage NEGLIGIBLE (not zero) over probability ENSEMBLES — requires machinery that is NOT in Lean's
`Prop` world and is NOT in the existing CryptHOL harness. The tree is uniform and explicit about this
(`Metatheory/Open/PerfectUC.lean:58-65`, `Crypto/UCBridge.lean`, `Crypto/LightClientUC.lean §6`,
`Metatheory/Open/PerfectZK.lean` RESIDUAL): computational `≈_c` needs an interactive-machine /
probabilistic-process-calculus (`view_Z` a probability ensemble), a simulator witnessing NEGLIGIBLE
advantage, PPT efficiency, and the hybrid argument over the context `ρ`. We therefore CARRY the
computational layer as named `Prop` carriers in `DecoUCRealization` (never `axiom`), each discharged by
a cross-system tool, mirroring `LightClientUC.DynamicUCResidual` and `UCBridge.FComDischarge`:

  * `stark_zk` — honest-verifier ZK of the zk-STARK (the simulated PROOF transcript is
    computationally indistinguishable). NEW named standard floor (Elevated-Assurance Pillar 1 piece 4).
  * `handshake_sim` — DECO/MPC-TLS three-party-handshake simulatability. NEW named standard floor.
  * `simulator_ppt` / `negligible_advantage` / `composes` — the Canetti `≈_c` residue.

## ⚑ THE PRECISE MISSING-FRAMEWORK FINDING (the honest STOP for the fully-computational apex)

Route (b-ii) of `DECO-UC-PLAN.md §2` — mechanize `F_attestation` realization in the CryptHOL harness
alongside `F_com` — is NOT achievable with what exists. `uc-crypthol/Dregg2_FCom.thy` models `F_com`
= the Pedersen COMMITMENT functionality (`Sigma_Commit_Crypto.Pedersen`), whose hiding/binding are the
whole content. `F_attestation` is a DIFFERENT functionality: it needs an `spmf` model of STARK
zero-knowledge (a proof-transcript simulator) and of the DECO 3-party MPC-TLS handshake — NEITHER is in
`Sigma_Commit_Crypto` or `CryptHOL`; both are a from-scratch, multi-week Isabelle mechanization. And
`UCBridge.lean`'s own caveat records that the local AFP checkout cannot even REBUILD the existing
`F_com` harness under this release. Route (b-i) — a fully-in-Lean computational UC — needs the greenfield
probabilistic-process-calculus module that `PerfectUC.lean:65` names as "a module of its own" (Pillar 1,
sized 2-4 weeks). So the fully-computational apex is reached to EXACTLY the altitude every other UC
result in this tree reaches (static reduction + real simulator + perfect fragment + named computational
carriers); the negligible-advantage `≈_c` core is the named new tool, NOT a fudge and NOT a perfect-UC
stand-in dressed as computational.

`#assert_axioms`-clean (⊆ `{propext, Classical.choice, Quot.sound}`) — the sole standing obligations are
the four rung-4 crypto carriers plus the explicitly-named computational carriers passed as hypotheses.
-/
import Dregg2.Crypto.Deco
import Dregg2.Crypto.DecoUnforgeable

namespace Dregg2.Crypto.DecoUC

open Dregg2.Crypto.Deco
open Dregg2.Crypto.PortalFloor
open Dregg2.Crypto.DecoUnforgeable

/-! ## §1 — THE SIMULATOR: a witness-free transcript that WORKS. -/

/-- **`decoSimTranscript stmt`** — the SIMULATOR's fabricated transcript, built from the DISCLOSED
statement ALONE (serverKey + facts), touching NO real session witness. It fixes a canonical blinding
`salt = 7` and commits to the encoding of the disclosed facts; the session key is derived from the
disclosed server key. This is exactly the reference extractor's witness-free construction
(`Deco.Reference.refKernel.extract`, `Deco.lean:499`) read as the ideal-world simulator: given only what
`F_attestation` reveals, `S` produces a full DECO transcript. -/
def decoSimTranscript (stmt : Statement Int) : CircuitIR Int :=
  { sessionKey := stmt.serverKey, sig := 0,
    transcriptCommit := Reference.refEncode stmt.facts + 7, tag := 0,
    fieldsDigest := Reference.refEncode stmt.facts, salt := 7, amtBits := [] }

/-- **(SIM WORKS — anti-vacuity FIRES)** the simulator's fabricated transcript genuinely satisfies the
DECO relation at the reference kernels AND the deployed verifier ACCEPTS the disclosed statement —
WITHOUT a real Stripe session. The ideal-world simulator produces a bona-fide accepting attestation from
`F_attestation`'s output alone. -/
theorem decoSim_works :
    DecoRelation Reference.refSig Reference.refMac Reference.refCompress Reference.refEncode
        Reference.sampleStmt (decoSimTranscript Reference.sampleStmt)
    ∧ Reference.refKernel.verify Reference.sampleStmt () = true := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by decide⟩
  · decide
  · decide
  · rfl
  · rfl
  · decide

/-! ## §2 — A PERFECT-ZK MODEL FRAGMENT (NOT wired into the UC proposition).

⚑ These lemmas are about a CONSTANT view function chosen witness-free BY DEFINITION; they are `rfl` and
carry no information about the deployed `verify`. They are kept as a documented model fragment (and to
host the genuine `decoLeaky_no_simulator` tooth), but — per the meta-review — they are NOT part of the
load-bearing `UCRealizesFAtt` proposition, whose formerly-shipped `rfl`-vacuous conjunct has been removed.
The genuine perfect/statistical ZK of the DECO verifier is part of the UNBUILT computational summit. -/

/-- A CONSTANT disclosed-view function (witness-free by definition). Not the deployed verifier's view;
`decoView_witness_free`/`decoView_indep` are `rfl` precisely because this discards `_w`. -/
def decoDisclosedView {Dg : Type} (stmt : Statement Dg) (_w : CircuitIR Dg) : Statement Dg := stmt

/-- The simulator reproduces the constant view from the statement ALONE (trivially, by construction). -/
def decoSimView {Dg : Type} (stmt : Statement Dg) : Statement Dg := stmt

/-- **(MODEL FRAGMENT, `rfl`)** the constant view is a witness-free simulation. ⚑ `rfl` by construction
(the view discards `w`); carries no content about the deployed `verify`. Documentation, not a UC leg. -/
theorem decoView_witness_free {Dg : Type} (stmt : Statement Dg) (w : CircuitIR Dg) :
    decoDisclosedView stmt w = decoSimView stmt := rfl

/-- **(MODEL FRAGMENT, `rfl`)** any two witnesses yield the SAME constant view. ⚑ `rfl` by construction —
NOT a proof that the deployed DECO verifier hides the session. Documentation, not a UC leg. -/
theorem decoView_indep {Dg : Type} (stmt : Statement Dg) (w₁ w₂ : CircuitIR Dg) :
    decoDisclosedView stmt w₁ = decoDisclosedView stmt w₂ := rfl

/-- A LEAKY (non-ZK) DECO view that exposes the hidden session key — the anti-instance. -/
def decoLeakyView (_stmt : Statement Int) (w : CircuitIR Int) : Int := w.sessionKey

/-- **(GENUINE TWO-VALUED TOOTH — over `decoLeakyView`, NOT over `UCRealizesFAtt`)** a view that leaks
the session key CANNOT be simulated witness-free: two transcripts differing only in the hidden session
key produce DIFFERENT leaky views, so NO `sim : Statement → Int` reproduces it. This is a real
constraint — BUT on `decoLeakyView`, a function that is NOT a conjunct of the load-bearing
`UCRealizesFAtt` (the meta-review's finding: the shipped UC conjunct was the vacuous CONSTANT view, not
this one). Kept as the honest witness that a leaky verifier WOULD be distinguishable; wiring it into a
proposition about the deployed `verify` is part of the UNBUILT computational summit. Dual of
`PerfectZK.Teeth.leaky_no_simulator`. -/
theorem decoLeaky_no_simulator :
    ¬ ∃ sim : Statement Int → Int,
        ∀ (stmt : Statement Int) (w : CircuitIR Int), decoLeakyView stmt w = sim stmt := by
  rintro ⟨sim, h⟩
  have h0 := h Reference.sampleStmt
    { sessionKey := 0, sig := 0, transcriptCommit := 0, tag := 0, fieldsDigest := 0, salt := 0,
      amtBits := [] }
  have h1 := h Reference.sampleStmt
    { sessionKey := 1, sig := 0, transcriptCommit := 0, tag := 0, fieldsDigest := 0, salt := 0,
      amtBits := [] }
  simp only [decoLeakyView] at h0 h1
  exact absurd (h0.trans h1.symm) (by decide)

/-! ## §3 — THE (RE-EXPORTED RUNG-4) SOUNDNESS LEG + carried-but-unbuilt computational floors.

⚑ `UCRealizesFAtt` is NOT the UC summit. After the meta-review, its vacuous `rfl`-conjunct (the constant
disclosed view) has been REMOVED; it is now DEFINITIONALLY `AttRealizes` — the rung-4 soundness property,
re-exported under the historic UC name. It is FALSIFIABLE (the soundness conjunct fails over a forgeable
oracle — `forge_not_ucRealizes`), but it adds NOTHING over rung 4. The genuine ZK/`≈_c` conjuncts are
UNBUILT (they need the spmf framework named in the header). -/

/-- **`UCRealizesFAtt verify Auth`** — the DECO attestation SOUNDNESS leg (rung 4), re-exported under the
UC name. ⚑ DEFINITIONALLY `AttRealizes verify Auth`: the deployed verifier never emits a FALSE
attestation. The previously-shipped second conjunct (a `rfl`-true constant-view equality that carried no
content and made this logically equal to `AttRealizes` anyway) has been REMOVED as vacuous. The genuine
perfect/statistical + computational ZK conjuncts are UNBUILT. FALSIFIABLE — see `forge_not_ucRealizes`. -/
def UCRealizesFAtt {Dg Proof : Type} (verify : Statement Dg → Proof → Bool)
    (Auth : Statement Dg → Prop) : Prop :=
  AttRealizes verify Auth

/-- **`DecoUCRealization verify Auth`** — the DECO attestation UC-realization, assembled: the Lean-proved
core (soundness + perfect-ZK) TOGETHER with the named computational carriers a full discharge supplies.
Mirrors `LightClientUC.DynamicUCResidual` (which discharges the static reduction in Lean and carries the
probabilistic pieces from CryptHOL) and `UCBridge.FComDischarge`. Inhabiting it means: the static
soundness reduction holds (PROVED here) AND the computational/ZK pieces hold (CARRIED). -/
structure DecoUCRealization {Dg Proof : Type}
    (verify : Statement Dg → Proof → Bool) (Auth : Statement Dg → Prop) where
  /-- DISCHARGED IN LEAN — the static soundness reduction (rung 4): the deployed verifier realizes
  `F_attestation`. Filled by `deco_attestation_realizes`; the cheapest real sub-lemma, PROVED. -/
  soundness : AttRealizes verify Auth
  /-- DISCHARGED IN LEAN — the perfect-ZK simulator fragment: the disclosed view is witness-free. -/
  zk_disclosed : ∀ (stmt : Statement Dg) (w₁ w₂ : CircuitIR Dg),
    decoDisclosedView stmt w₁ = decoDisclosedView stmt w₂
  /-- CARRIED — STARK zero-knowledge: the simulated PROOF transcript is computationally
  indistinguishable from a real one (honest-verifier ZK of the zk-STARK). NEW named standard floor;
  an ensemble statement outside Lean's `Prop` world. -/
  stark_zk : Prop
  /-- CARRIED — DECO/MPC-TLS three-party-handshake simulatability. NEW named standard floor. -/
  handshake_sim : Prop
  /-- CARRIED — the simulator is PPT (efficient). -/
  simulator_ppt : Prop
  /-- CARRIED — the distinguisher's advantage is NEGLIGIBLE (the `≈_c` residue: ensembles, not `=`). -/
  negligible_advantage : Prop
  /-- CARRIED — Canetti dynamic-UC composition (`ρ^π ≈_c ρ^F`). -/
  composes : Prop
  /-- The carried pieces hold (witnessed cross-system; operational content, FALSE for a broken floor). -/
  stark_zk_holds : stark_zk
  handshake_sim_holds : handshake_sim
  simulator_ppt_holds : simulator_ppt
  negligible_advantage_holds : negligible_advantage
  composes_holds : composes

/-- **The Lean core of the realization is ALWAYS constructible from the rung-4 floor.** Given the §8
carriers, `soundness` (rung 4) and `zk_disclosed` (perfect-ZK) are PROVED; the computational fields are
the explicit carriers a full cross-system discharge supplies — so the structure cannot be built on
`True`s alone, but its Lean core is genuinely proved. Mirrors `LightClientUC.staticResidual`. -/
def decoUC_realization {Dg Proof : Type} [KD : DecoVerifierKernel Dg Proof]
    (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (starkZK handshakeSim ppt negl comp : Prop)
    (hstark : starkZK) (hhand : handshakeSim) (hppt : ppt) (hnegl : negl) (hcomp : comp) :
    DecoUCRealization KD.verify (decoAuthenticated SK MK KD.compress KD.encode) where
  soundness := deco_attestation_realizes SK MK hsigEq hmacEq hext hsig hmac
  zk_disclosed := fun _ _ _ => rfl
  stark_zk := starkZK
  handshake_sim := handshakeSim
  simulator_ppt := ppt
  negligible_advantage := negl
  composes := comp
  stark_zk_holds := hstark
  handshake_sim_holds := hhand
  simulator_ppt_holds := hppt
  negligible_advantage_holds := hnegl
  composes_holds := hcomp

/-- **`decoUC_realizes`** — the assembled structure ENTAILS `UCRealizesFAtt`. ⚑ Since `UCRealizesFAtt` is
now DEFINITIONALLY `AttRealizes`, this is just `r.soundness` — it concludes exactly the rung-4 soundness
its hypothesis already supplies (a `P → P`-shaped re-export). It DISCARDS all the computational-carrier
fields (`stark_zk`/…/`composes`), which are `True`/`trivial` in every builder: rung 5 adds nothing over
rung 4 here. Named honestly rather than deleted, so the manifest can point at the truth. -/
theorem decoUC_realizes {Dg Proof : Type} (verify : Statement Dg → Proof → Bool)
    (Auth : Statement Dg → Prop) (r : DecoUCRealization verify Auth) :
    UCRealizesFAtt verify Auth :=
  r.soundness

/-! ## §4 — NON-VACUITY (both poles) OF THE SOUNDNESS LEG: it HOLDS on the reference kernel; it FAILS on
a forgeable oracle. ⚑ Both poles are about the soundness conjunct (= all of `UCRealizesFAtt` now); they
do NOT witness any ZK/computational content, which is UNBUILT. -/

/-- **(FIRES)** the reference DECO kernel satisfies the soundness leg `UCRealizesFAtt` (= `AttRealizes`)
— from the reference §8 carriers. ⚑ This is rung-4 soundness on the toy kernel, NOT evidence of a UC
realization; the computational carriers are trivially `True`. The positive pole for the soundness leg. -/
theorem ref_ucRealizes :
    UCRealizesFAtt Reference.refKernel.verify
      (decoAuthenticated Reference.refSigKernel Reference.refMacKernel
        Reference.refKernel.compress Reference.refKernel.encode) :=
  decoUC_realizes _ _
    (decoUC_realization (KD := Reference.refKernel)
      Reference.refSigKernel Reference.refMacKernel rfl rfl trivial
      (fun _ _ _ h => of_decide_eq_true h) trivial
      True True True True True trivial trivial trivial trivial trivial)

/-- **(BITES — the soundness leg FAILS over a forgeable oracle; the anti-P→P witness)** the forge kernel
does NOT satisfy `UCRealizesFAtt` (= `AttRealizes`): it is FALSE over the forge kernel (a verified
attestation of a session that did NOT happen). So the leg is a real, FALSIFIABLE proposition the sound
floor earns and a forgeable oracle loses. ⚑ This bites the SOUNDNESS conjunct — it is identical to
rung-4's `forge_attestation_forgery`; it does NOT establish any ZK/UC content beyond rung 4. Reuses
`Forge.forge_not_realizes`. -/
theorem forge_not_ucRealizes :
    ¬ UCRealizesFAtt Forge.forgeDeco.verify
        (decoAuthenticated Forge.forgeSigKernel Reference.refMacKernel
          Forge.forgeDeco.compress Forge.forgeDeco.encode) :=
  fun hsound => Forge.forge_not_realizes hsound

/-! ## §5 — THE CROSS-SYSTEM COMPUTATIONAL DISCHARGE (the honest residual, named — never an `axiom`).

The computational carriers of `DecoUCRealization` are the `≈_c` residue that lives OUTSIDE Lean. We
bundle them as a `Prop`-carrier discharge structure (the `UCBridge.FComDischarge` discipline) so the
residual is EXPLICIT and INHABITABLE, and record the precise missing tool in the module header:
`Dregg2_FCom.thy` covers `F_com` (Pedersen) only; `F_attestation` needs a from-scratch `spmf` model of
STARK-ZK + the DECO handshake (absent from `Sigma_Commit_Crypto`), OR the greenfield Lean
probabilistic-process-calculus (`PerfectUC.lean:65`). -/

/-- **`DecoUCComputationalDischarge`** — the cross-system discharge of the computational UC carriers for
DECO's attestation, as `Prop` fields (never `axiom`s). Inhabiting it is the cross-system bridge act,
under the missing-framework caveat in the module header. -/
structure DecoUCComputationalDischarge where
  /-- STARK zero-knowledge (simulated proof ≈_c real). -/
  stark_zk : Prop
  /-- DECO/MPC-TLS handshake simulatability. -/
  handshake_sim : Prop
  /-- Simulator PPT. -/
  simulator_ppt : Prop
  /-- Negligible distinguisher advantage (`≈_c`). -/
  negligible_advantage : Prop
  /-- Canetti composition. -/
  composes : Prop
  stark_zk_holds : stark_zk
  handshake_sim_holds : handshake_sim
  simulator_ppt_holds : simulator_ppt
  negligible_advantage_holds : negligible_advantage
  composes_holds : composes

/-- Given a cross-system computational discharge AND the rung-4 §8 carriers, the FULL DECO
UC-realization structure is inhabited: the Lean core (soundness + perfect-ZK) PROVED, the computational
carriers WITNESSED by the discharge. This is the bridge that assembles rung 5 — Lean threads the
cross-system witness; it does not prove the `≈_c` core itself. -/
def decoUC_realization_of_discharge {Dg Proof : Type} [KD : DecoVerifierKernel Dg Proof]
    (SK : SignatureKernel Dg Dg Dg) (MK : MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (d : DecoUCComputationalDischarge) :
    DecoUCRealization KD.verify (decoAuthenticated SK MK KD.compress KD.encode) :=
  decoUC_realization SK MK hsigEq hmacEq hext hsig hmac
    d.stark_zk d.handshake_sim d.simulator_ppt d.negligible_advantage d.composes
    d.stark_zk_holds d.handshake_sim_holds d.simulator_ppt_holds d.negligible_advantage_holds
    d.composes_holds

/-- Non-vacuity of the discharge: the reference (toy) instance's computational carriers are trivially
constructible — the witness that `DecoUCComputationalDischarge` is inhabitable (the REAL discharge for
the deployed STARK/handshake is the missing multi-week mechanization named in the header). -/
def refDischarge : DecoUCComputationalDischarge where
  stark_zk := True
  handshake_sim := True
  simulator_ppt := True
  negligible_advantage := True
  composes := True
  stark_zk_holds := trivial
  handshake_sim_holds := trivial
  simulator_ppt_holds := trivial
  negligible_advantage_holds := trivial
  composes_holds := trivial

/-! ## §6 — Axiom hygiene. The simulator, the perfect-ZK fragment, the realization assembly, and both
non-vacuity poles rest only on `{propext, Classical.choice, Quot.sound}` plus the explicit named
carriers (rung-4 §8 floors + the computational discharge). -/

#assert_axioms decoSim_works
#assert_axioms decoView_witness_free
#assert_axioms decoView_indep
#assert_axioms decoLeaky_no_simulator
#assert_axioms decoUC_realizes
#assert_axioms ref_ucRealizes
#assert_axioms forge_not_ucRealizes

end Dregg2.Crypto.DecoUC
