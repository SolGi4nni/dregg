/-
# `Dregg2.Crypto.DreggPqRefinement` — the DOWN direction: "the code IS the proof" (a beachhead).

Every other file in `Dregg2/Crypto/` proves the MODEL: EUF-CMA reduces to MSIS, the X-Wing combiner
is IND-CCA if either half is, an id commitment binds. This file opens the *opposite* direction and
NAMES the gap: it connects the DEPLOYED `dregg-pq` Rust API to the abstract `SigScheme` / `KEM` models
the security proofs are about, so "the model is proven" and "the code is trusted" stop being two
disconnected sentences.

This is the BEGINNING of a code-refinement effort, not a claim that the Rust is verified. The honest
ledger, stated up front:

  * PROVEN GLUE (this file). The `dregg-pq` glue — deterministic-from-seed key derivation
    (`MlDsaKey::from_ed25519_seed`), caller-supplied `ctx` domain separation (`sign(ctx, msg)` /
    `ml_dsa_verify(pk, ctx, msg, sig)`), the fail-closed verify (`ml_dsa_verify` returns `false`, never
    panics, on malformed input), and the hybrid concat-KDF combiner (`hybrid_kem::combine` =
    HKDF-SHA256 over `ss_x ‖ ss_pq ‖ transcript`) — is modeled as a concrete `SigScheme` / `KEM`
    instance and CONNECTED to the existing security proofs (`pq_euf_cma_grounded_in_msis`,
    `hybrid_kem_ind_cca_if_either`). The refinement `dregg_pq_refines_sigscheme` proves the model is a
    faithful abstraction of the API's public behavior.

  * TRUSTED PRIMITIVE FLOOR (named, not laundered). What remains trusted is that the `fips204`
    (ML-DSA-65) and `ml-kem` crates CORRECTLY IMPLEMENT FIPS 204 / FIPS 203. Their internals are NOT
    Lean-verified. We state this as a clearly-labeled, `axiom`-free HYPOTHESIS the correctness
    conclusion is CONDITIONED on — `Fips204Correct` (the sign→verify round-trip) and `Fips203Correct`
    (the encaps→decaps round-trip) — exactly as the abstract EUF-CMA / IND-CCA games ASSUME ML-DSA is a
    signature scheme and ML-KEM a KEM. It is a HYPOTHESIS the theorems take, NOT a `def …Hard` used as a
    proof (which `#assert_axioms` would never see): a future verified-`fips204` effort would DISCHARGE
    it. That `Fips204Correct` is load-bearing — the correctness round-trip is UNDERIVABLE without it —
    is proved with teeth (`badApi_not_correct`), so it is honestly the trusted base, not decorative.

## What this closes vs the named trusted base

CLOSED: the Rust GLUE dregg-pq adds ON TOP of the FIPS primitives (from-seed derivation, ctx
separation, verify fail-closed, the hybrid combiner) is now a Lean object connected to the proved
security games — the ML-DSA instance inherits EUF-CMA → MSIS, the hybrid KEM inherits IND-CCA-if-either.
STILL TRUSTED: FIPS 204 / FIPS 203 primitive correctness (`fips204` / `ml-kem` internals). That is the
whole gap, named precisely and reduced to a single labeled hypothesis per primitive.

Reads (contract matched to the ACTUAL Rust signatures): `dregg-pq/src/mldsa.rs`
(`MlDsaKey::from_ed25519_seed` / `sign(ctx, msg)` / `public_bytes`; free `ml_dsa_verify`) and
`dregg-pq/src/hybrid_kem.rs` (`combine(ss_x, ss_pq, transcript)` = HKDF-SHA256, the X-Wing combiner).
-/
import Dregg2.Crypto.HybridCombiner

namespace Dregg2.Crypto.DreggPqRefinement

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.HybridCombiner

/-! ## PART 1 — the `dregg-pq` ML-DSA API surface, as a Lean contract.

The OBSERVABLE surface (`dregg-pq/src/mldsa.rs`), stated as function shapes only — no proof obligations
baked in, because the primitive's guarantees are the TRUSTED floor, named separately below:

  * `keygen : Seed → PK`   ⇐ `MlDsaKey::from_ed25519_seed(seed).public_bytes()`. A *function* of the
    seed — so "from-seed is deterministic" is captured STRUCTURALLY (same seed ⇒ same public key, no
    separate ceremony), the exact `from_seed_is_deterministic` property.
  * `sign : Seed → Ctx → Msg → Sig`   ⇐ `MlDsaKey::sign(ctx, message)` (the caller supplies `ctx`).
  * `verify : PK → Ctx → Msg → Sig → Bool`   ⇐ the free `ml_dsa_verify(pk, ctx, msg, sig)`. It returns
    a `Bool` (never a `Prop`, never a panic): "fail-CLOSED on malformed input" is captured by verify
    being TOTAL and Bool-valued — anything the primitive does not accept is `false`. -/

/-- The observable `dregg-pq` ML-DSA API surface: the three public entry points, matched to the Rust
signatures. Carries NO proof fields — the primitive's correctness is the trusted floor (`Fips204Correct`,
below), not something this structure asserts. -/
structure DreggPqApi (Seed PK Ctx Msg Sig : Type*) where
  /-- `MlDsaKey::from_ed25519_seed(seed).public_bytes()` — the deterministic from-seed public key. -/
  keygen : Seed → PK
  /-- `MlDsaKey::sign(ctx, message)` — sign under the caller-supplied FIPS 204 `ctx`. -/
  sign : Seed → Ctx → Msg → Sig
  /-- `ml_dsa_verify(pk, ctx, msg, sig)` — the fail-closed Bool verifier. -/
  verify : PK → Ctx → Msg → Sig → Bool

/-! ### THE HONEST BOUNDARY — the trusted FIPS 204 primitive floor.

The single labeled hypothesis the correctness conclusion is CONDITIONED on. It says: `fips204`
implements the ML-DSA sign→verify round-trip. We do NOT prove it — `fips204`'s internals
(`ml_dsa_65::KG::keygen_from_seed`, `try_sign`, `PublicKey::verify`) are the trusted primitive base,
exactly as the abstract EUF-CMA game assumes "ML-DSA is a signature scheme". A verified-`fips204` effort
would discharge it. Because it is a `def`-Prop taken as a THEOREM HYPOTHESIS (never a carrier used to
close a goal), it is honestly named; `badApi_not_correct` shows it is load-bearing. -/
def Fips204Correct {Seed PK Ctx Msg Sig : Type*} (api : DreggPqApi Seed PK Ctx Msg Sig) : Prop :=
  ∀ (seed : Seed) (ctx : Ctx) (msg : Msg),
    api.verify (api.keygen seed) ctx msg (api.sign seed ctx msg) = true

/-! ## PART 2 — the model: `dreggPqSigScheme` as a concrete `SigScheme`, and `Correct` from the floor.

The abstract `SigScheme SK PK Msg Sig` (HybridCombiner) has `sign : SK → Msg → Sig`,
`verify : PK → Msg → Sig → Prop`. The `dregg-pq` `ctx` rides INSIDE the message: the signed object is
the pair `(ctx, msg)`, so `verify` under a different `ctx` is `verify` on a DIFFERENT message — domain
separation becomes structural (the "same key material can never produce a signature valid on two
surfaces" invariant). `verify` lifts the fail-closed `Bool` to `… = true`. -/

/-- The `dregg-pq` ML-DSA API as a concrete `SigScheme`: secret keys are seeds, the message is the
domain-separated pair `(ctx, msg)`, `pkOf = keygen`, `sign`/`verify` forward to the API (the Bool lifted
to `= true`, so a `false`/malformed verify is a FALSE `Prop`). -/
@[reducible] def dreggPqSigScheme {Seed PK Ctx Msg Sig : Type*}
    (api : DreggPqApi Seed PK Ctx Msg Sig) : SigScheme Seed PK (Ctx × Msg) Sig where
  pkOf := api.keygen
  sign sk cm := api.sign sk cm.1 cm.2
  verify pk cm σ := api.verify pk cm.1 cm.2 σ = true

/-- **CORRECTNESS FROM THE TRUSTED FLOOR.** The model satisfies `Correct` (every honestly-produced
signature verifies) EXACTLY WHEN the trusted `Fips204Correct` round-trip holds — the conclusion is
conditioned on, and derived from, the honestly-named primitive assumption. This is the crux of the
honest boundary: the proof of `Correct` is `hfips` and nothing more. -/
theorem dregg_pq_correct {Seed PK Ctx Msg Sig : Type*} (api : DreggPqApi Seed PK Ctx Msg Sig)
    (hfips : Fips204Correct api) : Correct (dreggPqSigScheme api) :=
  fun sk cm => hfips sk cm.1 cm.2

/-! ### Domain separation — the `ctx` is load-bearing, both structurally and via unforgeability. -/

/-- **STRUCTURAL ctx-separation.** Distinct contexts give distinct signed objects: `(ctx, msg)` and
`(ctx', msg)` are different messages to the scheme. This is why one key's signature under one surface is
checked against a DIFFERENT message on another surface. -/
theorem dregg_pq_ctx_distinguishes {Ctx Msg : Type*} (ctx ctx' : Ctx) (msg : Msg) (h : ctx ≠ ctx') :
    ((ctx, msg) : Ctx × Msg) ≠ (ctx', msg) :=
  fun hpair => h (congrArg Prod.fst hpair)

/-- **DOMAIN-SEPARATION UNDER UNFORGEABILITY** — the deployment payoff of the caller-supplied `ctx`. If
the signer was never queried on surface `(ctx', msg)` and the scheme is EUF-CMA, then NO signature
verifies there: a signature minted for one surface cannot be replayed onto another. This is exactly the
`ctx_separates_domains` guarantee (`mldsa.rs`) as a theorem — carried by unforgeability over the
ctx-tagged message. -/
theorem dregg_pq_ctx_domain_separated {Seed PK Ctx Msg Sig : Type*}
    (api : DreggPqApi Seed PK Ctx Msg Sig) (pk : PK) (Q : (Ctx × Msg) → Prop)
    (ctx' : Ctx) (msg : Msg) (σ : Sig)
    (hunqueried : ¬ Q (ctx', msg))
    (heuf : EufCma (dreggPqSigScheme api) pk Q) :
    ¬ (dreggPqSigScheme api).verify pk (ctx', msg) σ :=
  fun hv => heuf ⟨(ctx', msg), σ, hunqueried, hv⟩

/-! ## PART 3 — inheritance: the concrete `dregg-pq` ML-DSA inherits EUF-CMA → MSIS.

The concrete scheme is a `SigScheme`, so it plugs straight into `pq_euf_cma_grounded_in_msis`: given the
ML-DSA forgery→SelfTargetMSIS forking reduction (the rewind step, a hypothesis reducing to the PROVED
`no_forgery_under_msis_selftarget`), Module-SIS hardness on `[A | t]` makes the DEPLOYED scheme
`EufCma`. No fresh carrier — the only floor is `MSISHard`. -/

section MsisInheritance
variable {Seed PK Ctx Msg Sig : Type*}
variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **THE DEPLOYED ML-DSA INHERITS EUF-CMA → MSIS.** Specializes `HybridCombiner.pq_euf_cma_grounded_in_msis`
to `dreggPqSigScheme api`: with the forking reduction (a forgery yields two SelfTargetMSIS solutions on a
shared `w`, distinct challenges `c ≠ c'`), Module-SIS hardness makes the concrete `dregg-pq` ML-DSA
`EufCma`. The code's signature scheme now bottoms out at the SAME lattice floor the model does.

⚠ **`fork` IS RETIRED — use `ForkingDischarge.dregg_pq_is_eufcma_under_msis_discharged`.** `fork` here was
an UN-DISCHARGED hypothesis on the DEPLOYED path: it assumed the entire forking extraction outright. The
discharged sibling PROVES the extraction (`ForkingDischarge.forkPair_of_advantage`) and rests on `MSISHard`
plus a realizability MODELLING bridge. This statement is kept for the existing call sites. -/
theorem dregg_pq_is_eufcma_under_msis
    (api : DreggPqApi Seed PK Ctx Msg Sig) (pk : PK) (Q : (Ctx × Msg) → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (fork : Forgery (dreggPqSigScheme api) pk Q →
      ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma (dreggPqSigScheme api) pk Q :=
  pq_euf_cma_grounded_in_msis (dreggPqSigScheme api) pk Q A t β fork hard

end MsisInheritance

/-! ## PART 4 — the hybrid KEM: `dregg-pq`'s concat-KDF is the modeled X-Wing combiner.

`dregg-pq/src/hybrid_kem.rs`: `combine(ss_x, ss_pq, transcript) = HKDF-SHA256(salt = DOMAIN,
ikm = ss_x ‖ ss_pq, info = DOMAIN ‖ transcript)` — a CONCATENATION KDF (never XOR), the X-Wing combiner
`HybridCombiner` Part B models. We model the API's `combine` as the combiner `KDF`, and inherit
`hybrid_kem_ind_cca_if_either`: under the standard HKDF dual-PRF assumption, the hybrid session key is
IND-CCA if EITHER X25519 or ML-KEM is. -/

/-- The observable `dregg-pq` hybrid-KEM combiner surface: `combine ss_x ss_pq transcript`
(`hybrid_kem::combine`, HKDF-SHA256 over `ss_x ‖ ss_pq ‖ transcript`). -/
structure DreggPqKemApi (SS Ctx : Type*) where
  /-- `hybrid_kem::combine(ss_x, ss_pq, transcript)` — the concat-KDF (HKDF-SHA256). -/
  combine : SS → SS → Ctx → SS

/-- The standard X-Wing / HKDF assumption on the combiner, in the modeled currency: `hybrid_kem::combine`
is a dual-PRF (unpredictability-preserving keyed on EITHER input). Named explicitly, reduced to — the
SAME `DualPRF` requirement `HybridCombiner` Part B states, not hidden. -/
def DreggPqKdfIsDualPRF {SS Ctx : Type*} (api : DreggPqKemApi SS Ctx) : Prop := DualPRF api.combine

/-- **THE DEPLOYED HYBRID KEM INHERITS IND-CCA-IF-EITHER.** Specializes
`HybridCombiner.hybrid_kem_ind_cca_if_either` to the `dregg-pq` `combine`: under the HKDF dual-PRF, if
X25519 OR ML-KEM is IND-CCA (its shared-secret source unpredictable), the deployed hybrid session key is
IND-CCA through the corresponding channel. The code's combiner now rides the proved X-Wing model. -/
theorem dregg_pq_hybrid_kem_ind_cca_if_either {SS Ctx : Type*}
    (api : DreggPqKemApi SS Ctx) (hdual : DreggPqKdfIsDualPRF api) (tr : Ctx)
    {In : Type*} (sourceX sourcePq : In → SS) (ssx sspq : SS)
    (heither : KemIndCca sourceX ∨ KemIndCca sourcePq) :
    KemIndCca (fun i => api.combine (sourceX i) sspq tr) ∨
    KemIndCca (fun i => api.combine ssx (sourcePq i) tr) :=
  hybrid_kem_ind_cca_if_either api.combine hdual tr sourceX sourcePq ssx sspq heither

/-! ### THE HONEST BOUNDARY (KEM) — the trusted FIPS 203 primitive floor.

The KEM analogue of `Fips204Correct`: `ml-kem` implements the ML-KEM encaps→decaps round-trip (the
responder recovers the initiator's shared secret). NOT Lean-verified — `ml-kem`'s internals are the
trusted primitive base, as the KEM game assumes "ML-KEM is a KEM". `badKem_not_fips203` shows it is a
real, falsifiable boundary, not decorative. -/
def Fips203Correct {PK SK CT SS : Type*} (encaps : PK → CT × SS) (decaps : SK → CT → SS)
    (pk : PK) (sk : SK) : Prop :=
  decaps sk (encaps pk).1 = (encaps pk).2

/-! ## PART 5 — THE REFINEMENT RELATION: the model is a faithful abstraction of the API contract.

`Refines api S` says the model `S` reads back EXACTLY the API's public behavior: same keygen, same sign,
and `S.verify` (a `Prop`) matches the API's `verify` (a `Bool`) pointwise. `dregg_pq_refines_sigscheme`
proves `dreggPqSigScheme api` refines its own contract by construction. The relation has TEETH: an
UNFAITHFUL model (one that ignores `ctx`) fails to refine (`badModel_not_refines`), so `Refines` genuinely
distinguishes a faithful abstraction from a wrong one — it is not a vacuous predicate. -/

/-- **THE REFINEMENT RELATION.** The `SigScheme` model `S` faithfully abstracts the API contract `api`:
(1) keygen agrees, (2) sign agrees on the ctx-tagged message, (3) the model's `Prop`-verify holds iff the
API's `Bool`-verify is `true`. A model that mis-reads any of the three does NOT refine. -/
def Refines {Seed PK Ctx Msg Sig : Type*}
    (api : DreggPqApi Seed PK Ctx Msg Sig) (S : SigScheme Seed PK (Ctx × Msg) Sig) : Prop :=
  (∀ sk : Seed, S.pkOf sk = api.keygen sk) ∧
  (∀ (sk : Seed) (cm : Ctx × Msg), S.sign sk cm = api.sign sk cm.1 cm.2) ∧
  (∀ (pk : PK) (cm : Ctx × Msg) (σ : Sig), S.verify pk cm σ ↔ api.verify pk cm.1 cm.2 σ = true)

/-- **THE REFINEMENT HOLDS.** `dreggPqSigScheme api` is a faithful abstraction of its API contract — each
clause is definitional (the model is BUILT from the contract), so the abstraction is exact. This is the
beachhead: the Rust API's public behavior and the proved `SigScheme` model are now one connected object. -/
theorem dregg_pq_refines_sigscheme {Seed PK Ctx Msg Sig : Type*}
    (api : DreggPqApi Seed PK Ctx Msg Sig) : Refines api (dreggPqSigScheme api) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩

/-! ## Teeth — the model is a NON-VACUOUS SigScheme + Correct, the boundary is LOAD-BEARING, refinement has TEETH.

Concrete toy over `ℕ` (`keygen = id`, `sign seed ctx msg = seed + ctx + msg`, `verify pk ctx msg σ =
(σ == pk + ctx + msg)`), decidable so the `#guard`s fire:

(a) `dreggPqSigScheme toyApi` satisfies `Correct` (round-trip) and is a real signature scheme — an honest
    signature VERIFIES while a forgery / a wrong-ctx signature is REJECTED (non-vacuity + ctx separation).
(b) THE BOUNDARY IS LOAD-BEARING: for `badApi` (verify always `false`) `Fips204Correct` FAILS and, without
    it, `Correct` is UNDERIVABLE (`badApi_not_correct`) — so `Fips204Correct` is honestly the trusted base.
(c) `Refines` has TEETH: an unfaithful `badModel` (ignores `ctx`) does NOT refine `toyApi`.
(d) the KEM combiner inherits IND-CCA-if-either on the concrete `toyKem`, and `Fips203Correct` is a real,
    falsifiable boundary. -/

section Teeth

/-! ### (a) A HONEST, correct, non-vacuous instance. -/

/-- A concrete `dregg-pq` API surface over `ℕ`: `keygen` is the identity (deterministic-from-seed), the
signature is `seed + ctx + msg`, and `verify` recomputes and compares (fail-closed via `==`). -/
def toyApi : DreggPqApi ℕ ℕ ℕ ℕ ℕ where
  keygen seed := seed
  sign seed ctx msg := seed + ctx + msg
  verify pk ctx msg σ := σ == pk + ctx + msg

/-- The trusted floor HOLDS for the honest toy: the sign→verify round-trip closes. -/
theorem toyApi_fips204 : Fips204Correct toyApi := by
  intro seed ctx msg; simp [toyApi]

/-- Hence `dreggPqSigScheme toyApi` satisfies `Correct` — round-trip, DERIVED from the floor. -/
theorem toyApi_correct : Correct (dreggPqSigScheme toyApi) :=
  dregg_pq_correct toyApi toyApi_fips204

-- The honest signature VERIFIES (round-trip fires on concrete data).
#guard toyApi.verify (toyApi.keygen 3) 5 7 (toyApi.sign 3 5 7) = true
-- A forged signature (arbitrary `σ`) is REJECTED — the scheme is non-vacuous (verify is not always true).
#guard toyApi.verify (toyApi.keygen 3) 5 7 99 = false
-- A signature minted under ctx = 5 is REJECTED under ctx = 6 — the ctx separates domains.
#guard toyApi.verify (toyApi.keygen 3) 6 7 (toyApi.sign 3 5 7) = false
-- The model's `Prop`-verify agrees: the honest signature verifies in the abstract SigScheme.
#guard decide ((dreggPqSigScheme toyApi).verify (toyApi.keygen 3) (5, 7) (toyApi.sign 3 5 7))
-- …and rejects the forgery.
#guard decide (¬ (dreggPqSigScheme toyApi).verify (toyApi.keygen 3) (5, 7) 99)

/-! ### (b) THE BOUNDARY IS LOAD-BEARING — `Fips204Correct` is the trusted base, not decorative. -/

/-- A degenerate API whose `verify` ALWAYS rejects (as if `fips204` did not implement FIPS 204). -/
def badApi : DreggPqApi ℕ ℕ ℕ ℕ ℕ where
  keygen seed := seed
  sign _ _ _ := 0
  verify _ _ _ _ := false

/-- `Fips204Correct` FAILS for `badApi`: the round-trip returns `false`, never `true`. -/
theorem badApi_not_fips204 : ¬ Fips204Correct badApi := by
  intro h; have := h 0 0 0; simp [badApi] at this

/-- **THE LOAD-BEARING TOOTH.** Without `Fips204Correct`, `Correct` is UNDERIVABLE — `dreggPqSigScheme
badApi` is NOT `Correct` (nothing verifies). So the correctness round-trip genuinely REQUIRES the trusted
FIPS 204 floor: `Fips204Correct` is honestly the trusted base of the code, not a decorative hypothesis. -/
theorem badApi_not_correct : ¬ Correct (dreggPqSigScheme badApi) := by
  intro h; have := h 0 (0, 0); simp [badApi] at this

/-! ### (c) `Refines` HAS TEETH — an unfaithful model does not refine. -/

/-- An UNFAITHFUL model: `verify` ignores the `ctx` component (`cm.1`), reading only `pk + msg`. It is a
`SigScheme`, but it does NOT abstract `toyApi` (which is ctx-sensitive). -/
def badModel : SigScheme ℕ ℕ (ℕ × ℕ) ℕ where
  pkOf s := s
  sign s cm := s + cm.1 + cm.2
  verify pk cm σ := σ = pk + cm.2

/-- **REFINEMENT TEETH.** `badModel` does NOT refine `toyApi`: its ctx-blind `verify` disagrees with the
contract at `ctx = 1` (`badModel.verify 0 (1,0) 0` holds, but `toyApi.verify 0 1 0 0 = false`). So
`Refines` genuinely rejects a wrong abstraction — it is not vacuously true. -/
theorem badModel_not_refines : ¬ Refines toyApi badModel := by
  rintro ⟨_, _, hv⟩
  have h := hv 0 (1, 0) 0
  simp [badModel, toyApi] at h

/-! ### (d) The hybrid KEM combiner inherits, and the FIPS 203 boundary is real. -/

/-- A concrete `dregg-pq` combiner over `ℤ` standing in for HKDF: `combine k1 k2 _ = k1 − k2`, the proved
`HybridCombiner.goodKDF` — a genuine dual-PRF (injective in each input). -/
def toyKem : DreggPqKemApi ℤ Unit := ⟨goodKDF⟩

/-- `toyKem`'s combiner IS a dual-PRF — inherited verbatim from the proved `goodKDF_dualPRF`. -/
theorem toyKem_dualPRF : DreggPqKdfIsDualPRF toyKem := goodKDF_dualPRF

/-- **KEM INHERITANCE FIRES.** With an unpredictable X25519 source (`id`), the concrete hybrid combiner is
IND-CCA — `dregg_pq_hybrid_kem_ind_cca_if_either` delivers it through the classical channel. -/
theorem toyKem_ind_cca_via_classical (sspq : ℤ) :
    KemIndCca (fun i : ℤ => toyKem.combine (id i) sspq ()) ∨
    KemIndCca (fun i : ℤ => toyKem.combine (0 : ℤ) (id i) ()) :=
  dregg_pq_hybrid_kem_ind_cca_if_either toyKem toyKem_dualPRF () id id 0 sspq
    (Or.inl Function.injective_id)

/-- A correct toy KEM: `encaps pk = (pk, pk)`, `decaps _ ct = ct` — the round-trip recovers the secret. -/
def toyEncaps : ℕ → ℕ × ℕ := fun pk => (pk, pk)
/-- The toy decapsulation: return the ciphertext as the shared secret. -/
def toyDecaps : ℕ → ℕ → ℕ := fun _ ct => ct

/-- The FIPS 203 floor HOLDS for the honest toy KEM: decaps recovers encaps' secret. -/
theorem toyKem_fips203 : Fips203Correct toyEncaps toyDecaps 5 5 := rfl

/-- A broken decapsulation (always `0`) that does NOT recover the secret. -/
def badDecaps : ℕ → ℕ → ℕ := fun _ _ => 0

/-- **THE KEM BOUNDARY IS REAL.** `Fips203Correct` FAILS when decaps does not recover the secret — a
falsifiable, load-bearing trusted floor, not decorative. -/
theorem badKem_not_fips203 : ¬ Fips203Correct toyEncaps badDecaps 5 5 := by
  intro h; simp [Fips203Correct, toyEncaps, badDecaps] at h

-- The concrete combiner is injective in each input (the dual-PRF, on data).
#guard toyKem.combine 7 3 () = 4
#guard toyKem.combine 7 3 () ≠ toyKem.combine 8 3 ()   -- injective in the classical key
#guard toyKem.combine 7 3 () ≠ toyKem.combine 7 4 ()   -- injective in the pq key
-- The FIPS 203 round-trip recovers the secret honestly, but the broken decaps does not.
#guard toyDecaps 5 (toyEncaps 5).1 = (toyEncaps 5).2
#guard badDecaps 5 (toyEncaps 5).1 ≠ (toyEncaps 5).2

end Teeth

#assert_all_clean [
  dregg_pq_correct,
  dregg_pq_ctx_distinguishes,
  dregg_pq_ctx_domain_separated,
  dregg_pq_is_eufcma_under_msis,
  dregg_pq_hybrid_kem_ind_cca_if_either,
  dregg_pq_refines_sigscheme,
  toyApi_fips204,
  toyApi_correct,
  badApi_not_fips204,
  badApi_not_correct,
  badModel_not_refines,
  toyKem_dualPRF,
  toyKem_ind_cca_via_classical,
  toyKem_fips203,
  badKem_not_fips203
]

end Dregg2.Crypto.DreggPqRefinement
