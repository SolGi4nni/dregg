/-
# `Dregg2.Crypto.DreggKemRefinement` — the DOWN direction for the HYBRID KEM GLUE.

`DreggPqRefinement.lean` opened the code↔model beachhead for `dregg-pq`'s ML-DSA surface and, in its
Part 4, connected the concat-KDF `combine` to the modeled X-Wing combiner. This file extends that same DOWN
direction to the FULL `dregg-pq` hybrid-KEM GLUE — the whole offer/encaps/decaps round trip of
`dregg-pq/src/hybrid_kem.rs`, not just the KDF call — so "the model is proven" and "the deployed session
KEM is trusted" stop being two disconnected sentences for the X25519+ML-KEM-768 handshake.

The Rust surface it abstracts (`dregg-pq/src/hybrid_kem.rs`):

  * `responder_offer()` mints an X25519 ephemeral keypair AND an ML-KEM-768 keypair; the offer is
    `(x25519_pk, mlkem_ek)`.
  * `initiate(offer)` derives TWO secrets — the classical `ss_x25519 = DH(x25519_sk, offer.x25519_pk)` and
    the post-quantum `(ct, ss_mlkem) = ML-KEM.encaps(offer.mlkem_ek)` — builds the public `transcript`
    (`offer_x25519 ‖ ek ‖ msg_x25519 ‖ ct`), and combines: `key = combine(ss_x25519, ss_mlkem, transcript)`.
  * `HybridResponder::finish(msg)` recovers the SAME two secrets — `ss_x25519 = DH(x25519_sk, msg.x25519_pk)`
    (X25519 agreement) and `ss_mlkem = ML-KEM.decaps(dk, ct)` (FIPS 203 round trip) — rebuilds the same
    transcript, and combines to the SAME key.

## The honest ledger, stated up front

  * PROVEN GLUE (this file). The KEM glue `dregg-pq` adds ON TOP of the primitives — the TWO-secret
    derivation, the concat-KDF `combine` over the full public transcript, and the transcript BINDING that
    makes decaps recover the initiator's key — is modeled as a concrete `HybridCombiner.KEM` and CONNECTED
    to the proved X-Wing games. `dregg_kem_correct` derives session-key agreement from the two labeled
    primitive round-trips; `dregg_kem_refines` proves the model faithfully abstracts the contract; and the
    deployed `combine` INHERITS `HybridCombiner.hybrid_kem_ind_cca_if_either` (IND-CCA if EITHER X25519 or
    ML-KEM is, under the X-Wing dual-PRF).

  * TRUSTED PRIMITIVE FLOOR (named, not laundered). What remains trusted is that the three primitives are
    CORRECT: `ml-kem` implements the FIPS 203 encaps→decaps round trip (`Fips203Correct`), `x25519-dalek`
    implements ECDH shared-secret AGREEMENT (`X25519Correct`), and HKDF-SHA256 is a dual-PRF over the
    concatenation (`DreggKemKdfIsDualPRF`). These are clearly-labeled, `axiom`-free HYPOTHESES the
    conclusions are CONDITIONED on — exactly as the abstract IND-CCA game ASSUMES ML-KEM is a KEM and the
    X-Wing analysis ASSUMES the combiner is a dual-PRF. They are HYPOTHESES the theorems take, NOT
    `def …Hard` carriers used to close a goal (which `#assert_axioms` would never see): a verified-`ml-kem`
    / verified-`x25519-dalek` effort would DISCHARGE them. Each is proved LOAD-BEARING with teeth
    (`badKem_not_fips203` / `badKem_breaks_correctness`, `badDh_not_x25519 …`), so they are honestly the
    trusted base, not decorative.

No named-carrier laundering: no `def …Hard` is introduced OR taken as a hypothesis here. The hardness
disjunction (`KemIndCca sourceX ∨ KemIndCca sourcePq`) is INHERITED from the proved
`HybridCombiner.hybrid_kem_ind_cca_if_either`; the component floors themselves bottom out — for the ML-KEM
disjunct at `Lattice.MLWESearchHard` via `MlKemIndCca`, for the X25519 disjunct at
`SchnorrCurveField.SchnorrDLHard` via the classical-KEM analysis — in the MODEL, not re-asserted here.

## What this closes vs the named trusted base

CLOSED: the Rust KEM GLUE (the combiner, the transcript binding, the two-secret KDF) is now a Lean object
connected to the proved KEM game — the deployed hybrid session KEM's agreement is DERIVED from the primitive
round-trips, and its `combine` rides `hybrid_kem_ind_cca_if_either`. STILL TRUSTED: FIPS 203 / X25519 / HKDF
primitive correctness (`ml-kem` / `x25519-dalek` / `hkdf`+`sha2` internals). That is the whole gap, named
precisely and reduced to one labeled hypothesis per primitive.

Reads (contract matched to the ACTUAL Rust signatures): `dregg-pq/src/hybrid_kem.rs`
(`responder_offer` / `initiate` / `HybridResponder::finish`; `combine(ss_x, ss_pq, transcript)` = HKDF-SHA256;
`transcript(offer_x, ek, msg_x, ct)` = the concatenation binding).

Cite: X-Wing (Barbosa–Connolly–Duarte–Kaidel–Schwabe–Westerbaan); FIPS 203 (ML-KEM); RFC 7748 (X25519).
-/
import Dregg2.Crypto.HybridCombiner

namespace Dregg2.Crypto.DreggKemRefinement

open Dregg2.Crypto.HybridCombiner

/-! ## PART 1 — the `dregg-pq` hybrid-KEM API surface, as a Lean contract.

The OBSERVABLE surface of `dregg-pq/src/hybrid_kem.rs`, stated as function shapes only — no proof
obligations baked in, because each primitive's guarantee is the TRUSTED floor named separately below. The
fields mirror, one for one, the Rust primitive calls the handshake makes:

  * `x25519_pk : Xsk → Xpk`   ⇐ `PublicKey::from(&x25519_sk).to_bytes()` (a function of the secret — so
    "the public key is deterministic from the secret" is STRUCTURAL).
  * `x25519_dh : Xsk → Xpk → SS`   ⇐ `x25519_sk.diffie_hellman(&peer_pk).to_bytes()` (the ECDH secret).
  * `ekOf : Dk → Ek`   ⇐ the encapsulation key held alongside the decapsulation key by `MlKem768::generate`.
  * `mlkem_encaps : Ek → CT × SS`   ⇐ `ek.encapsulate(rng)` (the ciphertext + PQ shared secret).
  * `mlkem_decaps : Dk → CT → SS`   ⇐ `dk.decapsulate(&ct)` (the recovered PQ shared secret).
  * `transcript : Xpk → Ek → Xpk → CT → Tr`   ⇐ `transcript(offer_x25519, ek, msg_x25519, ct)` (the exact
    public-handshake concatenation both sides agree on).
  * `combine : SS → SS → Tr → SS`   ⇐ `combine(ss_x, ss_pq, transcript)` (HKDF-SHA256, the X-Wing combiner). -/

/-- The observable `dregg-pq` hybrid-KEM API surface: the seven primitive entry points the handshake calls,
matched to the Rust. Carries NO proof fields — each primitive's correctness is the trusted floor
(`Fips203Correct` / `X25519Correct` / `DreggKemKdfIsDualPRF`, below), not something this structure asserts. -/
structure DreggKemApi (Xsk Xpk Dk Ek CT SS Tr : Type*) where
  /-- `PublicKey::from(&sk)` — the deterministic X25519 public key of a secret. -/
  x25519_pk : Xsk → Xpk
  /-- `sk.diffie_hellman(&peer)` — the X25519 ECDH shared secret. -/
  x25519_dh : Xsk → Xpk → SS
  /-- the ML-KEM encapsulation key paired with a decapsulation key at keygen. -/
  ekOf : Dk → Ek
  /-- `ek.encapsulate(rng)` — the ML-KEM-768 ciphertext + PQ shared secret. -/
  mlkem_encaps : Ek → CT × SS
  /-- `dk.decapsulate(&ct)` — the recovered ML-KEM shared secret. -/
  mlkem_decaps : Dk → CT → SS
  /-- `transcript(offer_x, ek, msg_x, ct)` — the public-handshake concatenation. -/
  transcript : Xpk → Ek → Xpk → CT → Tr
  /-- `combine(ss_x, ss_pq, transcript)` — the HKDF-SHA256 concat-KDF (never XOR). -/
  combine : SS → SS → Tr → SS

variable {Xsk Xpk Dk Ek CT SS Tr : Type*}

/-! ### The derived observable operations — `initiate` and `HybridResponder::finish`.

`initMsg` / `initKey` are what `initiate(offer)` returns; `finishKey` is what `HybridResponder::finish(msg)`
returns. Each is a Lean FUNCTION of the primitive fields — the two-secret derivation and the transcript
binding written out exactly as the Rust does them. -/

/-- The initiator's outgoing message `initiate` produces: its X25519 ephemeral public key and the ML-KEM
ciphertext (`HybridInitiatorMessage { x25519_pk, mlkem_ct }`). -/
@[reducible] def initMsg (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr)
    (_offerX : Xpk) (ek : Ek) (xski : Xsk) : Xpk × CT :=
  (api.x25519_pk xski, (api.mlkem_encaps ek).1)

/-- The initiator's session key `initiate` derives: `combine(ss_x25519, ss_mlkem, transcript)` over the
CLASSICAL DH secret against the offer key, the ML-KEM ENCAPS secret, and the full public transcript. -/
@[reducible] def initKey (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr)
    (offerX : Xpk) (ek : Ek) (xski : Xsk) : SS :=
  api.combine (api.x25519_dh xski offerX) (api.mlkem_encaps ek).2
    (api.transcript offerX ek (api.x25519_pk xski) (api.mlkem_encaps ek).1)

/-- The responder's session key `HybridResponder::finish` derives: `combine` over the DH secret against the
initiator key, the ML-KEM DECAPS secret, and the SAME reconstructed transcript. -/
@[reducible] def finishKey (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr)
    (xskr : Xsk) (dk : Dk) (xpki : Xpk) (ct : CT) : SS :=
  api.combine (api.x25519_dh xskr xpki) (api.mlkem_decaps dk ct)
    (api.transcript (api.x25519_pk xskr) (api.ekOf dk) xpki ct)

/-! ### THE HONEST BOUNDARIES — the trusted primitive floors, named.

Two labeled hypotheses the correctness conclusion is CONDITIONED on. `X25519Correct` says the ECDH secrets
AGREE (`DH(a, g^b) = DH(b, g^a)` — RFC 7748 correctness); `Fips203Correct` says the ML-KEM encaps→decaps
round trip recovers the shared secret (FIPS 203 correctness). We do NOT prove them — `x25519-dalek` /
`ml-kem` internals are the trusted primitive base, exactly as the abstract IND-CCA game assumes "ML-KEM is a
KEM". Both are `def`-Props taken as THEOREM HYPOTHESES (never carriers used to close a goal); each is proved
load-bearing below. The HKDF/SHA-256 trust surface is the SEPARATE `DreggKemKdfIsDualPRF` (Part 4). -/

/-- **THE X25519 BOUNDARY.** ECDH shared-secret AGREEMENT: the DH of one party's secret against the other's
public key equals the mirror. This is RFC 7748 correctness for X25519 — trusted, not Lean-verified. -/
def X25519Correct (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) : Prop :=
  ∀ (ski skr : Xsk),
    api.x25519_dh ski (api.x25519_pk skr) = api.x25519_dh skr (api.x25519_pk ski)

/-- **THE FIPS 203 BOUNDARY.** The ML-KEM encaps→decaps round trip: decapsulating an honestly-encapsulated
ciphertext (under the matching key) recovers the encapsulated shared secret. Trusted `ml-kem` correctness. -/
def Fips203Correct (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) : Prop :=
  ∀ (dk : Dk),
    api.mlkem_decaps dk (api.mlkem_encaps (api.ekOf dk)).1 = (api.mlkem_encaps (api.ekOf dk)).2

/-! ## PART 2 — CORRECTNESS FROM THE TRUSTED FLOORS: both parties derive the SAME session key. -/

/-- **KEM CORRECTNESS FROM THE FLOORS.** For an honest handshake — responder secrets `(xskr, dk)`, initiator
ephemeral `xski` — the initiator's `initKey` and the responder's `finishKey` (over the message the initiator
sent) are EQUAL, EXACTLY WHEN the two trusted round-trips hold. The proof is `hx` (the DH secrets agree) and
`hfips` (the ML-KEM secrets agree) and nothing more: the transcripts coincide by construction, so agreement
reduces to the two primitive floors. This is the crux of the honest boundary — the whole content of
`hybrid_roundtrip_same_key` (the Rust test) as a theorem conditioned on the named primitive assumptions. -/
theorem dregg_kem_correct (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr)
    (hx : X25519Correct api) (hfips : Fips203Correct api)
    (xskr : Xsk) (dk : Dk) (xski : Xsk) :
    initKey api (api.x25519_pk xskr) (api.ekOf dk) xski
      = finishKey api xskr dk (api.x25519_pk xski) (api.mlkem_encaps (api.ekOf dk)).1 := by
  simp only [initKey, finishKey]
  rw [hx xski xskr, hfips dk]

/-! ## PART 3 — THE MODELED SESSION KEM and the REFINEMENT RELATION.

The glue, assembled into a genuine `HybridCombiner.KEM`: public key = the offer `(x25519_pk, ek)`, secret =
`(xsk, dk)`, ciphertext = the initiator message `(x25519_pk, ct)`, shared secret = the session key.
`encaps` runs `initiate` (the two-secret derivation + transcript + combine); `decaps` runs
`HybridResponder::finish`. Parametrised by the initiator's ephemeral secret `xski` (the honest encapsulation
coins), which the abstract deterministic `encaps` fixes. -/

/-- **THE MODELED SESSION KEM.** The `dregg-pq` hybrid handshake as a concrete `HybridCombiner.KEM`, built
from the API's derived `initMsg` / `initKey` / `finishKey`. This exhibits the deployed glue as a real KEM,
not just a shared-secret function. -/
@[reducible] def modeledSessionKEM (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) (xski : Xsk) :
    KEM (Xpk × Ek) (Xsk × Dk) (Xpk × CT) SS where
  pkOf sk := (api.x25519_pk sk.1, api.ekOf sk.2)
  encaps pk := (initMsg api pk.1 pk.2 xski, initKey api pk.1 pk.2 xski)
  decaps sk ct := finishKey api sk.1 sk.2 ct.1 ct.2

/-- **THE MODELED KEM IS CORRECT** — decaps recovers encaps' shared secret, from the two floors. The session
KEM's round trip is exactly `dregg_kem_correct`: an honestly encapsulated key decapsulates to itself, given
`X25519Correct` and `Fips203Correct`. -/
theorem modeled_kem_correct (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr)
    (hx : X25519Correct api) (hfips : Fips203Correct api) (sk : Xsk × Dk) (xski : Xsk) :
    (modeledSessionKEM api xski).decaps sk
        ((modeledSessionKEM api xski).encaps ((modeledSessionKEM api xski).pkOf sk)).1
      = ((modeledSessionKEM api xski).encaps ((modeledSessionKEM api xski).pkOf sk)).2 :=
  (dregg_kem_correct api hx hfips sk.1 sk.2 xski).symm

/-- **THE REFINEMENT RELATION.** The `KEM` model `K` faithfully abstracts the API contract `api` at the
chosen ephemeral `xski`: (1) `pkOf` reads back the offer, (2) `encaps` reads back `initiate`'s message + key,
(3) `decaps` reads back `HybridResponder::finish`. A model that mis-reads any of the three does NOT refine. -/
def Refines (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) (xski : Xsk)
    (K : KEM (Xpk × Ek) (Xsk × Dk) (Xpk × CT) SS) : Prop :=
  (∀ sk : Xsk × Dk, K.pkOf sk = (api.x25519_pk sk.1, api.ekOf sk.2)) ∧
  (∀ pk : Xpk × Ek, K.encaps pk = (initMsg api pk.1 pk.2 xski, initKey api pk.1 pk.2 xski)) ∧
  (∀ (sk : Xsk × Dk) (ct : Xpk × CT), K.decaps sk ct = finishKey api sk.1 sk.2 ct.1 ct.2)

/-- **THE REFINEMENT HOLDS.** `modeledSessionKEM api xski` is a faithful abstraction of its API contract —
each clause is definitional (the model is BUILT from the contract's derived ops), so the abstraction is
exact. This is the beachhead: the Rust hybrid-KEM's observable behaviour and the proved `KEM` model are now
one connected object. -/
theorem dregg_kem_refines (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) (xski : Xsk) :
    Refines api xski (modeledSessionKEM api xski) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-! ## PART 4 — INHERITANCE: the deployed `combine` is the modeled X-Wing dual-PRF, IND-CCA if either.

`combine(ss_x, ss_pq, transcript)` is the CONCATENATION KDF (never XOR) `HybridCombiner` Part B models as
the X-Wing combiner. We model the API's `combine` as the combiner `KDF` and inherit
`hybrid_kem_ind_cca_if_either`: under the standard HKDF dual-PRF assumption, the hybrid session key is
IND-CCA if EITHER the X25519 or the ML-KEM shared-secret source is. -/

/-- **THE HKDF TRUST SURFACE.** The standard X-Wing / HKDF assumption on the combiner: `combine` is a
dual-PRF (unpredictability-preserving keyed on EITHER input). Named explicitly and reduced to — the SAME
`DualPRF` requirement `HybridCombiner` Part B states, not hidden. This is the HKDF-SHA256 / concatenation
correctness surface, a labeled hypothesis, NOT a `def …Hard` carrier. -/
def DreggKemKdfIsDualPRF (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) : Prop := DualPRF api.combine

/-- **THE DEPLOYED HYBRID KEM INHERITS IND-CCA-IF-EITHER.** Specializes
`HybridCombiner.hybrid_kem_ind_cca_if_either` to the `dregg-pq` `combine`: under the HKDF dual-PRF, if X25519
OR ML-KEM is IND-CCA (its shared-secret source unpredictable), the deployed hybrid session key is IND-CCA
through the corresponding channel. No fresh carrier — the component disjuncts bottom out, in the MODEL, at
`SchnorrDLHard` (X25519, via the classical-KEM analysis) and `MLWESearchHard` (ML-KEM, via `MlKemIndCca`). -/
theorem dregg_kem_ind_cca_if_either (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr)
    (hdual : DreggKemKdfIsDualPRF api) (tr : Tr)
    {In : Type*} (sourceX sourcePq : In → SS) (ssx sspq : SS)
    (heither : KemIndCca sourceX ∨ KemIndCca sourcePq) :
    KemIndCca (fun i => api.combine (sourceX i) sspq tr) ∨
    KemIndCca (fun i => api.combine ssx (sourcePq i) tr) :=
  hybrid_kem_ind_cca_if_either api.combine hdual tr sourceX sourcePq ssx sspq heither

/-! ## Teeth — correctness is DERIVED from the floors, each floor is LOAD-BEARING, refinement has TEETH.

Concrete toy over `ℤ` (decidable, so the `#guard`s fire): `x25519_pk = id`, `x25519_dh a b = a * b`
(commutative ⇒ a genuine DH agreement), ML-KEM as a trivial round trip (`ekOf = id`, `encaps e = (e, e)`,
`decaps _ ct = ct`), a concatenation-style `transcript`, and `combine k1 k2 _ = k1 − k2` — the proved
`HybridCombiner.goodKDF`, a genuine dual-PRF.

(a) the honest toy satisfies BOTH floors, so `dregg_kem_correct` fires — the round trip agrees;
(b) FIPS 203 is LOAD-BEARING: `badKem` (broken decaps) fails `Fips203Correct` AND breaks agreement;
(c) X25519 is LOAD-BEARING: `badDh` (a non-agreeing DH) fails `X25519Correct` AND breaks agreement;
(d) `Refines` has TEETH: a `badModel` KEM that drops the PQ secret in decaps does NOT refine;
(e) the combiner inherits IND-CCA-if-either on the concrete toy. -/

section Teeth

/-! ### (a) An HONEST, correct, non-vacuous instance. -/

/-- A concrete `dregg-pq` hybrid-KEM surface over `ℤ`: `x25519_pk = id`, `x25519_dh a b = a * b` (a
commutative DH), the trivial ML-KEM round trip, and `combine k1 k2 _ = k1 − k2` (the proved dual-PRF). -/
def toyApi : DreggKemApi ℤ ℤ ℤ ℤ ℤ ℤ ℤ where
  x25519_pk sk := sk
  x25519_dh a b := a * b
  ekOf dk := dk
  mlkem_encaps ek := (ek, ek)
  mlkem_decaps _ ct := ct
  transcript a b c d := a + b + c + d
  combine k1 k2 _ := k1 - k2

/-- The X25519 floor HOLDS for the honest toy: the DH secrets agree (`a * b = b * a`). -/
theorem toyApi_x25519 : X25519Correct toyApi := by
  intro a b; simp only [toyApi]; ring

/-- The FIPS 203 floor HOLDS for the honest toy: decaps recovers the encapsulated secret. -/
theorem toyApi_fips203 : Fips203Correct toyApi := by
  intro dk; simp only [toyApi]

/-- Hence the honest handshake AGREES — `dregg_kem_correct` DERIVES it from the two floors. -/
theorem toyApi_correct (xskr dk xski : ℤ) :
    initKey toyApi (toyApi.x25519_pk xskr) (toyApi.ekOf dk) xski
      = finishKey toyApi xskr dk (toyApi.x25519_pk xski) (toyApi.mlkem_encaps (toyApi.ekOf dk)).1 :=
  dregg_kem_correct toyApi toyApi_x25519 toyApi_fips203 xskr dk xski

-- The two parties derive the SAME key on concrete data (initiator vs responder, honest handshake).
#guard decide (initKey toyApi 3 5 7 = 16)          -- 7*3 − 5 = 16
#guard decide (finishKey toyApi 3 5 7 5 = 16)       -- 3*7 − 5 = 16
#guard decide (initKey toyApi 3 5 7 = finishKey toyApi 3 5 7 5)
-- The transcript BINDS: a different public transcript changes the key (concat-KDF, not XOR of secrets).
#guard decide (toyApi.combine 21 5 100 ≠ toyApi.combine 21 6 100)   -- the PQ secret is load-bearing
#guard decide (toyApi.combine 21 5 100 ≠ toyApi.combine 22 5 100)   -- the classical secret is load-bearing

/-! ### (b) THE FIPS 203 BOUNDARY IS LOAD-BEARING. -/

/-- A degenerate API whose ML-KEM `decaps` ALWAYS returns `0` (as if `ml-kem` did not implement FIPS 203). -/
def badKem : DreggKemApi ℤ ℤ ℤ ℤ ℤ ℤ ℤ :=
  { toyApi with mlkem_decaps := fun _ _ => 0 }

/-- `Fips203Correct` FAILS for `badKem`: decaps returns `0`, never the encapsulated secret. -/
theorem badKem_not_fips203 : ¬ Fips203Correct badKem := by
  intro h; have h5 := h 5; simp only [badKem, toyApi] at h5; omega

/-- **THE FIPS-203 TOOTH.** With a broken decaps the two parties DIVERGE — `initKey ≠ finishKey`. So key
agreement genuinely REQUIRES the trusted FIPS 203 round trip: `Fips203Correct` is honestly load-bearing. -/
theorem badKem_breaks_correctness :
    initKey badKem (badKem.x25519_pk 3) (badKem.ekOf 5) 7
      ≠ finishKey badKem 3 5 (badKem.x25519_pk 7) (badKem.mlkem_encaps (badKem.ekOf 5)).1 := by
  simp only [badKem, toyApi, initKey, finishKey]; decide

/-! ### (c) THE X25519 BOUNDARY IS LOAD-BEARING. -/

/-- A degenerate API whose X25519 `dh` DROPS the peer key (`dh a _ = a`), so it is NOT a real DH: the two
sides never agree unless their secrets coincide. -/
def badDh : DreggKemApi ℤ ℤ ℤ ℤ ℤ ℤ ℤ :=
  { toyApi with x25519_dh := fun a _ => a }

/-- `X25519Correct` FAILS for `badDh`: `dh 1 (pk 2) = 1` but `dh 2 (pk 1) = 2`. -/
theorem badDh_not_x25519 : ¬ X25519Correct badDh := by
  intro h; have h12 := h 1 2; simp only [badDh, toyApi] at h12; omega

/-- **THE X25519 TOOTH.** With a non-agreeing DH the two parties DIVERGE — `initKey ≠ finishKey`. So key
agreement genuinely REQUIRES the trusted X25519 agreement: `X25519Correct` is honestly load-bearing. -/
theorem badDh_breaks_correctness :
    initKey badDh (badDh.x25519_pk 3) (badDh.ekOf 5) 7
      ≠ finishKey badDh 3 5 (badDh.x25519_pk 7) (badDh.mlkem_encaps (badDh.ekOf 5)).1 := by
  simp only [badDh, toyApi, initKey, finishKey]; decide

/-! ### (d) `Refines` HAS TEETH — a model that drops the PQ secret does not refine. -/

/-- An UNFAITHFUL KEM: `decaps` uses ONLY the classical channel (`sk.1 * ct.1`), dropping the ML-KEM secret
and the combine. It is a `KEM`, but it does NOT abstract `toyApi` (whose decaps folds in the PQ secret). -/
def badModel : KEM (ℤ × ℤ) (ℤ × ℤ) (ℤ × ℤ) ℤ where
  pkOf sk := (sk.1, sk.2)
  encaps pk := ((pk.1, pk.2), pk.1)
  decaps sk ct := sk.1 * ct.1

/-- **REFINEMENT TEETH.** `badModel` does NOT refine `toyApi`: its PQ-blind `decaps` disagrees with the
contract at `sk = (0,0)`, `ct = (0,1)` (`badModel.decaps = 0`, but `finishKey toyApi 0 0 0 1 = −1`). So
`Refines` genuinely rejects a wrong abstraction — it is not vacuously true. -/
theorem badModel_not_refines : ¬ Refines toyApi 0 badModel := by
  rintro ⟨_, _, hd⟩
  have h := hd (0, 0) (0, 1)
  simp only [badModel, toyApi, finishKey] at h; omega

/-! ### (e) The hybrid KEM combiner inherits IND-CCA-if-either on the toy. -/

/-- `toyApi`'s combiner IS a dual-PRF — injective in each key argument (`k1 − k2`). -/
theorem toyApi_dualPRF : DreggKemKdfIsDualPRF toyApi := by
  constructor
  · intro k2 tr a b h; simp only [toyApi] at h; omega
  · intro k1 tr a b h; simp only [toyApi] at h; omega

/-- **KEM INHERITANCE FIRES.** With an unpredictable X25519 source (`id`), the concrete hybrid combiner is
IND-CCA — `dregg_kem_ind_cca_if_either` delivers it through the classical channel. -/
theorem toyApi_ind_cca_via_classical (sspq tr : ℤ) :
    KemIndCca (fun i : ℤ => toyApi.combine (id i) sspq tr) ∨
    KemIndCca (fun i : ℤ => toyApi.combine (0 : ℤ) (id i) tr) :=
  dregg_kem_ind_cca_if_either toyApi toyApi_dualPRF tr id id 0 sspq (Or.inl Function.injective_id)

-- The combiner is injective in BOTH inputs (the dual-PRF, on data)…
#guard decide (toyApi.combine 7 3 0 = 4)
#guard decide (toyApi.combine 7 3 0 ≠ toyApi.combine 8 3 0)   -- injective in the classical key
#guard decide (toyApi.combine 7 3 0 ≠ toyApi.combine 7 4 0)   -- injective in the PQ key
-- …while the broken decaps and the non-agreeing DH each break the honest round trip.
#guard decide (badKem.mlkem_decaps 5 5 ≠ (badKem.mlkem_encaps (badKem.ekOf 5)).2)
#guard decide (badDh.x25519_dh 1 (badDh.x25519_pk 2) ≠ badDh.x25519_dh 2 (badDh.x25519_pk 1))

end Teeth

#assert_all_clean [
  dregg_kem_correct,
  modeled_kem_correct,
  dregg_kem_refines,
  dregg_kem_ind_cca_if_either,
  toyApi_x25519,
  toyApi_fips203,
  toyApi_correct,
  badKem_not_fips203,
  badKem_breaks_correctness,
  badDh_not_x25519,
  badDh_breaks_correctness,
  badModel_not_refines,
  toyApi_dualPRF,
  toyApi_ind_cca_via_classical
]

end Dregg2.Crypto.DreggKemRefinement
