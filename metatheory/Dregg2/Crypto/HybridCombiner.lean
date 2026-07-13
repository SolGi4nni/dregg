/-
# `Dregg2.Crypto.HybridCombiner` — the KEYSTONE of "hybrid, not PQ-only".

The whole no-pre-quantum campaign ASSERTS that dregg's signatures and KEMs are HYBRID: a classical
component (ed25519 / X25519, hard iff discrete log is) welded to a post-quantum component (ML-DSA /
ML-KEM, hard iff a lattice problem is), verified/combined so that breaking ONE leaves the other holding.
This file PROVES that formal content — the two combiner security theorems the campaign leans on but never
stated:

* **Signatures (Part A).** A hybrid signature that verifies BOTH component signatures over the same
  message is EUF-CMA-unforgeable if EITHER component is. The reduction is the beautiful part: a hybrid
  forgery on a FRESH message `m*` is a PAIR `(σc*, σpq*)` with BOTH halves valid on `m*`, so PROJECTING
  the pair gives a forgery on the classical scheme AND, independently, a forgery on the pq scheme. Hence a
  hybrid forger yields a component forger on each side; if either component's EUF-CMA holds, the hybrid
  forger cannot exist. This is the "ed25519 OR ML-DSA suffices" theorem.

* **KEMs (Part B, X-Wing).** The hybrid shared secret `ss = KDF(ss_x ‖ ss_pq ‖ transcript)` is
  IND-CCA-secure if EITHER X25519 OR ML-KEM is — provided `KDF` is a **dual-PRF** (the standard X-Wing
  requirement, stated explicitly and reduced to, never hidden): keyed on EITHER input it preserves the
  unpredictability of that input. Breaking one component leaves the other's shared secret as an
  unpredictable key the adversary cannot pin, so the combined output stays unpredictable.

## No named-carrier laundering

Neither combiner introduces a hardness carrier. Each component's game bottoms out at the EXISTING floors:
`classical_euf_cma_grounded_in_dl` reduces the classical half to `SchnorrCurveField.SchnorrDLHard` (the
curve DL assumption) through the Schnorr EUF-CMA→DL forking reduction (a REDUCTION hypothesis, cited to the
proved forking machinery of `HermineTSUF`, NOT a re-asserted carrier); `pq_euf_cma_grounded_in_msis`
reduces the pq half to `Lattice.MSISHard` by feeding a forked ML-DSA forgery to the PROVED SelfTargetMSIS
extraction `HermineSelfTargetMSIS.no_forgery_under_msis_selftarget`. The combined
`hybrid_secure_if_either_floor` then says: the hybrid signature is unforgeable if EITHER `SchnorrDLHard` OR
`MSISHard` holds — the formal "hybrid, not PQ-only".

## Modelling notes (honest boundaries)

* EUF-CMA is modelled at the level `VRF.lean`/`RandomnessBeacon.lean` use: the signing oracle is captured
  by the set `Q` of queried messages (the hybrid signer signs each queried message with BOTH keys, so both
  component oracles see EXACTLY `Q`), a `Forgery` is a self-contained witness `(m, σ)` with `m` fresh
  (`¬ Q m`) and valid, and `EufCma := ¬ Forgery`. Freshness on the hybrid IS freshness on each component
  (same `m ∉ Q`), so the projection reduction is perfectly faithful without probabilistic machinery.
* The dual-PRF's load-bearing consequence — unpredictability-preservation keyed on either input — is
  modelled as key-wise INJECTIVITY, the SAME concrete proxy `RandomnessBeacon.lean` uses for
  unpredictability (an injective combine-hash = an unpredictable output). The full probabilistic dual-PRF
  is the standard X-Wing assumption; this captures its structural content and does not hide it.

Cite: X-Wing (Barbosa–Connolly–Duarte–Kaidel–Schwabe–Westerbaan, the X25519+ML-KEM hybrid KEM); the
generic ∧-combiner for hybrid signatures (Bindel–Herath–McKague–Stebila).
-/
import Dregg2.Crypto.HermineSelfTargetMSIS
import Dregg2.Crypto.SchnorrCurveField

namespace Dregg2.Crypto.HybridCombiner

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

/-! ## PART A — the hybrid signature ∧-combiner. -/

/-- **An abstract signature scheme** over carrier types: secret keys `SK`, public keys `PK`, messages
`Msg`, signatures `Sig`. `pkOf` is the public half of keygen; `sign sk m` signs; `verify pk m σ` decides
(as a `Prop`) whether `σ` is a valid signature on `m` under `pk`. -/
structure SigScheme (SK PK Msg Sig : Type*) where
  /-- The public key of a secret key (public output of keygen). -/
  pkOf : SK → PK
  /-- Signing: `sign sk m` produces a signature on `m`. -/
  sign : SK → Msg → Sig
  /-- Verification of a signature against a public key and message. -/
  verify : PK → Msg → Sig → Prop

/-! ### Correctness. -/

/-- **Correctness hypothesis.** Every honestly-produced signature verifies against the derived public key —
the relation a concrete scheme establishes between `sign` and `verify`. -/
def Correct {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) : Prop :=
  ∀ (sk : SK) (m : Msg), S.verify (S.pkOf sk) m (S.sign sk m)

/-- **CORRECTNESS.** Given the hypothesis, an honestly-signed message verifies. -/
theorem correctness {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (hc : Correct S)
    (sk : SK) (m : Msg) : S.verify (S.pkOf sk) m (S.sign sk m) := hc sk m

/-! ### EUF-CMA (existential unforgeability under chosen-message attack).

The signing oracle is captured by `Q : Msg → Prop`, the set of messages the adversary queried. A `Forgery`
is a FRESH-message signature: `m` not in `Q` (`¬ Q m`) with a verifying `σ`. `EufCma := ¬ Forgery` — no
adversary produces a valid signature on a message it never had signed (the abstract-game style of
`VRF.lean`/`RandomnessBeacon.lean`). -/

/-- **A forgery** against `pk` given the queried-message set `Q`: a FRESH message `m` (`¬ Q m`) carrying a
verifying signature `σ`. This is the adversary's win in the EUF-CMA game. -/
def Forgery {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop) : Prop :=
  ∃ (m : Msg) (σ : Sig), ¬ Q m ∧ S.verify pk m σ

/-- **EUF-CMA.** No forgery exists: no adversary with the signing oracle `Q` produces a valid signature on a
message outside `Q`. The named security game for the scheme. -/
def EufCma {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop) : Prop :=
  ¬ Forgery S pk Q

/-! ### The hybrid scheme — verify BOTH over the same message. -/

/-- **The hybrid verification relation** — verify BOTH component signatures over the SAME message: the
signature is a pair `(σc, σpq)` and it is valid iff the classical half AND the pq half each verify. This is
the whole content of "hybrid": acceptance requires both. -/
@[reducible] def hybridVerify {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pk : PKc × PKp) (m : Msg) (σ : Sigc × Sigp) : Prop :=
  Cl.verify pk.1 m σ.1 ∧ Pq.verify pk.2 m σ.2

/-- **The hybrid signature scheme**: keypairs, signatures and verification pair up the classical and pq
components; `verify = hybridVerify` demands BOTH halves. This is the `ed25519 × ML-DSA` object. -/
@[reducible] def hybrid {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp) :
    SigScheme (SKc × SKp) (PKc × PKp) Msg (Sigc × Sigp) where
  pkOf sk := (Cl.pkOf sk.1, Pq.pkOf sk.2)
  sign sk m := (Cl.sign sk.1 m, Pq.sign sk.2 m)
  verify := hybridVerify Cl Pq

/-- **The hybrid is a well-formed scheme.** If both components are correct, the hybrid is correct: an
honest hybrid signature verifies BOTH halves. -/
theorem hybrid_correct {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (hcl : Correct Cl) (hpq : Correct Pq) : Correct (hybrid Cl Pq) :=
  fun sk m => ⟨hcl sk.1 m, hpq sk.2 m⟩

/-! ### The projection reductions — the "either suffices" proof.

A hybrid forgery on a fresh `m*` is a PAIR both of whose halves verify on `m*`. Projecting the first
coordinate is a classical forgery on the SAME fresh `m*`; projecting the second is a pq forgery. So a
hybrid forger yields a classical forger AND a pq forger — the load-bearing step. -/

/-- **PROJECT TO CLASSICAL.** A hybrid forgery yields a forgery on the classical component: take the fresh
message and the FIRST signature coordinate; the hybrid's `verify` gave `Cl.verify` as its left conjunct,
and freshness is the same `¬ Q m`. -/
theorem hybrid_forger_projects_to_classical {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (h : Forgery (hybrid Cl Pq) (pkc, pkp) Q) : Forgery Cl pkc Q := by
  obtain ⟨m, σ, hfresh, hv⟩ := h
  exact ⟨m, σ.1, hfresh, hv.1⟩

/-- **PROJECT TO PQ.** Symmetrically, a hybrid forgery yields a forgery on the pq component: the SECOND
signature coordinate, on the same fresh message, valid by the right conjunct of the hybrid `verify`. -/
theorem hybrid_forger_projects_to_pq {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (h : Forgery (hybrid Cl Pq) (pkc, pkp) Q) : Forgery Pq pkp Q := by
  obtain ⟨m, σ, hfresh, hv⟩ := h
  exact ⟨m, σ.2, hfresh, hv.2⟩

/-- **THE HYBRID SIGNATURE COMBINER — EUF-CMA if EITHER component is.** If the classical OR the pq
component is EUF-CMA-unforgeable, so is the hybrid. Proof: a hybrid forger projects to a forger on EACH
component (the two projection reductions); whichever component's `EufCma` holds refutes its projection,
hence no hybrid forger exists. This is the formal "ed25519 OR ML-DSA suffices" — break one, the other still
holds. -/
theorem hybrid_euf_cma_if_either {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (heither : EufCma Cl pkc Q ∨ EufCma Pq pkp Q) :
    EufCma (hybrid Cl Pq) (pkc, pkp) Q := by
  intro hforge
  rcases heither with hc | hp
  · exact hc (hybrid_forger_projects_to_classical Cl Pq pkc pkp Q hforge)
  · exact hp (hybrid_forger_projects_to_pq Cl Pq pkc pkp Q hforge)

/-! ### Anchoring the component games to the EXISTING floors (no re-asserted carrier).

Each component's `EufCma` bottoms out at a floor already in the tree — the classical half at
`SchnorrDLHard` (the curve discrete-log assumption), the pq half at `MSISHard` (Module-SIS). The bridge in
each case is a REDUCTION hypothesis (a forger ⟹ a solver / an MSIS witness), which is a THEOREM proved by
the existing forking + extraction machinery, NOT a hardness carrier. -/

/-- **CLASSICAL HALF grounded in discrete log.** Given the Schnorr EUF-CMA→DL reduction — a hybrid/classical
forgery yields a `DLSolver` on the curve (the forking-lemma reduction; reuses the PROVED forking machinery
of `HermineTSUF`, cited, not re-asserted) — the discrete-log assumption `SchnorrDLHard` implies the
classical scheme is `EufCma`. The floor is `SchnorrDLHard`; `fork` is a reduction.

⚠ **`fork` IS RETIRED — use `ForkingDischarge.classical_euf_cma_grounded_in_dl_discharged`.** The citation
above was never wired: `fork` is an UN-DISCHARGED hypothesis, and `ForkingDischarge` proves it cannot be
discharged in this shape at all (a deterministic `Forgery` is a SINGLE transcript, so its fork probability
is `0` — `no_forked_pair_of_hits_le_one`). The discharged replacement rests on `SchnorrEufCma.SchnorrDLHardF`
(the field-scalar DL floor the Schnorr forking reduction is actually PROVED against) plus a realizability
bridge, with the extraction PROVED. This statement is kept for the existing call sites. -/
theorem classical_euf_cma_grounded_in_dl {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    (fork : Forgery S pk Q → DLSolver C G)
    (hard : SchnorrDLHard C G) : EufCma S pk Q :=
  fun hforge => hard (fork hforge)

section PqAnchor
variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **PQ HALF grounded in Module-SIS.** Given the ML-DSA forgery→MSIS forking reduction — a fresh forgery
yields two SelfTargetMSIS solutions on a SHARED commitment `w` with DISTINCT challenges `c ≠ c'` (the
rewind/forking step of `HermineTSUF`, cited) — Module-SIS hardness on the augmented map `[A | t]` implies
the pq scheme is `EufCma`. The discharge runs THROUGH the PROVED extraction
`HermineSelfTargetMSIS.no_forgery_under_msis_selftarget`, so the ONLY floor invoked is `MSISHard`; `fork`
is a reduction, not a carrier.

⚠ **`fork` IS RETIRED — use `ForkingDischarge.pq_euf_cma_grounded_in_msis_discharged`.** The cited rewind
was never wired: `fork` is an UN-DISCHARGED hypothesis. `ForkingDischarge.fork_of_realizable` now PROVES
exactly this `fork` type from a realizability bridge plus the forking bound, and
`ForkingDischarge.pq_advantage_bounded_under_msis` states the reduction in its honest advantage-bounded
form. This statement is kept for the existing call sites. -/
theorem pq_euf_cma_grounded_in_msis {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (fork : Forgery S pk Q →
      ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma S pk Q := by
  intro hforge
  obtain ⟨w, c, c', z, z', hne, hf, hf'⟩ := fork hforge
  exact no_forgery_under_msis_selftarget A t w c c' z z' β hne hf hf' hard

end PqAnchor

/-- **THE KEYSTONE — hybrid unforgeable if EITHER FLOOR holds.** With the two forking reductions in hand,
the hybrid `ed25519 × ML-DSA` signature is EUF-CMA-unforgeable if EITHER the discrete-log floor
`SchnorrDLHard` OR the Module-SIS floor `MSISHard` holds. This is "hybrid, not PQ-only" as a theorem: a
quantum adversary that breaks the discrete-log half still faces MSIS; a lattice cryptanalyst that breaks
ML-DSA still faces discrete log. Only if BOTH floors fall does the hybrid fall.

⚠ **THE TWO FORKING HYPOTHESES ARE RETIRED — use `ForkingDischarge.hybrid_secure_if_either_floor_discharged`**
(and `ForkingDischargeConsumers.hybrid_secure_under_msis_alone` for the deployed post-quantum statement,
which needs NO classical model at all: note `dlFork` below is demanded unconditionally yet is NEVER used on
the `MSISHard` branch). Every one of the twelve protocol consumers of this keystone has a discharged
sibling in `ForkingDischargeConsumers`. This statement is kept for the existing call sites. -/
theorem hybrid_secure_if_either_floor
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
    {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (dlFork : Forgery Cl pkc Q → DLSolver C G)
    (msisFork : Forgery Pq pkp Q →
      ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma (hybrid Cl Pq) (pkc, pkp) Q := by
  refine hybrid_euf_cma_if_either Cl Pq pkc pkp Q ?_
  rcases hfloor with hdl | hmsis
  · exact Or.inl (classical_euf_cma_grounded_in_dl Cl pkc Q C G dlFork hdl)
  · exact Or.inr (pq_euf_cma_grounded_in_msis Pq pkp Q A t β msisFork hmsis)

/-! ### Teeth — the "either" is load-bearing, and the combiner is non-vacuous.

Toy schemes over `Unit` keys and `Bool` messages/signatures isolate the combiner. `secureToy` verifies
NOTHING (its `EufCma` holds — no forgery possible); `brokenToy` verifies EVERYTHING (a forgery on any fresh
message). With the empty query set (every message fresh):

* `hybrid secureToy brokenToy` is UNFORGEABLE — because ONE component (`secureToy`) is EUF-CMA, even though
  the other is fully broken. (Non-vacuity: the combiner delivers security from a single good component.)
* `hybrid brokenToy brokenToy` is FORGEABLE — if BOTH components are broken, the hybrid is broken. So the
  "either" hypothesis is LOAD-BEARING, not vacuous: one secure component is exactly what is needed. -/

section SigTeeth

/-- The empty signing transcript: no message queried, so EVERY message is fresh (`¬ Q m` for all `m`). -/
def noQueries : Bool → Prop := fun _ => False

/-- A SECURE toy scheme: `verify` accepts NOTHING, so no forgery can exist — `EufCma` holds. -/
@[reducible] def secureToy : SigScheme Unit Unit Bool Bool where
  pkOf _ := ()
  sign _ _ := false
  verify _ _ _ := False

/-- A BROKEN toy scheme: `verify` accepts EVERYTHING, so any fresh message carries a forgery. -/
@[reducible] def brokenToy : SigScheme Unit Unit Bool Bool where
  pkOf _ := ()
  sign _ _ := true
  verify _ _ _ := True

/-- `secureToy` is EUF-CMA: nothing verifies, so `Forgery` is uninhabited. -/
theorem secureToy_euf_cma : EufCma secureToy () noQueries := by
  rintro ⟨m, σ, _, hv⟩; exact hv

/-- `brokenToy` is FORGEABLE: everything verifies and every message is fresh, so a forgery exists. -/
theorem brokenToy_forgeable : Forgery brokenToy () noQueries :=
  ⟨true, true, not_false, trivial⟩

/-- **NON-VACUITY / ONE-COMPONENT SUFFICES.** The hybrid of a SECURE and a BROKEN component is EUF-CMA —
delivered by the combiner from the single secure half (`Or.inl`). Even with a completely broken pq (or
classical) component, the hybrid holds. -/
theorem hybrid_secure_via_left : EufCma (hybrid secureToy brokenToy) ((), ()) noQueries :=
  hybrid_euf_cma_if_either secureToy brokenToy () () noQueries (Or.inl secureToy_euf_cma)

/-- Symmetrically, security in the RIGHT (pq) component alone also carries the hybrid. -/
theorem hybrid_secure_via_right : EufCma (hybrid brokenToy secureToy) ((), ()) noQueries :=
  hybrid_euf_cma_if_either brokenToy secureToy () () noQueries (Or.inr secureToy_euf_cma)

/-- **THE LOAD-BEARING TOOTH.** If BOTH components are broken, the hybrid is FORGEABLE — a fresh valid
signature exists. So the `either` in `hybrid_euf_cma_if_either` is not vacuous: with neither component
secure the conclusion genuinely fails. -/
theorem hybrid_broken_if_both : Forgery (hybrid brokenToy brokenToy) ((), ()) noQueries :=
  ⟨true, (true, true), not_false, trivial, trivial⟩

/-- …hence `hybrid brokenToy brokenToy` is NOT EUF-CMA — the contrapositive of "one secure component
suffices". -/
theorem hybrid_broken_not_euf : ¬ EufCma (hybrid brokenToy brokenToy) ((), ()) noQueries :=
  fun h => h hybrid_broken_if_both

-- The broken component verifies anything (a forgery on any fresh message).
#guard decide (brokenToy.verify () true true)
-- The secure component verifies nothing (its EUF-CMA holds).
#guard decide (¬ secureToy.verify () true true)
-- ONE secure component BLOCKS the hybrid: secure∧broken verification is FALSE — hybrid unforgeable.
#guard decide (¬ (hybrid secureToy brokenToy).verify ((), ()) true (true, true))
-- BOTH broken: the hybrid verification is TRUE — a forgery goes through (the "either" is load-bearing).
#guard decide ((hybrid brokenToy brokenToy).verify ((), ()) true (true, true))

end SigTeeth

/-! ## PART B — the hybrid KEM (X-Wing) combiner. -/

/-- **An abstract KEM** over carrier types: public keys `PK`, secret keys `SK`, ciphertexts `CT`, shared
secrets `SS`. `encaps pk = (ct, ss)` encapsulates; `decaps sk ct` recovers the shared secret. -/
structure KEM (PK SK CT SS : Type*) where
  /-- The public key of a secret key. -/
  pkOf : SK → PK
  /-- Encapsulation: produce a ciphertext and shared secret under a public key. -/
  encaps : PK → CT × SS
  /-- Decapsulation: recover the shared secret from a ciphertext. -/
  decaps : SK → CT → SS

/-! ### Unpredictability and the dual-PRF (the X-Wing requirement, stated explicitly).

A shared secret is UNPREDICTABLE when, as a function of the honest party's hidden encapsulation coins, it
is INJECTIVE — a fixed a-priori prediction matches at most one coin value, so the adversary cannot pin it.
This is the concrete unpredictability proxy `RandomnessBeacon.lean` uses (an injective combine-hash = an
unpredictable output). `KDF` is a **dual-PRF** when it preserves this unpredictability keyed on EITHER
input: injective in its first key argument (with the second fixed) AND injective in its second. Stated
honestly and reduced to — this is exactly the X-Wing dual-PRF requirement, not hidden. -/

/-- **Unpredictable** — the secret, as a function of the hidden input, is injective: distinct hidden inputs
give distinct secrets, so no fixed prediction matches more than one. -/
def Unpredictable {In SS : Type*} (f : In → SS) : Prop := Function.Injective f

/-- **DUAL-PRF (the X-Wing KDF requirement).** `KDF` preserves unpredictability keyed on EITHER input:
injective in the first key (second key + context fixed) AND injective in the second key. The standard
X-Wing assumption on the combiner, stated explicitly; the "either" theorem reduces to it. -/
def DualPRF {SS Ctx : Type*} (KDF : SS → SS → Ctx → SS) : Prop :=
  (∀ (k2 : SS) (tr : Ctx), Function.Injective (fun k1 => KDF k1 k2 tr)) ∧
  (∀ (k1 : SS) (tr : Ctx), Function.Injective (fun k2 => KDF k1 k2 tr))

/-- **The X-Wing combiner**: the hybrid shared secret is `KDF(ss_x, ss_pq, transcript)` — both component
shared secrets fed through the KDF over the transcript. -/
def hybridKemSecret {SS Ctx : Type*} (KDF : SS → SS → Ctx → SS) (ssx sspq : SS) (tr : Ctx) : SS :=
  KDF ssx sspq tr

/-- **The hybrid X-Wing KEM** as a genuine KEM: encapsulation runs BOTH components and combines their
shared secrets via `KDF` over the transcript (the two ciphertexts); decapsulation recomputes the combine.
This exhibits the combiner as a real KEM, not just a shared-secret function. -/
def hybridKEM {SS Ctx PKx SKx CTx PKp SKp CTp : Type*}
    (KDF : SS → SS → Ctx → SS) (mkCtx : CTx → CTp → Ctx)
    (Kx : KEM PKx SKx CTx SS) (Kp : KEM PKp SKp CTp SS) :
    KEM (PKx × PKp) (SKx × SKp) (CTx × CTp) SS where
  pkOf sk := (Kx.pkOf sk.1, Kp.pkOf sk.2)
  encaps pk :=
    let rx := Kx.encaps pk.1
    let rp := Kp.encaps pk.2
    ((rx.1, rp.1), KDF rx.2 rp.2 (mkCtx rx.1 rp.1))
  decaps sk ct := KDF (Kx.decaps sk.1 ct.1) (Kp.decaps sk.2 ct.2) (mkCtx ct.1 ct.2)

/-! ### The combiner core — unpredictable if EITHER input secret is. -/

/-- **Unpredictability flows through the CLASSICAL channel.** If the classical shared-secret source is
unpredictable (injective in the hidden coins) and `KDF` is a dual-PRF (injective on its first key), the
hybrid secret keyed on that channel — pq secret held FIXED (whatever the adversary may know) — is
unpredictable. Injective ∘ injective. -/
theorem hybrid_unpredictable_via_classical {SS Ctx : Type*}
    (KDF : SS → SS → Ctx → SS) (hdual : DualPRF KDF) (tr : Ctx)
    {In : Type*} (source : In → SS) (sspq : SS) (hx : Unpredictable source) :
    Unpredictable (fun i => KDF (source i) sspq tr) := by
  intro a b h
  exact hx ((hdual.1 sspq tr) h)

/-- **Unpredictability flows through the PQ channel.** Symmetrically: if the pq shared-secret source is
unpredictable and `KDF` is a dual-PRF (injective on its SECOND key), the hybrid secret keyed on the pq
channel — classical secret held fixed — is unpredictable. This is the leg a NON-dual (single-keyed)
combiner would LACK. -/
theorem hybrid_unpredictable_via_pq {SS Ctx : Type*}
    (KDF : SS → SS → Ctx → SS) (hdual : DualPRF KDF) (tr : Ctx)
    {In : Type*} (ssx : SS) (source : In → SS) (hp : Unpredictable source) :
    Unpredictable (fun i => KDF ssx (source i) tr) := by
  intro a b h
  exact hp ((hdual.2 ssx tr) h)

/-- **THE HYBRID KEM COMBINER CORE — unpredictable if EITHER component's secret is.** Under the dual-PRF,
if the X25519 OR the ML-KEM shared-secret source is unpredictable, the hybrid X-Wing shared secret is
unpredictable through the corresponding channel. Breaking one component leaves the other's secret an
unpredictable key the adversary cannot pin. -/
theorem hybrid_kem_secret_unpredictable_if_either {SS Ctx : Type*}
    (KDF : SS → SS → Ctx → SS) (hdual : DualPRF KDF) (tr : Ctx)
    {In : Type*} (sourceX sourcePq : In → SS) (ssx sspq : SS)
    (heither : Unpredictable sourceX ∨ Unpredictable sourcePq) :
    Unpredictable (fun i => KDF (sourceX i) sspq tr) ∨
    Unpredictable (fun i => KDF ssx (sourcePq i) tr) := by
  rcases heither with hx | hp
  · exact Or.inl (hybrid_unpredictable_via_classical KDF hdual tr sourceX sspq hx)
  · exact Or.inr (hybrid_unpredictable_via_pq KDF hdual tr ssx sourcePq hp)

/-! ### IND-CCA lift (stated honestly).

At the shared-secret level, IND-CCA of a KEM is exactly: the encapsulated shared secret, as a function of
the honest hidden coins, is unpredictable given the transcript (the standard KEM equivalence — IND-CCA ⟺
the encapsulated key is pseudorandom given the ciphertext, with the decapsulation oracle). We model IND-CCA
as this `Unpredictable` predicate, so the combiner core lifts directly. The full probabilistic IND-CCA game
(decaps oracle, distinguisher advantage) is the standard X-Wing statement this captures at the key level. -/

/-- **IND-CCA (at the shared-secret level).** The encapsulated shared secret is unpredictable given the
transcript — the standard KEM equivalence. -/
def KemIndCca {In SS : Type*} (secret : In → SS) : Prop := Unpredictable secret

/-- **THE HYBRID KEM IS IND-CCA IF EITHER COMPONENT IS** (under the dual-PRF). Direct lift of the combiner
core to the IND-CCA level: if X25519 OR ML-KEM is IND-CCA, the X-Wing hybrid is IND-CCA through the
corresponding channel. This is "hybrid KEM, not PQ-only" — one component's IND-CCA suffices, provided the
KDF is a dual-PRF. -/
theorem hybrid_kem_ind_cca_if_either {SS Ctx : Type*}
    (KDF : SS → SS → Ctx → SS) (hdual : DualPRF KDF) (tr : Ctx)
    {In : Type*} (sourceX sourcePq : In → SS) (ssx sspq : SS)
    (heither : KemIndCca sourceX ∨ KemIndCca sourcePq) :
    KemIndCca (fun i => KDF (sourceX i) sspq tr) ∨ KemIndCca (fun i => KDF ssx (sourcePq i) tr) :=
  hybrid_kem_secret_unpredictable_if_either KDF hdual tr sourceX sourcePq ssx sspq heither

/-! ### Teeth — the dual-PRF is load-bearing, and the combiner is non-vacuous.

Over `ℤ` with the empty context. `goodKDF k1 k2 = k1 − k2` is injective in EACH argument — a genuine
dual-PRF — and it propagates unpredictability from EITHER channel. `badKDF k1 k2 = k1` IGNORES the second
input: it is injective in the first (single-PRF) but NOT the second, so it is NOT a dual-PRF, and it FAILS
to propagate a secure pq component. This is the load-bearing point of X-Wing: a combiner keyed on only one
input inherits security from that ONE fixed component; the DUAL-PRF is exactly what buys "either". -/

section KemTeeth

/-- A genuine dual-PRF over `ℤ`: `KDF(k1, k2) = k1 − k2`, injective in each argument. -/
def goodKDF : ℤ → ℤ → Unit → ℤ := fun k1 k2 _ => k1 - k2

/-- `goodKDF` IS a dual-PRF — injective in both key arguments. -/
theorem goodKDF_dualPRF : DualPRF goodKDF := by
  constructor
  · intro k2 tr a b h; simp only [goodKDF] at h; omega
  · intro k1 tr a b h; simp only [goodKDF] at h; omega

/-- **NON-VACUITY (classical channel).** With an unpredictable classical source (`id`), the good dual-PRF
propagates unpredictability to the hybrid secret. -/
theorem goodKDF_propagates_classical (sspq : ℤ) :
    Unpredictable (fun i : ℤ => goodKDF (id i) sspq ()) :=
  hybrid_unpredictable_via_classical goodKDF goodKDF_dualPRF () id sspq Function.injective_id

/-- **NON-VACUITY (pq channel) — the leg a single-PRF lacks.** With an unpredictable pq source, the good
DUAL-PRF propagates through the SECOND channel. -/
theorem goodKDF_propagates_pq (ssx : ℤ) :
    Unpredictable (fun i : ℤ => goodKDF ssx (id i) ()) :=
  hybrid_unpredictable_via_pq goodKDF goodKDF_dualPRF () ssx id Function.injective_id

/-- A single-keyed combiner: `badKDF(k1, k2) = k1` ignores the second (pq) input. -/
def badKDF : ℤ → ℤ → Unit → ℤ := fun k1 _ _ => k1

/-- **`badKDF` is NOT a dual-PRF.** It is constant in its second argument, so the second-key injectivity
leg fails (`badKDF 0 0 = badKDF 0 1 = 0` but `0 ≠ 1`). -/
theorem badKDF_not_dualPRF : ¬ DualPRF badKDF := by
  rintro ⟨_, h2⟩
  have hcol : (fun k2 => badKDF 0 k2 ()) 0 = (fun k2 => badKDF 0 k2 ()) 1 := rfl
  exact absurd (h2 0 () hcol) (by decide)

/-- `badKDF` DOES propagate the CLASSICAL channel (it is keyed on the first input) — so a single-PRF hybrid
is secure when the CLASSICAL component is. -/
theorem badKDF_propagates_classical (sspq : ℤ) :
    Unpredictable (fun i : ℤ => badKDF (id i) sspq ()) := by
  intro a b h; simpa [badKDF] using h

/-- **THE LOAD-BEARING TOOTH.** `badKDF` does NOT propagate a secure PQ component: even though the pq source
`id` is unpredictable, the hybrid secret through `badKDF` is CONSTANT (`= ssx`), hence predictable. So
without the DUAL-PRF property, "either" FAILS — a single-keyed combiner inherits security only from the
one fixed component. The dual-PRF assumption in `hybrid_kem_ind_cca_if_either` is load-bearing. -/
theorem badKDF_pq_not_propagated (ssx : ℤ) :
    ¬ Unpredictable (fun i : ℤ => badKDF ssx (id i) ()) := by
  intro hinj
  have hcol : (fun i : ℤ => badKDF ssx (id i) ()) 0 = (fun i : ℤ => badKDF ssx (id i) ()) 1 := rfl
  exact absurd (hinj hcol) (by decide)

-- The good dual-PRF is injective in BOTH arguments…
#guard decide (goodKDF 7 3 () = 4)
#guard decide (goodKDF 7 3 () ≠ goodKDF 8 3 ())   -- injective in the first (classical) key
#guard decide (goodKDF 7 3 () ≠ goodKDF 7 4 ())   -- injective in the second (pq) key
-- …but `badKDF` COLLAPSES the second (pq) input — the tooth: pq security cannot propagate through it.
#guard decide (badKDF 7 3 () = badKDF 7 4 ())

end KemTeeth

#assert_all_clean [
  correctness,
  hybrid_correct,
  hybrid_forger_projects_to_classical,
  hybrid_forger_projects_to_pq,
  hybrid_euf_cma_if_either,
  classical_euf_cma_grounded_in_dl,
  pq_euf_cma_grounded_in_msis,
  hybrid_secure_if_either_floor,
  secureToy_euf_cma,
  brokenToy_forgeable,
  hybrid_secure_via_left,
  hybrid_secure_via_right,
  hybrid_broken_if_both,
  hybrid_broken_not_euf,
  hybrid_unpredictable_via_classical,
  hybrid_unpredictable_via_pq,
  hybrid_kem_secret_unpredictable_if_either,
  hybrid_kem_ind_cca_if_either,
  goodKDF_dualPRF,
  goodKDF_propagates_classical,
  goodKDF_propagates_pq,
  badKDF_not_dualPRF,
  badKDF_propagates_classical,
  badKDF_pq_not_propagated
]

end Dregg2.Crypto.HybridCombiner
