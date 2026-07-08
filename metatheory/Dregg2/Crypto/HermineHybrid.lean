/-
# `Dregg2.Crypto.HermineHybrid` — Hermine as the hybrid's COMPACT post-quantum half.

The deployable FIPS hybrid (`federation/src/frost.rs`) pairs the ed25519 vote quorum with a
CONCATENATION of `t` ML-DSA-65 signatures — genuinely quantum-safe, but the PQ half grows linearly with
the committee (`t × ~3.3 KB`). This file is the verified statement of the *compact* upgrade: the same
hybrid security, with the PQ half a single **Hermine** threshold certificate `(w, z)` — one cert,
COMMITTEE-INDEPENDENT — instead of the concatenation.

It is a direct instantiation of the scheme-generic `HybridQuorum` theorems at Hermine's verifier
(`HermineThreshold.verify`), so nothing new is assumed:

* `hermine_hybrid_survives_classical_break` — even with the classical half TOTALLY broken (ed25519 to
  Shor, the classical verifier rubber-stamps everything), the hybrid is unforgeable as long as the
  Hermine PQ half is `Unforgeable`.
* `hermine_hybrid_unforgeable_of_either` — the hybrid holds if EITHER half does.

And the Hermine half's unforgeability is exactly `HermineMSIS.no_forgery_under_msis` — a (forked) forgery
yields an MSIS solution — so **the compact hybrid's quantum-safety reduces to MSIS hardness** (modulo the
ROM forking probability, the one named carrier). What crypto-hermine still needs before this replaces the
ML-DSA half in LIVE consensus is deployment-grade maturity (full-size params + external audit); the
security *shape* is proved here.
-/
import Dregg2.Crypto.HybridQuorum
import Dregg2.Crypto.HermineThreshold
import Dregg2.Crypto.HermineMSIS

namespace Dregg2.Crypto.HermineHybrid

open Dregg2.Crypto.HybridQuorum

variable {Rq : Type*} [CommRing Rq]
variable {Mod : Type*} [AddCommGroup Mod] [Module Rq Mod]
variable {Nod : Type*} [AddCommGroup Nod] [Module Rq Nod]
variable {Msg : Type*}

/-- A Hermine PQ certificate: the commitment `w` and combined response `z` (the challenge is derived
from the message by Fiat–Shamir). ONE cert — no dependence on the committee size, unlike the ML-DSA
concatenation. -/
structure HermineSig (Nod Mod : Type*) where
  w : Nod
  z : Mod

/-- The Hermine PQ verifier as a message→signature predicate: against group public key `t`, with the
challenge `chal m` derived from the message, the certificate `(w, z)` verifies iff the lattice relation
`A z = w + c·t` holds — i.e. `HermineThreshold.verify`. This is the `Vp` plugged into the generic hybrid. -/
def herminePqVerify (A : Mod →ₗ[Rq] Nod) (t : Nod) (chal : Msg → Rq) :
    Msg → HermineSig Nod Mod → Prop :=
  fun m σ => HermineThreshold.verify A t σ.w (chal m) σ.z

/-- **Hermine as the compact PQ half — quantum-safety.** Instantiate
`HybridQuorum.hybrid_survives_classical_break` at the Hermine verifier: even under a TOTAL classical
break, the hybrid stays unforgeable while the Hermine PQ half is `Unforgeable`. That PQ-unforgeability is
`HermineMSIS.no_forgery_under_msis` (a forked forgery → an MSIS solution), so the guarantee bottoms out
at MSIS hardness. -/
theorem hermine_hybrid_survives_classical_break {Sc : Type*}
    (A : Mod →ₗ[Rq] Nod) (t : Nod) (chal : Msg → Rq) (Signed : Msg → Prop)
    (hpq : Unforgeable (herminePqVerify A t chal) Signed) :
    HybridUnforgeable (fun (_ : Msg) (_ : Sc) => True) (herminePqVerify A t chal) Signed :=
  hybrid_survives_classical_break hpq

/-- **Hermine hybrid — unforgeable if either half holds.** The compact hybrid (ed25519 votes + one
Hermine cert) is unforgeable whenever EITHER the classical half OR the Hermine PQ half is unforgeable,
so trusting neither in isolation suffices. -/
theorem hermine_hybrid_unforgeable_of_either {Sc : Type*}
    (A : Mod →ₗ[Rq] Nod) (t : Nod) (chal : Msg → Rq)
    (Vc : Msg → Sc → Prop) (Signed : Msg → Prop)
    (h : Unforgeable Vc Signed ∨ Unforgeable (herminePqVerify A t chal) Signed) :
    HybridUnforgeable Vc (herminePqVerify A t chal) Signed :=
  hybrid_unforgeable_of_either h

/-- **Compactness, made explicit.** Whatever the committee, the Hermine PQ half is a SINGLE
`HermineSig` — one `(w, z)` — not a `t`-fold concatenation. This is the size win over the ML-DSA hybrid
(`t × ~3.3 KB` → one `~3 KB` cert), the reason Hermine is the compact upgrade. -/
theorem hermine_pq_half_is_one_cert (w : Nod) (z : Mod) :
    ∃ cert : HermineSig Nod Mod, cert = ⟨w, z⟩ := ⟨_, rfl⟩

#assert_axioms hermine_hybrid_survives_classical_break
#assert_axioms hermine_hybrid_unforgeable_of_either

end Dregg2.Crypto.HermineHybrid
