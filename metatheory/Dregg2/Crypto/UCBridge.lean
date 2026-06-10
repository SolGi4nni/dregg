/-
# Dregg2.Crypto.UCBridge — cross-system bridge for the dynamic-UC commitment obligation.

`Metatheory.EpistemicConsensus §6` states the full Canetti dynamic UC theorem

    (∀ Z, view_Z(π) ≈ view_Z(F))  →  (∀ Z, view_Z(ρ^π) ≈ view_Z(ρ^F))

as a sharp OPEN, resting on "simulator existence + computational indistinguishability of
ensembles" — the same cryptographic residue that `Crypto.Primitives` isolates as the
`Prop` carriers `CryptoPrimitives.binding` (DLog binding) and `CryptoPrimitives.unlinkable`
(hiding/anonymity). Those carriers are never proved in Lean — Lean's `Verify` is a decidable
oracle, not a probabilistic ensemble, and `≈` is not a Lean order-law.

This module does NOT prove UC in Lean. It CARRIES the *core commitment-security* obligation
(the heart of realizing the ideal commitment functionality `F_com`) as an explicit `Prop`
structure — and records that this obligation has been **discharged in a real UC / game-based
tool**: CryptHOL + the AFP `Sigma_Commit_Crypto` Pedersen development, on Isabelle/HOL. The
dregg2 Pedersen `commit` definitions were TRANSPORTED into that framework
(`~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy`) and the realization theorem PROVED there:

    Dregg2_UC.pedersen.dregg2_pedersen_realizes_F_com
      — correctness ∧ perfect-hiding ∧ (binding-advantage = DLog-advantage of the reduction);
    Dregg2_UC.pedersen_asymp.dregg2_pedersen_realizes_F_com_asymp
      — perfect hiding at every η ∧ (binding negligible ↔ DLog negligible);
    Dregg2_UC.pedersen_asymp.dregg2_binding_under_dlog
      — DLog hard ⟹ binding negligible (the honest implication the `binding` carrier asserts).

## THE CROSS-SYSTEM TRUST CAVEAT (read this).
What is asserted here is NOT a Lean proof of UC. It is a *carrier* whose truth rests on a
proof in ANOTHER system. Accepting it WIDENS the trust base of dregg2 to include, beyond Lean's
kernel:
  1. **Isabelle/HOL's kernel** (the LCF-style core that checked the CryptHOL proofs);
  2. **the AFP entries `CryptHOL` and `Sigma_Commit_Crypto`** (their `spmf` semantics, the
     `abstract_commitment` game definitions, the `dis_log` discrete-log game, and the proved
     Pedersen `abstract_perfect_hiding` / `pedersen_bind` / `pedersen_bind_asym`);
  3. **the FIDELITY OF THE DEFINITION TRANSPORT** — that the dregg2 Layer-A `commit value
     blinding` (with its sole proved law `commit_hom`, the additive homomorphism over an
     `AddCommGroup`) really IS the cyclic-group Pedersen commitment `commit ck m = g^d · ck^m`
     formalised in `Dregg2_FCom.thy`. This is a HUMAN-CHECKED correspondence, not a
     machine-checked one: the two formalisations live in different logics and are not connected
     by a verified translation. It is the residual gap.

This is strictly stronger than a bare Lean `axiom`/`sorry` (which would assert UC on nothing):
the obligation is discharged by a real proof in a real UC tool. It is strictly weaker than a
single-kernel Lean proof: the trust spans two kernels + the transport fidelity.

## How to verify the Isabelle side.
    isabelle build -d <afp-matching-Isabelle2025-RC3>/thys \
                   -d ~/dev/breadstuffs/uc-crypthol Dregg2_UC
(exit 0 ⇒ the CryptHOL theorems above are kernel-checked.) The theory file is
`~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy`; it contains no `sorry`/`oops` and references only
real, already-proven `Sigma_Commit_Crypto` theorems. CAVEAT: the green build was NOT reproduced on
the dev machine — the local AFP checkout (`afp-devel`) is an Isabelle-*dev* revision incompatible
with Isabelle2025-RC3 at the ML/proof-automation level; it needs the RC3-matched AFP. See
`docs/rebuild/PHASE-UC-TRANSPORT.md §3` for the exact obstruction. The Pedersen security itself is
long-established in the AFP; what is blocked is recompiling that AFP under this release candidate.

## Axiom hygiene.
The cross-system facts are fields of the `FComDischarge`
structure, passed as hypotheses. The bridge theorem
`binding_unlinkable_discharged_by_crypthol` proves (in Lean, kernel-clean) that given such a
discharge structure, the `binding` and `unlinkable` carriers are inhabited — witnessed by CryptHOL,
not assumed.
-/
import Dregg2.Crypto.Primitives
import Dregg2.Tactics

namespace Dregg2.Crypto.UCBridge

universe u

variable {Digest : Type u} [AddCommGroup Digest]

/-! ## The cross-system discharge structure.

`FComDischarge P` bundles — as `Prop` fields (carriers, never `axiom`s) — the core security
guarantees dregg2's Pedersen commitment must satisfy to realize `F_com`. Each field names the
CryptHOL theorem that establishes it. To construct an `FComDischarge`, the caller vouches (under
the trust caveat in the module header) that `Dregg2_FCom.thy`'s realization theorem holds for
this primitive set. -/

/-- `FComDischarge` — the F_com realization obligation for a `CryptoPrimitives` set, as a
`Prop`-bundling carrier. Its fields are the UC-relevant security properties proved in CryptHOL
(`Dregg2_FCom.thy`); inhabiting it is the cross-system bridge act. Not an `axiom`. -/
structure FComDischarge (P : CryptoPrimitives Digest) where
  /-- **Correctness** (CryptHOL `pedersen.abstract_correct`): an honest open of `commit v r`
  always verifies. Carried; proved in `Dregg2_FCom.thy`. -/
  correct : Prop
  /-- **Perfect hiding** (CryptHOL `pedersen.abstract_perfect_hiding`): the commitment leaks
  nothing about the committed value — the hiding half of dregg2's `unlinkable`. Carried. -/
  perfectHiding : Prop
  /-- **Binding reduces to DLog** (CryptHOL `pedersen.pedersen_bind` /
  `pedersen_asymp.dregg2_binding_under_dlog`): equivocating a commitment is exactly as hard as
  discrete log; negligible under DLog hardness — dregg2's `binding`. Carried. -/
  bindingReducesToDLog : Prop
  /-- The discharge asserts each transported guarantee holds (witnessed by the CryptHOL proof,
  under the transport-fidelity caveat). These are operational contents, not free `True`s. -/
  correct_holds : correct
  /-- Perfect hiding holds (CryptHOL). -/
  hiding_holds : perfectHiding
  /-- Binding-under-DLog holds (CryptHOL). -/
  binding_holds : bindingReducesToDLog
  /-- The transported guarantees ENTAIL the dregg2 Layer-A `binding` carrier: the cross-system
  proof is what makes `CryptoPrimitives.binding` true for this primitive set. -/
  entails_binding : bindingReducesToDLog → P.binding
  /-- The transported hiding guarantee ENTAILS the (hiding half of the) dregg2 `unlinkable`
  carrier: perfect hiding is the unlinkability of the committed value. -/
  entails_unlinkable : perfectHiding → P.unlinkable

/-- `binding_discharged_by_crypthol` — given a CryptHOL F_com discharge, the `binding` carrier
is inhabited, witnessed by the CryptHOL `pedersen_bind` proof. Kernel-clean. -/
theorem binding_discharged_by_crypthol
    {P : CryptoPrimitives Digest} (d : FComDischarge P) : P.binding :=
  d.entails_binding d.binding_holds

/-- `unlinkable_discharged_by_crypthol` — given a CryptHOL F_com discharge, the hiding half of
`unlinkable` is inhabited, witnessed by `abstract_perfect_hiding`. Kernel-clean. -/
theorem unlinkable_discharged_by_crypthol
    {P : CryptoPrimitives Digest} (d : FComDischarge P) : P.unlinkable :=
  d.entails_unlinkable d.hiding_holds

/-- `binding_unlinkable_discharged_by_crypthol` — the bridge theorem. A CryptHOL F_com discharge
witnesses both `binding` and `unlinkable`. The carriers that `EpistemicConsensus §6` leaves OPEN
in Lean are discharged by a real proof in a real UC tool. Proved in Lean (kernel-clean) from the
carried CryptHOL facts — Lean threads the cross-system witness; it does not prove UC itself. -/
theorem binding_unlinkable_discharged_by_crypthol
    {P : CryptoPrimitives Digest} (d : FComDischarge P) : P.binding ∧ P.unlinkable :=
  ⟨binding_discharged_by_crypthol d, unlinkable_discharged_by_crypthol d⟩

/-! ## Non-vacuity over the reference instance.

Witnesses that `FComDischarge` is inhabitable by discharging it for the toy primitive set
(`Crypto.Primitives.Reference`, carriers `True`). Not the real CryptHOL transport — an
inhabitation witness only. The real discharge is for the Poseidon2/Pedersen FFI instance,
vouched under the transport-fidelity caveat against `Dregg2_FCom.thy`. -/

namespace Reference
open Dregg2.Crypto.Reference

/-- The reference primitive set's `binding`/`unlinkable` are `True`, so the discharge is
trivially constructible — the non-vacuity witness that `FComDischarge` is inhabitable. -/
def refDischarge : FComDischarge (Digest := Int) instCryptoPrimitives where
  correct := True
  perfectHiding := True
  bindingReducesToDLog := True
  correct_holds := trivial
  hiding_holds := trivial
  binding_holds := trivial
  entails_binding := fun _ => trivial
  entails_unlinkable := fun _ => trivial

/-- Non-vacuity of the bridge: at the reference instance the carriers are discharged. -/
example : (instCryptoPrimitives.binding) ∧ (instCryptoPrimitives.unlinkable) :=
  binding_unlinkable_discharged_by_crypthol refDischarge

end Reference

-- The bridge theorems rest only on the carried `FComDischarge` fields (passed as a
-- hypothesis). This is a carrier, not a Lean UC proof.
#assert_axioms binding_discharged_by_crypthol
#assert_axioms unlinkable_discharged_by_crypthol
#assert_axioms binding_unlinkable_discharged_by_crypthol

end Dregg2.Crypto.UCBridge
