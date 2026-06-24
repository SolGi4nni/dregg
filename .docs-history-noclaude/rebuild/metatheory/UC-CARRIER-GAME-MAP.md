# UC Carrier ↔ CryptHOL Game Map — the Lean↔Isabelle trust seam

This note is the **trust interface** for pillar #6 (UC-security). It records, per Lean §8 portal
carrier (a `Prop` the metatheory never proves), the **exact CryptHOL/AFP game** that discharges it,
and whether the discharge is **proved**, **perfect-fragment-only**, or **honestly open**.

Two kernels are in the trust base when you accept a carrier as discharged: Lean's, and
Isabelle/HOL's (plus the AFP entries and the **transport fidelity** — a human-checked, not
machine-checked, correspondence between the Lean object and the CryptHOL object). See
`Dregg2/Crypto/UCBridge.lean` header for the full caveat.

## Toolchain status (HONEST)

`isabelle` is **not installed** on this dev machine (only the AFP *sources* are present at
`~/isabelle/afp-2026-05-29/` and `~/isabelle/afp-devel-branch-default/`). The `.thy` files were
authored against the **real** AFP theory/lemma names (verified by source grep), but the green build
was **NOT reproduced locally**. To check:

```
isabelle build -d ~/isabelle/afp-2026-05-29/thys -d ~/dev/breadstuffs/uc-crypthol Dregg2_UC
```

(needs an `isabelle` binary matching AFP 2026-05-29). Until then, the `.thy` proofs are
**transcribed-but-unverified** — a precise formal model with attested library names, flagged here.

## The map

| Lean carrier (file:line) | Assumption | CryptHOL game | `.thy` theorem | Status |
|---|---|---|---|---|
| `PedersenKernel.binding` (PortalFloor.lean:111) · `CryptoPrimitives.binding` (Primitives.lean:41) | DLog binding | `Sigma_Commit_Crypto.Pedersen` `bind_advantage` = `discrete_log.advantage` | `Dregg2_FCom.dregg2_F_com_binding` / `…_binding_under_dlog` | **PROVED** (reduction to DLog) |
| `CryptoPrimitives.unlinkable` (Primitives.lean:46) — hiding half | perfect hiding | `abstract_commitment.perfect_hiding_ind_cpa` | `Dregg2_FCom.dregg2_F_com_hiding` | **PROVED** (advantage = 0, unconditional) |
| `PedersenKernel.commit_hom` (PortalFloor.lean:107) | (algebraic law, not an assumption) | group law | `Dregg2_FCom.dregg2_commit_hom` | **PROVED** (transport fidelity of the one law) |
| `SignatureKernel.unforgeable` (PortalFloor.lean:47) — ed25519 EUF-CMA | signature unforgeability | `Game_Based_Crypto.SUF_CMA.suf_cma` `advantage₁` / `secure_for₁` | `Dregg2_Carriers.suf_cma.dregg2_unforgeable` (= `∀𝒜. negligible (advantage₁ 𝒜)`) | **STATED as the real game** + non-vacuity proved; the *concrete* ed25519 advantage bound is the standing assumption |
| `MacKernelE.unforgeable` (PortalFloor.lean:271) — HMAC EUF-CMA | MAC unforgeability | same `suf_cma` (a MAC = single-key deterministic signature) | `Dregg2_Carriers.suf_cma.dregg2_unforgeable` | same as ed25519 |
| `Poseidon2Kernel.collisionHard` (PortalFloor.lean:150) | collision resistance | `Dregg2_Carriers.dregg2_hash.cr_game` (game-based CR on `spmf` + `Negligible`) | `dregg2_hash.secure_cr` (= `∀𝒜. negligible (cr_advantage 𝒜)`) | **GAME DEFINED** + perfect fragment proved (`injective_secure_cr`) + refuted on collapsing hash (`collapsing_not_secure_cr`) |
| `Blake3Kernel.collisionHard` (PortalFloor.lean:183) | collision resistance | same `dregg2_hash.cr_game` | `dregg2_hash.secure_cr` | same as Poseidon2 |
| `VerifierKernel.extractable` (PortalFloor.lean:78) — STARK/FRI | knowledge soundness / extractability | — (no off-the-shelf AFP game) | — | **OPEN** — Lean-side carrier only (PortalFloor §9 ref + §9b refutation) |
| `SealKernel.authentic` (PortalFloor.lean:237) — AEAD+X25519 | AEAD authenticity | (AFP `IND_CCA2_sym` is close but not authenticity) | — | **OPEN** — Lean-side carrier only |
| `NullifierKernel.unlinkable` (PortalFloor.lean:211) | anonymity | — | — | **OPEN** — Lean-side carrier only (determinism is *proved* in Lean) |

## Non-vacuity discipline (every new spec has a witness)

Each game-based carrier in `Dregg2_Carriers.thy` has BOTH:
- an **inhabitation** witness (a scheme where the carrier holds): reject-all signature
  (`dregg2_unforgeable_nonvacuous`), injective hash (`injective_secure_cr`);
- a **refutation** witness (a broken scheme where the carrier is FALSE): constant-1 advantage
  (`forgeable_advantage_not_negligible` / `not_negligible_1`), collapsing hash
  (`collapsing_not_secure_cr`).

This mirrors the Lean §9 / §9b discipline (`PortalFloor.lean` reference vs Forge/Collide instances):
a carrier is a *genuine* assumption, not `True` in disguise.

## Whole-protocol UC (F_dregg) — `Dregg2_FDregg.thy`

`F_dregg` is the **ideal capability-ledger functionality**: a state `(supply, caps, nullifiers)`
with the ideal transition `fdregg_step` that fires ONLY on **authorized + non-amplifying** effects
and performs the **conservation-preserving** update.

PROVED (perfect/structural fragment — the ideal world):
- per-step: `fdregg_authorized`, `fdregg_conserves`, `fdregg_no_amplify`,
  `fdregg_derived_cap_attenuates`, `fdregg_nullifier_fresh_then_spent`;
- whole-run: `fdregg_run_conserves`, `fdregg_run_nullifiers_monotone`, `fdregg_run_caps_monotone`;
- non-vacuity: `fdregg_inhabited` (a genuine authorized transfer run) + `…_conserves`.

STATED, **OPEN** (computational fragment — the realization crown):
- `dregg2_uc.Dregg2RealizesFDregg` — the running dregg2 protocol UC-realizes `F_dregg`, phrased in
  the `Constructive_Cryptography.advantage` (negligible distinguishing advantage) shape;
- `dregg2_uc.fdregg_realization_under_carriers` — realization FOLLOWS from the §8 carrier
  negligibilities **once** the hybrid simulator's per-η advantage bound (the `reduction` hypothesis)
  is supplied. That bound — *constructing* the simulator + the hybrid argument over the
  `Dregg2_Carriers`/`Dregg2_FCom` advantages — is the genuinely research-open part. It is carried as
  an explicit **hypothesis**, never asserted as a theorem. The last-mile (negligible closed under
  finite sums) IS discharged, so the only missing piece is the reduction's advantage bound.

This is the honest shape of the Canetti dynamic-UC residue that `UCBridge.lean` carries: the
structural/ideal guarantees are machine-checked; the computational realization is a precise OPEN.
