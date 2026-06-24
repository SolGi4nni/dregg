# Supply as a linear verb — deriving the model from the metatheory

> ⚠ CORRECTION (mutation-canary, `scripts/mutation-canary.sh`): the claims below that the supply
> layer is "conserved-affine," that Stage 3 "broke the meta-law," and that a law-violating burn
> "passed with nothing catching it" are **empirically REFUTED**. Real mutation testing (replace the
> burn gate with `True`) goes **RED** — `auth_drop_breaks_iff` (sorry-free) shows the admission
> biconditional `(∃ commit) ↔ BurnGuard` becomes false. The supply authority **is load-bearing**
> (executor ⟺ `BurnGuard`). Stage 3 stayed green because it was a *lockstep guard+def migration*
> (monotone add-a-disjunct), not a decorative pass-through. What remains valid + worth building is
> NARROWER: the `BurnGuard`/`mintSpec` specs are not yet proven **independent + meaningful** (they
> may be gate-copies, not refinements of intent). The verb-binding below is the right *hardening* —
> it makes the supply spec a genuine refinement of `Metatheory.Verb`/`AuthorizedProduction`, gated by
> the `@[load_bearing]` linter (import-boundary + `isDefEq spec gate` + `NonVacuous`) and the canary —
> but it is hardening an already-load-bearing system into a provably-meaningful one, not a rescue.


Status: design + plan. The supply work to date (per-asset wells, `Effect::Mint`, the Stage-3
self-redeem split) built a **conserved-affine** supply layer. That is *wrong against our own
abstract spec*: it lets a holder unilaterally move value out with **no admission**, which is
not a verb. This document derives the correct model from `metatheory/Metatheory` and lays out
the plan to slot it through the whole stack.

## What the metatheory FIXES (not chosen — derived; file:line)

The abstract spec is bound to the concrete kernel (`Metatheory/Categorical.lean:23`,
`Dynamics/VerbSignature.lean:36` both `import Dregg2.Laws`; §2 proves the abstract `Seam` **is**
`Dregg2.Laws.predicate_witness_galois`). It fixes three things that together *are* the supply
semantics:

1. **Value is the LINEAR substance.** `Dynamics/Substance.lean` — the four substances are
   `value × authority × evidence × state`; §2(b) "Value — the linear discipline bites."
   `Categorical.lean §1(a)`:
   - `no_free_copy` — a non-zero value has no `copy : A ⟶ A⊗A` (no contraction).
   - **`no_free_discard`** — a discard `wk : A ⟶ 𝟙` forces `Σ̃A = 0`: a non-zero value **cannot
     be dropped**. It can only be **moved by a frame-preserving update** (`Fpu`).

2. **A verb fires iff `Admission ∧ Footprint-Fpu`.** `Dynamics/VerbSignature.lean`
   `kernel_meta_law`: a `Verb` is *literally* `Admission × Footprint`, and `Fires v w` requires
   BOTH — the admission witness discharges the demand (the `Predicate ⊣ Witness` authority seam)
   AND the footprint is conservation-preserving. **A move with no admission is not a verb.**

3. **Authority grows only by `AuthorizedProduction`.** `Dynamics/Production.lean` (non-forgeable
   frame-preserving production) + `Open/AuthorityClosure.noforge_closure` (the transitive
   non-amplification closure). You can only exercise authority you hold or were authorized to
   produce.

## The forced reading of "burn"

A burn is **a verb on linear value**. Therefore:

- **It is never a drop.** `no_free_discard` forbids destroying value. The well model is the
  *correct realization*: a burn **moves** value holder→well (`Σ̃` invariant including the well —
  `Open/ConservationMultiEdge.round_boundaryFlow_zero`). Stage 1 (conserving well-burn) is
  exactly this and is right.
- **It must be admitted.** By `kernel_meta_law`, the move only fires if its **admission demand**
  is discharged by a witness. The admission demand for moving value *out of a holding* is an
  **authority** predicate. **"Return through an issuer-approved path" = the burn verb's admission
  demand is the issuer's authority predicate**, and the holder discharges it by producing the
  witness the issuer's policy requires.
- **Permissionless self-redeem is a verb with no admission → it violates `kernel_meta_law`.**
  Stage 3's `actor = cell ⇒ unconditional` is the bug: it is not "the affine case," it is a
  non-verb. There is no affine case for value — value is linear; the only freedom is *which
  witness the issuer's predicate admits*.

## Linear-vs-"affine" is NOT a per-asset toggle — it is the issuer's admission predicate

The kernel mechanism is **one**: every supply verb fires iff `Admission(issuerPredicate) ∧ Fpu`.
The per-asset variation people call "linear vs affine" is entirely the **issuer's admission
predicate** (its `Predicate ⊣ Witness` demand), which lives where DREGG3 already says policy
lives — the issuer cell's program:

- **Strict-linear asset**: the issuer's predicate admits a return only with an issuer-granted
  return witness (a return capability the issuer produced — `AuthorizedProduction`). No witness ⇒
  the holder *cannot* move value out; it is genuinely conserved-and-stuck until the issuer admits
  a path. This is the "proper linear resource."
- **Permissive asset**: the issuer's predicate is satisfied by a trivial witness (`Admits` holds
  for any holder of the value). A holder returns freely — but it is *still a verb* (trivial
  admission), *still conserving*, never a drop.

So we support every point on the spectrum with **one kernel law**, and the asset's issuer chooses
its predicate. Nothing is hardcoded; nothing collapses the linear distinction.

## Where it must slot (the whole object, not just the executor)

| layer | what it must enforce | today |
|---|---|---|
| `Metatheory/Dynamics` (abstract) | supply op IS a `Verb`; `Fires = Admission ∧ Fpu` | the laws exist; **supply ops not yet bound to `Verb`** |
| `Dregg2` kernel (`recKBurnAsset`/`recKMintAsset`) | admission = issuer predicate (not `actor=cell`/bare `mintAuthorizedB`); Fpu = well-move | **admission is permissionless self-redeem (Stage 3) — non-verb** |
| executor (`apply_burn`/`apply_mint`) | run the **issuer/well cell's program** as the admission demand | **`collect_touched_cells` has no Burn/Mint arm → issuer program never evaluated** |
| circuit (Argus / the supply rung) | the in-circuit admission gate witnesses the issuer predicate | mint VALUE_FORCED proven; **admission-as-issuer-predicate not yet the gate** |
| userspace verifier (`dregg-userspace-verify`) | checks conservation **and** the supply admission | checks conservation (B) + authority generally; **supply admission not a distinct check** |

## Plan (staged; each stage binds a layer to the law)

1. **Bind the concrete supply op to the abstract `Verb`** (Lean). Express `recKBurnAsset`/
   `recKMintAsset` as `Metatheory.Dynamics.Verb` instances and prove `Fires = Admission ∧ Fpu`
   via `kernel_meta_law`. This makes the meta-law the *definition* of a valid supply op and turns
   "permissionless self-redeem" into a type error (a verb without an admission demand cannot be
   constructed). **Revert Stage 3's unconditional self-redeem here** — replace it with
   `admission = issuerPredicate actor a`.
2. **The issuer predicate = the issuer cell's program** (Lean + Rust). Define the supply admission
   demand as the issuer/well cell's program-as-predicate (DREGG3 "policy lives in the issuer's
   program," realized as the seam, not a docstring). Default issuer program = permissive predicate
   (recovers today's behavior for un-opted assets); a linear asset's program demands a return
   witness.
3. **Wire the executor admission** (Rust). Add Burn/Mint arms to `collect_touched_cells` so the
   issuer/well cell enters the program-eval set; `apply_burn`/`apply_mint` admit the move iff the
   issuer cell's program (predicate) is discharged by the turn's witness. Remove the
   `actor==target ⇒ skip` shortcut; the self path discharges the (possibly-trivial) issuer
   predicate like any other.
4. **Circuit admission rung** (VK-affecting, deploy-gated). The supply selector's in-circuit gate
   witnesses the issuer-predicate discharge (the admission half), on top of the proven Fpu/value
   forcing. Mirrors the cap-membership pattern.
5. **Userspace verifier** (Rust). Add a supply-admission check beside conservation: a forest's
   burn/mint moves each carry a witness discharging the issuer predicate; flag any supply move
   admitted without one.

## The invariant this restores

After this, "can a holder shrink an asset's supply with no issuer participation?" is answered by
the issuer's own predicate, *enforced as a verb admission across kernel + circuit + verifier* —
not by a hardcoded kernel branch, and never by dropping value (which `no_free_discard` forbids).
Linear resources become real: their issuer's predicate has no trivial witness, so value returns
only through the path the issuer produced authority for.
