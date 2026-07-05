# Membrane / forwarder — where authority composes UPWARD

`cell/src/membrane.rs`. The unit of object-capability *abstraction*.

## What it is

dregg's cap discipline, before this, only knew how to go **down**. A facet
narrows authority on the way to a delegate (`is_facet_attenuation` — the
`EffectMask` submask, never amplify), and a read-cap does the dual for reads
(`ReadCap::attenuate` returns `None` on a slot you cannot read). Both answer one
question: *may a child do less than its parent?* They have no answer for the
opposite move — taking two authorities you hold and **composing** them into a
single new authority that may be exercised only by presenting **both**.

A **membrane** is a cell whose program is a composition policy. It holds (or
references) caps **A** and **B** and exposes a new cap **C** whose exercise
REQUIRES presenting both. This is the *forwarder* of E / object-capability
practice: a guarded facet that re-exports a conjunction of inner authorities. It
is the dual of attenuation — authority composes upward through it — and it is the
unit of ocap abstraction (a membrane *is* an object whose interface is "exercise
C", implemented over A and B).

```text
   attenuation (descent)            membrane (ascent)
   parent ⊒ child                   {A ∧ B} ⊒ C
   is_facet_attenuation(p, c)       is_facet_attenuation(a & b, exposed)
```

The membrane is the SAME submask partial order the descent side already proves,
read upward through a **meet**.

## The weld (over existing primitives, no new crypto)

| membrane piece            | welded over (existing)                              |
|---------------------------|-----------------------------------------------------|
| `HeldFacet { target, mask }` | the bare authority shape — `CellId` + `EffectMask` (`cell/src/facet.rs`) |
| `compose_both(a, b) = a.mask & b.mask` | the meet on the `EffectMask` lattice |
| non-amp check at seal     | `is_facet_attenuation(a & b, exposed)` — the proven submask order |
| `Membrane::seal → Option` | mirrors `ReadCap::attenuate → Option` (forge ⇒ `None`) |
| `MembraneCap { target, authority }` | the exposed cap C, authority `⊑ a & b` |

No descriptor, cap-root, or circuit code is touched. The membrane is pure
ocap-algebra over the cell crate's facet lattice.

## The composition policy

`CompositionPolicy::BothOf` — the genuine 2-of-2 slice. C fires only when the
caller presents proof of holding both A and B, and C's exposed authority is
bounded by the meet `a & b`:

```text
   authority_bound(A, B)  =  a.mask & b.mask      (the conjunction floor)
```

An effect bit may appear in C's exposed authority only if BOTH held caps carry
it. If only A carries it, A's partner B could not have justified it, so granting
it through C would be **amplification**.

## The non-amplification floor (the load-bearing constraint)

A membrane must never leak more authority than its held caps jointly justify:

```text
   exposed ⊑ compose(A, B)               (no amplification)
```

This is enforced **twice**:

1. **At seal** (`Membrane::seal`) — the only path to a usable cap C. A forged
   membrane whose `exposed` claims a bit outside `a & b` returns `None`. A
   leaking membrane simply does not come into being. (Dual of
   `ReadCap::attenuate` refusing a slot you cannot read.)

2. **At exercise** (`SealedMembrane::exercise`) — a defensive re-check, so a
   `SealedMembrane` reconstructed by tampered deserialization (bypassing
   `seal`) is still refused (`MembraneError::AmplifyingMembrane`).

The forge-detector is genuine, not a stub: `forged_over_grant_is_rejected_at_seal`
and `forged_grant_of_bit_in_neither_is_rejected` construct over-granting
membranes and assert they do not seal; `tampered_sealed_membrane_is_rejected_at_exercise`
forges `exposed` post-seal and asserts the exercise path refuses.

## The require-both gate (`SealedMembrane::exercise`)

In order:

1. **Both presented** — missing A ⇒ `MissingA`, missing B ⇒ `MissingB`. This is
   the refuse-without-both tooth (`a_alone_is_refused`, `b_alone_is_refused`).
2. **Each presentation matches the held cap** — same target, and at least the
   recorded authority (`held ⊆ presented`). You cannot prove "I hold A" by
   presenting something weaker than A or over a different target
   (`presenting_a_weaker_facet_does_not_prove_holding`,
   `presenting_wrong_target_does_not_prove_holding`).
3. **Defensive non-amp re-check** (see above).
4. **Requested effect within exposed authority** — outside ⇒ `NotExposed`
   (`exercising_outside_exposed_authority_is_refused`).

## The bar (passing tests, `cargo test -p dregg-cell membrane` — 14 green)

- `a_plus_b_exercises_c` — A+B exercises C (**success**).
- `a_alone_is_refused` / `b_alone_is_refused` — A-alone / B-alone (**refused**).
- `forged_over_grant_is_rejected_at_seal` + `forged_grant_of_bit_in_neither_is_rejected`
  + `tampered_sealed_membrane_is_rejected_at_exercise` — the **non-amp
  forge-detector**: a forged "C grants more than A∧B" is **rejected**.
- `exposed_is_always_submask_of_held_meet` — the soundness invariant
  `exposed ⊑ a & b` directly, over a sweep of mask pairs.

The full `dregg-cell --lib` suite is green (699 tests).

## Honest seams (named with their lanes)

- **Executor tooth PROVEN, circuit tooth not yet bound.** The executor non-amp
  floor is no longer just smoke-tested: it is the executor image of the
  kernel-clean Lean rung `metatheory/Dregg2/Deos/Membrane.lean` (the upward
  conjunction leg — `membrane_non_amplifies` — proven by reuse of the same
  `capAuthConferred ⊆` order / `attenuate_subset` the cap crown proves on), and
  `membrane.rs::non_amp_floor_matches_lean_rung` mirrors that rung's witnesses on
  the Rust side. What remains is the **circuit** tooth: a `SealedMembrane` is a
  verified-policy object and `MembraneCap` is the exposed cap C, but binding the
  membrane's `exposed` mask into the cell state-commitment / cap-root the circuit
  sees (so a light client *witnesses* "C's authority = a&b") is still the circuit
  follow-up — the same VK-gated lane the cap-root reshape
  (`project-cap-reshape-plan`) drives. The proven executor tooth is real; the
  circuit tooth is its named shadow.
- **2-of-2 is the genuine slice, not the ceiling.** `CompositionPolicy` is the
  additive surface for k-of-n (hold a `Vec` of facets, require a quorum) and
  predicate-gated composition (the `CapabilityCaveat::Witnessed` surface).

## Next slice

1. **k-of-n / predicate-gated `CompositionPolicy`** — generalise the meet to a
   quorum bound, and admit a `WitnessedPredicate` gate on exercise.
2. **Circuit binding** — fold `exposed` into the cap-root so a light client
   witnesses the composition floor; the executor non-amp tooth becomes a circuit
   rung (`exposed ⊑ a & b` in-circuit), riding the cap-reshape VK lane.
3. **Turn-executor integration** — surface the membrane as a held cell-program
   so `ExerciseViaCapability` routes through `SealedMembrane::exercise` with the
   real in-circuit cap-membership witness replacing `Presentation`.
