# Lean: conservation & supply

What the conservation subsystem of dregg2 IS at HEAD. Two Lean modules: a tactic/lemma
library (`Dregg2.Conserve`) and the typed conservation law (`Dregg2.Spec.Conservation`).
The law is grounded in the Rust effect coloring (`turn/src/action.rs`); the Lean side does
not port the real effect enum — it works over an abstract carrier and proves the algebra.

## The coloring: `LinearityClass` (six colors)

An effect is not just "ordinary vs mint/burn". It carries one of exactly six *linearity
colors* saying HOW it may move a conserved quantity. The Lean enum mirrors the Rust one:

- `Dregg2.Spec.LinearityClass` — six constructors: `Conservative`, `Monotonic`, `Terminal`,
  `Generative`, `Annihilative`, `Neutral` (`Dregg2/Spec/Conservation.lean:78`).
- The Rust source it mirrors: `pub enum LinearityClass { Conservative, Monotonic, Terminal,
  Generative, Annihilative, Neutral }` (`turn/src/action.rs:886`).

Color meanings (from the constructor docstrings, `Dregg2/Spec/Conservation.lean:78`):
- `Conservative` — paired: per-domain deltas must sum to `0` (`Σδ = 0`); a debit matched by
  an equal credit (transfer/move).
- `Monotonic` — may only increase (append-only counter, monotone clock); unpaired.
- `Terminal` — one-way, no inverse (a finalized/consumed marker); unpaired.
- `Generative` — created from nothing (a mint); NOT conserved, but the break is *disclosed*.
- `Annihilative` — destroyed (a burn); NOT conserved, disclosed like `Generative`.
- `Neutral` — touches no conserved quantity (opaque metadata field); the trivial color.

Two classifiers over the color, each an exhaustive `match` with no default arm (so a new
color cannot compile until it answers both questions):
- `LinearityClass.requires_paired_sibling : LinearityClass → Bool` — true *exactly* on
  `Conservative` (`Dregg2/Spec/Conservation.lean:104`).
- `LinearityClass.is_disclosed_non_conservation : LinearityClass → Bool` — true *exactly* on
  `Generative` or `Annihilative` (`Dregg2/Spec/Conservation.lean:116`).

The classifier prose is pinned to the `def`s by three theorems:
- `requires_paired_sibling_iff` — `= true ↔ c = Conservative`
  (`Dregg2/Spec/Conservation.lean:127`).
- `is_disclosed_non_conservation_iff` — `= true ↔ (c = Generative ∨ c = Annihilative)`
  (`Dregg2/Spec/Conservation.lean:132`).
- `paired_and_disclosed_exclusive` — no color both requires a paired sibling and is a
  disclosed non-conservation; the two regimes are mutually exclusive
  (`Dregg2/Spec/Conservation.lean:139`).

The Rust classifiers match: `requires_paired_sibling` returns true only for
`Conservative` (`turn/src/action.rs:925`); the disclosed-non-conservation check matches
`Generative | Annihilative` (`turn/src/action.rs:938`).

## The coloring map `linearity : Effect → LinearityClass`

`Effect` here is an ABSTRACT carrier — the Lean module deliberately does NOT port dregg1's
large effect enum. A three-constructor example type (`transfer`, `mint`, `setField`,
`Dregg2/Spec/Conservation.lean:154`) witnesses that the coloring map is total and
discriminating:
- `linearity : Effect → LinearityClass`, total, no default arm: `transfer ↦ Conservative`,
  `mint ↦ Generative`, `setField ↦ Neutral` (`Dregg2/Spec/Conservation.lean:164`).
- `linearity_examples` — the transfer is paired, the mint is a disclosed non-conservation,
  the set-field is neither (`Dregg2/Spec/Conservation.lean:171`).

The real total map lives in Rust: `Effect::linearity(&self) -> LinearityClass`
(`turn/src/action.rs:1645`), e.g. `Transfer ↦ Conservative` (`turn/src/action.rs:1648`),
`IncrementNonce ↦ Monotonic` (`turn/src/action.rs:1671`), `RevokeCapability ↦ Terminal`
(`turn/src/action.rs:1684`). The Lean module does not enumerate these — it proves the
algebra a coloring of any such shape obeys.

## Domains and per-domain conservation, parametric over a value monoid

The conserved quantity in a domain is valued in an *arbitrary* commutative monoid `Bal`
(`variable {Bal : Type*} [AddCommMonoid Bal]`, `Dregg2/Spec/Conservation.lean:204`). In the
public case `Bal = ℤ` (cleartext balances); in the private case `Bal` is a commitment group.
The same law runs over both.

- `Dregg2.Spec.Domain` — four distinct domains: `balance`, `note`, `gas`, `crossCell`
  (`Dregg2/Spec/Conservation.lean:189`).
- `conservedInDomain (dom : Domain) (deltas : List Bal) : Prop := deltas.sum = 0` — the
  `Conservative`-color obligation lifted to an arbitrary monoid; the `dom` argument names the
  four independent obligations (`Dregg2/Spec/Conservation.lean:210`).

This generalizes `Dregg2.Core`'s conservation, which already states the conserved quantity
as a monoid-valued measure `count : Cell → M` over any commutative monoid `(M,+,0)`
(`Dregg2/Core.lean:80`, `Dregg2/Core.lean:31`); the Spec module factors the value type out as
an explicit parameter so the *same* `Σδ = 0` runs over commitments.

### Key theorem 1 — conservation over a monoid

- `conservation_over_monoid (dom) (pre : Bal) (deltas) (hcons : conservedInDomain dom deltas)
  : pre + deltas.sum = pre` — if the `Conservative` deltas sum to `0`, adding them to any
  prior total leaves it unchanged (`Dregg2/Spec/Conservation.lean:217`).
- `conservation_over_monoid_finset` — the `Finset.sum` form the executable kernels use: given
  `bal δ : ι → Bal` over a `Finset` with `Σ δ = 0`, the post total equals the pre total
  (`Dregg2/Spec/Conservation.lean:226`).

## Disclosure obligation (receipt-binding) for non-conservation

A `Generative`/`Annihilative` delta need NOT be `0`, but because
`is_disclosed_non_conservation` is true for exactly those colors, the broken amount must be
DISCLOSED. The module models "bound into the receipt" as a *field* of a receipt record, so
the binding is structural, not a side condition.

- `Receipt (Bal)` — a `color : LinearityClass` plus `disclosedDelta : Option Bal`
  (`Dregg2/Spec/Conservation.lean:252`).
- `Receipt.WellFormed r := r.disclosedDelta.isSome = r.color.is_disclosed_non_conservation` —
  a receipt discloses a delta exactly when its color demands it
  (`Dregg2/Spec/Conservation.lean:262`).

### Key theorem 2 — disclosed non-conservation

- `disclosed_non_conservation (r) (hwf : r.WellFormed)` — for a well-formed receipt: a
  disclosed-non-conservation color *forces* a present delta, and a non-disclosed color
  carries `none`. The delta value is not constrained to `0` (mint/burn legitimately break
  conservation); only its *disclosure* is required (`Dregg2/Spec/Conservation.lean:270`).
- `conservative_discloses_nothing` — corollary: a `Conservative` receipt discloses nothing;
  its only obligation is `Σδ = 0`, checked against the deltas, not the receipt. The two
  regimes are disjoint: conserved ⇒ no disclosure, disclosed ⇒ not conserved
  (`Dregg2/Spec/Conservation.lean:285`).

## Key theorem 3 — committed ⇔ cleartext (the privacy payoff)

Conservation over hidden committed values is equivalent to cleartext conservation, carried by
a monoid hom `h : Cleartext →+ Commitment` (Pedersen, here an `AddMonoidHom` PARAMETER, so
the law rests on a hypothesis not an axiom). Two `AddCommMonoid` value types
(`Dregg2/Spec/Conservation.lean:315`):

- `committed_of_cleartext (h) (s) (δ) (hcleartext : Σ δ = 0) : Σ (h ∘ δ) = 0` — the forward
  half, pure homomorphism (`map_sum`/`map_zero`), no injectivity needed; the direction the
  PROVER uses to publish a blind committed check (`Dregg2/Spec/Conservation.lean:322`).
- `committed_iff_cleartext (h) (hinj : Function.Injective h) (s) (δ) : Σ δ = 0 ↔ Σ (h ∘ δ) =
  0` — under the binding hypothesis that `h` is injective, blind committed conservation is
  sound and complete for real cleartext conservation; injectivity is consumed only in the
  backward direction (the VERIFIER's) (`Dregg2/Spec/Conservation.lean:333`).

## Key theorem 4 — multi-domain independence

The four domains conserve INDEPENDENTLY; no cross-domain leakage (a surplus in one domain
cannot cover a deficit in another — the "pay gas with notes" attack).

- `TurnDeltas (Bal) := Domain → List Bal` — one delta list per domain
  (`Dregg2/Spec/Conservation.lean:359`).
- `turnConserves (td) : Prop` — the conjunction of `conservedInDomain` over `balance`, `note`,
  `gas`, `crossCell`; no cross-domain term (`Dregg2/Spec/Conservation.lean:363`).
- `multi_domain_independent (td) : turnConserves td ↔ (∀ dom, conservedInDomain dom (td dom))`
  — whole-turn conservation is *exactly* the four separate domain checks
  (`Dregg2/Spec/Conservation.lean:372`).
- `turnConserves_balance` — projection: a conserving turn conserves the balance domain in
  particular (no domain is vacuous) (`Dregg2/Spec/Conservation.lean:385`).

## The §8 OPEN: range-proof anti-inflation rib

`committed_iff_cleartext` assumes well-formed openings. A malicious prover can satisfy
`Σ commitments = 0` by committing to an out-of-range value (a "negative" amount that is a
huge value mod the group order), hiding inflation while the blind sum checks out. The Lean
law is parametric over `Bal` and sees only the algebra — it CANNOT rule this out. Soundness
needs a per-note range proof (`0 ≤ value < 2^n`), which is the CIRCUIT's job, not this
module's. The obligation is *named*, not discharged:

- `RangeObligation (InRange : Bal → Prop) (s) (δ) := ∀ i ∈ s, InRange (δ i)` — the shape of
  the §8 obligation, stated as an explicit premise the circuit/executable layer must supply,
  so downstream proofs take it as a hypothesis rather than smuggle it
  (`Dregg2/Spec/Conservation.lean:413`).

## The proof library and tactics (`Dregg2.Conserve`)

Factors out the patterns that recur verbatim in the executable kernels. `CellId := Nat`
(`Dregg2/Conserve.lean:23`); the conserved quantity here is `CellId → ℤ`.

General `Finset.sum` lemmas:
- `sum_indicator` — an indicator that is `v` at `a ∈ acc` and `0` elsewhere sums to `v`
  (`Dregg2/Conserve.lean:33`).
- `sum_pointUpdate` — a pointwise update changes the sum by the sum of per-point deltas
  (`Dregg2/Conserve.lean:42`).
- `sum_conserve_of_deltas_zero` — if per-point deltas sum to `0`, the total is conserved
  (`Dregg2/Conserve.lean:49`).
- `sum_transfer_conserve` — a debit/credit between two *distinct* cells (`src ≠ dst`, both in
  `acc`) conserves the sum; the deltas (`-amt` at `src`, `+amt` at `dst`) are individually
  nonzero but globally cancel. `hne : src ≠ dst` is load-bearing
  (`Dregg2/Conserve.lean:57`).

Tactics:
- `conserve` — closes `(∑ f) = ∑ g` when per-point deltas cancel *pointwise* (re-labellings,
  `+v−v` round-trips, per-cell net zero). Wrapped `first | <real> | fail "…"`: if deltas do
  not cancel pointwise, `ring` fails and the tactic errors loudly — it never falls through to
  a weaker closer that could mask a missing hypothesis. The two-cell move is NOT pointwise;
  use `sum_transfer_conserve` for that (`Dregg2/Conserve.lean:102`). A `fail_if_success`
  negative test guards the honesty rail (`Dregg2/Conserve.lean:170`).
- `commit_cases h with pat` — for a fail-closed executor `if guard then some … else none`
  given `h : f … = some s'`: splits the `if`, closes the `none` branch by contradiction, and
  on the `some` branch reads back the result (`Option`/`Prod` injection + `subst`) and
  `obtain`s the guard — leaving the content goal open. It runs NO closer on the `some` branch
  (which carries the real obligation) (`Dregg2/Conserve.lean:133`).

## Axiom hygiene

Both modules pin their keystones kernel-clean with `#assert_axioms`. The macro errors unless
every axiom the named decl depends on is one of the three standard kernel axioms (`propext`,
`Classical.choice`, `Quot.sound`); it fails the build on any faked-green axiom
(`Dregg2/Tactics.lean:47`).

- `Dregg2.Conserve` pins `sum_indicator`, `sum_pointUpdate`, `sum_conserve_of_deltas_zero`,
  `sum_transfer_conserve` (`Dregg2/Conserve.lean:77`).
- `Dregg2.Spec.Conservation` pins the four key theorems and their supporting classifier facts
  — including `conservation_over_monoid`, `committed_iff_cleartext`,
  `multi_domain_independent`, and `disclosed_non_conservation`
  (`Dregg2/Spec/Conservation.lean:421`).

`RangeObligation` is *not* pinned (it is a named hypothesis, not a proved fact).

## Shape of the whole

The coloring (`LinearityClass` + `linearity`) decides, per effect, *which* law applies:
`Conservative` ⇒ the `Σδ = 0` obligation (`conservedInDomain`, proved by
`conservation_over_monoid`); `Generative`/`Annihilative` ⇒ a disclosure obligation
(`Receipt.WellFormed`, proved by `disclosed_non_conservation`); `Monotonic`/`Terminal`/
`Neutral` ⇒ neither paired nor disclosed. The value monoid is a parameter, so the same
`Σδ = 0` covers cleartext balances and Pedersen commitments, joined by `committed_iff_cleartext`.
The four domains conserve independently (`multi_domain_independent`). The one acknowledged
gap — hidden out-of-range inflation under commitment — is named as `RangeObligation` and
deferred to the circuit.
