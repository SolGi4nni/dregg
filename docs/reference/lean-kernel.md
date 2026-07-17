# Lean: the kernel spec

What this subsystem is: the Lean4 formalization of the dregg kernel as an l4v-shaped
**spec ⊑ design** stack. `Dregg2/Spec/` states the laws (abstract `Prop`s, parametric over
value monoids and rights lattices); `Dregg2/Exec/` builds an executable machine; the
refinement modules prove the machine satisfies the laws. The abstract conservation algebra
lives at the root in `Dregg2/Core.lean`.

Everything below is cited to a real `Module.decl` at HEAD.

---

## Core — the conservation algebra (`Dregg2/Core.lean`)

The most abstract layer: cells and turns as a (claimed) symmetric-monoidal category, with
conservation as a monoid-valued measure.

- `Dregg2.Core.Cell` — a unit of sovereign state, carrying an opaque `id : Nat`
  (`Core.lean:48`).
- `Dregg2.Core.TurnTag` — a turn is `ordinary | mint k amount | burn k amount`; only
  `mint`/`burn` may move the conserved measure (`Core.lean:55`).
- `Dregg2.Core.Turn A B` — a morphism carrying a `tag : TurnTag` (`Core.lean:66`).
- `Dregg2.Core.Conservation M` (over `[AddCommMonoid M]`) — the measure `count : Cell → M`
  with per-generator `minted`/`burned : TurnTag → M`. The conservation law is a **balance**
  (`count A + minted = count B + burned`), not a signed delta, because a bare `AddCommMonoid`
  has no negation (`Core.lean:88`). The structure also carries a measure-level `tensor`/`unit`
  shadow of the monoidal product, with `unit_zero` (`count I = 0`) and `tensor_add`
  (`count (A ⊗ B) = count A + count B`) — i.e. `count` is a monoid homomorphism
  (`Core.lean:114`, `Core.lean:122`).
- `Dregg2.Core.ConservesStep cons` — Law 1 carried as a typeclass `Prop` field
  (`step : ∀ f, count A + minted f.tag = count B + burned f.tag`), the operational model's
  obligation, discharged elsewhere — explicitly NOT an unproved hole (`Core.lean:149`).

Proved corollaries from the field:

- `conservation_ordinary` — an ordinary turn preserves the measure exactly (`Core.lean:162`).
- `mint_delta` / `burn_delta` — generators move the measure by their inflow/outflow
  (`Core.lean:171`, `Core.lean:181`).
- `noClone_of_invariant_tensor` — the general no-clone core: over any cancellative comm
  monoid, `count A = count (tensor A A)` forces `count A = 0` (`Core.lean:206`).
- `withholding_no_free_copy` — the operational corollary: a conservation-respecting copy turn
  `A ⟶ A ⊗ A` (`ordinary`) admits only on the zero-measure cell (`Core.lean:227`).

`TurnCat` (the actual `Category`/`MonoidalCategory`/`SymmetricCategory` instances) is stated
as an existence obligation marked `TODO`, not discharged (`Core.lean:75`).

---

## Spec — the abstract laws (`Dregg2/Spec/`)

### Conservation (`metatheory/Dregg2/Spec/Conservation.lean`)

- `Spec.LinearityClass` — the effect coloring: six colors
  `Conservative | Monotonic | Terminal | Generative | Annihilative | Neutral`
  (`Conservation.lean:78`). Two exhaustive classifiers with no default arm:
  `requires_paired_sibling` (true exactly on `Conservative`) and
  `is_disclosed_non_conservation` (true exactly on `Generative`/`Annihilative`)
  (`Conservation.lean:104`, `Conservation.lean:116`). Proved: `requires_paired_sibling_iff`,
  `is_disclosed_non_conservation_iff`, and `paired_and_disclosed_exclusive` (the two
  classifiers are disjoint) (`Conservation.lean:127`, `:132`, `:139`).
- `Spec.Effect` — a tiny abstract carrier (`transfer | mint | setField`) with
  `linearity : Effect → LinearityClass` witnessing the coloring is total and discriminating;
  the real 50-variant enum is colored the same way (`Conservation.lean:154`, `:164`).
- `Spec.Domain` — the independent conservation domains `balance | note | gas | crossCell`
  (`Conservation.lean:189`).
- `Spec.conservedInDomain dom deltas := deltas.sum = 0` — the per-domain `Σδ = 0` criterion,
  parametric over a value monoid `Bal` (`Conservation.lean:210`). KEY theorems:
  `conservation_over_monoid` (`pre + Σδ = pre`, `:217`) and `conservation_over_monoid_finset`
  (the `Finset.sum` form the executable kernels use, `:226`).
- `Spec.Receipt` + `Receipt.WellFormed` — the disclosure discipline: a receipt discloses a
  domain delta `iff` its color is a disclosed non-conservation, structurally (a field, not a
  side condition) (`Conservation.lean:252`, `:262`).
- `Spec.TurnDeltas` / `turnConserves` / `multi_domain_independent` — a turn conserves iff
  every domain conserves; no cross-domain leakage (`Conservation.lean:359`, `:363`, `:372`).

### Guard (`metatheory/Dregg2/Spec/Guard.lean`)

- `Spec.Guard Request Statement` — the gating algebra: five constructors
  `firstParty (p : Request → Bool) | witnessed (s : Statement) | all gs | any gs | gnot g`
  (`Guard.lean:90`). `all`/`any` are the meet/join; `witnessed` is the single site where the
  verify seam (the oracle kinds) enters.
- `Guard.admits g req w : Bool` — evaluation, a `mutual` recursion descending through lists
  via `admitsAll`/`admitsAny`; `witnessed s` evaluates to `Verifiable.Verify s (w s)`
  (`Guard.lean:107`). `admitsAll [] = true`, `admitsAny [] = false`.
- `admits_all` / `admits_any` — `all` is the meet (`∀ g ∈ gs`), `any` is the join
  (`∃ g ∈ gs`) (`Guard.lean:168`, `:176`).
- `Guard.attenuate g c := all [g, c]` — attenuation is the **meet** `a ⊓ c`, never a Heyting
  residual; `attenuate_narrows` proves `a ⊓ c ≤ a` (adding a conjunct only removes admitted
  requests) (`Guard.lean:195`, `:207`).
- `admits_witnessed_iff_discharged` — the demand⊣supply seam: a `witnessed s` guard admits
  iff the verifier discharges `s` with `w s` (`admits` is definitionally `Laws.Discharged` at
  the verify seam) (`Guard.lean:224`).

### Authority (`metatheory/Dregg2/Spec/Authority.lean`)

The capability graph as rights-labelled edges, parametric over `[SemilatticeInf Rights]
[OrderTop Rights]`.

- `Spec.Cap CellId Rights` — a directed edge `holder ⟶ target @ rights` (`Authority.lean:73`).
  `Spec.Graph := CellId → Cap → Prop` is the relational c-list (`Authority.lean:81`);
  `Graph.has h t := ∃ r, G h ⟨t, r⟩` is the Granovetter connectivity predicate
  (`Authority.lean:86`).
- `Spec.confers parent child := child.target = parent.target ∧ child.rights ≤ parent.rights`
  — the non-amplifying conferral order (`is_attenuation`), proved reflexive (`confers_refl`)
  and transitive (`confers_trans`) (`Authority.lean:100`, `:105`, `:110`).
- The ops, each a `Prop`-structure relation `G ⟶ G'` carrying its authorization premise in
  the relation: `Introduce` (Granovetter introduction, four-part discipline: connectivity +
  held parent + non-amplifying + consent, `Authority.lean:152`), `Amplify`
  (`Authority.lean:171`), `Mint` (powerbox, needs a held factory cap + contract conformance,
  `Authority.lean:189`), `Endow`, `Attenuate`, `Revoke`. They fold under `GenAct`
  (generative) and `RestrictAct` (restrictive), unified by `AuthStep`, closed by `Reachable`
  (reflexive-transitive closure of authorized steps) (`Authority.lean:249`, `:263`, `:271`,
  `:282`).

The keystone theorems (§5):

- `introduce_non_amplifying` / `introduce_same_target` — the conferred cap is `≤` the held
  cap and names the same target (`Authority.lean:294`, `:303`).
- `amplify_needs_held_amplifier`, `mint_needs_held_factory`, `mint_conforms_to_contract` —
  amplification/minting are not ambient; they require a held authorizing edge and (for mint)
  contract conformance (`Authority.lean:313`, `:321`, `:330`).
- `only_connectivity_begets_connectivity` — **the headline non-forgeability invariant**:
  every edge in a reachable graph either descends by conferral from an initial edge held by
  the same cell, or descends by conferral from an edge added by an authorized generative act.
  No edge appears ex nihilo. Proved by induction on `Reachable`, with the `attenuate` case
  extending the origin witness by one `confers_trans` narrowing (`Authority.lean:456`).

Axiom hygiene: §7 pins every keystone (including `only_connectivity_begets_connectivity`)
with `#assert_axioms` (`Authority.lean:552`–`:569`).

---

## Exec — the executable machine (`Dregg2/Exec/Kernel.lean`)

The l4v `design` analog: a computable `exec` that actually runs a turn, fail-closed, checking
both the resource law and authority.

- `Exec.KernelState` — finite `accounts : Finset CellId`, a total `bal : CellId → ℤ` (ℤ so
  debt is representable and conservation is a clean group argument), and a capability table
  `caps : Caps` (`Kernel.lean:35`).
- `Exec.Turn` — `actor` moves `amt` from `src` to `dst` (`Kernel.lean:45`).
- `Exec.authorizedB caps turn : Bool` — authorized over `src` iff the actor owns it
  (`actor = src`) OR holds a `node src` cap OR an `endpoint src` cap carrying `Auth.write`
  (`Kernel.lean:54`).
- `Exec.exec k turn : Option KernelState` — commits only when authorized, `0 ≤ amt`,
  `amt ≤ bal src`, `src ≠ dst`, and both cells are live accounts; otherwise `none`
  (fail-closed) (`Kernel.lean:69`).
- `Exec.total k := ∑ c ∈ accounts, bal c` — the conserved quantity (`Kernel.lean:78`).

Proved of the machine:

- `exec_conserves` — every committed turn preserves `total` (debit and credit cancel, via
  `transfer_sum_conserve`) (`Kernel.lean:109`, `:90`).
- `exec_authorized` — no state change without authority (`Kernel.lean:125`).
- `exec_unauthorized_fails` — an unauthorized turn does not commit (`Kernel.lean:134`).
- `kernel_run_conserves` — conservation across an entire `kernelSystem` run, lifting
  `exec_conserves` through `Execution.invariant_run` (`Kernel.lean:144`, `:150`).

`#guard`s at the end exercise it executably: `s0`/`t1`/`tBad` show an owned transfer commits,
an unauthorized one fails, and total is conserved at `105` (`Kernel.lean:162`–`:175`).

---

## The refinement square: `Exec ⊑ Spec` (`metatheory/Dregg2/Spec/ExecRefinement.lean`)

This module proves `Dregg2.Exec.Kernel ⊑ Dregg2.Spec.{Conservation,Guard,Authority}` — the
l4v `Design ⊑ Abstract` move — via two tractable projections of the simulation square.

**Conservation projection (§1).** `refineConservation s s'` packages the per-cell ℤ deltas as
the `List ℤ` that `Spec.conservedInDomain` consumes (`ExecRefinement.lean:80`).
`exec_refines_conservation` proves a committed `exec` step satisfies
`conservedInDomain Domain.balance` — i.e. `exec_conserves` IS Spec's `Σδ = 0` at `Bal = ℤ`,
`Domain.balance` (`ExecRefinement.lean:100`). `exec_refines_conservation_over_monoid` and
`exec_inhabits_balance_domain` lift to the abstract monoid form (`:118`, `:129`).

**Authority projection (§2).** `execAuthGuard caps : Guard ExecRequest Statement` is the
abstract gate built from the cap table; `exec_authz_refines_guard` /`exec_authz_iff_guard`
prove `Exec.authorizedB` admitting a turn corresponds to `Guard.admits` being `true`
(`ExecRefinement.lean:164`, `:172`, `:183`). `capToSpec` maps an executable
`Authority.Cap` into a `Spec.Cap`; `attenuate_confers_real`,
`confers_real_forbids_amplification`, `amplifying_grant_refused`, `strict_attenuation_witness`
tie attenuation to `Spec.confers` (`:246`, `:262`, `:272`, `:281`, `:293`).

The authority connectivity reference is split deliberately:

- `execGraph caps` is the executor's `.any confersEdgeTo` lookup gate copied verbatim, so it
  is `isDefEq` to that gate — making it a **negative calibration fixture** for the load-bearing
  linter's defeq check, carried `@[linter_calibration]`, NOT used as a connectivity spec
  (`ExecRefinement.lean:321`).
- `authConnects caps h c := ∃ cap ∈ caps h, authConnectsCap c.target cap` is the **independent**
  `Graph.has`-shaped reference (a `Prop`-existential over list membership, propositionally but
  not definitionally equal to the gate, so the refinement `gate ⟹ authConnects` is a real
  proof) (`ExecRefinement.lean:364`, `:355`). `authConnects_nonvacuous` proves it is neither
  everywhere-true nor everywhere-false (`:371`). `authConnects_is_authorized_production` binds
  it to the abstract `Metatheory.Dynamics.AuthorizedProduction` non-forgeability law
  (`:427`).

**The square (§3).** `AbstractState` carries `balanceTotal : ℤ` + `authGraph`; `absOf` is the
abstraction function; `Refines k a` is the simulation relation, witnessed by `refines_absOf`
(`ExecRefinement.lean:557`, `:565`, `:573`, `:577`). `exec_step_refines_conservation` and
`exec_step_refines_authority` prove each projection commutes; `exec_step_refines` assembles
them: every committed step has an abstract successor preserving both the conserved total and
the authority graph, with the turn passing the abstract gate
(`ExecRefinement.lean:585`, `:598`, `:623`). `run_refines_conservation` lifts the conservation
projection to a whole run (`:641`).

The full bisimulation's residual operational thread (a small-step abstract LTS) is marked
`-- OPEN:` as prose, not an open Lean hole; the two proved projections are the tractable
squares (`ExecRefinement.lean:26`–`:33`).

**Second square (§3.5).** The same conservation projection is re-proved for the
content-addressed record kernel (`Exec.RecordKernel`, `cell : CellId → Value`), which
conserves a named `balance` field: `recExec_refines_conservation` lands on the same
`conservedInDomain Domain.balance` law (`ExecRefinement.lean:677`).

Axiom hygiene: every keystone in this module is pinned with `#assert_axioms`
(`ExecRefinement.lean:757`–`:776`, plus `:473`/`:714`).

---

## What `#assert_axioms` certifies

`#assert_axioms foo` (defined `Tactics.lean:50`) errors unless every axiom `foo` transitively
depends on is in `Dregg2.cleanAxioms := [propext, Classical.choice, Quot.sound]`
(`Tactics.lean:31`). It is a pure rejector (it can fail a build but never close a goal) that
catches a faked-green axiom leaking into a "PROVED" keystone. Typeclass/hypothesis obligations
(the `CryptoKernel`/`World`/`Verifiable` seams) enter as parameters, not `axiom`-keyword
declarations, so they are not in scope of this guard by design (`Tactics.lean:23`).

---

## How it composes

```
Core.lean            abstract conservation algebra (monoid-hom measure, no-clone)
   │
Spec/Conservation    Σδ=0 per domain, parametric over Bal; effect coloring; disclosure
Spec/Guard           the gate algebra (meet/join/verify-seam); attenuation = meet
Spec/Authority       cap-graph laws; only_connectivity_begets_connectivity
   │  ⊑ (refinement)
Exec/Kernel          the computable fail-closed machine; exec_conserves, exec_authorized
   │
Spec/ExecRefinement  the simulation square: Exec ⊑ Spec on conservation + authority
                     (operational thread OPEN as prose), + the record-kernel square
```

The spec states laws over abstract carriers (a value monoid `Bal`, a rights lattice
`Rights`); the executable kernel is one concrete instance (`Bal = ℤ`, the `node`/`endpoint`
cap inductive); the refinement modules prove the instance satisfies the laws and pin the
proofs kernel-clean.
