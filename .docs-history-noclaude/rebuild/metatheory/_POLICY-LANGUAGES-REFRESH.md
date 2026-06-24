# Policy-Languages Refresh — de-stodgying predicate / caveat / datalog (read-only design pass)

Scope: the three "policy" surfaces dregg2 FORMALIZES in Lean and ENFORCES by the verified executor —
the **predicate / cell-program** language, the **caveat** language, and the **datalog authorization**
language. Goal: more expressive + more ergonomic with the SAME-or-better assurance. This is a
design doc for an implementation wave; it changes no code. Every claim cites `file:line`.

Status legend used below:
- **STODGY-BUT-SOUND** — a real expressiveness/ergonomics gap, but no guarantee is broken; adding
  expressiveness is purely additive.
- **ENFORCEMENT-GAP** — the language can NAME something the executor does not actually enforce
  (a hole, not just a missing feature).

---

## 0. The surface map (what actually exists — corrects the prompt's "2-constructor toy")

There is **no** `RecOp setScalar/addScalar` toy predicate language driving admission. `RecOp`
(`Exec/RecordCell.lean:37`) is the *operation* alphabet a cell consumes, NOT the admission predicate.
The admission predicate is a genuinely substantial catalog, present in FIVE related surfaces:

| surface | file:line | constructors | who enforces it | predicate-or-function |
|---|---|---|---|---|
| `SimpleConstraint` | `Exec/Program.lean:51-71` | 9 (fieldEquals/Ge/Le/immutable/writeOnce/monotonic/strictMono/fieldDelta/not) | `evalSimple` (`:106`) | **predicate** (filter) |
| `StateConstraint` | `Exec/Program.lean:75-96` | 8 (simple, fieldLeField, sumEquals, sumEqualsAcross, fieldDeltaInRange, allowedTransitions, anyOf, boundDelta) | `evalConstraint` (`:126`) | **predicate** |
| `RecordProgram` | `Exec/Program.lean:194-203` | 4 (none/predicate/cases/circuit) + `TransitionGuard` dispatch (`:149`) | `RecordProgram.admits` (`:209`) | **predicate** |
| `SlotCaveat` | `Exec/RecordKernel.lean:81-112` | 7 (immutable/monotonicSeq/monotonic/writeOnce/senderAuthorized/boundedBy/**admitTable**) | `SlotCaveat.eval` (`:129`) via `stateStepGuarded` (`EffectsState.lean:258`) | **predicate** |
| `Guard` | `Exec/CellProgram.lean:39-55` | 8 (tt/ff/authorized/amountLe/reserveSrc/selfOnly/and/or) | `Guard.eval` (`:59`) | **predicate** |
| `StateConstraintGuard` (catalog) | `CatalogInstances.lean:40-176` | ~29 derived smart-ctors over `Spec.Guard` | the `catalog` codegen | **predicate** |

Key architectural facts the design must respect:

1. **The two real surfaces are forked.** `Exec/Program.lean`'s `StateConstraint` (name-keyed over
   `Value` records, the developer eDSL target via `DSL.lean`) and `RecordKernel.lean`'s `SlotCaveat`
   (the EXECUTOR-enforced per-slot caveat consulted by `stateStepGuarded`) are **two transcriptions of
   the same dregg1 `cell/src/program.rs` catalog** that have drifted (`SlotCaveat` has 7 arms;
   `StateConstraint` has ~17 distinct shapes; `CatalogInstances` has ~29). Only `SlotCaveat` is wired
   into `stateStepGuarded` field writes; `StateConstraint`/`RecordProgram` is the richer language but
   is enforced only in the `recExec`/`RecordCell` replay path, NOT in the live `setFieldA` executor
   leg. This fork is the single biggest ergonomics tax.

2. **Cell programs are PREDICATES, by deliberate design.** `CellProgram.lean:9-12`: "A program can
   only ever *tighten* `exec`, never bypass it." The whole soundness story (`denote_eq_exec_on_success`
   `:101`, `denote_conserves` `:116`, `stateStepGuarded_eq` `EffectsState.lean:269`) rests on the gate
   being a *domain restrictor* that commits the **identical** kernel post-state. This is load-bearing
   and must not be weakened (see §C).

3. **A lattice/DAG primitive ALREADY EXISTS but is ORPHANED.** `Authority/ClearanceGraph.lean` has a
   full reflexive-transitive `Dominates` relation (`:37`), a decidable `dominatesD` (`:53`) PROVED
   sound (`dominates_of_dominatesD` `:92`), `mayRead` (`:100`) and conjunctive `needsAll` (`:104`). It
   is used by `Apps/CompartmentWorkflowMandate` but is **not reachable from any `StateConstraint`
   constructor** — the predicate language cannot say "this transition requires clearance ≥ ℓ". This is
   the cheapest high-value win in the whole doc (the hard proof is done).

---

## A. The stodginess diagnosis (per language)

### A.1 Predicate / cell-program language

**STODGY-BUT-SOUND gaps (the memory-flags ember named):**

- **No allowlist / set-membership over field VALUES.** You can write `allowedTransitions f [(a,b),…]`
  (`Program.lean:88`) — a finite `(old,new)` *pair* table — but you cannot write "`new[role] ∈
  {admin, editor, viewer}`" as a one-sided value allowlist. The `SlotCaveat.admitTable`
  (`RecordKernel.lean:111`) is the executor-side analog but is *also* a pair-table, not a value set,
  and is hand-baked (`a mandate computes this table ONCE`, `:108`). **Blocks:** a nameservice/role
  cell that admits any value drawn from a published vocabulary without enumerating every transition.

- **No prefix / string-structure predicate.** Fields read as `Int` scalars only (`Value.scalar`
  `Program.lean:33`); there is no `prefixOf`/`hasPrefix` over `Value.sym` names. **Blocks:** "a DNS
  subdomain may only be registered under a namespace the actor owns" (prefix containment) — the
  canonical nameservice policy. This is the one the Rust datalog *does* express (`feature_glob`,
  `datalog_verify.rs:1398`) but the cell-program language cannot.

- **No clearance / lattice compare.** `ClearanceGraph.dominatesD` exists and is proved
  (`ClearanceGraph.lean:53,92`) but no `StateConstraint` constructor invokes it. **Blocks (ember's
  example):** SGM clearance mandates — "a write to slot `s` is admitted only if `actor`'s clearance
  label dominates `s`'s sensitivity label" — cannot be enforced inline by the cell program. Today this
  lives only in the app-mandate layer, OUT of the verified executor gate.

- **No DAG-reachability / prerequisite predicate.** Same `Dominates` machinery would give "this
  workflow step is admissible only if its prerequisite steps are marked done" (the CWM advance / SGM
  admit the memory calls out). **Blocks:** `cwmAdvanceM`/`sgmAdmitM` being load-bearing *in the
  executor* rather than precomputed into an `admitTable`.

- **No general arithmetic relation between fields.** `fieldLeField l r` (`:79`) gives `new[l] ≤
  new[r]`; `sumEqualsAcross` (`:84`) gives a conservation sum. But there is no `new[a] + new[b] ≤
  new[c]`, no `new[a] = k * new[b]`, no `|new[f] − old[f]| ≤ d` two-sided (the catalog's `boundDelta`
  `CatalogInstances.lean:111` is one-sided and **`StateConstraint.boundDelta` is deferred-to-`true`**,
  `Program.lean:144`). **Blocks:** AMM/price-band/exchange-rate cells; any multi-field invariant.

- **Combinators are shallow & non-uniform.** `anyOf` (`:90`) is **single-level** over
  `SimpleConstraint` only — no `allOf`, no nested `anyOf`, no negation at the `StateConstraint` level
  (`not` is `SimpleConstraint`-only, `:70`). So the predicate algebra is not a clean Boolean algebra;
  it's an ad-hoc 2-level grammar. **Blocks:** ergonomic authoring of any non-trivial policy without
  hand-desugaring.

**ENFORCEMENT-GAP (stodgy AND a real hole):**

- **`StateConstraint.boundDelta` is enforced as `true`.** `evalConstraint … | .boundDelta _ _ _ _ => true`
  (`Program.lean:144`). It is *declared* cross-cell and deferred to the JointTurn aggregate, but in the
  single-cell evaluator it admits unconditionally. Any program that relies on a `boundDelta` for safety
  has NO teeth in `recExec`/`stateStepGuarded`. This is the predicate-language twin of the coordinated-
  caveat fail-closed problem (§A.2) — except here it fails **OPEN**, which is worse. Flag for the wave:
  a `boundDelta` in a `predicate` program must fail-*closed* until the cross-cell discharge exists, OR
  be routed to the CoordinatedCaveat equalizer (`CoordinatedCaveat.lean:95`) that already exists.

### A.2 Caveat language

The caveat language is in good structural shape — better than the prompt implies. Three real layers:
- `Caveat` = `local (Ctx → Bool) | thirdParty Gateway` (`Authority/Caveat.lean:38`); a `Token` is a
  list of these admitted by meet (`Token.admits` `:71`); `attenuate_narrows` is PROVED (`:84`).
- `CaveatChain` carries the REAL HMAC fold (`foldTag` `:138`), replay-verify (`:169`), and a genuine
  de-vacuified `chain_unforgeable` reduction against the §8 `MacKernel.unforgeable` carrier (`:402`),
  with a negative collapse-tooth (`collapse_not_unforgeable` `:509`). This is exemplary, not stodgy.
- The executor gate `caveatsDischarged` (`FullForestAuth.lean:442`) meets tiered `GatedCaveat.holds`
  (`:232`) with the macaroon `chainGateG` (`:427`).

**STODGY-BUT-SOUND gaps:**

- **The local-caveat predicate is an opaque `Ctx → Bool`.** `Caveat.local (check : Ctx → Bool)`
  (`Caveat.lean:39`). It is maximally expressive but **not introspectable, not serializable, not
  circuit-emittable, and not attenuation-comparable** — you cannot decide whether one local caveat
  narrows another (the `attenuate_narrows` proof works structurally on the *list*, not on caveat
  *content*). **Blocks:** authoring caveats in a wire format, proving one caveat refines another,
  emitting a caveat into the STARK. The datalog grants (`dregg_caveats::DreggGrant`, `factset.rs:74`)
  ARE a reified caveat vocabulary (App/Service/Feature/ConfineUser/ValidityWindow/OAuthScope/Budget/
  FeatureGlob) — but they live Rust-side and are not the Lean `Caveat`. The two should converge on one
  reified caveat AST.

- **`GatedCaveat.check` is likewise opaque** (`RecChainedState → Bool`, `FullForestAuth.lean:226`).
  Same introspection gap on the executor side.

**ENFORCEMENT-GAP — now mostly CLOSED, verify before relying:**

- The tier-3 `.coordinated` (cross-cell) caveat **fail-closes** in the intra-cell gate
  (`GatedCaveat.holds … | .coordinated => false`, `FullForestAuth.lean:234`). The prompt flags this as
  "not executed". It now HAS a positive discharge path: `CoordinatedCaveat.dischargeCoordinated`
  (`CoordinatedCaveat.lean:95`) routes it to the proved atomic-snapshot equalizer
  `jointApplyCaveated`, with `coordinated_discharge_sound` (`:111`) and `coordinated_no_toctou`
  (`:123`) PROVED. **But** the two are not yet welded: the *forest gate* still returns `false` on
  `.coordinated`; only a separately-invoked bilateral turn uses the equalizer. The stodginess is that
  a developer cannot write a single coordinated caveat and have the standard `execFullForestG` path
  discharge it — they must hand-route to the joint-turn API. Wave item: wire `caveatsDischarged` to
  call `dischargeCoordinated` when the node is part of a bilateral turn (design in §B.2).

### A.3 Datalog authorization

**Lean coverage: NONE.** There is no Lean model of the datalog semantics. The entire authorization
datalog lives in Rust: `token/src/datalog_verify.rs` (the ~21-rule policy `full_policy()` `:317`),
`token/src/factset.rs` (`grant_to_facts` `:74`), `dregg-trace` (the `Evaluator`/`Rule`/`Atom`/`Check`
types). The Lean `Authorization`/`Token` catalog (`CatalogInstances.lean §2`) models the *credential
kinds* (signature/proof/bearer/token/…) as verify-seam guards, but **not** the datalog evaluation that
`Authorization::Token` actually runs. So the "ground-truth verification semantics"
(`datalog_verify.rs:2`) is UNVERIFIED.

**STODGY (ergonomics) gaps in the Rust datalog itself:**

- **The policy is a hand-built fixed rule set, not user-authored.** `full_policy()` returns 21
  hardcoded `Rule`s (`:317-817`), heavily duplicated across the temporal cross-product (Rules 10-18 are
  the same 3 rules × {valid_until-only, valid_after-only, both-window}). Adding a new authorization
  *dimension* (a new grant kind) means hand-writing another rule family + reserving predicates
  (`RESERVED_PREDICATES` `:830`). There is no surface for an app to express its OWN datalog policy.

- **Negation is faked as a pre-pass.** "deny checks… NEGATIVE constraints… awkward in a pure-positive
  Datalog… handled as pre-checks" (`datalog_verify.rs:1232-1250`). Time/user/oauth/feature/budget are
  imperative Rust `if` blocks (`pre_evaluation_deny_checks` `:1251`), explicitly noted as "semantically
  equivalent to… stratified Datalog with negation" but NOT actually that. So the language has no
  real stratified negation; least-privilege is enforced by Rust control flow (`:1507`).

- **No recursion.** The evaluator is invoked once (or once-per-atomic-action, `:198`); no rule head
  feeds another rule's body across iterations beyond the single `action_allowed` expansion. Delegation
  *depth* (biscuit-style "this token may delegate, the child may delegate, …") is not expressed as a
  recursive datalog rule; it lives in the macaroon HMAC chain instead.

- **Awkward to author.** Building a grant means: pick a `CAV_*` type id, msgpack-encode a tuple
  (`encode_name_actions`), intern symbols, emit facts (`factset.rs:74`). There is no readable DSL; the
  policy and the fact-encoding are two separate hand-maintained tables that must agree
  (`RESERVED_PREDICATES` must list every engine predicate, `:830`).

---

## B. The less-stodgy target (concrete designs)

Design principle throughout: **a small core of orthogonal, introspectable combinators** that the old
corpora embed into as a *no-op extension*, so existing proofs LIFT (see §D). Prefer ONE reified AST
per language over parallel forks.

### B.1 A `StateConstraint` ALGEBRA (the predicate language)

Unify the forked surfaces onto ONE extended catalog and a clean Boolean algebra. Two parts:

**(i) A clean atom set — add the missing memory-flags as ATOMS that read `(old,new)`:**

```lean
inductive Atom where               -- replaces / extends SimpleConstraint
  -- existing (unchanged, embed verbatim):
  | fieldEquals (f : FieldName) (v : Int)
  | fieldGe | fieldLe | immutable | writeOnce | monotonic | strictMono | fieldDelta   -- as today
  -- NEW value-set / structure atoms:
  | memberOf      (f : FieldName) (set : List Int)              -- new[f] ∈ set   (allowlist)
  | prefixOf      (f : FieldName) (prefix : Sym)               -- new[f] is a Sym with this prefix
  | inRangeTwoSided (f : FieldName) (lo hi : Int)              -- lo ≤ new[f] ≤ hi   (one-sided exists; add abs)
  | deltaBounded  (f : FieldName) (d : Int)                    -- |new[f] − old[f]| ≤ d   (REAL two-sided)
  -- NEW relational atoms (close the arithmetic gap):
  | affineLe      (terms : List (Int × FieldName)) (c : Int)   -- Σ kᵢ·new[fᵢ] ≤ c
  | affineEq      (terms : List (Int × FieldName)) (c : Int)   -- Σ kᵢ·new[fᵢ] = c
  -- NEW lattice / DAG atoms (REUSE the proved ClearanceGraph):
  | clearanceGe   (g : ClearanceGraph) (actorLabelField : FieldName) (boxLabel : Label)
                                                               -- dominatesD g (label-of new[field]) boxLabel
  | reachable     (g : ClearanceGraph) (fromField toLabel)     -- DAG-prereq: dominatesD g (new[from]) toLabel
```

**(ii) A uniform Boolean combinator layer** (the Heyting algebra done properly — orthogonal to atoms):

```lean
inductive Pred where
  | atom (a : Atom)
  | tt | ff
  | and  (l r : Pred)
  | or   (l r : Pred)
  | not  (p : Pred)                -- full negation at every level (not just SimpleConstraint)
  | allOf (ps : List Pred)         -- n-ary conjunction
  | anyOf (ps : List Pred)         -- n-ary disjunction (replaces the 2-level anyOf)
```

`StateConstraint` becomes `Pred`; `evalConstraint : Pred → Value → Value → Bool` is a structural fold.
The cross-slot/conservation/state-machine shapes (`fieldLeField`, `sumEquals`, `sumEqualsAcross`,
`allowedTransitions`) become *derived* `Atom`s or `affineLe`/`affineEq` instances, collapsing the ad-hoc
constructors into the affine core. **`boundDelta` (the enforcement-gap, `Program.lean:144`) becomes
`reachable`-or-coordinated and is removed as a silent-`true` arm.**

Decidability/computability is preserved (every atom is a decidable `Bool` over named-field reads). The
circuit-emit story is *improved*: `affineLe`/`affineEq` map directly to PLONK linear gates;
`memberOf` to a lookup argument (we already have lookups, see `DESIGN-lookups-plonky3-perf.md`);
`clearanceGe`/`reachable` to a precomputed reachability lookup table.

**Unify the fork:** `SlotCaveat` (`RecordKernel.lean:81`) becomes a *thin executor adapter* that holds
a `Pred` per slot (replacing the 7 hand-arms), and `stateStepGuarded`'s `caveatsAdmit`
(`EffectsState.lean:248`) evaluates that `Pred` against `(actor, old, new)`. One language, one
evaluator, enforced both in `recExec` replay AND the live `setFieldA` leg.

### B.2 A richer + reified caveat predicate set, with real coordination

**(i) Reify the local caveat.** Replace `Caveat.local (Ctx → Bool)` with `Caveat.pred (CaveatPred)`
where `CaveatPred` is a small introspectable AST over a typed request context (the union of the Rust
`DreggGrant` vocabulary + the temporal/budget/scope dimensions):

```lean
inductive CaveatPred where
  | appAction (app : Sym) (actions : ActionSet)          -- DreggGrant::App   (factset.rs:76)
  | service   (svc : Sym) (actions : ActionSet)          -- DreggGrant::Service
  | confineUser (uid : Sym) | oauthScope (s : Sym) | feature (f : Sym)
  | validAfter (t : Int) | validUntil (t : Int)          -- DreggGrant::ValidityWindow
  | budget (id : Sym) (limit : Nat)
  | featureGlob (include exclude : List Sym)
  | and | or | not (…)                                   -- closes negation-as-pre-pass (A.3)
```

`Caveat.ok` folds this AST. The payoff: (a) `attenuate_narrows` can be SHARPENED to a structural
*refinement* check on caveat content (one `CaveatPred` provably narrows another); (b) one vocabulary
shared with the datalog factset (`factset.rs:74`), killing the Rust/Lean fork; (c) caveats become
wire-serializable AND circuit-emittable. `Caveat.thirdParty` is unchanged (the await face). The opaque
`Ctx → Bool` escape hatch can be retained as `Caveat.opaque` for handwritten policies (so nothing
regresses), but the reified path becomes the default.

**(ii) Real cross-cell coordination (weld the existing equalizer).** The proved
`CoordinatedCaveat.dischargeCoordinated` (`CoordinatedCaveat.lean:95`) already gives sound, no-TOCTOU
discharge. The wave change is purely *wiring*: extend `caveatsDischarged` (`FullForestAuth.lean:442`)
so that when a node carries a `.coordinated` caveat AND the turn is a bilateral/joint turn, the gate
calls `dischargeCoordinated` on the joint snapshot instead of returning `false`. The intra-cell
fail-closed (`GatedCaveat.holds … .coordinated => false` `:234`) stays the conservative default for the
single-cell path; the joint path gets the positive discharge. No new metatheory — `coordinated_refines_
failclosed` (`CoordinatedCaveat.lean:30`) already proves the promotion never opens a hole.

### B.3 Datalog: a Lean-verified core + an authorable surface

Two independently-valuable moves:

**(i) A Lean model of the datalog evaluator** (closes the "ground-truth is unverified" gap, A.3).
Model `Fact`/`Rule`/`Atom`/`Check`/`Evaluator` as Lean datatypes and define `evaluate : List Fact →
List Rule → Request → Bool` as a fuel-bounded fixpoint (exactly the `dominatesFuel` pattern
`ClearanceGraph.lean:46`, which is the proof-of-concept that fuel-bounded datalog-shaped search is
already done-and-proved here). Prove: (a) **monotonicity** (more facts ⇒ more derivations — the
attenuation-narrows analog); (b) **soundness of the deny-pre-pass** = stratified-negation equivalence
(the claim `datalog_verify.rs:1246` ASSERTS but never proves); (c) **reserved-predicate
non-injection** (`RESERVED_PREDICATES` `:830` genuinely prevents `allow()` injection — a real security
property currently only tested). This makes `Authorization::Token` admission verified end-to-end.

**(ii) An authorable policy DSL** mirroring `DSL.lean`'s `dregg_program` eDSL. A `datalog_policy { … }`
block elaborating to `List Rule`, so apps express their own positive-authorization rules instead of
forking `full_policy()`. The 21-rule temporal cross-product (`:474-815`) collapses to ONE rule family
parameterized over an optional `[validAfter, validUntil]` window, removing the 6× duplication.

---

## C. The predicate → function question (the "expand outward" steer)

**Recommendation: keep cell programs PREDICATES at the kernel-commit boundary; expand outward by adding
EXPRESSIVE predicate atoms (§B.1) and a SEPARATE, predicate-checked "derive" facet — never a raw
compute-new that bypasses the conservation/authority gate.**

Why predicates must stay the commit gate: the entire soundness tower is
`gate ⇒ commit-the-identical-kernel-post-state`:
`denote_eq_exec_on_success` (`CellProgram.lean:101`), `denote_conserves` (`:116`),
`stateStepGuarded_eq` (`EffectsState.lean:269`), and the gated-forest `eraseG` bridge
(`FullForestAuth.lean:303`, every conservation/no-amplify theorem re-used via erasure). If a cell
program could COMPUTE the new state, the post-state would no longer be `exec`'s/`stateStep`'s, and
**every one of those lemmas breaks** — you would be re-proving conservation/authority/noninterference
for an arbitrary user function. That is exactly the "launder vacuity / degrade a guarantee" trap to
reject.

But the steer is right that "just inspect (old,new)" is too narrow. The genuinely-more-useful, still-
sound move is a **guarded transformer = (predicate, deterministic derive) pair** where the derive is
itself *checked by a predicate*: the executor computes a candidate `new' = derive(old, args)`, then
runs the SAME admission predicate on `(old, new')`. The cell still commits only states the predicate
admits — so conservation/authority lift verbatim (the post-state is still a predicate-admitted state) —
but the developer gets compute-new ergonomics (no need to supply `new` and have it checked; the cell
derives it). This is the lens/comodel `get/put/guard` shape already sketched in the dregg4 vision
(`MEMORY` "turn = guarded comodel/lens"). Concretely:

```lean
structure GuardedTransformer where
  derive : Value → Args → Value         -- compute candidate new (deterministic, total)
  guard  : Pred                         -- the SAME predicate language admits (old, derived)
-- commit iff guard.eval old (derive old args) ; post-state = derive old args
```

Soundness: `commit ⇒ guard.eval old new' = true`, so any theorem of the form "admitted transitions
preserve P" lifts unchanged. The new proof obligation is ONLY `derive` totality + determinism (trivial
for a closed grammar of derives: setField/addField/swap-fields/applyAffine). **This buys the "outward"
expansion without touching the conservation keystone.** Recommend building it AFTER §B.1 (it reuses the
extended `Pred`). For pure conserved-quantity moves (transfer/escrow) the kernel `recKExec`
(`RecordKernel.lean:621`) already IS the derive-with-guard; this generalizes that pattern to app slots.

---

## D. Proof-repair scope (the load-bearing part)

Ordered LEAST-disruptive first. The governing trick: **every new constructor is a no-op extension of an
existing inductive, so old corpora don't mention it and old proofs LIFT by `simp`/structural-recursion
coverage; the only NEW proofs are the new arms' admit-characterizations.** No extension below requires
or permits a `:=True` shortcut.

**Blast radius of the predicate language** (consumers of `evalSimple`/`evalConstraint`/`RecordProgram`,
17 files): `Exec/{Program, RecordCell, RecordCellLive, RecordKernel, EffectsState, Factory, CapInbox,
CellRuntime, CellUpgrade, PubSubTopic, RelayOperator, TurnExecutorFull}`, `DSL.lean`,
`Proof/{WP, WPCatalog}`, `Spec/FunctionalRefinement`, `Circuit/Spec/cellstatefield`.

| Stage | Extension | What BREAKS | What LIFTS | Hardness |
|---|---|---|---|---|
| **D0** | `clearanceGe` / `reachable` atom reusing `ClearanceGraph` | Nothing — new `Atom` arm; `evalSimple`/`evalConstraint` get one new match case | ALL existing programs (they don't use it); `dominates_of_dominatesD` (`ClearanceGraph.lean:92`) is the soundness lemma, already PROVED | **LOW** — the hard proof exists; just add the arm + its admit-char theorem |
| **D1** | `memberOf` / `inRangeTwoSided` / `deltaBounded` atoms | new match arms in `evalSimple` (`Program.lean:106`) + the `SlotCaveat.eval` adapter (`RecordKernel.lean:129`) | every `denote_*`/`stateStepGuarded_*` lemma (they quantify over "admitted" abstractly, not over the atom set) | **LOW** — decidable Bool atoms; admit-char by `decide` |
| **D2** | `affineLe` / `affineEq` (subsumes fieldLeField/sumEquals/sumEqualsAcross) | the 3 subsumed constructors' lemmas if you DELETE them; safe path KEEPS them as derived defns | conservation lemmas over `sumEqualsAcross` re-expressed via `affineEq` (one rewrite) | **LOW-MID** — keep old ctors as `def`s = zero break; collapse later |
| **D3** | Uniform `Pred` Boolean layer (`allOf`/nested `anyOf`/top-level `not`) | `evalConstraint_anyOf` (`Program.lean:245`), `admits_predicate` (`:224`) restated as a fold; `DSL.lean` `macro_rules` (`:119`) extended | `denote`/`admits` keystones (they fold over the list; the fold generalizes) | **MID** — structural-recursion termination + the Heyting laws (`evalSimple_not_not` `:240` generalizes) |
| **D4** | Fix `boundDelta` enforcement-gap: silent-`true` → fail-closed/route-to-coordinated | `evalConstraint … boundDelta => true` (`Program.lean:144`) changes truth value; any `#eval`/`#guard` asserting it admits | nothing relies on it admitting (it's a hole); CoordinatedCaveat discharge (`CoordinatedCaveat.lean:95`) is the target | **MID** — must check no app silently depended on the open behavior; this is a soundness FIX |
| **D5** | Unify `SlotCaveat` ⟶ `Pred` adapter; `caveatsAdmit` evaluates `Pred` | `caveatsAdmit` (`EffectsState.lean:248`), `SlotCaveat.eval`/`.bornFresh`/`.field` (`RecordKernel.lean:115-151`), `FactoryEntry.conforms` (`:187`), `stateStepGuarded_admits` (`EffectsState.lean:280`) | `stateStepGuarded_eq` (`:269`) — UNCHANGED (post-state still `stateStep`'s); all forward-sim lifts | **MID-HIGH** — touches the executor-enforced surface; the `_eq` lemma is the safety net |
| **D6** | Reify `Caveat.pred` (CaveatPred AST), keep `Caveat.opaque` | `Caveat.ok` (`Caveat.lean:47`), `Token.admits` (`:71`), `chainToken` (`CaveatChain.lean:256`), `GatedCaveat.check` (`FullForestAuth.lean:226`) | `attenuate_narrows` (`Caveat.lean:84`), `append_narrows` (`CaveatChain.lean:230`), `chain_unforgeable` (`:402`) — all structural over the list, AST-agnostic | **MID** — add an arm, fold it; the narrowing proofs don't inspect content |
| **D7** | Weld coordinated discharge into `caveatsDischarged` | `caveatsDischarged` (`FullForestAuth.lean:442`), `gateOK` (`:461`), `gateOK_revoked_fails` (`:472`) | `coordinated_discharge_sound`/`_no_toctou`/`_refines_failclosed` (`CoordinatedCaveat.lean:111-130`) — all PROVED | **MID** — wiring; the math exists |
| **D8** | `GuardedTransformer` (predicate→function, §C) | nothing existing (new structure); its commit-rule is `guard.eval old (derive…)` | every "admitted ⇒ P" theorem (post-state is predicate-admitted) | **MID** — only NEW obligations: `derive` totality/determinism |
| **D9** | Lean datalog evaluator + soundness | nothing existing (greenfield Lean module modelling Rust) | `dominatesFuel` (`ClearanceGraph.lean:46`) is the fuel-fixpoint template | **HIGH** — monotonicity + stratified-negation-equiv + non-injection; this is the real research-grade proof |

**Anti-vacuity discipline (mandatory for the wave):** every new atom must ship a non-vacuity pair — a
witness it ADMITS a real transition AND a witness it REJECTS one (`by decide`), exactly as
`Program.lean:257-282` and `DSL.lean:215-323` already do. The `boundDelta` D4 fix specifically replaces
a vacuous-`true` with a teeth'd predicate; do NOT "fix" it by another `:=True` or by deleting the
constructor silently.

---

## E. Implementation plan (staged, buildable, beachhead-first)

Each stage ends GREEN with `#assert_axioms`/`#assert_namespace_axioms` clean (the repo's honesty pin,
`CatalogInstances.lean:391`). Validated-reference-first: ONE constructor end-to-end before fan-out.

**BEACHHEAD (do this first, alone) — `clearanceGe` end-to-end (D0).** Highest value/effort ratio: the
hard proof (`dominates_of_dominatesD`) is DONE and orphaned; wiring it in is a few hours and immediately
makes SGM clearance mandates enforceable INLINE by the executor (ember's named blocked policy).
1. Add `Atom.clearanceGe` to `SimpleConstraint`/`Pred` (`Program.lean:51`).
2. Extend `evalSimple` (`:106`) with the arm calling `ClearanceGraph.dominatesD`.
3. Prove `evalSimple_clearanceGe_iff` (admit-char) + non-vacuity admit/reject `#guard`s.
4. Add the `SlotCaveat` adapter arm + extend `caveatsAdmit` (`EffectsState.lean:248`) so the LIVE
   `setFieldA` leg enforces it; confirm `stateStepGuarded_eq` still closes by `rfl`/existing proof.
5. Ship ONE real policy: a clearance-gated nameservice/SGM cell whose write is admitted only when the
   actor's clearance label dominates the slot's sensitivity — `by decide` admit + `by decide` reject.
   This is the "a real policy that now works" deliverable.

**Then fan out (least-disruptive order):**
- **Stage 1 (D1):** value-set/range/two-sided-delta atoms + the `DSL.lean` surface syntax. Quick wins.
- **Stage 2 (D2):** `affineLe`/`affineEq`; re-express `sumEqualsAcross` (keep old ctors as derived).
- **Stage 3 (D3):** the uniform `Pred` Boolean layer; migrate `DSL.lean` `macro_rules`. Ergonomics jump.
- **Stage 4 (D4):** the `boundDelta` soundness FIX (silent-`true` → fail-closed). Gated on a sweep that
  no app relied on the open behavior (grep app corpora).
- **Stage 5 (D5):** unify `SlotCaveat` onto `Pred` — one language, enforced live + in replay.
- **Stage 6 (D6 + D7):** reify `Caveat.pred`; weld coordinated discharge into the forest gate.
- **Stage 7 (D8):** `GuardedTransformer` (predicate→function expand-outward) over the extended `Pred`.
- **Stage 8 (D9):** the Lean datalog evaluator + soundness (research-grade; parallelizable, independent).

**Sequencing note:** D0–D5 are the predicate-language spine and should land before D6–D7 (caveat) so
the two surfaces converge on one `Pred`/`CaveatPred` vocabulary rather than re-forking. D9 (datalog) is
independent and can run as a parallel workflow from the start.

---

## Appendix — one-line orientation for the implementer

- Predicate atoms + evaluator: `Exec/Program.lean` (`SimpleConstraint:51`, `evalSimple:106`,
  `StateConstraint:75`, `evalConstraint:126`, the **`boundDelta:144` HOLE**).
- Executor enforcement of slot caveats: `Exec/EffectsState.lean` (`caveatsAdmit:248`,
  `stateStepGuarded:258`, the safety-net `stateStepGuarded_eq:269`).
- The orphaned lattice/DAG primitive to reuse: `Authority/ClearanceGraph.lean`
  (`dominatesD:53`, proved sound `dominates_of_dominatesD:92`).
- Caveat algebra: `Authority/Caveat.lean` (opaque `local:39`, `attenuate_narrows:84`);
  HMAC chain `Authority/CaveatChain.lean` (`chain_unforgeable:402`).
- Forest gate: `Exec/FullForestAuth.lean` (`GatedCaveat:221`, `caveatsDischarged:442`, `gateOK:461`).
- Coordinated discharge (already proved, needs welding): `Exec/CoordinatedCaveat.lean:95-130`.
- Datalog (Rust-only, to model): `token/src/datalog_verify.rs` (`full_policy:317`,
  `pre_evaluation_deny_checks:1251`), `token/src/factset.rs` (`grant_to_facts:74`).
- The eDSL to mirror for new surfaces: `Dregg2/DSL.lean` (`dregg_program:166`).
