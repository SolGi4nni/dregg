# Proof-integrity repair — request for pointed recommendations

You are auditing a large Lean 4 (+ mathlib) verification effort and recommending how to make it
prove something *meaningful*. Be concrete and pointed; assume a sophisticated reader; do not give
generic "write good specs" advice. Cite the failure modes below and propose mechanizable fixes.

## The system (dregg)

A capability-secure protocol verified in Lean 4. Four layers, already mutually bound:
- **Concrete kernel** (`Dregg2.Exec.*`): the executor. Effects (Transfer / SetField / Mint / Burn /
  GrantCapability / NoteSpend / lifecycle …) are state transitions over a `RecordKernelState`
  (per-asset balances, capability c-lists, lifecycle, nullifiers). A step is a partial function
  `k → Option k'` whose `some`-condition is a "gate" (authority + preconditions).
- **STARK circuit** (`Dregg2.Circuit.*`): per-effect AIR descriptors, with a refinement obligation
  `descriptorRefines S hash R kstep := Satisfied2 <descriptor> → StateDecode → kstep pre post`, composed
  into a light-client-unfoolability apex (`verifyBatch accept ⟹ ∃ genuine kernel transition`).
- **Abstract spec** (`Metatheory/*`): a categorical/dynamics layer that `import Dregg2.Laws` and is
  proven to *be* the concrete seam. It fixes (these are real, proven theorems):
  - conservation as a lax-monoidal functor `measure : C ⥤ Discrete M` — `measure_unit`, `measure_tensor`,
    `no_free_copy` (a counted resource has no diagonal), `no_free_discard` (a discard forces measure 0).
  - a verb meta-law: a `Verb` is `Admission × Footprint`, and `Fires v w := Admits adm w ∧ Footprint-Fpu v`.
  - authority as non-forgeable production: `AuthorizedProduction held produced`, `noforge_closure`.
  - a `Predicate ⊣ Witness` Galois seam (= `Dregg2.Laws.predicate_witness_galois`).
- **Userspace verifier** (Rust): checks conservation + authority over a transaction forest.

## The problem: systematic circularity (an internal audit found this)

A large class of theorems are GREEN but constrain NOTHING. Concrete, representative instances:

1. **Decorative authority proofs (~60–103 theorems).** Example:
   ```
   theorem issuerBurnK_authorized (h : issuerBurnK k actor a src amt = some k') :
       actor = src ∨ mintAuthorizedB k.caps actor (issuerOf a) = true := by
     unfold issuerBurnK at h; by_cases hg : (<the gate>) ; exact hg.1
   ```
   The conclusion is a *projection of the def's own gate*. It stays green for ANY gate. We recently
   relaxed the burn admission to a law-violating form (a value-move with no admission) and **lake
   stayed fully green** — no proof reds, because the only "authority" theorem re-reads whatever gate
   we write. This includes the LIVE executor's whole per-effect authority shelf (`execFullA_*A_authorized`,
   ~16 effects) and the supply (`recKBurnAsset_authorized`, `recKMintAsset_authorized`).
2. **Circular specs (spec ≡ implementation gate).** `exercise_authorized` concludes
   `Spec.execGraph caps actor target` — looks like refinement to a spec. But `execGraph_eq_any := rfl`:
   the "spec graph" is *definitionally* the executor step's own `.any confersEdgeTo` gate. So
   `impl ⟺ spec` is `rfl`-trivial; the spec adds no constraint.
3. **Weak "mitigations" that are also circular.** Fail-closed teeth `¬gate → step = none` are the
   gate's *negation* (still self-referential). `*_iff_spec` equivalences are vacuous when the spec is
   `:= gate`. `*_floor_sound := K.verify_sound` just returns a typeclass field.

We must NOT assume the remaining "genuine-looking" proofs (conservation measures; the circuit
`descriptorRefines` rungs) are meaningful either: a `descriptorRefines` only counts if the *kernel
step it targets* is an honest model of the intended behavior, and a conservation `measure` only counts
if the measure is non-trivial and the moves it ranges over are the real ones. The audit's
"genuine/decorative" split was too coarse; we need a sharper, falsifiable criterion.

## What we need

**Real proofs over real specs.** Specifications that:
- (a) are defined **independently of the implementation** — capturing the intended security/correctness
  property at an abstract level (we have a candidate independent layer in `Metatheory`),
- (b) are **non-vacuous** — not satisfiable by a degenerate or wrong implementation; demonstrably
  true at some inputs and FALSE at others,
- (c) the implementation (kernel + circuit + verifier) provably **refines**, such that a *wrong*
  implementation **fails** the proof.

The verification must be **falsifiable and load-bearing**, not green-by-construction.

## Give pointed recommendations on

1. **A criterion.** A rigorous, ideally mechanizable criterion separating a load-bearing proof over a
   meaningful spec from a decorative/circular/vacuous one — addressing BOTH "is the proof falsifiable
   by a wrong impl" AND "is the spec independent + non-vacuous + intent-capturing." How would you
   formalize "the spec is not definitionally derived from the implementation"? How do you detect a
   measure/spec that is trivially preserved?
2. **Detection at scale.** Concrete methods over a large Lean 4 corpus: (i) structural — flag a spec
   that is `rfl`/`def`-unfoldable to the impl gate, and a proof that `unfold`s the impl and projects a
   hypothesis; (ii) **mutation testing** — mutate the implementation's gate (weaken/remove a conjunct)
   and require the proof to RED; staying green ⇒ decorative. Recommend a workable Lean-4 mutation-testing
   harness (what to mutate, how to drive `lake`/`lean` over mutants, how to keep it cheap), and a
   non-vacuity check (e.g. machine-checked witnesses that the spec is satisfiable AND refutable).
3. **Restructuring methodology.** How to rebuild so specs are independent + meaningful, leveraging the
   existing `Metatheory` abstract layer (the verb meta-law `Fires = Admission ∧ Fpu`, the conservation
   functor, non-forgeable `AuthorizedProduction`) as the spec the kernel must refine. The right
   hierarchy (abstract law ⊐ kernel refinement ⊐ circuit refinement ⊐ verifier) and where each
   obligation lives. Concretely for the worst layer (authority/admission): what does a *genuine*
   `*_authorized` look like — i.e. how do you state it so that a "missing-admission" implementation is
   **unprovable**, not auto-tracked? (We believe the answer is: refine the impl admission to the abstract
   `Admits`/`AuthorizedProduction` so the meta-law is the definition of a valid step — but want your
   sharper formulation and the pitfalls.)
4. **Repair plan.** A prioritized sequence (security-critical authority/admission first), with the
   supply/burn admission — currently decorative AND demonstrably law-violable — as the exemplar.
5. **Regression prevention.** A discipline/CI to keep proofs load-bearing going forward: mutation
   testing in CI; a lint forbidding `exact h.1`-off-own-gate and `spec := gate`/`rfl`-equalities; a
   requirement that each `*_sound`/`*_authorized` cite an independent spec and a non-vacuity witness.
   What's the cheapest high-signal gate to add first?

Constraints: Lean 4 + mathlib; do not propose abandoning the existing apparatus — the `Metatheory`
abstract layer and the light-client apex are assets to *anchor* against. The deliverable is a concrete
methodology + the first three things to do, not a survey.
