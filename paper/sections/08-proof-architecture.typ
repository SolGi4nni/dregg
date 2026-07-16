// =============================================================================
// Section 8: The proof architecture
// =============================================================================

#import "../defs.typ": lean
= The proof architecture: ARGUS and path preservation <sec-proof-arch>

@sec-proofs states what a proof says: a verifier holding one root learns the
whole history. This section is how that claim survives change in the proof
system itself. The arithmetization is not frozen --- the field, the
commitment layout, and the per-effect circuits evolve --- and a verified
substrate has to guarantee that evolution never opens a gap the @sec-intro
adversary, the server that ran the protocol wrong, can slip through. The
discipline that guarantees it has three parts: the circuit *witnesses correct
evolution* (ARGUS), the circuit shape *rotates* under proof, and every finalized
turn *stays proven across shapes*.

== ARGUS: the circuit witnesses correct evolution

The design principle of the proof layer is that the proof is not an external
certificate *about* a run but an internal witness *of the protocol's correct
evolution*. A light client that checks one aggregate root is fooled exactly when
it can be convinced of a transition the kernel would not have produced; the
circuit is built so that no such proof exists. This is the negation @sec-intro
names --- a history that verifies but never happened --- and the circuit
architecture is derived from ruling it out, not from matching whatever the
executor's host implementation happened to compute.

Unfoolability decomposes into three properties the per-turn proof must have
jointly, and each is a discharged obligation:

- *non-malleable* --- the proof binds every guarantee-relevant field of the
  transition, so it cannot be re-pointed at a different pre-state, post-state,
  receipt log, or system root. The state-commitment binding below is exactly this
  property made a fact of the arithmetized field
  (#lean("RotationLayout.rotatedCommit_binds")).
- *omits no precondition* --- authority, availability (freshness against the
  nullifier set), freshness, and non-amplification are *in-circuit conjuncts*, not
  side conditions the prover may quietly skip. A verifying proof exists only if
  every one of them held; an amplifying grant or a replayed spend forces the
  binding predicate false (#lean("EffectsAuthority.amplifying_grant_rejected"),
  #lean("noteSpendStmt_replay_rejected")). A forgotten precondition is the
  classic way a verified system is fooled, so the circuit makes forgetting one
  unrepresentable.
- *refines the protocol* --- the property the proof attests is the kernel's own
  semantics, derived from the unfoolability requirement, never a lossy
  re-encoding a host implementation happened to produce. The two readings of one
  descriptor (below) are what make this a theorem rather than a discipline.

Concretely, ARGUS is the two-readings discipline of @sec-proofs carried to every
effect. Each kernel statement is a descriptor; the executor reading (`interp`)
and the circuit reading (`compile`) are obtained from the *same* descriptor, and
the receipt-level weld #lean("Argus.Receipt.argus_circuit_executor_receipts_agree")
proves they cannot disagree. Because the circuit reading is generated, not
hand-authored, there is no second source of truth to drift: a coverage gap is
closed by emitting from a proved Lean module. The per-effect statements live in
`Circuit/Argus/Effects/`; the aggregate realization is the Argus strand
(#lean("Argus.Aggregate.argus_strand_light_client"),
#lean("Argus.Aggregate.tampered_argus_strand_rejected")).

== The state commitment binds the whole post-state

The fidelity floor is the per-turn state commitment: the field from which the
proof's pre- and post-state are read. It is a chained Poseidon2 sponge over a
fixed limb layout --- the cells root, the application registers, the capability /
nullifier / heap map roots, and the lifecycle, epoch, and height fields --- so
that, under permutation collision-resistance, equal commitments imply equal
state in *every* limb, including the frame the step did not touch
(#lean("RotationLayout.rotatedCommit_binds")). The binding is non-vacuous limb by
limb: tampering with the heap root (#lean("RotationLayout.rotatedCommit_binds_heapRoot")),
a named register (#lean("RotationLayout.rotatedCommit_binds_named_field")), or the
receipt log --- by omission, reorder, extension, or truncation
(#lean("RotationLayout.rotatedCommit_binds_log"), composing
#lean("MMR.mroot_injective")) --- produces a distinct commitment. The
chained absorption itself is the circuit-side construction `wireCommit`, proved
collision-resistant against the same floor
(#lean("EffectVmEmitRotation.wireCommit_binds")). This is the @sec-proofs
"receipt binds the whole post-state" made a property of the arithmetized field,
so a proof cannot certify a post-state that differs anywhere from the one the
executor produced.

== Rotation: the circuit shape evolves under proof

The commitment layout and the per-effect circuit cohort are not fixed constants;
they *rotate*. A rotation is a coordinated regeneration of the arithmetization
--- the limb layout, the per-effect descriptors, and the verifying key together
--- carried out under a single discipline: the rotated shape is proven to enforce
the same semantics as the shape it replaces *before* any verifying key changes.
The mechanism is one parametric transformation, #lean("EffectVmEmitRotationV3.rotateV3"),
that appends the rotated commitment block to any per-effect descriptor, and two
keystones that make the rotation safe to land:

- *equivalent enforcement* --- a rotated descriptor forces exactly the
  pre-rotation per-effect satisfaction semantics, so rotating adds no new
  per-effect proof obligation
  (#lean("EffectVmEmitRotationV3.rotateV3_satisfiedVm_v1"));
- *equal published state* --- a pre-rotation and a rotated witness of the same
  effect publish the same state (cells root, registers, map roots, nullifiers),
  so the rotation cannot change what a turn means
  (#lean("EffectVmEmitRotationV3.rotV3_binds_published")).

Rotation is a *staged-additive-then-cutover* operation: the rotated cohort is
generated and proven beside the live path, with the legacy path byte-identical
and its drift guards green, and the verifying-key change is a single deliberate
step that makes the rotated shape live. The economics are measured before that
step, not assumed: a real multi-operation heap turn proves at a measured size,
and the always-paid register limbs versus the metered heap limbs are priced from
that measurement. The cell-side and circuit-side state shapes are kept identical
by a differential that takes a real turn's post-state through both the cell's
commitment and the circuit's trace and asserts they agree, with anti-tamper teeth.

== Path preservation: every finalized turn stays proven

Rotation raises a sharper obligation than "the new shape is sound": *every turn
the system has ever finalized must remain provable on the live path, including
turns whose shape is heterogeneous.* A single turn may exercise several distinct
effect kinds, and an actor's cell may carry arbitrary fields and capabilities ---
shapes a single monolithic per-effect leg does not cover. Path preservation is
the composition that covers them without authoring a new circuit: a heterogeneous
turn is split into maximal *cohort-runs* --- contiguous spans whose effects all
resolve to one rotated descriptor --- each cohort-run proves through its
Lean-emitted descriptor, and the legs are *chained* by an adjacency check, each
run's post-commitment equal to the next run's pre-commitment. A homogeneous turn
is one run, byte-identical to the single-leg case; the chain only generalizes it.

The composition is verifier-side arithmetic over the existing Lean-emitted
descriptors --- it authors no new constraint (the @sec-proofs law). This is the
load-bearing soundness point, so it is worth stating exactly why it is clean: each
cohort-run is homogeneous and therefore proves through one of the rotated cohort
descriptors already emitted from Lean, whose per-leg binding pins that leg's
pre- and post-state (#lean("EffectVmEmitRotationV3.rotV3_binds_published")); the
split is a pure fold over the descriptor resolver; and the only new verifier
obligation is *equality of two already-proven public inputs* --- one leg's
post-commitment against the next leg's pre-commitment --- a chain break being a
typed rejection. The verifier also pins each leg's effect span by re-deriving the
cohort split from the turn's effects (so a prover cannot substitute a
different-but-chaining effect multiset) and sums the per-leg net deltas to the
turn's declared total, so conservation rides the chain. Comparing independently
proven public inputs introduces no new statement about what a transition *means*,
which is why the composition needs Lean only for review --- confirming each
per-cohort theorem binds first-row-pre and last-row-post, which a multi-row run
already satisfies --- and not a new emitted circuit.

The result is the @sec-proofs light-client guarantee made *robust to the proof
system's own evolution*: the aggregate a light client checks
(#lean("RecursiveAggregation.light_client_verifies_whole_history")) folds the
rotated, chained legs, so no finalized turn need fall back to an unverified path on
account of its shape.

#emph[Scope.] The rotated cohort covers every live effect kind. The resolver
that names a descriptor for an effect returns one for every selector the wire
enum carries; its fail-closed arm is reached only by the structural no-op and by
unknown selectors, and a registry test pins the resolver's output to the exact
membership of the Lean-emitted registry
(`residue_is_empty_every_live_selector_resolves` in
`circuit/src/effect_vm/trace_rotated.rs`). The two effect kinds that formerly
resolved outside the cohort now resolve inside it. Capability revocation proves
through its rotated descriptor, a held-membership map read composed with a
zero-value removal write; separately, the revocation-freshness circuit --- the
last deployed first-party circuit whose constraints were authored in Rust --- is
emitted from a proved Lean module (`Circuit/Emit/NonRevocationAdjacencyEmit`) as
a depth-general composition of a membership-adjacency half and an ordering half,
with the emitted bytes pinned to the committed golden the prover loads. The
custom effect --- a cell program whose domain constraints are proven in an
external sub-proof --- resolves to a descriptor carrying the
recursive-proof-binding constraint kind (#lean("DescriptorIR2.ProofBind")): the
row's proof-commitment and program-key columns are published as public inputs
(#lean("EffectVmEmitRotationV3.customPiExposure")), and the per-turn fold ties
them to the folded sub-proof leaf. That binding is a theorem on the same floor
as every other effect --- a verifying aggregate forces the published commitment
to be backed by a verifying sub-proof whose program key is uniquely determined,
and a forged commitment with no backing sub-proof makes the aggregate
unsatisfiable (#lean("CustomBindingFromFold.custom_binding_from_fold"),
#lean("CustomBindingFromFold.custom_companion_grounded")).

There is no unproven path beneath this coverage. The hand-rolled STARK engine is
deleted from the tree; the descriptor prover over the byte-pinned registry is
the only production proving path, and a resolver miss is a typed refusal, never
a route to a hand-authored circuit. A repository gate keeps the coverage claim
from rotting: `circuit-prove/tests/law1_enforcement_gate.rs` scans every source
file of the two circuit crates for constraint algebra in each of the three
dialects it can take --- symbolic builder calls, evaluation closures, and
constraint-expression data --- against a frozen per-file baseline. A new file
containing constraint algebra fails the build; a listed file that grows fails
the build; shrinking is always allowed. The baseline's remaining entries are
classified rather than amnestied: interpreters that evaluate Lean-emitted
constraints, a proved-faithful encoding lowering, drift-detector twins the
emitted paths check against at build time, and the user-facing predicate
grammar. A hand-authored constraint therefore cannot re-enter a deployed
circuit without turning the build red.
