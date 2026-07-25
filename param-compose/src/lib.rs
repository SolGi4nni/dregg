//! # The general parameter-composition verifier
//!
//! The Custom-VK AIR that a Braid resolver — and every future creature, entity, item, or
//! institution system — lives in. It proves a **bounded nonlinear composition over typed
//! projections**, and it contains no game.
//!
//! This is the §9.3 component of `docs/design/HOARDLIGHT-LIVING-WORLD.md`, built to the
//! shape that doc demands:
//!
//! > The resonance proof will become the most reused and most tempting-to-hardcode
//! > component. Its public inputs must be a bounded list of typed projections plus roots
//! > and roles — not a fixed Rust struct whose field count encodes Stage 1.
//!
//! ## What it proves
//!
//! > Given the canonical ordered list of typed projections committed by `subjects_root`,
//! > and the versioned law committed by `ruleset_root`, the value committed by
//! > `outcome_commitment` is the composition that law licenses — and the per-term
//! > contributions committed by `explanation_root` are the terms it is made of.
//!
//! `outcome = Σ_linear coeff · P[role].params[i] + Σ_knots coeff · P[a].params[i] · P[b].params[j]`
//!
//! The **knots** are the point. `AffineLe`/`AffineEq` — the declarative StateConstraint
//! vocabulary — are LINEAR: nothing in them multiplies two state values. A knot is a
//! degree-3 gate `coeff · val_a · val_b` over two subjects' params, so a nonlinear
//! composition MUST be a Custom VK with a hand-written AIR. That is settled, and this is
//! that AIR in its general form.
//!
//! ## Why it is general (what a new game costs)
//!
//! | new thing | cost |
//! |---|---|
//! | new balance numbers | a new `ruleset_root` — data |
//! | new roles / new role vocabulary | data (a role is an opaque `u64` the ruleset addresses) |
//! | new params, new param meanings | data (params are witnessed; `param_count` is a PI) |
//! | new knots (new nonlinear relations) | data |
//! | a whole new creature/entity/institution system | data |
//! | more subjects / params / knots than the bounds | a new [`ComposeShape`] = a new VK (a size class, like a bigger board) |
//! | **a kernel or AIR edit** | **never** |
//!
//! Nothing the emitted AIR is parameterised by is a field count, a param count, a role list,
//! or a rule table. [`ComposeShape`] carries only MAXIMA, which double as the fuel/DoS meter
//! ([`ComposeShape::hash_sites`]) — a host prices a composition from the shape alone,
//! without seeing its content.
//!
//! ## The public inputs
//!
//! See [`pi`]. `[old_commit8 ‖ new_commit8]` is the Custom-VK door's state-binding ABI
//! (`dregg_circuit::effect_vm::custom_state_binding`); the app PIs are the ABI version,
//! four counts, and the four roots. **The layout is constant in the number of subjects** —
//! `subjects_root` binds the whole canonical ordered list at ~124 bits rather than
//! spending a PI slot per subject, which is exactly the "field count encodes Stage 1"
//! cul-de-sac §9.3 forbids.
//!
//! ## The budget (measured — `tests/size.rs`)
//!
//! Against the deployed caps `MAX_TRACE_WIDTH = 1024`, `MAX_CONSTRAINT_DEGREE = 8`,
//! `MAX_PUBLIC_INPUTS = 64`. `leaf` is the EMITTED IR-v2 `trace_width` — which IS the width the
//! folded leaf carries, because the Lean family emits IR-v2 directly: there is no `CellProgram`,
//! no custom-leaf lowering step, and hence no `lane` column term. (The retired Rust AIR needed two
//! numbers; `rust` below is its historical `prog` count, kept only because the 33-column delta is
//! evidence the two objects were the same AIR — one `zero` padding column plus four 8-felt IV
//! groups that Lean replaces with literal constants in the chip tuple.)
//!
//! ```text
//!   shape                       leaf   deg  PIs  app  sites  verdict            (rust, retired)
//!   n2 p2  l1  k1                186    3    53   37     6    FITS                       219
//!   n3 p4  l3  k2                346    3    53   37     9    FITS  <- proved as a leaf   379
//!   n4 p8  l8  k6 (realistic)    770    3    53   37    18    FITS  (identity_bits=28)    803
//!   n6 p8  l12 k10              1277    3    53   37    27    EXCEEDS -> segment            —
//!   n8 p16 l16 k16              2462    3    53   37    46    EXCEEDS -> segment            —
//! ```
//!
//! Degree is **3** everywhere (cap 8) — the knot `coeff · val_a · val_b` and the
//! `sel_j · selp_p · param` read are the only cubics, so degree is never the binding
//! constraint. PIs are **53/64 (37/48 app)** and CONSTANT in every bound — growing the
//! scene never touches the layout.
//!
//! **Segmentation is NOT needed at the realistic shape — and the DEFAULT 28-bit
//! identity namespace fits, with room to spare.** The realistic shape carries a 770-column
//! leaf, 254 under the 1024 cap, and `tests/prove_fold.rs` proves that saturated shape as a
//! SINGLE foldable leaf. This was the previously-unstated price `node8` erased: the old 8-chain
//! digest paid 368 node hash sites, each costing 7 lane columns in the lowered leaf, so the
//! "999-column" realistic shape actually folded a 3575-column leaf (999 + 368×7 = 2576 lane
//! columns). One `node8` site per 8-felt block binds the same ~124 bits at zero lane cost, and the
//! digest chains fell from ~400 program columns to ~176.
//!
//! ### The segmentation plan (needed for growth past ~n4/p8, not for Stage 1)
//!
//! The digest chains are no longer the dominant cost (they are ~176 of the 770 columns and
//! carry no lane columns). Past the realistic shape the ordering tooth's range gadgets
//! dominate — the natural cut is the AIR's own body, not the digest.
//!
//! * **Segment A (composition)** — subjects, ruleset, role/param resolution, the knots,
//!   the outcome, the contributions.
//! * **Segments B_d (digest)**, one per stream `d ∈ {subjects, ruleset, outcome,
//!   explanation}` — the `node8` chain over that stream's felts.
//!
//! The seam is the pattern the deployed fold ALREADY uses for the custom leaf's
//! commitment (`prove_custom_binding_node_segmented` `connect`s a claimed commitment,
//! lane by lane, to what the leaf computes in-circuit): segment A exposes its stream
//! columns, each B_d exposes `[its stream ‖ its root]`, and the binding node `connect`s
//! A's stream lanes to B_d's stream lanes and B_d's root lanes to the PI. The connected
//! width is the stream length (46 felts for subjects, 72 for the ruleset at the realistic
//! shape), so it is a fold-node cost, not a new mechanism. This is the automatafl width
//! residual in the same shape and closed the same way — named here, not discovered later.
//!
//! ## SAY THE SUBSTRATE OUT LOUD — the AIR is LEAN-AUTHORED
//!
//! The constraint system lives in `metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean`
//! (`paramComposeDesc`, a shape-parametric family byte-pinned by an `emitVmJson2` `#guard`, with
//! the SAT ⟹ law bridge in `ParamComposeRefine.lean`). The Rust side of that route is two modules
//! that author NO constraints:
//!
//!   * [`lean_descriptor`] — resolve the emitted descriptor for a shape, straight out of the Lean
//!     source (no transcription hop). A shape Lean has not pinned is BLOCKED, not faked.
//!   * [`witness`] — the WITNESS PRODUCER: fill that descriptor's column layout from this crate's
//!     host-side composition data, so `prove_vm_descriptor2` can prove the Lean object. Acceptance
//!     is judged by the DEPLOYED IR-v2 evaluator over the emitted descriptor
//!     ([`witness::compose_trace_accepts`]), never by a predicate this crate wrote.
//!
//! The production consumer (`entity-compose` on the deployed `Effect::Custom` door, and
//! `braid-hook`'s direct-IR2 fold) rides THAT route: the leaf re-proves the emitted descriptor
//! itself, so the relation has exactly one semantics.
//!
//! ### The hand-written Rust AIR is DELETED (2026-07-25)
//!
//! `src/air.rs` (659 lines) and `src/builder.rs` (369) hand-wrote the same AIR in Rust —
//! constraints, gadgets, an `air_accepts` predicate and a `tamper()` forgery harness: the three
//! things the Lean-authored-AIR law names, plus the fourth. They are GONE, together with their two
//! `BASELINE` rows in `circuit-prove/tests/law1_enforcement_gate.rs`. The whole test corpus
//! (`tests/{composition,size,turn_door,prove_fold,lean_witness}.rs`) now rides the emitted
//! descriptor.
//!
//! **The honest price of that deletion**, at current resolution. Four things named as EMITTED but
//! NOT YET REFINED in `ParamComposeRefine.lean`'s coverage boundary lost the only checker they had:
//!
//!   1. **the four digest chains' root-is-the-fold induction** — the wide `node8` chip lookups are
//!      a cross-table BUS arm, and the deployed row-local evaluator
//!      ([`witness::compose_trace_accepts`]) is deliberately silent on those. The retired
//!      `builder.air_accepts` evaluated the `MerkleHash8` sites directly, so a wrong digest column
//!      went red in milliseconds; now only the real batch prover sees it
//!      (`tests/prove_fold.rs::a_tampered_node8_digest_lane_does_not_prove`, `#[ignore]`d). The
//!      PRODUCER-side equality with `crate::reference`'s host twins is still checked fast.
//!   2. **the ordering tooth's integer-level non-vacuity** — the ℤ-level argument that consumes the
//!      `identity_bits <= 28` margin. (The ordering GATES themselves still bite row-locally.)
//!   3. **the activity-prefix corollaries** — "active is a prefix of length `subject_count`" and
//!      "absence is committed as zero".
//!   4. **an assembled `Satisfied2` witness** of the `MultiStepChainRefine.wTrace_satisfied2` kind.
//!
//! ...plus **multi-shape VK distinctness** at `canonical_vk_v2` resolution (there is no
//! `CellProgram` to hash any more; `tests/composition.rs` now pins distinctness of the emitted
//! descriptor NAME and WIRE BYTES, which is what that key is computed over) and the **cross-shape
//! hash-site census**, which moved from `builder.hash_site_count()` to counting the emitted
//! `Lookup` constraints — the same number, read off the emitted object instead of a Rust twin.
//!
//! The emitted descriptor CARRIES all of these gates. The Lean refinement has not PROVEN them.
//!
//! ## Honest scope
//!
//! Things this crate does NOT do, stated at current resolution:
//!
//! 1. **The outcome is not welded into the cell state.** `[old8 ‖ new8]` ride the door and
//!    the EXECUTOR welds them to the cell's roots, but nothing yet requires the cell's new
//!    state to CONTAIN `outcome_commitment`. That weld needs cell-state-layout knowledge,
//!    which is app-specific; its general form is an executor-enforced atom ("the new state
//!    carries the sub-proof's published outcome commitment"), and it is the named residual.
//! 2. **Identity faithfulness is the projection layer's obligation.** The duplicate tooth
//!    refuses two subjects sharing an identity, over the identities it is GIVEN; that an
//!    identity names a distinct real entity is upstream (see [`model::Subject::identity`]).
//! 3. **The binding width is a single `node8` site per block (was 8× costlier).** ~124-bit
//!    roots are a `cap_node8` Merkle-Damgård chain over `ConstraintExpr::MerkleHash8` —
//!    one arity-16 Poseidon2 site whose 8 outputs are program-owned, so it costs zero lane
//!    columns. This used to be 8 parallel 4-ary (`Hash4to1`) chains because the custom-leaf
//!    lowering refused `MerkleHash8`; that refusal is gone. See [`digest`] and
//!    [`shape::DIGEST_FELTS`].
//! 4. **The identity namespace is bounded** (`identity_bits <= 28`, a shape field). Not a
//!    hidden count, but a real limit: the ordering comparison goes VACUOUS on a full-width
//!    31-bit value, so an unbounded identity would give an ordering tooth that looks
//!    present and enforces nothing. A shape that would defeat the margin is REFUSED
//!    ([`ComposeShape::identity_bits_sound`]) rather than silently built.
//! 5. **A role is a KEY.** Roles are unique per composition, which is what makes
//!    `role -> subject` a function (and the outcome non-malleable). Several same-kind
//!    participants therefore take distinct tags (`equipped_0`, `equipped_1`), not a
//!    repeated one — a designed semantic, not an oversight.
//! 6. **Selective disclosure is a commitment opening, not a proof.** Params are private
//!    witness and never public; a caller discloses by opening `subjects_root` /
//!    `explanation_root`. A zero-knowledge *predicate* over a hidden param (rather than
//!    revealing it) is a further ruleset term, not a new mechanism.

pub mod digest;
pub mod field;
pub mod lean_descriptor;
pub mod model;
pub mod pi;
pub mod reference;
pub mod shape;
pub mod witness;

pub use digest::DIGEST_FELTS;
pub use lean_descriptor::lean_descriptor_for;
pub use model::{ComposeError, Composition, Knot, LinearTerm, Ruleset, Subject};
pub use reference::{Composed, compose_over};
pub use shape::{ComposeShape, PARAM_COMPOSE_ABI_VERSION};
pub use witness::{ComposeLayout, ComposeWitness, compose_witness};
