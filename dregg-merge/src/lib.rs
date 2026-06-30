//! # dregg-merge — the I-confluent offchain merge/write runtime
//!
//! This is the **WRITE half** of the read face [`dregg_query`]: the production
//! realization of the DREGG3 §2.4 `merge` interpretation (interp = executor,
//! compile = circuit, **merge = CRDT-sync**), which was the missing half of the
//! mostly-offchain-coordination thesis (`DreggNet/docs/ARCHITECTURE-CRITIQUE.md`
//! §4.3, §5.4: the read face + the formal gate exist; the write/merge runtime
//! was unbuilt).
//!
//! ## The offchain-coordination payoff
//!
//! Two parties each hold their own copy of a cell. Each applies **I-confluent**
//! operations to its own copy *offchain, with no coordination* (partition-
//! tolerant, no consensus, no chain op). Then they **merge**: a deterministic,
//! commutative, associative, idempotent CvRDT join ([`MergeState::join`]) that
//! converges to a single state **regardless of merge order** — and, crucially,
//! **needs no consensus**. That is the whole point of I-confluence: concurrent
//! invariant-preserving versions merge invariant-safely (BEC Thm 3.1), so the
//! merge is a *local* operation neither party has to be told is legal.
//!
//! ## The confluence gate — only I-confluent ops merge freely
//!
//! The runtime is gated by [`gate::classify_merge`], the Rust face of
//! `metatheory/Dregg2/Confluence.lean` (`IConfluent` / `Tier1Eligible`) and
//! `Dregg2/Confluence/SemanticConvergence.lean` (the rhizomatic G-Set + the
//! `survivors = asserted \ negated` non-monotone reason). The gate distinguishes
//! two reasons a merge is **not** free:
//!
//! 1. **A structurally non-I-confluent invariant** (a bounded resource —
//!    `balance ≥ 0`, the `cardLeOne_not_iconfluent` shape). Two locally-valid
//!    decrements merge to an overdraft. [`BoundedCounter`] is the witness.
//! 2. **A non-monotone op participating** (a retraction/negation — the
//!    `negation_retracts` reason; `dregg_query::CoordinationClass::FinalizedDependent`).
//!    [`GrowSet`] with a tombstone is the witness.
//!
//! When either holds the gate **refuses the free merge** and returns
//! [`Escalation::MustSettle`]: the operation must go through a settling turn at
//! the boundary — the one place revocation is non-monotone
//! (`metatheory/Dregg2/.../SettlementSoundness.lean`). Confluent → merge offchain
//! free; non-confluent → settle at the boundary.
//!
//! ## The mergeable receipt — a verifiable trace with no chain op
//!
//! Every free merge emits a [`MergeReceipt`]: the merged state's content
//! commitment + the provenance of the merged operations + a prev-hash chain (the
//! `TurnReceipt`/`BridgeReceipt` discipline the critique praised). A third party
//! who holds the two input states can [`MergeReceipt::rewitness`] the merge —
//! recompute the join and check the commitment — with **no chain op per merge**.
//! The receipts compose as leaves of the read face's MMR
//! ([`dregg_query::Mmr`]), so the whole offchain-coordination trace carries a
//! non-omission certificate (see `tests/`).
//!
//! ## What is and is not proved here
//!
//! The CRDT laws and the gate's dichotomy are **machine-checked in Lean** over
//! the abstract lattice (`Confluence.lean`, `SemanticConvergence.lean` —
//! axiom-clean, both polarities witnessed). This crate is the executable Rust
//! realization: the same dichotomy, exercised by the test suite as
//! commutativity / associativity / idempotence / merge-order determinism, the
//! non-confluent refusal, and the re-witnessable receipt. The Lean ⟷ Rust
//! refinement (that THIS `join` IS the `⊔` the gate reasons about, in-circuit)
//! is a NAMED SEAM for the circuit swarm — see [`gate`].

pub mod delta;
pub mod gate;
pub mod receipt;
pub mod runtime;
pub mod state;

pub use delta::{Delta, Hash, OpKind, content_id};
pub use gate::{Escalation, MergeVerdict, classify_merge};
pub use receipt::{DeltaProvenance, MergeReceipt, RewitnessError};
pub use runtime::{MergeOutcome, MergeRuntime};
pub use state::{BoundedCounter, GrowSet, MergeState};

/// Re-exported from the read face so producers annotate merges with the SAME
/// coordination grade the query side speaks (`dregg_query::classify`).
pub use dregg_query::CoordinationClass;
