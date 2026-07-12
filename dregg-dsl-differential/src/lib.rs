//! Cross-backend differential testing for `dregg-dsl`.
//!
//! # Mission
//!
//! Given the same caveat predicate expressed once via `#[dregg_caveat]`, the DSL
//! emits EIGHT backends. FIVE of them — `gen_rust`, `gen_datalog`, `gen_air`,
//! `gen_kimchi`, `gen_plonky3` — are run in-process and must AGREE on
//! accept/reject for any given input; this is the cross-validated **agreement
//! set**. This crate emits a battery of canonical predicates, drives a curated
//! input set through every agreement-set backend, and asserts they all report
//! the same verdict.
//!
//! The remaining three emitted backends are deliberately NOT in the agreement
//! set, and are NOT counted as cross-validated:
//!
//! - `gen_midnight` and `gen_sp1` are STRING emitters whose execution needs an
//!   external toolchain (a Midnight proof server / the SP1 RISC-V toolchain).
//!   The harness lint-checks their output and records `Skip` — they cast no
//!   Accept/Reject vote and contribute nothing to agreement.
//! - `emit_stark` emits a compile-time-baked hand-AIR impl. It is exercised
//!   by the prove/verify tests in `dregg-dsl-tests`, not by this differential
//!   harness, so it is not in the agreement matrix either.
//!
//! # Backend Roster
//!
//! The DSL has eight code generators (5 cross-validated here + 3 not):
//!
//! | Backend     | Emits                              | In the agreement set?                           |
//! |-------------|------------------------------------|-------------------------------------------------|
//! | `gen_rust`     | `{name}_check(...)` evaluator   | YES — call the function directly. (Oracle.)     |
//! | `gen_datalog`  | `{name}_datalog() -> &'static str` Datalog rule string | YES — mini in-crate Datalog evaluator. |
//! | `gen_air`      | `{name}_air_constraints() -> AirConstraintSet` topology descriptor | YES — re-derive accept/reject via the IR-aligned `dregg_dsl_runtime::diff_witness` primitives, sanity-checked against the descriptor's column accounting. |
//! | `gen_kimchi`   | `{name}_kimchi() -> KimchiCircuitDescriptor` gate descriptor | YES — Generic-gate simulator that fills the canonical witness per IR shape and asserts every gate's `c_i * w_i` polynomial evaluates to zero. Poseidon gates (membership-only) are checked structurally. |
//! | `gen_plonky3`  | `{Name}P3Air` native Plonky3 AIR struct | YES (subset) — for the predicate shapes we can build a generic `CircuitDescriptor` over (arithmetic comparisons, equalities), we round-trip through `prove_dsl_plonky3` + `verify_dsl_plonky3`. Membership shapes require Poseidon2 gadgets and are marked SKIP. |
//! | `emit_stark`   | (REMOVED with the hand-STARK engine, stark-kill f04b2dd1e) | Its forge-detector probe (`tests/_probe_stark.rs`: LE/EQ/NE honest-accept + violation-reject, incl. the inequality bit-decomposition tooth) died with it; those accept/reject poles are carried by the curated comparison/equality cases voted through `gen_plonky3`'s `prove_dsl_plonky3`/`verify_dsl_plonky3` round-trip against the rust oracle in this harness. |
//! | `gen_midnight` | `{name}_midnight_zkir() -> &'static str` ZKIR v3 JSON | NO — emit-only/lint-only. Midnight ZKIR is consumed by an off-chain proof server; we lint the emitted JSON (parses, mentions every param, terminates with an `output` instruction) and record `Skip`. Casts no agreement vote. |
//! | `gen_sp1`      | `{name}_sp1_guest() -> &'static str` SP1 guest source | NO — emit-only/lint-only. Running the guest requires the SP1 RISC-V toolchain (`sp1-prove`/`cargo prove build`); we lint the source (has `main`, declares each input via `sp1_zkvm::io::read`) and record `Skip`. Casts no agreement vote. |
//!
//! # Predicate Suite
//!
//! See [`predicates`]. We cover the IR shapes a caveat can take today:
//!
//! - Pure inequalities: `<=`, `>=`
//! - Equality, non-equality (on `u64` and `[u8; 32]`)
//! - Conjunction (multiple `require!` in one body)
//! - Bound-relative comparisons (`threshold + step <= cap`)
//! - Set membership (`set.contains(elem)`)
//! - Combined: membership AND inequality
//!
//! For each predicate we curate a small, deterministic input set spanning
//! positive cases, negative cases, and boundary values (zero, one,
//! `u64::MAX`, near-overflow, byte-array all-zeros, byte-array all-ones).
//!
//! # Failure Narration
//!
//! When backends disagree, [`agreement::AgreementMatrix`] reports which
//! backends voted Accept vs Reject, what the input was, and which backends
//! were Skipped. The test binary panics with a structured report so the
//! offender is identifiable in CI logs.

pub mod agreement;
pub mod air_runner;
pub mod datalog_eval;
pub mod harness;
pub mod kimchi_sim;
pub mod midnight_lint;
pub mod plonky3_runner;
pub mod predicates;
pub mod sp1_lint;

pub use agreement::{AgreementMatrix, BackendName, BackendVerdict, RowReport};
