//! Dregg Constraint DSL — proc macro crate.
//!
//! Provides `#[dregg_caveat]` and `#[dregg_effect]` which compile one constraint
//! function into SIX backends:
//! - `gen_rust`     — a Rust evaluator (`{name}_check`)              [agreement set]
//! - `gen_air`      — an AIR constraint descriptor (`{name}_air_constraints`) [agreement set]
//! - `gen_datalog`  — a Datalog rule fragment (`{name}_datalog`)    [agreement set]
//! - `gen_kimchi`   — a Kimchi circuit descriptor (`{name}_kimchi`) [agreement set]
//! - `gen_midnight` — a Midnight ZKIR v3 program (`{name}_midnight_zkir`) [emit-only/lint-only]
//! - `gen_sp1`      — an SP1 guest program (`{name}_sp1_guest`)      [emit-only/lint-only]
//!
//! The former `emit_stark` backend (a compile-time impl of the hand-rolled `dregg_circuit` STARK) was
//! removed with that engine. The former `gen_plonky3` backend (a native `{Name}P3Air` uni-STARK impl) was
//! DELETED 2026-07-17 — see the retirement note below. **Proving is the descriptor path**: `gen_air` emits
//! the constraint descriptor, and `dregg_circuit::dsl::dsl_p3_air` (a batch-STARK INTERPRETER over that
//! descriptor) proves/verifies it.
//!
//! ## Cross-validation status
//!
//! FOUR backends (`gen_rust`, `gen_air`, `gen_datalog`, `gen_kimchi`) form the **agreement set**
//! cross-checked by `dregg-dsl-differential` (gen_rust is the oracle). `gen_midnight` and
//! `gen_sp1` are STRING emitters validated by lint only (their proof systems need
//! external toolchains); they cast no agreement vote.
//!
//! ⚠ RETIREMENT — `gen_plonky3` DELETED 2026-07-17 (it emitted code that DOES NOT COMPILE).
//!
//! It claimed an agreement-set vote it never cast, and it was **broken**: the emitted `{Name}P3Air`
//! targets an OBSOLETE Plonky3 API (`MainWindow::current_slice()`, and `AB::Expr::ONE` without the
//! trait in scope). Nothing caught that because **nothing ever compiled it**: the macro emitted the impl
//! behind `#[cfg(feature = "plonky3")]`, and NO consumer crate ever declared that feature — not even
//! `dregg-dsl-tests`, this DSL's own compile-test crate. (rustc's `unexpected_cfgs` lint, once flipped to
//! `warn`, surfaced all 16 always-false gates; declaring the feature made the codegen meet the compiler for
//! the first time, and it failed instantly.) Its `falsifier_*` tests could not catch this: they check the
//! emitted TOKEN STRUCTURE, which cannot detect API drift in code nobody builds.
//!
//! Its "vote" was already a fiction, and the old doc said so honestly: `dregg-dsl-differential`'s
//! `plonky3_runner` **never instantiated the macro-emitted `{Name}P3Air`** — it hand-builds its own
//! `CircuitDescriptor` from the IR and round-trips THAT, so the harness "agreed" with a **re-derived
//! mirror** of the predicate, not with the columns this backend bound. That gap is what let the
//! `find_p3_col` column-0 fallback survive undetected. **THE LESSON SURVIVES THE BACKEND:** the harness
//! still validates a re-derived descriptor through the production interpreter — which is the RIGHT thing to
//! validate (it is what deploys), but it means no agreement vote is cast by macro-emitted prover code, and
//! none is claimed any more.
//!
//! ## Range-check soundness
//!
//! ⚠ CORRECTED 2026-07-17. This section used to claim `<=`, `>=` and `in_range!` compile to a genuine
//! bit-decomposition range check (`RANGE_CHECK_BITS` binary witness columns, reconstruction enforced, top
//! bits forced to zero, so a field-wrapped negative difference is UNSATISFIABLE). **That check lived ONLY
//! in `gen_plonky3` — i.e. in code that NEVER COMPILED — so the claimed soundness was never real in any
//! built artifact.** It is deleted with the backend, and the claim with it.
//!
//! WHAT IS TRUE NOW: comparisons lower through `gen_air`
//! (`RequirementKind::LessEqual`, gen_air.rs:89, "each comparison requirement adds auxiliary columns") into
//! the descriptor the production interpreter proves.
//!
//! ⚑ RESOLVED 2026-07-17 — `DslComparisonRangeSoundnessResidual` was NAMED, then PROVEN UNSOUND by a
//! live prover, then FIXED. Both halves are pinned by teeth in
//! `dregg-dsl-differential/tests/comparison_wrap_soundness.rs`.
//!
//! 1. **`gen_air`'s `Constraint::RangeCheck { diff_col, bit_col }` proves NOTHING — still open.** It is a
//!    topology DESCRIPTOR (`dregg_dsl_runtime::AirConstraintSet`). Its only consumers are `air_runner.rs`
//!    (matches the variant SHAPE, then re-derives accept/reject in NATIVE u64 via `check_le`) and structural
//!    token tests. There is no `AirConstraintSet -> CircuitDescriptor` converter in the repo — nothing
//!    lowers it into a proved constraint system. One `bit_col` could not range-check a ~31-bit difference
//!    anyway.
//! 2. **The one path that reaches a real prover WAS unsound; it is now range-checked — PROVEN SOUND
//!    against the forgery that broke it.** `dregg-dsl-differential/src/plonky3_runner.rs::drive_inequality`
//!    hand-builds a `CircuitDescriptor` ("diff-le") and proves it through the production interpreter. Its
//!    constraints used to be only: `bigger - smaller - diff == 0` (mod p — always satisfiable), `indicator`
//!    boolean, `indicator == 0`. No bit decomposition bounded `diff`, and nothing linked `indicator` to
//!    `diff`, so the comparison's truth lived in the honest WITNESS GENERATOR (native `ir_ok = smaller <=
//!    bigger`), which volunteered an invalid witness when the claim was false — a courtesy a malicious
//!    prover declines. Demonstrated live: `5 <= 3` with `diff = (3-5) mod p` and `indicator = 0` satisfied
//!    every constraint and was ACCEPTED by the production p3 prover AND verifier. (The old in-file claim
//!    that capping operands to "a 30-bit range" kept the encoding sound was FALSE: the forgery used
//!    far-sub-30-bit operands, because capping the OPERANDS bounds nothing about a `diff` column no
//!    constraint reads.)
//!
//!    The lowering now carries the genuine gadget: a bit-decomposition range check with every bit
//!    boolean-pinned, so a field-wrapped negative difference is UNSATISFIABLE, and the operands are
//!    PI-bound so the proof is about the publicly claimed comparison. The `indicator` column is gone:
//!    rejection of a false claim is now the constraint system's verdict, not the generator's confession.
//!    The forgery pin is flipped into a rejection tooth, with companions pinning that the binary
//!    constraints and PI bindings are load-bearing.
//!
//!    ⚑ **The stated limit is GONE — the gadget now covers the whole u64 domain** (2026-07-17, lane
//!    `dsl-2p30-fallback`). The first fix was sound only on `[0, 2^30)`: `drive_inequality`
//!    SHORT-CIRCUITED to `prove_trivial(ir_ok)` when either operand was `>= 2^30`, and on that path NO
//!    circuit was built — the verdict WAS the native-`u64` oracle's own answer, precisely the
//!    generator's confession the paragraph above says is gone, for the operands (`u64::MAX` and
//!    friends) the predicate suite uses most. It was disclosed rather than closed because no test could
//!    see it: `Reject` looks identical whether constraints refuted the claim or the oracle just
//!    answered.
//!
//!    That path is DELETED, not documented. It could not be closed by widening the decomposition, for
//!    two independent reasons worth keeping: (i) `2^30 - 1 < p` but `2^31 - 1 > p`, so 30 bits was
//!    already THE CEILING for a single-element range check, not a cautious choice; and (ii)
//!    `BabyBear::from_u64` reduces mod p, so operands `>= p` were never in their columns at all
//!    (`from_u64(u64::MAX) = 1172168162`, `from_u64(BABYBEAR_P) = 0`) — an EMBEDDING failure no range
//!    check can reach. So the gadget stopped asking one field element to carry a u64: `u64-le` splits
//!    each operand into four PI-bound base-`2^16` limbs, range-checks each with 16 boolean bits, and
//!    subtracts with a borrow chain whose top borrow must be zero. Every intermediate stays under
//!    `2^18` — ~13 bits of headroom under `p` — so each field equation implies its integer counterpart,
//!    and the witness is unique, so there is nothing for a prover to search for.
//!
//!    The closure is ASSERTED, not announced: `every_operand_takes_the_circuit_never_the_oracle` pins
//!    that operands across the domain (`0`, `2^30 - 1`, `2^30`, `BABYBEAR_P`, `2^32`, `u64::MAX`) are
//!    decided by a CIRCUIT, and `modulus_aliased_operands_are_decided_by_constraints` pins the exact
//!    rock a naive widening would have foundered on — `BABYBEAR_P <= 0` must be UNSAT. Every constraint
//!    in the gadget has a tooth proven by a mutation canary; see the mutation matrix in
//!    `dregg-dsl-differential/tests/comparison_wrap_soundness.rs`. One of those canaries found a real
//!    forgery the lane had not modelled (a non-boolean borrow buying back the modulus), which the
//!    production prover accepted once its constraint was removed.
//!
//!    ⚠ **The remaining fallback.** `drive_equality_u64` / `drive_nonequality_u64` still carry the
//!    `2^30` cutoff that inequalities no longer do, and it is load-bearing for them: without it
//!    `eq-u64` would ACCEPT the false `BABYBEAR_P == 0` (both operands embed to the zero column). The
//!    cutoff hides that aliasing rather than fixing it, and the same limb machinery closes it. Named,
//!    not closed: `DslEqualityOperandAliasingResidual`. The u64-domain teeth cover `<=`/`>=` only.
//! 3. **Scope:** that lowering is the DIFFERENTIAL HARNESS's own, not a shipped circuit — so what changed
//!    is that the harness's Plonky3 agreement vote on inequalities now validates its CONSTRAINTS and not
//!    merely its witness generator. Production circuits needing order comparisons always did range-check
//!    genuinely (30-bit decomposition + binary-pinned bits + top bit fixed to zero):
//!    `circuit/src/dsl/committed_threshold.rs` (C4/C5 + `BoundaryDef::Fixed` on the top bit),
//!    `derivation.rs` C17/C22, `descriptors.rs` ordering — and the fix copies that precedent.
//!    **No DSL surface lowers `<=`/`>=`/`in_range!` into a proved circuit at all** — that gap (item 1) is
//!    what remains.

extern crate proc_macro;

mod gen_air;
mod gen_datalog;
mod gen_kimchi;
mod gen_midnight;
mod gen_rust;
mod gen_sp1;
mod ir;
mod parse;

use proc_macro::TokenStream;
use quote::quote;
use syn::{ItemFn, parse_macro_input};

/// Marks a function as a dregg caveat constraint.
///
/// The function body must consist of `require!(expr)` statements where each
/// `expr` is a binary comparison or a `.contains()` membership check.
/// The macro expands the function into generated items:
///
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — runtime evaluator
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR topology descriptor
/// - `{name}_datalog() -> &'static str` — Datalog rule
/// - `{name}_kimchi() -> KimchiCircuitDescriptor` — Kimchi gate descriptor
///
/// # Example
///
/// ```ignore
/// // IGNORED: `dregg-dsl` is a proc-macro crate whose dependencies are exactly
/// // `syn`/`quote`/`proc-macro2`, while this macro EXPANDS to code naming
/// // `dregg_dsl_runtime::{ConstraintError, AirConstraintSet, Constraint, …}`. The
/// // expansion therefore cannot resolve inside this crate's own doctests. The compiled
/// // exercise of exactly this shape lives in `dregg-dsl-tests/src/dregg_definitions.rs`.
/// #[dregg_caveat]
/// fn not_after(token_expiry: u64, current_time: u64) {
///     require!(current_time <= token_expiry);
/// }
/// ```
#[proc_macro_attribute]
pub fn dregg_caveat(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    let ir = match parse::parse_caveat(&func) {
        Ok(ir) => ir,
        Err(e) => return e.to_compile_error().into(),
    };

    let rust_eval = gen_rust::generate_rust_evaluator(&ir);
    let air_desc = gen_air::generate_air_descriptor(&ir);
    let datalog = gen_datalog::generate_datalog(&ir);
    let kimchi = gen_kimchi::generate_kimchi(&ir);
    let midnight = gen_midnight::generate_midnight(&ir);
    let sp1 = gen_sp1::generate_sp1(&ir);

    let output = quote! {
        #rust_eval
        #air_desc
        #datalog
        #kimchi
        #midnight
        #sp1
    };

    output.into()
}

/// Marks a function as a dregg effect — a constraint with state mutation.
///
/// Effect functions may contain `&mut` parameters and mutation statements
/// (`*balance -= amount`), in addition to `require!()` checks and `match` arms.
///
/// Supports a `requires` attribute for permission gating:
/// ```ignore
/// // IGNORED: same structural reason as `dregg_caveat` above — the expansion names
/// // `dregg_dsl_runtime::*`, which this proc-macro crate deliberately does not depend on
/// // (and `Direction` is the caller's enum). Compiled counterpart:
/// // `dregg-dsl-tests/src/dregg_definitions.rs`.
/// #[dregg_effect(requires = "Send")]
/// fn transfer(balance: &mut u64, amount: u64, direction: Direction) {
///     match direction {
///         Direction::Outgoing => {
///             require!(balance >= amount);
///             *balance -= amount;
///         }
///         Direction::Incoming => {
///             *balance += amount;
///         }
///     }
/// }
/// ```
///
/// Generates:
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — evaluator that mutates in-place
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR with old+new columns per mutable param
/// - `{name}_datalog() -> &'static str` — Datalog rule
/// - `{name}_kimchi() -> KimchiCircuitDescriptor` — Kimchi gates
/// - `{name}_effect_descriptor() -> EffectDescriptor` — effect metadata
#[proc_macro_attribute]
pub fn dregg_effect(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    // Parse the attribute for `requires = "..."`.
    let required_permission = parse_effect_attr(attr);

    let ir = match parse::parse_effect(&func, required_permission) {
        Ok(ir) => ir,
        Err(e) => return e.to_compile_error().into(),
    };

    let rust_eval = gen_rust::generate_rust_evaluator(&ir);
    let air_desc = gen_air::generate_air_descriptor(&ir);
    let datalog = gen_datalog::generate_datalog(&ir);
    let kimchi = gen_kimchi::generate_kimchi(&ir);
    let effect_desc = gen_rust::generate_effect_descriptor(&ir);
    let midnight = gen_midnight::generate_midnight(&ir);
    let sp1 = gen_sp1::generate_sp1(&ir);

    let output = quote! {
        #rust_eval
        #air_desc
        #datalog
        #kimchi
        #effect_desc
        #midnight
        #sp1
    };

    output.into()
}

/// Parse `#[dregg_effect(requires = "Send")]` attribute.
fn parse_effect_attr(attr: TokenStream) -> Option<String> {
    let attr_str = attr.to_string();
    if attr_str.is_empty() {
        return None;
    }
    // Simple parsing: look for `requires = "..."`
    if let Some(start) = attr_str.find("requires")
        && let Some(eq_pos) = attr_str[start..].find('=')
    {
        let after_eq = &attr_str[start + eq_pos + 1..];
        let trimmed = after_eq.trim();
        if trimmed.starts_with('"') {
            let end = trimmed[1..].find('"').unwrap_or(trimmed.len() - 1);
            return Some(trimmed[1..1 + end].to_string());
        }
    }
    None
}
