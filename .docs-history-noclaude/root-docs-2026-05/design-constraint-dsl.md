# `dregg` Constraint DSL

## Problem

Authorization logic is duplicated across imperative Rust (`verify_caveats`), Datalog rules (`attenuation_datalog`), AIR constraints (`derivation_air`), and sovereign transition proofs. These diverge, producing bugs like dimension_passthrough, factset mismatches, and check-term unbinding. A single-source DSL compiling to all four targets eliminates that class of bug entirely.

## What Developers Write

```rust
#[dregg_caveat]
fn not_after(token_expiry: u64, current_time: u64) {
    require current_time <= token_expiry;
}

#[dregg_caveat]
fn budget(remaining: u64) -> Mutation {
    require remaining >= 1;
    mutate remaining -= 1;
}

#[dregg_caveat]
fn service_scope(allowed_services: Set<ServiceId>, requested: ServiceId) {
    require allowed_services.contains(requested);
}

#[dregg_effect]
fn transfer(balance: u64, amount: u64, direction: Direction) -> Mutation {
    match direction {
        Outgoing => {
            require balance >= amount;
            mutate balance -= amount;
        }
        Incoming => {
            mutate balance += amount;
        }
    }
}

#[dregg_predicate]
fn balance_gte(balance: u64, threshold: u64) {
    require balance >= threshold;
}
```

## What Gets Generated

Each annotated function expands to four compilation targets:

### Target 1: Rust Evaluator

```rust
// From #[dregg_caveat] fn not_after
pub fn not_after_verify(token_expiry: u64, current_time: u64) -> Result<(), CaveatError> {
    if !(current_time <= token_expiry) {
        return Err(CaveatError::RequireFailed("not_after"));
    }
    Ok(())
}
```

Replaces hand-written logic in `token/src/dregg_caveats.rs`. Used for trusted-mode verification and the hosted cell executor.

### Target 2: Datalog Rules

```rust
// From #[dregg_caveat] fn not_after
pub fn not_after_datalog() -> Rule {
    rule!("satisfied_not_after(Token) :- \
           token_expiry(Token, Exp), context_time(Now), lte(Now, Exp).")
}
```

Replaces `dregg.rs::attenuation_datalog()`. Caveats become rule bodies; composition is conjunction of rules. Used in the token authorization engine and multi-step derivation chains.

### Target 3: AIR Constraints (BabyBear STARK)

```rust
// From #[dregg_caveat] fn not_after
impl NotAfterAir {
    const TRACE_WIDTH: usize = 18; // 2 inputs + 16-bit decomposition

    fn generate_trace(&self, token_expiry: u64, current_time: u64) -> RowMajorMatrix<BabyBear> {
        let diff = token_expiry - current_time;
        let bits = decompose_u64_to_bits::<16>(diff);
        // ... pack into trace row
    }

    fn eval(&self, builder: &mut ConstraintBuilder) {
        // diff = token_expiry - current_time
        let diff = local[COL_EXPIRY] - public[PI_TIME];
        // range check: diff decomposes into 16 bits (proves non-negative)
        let recomposed = (0..16).fold(AB::Expr::zero(), |acc, i| {
            acc + local[COL_BIT_0 + i] * AB::Expr::from_wrapped_u32(1 << i)
        });
        builder.assert_eq(diff, recomposed);
        // each bit is boolean
        for i in 0..16 {
            builder.assert_bool(local[COL_BIT_0 + i]);
        }
    }
}
```

Replaces hand-written constraints in `circuit/src/derivation_air.rs` and `circuit/src/sovereign_transition_air.rs`. The compiler in `circuit/src/predicate_program.rs` becomes part of the DSL backend.

### Target 4: SP1 Guest (same as Rust, packaged for cross-chain bridging)

```rust
// Compiled into sp1 guest binary
#[sp1_guest::main]
fn main() {
    let (token_expiry, current_time) = sp1_guest::read_input();
    not_after_verify(token_expiry, current_time).expect("constraint violated");
    sp1_guest::commit(&true);
}
```

Used for proving to EVM/Midnight/external chains via the bridge in `bridge/src/present.rs`.

## Compilation Strategy

| DSL construct | Rust | Datalog | AIR | SP1 |
|---|---|---|---|---|
| `require a <= b` | `if !(a <= b) { err }` | `lte(A, B)` | range-check bit decomposition | same as Rust |
| `require set.contains(x)` | `set.contains(&x)` | `member(X, Set)` | MemberOf commitment equality | same as Rust |
| `mutate x -= n` | `*x -= n` | output fact | next_row[col] = local[col] - n | same as Rust |
| `match` on enum | `match` | multiple rules | selector columns | same as Rust |

## Type System

- `u64` -- amounts, timestamps. In AIR: 4 BabyBear limbs with range checks.
- `[u8; 32]` -- hashes, keys. In AIR: 8 limbs, Poseidon-committed.
- `bool` -- flags. In AIR: single column with boolean constraint.
- `Set<T>` -- collections. In AIR: Merkle commitment with membership proofs as auxiliary trace.
- `Direction`, user enums -- finite variants. In AIR: selector column (one-hot encoding).

No unbounded loops. Bounded iteration over fixed-size structures only (`for field in cell.fields[0..8]`). This keeps AIR trace width static and Datalog rules finite.

## Composition

Caveats compose by conjunction (all must pass). Effects compose by sequencing (applied in order). A token carries a list of caveat references; a transaction carries a list of effect invocations. The generated AIR stacks sub-AIRs vertically (one row-section per constraint) within the existing `multi_step_air` framework.

## Roadmap

| Phase | Scope | Replaces |
|---|---|---|
| 1 | Proc macro for caveats -> Rust + AIR | `dregg_caveats.rs`, `derivation_air.rs` constraint logic |
| 2 | Proc macro for effects -> executor + sovereign AIR | `sovereign_transition_air.rs`, executor mutation code |
| 3 | User-defined constraint programs (the DSL becomes the cell language) | `predicate_program.rs` |
| 4 | Standalone `.dregg` language + LSP if macros prove limiting | -- |

## Why Proc Macro First

A proc macro means zero new tooling: `cargo build` compiles constraints, `rust-analyzer` provides completions, existing test infrastructure works unchanged. The macro inspects the function body's AST, extracts `require` and `mutate` nodes, and emits the four target implementations as sibling items. If Rust syntax becomes too constraining (likely around Phase 3 when users write programs), we introduce `.dregg` files with a custom parser that still outputs Rust via `build.rs`.

## Crate Layout

```
dregg-dsl/
  dregg-macro/       # proc macro crate (#[dregg_caveat], #[dregg_effect], #[dregg_predicate])
  dregg-ir/          # intermediate representation (constraint graph, mutation DAG)
  dregg-air-gen/     # IR -> AIR trace layout + constraint eval + witness gen
  dregg-datalog-gen/ # IR -> Datalog rules
  dregg-runtime/     # shared types (CaveatError, CellState, Context)
```

The IR is the key artifact: a directed graph of require-nodes and mutate-nodes with typed edges. Each backend walks this graph to emit its target. Adding a new backend (e.g., Noir for Aztec integration) means implementing one trait over the IR.
