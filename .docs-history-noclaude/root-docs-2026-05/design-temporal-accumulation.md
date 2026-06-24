# Temporal Accumulation: Generalizing Temporal Predicates into Rolling State Accumulators

## The Primitive

Our temporal predicate system currently proves: "attribute X >= threshold for N consecutive blocks." This is a degenerate case of a more general primitive: a **rolling state accumulator** that proves statistical properties over a sliding window, compressed to constant size via IVC.

The generalized accumulator extends `TemporalPredicateAir` from a single-value threshold check into a multi-aggregate windowed computation:

```rust
/// Trace layout for a generalized temporal accumulator.
/// Each row = one step in the rolling window.
///
/// | Column Range   | Name             | Description                          |
/// |----------------|------------------|--------------------------------------|
/// | 0              | value            | Current measurement                  |
/// | 1              | step_count       | Monotonic step counter               |
/// | 2              | sum              | Running sum over window              |
/// | 3              | sum_squares      | Running sum of squares (variance)    |
/// | 4              | min_val          | Running minimum                      |
/// | 5              | max_val          | Running maximum                      |
/// | 6              | evicted          | Value leaving the window             |
/// | 7..7+W         | window[0..W]     | Circular buffer (W = window size)    |
/// | 7+W            | window_pos       | Current write position in buffer     |
/// | 8+W            | state_root       | Binding to IVC chain                 |
/// | 9+W            | ema              | Exponential moving average           |
/// | 10+W..10+W+29  | range_bits[0..29]| Bit decomp for bound checks         |
```

### Transition constraints (row i to row i+1)

```
next.window[local.window_pos] = local.value
next.window_pos = (local.window_pos + 1) % WINDOW
next.sum = local.sum + local.value - local.evicted
next.sum_squares = local.sum_squares + local.value^2 - local.evicted^2
next.min_val = min(local.min_val, local.value)  // via bit decomp
next.max_val = max(local.max_val, local.value)  // via bit decomp
next.ema = local.ema + alpha * (local.value - local.ema)  // fixed-point
next.step_count = local.step_count + 1
```

### Boundary constraints

```
row(0).step_count = 0
row(0).sum = 0
row(last).step_count = pi[total_steps]
row(last).sum = pi[final_sum]  // optional: expose final statistics
```

## IVC Compression

Each accumulator step is one STARK row. The `IvcBuilder` chains steps: step N's `state_root` output feeds step N+1's input. After 1000 steps, the existing `prove_ivc_stark` compresses the entire history into ONE proof via `StateTransitionAir`. The verifier checks a single constant-size proof attesting: "I accumulated 1000 measurements and the final rolling state is X."

No new recursion machinery needed. The `AccumulatedHash` (124-bit wide) already commits to all intermediate roots. We wire the temporal accumulator's per-step `state_root` column as the `new_root` input to `extend_accumulated_hash_wide`.

## Compute Marketplace Application

A GPU worker deploys a temporal accumulator as their sovereign cell program via `ProgramRegistry::deploy`. The DSL form:

```rust
let descriptor = CircuitDescriptor {
    name: "gpu-worker-sla-accumulator-v1".into(),
    trace_width: 42,  // value + stats + window(32) + auxiliaries
    max_degree: 2,
    columns: /* value, sum, sum_sq, min, max, ema, window[0..31], window_pos,
               state_root, step_count, evicted, range_bits[0..29] */,
    constraints: vec![
        // Per-row: sum update is correct
        ConstraintExpr::Polynomial { /* next.sum - local.sum - local.value + local.evicted */ },
        // Per-row: EMA update (fixed-point multiply via auxiliary columns)
        ConstraintExpr::Polynomial { /* next.ema - local.ema - alpha*(local.value - local.ema) */ },
        // Transition: circular buffer write
        ConstraintExpr::Transition { next_col: WINDOW_START + pos, local_col: VALUE },
        // Transition: step counter increment
        ConstraintExpr::Transition { next_col: STEP_COUNT, local_col: STEP_PLUS_ONE },
        // Per-row: range check on value (latency < bound)
        ConstraintExpr::Binary { col: RANGE_BITS_START + i },  // for each bit
        ConstraintExpr::Polynomial { /* bit reconstruction == value - bound */ },
        ConstraintExpr::Polynomial { /* high bit zero => value < bound */ },
    ],
    boundaries: vec![
        BoundaryDef::Fixed { row: BoundaryRow::First, col: STEP_COUNT, value: BabyBear::ZERO },
        BoundaryDef::PiBinding { row: BoundaryRow::Last, col: STEP_COUNT, pi_index: 0 },
        BoundaryDef::PiBinding { row: BoundaryRow::Last, col: SUM, pi_index: 1 },
    ],
    public_input_count: 4, // [total_steps, final_sum, final_min, final_max]
};

let program = CellProgram::new(descriptor, 1);
registry.deploy(program)?;
```

Each block, the worker:
1. Measures latency/throughput/uptime
2. Extends their trace by one row (accumulating into rolling stats)
3. Calls `IvcBuilder::add_fold` to chain the state transition
4. Periodically calls `finalize()` to produce a compressed proof

When a buyer queries capability, the worker provides ONE `IvcProof` covering their entire history. The buyer calls `verify_ivc` -- O(1) verification, no trust required.

## Virtual Organizations

Multiple workers form a VO by composing their individual accumulator proofs. This uses committed conservation (existing in `design-committed-payments.md`) plus cross-state derivation:

- **Sum of capacities**: Each worker's `final_sum` public input is committed. The VO proves `sum(worker_i.final_sum) = total_capacity` via a conservation AIR.
- **Weighted uptime**: `sum(worker_i.uptime * worker_i.stake) / sum(worker_i.stake)` proven via committed threshold composition.
- **Revenue splits**: Each worker's contribution share is `worker_i.final_sum / total_sum`, enforced by the conservation constraint.

The VO itself is a cell program whose trace rows are the member workers' public outputs, with constraints enforcing the aggregation formula.

## What We Add

| Component | Status | Work Required |
|-----------|--------|---------------|
| Rolling window (circular buffer columns) | New | Trace layout + modular position constraint |
| Statistical aggregates (sum, variance, min, max) | New | Polynomial constraints over auxiliary columns |
| IVC compression of temporal steps | **Exists** | Wire `state_root` to `IvcBuilder` |
| Multi-party aggregation | Partially exists | Conservation AIR over N public input vectors |
| Time-weighted EMA | New | Fixed-point multiply in BabyBear via auxiliary decomposition |

The fixed-point EMA requires representing the smoothing factor alpha as a ratio `a/b` where both fit in BabyBear. For alpha = 2/(N+1) with window N=32: `a=2, b=33`. The constraint becomes `next.ema * b = local.ema * b + a * (local.value - local.ema)`, which is degree-2 and native to our AIR framework.

## Integration Path

The temporal accumulator is deployed as a `CellProgram` via `ProgramRegistry`. Verification uses `CellProgram::verify_transition` with the STARK proof bytes. The IVC layer (`IvcBuilder`) chains transitions. No changes to the executor or turn model -- the accumulator is just a richer cell program that happens to maintain rolling statistics instead of simple thresholds.
