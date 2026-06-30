# The Faithful-Commitment Law

**Every 32-byte component that flows into the deployed state commitment binds its
SOURCE at the system's own soundness strength (~124-bit, the 8-felt encoding) —
never a lossy 1-felt projection.**

## Why this is a law, not a preference

The deployed state commitment once carried components folded **32 bytes → ONE
BabyBear** (`fold_bytes32_to_bb`, a Horner fold). A single BabyBear is ~31 bits,
so two distinct 32-byte values collide with probability ~`1/p ≈ 2^-31`. That is
**far below** the system's own ~130-bit FRI/STARK soundness floor: an adversary
who can grind a 31-bit collision can show a light client a forged committed state
that the proof still accepts.

The insidious part: **a bare `BabyBear` limb carries no evidence of
faithful-vs-degraded.** A faithful 8-felt binding and a degraded 1-felt fold are
the same type (`BabyBear` / `[BabyBear; …]`), so a lossy fold slid into the
commitment silently and was only found by a **bit-audit months later** — then
cost weeks to grind back to faithful 8-felt. The cost of catching it at write
time is one CI second; the cost of not catching it is the months-to-weeks loop.

See the historical analysis in `.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`
and the memory note *Don't Launder a Load-Bearing Insecurity*.

## The rule

- **Degraded (forbidden in a commitment position):** `fold_bytes32_to_bb(x)` —
  32 bytes → 1 felt (~31-bit). Defined in `circuit/src/effect_vm/helpers.rs`.
- **Faithful (required):** `bytes32_to_8_limbs(x)` → `[BabyBear; 8]` (~124-bit),
  and its hash-domain siblings (`hash_many` over 8-felt groups). The commit binds
  the **source**, not a degraded projection of it.

A degraded fold is a fine **consistency tag** where the *real* binding lives
elsewhere (defense-in-depth), and a fine per-effect param projector. It is a
**bug** only when it IS the commitment of a 32-byte component.

## Where the law bites (the commitment-bearing producers)

| File | Role |
|------|------|
| `cell/src/commitment.rs` (`compute_rotated_pre_limbs`) | the canonical `pre_limbs` the rotation commits |
| `turn/src/rotation_witness.rs` | the producer twin of the above |
| `circuit/src/effect_vm/trace_rotated.rs` | the rotated trace that re-absorbs `pre_limbs` |

Non-commitment uses of the fold are **out of scope and sound**: the executor/SDK
per-effect param projectors (`effect_vm_bridge.rs`, `cipherclerk.rs`), the D5 PI
cross-binding reconstruction (`proof_verify.rs`, `node/src/turn_proving.rs` — the
real binding is the `SCHEMA_NOTE_SPEND` proof + the committed set), and tests.

## The gate

`scripts/check-no-degraded-felt.sh` runs `ast-grep` against the producers above
(rule `.ast-grep/rules/faithful-commitment-felt.yml`, scoped by its `files:`
field). Wired into CI as the **`no-degraded-felt`** job in `.github/workflows/ci.yml`.
A net-new `fold_bytes32_to_bb` in a commitment producer **fails the PR**.

### Allowlisting a deliberate residual

A justified residual is annotated inline, line-scoped:

```rust
// FAITHFUL-COMMITMENT-LAW residual: <why this is safe / when it gets fixed>.
pre[4 + i] = fold_bytes32_to_bb(&cell.state.fields[i]); // ast-grep-ignore: degraded-felt-commitment
```

⚠ The text after the directive's colon is parsed by ast-grep as a **rule-id
list**, so the suppression must read exactly `// ast-grep-ignore:
degraded-felt-commitment` (the rule id) — the human REASON goes on the line
ABOVE, never after the colon.

### Current allowlisted residuals

- **`fields[0..7]`** (the r3..r10 Horner fold in `compute_rotated_pre_limbs` and
  its `rotation_witness` twin): the unfixed faithful-commitment residual. The
  8-felt grind for these limbs is a TODO, parallel to the cap/heap/fields_root
  grind. Allowlisted with a reason; **a different / additional degrading fold here
  still fails the gate.**

## The capstone (named future work)

This gate is the **ast-grep flavor** of "never introduce a degraded felt again."
It enforces the law by *pattern* in three known producers. The stronger,
type-level capstone — a **`Faithful8` newtype** whose only constructor is the
8-felt encoder, so the *compiler* refuses to place a degraded felt in a committed
position anywhere — comes **after** the faithful-commitment campaign lands
cap/heap/fields_root at 8-felt (it needs the commitment limbs to already be
8-felt before the wall can stand without a sea of escape hatches). Until then,
this gate holds the line.
