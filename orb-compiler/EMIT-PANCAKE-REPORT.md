# EMIT-PANCAKE REPORT — the generator that emits Pancake from a primitive description

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900, Ubuntu) for `cake`/`cc`;
local (Lean 4.17.0) for the generator. **Status: DONE for region + machine —
the region emitter reproduces C0's hand-written `boundscan.pnk` and compiles to a
`.S` that is BYTE-IDENTICAL to C0's; the machine emitter generates a second
distinct primitive that `cake` compiles and whose runs match its Lean spec. Zero
sorries, zero axioms in the generator.**

## Verdict in one paragraph

C0 hand-wrote `pnk/boundscan.pnk` and dual-emitted it (Lean SPEC ↔ Pancake IMPL).
EMIT-PANCAKE removes the "hand-wrote": a Lean function `emitRegion : RegionSpec →
PFun` (in `Dsl/EmitPancake.lean`) now *generates* that Pancake from a declarative
spec — the control-block layout, the digest-fold constants, the FFI names — with
no program text baked into the spec. The proof that the emission is generative,
not a disguised copy, is the strongest available: the generated `region.pnk` is
code-identical to C0's hand-written `boundscan.pnk` (modulo whitespace and one
redundant paren), and when compiled with the same `cake --pancake` it produces a
`region.S` that is **`cmp`-identical, byte for byte, to C0's `boundscan.S`**, and
runs the **identical eight-vector column** C0 recorded. A second emitter,
`emitMachine : MachineSpec → PFun`, generates a different primitive — a guarded
threshold token-scan FSM — that `cake` also compiles and whose four test runs
match the Lean model `tokenScanSpec` exactly. The whole generator is total,
core-Lean, `#print axioms`-empty; a malformed emission cannot yield a well-typed
`PFun`. What this is: the emission *mechanism*, proven generative on the two
primitives that have (region) or are scaffolded toward (machine) their Link-A
refinement. What it is not: the refinement theorem for the emitted machine loop —
that remains C0/C1's priced multi-day item, unchanged and restated in §5.

---

## 1. What was built

`Dsl/EmitPancake.lean` — self-contained, core Lean 4.17.0 (no `import Lean`, no
Mathlib, no `partial`, no `sorry`). Three layers:

1. **A Pancake AST as a Lean datatype.** `PExpr` / `PStmt` / `PFun` model the
   *subset* of Pancake concrete syntax the primitives use — exactly the subset C0
   exercised and C1 proved the bounds-`If` of: `@base` / `Const` / `Var`, the
   operators `+ * < &`, `lds`/`ld8` loads, and the statements
   `var`/assign/`if`/`while`/`st`/`@ffi`/`return`. Not the whole language; the
   honest emission surface.
2. **A total pretty-printer** `ppFun : PFun → String` to Pancake concrete syntax.
   Structural, terminating (all recursion on strict subterms). Parenthesisation
   is minimal-but-correct: binop operands are wrapped except same-op children of
   an associative parent (so `add (add a b) c` prints `a + b + c`), and **loads
   are wrapped in operand position** (`a + (ld8 x)`, not `a + ld8 x`) — a fact
   discovered against the real parser (§3, the parse-error finding).
3. **The two emitters.** `emitRegion`/`emitMachine` take a spec and build a
   `PFun`. The program *structure* lives in the emitter; every *constant and
   name* lives in the spec, so re-laying-out the control block or changing the
   fold is a spec edit, not an emitter edit.

Companion: `tokenScanSpec` — the machine's Lean SPEC, in the same file, so one
`MachineSpec` drives both the model and the `.pnk` (the dual-emission shape).

**Footprint:** `#print axioms` on `ppExpr`, `ppStmt`, `emitRegion`,
`emitMachine`, `regionPnk`, `firstBelow`, `tokenScanSpec` — all report *does not
depend on any axioms* (empty ⊂ the allowed `{propext, Quot.sound,
Classical.choice}`). The file typechecks warning-free under
`leanprover/lean4:v4.17.0`.

## 2. The generated sources

`lean --run Dsl/EmitPancake.lean` writes `emit/region.pnk` and `emit/machine.pnk`.

**`emit/region.pnk`** (generated body; banner elided):

```
fun main() {
  var base = @base;
  var buf = base + 32;
  @load_vec(base, 24, buf, 4096);
  var alen = lds 1 base;
  var off = lds 1 (base + 8);
  var len = lds 1 (base + 16);
  var result = 0;
  if alen < (off + len) {
    result = 4294967295;
  } else {
    var acc = 0;
    var i = 0;
    while i < len {
      acc = ((acc * 31) + (ld8 (buf + off + i))) & 16777215;
      i = i + 1;
    }
    result = acc;
  }
  st base + 24, result;
  @report_vec(base + 24, 8, base, 8);
  return 0;
}
```

Diffed against C0's hand-written `pnk/boundscan.pnk` with comments and blank
lines stripped and runs of spaces collapsed: **code-identical**. The only
residual differences are cosmetic whitespace alignment (`var off  =` vs
`var off =`) that the collapse normalises away.

**`emit/machine.pnk`** (generated body):

```
fun main() {
  var base = @base;
  var buf = base + 32;
  @load_vec(base, 24, buf, 4096);
  var len = lds 1 (base + 16);
  var i = 0;
  var found = 0;
  while (i < len) & (found < 1) {
    var b = ld8 (buf + i);
    if b < 32 {
      found = 1;
    } else {
      i = i + 1;
    }
  }
  var result = i;
  st base + 24, result;
  @report_vec(base + 24, 8, base, 8);
  return 0;
}
```

A genuinely different shape from the region fold: an *early-terminating* guarded
`while` with a data-dependent `if` in the loop body, yet using no operator C0 has
not compiled. It scans the viewed bytes for the first byte strictly below a
threshold (32 = first control character) — a token/delimiter FSM whose output is
the first delimiter index, or `len` if none.

## 3. The cake build and the tri-kernel agreement (region)

On hbox, released `cake` at `~/r05/cake-x64-64/cake`, same driver
(`basis_ffi.c` + `boundscan_ffi.c`) C0 used:

```
cake --pancake < region.pnk > region.S     # exit 0, 10340 bytes
cc -O2 region.S basis_ffi.c boundscan_ffi.c -lm -o region
cmp region.S ~/c0/boundscan.S              # -> IDENTICAL (byte for byte)
```

`region.S` is **byte-identical to C0's `boundscan.S`** — the generated source
compiled, through the verified backend, to literally the same machine code. The
eight adversarial vectors (arena = `GET / HTTP/1.1\r\n`):

| off | len | in-bounds? | Lean `encode(boundScan)` (C0) | **generated-region x64** |
|----:|----:|:--:|--:|--:|
| 0  | 16 | yes (exact fit)  | 14695237   | **14695237** |
| 0  | 3  | yes              | 70454      | **70454** |
| 4  | 10 | yes              | 12467326   | **12467326** |
| 14 | 2  | yes (boundary)   | 413        | **413** |
| 0  | 17 | **no** (one past)| 4294967295 | **4294967295** |
| 16 | 1  | **no** (off end) | 4294967295 | **4294967295** |
| 10 | 8  | **no** (straddle)| 4294967295 | **4294967295** |
| 16 | 0  | yes (empty end)  | 0          | **0** |

Identical to C0's column — necessarily so, since the `.S` is identical. This is
C0's tri-kernel round-trip re-established with the *source generated*, not
hand-authored: **Lean model → generator → Pancake → verified backend → x64 →
correct output**, and the last four arrows are C0's, unchanged.

**The parse-error finding.** The first generated `region.pnk` failed
`cake --pancake` with `### ERROR: parse error / Not combinator failed`. Cause:
`cake`'s Pancake parser rejects a **load in bare operand position** —
`(acc * 31) + ld8 (buf + off + i)` does not parse; `(acc * 31) + (ld8 (buf + off
+ i))` does. C0's hand-written source had the extra parens and so never exposed
this; the generator did, because a generator emits exactly what its rule says.
The pretty-printer's `wrapOperand` now wraps `lds`/`ld8` children unconditionally
in operand position — a rule that is now *in the generator*, checked by the real
parser, not tribal knowledge in a human's head. (This is the emission analogue of
C1's "the comparison is signed" finding: paying the mechanism, not resting on a
hand-written twin, surfaces the real constraint.)

## 4. The cake build and the model agreement (machine)

```
cake --pancake < machine.pnk > machine.S   # exit 0, 10340 bytes
cc -O2 machine.S basis_ffi.c boundscan_ffi.c -lm -o machine
```

Runs vs the Lean model `firstBelow 32 (arena.extract 0 L) L 0` (first control
byte is `\r` = 13 at index 14):

| len (view) | compiled `machine` | Lean model | agree |
|----:|--:|--:|:--:|
| 16 | 14 | 14 | ✓ (finds `\r` at 14) |
| 14 | 14 | 14 | ✓ (no control byte in `[0,14)` → returns `len`) |
| 10 | 10 | 10 | ✓ |
| 3  | 3  | 3  | ✓ |

The generated machine compiles and behaves as its Lean spec says on every tested
length. This is behavioural agreement (kernel-checked testing), **not** a
refinement theorem — see §5.

## 5. Honest scope: what generates vs what is scaffolded

- **Region primitive: generates AND has its refinement path.** `emitRegion`
  reproduces the exact program C0 dual-emitted and C1 proved the bounds-`If` of
  against real `panSem`. So for region the emission is generative *and* the
  front-end obligation is (bounds) paid / (scan loop) priced exactly as C1 left
  it. Emission adds nothing to the proof cost and subtracts the hand-authoring.
- **Machine primitive: generates, refinement scaffolded/priced.** `emitMachine`
  produces valid, compiling, behaviourally-correct Pancake, and its Lean SPEC
  (`tokenScanSpec`) is in-hand. Its Link A — a Hoare-style loop-invariant proof
  over `panSem`'s clocked `While` (`i` monotone, `found` a one-shot latch, the
  postcondition "`result` = first-below index") plus the `ld8` memory relation —
  is **not** discharged here. It is the same shape as C0 §4-A-2/3, the multi-day
  item; the machine's early-terminating guard adds a second loop-exit disjunct to
  the invariant but no new *kind* of obligation.
- **The other three primitives (linear · shared · reactor): scaffold, contract
  stated.** They are not emitted here. The **emission contract** each must meet:
  a `<Prim>Spec` structure (constants + names only), a `emit<Prim> : <Prim>Spec →
  PFun` whose body is fixed structure, a Lean SPEC function in the same file so
  the spec dual-drives model and `.pnk`, and a `cake --pancake` green build as
  the parser gate. Linear (lease acquire/use/release-once) and reactor (the
  RingEvent→RingSubmission copy-once loop) will each introduce their own
  operand-position parser constraints — discovered the same way region's load-
  paren rule was — and their own Link-A loop/state obligations priced per C0/C1.

## 6. The generalization plan

1. **AST coverage grows by need, gated by the parser.** Each new primitive adds
   only the `PExpr`/`PStmt` constructors it uses; the pretty-printer's `cake`
   build is the acceptance test that the emitted syntax is real. The load-paren
   fix (§3) is the template: a parser rejection becomes a pretty-printer rule,
   permanently, in the generator.
2. **Spec/emitter split stays strict.** Structure in the emitter, constants and
   names in the spec. This is what makes "reproduces the hand-written program"
   provable (region) and what lets one spec dual-drive model + `.pnk`.
3. **The DSL macro calls the emitters.** `Dsl/Engine.lean`'s `engine … where …
   emit … cakeml` clause elaborates each declared primitive to its `<Prim>Spec`
   and calls `emit<Prim>`, then renames the per-primitive `main` and links the
   functions into one `.pnk` module. (Standalone emission here uses `main` as the
   entry because the Pancake basis invokes `main`; composition renames.)
4. **Refinement composes per C0/C1, not per emission.** Emission is free of proof
   cost; the recurring tax is Link A per looping primitive (loop invariant +
   memory relation), inherited unchanged from C0/C1. The generator does not make
   the refinement cheaper — it makes the *source* trustworthy-by-construction and
   removes hand-authoring drift between the model and the emitted program.

## 7. Files

- `Dsl/EmitPancake.lean` — the generator: AST, pretty-printer, `emitRegion`,
  `emitMachine`, `tokenScanSpec`, and `main` (writes the `.pnk` files). Core
  Lean 4.17.0, axiom-free, warning-free, no `sorry`.
- `docs/engine/probes/compiler/emit/region.pnk` — generated; code-identical to
  `pnk/boundscan.pnk`; compiles to a `.S` byte-identical to C0's.
- `docs/engine/probes/compiler/emit/machine.pnk` — generated; compiles; matches
  `tokenScanSpec`.

## 8. Reproduce

```
# generator: typecheck + emit (local, Lean 4.17.0)
elan run leanprover/lean4:v4.17.0 lean Dsl/EmitPancake.lean          # clean
elan run leanprover/lean4:v4.17.0 lean --run Dsl/EmitPancake.lean    # writes emit/*.pnk

# cake build + run (hbox), region:
scp docs/engine/probes/compiler/emit/region.pnk hbox@hbox.local:~/emitpnk/
ssh hbox@hbox.local 'cd ~/emitpnk && ~/r05/cake-x64-64/cake --pancake < region.pnk > region.S \
  && cc -O2 region.S basis_ffi.c boundscan_ffi.c -lm -o region \
  && cmp region.S ~/c0/boundscan.S \
  && for v in "0 16" "0 3" "4 10" "14 2" "0 17" "16 1" "10 8" "16 0"; do set -- $v; OFF=$1 LEN=$2 ./region; done'
# machine: same, then: for L in 16 14 10 3; do OFF=0 LEN=$L ./machine; done
```
(`basis_ffi.c` + `boundscan_ffi.c` copied from `~/c0`; both are outside any
refinement theorem — the FFI TCB residual C0 §4 named, unchanged.)

## 9. Bottom line

The Pancake emission is generative, not hand-authored, and the proof is a
byte-identical `.S`: the region primitive's compiled machine code is *literally
the same* whether C0 typed it or `emitRegion` produced it. A second, structurally
different primitive (the machine FSM) generates and runs correctly against its
Lean spec. The mechanism — AST + total pretty-printer + spec-driven emitters,
axiom-free in the Lean kernel, gated by the real `cake` parser — is the piece the
DSL's `emit cakeml` clause plugs into. The refinement cost is unchanged from
C0/C1 (backend inherited, front-end loop-invariant per primitive); what emission
buys is that the source the backend consumes is now generated from the same spec
as the model, with no hand-authoring seam between them.
