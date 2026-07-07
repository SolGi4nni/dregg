# C5 REPORT — a REAL engine primitive is now emitted + Link-A-proven: the Arena request-line SP scan (parseRequestLine's find-first-delimiter hot path), not a toy counter

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900) for HOL4/CakeML; drorb (Lean) for the model kernel.
**Status: DONE — the request-line find-first-SP scan is emitted to Pancake, compiled, run on real request-line vectors (agrees with the Lean parser), AND Link-A-proven end to end against real `panSem`.** One HOL4 theory (`hol-c5/arenaScanLinkAScript.sml`), thirteen kernel-checked theorems, every one `[oracles: DISK_THM] [axioms: ]`, `axioms "arenaScanLinkA" = 0`. Clean from-scratch rebuild: `machineStepLinkATheory [1/3] OK`, `machineLoopLinkATheory [2/3] OK`, `arenaScanLinkATheory [3/3] OK`.

## Verdict in one paragraph

C0–C4 proved the emission+preservation mechanism (single-transition Link A, the loop-invariant induction over the clocked `While`, the whole-program frame) on a **toy** saturating-counter FSM. C5 scales it to a **REAL engine component**: the find-first-SP loop of `Arena/Parse.lean parseRequestLine` — `findByteIdx SP line = line.findIdx? (· == 32)`, the scan that splits `"method SP target SP HTTP/x"` at the first space (RFC 9112 §3). This is not the counter: the loop **branches** in its body (on SP: record the offset; else: advance), it **early-exits** the instant it sees the delimiter (a compound guard `i < len && found == 0` — the first genuinely non-total scan the probes have handled), and its result is an **offset** — exactly the `i₁` the Lean parser records as the method length. The emitted `.pnk` compiles with `cake`, runs on real request lines (`GET / HTTP/1.1` → 3, …), and agrees with the Lean parser on all nine vectors; and `scanLoop_refines_findSp` proves — against real `panSem$evaluate` — that the emitted `While` computes **exactly** the Lean spec `scanSp` (the HOL twin of `findByteIdx SP`) for **all** inputs. The C3 loop-invariant skeleton, the C3 byte-memory `memRel` LoadByte relation, `w2w_byte`, `fix_clock_id`, `Seq_NONE`, and C2's `signed_lt_n2w64` are opened and reused **verbatim**; what is new is the branching body + two-mode exit.

---

## 1. What was emitted, compiled, and RAN (Kernel 2, observed)

`pnk/arenascan.pnk` — the scan loop, transcribed from `parseRequestLine`'s
`findByteIdx SP`:

```
fun main() {
  var base = @base;  var buf = base + 32;
  @load_line(base, 24, buf, 4096);          // $LINE -> buffer; len at base+16
  var len = lds 1 (base + 16);
  var i = 0;  var found = 0;  var b = 0;
  while (i < len && found == 0) {            // scan while in-range AND not found
    b = ld8 (buf + i);
    if b == 32 { found = 1; }                // SP at offset i -> record, exit
    else { i = i + 1; }                      // advance
  }
  st base + 24, i;                           // the first-SP offset (== len if none)
  @report_off(base + 24, 8, base, 8);
  return 0;
}
```

Compiled `cake --pancake < arenascan.pnk` (exit 0, 244-line `.S`), linked
`cc -O2 arenascan.S basis_ffi.c arenascan_ffi.c -o arenascan -lm`, and RUN on
request-line vectors. Observed output (quoted), against the REAL Lean parser run
with `lake env lean` over drorb's `Arena/Parse.lean`:

| vector (`LINE`) | Pancake `./arenascan` | Lean `findByteIdx SP` | Lean `parseRequestLine` method span |
|---|---|---|---|
| `"GET / HTTP/1.1"` | `3` | `3` | `method=(0,3)` |
| `"POST /submit HTTP/1.1"` | `4` | `4` | `method=(0,4)` |
| `"GET /path"` | `3` | `3` | `none` (not a full req-line) |
| `"DELETE /a/b/c?q=1 HTTP/2"` | `6` | `6` | `method=(0,6)` |
| `"NOSPACE"` | `7` | `7` (= len) | `none` |
| `""` | `0` | `0` (= len) | `none` |
| `" leading"` | `0` | `0` | `none` |
| `"X / HTTP/1.1"` | `1` | `1` | `method=(0,1)` |
| `"A  B"` | `1` | `1` (first SP) | `none` |

All nine agree. Where the line is a well-formed request line, the offset equals the
**method span length** `parseRequestLine` records (`off=0`, `len = SP-offset`) — the
emitted scan IS the `method|target` split point. Full table + reproduce lines:
`run/arenascan_vectors.txt`.

## 2. What was PROVEN (Kernel 3 — Link A against real `panSem`)

Theory `arenaScanLinkA` builds green against the just-built `panSemTheory` +
`panLangTheory`, CakeML `ed31510b3`, HOL4 Trindemossen 2. It **opens and reuses C2
and C3 verbatim**: `machineStepLinkATheory` (`signed_lt_n2w64`) and
`machineLoopLinkATheory` (`memRel`, `w2w_byte`, `fix_clock_id`, `Seq_NONE`) are
build dependencies. Full statements + tags: `hol-c5/verify_out.txt`.

**The Lean spec, re-declared in HOL** (byte-identical to `findByteIdx SP = List.findIdx? (· == 32)`):
```
scanSp []        = NONE
scanSp (b::bs)   = if b = 32 then SOME 0
                   else case scanSp bs of NONE => NONE | SOME j => SOME (SUC j)
```

**The emitted guard AST** — the EXACT term `panPtreeConversion` produces for `&&`
(each conjunct normalised through `Cmp NotEqual (Const 0w) _`, `==` → `Cmp Equal`,
`<` → `Cmp Less`):
```
scanGuard = Op And [ Cmp NotEqual 0w (Cmp Less  «i»   «len») ;
                     Cmp NotEqual 0w (Cmp Equal «found» 0w) ]
```

| theorem | what it says (all `[oracles: DISK_THM] [axioms: ]`) |
|---|---|
| `eval_scanGuard` | real `panSem$eval` of the compound guard = `1w` **iff** `i < len ∧ found = 0` — the `&&` desugaring's `NotEqual 0w` wrappers are idempotent on `{0w,1w}`, `Op And` is the logical and. |
| `eval_scan_loadbyte` | `ld8 (base + i)` returns the i-th model byte (reuses C3 `memRel` + `w2w_byte`). |
| `evaluate_scanBody` | one iteration: reads the byte, then **branches** — on SP `found := 1` (i held), else `i := i+1` — preserving the clock and re-establishing `scanInv` at the branch-appropriate `(i, found)`. |
| `scanLoop_unfold` | one clocked-`While` iteration reduces `evaluate (scanLoop, s)` to `evaluate (scanLoop, s2)`, one clock spent (C3 `machineLoop_unfold` shape, with the branch). |
| `scanLoop_scan_bounded` | the **loop-invariant induction**: from any invariant state, the emitted `While` terminates (no `TimeOut`) with `«i»`/`«found»` witnessing the scan — either `found=1` at the first-SP offset, or `found=0` with `i=|input|`. |
| **`scanLoop_refines_findSp`** | **THE HEADLINE Link A** — from a fresh `(i=0, found=0)` state with `clock ≥ |input|`: `∃s'. evaluate (scanLoop, s) = (NONE, s') ∧ case scanSp input of NONE ⇒ («found»=0w ∧ «i»=|input|) | SOME j ⇒ («found»=1w ∧ «i»=j)`. The emitted `While` computes **exactly** the Lean `findByteIdx SP`. |

The invariant `scanInv` **reuses C3's `memRel`** (the byte-memory LoadByte relation)
verbatim and adds the scan-specific facts: the scanned prefix has no SP
(`EVERY (λb. b ≠ 32) (TAKE i input)`), and `found = 1 ⇒ EL i input = 32`. The
soundness of the result then follows from two spec lemmas (`scanSp_found`,
`scanSp_none`), themselves kernel-checked.

## 3. Why this is a REAL primitive, not the toy (the honest delta from C2/C3/C4)

- **The body branches.** C2/C3 ran a uniform per-byte step (`stepBody`, same action
  every iteration). Here the body is `if b == SP then found:=1 else i:=i+1` — the
  invariant transition is genuinely two-way, and the induction re-establishes
  `scanInv` at *different* `(i, found)` per branch.
- **The loop early-exits.** C3's `machineLoop` always ran to `i = len`. This scan
  stops the instant it sees the delimiter, via a **compound guard**
  `i < len && found == 0`. Proving that guard meant handling the real Pancake `&&`
  desugaring (`Op And` over `Cmp NotEqual 0w`-wrapped comparisons) and a two-mode
  termination (found the SP / ran off the end), both new to C5.
- **The result is the parser's actual output.** `«i»` at exit is the method-length
  split point `parseRequestLine` records — a data-dependent offset that feeds the
  rest of the parse, not a counter read.

## 4. Standing boundaries (carried, none new, none an open research item)

Exactly the residuals C4 named, unchanged:
1. **FFI-oracle linkage.** `@load_line` is elided; `scanInv`'s `memRel` is *assumed*
   (the input is in the buffer). Connecting `memRel` to the actual `ExtCall`
   semantics (`read_bytearray`/`write_bytearray`/endianness) is the standing item.
2. **Parser faithfulness.** `scanGuard`/`scanBody`/`scanLoop` are the `.pnk`
   transcribed into the `panLang` AST by hand (not derived by running
   `panPtreeConversion` on `arenascan.pnk`). The compiled binary's agreement on
   nine vectors (§1) is independent evidence the transcription is faithful, but it
   is not a proof. The `«b»` slot is pre-declared before the loop (`var b = 0;`)
   rather than `Dec`'d per iteration, matching the `Assign`-to-existing-local AST.
3. **Link B (`pan_to_target`).** Inherited from the CakeML tree
   (`pan_to_target_compile_semantics`, `check_thm`'d) — the cited half, not re-done.

## 5. How many of the engine's real primitives now have the mechanism — and the distance to full-engine emission

**Real engine components now emitted + Link-A-proven: two.** (i) the Arena
bounds/region decision (`boundScan`, C0/C1 — a single bounds `If`); (ii) the Arena
request-line SP scan (C5 — a full branching/early-exit `While`, end to end). The
counter FSM (C2/C3/C4) is the toy that paid for the *mechanism* (single step, loop
induction, whole-program frame) those two real components now instantiate.

**Distance to the full request-head parser** (`Arena/Parse.lean`): the remaining
real components are all instances of the **same** mechanism (`scanInv`-style
invariant + the C3 loop skeleton + `memRel`), differing only in guard/body:
- `findDoubleCrlf` — a 4-byte-window scan for `CRLFCRLF` (same `While`, wider guard);
- `crlfPositions` / `segments` — scan-and-collect CRLF offsets (a scan that pushes,
  not one that stops);
- `parseHeaderLine` — a `COLON` find-scan (identical to C5 with delimiter 58) + two
  OWS `takeWhile` trims (find-first-non-OWS scans, C5's shape);
- `canonNameEntry` — a per-byte lowercasing **map** (a scan that writes, not reads);
- the `parseRequestLine` **field-split composition** — two *more* `findByteIdx SP`
  scans at shifted offsets (this exact theorem, re-instantiated) + `startsWithHttpSlash`
  (a fixed-window constant-index byte compare, C1's bounded-read shape) + offset
  arithmetic to assemble the three spans.

**Is any of that open research? No.** Every remaining request-head component is a
bounded byte-list fold/scan/map — the loop-invariant induction over the clocked
`While` (the per-primitive long pole) is **paid**, in C3, and reused here; each new
component owes a small, mechanical guard/body change, not new proof technique. The
only substantive standing residual across all of them is the single FFI-oracle
linkage (§4.1) and the inherited Link-B instantiation (§4.3) — both named since C4,
both bounded, neither an open proof-research item.

So the state of **"the full arena parser is emitted + preservation-proven"**: the
hot path (the find-first-delimiter scan) is CLOSED end to end against real `panSem`,
kernel-checked, clean footprint, and RUN against the real Lean parser; what stands
between that and the whole request-head parser is a handful more instances of the
same mechanism (mechanical) plus the two named, inherited boundaries.

## 6. Files (under `docs/engine/probes/compiler/`)

- `hol-c5/arenaScanLinkAScript.sml` — the theory: `scanSp`/`scanGuard`/`scanBody`/
  `scanLoop`/`scanInv`, the guard/body/iteration lemmas, the induction, and
  `scanLoop_refines_findSp`. Opens and reuses `machineStepLinkATheory` (C2) and
  `machineLoopLinkATheory` (C3, incl. `memRel`).
- `hol-c5/Holmakefile` — `INCLUDES` for the CakeML `pancake`, `pancake/semantics`,
  `compiler/backend`, `compiler/encoders/asm`, `misc`, `semantics/ffi` dirs.
- `hol-c5/verify_out.txt` — full theorem statements + `[oracles]`/`[axioms]` tags +
  the `axioms = 0` footprint audit.
- `pnk/arenascan.pnk`, `pnk/arenascan_ffi.c` — the emitted Pancake + its FFI driver.
- `run/arenascan_vectors.txt` — the two-kernel vector table + reproduce lines.

## 7. Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 at `~/src/HOL`, in a work
dir holding `Holmakefile`, `machineStepLinkAScript.sml` (C2),
`machineLoopLinkAScript.sml` (C3), `arenaScanLinkAScript.sml` (C5):
```
export CAKEMLDIR=$HOME/src/cakeml
export PATH=$HOME/src/HOL/bin:$PATH
Holmake arenaScanLinkATheory.uo      # builds C2, C3, then C5, green (~16 s)
```
Kernel 2 (the compiled scan): see §1 / `run/arenascan_vectors.txt`. Kernel 1 (the
Lean parser): `lake env lean --run` over a file importing `Arena.Parse` in drorb
(`Arena/Parse.olean` prebuilt).

## 8. Bottom line for Phase C

C3 paid the loop-induction long pole on a toy; C5 shows that pole was the real cost:
a genuine engine primitive — the request-line find-first-SP scan, the hot path of
`parseRequestLine` — is now **emitted, compiled, run against the real Lean parser,
and Link-A-proven** to compute exactly `findByteIdx SP`, with a clean kernel
footprint, by **reusing C3's induction skeleton + `memRel` verbatim** and adding
only the branching body and early-exit guard. The remaining request-head components
are more instances of the same mechanism — mechanical, not research — over one
standing FFI-oracle residual and the inherited Link-B half.
