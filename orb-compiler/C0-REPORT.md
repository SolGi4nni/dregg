# C0 REPORT — the verified-compiler seed: one primitive, dual-emitted, and an honest preservation-obligation price

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900, Ubuntu 24.10) for cake/HOL4;
local for Lean. **Status: PROBE DONE — real dual-emission end to end; preservation
theorem SCOPED, not proven (honestly).**

## Verdict in one paragraph

The `region`/`view` arena bounds-check + total byte-scan (ADR-7's primitive
reduced to its smallest honest core) now exists as **one Lean SPEC and one
Pancake IMPLEMENTATION that agree, byte for byte, in three independent
kernels**: (1) the Lean model compiled native, (2) HOL4 `EVAL` as
kernel-checked theorems, (3) **actual x64 machine code produced by the verified
CakeML/Pancake backend** (`cake --pancake`, 2026-06-18 release), linked with
`cc` and run. All eight adversarial vectors — interior, exact-boundary,
one-past-the-end, empty-at-end — produce the identical digest or the identical
out-of-bounds sentinel. This is P2's dual-kernel behavioral round-trip
**upgraded to a tri-kernel round-trip whose third kernel is the real machine**,
and it is the concrete "proven-AND-compiled" artifact the probe was asked to
produce. What it is **not**: the preservation *theorem*. That theorem factors
cleanly into a backend link that **already exists as a kernel-checked HOL4
theorem in the CakeML tree** (`pan_to_target_compile_semantics`) and a
front-end link that is the genuine, unpaid cost — a loop-invariant refinement
over `panSem$evaluate` plus a memory-model relation — whose price this report
itemizes against P2's eight conditions. Neither link is research-shaped; the
front-end link is real proof-engineering (est. multi-day for even this 40-line
program) and was **not** discharged here. That honest split — dual-emission
works today, the refinement theorem is priced not paid — is the deliverable.

---

## 1. The primitive and why this one

The DSL's `region`/`view` (ADR-7) is a flat immutable byte region plus a typed
`(off, len)` view. drorb's `Arena/Basic.lean` `Store.resolve` is exactly this:
it returns the viewed slice **iff** the view is in-bounds of its arena
(`Store.Wf`), else `none`. C0 takes that shape, specialized to one arena and
with a concrete total fold standing in for "return the slice":

> **`boundScan a off len`** = `some digest` if `off + len ≤ a.size`, else
> `none`; where `digest` is the rolling checksum `acc := (acc*31 + b) mod 2^24`
> over the viewed bytes.

The `mod 2^24` fold is deliberately the same one R05's H1 kernel used — it
defeats dead-code elimination and doubles as a cross-kernel correctness witness
(a wrong byte, wrong order, or wrong bound changes the digest). The single-word
result encoding `encode : Option UInt32 → UInt32` maps `none ↦ 0xFFFFFFFF` and
`some k ↦ k`; sound as an injection because every in-bounds digest is `< 2^24`,
so the sentinel is unreachable as a success value.

Why this primitive and not R05's full H1 loop: R05 was a **perf** probe (it
measured cycles/byte and did not care whether the compiled code matched a Lean
model). C0 is a **preservation** probe. The bounds-check + scan is the smallest
program that still contains all the parts a refinement proof must handle — a
data-dependent `If` (the bounds check), a `While` loop with an accumulator
invariant, a byte `LoadByte`/`ld8` from memory, and word arithmetic — so the
obligation it induces is representative, not a toy `x+1`.

## 2. Files (all under `docs/engine/probes/compiler/`)

- `model/BoundScan.lean` — the SPEC. Self-contained, Lean core only, no
  Mathlib. `#print axioms C0.boundScan` = `{propext, Quot.sound}` (a strict
  subset of the allowed `{propext, Quot.sound, Classical.choice}`; the model
  does not even need choice). Total by construction (structural fuel recursion,
  no `partial`).
- `pnk/boundscan.pnk` — the IMPLEMENTATION, 40 lines of Pancake. `Dec`/
  `Assign`/`If`/`While`/`StoreByte`/`Return` over `ld8` (`LoadByte`) and word
  ops `& 16777215`, `* 31`, `+`, `<`.
- `pnk/boundscan_ffi.c` — the trusted FFI driver (`@load_vec` writes
  `[arena_len, off, len]` and the fixed 16-byte arena; `@report_vec` prints the
  result word). This is **outside** any preservation theorem — see §4, the TCB.
- `hol/boundScanScript.sml` — the HOL4 transcription + 8 `EVAL_TAC` vector
  theorems. `Holmake` green (`boundScanTheory ... OK`), all 8 kernel-checked.
- `run/lean_vectors.txt`, `run/pancake_vectors.txt` — the raw runs.

## 3. The dual emission and the tri-kernel agreement (deliverable 1)

Compilation on hbox with the released `cake` (CakeML `ccfc23cb`, HOL4
`d4560227`, 2026-06-18):

```
cake --pancake < boundscan.pnk > boundscan.S     # 10,340 bytes of .S, sub-second
cc -O2 boundscan.S basis_ffi.c boundscan_ffi.c -lm -o boundscan
```

The three kernels, all eight vectors, arena = `GET / HTTP/1.1\r\n` (16 bytes):

| off | len | in-bounds? | Lean `encode(boundScan)` | HOL4 `EVAL` theorem | **compiled Pancake x64** |
|----:|----:|:--:|--:|--:|--:|
| 0  | 16 | yes (exact fit) | 14695237 | `vec_0_16` ✓ | **14695237** |
| 0  | 3  | yes | 70454 | `vec_0_3` ✓ | **70454** |
| 4  | 10 | yes | 12467326 | `vec_4_10` ✓ | **12467326** |
| 14 | 2  | yes (boundary) | 413 | `vec_14_2` ✓ | **413** |
| 0  | 17 | **no** (one past) | 4294967295 | `vec_0_17` ✓ | **4294967295** |
| 16 | 1  | **no** (off at end) | 4294967295 | `vec_16_1` ✓ | **4294967295** |
| 10 | 8  | **no** (straddles) | 4294967295 | `vec_10_8` ✓ | **4294967295** |
| 16 | 0  | yes (empty at end) | 0 | `vec_16_0` ✓ | **0** |

Three kernels, one column of answers. The HOL4 side is genuine kernel-checked
computation (not a test harness); the machine side is the output of the
verified backend running on real silicon. The boundary trio — `(14,2)` succeeds
(off+len = size), `(16,1)` fails, `(16,0)` succeeds with the empty digest — is
where an off-by-one in the bounds predicate would show, and all three kernels
agree on it.

**Honesty about what this is.** Agreement on eight vectors is *kernel-checked
testing*, exactly as P2's layer-3 round-trip is testing. It is strong evidence
(and it caught nothing wrong this time because the program is small and was
written carefully), but it is **not** the refinement theorem. The theorem is §4.

## 4. The preservation obligation, stated precisely (deliverable 2)

Let `p` = the panLang program `cake` parsed from `boundscan.pnk` (entry
`«main»`), and let `M` = the x64 machine code in `boundscan.S` with config `c'`,
as produced by `compile_prog p`. Let `σ` be an initial machine state whose
memory encodes an arena `a : Array UInt8` at `buf` and the control block
`[|a|, off, len]` in the agreed layout.

> **Preservation obligation (C0).** For every such `σ`, running `M` from `σ`
> terminates (within the resource limit) in a state whose result word at
> `base+24` equals `encode (boundScan a off len)`.

This factors across the ADR-3-REV bridge into two links.

### Link B — backend refinement. **INHERITED; already a kernel-checked HOL4 theorem.**

`pancake/proofs/pan_to_targetProofScript.sml:1256`,
**`pan_to_target_compile_semantics`** (`check_thm`'d at line 2501):

```
compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) ∧
pancake_good_code pan_code ∧ … (config/heap/memory hypotheses) …
semantics_decls s «main» pan_code ≠ Fail
⇒ machine_sem mc ffi ms ⊆
     extend_with_resource_limit'
       (option_lt stack_max (SOME (FST (read_limits …))))
       {semantics_decls s «main» pan_code}
```

In words: **every x64 machine behaviour of the emitted code is contained in the
behaviours the panLang *source semantics* prescribes**, modulo a resource limit
(OOM/stack — the `extend_with_resource_limit'`). This is the entire
CakeML/Pancake verified-backend guarantee, and it is precisely what deletes
`leanc`, `gcc`'s optimizer, and cake's own code generation from the TCB
(ADR-3-REV's whole point): we do **not** trust the compiler; this theorem
discharges it. Link B for C0 is *instantiating* this theorem at our `pan_code`
and config — a checking obligation (verify the `pancake_good_code` /
`distinct_params` / heap side-conditions hold for our program), not a new proof.

**TCB residual even with Link B (named, not hidden):** the x64 target ISA
model/encoding (`asm`/`lab_to_target` target semantics — trusted against real
hardware), and **the FFI**: `basis_ffi.c` + `boundscan_ffi.c`
(`@load_vec`/`@report_vec`) sit entirely outside the theorem, exactly as all
CakeML FFI does. In C0 the FFI *is* the arena-encoding oracle, so a faithful
whole-system claim would additionally owe a spec for those two C functions.
That is the honest boundary; the theorem is about the compiled Pancake, not the
C shim around it.

### Link A — front-end refinement. **NEW; the real cost; NOT discharged here.**

Link B connects machine code to *panLang source semantics*
(`semantics_decls s «main» pan_code`). It says nothing about our Lean SPEC. Link
A closes that gap:

> **Link A (C0).** `semantics_decls s «main» pan_code`, evaluated on the `σ`
> encoding `(a, off, len)`, returns a result word equal to
> `encode (boundScan a off len)`.

This is a statement half in HOL4 (`panSem$evaluate` / `semantics_decls`,
`pancake/semantics/panSemScript.sml`) and half in Lean (`boundScan`). The
ADR-3-REV bridge is how they meet: **reflect `panSem`'s `evaluate`/`eval`/
`mem_load_byte` definitions into Lean by P2's exporter** (checked at P2's three
kernel-checked layers), then prove Link A **in one logic (Lean, where the swarm
and its fluency are)** against the reflected semantics; it composes with Link B
across the definitional translator — the CR-2 ledger row P2 priced. Proving
Link A for this specific program requires, piece by piece:

1. **The bounds `If`.** `eval s (alen < off+len)` decides the branch; the
   out-of-bounds arm stores `0xFFFFFFFF` and returns → matches `boundScan = none`,
   `encode = 0xFFFFFFFF`. Pure `eval` over `Cmp`/`Op`; a **few-line proof,
   tractable today**. (This is the small instance I *could* have closed; see §6.)
2. **The scan `While`.** The loop invariant
   `acc = scanFrom a off i 0 ∧ pos = off+i ∧ i ≤ len`, maintained across the
   `While e c` clause of `evaluate` (`panSemScript.sml:523`), discharged by
   induction on `len − i` with the panSem clock. **This is P2 §5 condition #1**
   (recursive / mutually-recursive definition emission — `evaluate` is the
   clocked mutually-recursive function; its `While` clause is what a loop proof
   unfolds). Recipe known (clock+measure induction, the standard CakeML
   While-loop reasoning); acceptance gate unchanged (the stored `evaluate`
   equations must reflect by `rfl`/`simp`, so a wrong translation cannot pass
   silently). **Engineering, not research — but it is where the front-end
   person-hours actually go.** P2 called it "the largest single item"; C0
   confirms it is the load-bearing one for any looping primitive.
3. **`LoadByte` / the memory relation.** `eval s (LoadByte (buf+off+i))` reads
   `a[off+i]` from `σ`'s memory. This needs a lemma relating panSem's
   word-addressed byte memory (`mem_load_byte`, `s.memory : α word → α word_lab`
   over `s.memaddrs`) to the Lean `Array UInt8` — i.e. "the buffer at `buf`
   holds `a`". This is **P2 §4.7's shape** (the store/memory model — *not
   exercised* by P2, flagged there honestly). Standard and tractable, but it is
   a named piece P2 did not yet build; C0 is the first primitive that forces it.
4. **Word/int conventions.** `& 16777215`, `* 31`, `+` are word64 ops mapping
   `word_and/word_mul/word_add ↦ BitVec` (P2 §4.5). Here there is **no division
   and no negative on the path** and every intermediate is `< 2^24`, so the P2
   §4.2 floor-vs-Euclidean seam **does not bite** (matches R05's "cost bounded"
   note). Each op nonetheless owes its **adversarial convention-splitting
   witness pair** per the mandatory P2 §4.2 rule. Tractable, mechanical.
5. **The `encode` injection.** Sentinel `0xFFFFFFFF` (word64) vs digest `< 2^24`
   disjointness — the same fact `C0.encode`'s soundness note states. Trivial.

**Cost verdict for Link A.** No item is research-shaped; every one has a known
recipe and a loud checker. But items 2 and 3 together are a genuine
Hoare-style loop-invariant proof plus a memory-model relation over reflected
`evaluate` — for even this 40-line program that is **plausibly several days of
Lean/HOL4 proof-engineering, not an afternoon**, and it was **not** done in this
probe. Anyone who claims the refinement is "basically free once the backend
theorem exists" is wrong: the backend theorem (Link B) is free (inherited); the
front-end theorem (Link A) is the recurring per-primitive tax, and its unit
cost is dominated by P2 §5-#1 exactly as P2 predicted.

## 5. What this buys ADR-3-REV, concretely

- The **"emitted artifact stays CakeML/Pancake, no Rust, rustc out of the TCB"**
  clause is now not just asserted but *exercised*: our own primitive went
  source → verified backend → x64 → correct output, and the theorem that makes
  that trustworthy (`pan_to_target_compile_semantics`) is a real, `check_thm`'d
  line we can cite, not a hope.
- The **definitional-translator CR-2 row** is now backed by a worked front-end
  obligation with an itemized cost against P2's condition list — so the "small,
  syntactic, auditable bridge" claim can be checked against a concrete instance
  rather than taken on faith. The instance says: the *bridge* is small; the
  *refinement proof it enables* is not, and condition #1 is why.
- P2's round-trip is extended by a third, decisive kernel — **the machine** —
  closing the loop from "Lean and HOL4 agree on the definitions" to "and the
  compiled code agrees on the behaviour."

## 6. Honest gaps / what I did NOT do

- **Link A is unproven.** I did not close even the small tractable instance
  (§4-A-1, the out-of-bounds branch) as a HOL4/Lean theorem, because doing it
  *without* the reflected `panSem$evaluate` in Lean would be proving against a
  hand-transcription (circular), and standing up the P2 exporter's `evaluate`
  reflection is itself P2 §5-#1 — the very item being priced. So I priced it
  precisely instead of faking a partial. That is the correct probe outcome, but
  it means **the preservation claim rests on kernel-checked *testing* (§3) plus
  an *inherited* backend theorem (Link B) plus a *scoped* front-end obligation
  (Link A)** — not on a discharged end-to-end refinement.
- **The FFI is unspecified** (§4, Link B TCB residual). The arena-encoding C
  shim is trusted; a whole-system theorem owes it a spec.
- **Resource limit.** Link B's guarantee is modulo `extend_with_resource_limit'`
  (OOM/stack). For a fixed-size arena this is dischargeable but not discharged.
- **The HOL4 transcription in `boundScanScript.sml` is hand-written**, not
  emitted by the P2 exporter. It models bytes as `num`; faithful for this
  no-division, in-range primitive (§4-A-4), but it is a convenience twin for the
  behavioral layer, not the reflected `panSem`.

## 7. Reproduce

- Lean: `cd model && lean --run` a copy with `def main := C0.main` appended
  (see `run/lean_vectors.txt`).
- HOL4: `cd hol && Holmake` (needs `~/dev/HOL` built; green, `boundScanTheory OK`).
- Pancake: on hbox, `cd ~/c0 && cake --pancake < boundscan.pnk > boundscan.S &&
  cc -O2 boundscan.S basis_ffi.c boundscan_ffi.c -lm -o boundscan`, then
  `for v in "0 16" "0 3" "4 10" "14 2" "0 17" "16 1" "10 8" "16 0"; do set -- $v;
  OFF=$1 LEN=$2 ./boundscan; done` (see `run/pancake_vectors.txt`).

## 8. Bottom line for Phase C

The compiler seed germinates: a real primitive is dual-emitted and its compiled
machine code is correct against the Lean model, with the backend-preservation
theorem inherited from the CakeML tree intact and cited. The path is **open, not
free.** The unit cost of the verified-compiler goal is now measured, not
guessed: per looping primitive, one Link-A refinement = a loop-invariant proof
(P2 §5-#1) + a memory relation (P2 §4.7) + word-op witness pairs (P2 §4.2/§4.5),
on the order of days each with today's tooling, atop a one-time cost to stand up
the reflected `panSem$evaluate` in Lean. That number — days-per-primitive for
the refinement, backend free — is the honest input Phase C planning needs, and
it is why "proven-AND-compiled" is the structurally-hard clause it was billed
as.
