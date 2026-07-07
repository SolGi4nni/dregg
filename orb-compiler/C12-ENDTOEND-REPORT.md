# C12 REPORT — the deferred FRONT-END obligation paid down: the scan-`While` DIGEST loop invariant (C1 §4-A-2) is CLOSED, and the WHOLE decision+digest core of the emitted `main` now refines the Lean spec — both kernel-checked, `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats — with the EXACT residual for the single spec→machine-code theorem named precisely

**Date:** 2026-07-06 · **Machine:** hbox (i9-12900, 24c/123G) for HOL4/CakeML.
**HOL4 `Trindemossen 2` (stdknl), CakeML `ed31510b3`** — the exact tree C1–C11
used. **Status:** the item every prior front-end probe named as the multi-day
UNCLOSED residual — the scan-`While` loop invariant (C1-REPORT §4-A-2, restated
in C2 §6, C3, and C11 §4) — is now a **kernel-checked theorem, 0 axioms, 0
cheats**, proved against the REAL Pancake source semantics `panSem$evaluate`,
using the **exact emitted loop term** lifted from the CakeML-verified parser
output `boundScanProg`. On top of it, the **whole decision+digest core** of
`main` (the bounds `If` with the genuine scan loop inside its else-arm — **not**
the `Skip` stub C1 used — plus the `Dec acc/Dec i` scoping and the `result :=
acc` write-back) is proved to write **exactly** the Lean spec's encoded result
word `n2w (c0_encode (boundScan a off len))` into the local `«result»`.

**Honest verdict (§5):** there is **not yet** ONE closed spec→machine-code
theorem for the whole primitive. What is now closed is the *computational heart*
of whole-program Link A (the loop + the whole decision core); the exact residual
is the **FFI-trace wrapper** (the two `ExtCall`s + the `BaseAddr`/`Load`/`Store`
plumbing that stages the arena in memory and the result on the trace) and the
**`semantics_decls` clock-lift** — a front-end obligation of known shape resting
on the **FFI-oracle contract** (C11 §3.4, irreducibly trusted because the
observable behaviour *is* an FFI trace) and the standard CakeML machine-state
package. **None of the residual is leanc**, and none is the backend.

---

## 1. What C12 built (both theories, `docs/engine/probes/compiler/hol-c12/`)

Two kernel-checked theories, built green against the CakeML pancake semantics and
the C3/C5/C6 loop machinery (`machineStepLinkATheory` / `machineLoopLinkATheory`,
opened and reused verbatim: `memRel`, `Seq_NONE`, `w2w_byte`, `signed_lt_n2w64`).

### 1.1 `boundScanDigestLinkA` — the DIGEST scan-`While` loop invariant

`digLoop` is the **verbatim** emitted loop lifted from `functions boundScanProg`
(the `main` body's `While`): `Annot` location nodes, `Panop Mul`, `Op And`, the
3-operand `Op Add` `LoadByte` address `buf + off + i`, all as emitted. The
invariant `digInv` carries the running 24-bit digest `acc` and index `i`, the
byte-memory relation `memRel a buf` (the `LoadByte` relation named UNCLOSED in
C1 §4-A-3), and the signed-range side conditions. The headline:

```
digLoop_refines_scanFrom:                                   [oracles: DISK_THM] [axioms: ]
  ⊢ digInv a off buf len 0 0 s ∧ len ≤ s.clock ⇒
    ∃s'. evaluate (digLoop,s) = (NONE,s') ∧
         FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (dscan a off len 0))) ∧
         (∀v. v ≠ «acc» ∧ v ≠ «i» ⇒ FLOOKUP s'.locals v = FLOOKUP s.locals v)
```

`dscan`/`dstep` are byte-identical to `model/BoundScan.lean` `C0.scanFrom`/`C0.step`
and to hol-c1's `scanFrom`/`step` (the mask `& 0xFFFFFF` = `MOD 2^24` discharged
via `WORD_AND_EXP_SUB1`). The proof is a loop-invariant induction over the clocked
`While` (`digLoop_fold_bounded`), reusing the C3/C6 clock-accounting pattern
(`Seq_NONE`, `dec_clock`, the `LENGTH input − i ≤ clock` threading). The
`∀v … FLOOKUP` conjunct is the **locals frame** (the body writes only `«acc»`,
`«i»`) — needed downstream so `result := acc` sees a preserved `«result»`.

### 1.2 `boundScanCoreLinkA` — the WHOLE decision+digest core

`innerCore` is the **verbatim** `If` node from `main`: the bounds test, the
sentinel arm, and — crucially — the else-arm with the genuine `Dec acc (Const 0w)
/ Dec i (Const 0w) / (While … digLoop) / result := acc`. The headline:

```
evaluate_innerCore:                                         [oracles: DISK_THM] [axioms: ]
  ⊢ coreRel a off len buf r0 s ∧ len ≤ s.clock ⇒
    ∃s'. evaluate (innerCore,s) = (NONE,s') ∧
         FLOOKUP s'.locals «result»
           = SOME (ValWord (n2w (c0_encode (boundScan a off len))))
```

`boundScan`/`c0_encode` are byte-identical to `model/BoundScan.lean`
`C0.boundScan`/`C0.encode` (and hol-c1). Both arms are handled against real
`panSem$evaluate`: OUT-of-bounds writes the sentinel `0xFFFFFFFF = c0_encode NONE`;
in-bounds runs `digLoop` (§1.1) and writes the digest. The proof threads the two
`Dec` scopes (`res_var` restore of `«acc»`/`«i»`, `«result»` preserved because it
is neither — via `FLOOKUP_res_var_neq` and the loop frame), and sequences the
loop (clock-consuming) with `Seq_NONE_le`.

**This strictly supersedes C1** (`hol-c1/boundScanLinkAScript.sml`), whose Link A
proved the bounds `If` with the loop replaced by `Skip`. Here the loop is the
real emitted `While` and its digest flows into `«result»`.

Both: `axioms "…" = 0`, 0 cheats. Statements + tags in `hol-c12/verify_out.txt`.

## 2. How this composes toward the single end-to-end theorem

The target chain is `spec ⟺ semantics_decls s «main» boundScanProg` (whole-program
Link A) ∘ `machine_sem ⊆ {semantics_decls …}` (C11's `boundScanProg_linkB`,
Link B). C12 closes the **interior** of the Link-A obligation:

```
      «alen»/«off»/«len» in locals, arena in memory  ── evaluate_innerCore ──▶  «result» = spec word
                              ▲                                                        │
              (Load reads / load_vec FFI)                                (Store / report_vec FFI)
```

`evaluate_innerCore` is exactly the state-transformer refinement of the region
between the two `ExtCall`s. What remains to reach `semantics_decls` is the
wrapper around it (§3).

## 3. The EXACT residual (what a single spec→machine-code theorem still needs)

Running `main` is (from `functions boundScanProg`, verbatim):

```
Dec base BaseAddr; Dec buf (base+32);
@load_vec(base,24,buf,4096);                       -- FFI 1  (stages control block + arena)
Dec alen (Load One base); Dec off (Load One (base+8)); Dec len (Load One (base+16));
Dec result (Const 0);
  <innerCore>                                      -- CLOSED by C12 §1.2
Store (base+24) result;                            -- result word → memory
@report_vec(base+24,8,base,8);                     -- FFI 2  (result word → FFI trace)
Return (Const 0)
```

The precisely-named remaining obligations, each of **known shape**:

1. **The `BaseAddr`/`buf` `Dec`s** — `eval s BaseAddr = SOME (ValWord s.base_addr)`;
   trivial, deterministic.
2. **The `@load_vec` `ExtCall`** — `evaluate (ExtCall …)` reduces via
   `read_bytearray` / `call_FFI` / `write_bytearray`; its effect (the control
   block `[base,base+24)` reads back `LENGTH a`/`off`/`len`, the arena is written
   to `[buf,buf+|a|)`) is **exactly the FFI-oracle contract** — the single named
   honest assumption C11 §3.4 already isolated as *irreducible* (the observable
   behaviour is an FFI trace). Modelled as an oracle hypothesis, its post-state
   supplies the `coreRel` memory precondition C12 §1.2 consumes.
3. **The three `Load One` reads** — `mem_load One (base+k)` yields the control-block
   words into `«alen»`/`«off»`/`«len»`; deterministic given (2)'s post-state.
   This is the memory→locals bridge into `coreRel`.
4. **The `Store (base+24) result`** — `mem_stores` writes the (C12-computed)
   result word to memory; deterministic.
5. **The `@report_vec` `ExtCall`** — emits the result word onto `s.ffi.io_events`;
   the FFI-oracle contract again (its `conf` region is the result word).
6. **The `semantics_decls` clock-lift** — `semantics_decls` = `evaluate_decls`
   (installs `main`, dischargeable by EVAL) then `semantics s' «main»`, whose
   `semantics_def` quantifies over all clocks: one must show (a) for large enough
   `k`, `evaluate (Call NONE «main» [], s' with clock:=k) = (SOME (Return 0w), t)`
   with `t.ffi.io_events` the two-event trace carrying the spec word, and (b) **no**
   clock yields `Error`/`Break`/`Continue` (the standard CakeML whole-program
   non-error lift, via clock monotonicity). This is the one genuinely non-trivial
   remaining step; it is standard CakeML, not new mathematics.

Once (1)–(6) are discharged, whole-program Link A gives
`semantics_decls s «main» boundScanProg = Terminate Success <trace(spec word)>`,
and composition with `boundScanProg_linkB` is a substitution yielding
`machine_sem mc ffi ms ⊆ extend_with_resource_limit' … {Terminate Success <spec word>}`
— the single closed spec→machine-code theorem.

## 4. What is trusted (unchanged from C11; none of it is leanc)

leanc remains **OUT of the TCB**: `boundScanProg` is the CakeML-**verified**
Pancake parser's output on leanc's exact `boundscan.pnk` bytes
(`boundScanProg_is_parser_output`, C11). The residual (§3) rests only on:
(a) HOL4 + CakeML kernels; (b) the standard machine-state-install package +
`compile_prog_max` backend run (C11 §3, the x64 target-config side); (c) the
**FFI-oracle contract** for `@load_vec`/`@report_vec` (§3.2/§3.5), irreducible
because the observable behaviour is an FFI I/O trace. C12 adds **no** new trust:
both its theorems are `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats.

## 5. Honest verdict — is leanc out of the TCB end-to-end for boundScan?

**Is there now ONE closed spec→machine-code theorem for boundScan?** **No, not
yet.** But the ledger has moved decisively on the *front-end*, which was the sole
remaining blocker after C11 closed the backend:

| Piece | Status |
|---|---|
| Emitter (leanc) out of TCB — verified parser | ✓ (C10/C11) |
| Link-A bounds decision | ✓ (C1) |
| **Link-A scan-`While` digest loop invariant** (the multi-day deferred item) | **✓ (C12 §1.1)** |
| **Link-A whole decision+digest core** (`«result»` = spec word) | **✓ (C12 §1.2)** |
| Link-A FFI-trace wrapper + `semantics_decls` clock-lift | ✗ — the one open front-end obligation (§3) |
| Link-B backend, closed at the concrete program | ✓ (C11) |

So for boundScan: **leanc is fully out of the TCB**; the bounds decision, the
scan-loop invariant, and the whole decision+digest core are kernel-checked
Link-A theorems (0 axioms); the backend is a closed kernel-checked Link-B theorem;
and the **only** thing between here and a single end-to-end spec→machine-code
theorem is the FFI-trace wrapper + the standard `semantics_decls` clock-lift,
resting on the named FFI-oracle contract — a proof obligation of known shape,
**not** a build hole, **not** a trust hole, **not** leanc, **not** the backend.

## 6. Files (`docs/engine/probes/compiler/hol-c12/`)

- `boundScanDigestLinkAScript.sml` — Part 1: the digest loop (`digLoop` verbatim
  from `boundScanProg`), `digInv`, `digLoop_fold_bounded`, `digLoop_refines_scanFrom`
  (with locals frame).
- `boundScanCoreLinkAScript.sml` — Part 2: `innerCore` verbatim, `coreRel`,
  `eval_core_guard`, `evaluate_innerCore` (the whole decision+digest core → `«result»`).
- `Holmakefile` — `INCLUDES` the cakeml pancake/proofs dirs + `~/c6work` (the C3/C5/C6
  loop machinery) + `~/hol-c11` (`boundScanProg`); build with `CAKEMLDIR=~/src/cakeml`.
- `verify_out.txt` — printed statements + `[oracles: DISK_THM] [axioms: ]` +
  `axioms "…" = 0` for both theories.
