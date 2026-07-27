# cv_compute → OpenTheory → Lean: feasibility of importing Verifereum's EVM

Status: de-risk investigation, 2026-07-26. Companion to
`docs/OPENTHEORY-LEAN-IMPORTER-PLAN.md` and the working importer
`docs/opentheory-importer-poc/OTPoC.lean`.

This answers the two load-bearing unknowns for importing **Verifereum** (a
production HOL4 EVM semantics) into Lean via the OpenTheory→Lean importer:

1. **COMPACT-OR-EXPLODE.** When HOL4's `cv_compute` proves a ground evaluation
   `⊢ f x = v`, is that theorem *loggable to an OpenTheory article* compactly
   (one certificate step) or only by expanding a giant reduction trace?
2. **LEAN RE-ACCEPT COST.** Once such a `⊢ f x = v` is imported, the Lean kernel
   must re-check it. Is `Nat`/`BitVec` kernel reduction fast enough, or would it
   force `native_decide` (which pulls the compiler into the TCB — **refused**)?

## Executive verdict

- **cv_compute is category (C): a trusted ML kernel *primitive*, not a compact
  certificate and not a replayable trace.** It reduces the term in ML and
  *stamps* the resulting equation via `make_thm Count.Compute`. There is **no**
  pre-proved correctness theorem applied to certify the value (so nothing compact
  to log), and **no** inference trace is retained (so nothing to replay). The
  OpenTheory logger **hard-errors** on it today.
- **It is nonetheless not fundamentally unloggable**, because the primitive
  *retains its inputs* (the characteristic + code equations as theorems, and the
  input term). A **sound** logger patch can re-derive `f x = v` at log time by
  ordinary rewriting from those inputs — but that is the **EXPLODE** regime: the
  article grows proportional to the reduction length, which is exactly what
  `cv_compute` exists to avoid.
- **Therefore, for one small lemma (`⊢ fib 20 = 6765`) the HOL4 fork is a bounded
  ~week job; for Verifereum's compute-heavy EVM execution it is a quagmire** — not
  for soundness reasons but because of article/proof-size explosion.
- **Lean re-accept is tractable for *bounded* computations and does NOT need
  `native_decide`, but it is not free.** Measured (synchronous `isDefEq`): a
  BitVec-256 fuel loop costs **~60 µs per step** (62 ms at 1e3 steps, 725 ms at
  1e4, heartbeat-timeout at 1e5); large `Nat` bignum arithmetic scales with the
  operand size (`7^5000` = 54 ms). So the *same long-computation wall* that blocks
  HOL logging also makes Lean re-checking expensive for long traces — just at a
  more favorable constant, and **without** adding the compiler to the TCB.
- **Recommended path:** import Verifereum's *statement-level* results (specs,
  functional-correctness lemmas whose proofs are not `cv_compute`-bound) through
  the importer, and **re-prove compute-heavy executable lemmas natively in Lean**
  — viable when each obligation is a *bounded* evaluation (kernel `Nat`/`BitVec`
  reduction, no `native_decide`); a full unbounded EVM execution trace is
  expensive on either side (Part 2).

---

## Part 1 — COMPACT-OR-EXPLODE: how cv_compute builds its theorem

Evidence is from a local HOL4 checkout at `~/dev/HOL` (all paths absolute).

### cv_compute stamps, it does not derive

`cv_computeLib.cv_compute` is a thin cache over a genuine kernel primitive
`Thm.compute` (`~/dev/HOL/src/num/theories/cv_compute/cv_computeLib.sml:131-138`):

```sml
val cached = Thm.compute { cval_terms=..., cval_type=cvSyntax.cv,
                           num_type=numSyntax.num, char_eqns=char_eqns };
fun cv_compute eqs = cached (map SPEC_ALL eqs);
```

`Thm.compute` is exported in the kernel signature
(`~/dev/HOL/src/prekernel/FinalThm-sig.sml:144`) and counted as a *primitive
inference* `Compute`, alongside `Refl`/`Trans`/`Subst`/`EqMp`
(`~/dev/HOL/src/prekernel/Count.sig:22`). The OpenTheory-logging kernel builds
the result equation and stamps it (`~/dev/HOL/src/thm/otknl-thm.ML:1632-1635`):

```sml
val tm' = tc1 tm                        (* pure-ML reduction, tm  ~>  tm' *)
val eqn = safe_mk_eq tm tm'             (* build the TERM  `tm = tm'` *)
make_thm Count.Compute (tag1, empty_hyp, eqn, compute_prf (args, tm))
```

The reduction happens in a **private ML value world** (`Compute.sml`:
`datatype cval = Num of num | Pair ...`; the term is compiled to a `cexp`,
evaluated to a `cval`, and the final term reified). The `compute_prf` node stores
only `((compute_args * thm list) * term)` — the **inputs**, never a step-by-step
reduction. So:

- **Not (A) compact.** There is no `from_to`/`cv_rep` correctness theorem applied
  *inside* the primitive to certify the computed value. The transfer lemmas
  (`cv_rep`, `from_to_thm`) in `automation/cv_transLib.sml:945-963` wrap *around*
  the primitive with loggable `MATCH_MP`/`CONV_RULE`/`UNDISCH`, but the inner
  `cv_compute` conv step is the one unloggable atom.
- **Not (B) a replayable trace.** No inference trace is retained.
- **It is a trusted-base extension with a *clean* tag** (no oracle tag is
  stamped; `otknl-thm.ML:1613,1625` merge only the input theorems' tags), so a
  `cv_compute` result is indistinguishable from a fully-derived theorem while
  resting entirely on the trusted ML of `Compute.term_compute` + `make_thm`.

The soundness_check (`~/dev/HOL/src/num/theories/cv_compute/soundness_check/`)
treats the primitive as trusted **only** under input well-formedness guards — no
hypotheses on code equations (`otknl-thm.ML:1599,1615-1616`) and linear patterns
(the `g_xx` rejection) — and differentially cross-checks `cv_compute` against
`REWRITE_CONV` on a battery of cases. That is: the fast primitive is *validated
against* the genuine (loggable) rewriting path, not reduced to it.

### The OpenTheory logger hard-disables compute

`~/dev/HOL/src/opentheory/postbool/Logging.sml:715`:

```sml
| compute_prf _ => raise ERR "log_thm" "disabled in opentheory kernel";
```

This is deliberate. The cheap escape *exists* and is used for genuine primitive /
oracle leaves — `Axiom_prf`, `Disk_prf`, `deleted_prf` all emit an OpenTheory
`"axiom"` command (`Logging.sml:413-427`). Every other proof node expands into
logged OT primitives (`refl`, `betaConv`, `absThm`, `appThm`, `subst`, `sym`,
`trans`, `eqMp`, `deductAntisym`, `defineConst`, …). `compute_prf` is the **lone
node routed to `raise` instead of to any of these**.

### HOL issue #1118, in its own words

> "once `simp` (and friends) use the new compute under the hood it will [be] part
> of every development, but **the OpenTheory exporter won't know how to record its
> computation as OpenTheory primitive inferences**."

The proposed mitigations are to *disable* compute under OT export (a global flag,
or build-time conditional compilation) — not to expand it. This is the third
category: not article size per se, not missing definitions, not oracle-tagging —
the exporter simply has no representation for a compute step.

### Verdict for Part 1

`cv_compute` gives you **no compact certificate to log** (it is a stamp, not an
`eqMp` against a correctness theorem), and the only *sound* way to log it is to
**re-derive by rewriting from the retained inputs, which EXPLODES** (article size
∝ reduction length). The unsound shortcut (emit an `"axiom"` for the compute
result, mirroring `Disk_prf`) launders the whole computation into an assumption —
exactly the fail-open/vacuity pattern this project forbids.

---

## Part 2 — LEAN RE-ACCEPT COST (measured)

Method note (important for honesty): `addDecl`'s kernel type-check is *deferred*
in an interpreted `lean file.lean` run — timing around `addDecl` measures enqueue,
not reduction (a wrong value still prints "accepted" locally, then surfaces a
kernel error separately). The numbers below are therefore taken with **synchronous
`Meta.isDefEq lhs rhs`**, which forces the reduction immediately and returns
`false` on a mismatch. Comparing a term to *itself* is a no-op (defeq
short-circuits on syntactic equality), so every case compares the computation to a
**distinct literal**. Lean 4.30.0 on hbox; `native_decide` is neither used nor
needed.

| computation (forced to reduce, vs a distinct literal) | `isDefEq` time |
|---|---|
| `nfib 26` (structural recursion via `brecOn`) vs `121393` | **1.1 ms** |
| **NEG** `nfib 26` vs `999999` (wrong) → correctly `NEQ` | 1.1 ms (**rejected**) |
| `bvloop 1000` (BitVec-256 `acc:=acc*3+1`, 1e3 steps) vs literal | **62 ms** |
| `bvloop 10000` (1e4 steps) vs literal | **725 ms** |
| `bvloop 100000` (1e5 steps) vs literal | **heartbeat timeout** (>~7 s) |
| `bvloop 1000000` (1e6 steps) | did not finish in minutes |
| `7^5000` (GMP `Nat.pow`, 4226-digit result) vs literal | **54 ms** |
| `2^30000` (9031-digit result) vs literal | **357 ms** |
| **NEG** `7^5000` vs `+1` (wrong) → correctly `NEQ` | 52 ms (**rejected**) |

What this says, honestly:

1. **The kernel genuinely reduces (negative controls reject wrong values).** The
   times are real reductions, not no-ops.
2. **Per-step cost is ~tens of µs, and it scales with trace length.** A
   BitVec-256 fuel loop is ≈ 60 µs/step; structural recursion goes through
   `Nat.brecOn` (course-of-values, so "naive" `nfib` is linear, not exponential),
   but each step still costs real time. Individual 256-bit (EVM-word) operations
   are cheap; **the cost is the number of steps.**
3. **Large `Nat` bignum arithmetic scales with operand size** (GMP-backed but not
   free: `7^5000` = 54 ms). For EVM the words are bounded to 256 bits, so
   per-op arithmetic is µs-cheap — the dominant cost is trace length, not word
   size.

**Boundary (the load-bearing conclusion):** Lean re-accept is comfortable for
**bounded** computations — up to ~1e3–1e4 reduction steps re-check in tens to
hundreds of ms; ~1e5 steps hits the default heartbeat ceiling and needs a raised
`maxHeartbeats`; ~1e6+ steps is minutes. So the *same long-computation wall* that
blocks HOL's OpenTheory logging (Part 1) also bounds Lean re-checking — the gain is
that Lean pays a more favorable per-step constant and **adds nothing to the TCB**
(`native_decide`, which would compile `f` and trust the compiler + runtime
representation, is refused).

---

## Part 3 — Fork plan / feasibility

### One small lemma (`⊢ fib 20 = 6765`): bounded, ~week-scale, sound

The `compute_prf` node retains everything needed to re-derive soundly —
`(compute_args * thm list) * term` = the characteristic + code equations (as
theorems) and the input term (`otknl-thm.ML:105,115-118`). So a **sound** patch is
localized:

1. In `~/dev/HOL/src/opentheory/postbool/Logging.sml:715`, replace the
   `compute_prf _ => raise` branch with a re-derivation: build a `computeLib`
   compset / `REWRITE_CONV` from the captured `char_eqns` + `code_eqs` (HOL already
   ships this, and the cv_compute `selftest.sml` already uses `REWRITE_CONV` as its
   reference oracle), prove `tm = tm'` by that conv, then `log_thm` the derived
   theorem. It flows entirely through the already-logged primitives
   (`betaConv`/`refl`/`trans`/`subst`/`appThm`).
2. Build HOL4 with the logging kernel and `Holmake --ot` to emit the article
   (no Verifereum-side change; export is a HOL4-side capability).
3. Round-trip the article through `OTPoC.lean` (Part A) and measure article size +
   Lean re-accept.

Cost is dominated by article/proof size = O(reduction length). For `fib 20` that
trace is tiny; the fork is bounded and the mathematical content is all present.

**Do NOT take the 3-line unsound shortcut** (mirror `Disk_prf`, emit `"axiom"` for
`compute_prf`): it turns the computation into an article *assumption*, so the
importer's axiom gate would (correctly) refuse it, or — worse — it would launder an
unproven equation into the trusted set. That is the fail-open gate class.

### Verifereum's compute-heavy EVM: quagmire (explosion, not soundness)

Verifereum's selling point is that its EVM semantics is *executable by evaluation
inside the logic* — it leans on `cv_compute`/`EVAL` precisely to avoid
primitive-inference blowup. The sound logger patch reintroduces exactly that
blowup at log time: every reduction step becomes logged OT primitives, and the
article for a full EVM execution grows to the size of the whole computation. This
is why upstream #1118 prefers to *disable* compute under OT rather than expand it.

### Recommendation

- **Importable now (through `OTPoC.lean`):** Verifereum's statement-level results
  — the EVM state-transition *specification*, structural lemmas, and
  functional-correctness statements whose proofs are ordinary HOL reasoning (not
  `cv_compute`-bound). These log to articles and import kernel-clean, axiom-clean.
- **Re-prove natively in Lean:** the compute-heavy executable lemmas, *when each
  obligation is a bounded evaluation.* Part 2 shows the Lean kernel evaluates
  `Nat`/`BitVec` computations by reduction at ~tens of µs/step (no `native_decide`),
  which is comfortable up to ~1e4 steps and needs a raised `maxHeartbeats` by ~1e5.
  So an executable EVM step (or a short bounded run) can be *defined in Lean and
  evaluated by the kernel* directly against the imported spec — but a long
  unbounded execution trace is not cheap on either side, so decompose to bounded
  obligations rather than kernel-evaluating a whole trace.
- **Only if a specific compute lemma must be transferred verbatim** is the
  Logging.sml re-derivation patch worth it, and only for small computations.

The reusable importer is the right foundation and it works on real HOL4-emitted
articles today (Part A). "Import Verifereum's *executable* EVM through cv_compute
logging" remains blocked by the compute-logging explosion — an upstream-HOL4-shaped
cost, not an importer gap — and should be surfaced as the gating risk of any
"verified zkEVM by importing Verifereum" plan.

---

## Sources
- HOL4 `cv_compute`: `~/dev/HOL/src/num/theories/cv_compute/cv_computeLib.sml`,
  `~/dev/HOL/src/thm/otknl-thm.ML` (105, 115-118, 1594-1639; oracle contrast 1321),
  `~/dev/HOL/src/thm/Compute.sig` (16) & `Compute.sml`,
  `~/dev/HOL/src/prekernel/FinalThm-sig.sml:144`, `Count.sig:22`,
  `automation/cv_transLib.sml:945-1036`,
  `soundness_check/selftest.sml`, `cv_compute_unsoundScript.sml`.
- OpenTheory logger: `~/dev/HOL/src/opentheory/postbool/Logging.sml` (715; axiom
  path 413-427; primitive commands 429-713).
- HOL issue #1118 — https://github.com/HOL-Theorem-Prover/HOL/issues/1118
- Lean re-accept harness: `docs/opentheory-importer-poc/OTPoC.lean` and the B.2
  kernel-reduction measurements (Lean 4.30.0).
