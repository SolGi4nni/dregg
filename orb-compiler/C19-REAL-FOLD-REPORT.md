# C19 REPORT — the fold-loop schema REACHES REAL SERVE FOLD CODE: the deployed cache-key hash (`Cache.hashBytes`, run every request in `cacheEmptyStage`) closes its whole `While` loop core to `n2w (hashBytes input)` from an **~8-line per-step fill-in** — the SAME length as C16's toy byte-sum — and the one real friction (a **Nat** accumulator vs a **word64** register) is closed by a 4-line `n2w`-homomorphism. Every theorem `[oracles: DISK_THM] [axioms: ]`, hyps=0, 0 cheats, kernel-checked, `~/hol-c19` green on hbox.

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 Trindemossen-2 stdknl, CakeML `ed31510b3`** — the exact tree C1–C18 used.
**Dir:** `docs/engine/probes/compiler/hol-c19/` (built on hbox `~/hol-c19`, all theories `OK`). Sibling agents own `hol-c16/c17/c18` (done); C19 stays out.

---

## 0. What this probe answers

C16 built the **fold-loop schema** (`foldLoop_refines`: emitted `While` = `FOLDL accf init (MAP n2w input)` from a per-step fill-in) and demonstrated it on a **toy** byte-sum (`sumLoop_refines`, ~8-line `sumBody_step`). C17/C18 showed the SCALAR (loop-free) class reaches four real `deployStagesFull2` decisions. C18 §5 then drew the honest map: what remains to the whole serve is almost all **fold-over-list** computation.

C19 asks the fold analog of C17's Gate-A question: **does the C16 fold-loop schema transfer to a REAL, deployed serve fold — and what friction appears?** It picks a genuine `FOLDL` from the deployed serve, closes its whole loop core spec→`While`, and quantifies the fill-in.

**Verdict up front: YES, it transfers with the same ~8-line fill-in.** The single real-serve friction — the Lean spec accumulates in `Nat`, the machine in `word64` — is closed once by a `n2w`-semiring-homomorphism lemma.

## 1. THE real serve fold — the deployed cache-key hash

`Reactor/Stage/Cache.lean:115` (drorb):

```lean
def hashBytes (b : Bytes) : Nat := b.foldl (fun a x => a * 257 + x.toNat + 1) 0
```

- **Genuinely deployed, on the hot path.** `hashBytes` is called by `keyOf`
  (`Cache.lean:118-119`: `{ method := hashBytes c.req.method, uri := hashBytes c.req.target, .. }`)
  and by `varyOf` (`Cache.lean:247`). `keyOf` computes the cache key that
  `Reactor.Stage.Cache.mkStage` looks up — and that stage is `cacheEmptyStage`,
  **stage 4 of `Reactor.Deploy.deployStagesFull2`** (`Reactor/Deploy.lean:1442,1501`),
  the deployed orb serve. Every request that reaches the cache stage runs two
  `hashBytes` folds (over the method bytes and the target bytes).
- **Genuinely a `FOLDL` over a byte array** — the fold-loop schema's exact target —
  but a *richer* accumulator than the toy byte-sum: a **multiply-add** step
  `a*257 + byte + 1`, and a **`Nat`** result (the two frictions C16 flagged for
  "real-serve fold code": a non-`+` accf and a non-word accumulator).

## 2. THE closed loop core

`hashLoop_refines` — the emitted cache-hash `While` computes EXACTLY the deployed Lean fold, modulo 2^64:

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ !input bs (s:(64,'ffi) state).
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (While foldGuard hashBody, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (hashBytesN input)))
```

where `hashBytesN input = FOLDL (\a x. a*257 + x + 1) 0 input` is the drorb
`Cache.hashBytes` re-declared over nats (byte-identical: `List.foldl (fun a x => a*257 + x.toNat + 1) 0`), and `hashBody` is the emitted mul-add body

```
Seq (Assign «b» (LoadByte (base+i)))
(Seq (Assign «acc» (Op Add [Panop Mul [acc; 257w]; b; 1w]))     (* a*257 + b + 1 *)
     (Assign «i» (Op Add [i; 1w])))
```

in the exact verified-parser emitted style of C13's digest body (`Panop Mul` for
`*`, `Op Add` for `+`, `LoadByte` byte read). The installed `While` provably
computes `n2w (hashBytes input)` — the deployed hash the cache key is built from.

**Route:** identical to C16's byte-sum — discharge the schema's single obligation
(`hashBody_step`) with a per-step fill-in, compose via `foldLoop_refines`, then
rewrite the word fold to the Lean fold via the homomorphism `hashBytes_word`.
The C16 schema (`foldInv`, `foldLoop_iter`, `foldLoop_bounded`, `foldLoop_refines`)
was reused **verbatim, zero changes** — it is genuinely program-agnostic in
`⟨accf, body⟩`.

## 3. The per-step fill-in — QUANTIFIED

| primitive | loop-core Link-A proof | fill-in |
|---|---:|---|
| C13 `boundScan` (bespoke) | **~629 lines** | synthesise + hand-prove a loop invariant (`digInv`) |
| C16 `sumBody` (toy byte-sum) | **~8 tactic lines** | evaluate one `+` iteration, re-establish `foldInv` |
| **C19 `hashBody` (REAL cache hash)** | **~8 tactic lines** | evaluate one `a*257+b+1` iteration, re-establish `foldInv` |

`hashBody_step` (the whole fill-in) is 8 tactic invocations — byte-for-byte the
shape of `sumBody_step`. The **entire delta** for the real fold's richer
multiply-add accumulator is **two extra rewrites** in the one `simp`
(`pan_op_def`, `word_mul_n2w`, for the `Panop Mul`) and unfolding `hashAcc_def`
instead of `sumAcc_def`. The mul-add fold body is no harder to close than the
plain-add one. **The schema transferred with the fill-in cost UNCHANGED.**

## 4. The one real-serve friction found — a Nat accumulator vs a word64 register

The C16 schema computes the **word** fold `FOLDL hashAcc 0w (MAP n2w input)`
(`hashAcc a b = a*257w + b + 1w`, exact in `word64`, wraps at 2^64). The Lean
spec `hashBytes` accumulates in **`Nat`** (unbounded). The deployed C, compiled by
leanc into a fixed-width register, wraps — so `n2w (hashBytes input)` (the Lean
result mod 2^64) IS the faithful statement of what the machine computes. The
bridge is a `n2w`-semiring homomorphism, closed **once**, 4 lines total:

```
[oracles: DISK_THM] [axioms: ]
⊢ hashAccN_word:  !a b. n2w (a*257 + b + 1) = (n2w a)*257w + (n2w b) + 1w   (* n2w hom, per step *)
⊢ hashBytes_word: !input. n2w (hashBytesN input) = FOLDL hashAcc 0w (MAP n2w input)  (* list induction *)
```

This is the honest answer to "what real-serve fold friction appeared": **not**
variable-width elements and **not** early exit (the cache hash is a clean
fixed-width running accumulator over a byte list), but the **non-word (`Nat`)
accumulator** — resolved by stating the theorem at `n2w (hashBytes …)` (the
deployed fixed-width value) and discharging the Nat→word gap with a reusable
homomorphism. Any future serve fold whose Lean spec is a `Nat`/`UInt`-valued
running accumulator (`hashBytes`, a rolling checksum/CRC, a decimal
`Content-Length`/chunk-size scan `acc*10 + digit`) reuses this exact 2-lemma
pattern.

## 5. What remains — the fuel-budgeted whole-program wrapper (the C16 residual, now precisely scoped)

`hashLoop_refines` closes the loop **core** (spec = emitted `While`), exactly as
C16's `sumLoop_refines` did for the toy — it is **not** yet the whole-program
spec→machine-code `machine_sem = Terminate Success (…)` theorem. That needs the
**fuel-budgeted `mk_wrapper`** (C16 §4 residual, Part 1 of this probe's charge).
This probe did **not** land the generator extension; it did **ground it
precisely** against the C13 boundScan hand loop-wrapper stack (`~/hol-c13`), which
is already the fuel-budgeted whole-program wrapper for a loop primitive, done by
hand. The generalization of `panWrapperLib.mk_wrapper` (currently loop-free:
threads a fixed nonzero clock, reads N scalar words) into the loop case is
**mechanical — no new metatheory**; every step below exists in the C13 stack:

1. **`mk_mainRefine` — clock budget.** Add the antecedent `budget <= s0.clock`
   to the goal (C13 `boundScanMainRefine:10`: `… /\ len <= s0.clock ==>`), thread
   it `<= sRz.clock` down the `Dec` spine (each `Dec` preserves clock), and pass
   the extra `budget <= sRz.clock` conjunct when applying the core
   (`hashLoop_refines` needs it; the loop-free `coreFramed` had no clock
   precondition). One new parameter `clockBudget` on `mk_mainRefine`.
2. **`callMainRun` (Sem).** Replace the loop-free `s''.clock <> 0` antecedent with
   `budget <= (dec_clock s'').clock` (C13 `boundScanSem:25-27`).
3. **`main_semantics` (Sem).** The loop-free generator instantiates
   `s' with clock := 1`; the loop version instantiates `s' with clock := K0` under
   `?K. 0 < K /\ budget < K` and threads `budget <= (dec_clock sc).clock`
   (C13 `boundScanSem:54-74`). The clock witness (`SUC budget`) is the only new
   term; `semantics_Return_lift` + `extend_with_resource_limit` close the
   all-clocks quantification exactly as in the loop-free stack.
4. **`semanticsDecls` (Install) / EndToEnd.** Already universal over `Kc`
   (`boundScanInstall:44`); add the budget-witness discharge. LinkB composition is
   byte-identical.
5. **The array read.** Replace the `reads` list (N scalar `Load One`) with the
   C13 **`ctrlStaged`** array-staging clause: the `load_vec` oracle stages a
   control block (`base` holds `LENGTH input`, `base+8..` the view params) + the
   **arena at `base+32`** related by `memRel` — the pointer+length read the fold
   loop consumes. `boundScanFFI` already has this exact shape.

To *validate* the extended generator the C16 way (reproduce a hand loop-wrapper
automatically) requires a **verified-parser-parsed fold program + its LinkB** in
the build (the CakeML backend), i.e. emit `hashBytes` to Pancake and parse it — the
C0–C18 emit path — then re-derive the boundScan (or hashBytes) wrapper stack
through the parameterized generator. That is the concrete, scoped next step; it is
plumbing over the closed C13 template + this probe's closed core, not new proof.

## 6. Trust ledger (unchanged from C13–C18; none of it is leanc)

Every C19 theory is `[oracles: DISK_THM] [axioms: ]`, hyps=0, 0 cheats.
`DISK_THM` is the benign CakeML disk-export tag — no `cheat`, no `mk_thm`, no
axiom, identical footing to C11–C18. The fold core rests only on the C16 schema
(reused verbatim) + `panAuto`; the accumulator is an exact machine word and the
Nat→word bridge is a proved homomorphism, so no new trust is introduced. leanc
stays OUT of the TCB (the emitted body is the verified-parser style; the full
end-to-end that pins it to the *parsed* `hashBytesProg` is the §5 residual).

## 7. Files (`docs/engine/probes/compiler/hol-c19/`, built on hbox `~/hol-c19`)

- `hashBytesLoopScript.sml` — **the real serve fold**: `hashBytesN` (= drorb
  `Cache.hashBytes`), `hashAcc` (word step), the `n2w` homomorphism
  (`hashAccN_word`, `hashBytes_word_gen`, `hashBytes_word`), the emitted `hashBody`
  + `eval_hashUpdate`, the **~8-line `hashBody_step` fill-in**, and the closed
  **`hashLoop_refines`**.
- `foldLoopSchemaScript.sml` — the C16 fold-loop schema, **carried verbatim**
  (`foldInv`, `foldLoop_iter/bounded/refines`, `eval_foldByte`) — reused with zero
  changes, evidence it is program-agnostic.
- `panAutoScript.sml` — the C15 program-agnostic theory (`signed_lt_n2w64`) the
  schema's guard rests on.
- `verifyHash.sml` — the machine-checked oracle/axiom/hyp audit (prints all three
  headline theorems with `show_tags`).
- `Holmakefile` — includes the CakeML pancake/semantics dirs; build with
  `CAKEMLDIR=~/src/cakeml`.

## 8. Verdict

- **Does a REAL serve fold now auto-descend its loop core?** **Yes.** The deployed
  cache-key hash `Cache.hashBytes` (run every request in `cacheEmptyStage`) closes
  `evaluate (While foldGuard hashBody) = n2w (hashBytes input)` via the C16 schema,
  `[oracles: DISK_THM] [axioms: ]`, hyps=0, green on hbox.
- **Fill-in line count?** **~8 tactic lines** — identical to C16's toy byte-sum
  (vs boundScan's 629). The mul-add accumulator cost two extra rewrites, nothing
  structural. The schema transferred cleanly.
- **Real-serve fold friction?** One: the **`Nat` accumulator** (Lean spec) vs the
  **`word64` register** (machine). Closed once by a 4-line `n2w` homomorphism;
  reusable for every `Nat`-accumulating serve fold. No variable-width / early-exit
  friction in this fold.
- **Fuel-budgeted `mk_wrapper` (Part 1)?** **Not landed**; precisely scoped as five
  mechanical, no-new-metatheory changes to `panWrapperLib` against the closed C13
  boundScan loop-wrapper template (§5). Validating it needs a parser-parsed fold
  program + LinkB (the emit path) — the concrete next step.
- **What remains between here and composing the whole stage fold?** (1) the
  fuel-budgeted `mk_wrapper` §5 (turns this closed core into a `machine_sem =
  Terminate Success` theorem); (2) emit+parse `hashBytes` so the end-to-end pins to
  the *parsed* program (leanc fully out of TCB, as C17/C18 did for scalar
  fragments); (3) the stage-level compose — `keyOf` runs two `hashBytes` folds and
  a cache lookup, so composing the whole `cacheEmptyStage` needs sequencing two
  fold cores + the C18-closed `isFresh` scalar gate.
```
