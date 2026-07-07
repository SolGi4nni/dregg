# C6 — parseRequestLine two-scan composition (Link A): COMPLETE / GREEN

**Status: the keystone is proven.** `twoScan_refines_parseReqLine` builds GREEN,
**fully** (not two-scan-split-only), for *all* inputs, with `[oracles: DISK_THM]
[axioms: ]` and **axioms count 0** (no `cheat` / `new_axiom` / `mk_thm` / oracle
anywhere in the source). The framing induction that used to blow the HOL4
simplifier up (~23 GB, never finishing) now proves cleanly, and the whole theory
rebuilds from clean in ~5–9 s.

Source: `docs/engine/probes/compiler/hol-c6/arenaParseLineLinkAScript.sml`
(mirror on hbox: `~/c6work/arenaParseLineLinkAScript.sml`).

"Components compose mechanically" is now **proven, not merely supported**: two
instances of the C5 preservation-proven scan (`scanLoop_refines_findSp`) are
assembled — at shifted base/offset, through the `setup2` reshaping block — into a
bigger preservation-proven function `twoScan = Seq scanLoop (Seq setup2 scanLoop)`,
and the assembly mechanism (`scanLoop_frame` / `scanLoop_run` + `evaluate_setup2`
+ `Seq_NONE_le`) is what makes full-engine emission mechanical.

## Headline theorem (verbatim, as printed with tags)

```
[oracles: DISK_THM] [axioms: ] []
|- loadedReq line buf s /\ 2 * LENGTH line <= s.clock /\
   parseReqLine off line = SOME ((mOff,mLen),(tOff,tLen),vOff,vLen) ==>
   ?s'.
     evaluate (twoScan,s) = (NONE,s') /\
     FLOOKUP s'.locals «found1» = SOME (ValWord 1w) /\
     FLOOKUP s'.locals «found»  = SOME (ValWord 1w) /\
     FLOOKUP s'.locals «i1» = SOME (ValWord (n2w mLen)) /\
     FLOOKUP s'.locals «i»  = SOME (ValWord (n2w tLen)) /\ mOff = off /\
     tOff = off + mLen + 1
```

i.e. against real `panSem$evaluate`, whenever the Lean `parseRequestLine off line`
returns SOME spans, the emitted `twoScan` runs to completion (`evaluate = NONE` —
no Error, no TimeOut) and computes the **method length** `mLen` into local «i1» and
the **target length** `tLen` into local «i», with the offsets exactly the Lean
spans (`mOff = off`, `tOff = off + mLen + 1`). The version span and the three
residual checks (no-third-SP, `i1<>0`, `HTTP/`) are the mechanical remainder — the
compiled `pnk/parseline.pnk` computes them and agrees with the Lean parser on the
vectors (Kernel 2, below).

## Supporting theorems (all `[oracles: DISK_THM] [axioms: ]`, 0 axioms)

```
scanLoop_frame  (the framing induction — the lean part; NO memRel in its conclusion)
|- !k input bs i found s.
     scanInv input bs i found s /\ LENGTH input - i <= k /\
     LENGTH input - i <= s.clock ==>
     ?s'. evaluate (scanLoop,s) = (NONE,s') /\ memFrame s' s /\
          (?bb. FLOOKUP s'.locals «b» = SOME (ValWord bb)) /\
          s.clock - (LENGTH input - i) <= s'.clock /\ s'.clock <= s.clock /\
          keepSaved s' s

scanLoop_run    (exit summary, reconstructed NON-inductively)
|- !k input bs i found s.
     scanInv input bs i found s /\ LENGTH input - i <= k /\
     LENGTH input - i <= s.clock ==>
     ?s' j f. evaluate (scanLoop,s) = (NONE,s') /\ scanInv input bs j f s' /\
              (f = 1 ==> j < LENGTH input /\ EL input j = 32) /\
              (f = 0 ==> j = LENGTH input) /\
              FLOOKUP s'.locals «found» = SOME (ValWord (n2w f)) /\
              FLOOKUP s'.locals «i»     = SOME (ValWord (n2w j)) /\
              s.clock - (LENGTH input - i) <= s'.clock /\ s'.clock <= s.clock /\
              keepSaved s' s

evaluate_setup2, twoScan_firstNoSp   — also green, 0 axioms.
```

## The blowup, diagnosed and fixed

The C6 report's original diagnosis was correct as far as it went — the runaway
was `scanLoop_run` carrying `scanInv` (hence `memRel`'s `!j` byte-quantifier over
the whole panSem state) in its INDUCTION conclusion. The complete fix needed
**five** independent pieces (each lowered the memory ceiling; the frame reached
GREEN only with all five):

1. **Split off `scanLoop_frame`** — a lean induction whose conclusion carries only
   a memory/scalar frame + clock bounds + `keepSaved` and NOT `memRel`. Reprove
   `scanLoop_run` NON-inductively from `scanLoop_frame` + C5's
   `scanLoop_scan_bounded` (the witness, already `memRel`-free), rebuilding
   `scanInv` once at the top level from `memRel input bs s` + the memory equality.
2. **`scanInv_b_exists`** — an isolated accessor for the «b» local, so the
   induction never does `fs [scanInv_def]` (which re-introduces `memRel` into the
   simplifier when memory-equality hyps are present).
3. **Fold the memory frame into an OPAQUE predicate `memFrame`** (memory/memaddrs/
   be + «len»/«base»), threaded through the induction by `memFrame_trans`/`_refl`
   exactly like `keepSaved`. Carrying the frame as RAW state-field/`FLOOKUP`
   equalities makes the simplifier accumulate and re-normalise huge panSem-state
   equalities; a folded predicate does not. (`keepSaved` was carried through this
   same induction in every version and never blew up — that was the tell.)
4. **Self-contained arithmetic in the advance branch** — the IH's *nested* nat
   subtractions (`s2.clock - (LENGTH input - (i+1))` etc.) make `fs`/`DECIDE`'s
   arithmetic decision procedure blow up when run over the full context; pulling
   only the needed facts + dropping the rest (and using `DECIDE_TAC` for the
   double-nested clock goal) keeps it bounded.
5. **`n2w_sub_norm`** — a subtraction lemma stated in the srw normal form
   (`n2w a + -1w * n2w b = n2w (a-b)`), because `panSem$eval` of `Op Sub` reduces to
   `x + -1w * y` and the srw simpset rewrites every `a - b` to `a + -1w * b`, so
   the plain `-`-phrased `n2w_sub_le` no longer matches (this bit `evaluate_setup2`'s
   `len := len - (i+1)` assignment, which had never been reached before).

The `twoScan` composition itself needed order-independent lemma application
(`drule_all`/`irule` instead of positional `qspecl_then`, whose assumed
quantifier order was wrong) and recovering `j = i1`/`j = i2` from the scan spec
(`scanSp line = SOME j` via `scanSp_found`) after `gvs` rewrote the exit «i» value.

## Rebuild log (from clean, marker-free source)

```
$ Holmake        # deps (arenaScanLinkA, machineLoopLinkA, machineStepLinkA) prebuilt
Building 1 theory file
Starting work on arenaParseLineLinkATheory
Theory "arenaParseLineLinkA" took 4.7s to build
arenaParseLineLinkATheory                                   (9s)   [1/1]     OK
```

Peak memory ~2–5 GB (was 23 GB+ and non-terminating). Every theorem is
`[oracles: DISK_THM] [axioms: ] []` (verified by loading the built theory and
inspecting tags; source contains no `cheat`/`new_axiom`/`mk_thm`/oracle).

## Kernel 2 — emitted `.pnk` agrees with the Lean parser

`cake --pancake < pnk/parseline.pnk` compiled clean; linked with `basis_ffi.c` +
`pnk/parseline_ffi.c`. Runs:

```
LINE="GET / HTTP/1.1"              -> SOME method=(0,3)  target=(4,1)   version=(6,8)
LINE="POST /api/v1/users HTTP/1.1" -> SOME method=(0,4)  target=(5,13)  version=(19,8)
LINE="GET /index.html HTTP/1.0"    -> SOME method=(0,3)  target=(4,11)  version=(16,8)
LINE="nospaces"                    -> NONE
LINE="GET /only-one-space"         -> NONE
```

All agree with `parseRequestLine 0 line`: `GET / HTTP/1.1` → method(0,3),
target(4,1), version(6,8); no-SP and single-SP lines → NONE.
