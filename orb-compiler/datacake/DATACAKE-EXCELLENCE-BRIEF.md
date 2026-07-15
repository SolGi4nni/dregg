# datacake — the excellence brief (deputation-grade)

**North star:** make Dragon's Orb *both the fastest and the most assured* network orchestrator/control/dataplane
on the planet — by pushing verification all the way down to the machine code, so the fast code **is** the proven
code. Datacake is that wager made concrete. This brief is for bringing datacake to completion **via excellence** —
not "made to compile," but done *right*, as a coherent masterwork.

This is written to be executed by a powerful dedicated agent (codex-class) owning the whole slice end-to-end.
Ground-truth-first (real paths, real signatures, real proof structure) so it can execute for excellence, not
reconstruct from prose.

## Ground truth (what exists — ext1)
- **Fork:** hbox `~/dev/datacake` (rsync of `~/src/cakeml` @ ed31510b3 *with* `.hol` artifacts → incremental,
  ~25-min full-frontend rebuild loop). `~/src/cakeml` + `~/src/HOL` are the untouched baseline. Fork recipe:
  `rsync -a ~/src/cakeml/ ~/dev/datacake/` → `rm -rf pancake/{,proofs,semantics,parser}/.hol/make-deps` →
  `taskset -c 0-15 nice -n 15 ~/src/HOL/bin/Holmake -j 8` in `pancake/proofs`.
- **Owns (frontend, 36 theories):** `panLang`/`panSem`/`crep*`/`loop*`/`pan_to_target` + their proofs. **Reuses
  as-built (never rebuilt):** the `wordLang → stackLang → labLang → x64` backend + `misc/basis/semantics`.
- **ext1 done:** `Div/Mod` added (unsigned, via `LLongDiv`), frontend proven green `[oracles: DISK_THM]` 0-cheat,
  `/` `%` verified computing (div-by-zero → `NONE`). Patch: `docs/engine/datacake/divmod.patch`.
- **The known boundary:** CakeML's word backend has unsigned long-div *only on x86_64* → the all-ISA
  `every_inst_ok_less_*` chain hits an unprovable `c.ISA = x86_64`. We target x86_64, so it runs today; the fix is
  to thread `ISA=x86_64` through ~7 theorems (or scope datacake to x86_64 by design).

## The completion axes (in order)
1. **Close ext1's residual** — thread `ISA=x86_64` (or make x86_64 a datacake design invariant, dropping the
   all-ISA obligation cleanly). Green `pan_to_targetProof`. This is the warm-up.
2. **Packed-byte stores** — kill the byte-per-word-slot layout the serialize write-loops suffer. Real mechanical
   sympathy; unblocks efficient `serialize`/`Bytes` lowering. `StoreByte`/`Store32` exist — assess whether a packed
   multi-byte store shape is needed and lower+prove it.
3. **StageProg-native lowering** — the genuine per-constructor StageProg compiler (the thing the Lean-side copy-stub
   couldn't do on stock Pancake). Datacake constructs shaped for `addHeader`/`gate`/`rewriteBody`/`serialize` so
   `compile : StageProg → datacake` *computes* the response, not memcpy's a pre-computed answer.
4. **Mechanical sympathy pass** — register allocation quality on the hot paths, cache-shape, redundant-work
   elimination, the calling convention / entry ABI (`export fun` + the per-shard heap already work — tune them).
   Measure A/B vs leanc on the real hot paths.
5. **★ Verified SIMD intrinsics (the far horizon, the audacious part)** — model the needed AVX instructions in HOL
   (`PCMPEQB`/`PMOVMSKB` for byte-scan, vector load/store, vector memcpy), prove their semantics, and expose them
   as **proven intrinsics** the codegen uses — NOT general auto-vectorization. Each intrinsic = one hard beautiful
   proof (e.g. `scan_crlf` finds the first CRLF byte-identical to the scalar spec). Targets: parse (SIMD delimiter
   scan, simdjson-style), serialize/copy (vector memcpy), hash/checksum. This is a *backend* extension (owns more
   than the frontend) — the biggest, hardest, most singular piece. Do it intrinsics-first, tractably.

## The excellence bar (not just "green")
- **Fast:** the hot paths (parse/serialize/copy) measurably faster than leanc — the allocation-free story *plus*
  packed layout *plus* (eventually) SIMD intrinsics. Measure A/B same-box, report ratios + instruction/cache counts.
- **Assured:** every extension carries its HOL proof, `[oracles: DISK_THM]`, 0 cheat/admit/new_axiom. No mirrors,
  no vacuity — read the theorem *statements*. The A1 machine-code-as-oracle validator keeps working against the fork.
- **Clean + maintainable:** the fork stays a *comprehensible* delta over upstream (a patch series, not a rewrite);
  we own the proof-maintenance deliberately; document each extension's obligation.
- **Honest:** characterize residuals (like ext1's ISA boundary); refuse to fabricate primitives (like ext1's
  Div/Mod-not-faked); state ceilings, don't game them.

## Trust ledger (unchanging, stated honestly)
The Lean↔HOL tie **persists** — drorb's spec + proofs are Lean; datacake is HOL. Datacake owning the frontend does
not dissolve that (only a Lean-native backend would, which we are *not* doing). We own the proof-maintenance; no
upstream gating (fork + develop). The value is *performance + expressiveness under proof*, not seam-elimination.

## Deputation notes (ground-truth-first, or it builds a mirror)
- Real paths above; the fork recipe above; the ~25-min rebuild loop (edit below panLang = faster). Iterate proofs
  in a throwaway sandbox theory to avoid full-file rebuilds (ext1's method).
- Watch the metis-divergence trap (ext1 found a 72-min spin on an unprovable goal — bound builds, kill hangs).
- Never touch `~/src/cakeml` (the baseline + the working `cake` binary depend on it).
- The prize is a compiler *we own* that emits fast, proven, SIMD-capable machine code for the dataplane —
  the thing that makes Dragon's Orb fastest **and** most assured. Bring it there via excellence.
