# codex — datacake deputation entry point

**You are deputized to bring datacake to completion via excellence.** Your charter is
[`DATACAKE-EXCELLENCE-BRIEF.md`](./DATACAKE-EXCELLENCE-BRIEF.md) — read it fully first. This file is just the
cold-start pointer.

## Start here
- **The fork:** hbox `~/dev/datacake` (rsync of `~/src/cakeml` @ ed31510b3 *with* `.hol` artifacts → incremental).
  NEVER touch `~/src/cakeml` or `~/src/HOL` (baseline + the working `cake` binary depend on them).
- **Build:** `taskset -c 0-15 nice -n 15 ~/src/HOL/bin/Holmake -j 8` in `pancake/proofs` (~25-min full-frontend loop;
  edit below panLang = faster; iterate proofs in a throwaway sandbox theory to skip full rebuilds).
- **What's done (ext1):** `Div/Mod` added + proven green, `/`/`%` computing. Patch: `divmod.patch`. The one residual:
  the all-ISA `every_inst_ok_less_*` chain hits `c.ISA = x86_64` (CakeML's word-div is x86_64-only).

## Your axes, in order (from the brief)
1. **Close the ISA residual** — thread `ISA=x86_64` through ~7 theorems, or make x86_64 a datacake design invariant.
2. **Packed-byte stores** — kill the byte-per-word-slot serialize layout.
3. **StageProg-native lowering** — the genuine per-constructor compiler (the Lean side has the `StageProg` DSL +
   `denote` reference; the copy-stub compiler is the thing you replace).
4. **Mechanical-sympathy pass** — register quality, cache-shape, the hot-path ABI; measure A/B vs leanc.
5. **★ Verified SIMD intrinsics** — proven `PCMPEQB`/`PMOVMSKB` byte-scan + vector memcpy for parse/serialize.
   Intrinsics-not-auto-vectorization: one hard beautiful proof each. The audacious, singular piece.

## The bar (non-negotiable)
Fast (measured, not asserted) **and** assured (`[oracles: DISK_THM]`, 0 cheat/admit/new_axiom, read the theorem
*statements* — no mirrors, no vacuity) **and** clean (a comprehensible patch series over upstream) **and** honest
(characterize residuals like ext1's ISA boundary; refuse to fabricate primitives like ext1 refused fake Div/Mod;
state ceilings, never game them). Watch the metis-divergence trap (ext1 found a 72-min spin — bound builds, kill hangs).

The prize: a compiler *we own* emitting fast, proven, SIMD-capable machine code — the thing that makes Dragon's Orb
the fastest **and** most assured dataplane on the planet, *because the fast code is the proven code.* Go build it well.
