/**
 * MINA_TIER — how much of a leg runs.
 *
 * ── WHY ────────────────────────────────────────────────────────────────────
 * Measured 2026-07-30, `scripts/check-mina-attestation.sh` was ~19 legs and its
 * `--self-test` was ~6.5 hours — 56% of the entire default `local-gates.sh`
 * budget for one directory. And the arc's actual defects were not found by any
 * of it: they were found by CHEAP EXHAUSTIVE OUT-OF-CIRCUIT DIFFERENTIALS.
 *   * the braid's twin walks 11,303 segments in seconds and found four defects
 *     that "would each have compiled and proved cleanly for as far as any
 *     affordable run reaches" — a full output buffer on entry, `sample_bits`
 *     taking the low bits, `alpha_pow` starting at one, an undefined path
 *     direction;
 *   * the uniform-walk checker walks 820 boundaries and found ALL NINETEEN
 *     block-to-block joins broken — first observable at instance 46, sealed at
 *     820, so "any affordable proof run would have been green and wrong".
 * The cheap tier is therefore not a compromise. It is, on this directory's own
 * record, the BETTER INSTRUMENT, and this module is what lets a leg run it
 * without paying for the Pickles compiles that follow it.
 *
 * ── THE TIERS ──────────────────────────────────────────────────────────────
 *   0  out-of-circuit only. Twins, differentials, plan/census reproduction,
 *      arithmetic, pins. NOTHING COMPILES A CIRCUIT. Target: seconds.
 *   1  + compile and prove ONE representative instance per family. Minutes.
 *   2  everything the leg has: full chains, every family member, every splice.
 *      Hours. This is what `npm run <leg>` does with no MINA_TIER set, so a
 *      lane's own invocation is UNCHANGED by tiering.
 *
 * ── DISCIPLINE ─────────────────────────────────────────────────────────────
 * A tier that silently narrows itself is the `Documented ≠ Detected` class, so:
 *   * the DEFAULT is 2, not 0. Tiering can only ever be something a caller
 *     ASKED for; it is never what you get by forgetting.
 *   * an unparseable `MINA_TIER` is a FAILURE, never a fallback to a default.
 *   * `tierStop` prints a PASS line that NAMES the tier and ENUMERATES what did
 *     not run, so a tier-0 transcript can never be read as a full one.
 */

function parseTier(): number {
  const raw = process.env.MINA_TIER;
  if (raw === undefined || raw === '') return 2;
  if (!/^[0-2]$/.test(raw)) {
    console.error(
      `FAIL: MINA_TIER='${raw}' is not one of 0, 1, 2. A tier that cannot be parsed must not ` +
        'fall back to a default — that is how a run silently stops testing.',
    );
    process.exit(1);
  }
  return Number(raw);
}

/** The tier this process runs at. 2 (everything) unless a caller narrowed it. */
export const MINA_TIER: number = parseTier();

/** True when this run is allowed to do tier-`n` work. `atTier(1)` guards a compile. */
export function atTier(n: number): boolean {
  return MINA_TIER >= n;
}

/** True when this run must NOT do tier-`n` work. The negation, for guard readability. */
export function belowTier(n: number): boolean {
  return MINA_TIER < n;
}

/**
 * Print a leg's tier-0 PASS line and say WHAT DID NOT RUN.
 *
 * `name` is the leg's usual PASS banner stem (`ROOT-FRI-BRAID`), so the shell
 * gate greps `=== ROOT-FRI-BRAID TIER-0 PASS ===` and can never mistake it for
 * `=== ROOT-FRI-BRAID PASS ===`. `notRun` is prose naming the sections skipped
 * and the tier that runs them — a reader of the transcript must not have to go
 * to the source to find out what a tier-0 green does not cover.
 */
export function tierStop(name: string, checks: number, elapsed: string, notRun: string): void {
  console.log(`\n=== ${name} TIER-0 PASS === ${checks} out-of-circuit checks, ${elapsed}`);
  console.log(`    NOT RUN at MINA_TIER=0: ${notRun}`);
  console.log('    (nothing in this run compiled a circuit)\n');
}

/** The same, for a leg that stops after its tier-1 representative instance. */
export function tierStop1(name: string, checks: number, elapsed: string, notRun: string): void {
  console.log(`\n=== ${name} TIER-1 PASS === ${checks} checks, ${elapsed}`);
  console.log(`    NOT RUN at MINA_TIER=1: ${notRun}\n`);
}
