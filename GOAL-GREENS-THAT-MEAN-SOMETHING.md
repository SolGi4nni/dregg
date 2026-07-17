# GOAL — GREENS THAT MEAN SOMETHING (+ plain quality)

> ⚑ One of several live goal lanes — see [`GOALS-INDEX.md`](GOALS-INDEX.md). This file is the
> **greens-that-mean-something** lane only. Don't clobber other lanes' trails.

**Spine:** *a green only counts if it REDS when the thing it guards breaks.* Second axis, equally
real: plain quality — inefficiency, bad patterns, reinvented wheels, things simply worse than they
should be.

**Set:** 2026-07-17 ~04:40 by ember (away ~5× the night's elapsed; work self-paced until blocked).

## Current thrust
Cargo lock is held by co-tenant `dregg-mcp --release` builds → threads **1 (held Rust pile)** and
**2 (clippy)** are BLOCKED. So drive the **Lean** threads (lake on hbox `~/ts-verify/dregg`, warm
oleans — no cargo contention) + read-only discovery, and take the cargo threads the moment the lock
frees. **Integrator = single cargo-lock owner. Fan reads wide, keep builds narrow.**

## Next 3 moves
1. **Proof engineering, round 2** (unblocked; lake/hbox). Round 1 landed 2 real strengthenings and
   *named but did not action*: `PolisMembrane.transfer_safety` (a universal-acceptance hypothesis
   standing in for an unmodeled shield — a laundered assumption; "a larger threading job"), the
   `Fibration.lift_collapse` family (decorative, 0 external uses), `PolisStreamCarrier.
   polisFloorProp_inhabited` (`fun _ => True`). Strengthen until a real mutation reds it; REFUSE
   anything whose "vacuity" is an intentional thesis (round 1 rightly refused `computeThreshold 0 = 0`
   and `no_bad_debt`).
2. **Wiring hunt, round 2** (read-only discovery; the wire itself is cheap YAML). More tests/gates
   that exist, assert real things, and run nowhere.
3. **Held Rust pile** (thread 1) the instant the lock frees: verify each (compile + does-it-bite),
   commit sound path-limited, revert what does not hold. Never sweep other terminals' WIP; never `-A`.

## Open / flagged for ember
- Sign-floor CI step costs ~22 min via `CryptoVerifyAll`; narrowing that ONE step to
  `Dregg2.Crypto.AcvpKats` = ~130 s for the same sign-floor coverage (loses `=spec`/NttFaithful).
- **In flight:** a P→P laundering in the crypto TCB — `HermineHashCRRegrounded.lean:121`
  `hermine_concurrent_forgery_advantage_bound` carries a FREE ensemble discharged by its own `hmsis`
  hypothesis (the exact pattern the VRF sibling `VrfRegrounded` was repaired for). HashCR leg is
  sound; only the MSIS leg is rotten. Repair = port `uniqBreakToMsisSolver` (a real extractor +
  sampled-MSIS bridge over the real dichotomy `concurrent_forgery_breaks_hashcr_or_msis`). Lane firing.
- `check-emit-gate-weld.py` is RED on main — real descriptor drift (`dregg-derivation-v1` Rust 379 vs
  Lean 393; garbled-eval 32 vs 47) from another lane's mid-flight circuit refactor. Gate working.

## In flight
- **FINDING-2 sweep: ~20 injective-hash floor carriers re-grounding** — 3 empowered lanes (clusters:
  1=Poseidon2WideCR/Compress8CR/compress4Injective; 2=StateCommit/Factory/CommitmentBinding/
  MacaroonDischarge; 3=QueueRoot/PreRotation/Council/FriVerifier/Sponge/Blake3/Beacon/DomainSep).
  These are false-as-named at deployed params, used as free HYPOTHESES, none re-grounded. Template =
  the just-landed `HermineHashCRRegrounded` (4fe326cce) + `HashFloorHonesty` + `FloorRegroundedConsumers`.
  ⚑ LESSON (ember): dispatch a surfaced backlog to empowered agents IMMEDIATELY — logging it =
  it never gets done. [[feedback-swarm-delegate-identified-work-immediately]]

## Done log
- 04:58 — **Crypto-TCB laundering repaired: `hermine_concurrent_forgery_advantage_bound`** (`4fe326cce`,
  pushed): the free `hmsis : MSISHardQuantShape` hypothesis (a P→P) is GONE; the MSIS advantage now
  comes from a real extractor `forgeryToMsisSolver` DERIVED from the forger, union-bounded (forger ≤
  derived-MSIS + derived-collision), each a real game advantage, with the honest undischarged `Eff`.
  Canary bites (break the extractor challenge coord → `sorryAx` cascades RED). `#assert_all_clean: 14`.
- 04:55 — **Proof engineering round 2: 3 strengthenings, each canary-proven** (`47413e3e9`,
  `9984063f7`, `986bc1c2b`). `transfer_safety`: discharged the laundered acceptance hypothesis —
  transported the shield across the membrane so the floor holds for EVERY controller, no acceptance
  assumption (canary: a `decide`-proven adversary reaches dist=9 without the shield). `lift_collapse`:
  refuted round 1's "decorative" charge (3 internal uses) — contraposed it into `not_apex_of_violation`,
  the operationally-real direction. `polisFloorProp_inhabited`: verified the "inherent" excuse is true
  of the SHAPE, then supplied the honest nontrivial leg over concrete `Obs=Bool`. Refused 2 more that
  would degrade (`EnergyGame.unitBase.floor` deliberately isolates the grade). Found + FLAGGED (not
  rushed) the HermineHashCR P→P laundering — see Open.
- 04:36 — **ML-DSA Array UInt32/UInt64 ring twins** (`87ee60ab3`): additive; UInt64 accumulators
  (products hit 2⁴⁶ — a bare UInt32 multiply truncates); 6 fast-vs-**pure** `#guard`s; AcvpKats
  byte-exact KAT gate green. **MEASURED ~2%, not the 10× I claimed** (Lean unboxes small Nats; the
  real bottleneck is `Array` bounds-checks, not `Nat` boxing). Landed for the clearer representation.
- 04:35 — **CI no longer rebases ember's branch** (`91926bb15`): deleted lean-seed.yml's `pin` job,
  which `git pull --rebase --autostash`ed main on EVERY seed build to push provenance its own NOTE
  calls decorative. The one load-bearing line (`TAG=lean-seed`) is a stable constant, already set.
- 04:35 — **pre-push hook's 2 mystery errors, both REPRODUCED then fixed** (`91926bb15`):
  `'..' is outside repository` (blank stdin line → 4 empty vars → `git diff ".."` parsed as a
  *pathspec*) and `not a valid commit range` (a remote oid this clone never fetched — terminals
  rebase/force-push). One `usable_base` guard (non-empty ∧ not-all-zeros ∧ `cat-file -e` present),
  4 call sites; fails OPEN on scope, still CLOSED on a real secret.
- 03:45 — **Archive trim 272 MB → 23.87 MB** (`4f5f2c382`): Lean v4.30 emits **three** per-module
  inits; the trim cut **one**, so `runtime_initialize_aesop_*` read as a real call and dragged the
  whole proof cluster (783 members / 104 MB — measured **0** real-call boundary edges). Plus a
  plausibility floor (200) calibrated for the OLD buggy count that **silently** discarded the correct
  153-member trim. Probe-verified: links + round-trips a real committing turn.
- 03:06 — **The trim/GC silently no-opped on ALL of Linux/CI** (`31c85208c`): the nm parser was
  macOS-only, *duplicated* into both functions so the same bug existed twice. One shared
  `nm_split_member` + LOUD warnings at both bails. Also `fetch-lean-seed.sh`'s SIGPIPE — the same bug
  I'd fixed on the publish side and missed on fetch.
