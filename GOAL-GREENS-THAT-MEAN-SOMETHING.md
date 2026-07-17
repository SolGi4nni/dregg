# GOAL — GREENS THAT MEAN SOMETHING (+ plain quality)

> ⚑ One of several live goal lanes — see [`GOALS-INDEX.md`](GOALS-INDEX.md). This file is the
> **greens-that-mean-something** lane only. Don't clobber other lanes' trails.

**Spine:** *a green only counts if it REDS when the thing it guards breaks.* Second axis, equally
real: plain quality — inefficiency, bad patterns, reinvented wheels, things simply worse than they
should be.

**Set:** 2026-07-17 ~04:40 by ember (away ~5× the night's elapsed; work self-paced until blocked).

## Current thrust
The crypto-vacuity frontier is where wins are landing (Lean/lake, no cargo contention). FINDING-2
sweep (~18 carriers) DONE + pushed + main green (`lake build Dregg2` 9743 jobs). Its report surfaced a
big backlog → DISPATCHED (per [[feedback-swarm-delegate-identified-work-immediately]]): the 28 RED
dark `Circuit.Emit.*{Refine,Rung2}` modules, and the tree-wide ⊤-class defect (`CollisionResistant`
itself false-at-deployed; 6 earlier `*Regrounded` files still rest on it). Both lanes live on hbox.
⚑ Thread 1 (held Rust pile) is NOT a static pile I own — it is the live multi-terminal working tree
(40 intermixed .rs, mostly OTHER terminals' active WIP: credentials, circuit-prove, cell/*); its
owners land their own slices (a persvati `pbuild botverify` is doing exactly that). So thread 1 = pick
off only clearly-mine-and-verified pieces; do NOT force a wholesale integration.

## Next moves
1. **Harvest the 2 dispatched lanes** (28-red-Emit-modules · tree-wide ⊤-class) → verify + push.
2. **Round 3 vacuity/proof + wiring** as capacity frees (hbox lake). Named residuals: cluster-1's
   ~11 downstream `Poseidon2WideCR` uses + the `Cap8Scheme→Chip8Keyed` migration (signature-changing);
   the `RomEff` random-oracle-modelling landing site; `PairCR`/`LenBindCR` game re-grounding.
3. **Clippy → real gate** (thread 2) when cargo is genuinely idle: ember's hint — unused-import warns
   are often `#[cfg(test)]`-vs-not accidents; drive `clippy --workspace -- -D warnings` to zero, give
   non-inheriting crates `[lints] workspace = true`, drop continue-on-error. Do NOT red main mid-churn.

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
- 05:3x — **FINDING-2 sweep: ~18 injective-hash floor carriers re-grounded** (`0b0f0de37` cluster1 ·
  `a3668c8f0` cluster2 · `81e55f69f`/`c4294734c`/`974a9fb31`/`7cdf3f8a9` cluster3; all pushed, main
  green 9743 jobs). Each: proved FALSE-as-named at deployed BabyBear params (counting core), consumer
  re-grounded onto a real collision game with explicit undischarged `Eff` (the Hermine shape — NOT
  bare `CollisionResistant`, which is ITSELF false-at-⊤), mutation-canaried. Two lanes shipped
  relabeled-mirror games (`wins_imp = ⟨hne,hcom⟩` tautology) — caught by a peer AUDITOR reading proof
  bodies, both fixed to transport through real deployed objects. Fixed a RED-at-HEAD umbrella:
  `AssuranceCaseGrounded.hermine_rushing` still declared the pre-repair P→P shape (Hermine's own
  un-rebuilt downstream). ⚑ Surfaced backlog now DISPATCHED (28 red Emit modules; tree-wide ⊤-class).
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
