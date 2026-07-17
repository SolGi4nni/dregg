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
### ⚑⚑⚑ RUST DEFECT BACKLOG (07-17, read-only discovery lane — VERIFIED by re-reading code)
7 Tier-1 SOUNDNESS findings in the deployed system (full list + falsifiers in the discovery lane's
report). Handled per be-thoughtful-not-trigger-happy: isolated+clear ones get a falsifier-test-first
fix lane; consensus/crypto/value ones get a READ-ONLY deep-verify (real-hole vs named-seam) before ANY
fix — NOT a blind rewrite.
- **#2 bridge receipt** (`cell-crypto/note_bridge.rs:1157`) — `verify_bridge_receipt` accepts ANY
  trusted key; signer not bound to `destination_federation` → trusted fed A finalizes a bridge for
  dest B, burns the note with no B-side mint. SPOT-CONFIRMED. → fix lane (a3fac0ad, falsifier-first).
- **#6 overflow** (`node/equivocation_court_service.rs:663` + `sdk/factories.rs:177`) — `req.amount +
  fee` wraps → escrow≠bond. → same fix lane.
- **#1 fail-OPEN consensus hole** (`node/blocklace_sync.rs:1062`) — DEEP-VERIFIED REAL: solo-branch keys
  on the PQ-PROJECTED count; a live member with no published ML-DSA key (an acknowledged state) collapses
  a node to SOLO → finalizes with NO quorum → divergence; genesis-hybrid-unconfigured partitions the whole
  federation. Raw counts computed but never gate. Cited test covers only the vote layer. ⚑ ONE-LINE FIX
  (gate solo on RAW admitted count, fail-closed) → fix lane ac3c117a (falsifier-first). **Land before launch.**
- ⚑⚑⚑ **#3 predicate FORGERY — LIVE, PROVEN, fix NEEDS EMBER (circuit change).** `credentials/verification.rs:261`
  + `intent/fulfillment.rs:605` call the BARE `verify_predicate_proof` against the proof's OWN commitment
  (`x==x`) → a genuine `Gte(18)` proof attaches to a DIFFERENT credential; a foreign-state-root proof is
  accepted. TWO falsifier tests written (`#[ignore]`d, they FAIL today = the forgery is live) + misleading
  docs corrected — LANDED `214e531a9`. ⚠ THE FULL FIX CANNOT be a one-session drop-in: the sound
  `verify_predicate_proof_third_party` needs a `facts_root` that DOES NOT EXIST as a presentation STARK
  public input (`presentation_descriptor_witness.rs:29-80` binds only federation_root/predicate/timestamp/
  tag/revealed_facts_commitment/height). The fix is a CIRCUIT ripple → VK-changing: (1) expose `facts_root`
  as a presentation PI over the token's real fact set; (2) producer attaches `BridgeFactAttestation` per
  predicate; (3) route `verify()`/`verify_predicate_requirement` through the third-party fn. Introduced by
  `bac9e2b95` (closed the disclosure leg, left predicate self-referential). **Launch-critical; ember's call
  on the circuit change** — held per be-thoughtful-not-trigger-happy (soundness-critical circuit surgery).
- **#7 amended-quorum** (`blocklace/ordering.rs:307`) — REAL but LOW: off the live `tau` path (only bites
  `tau_unified` consumers amending ABOVE supermajority). Fix = `max(group.threshold, supermajority(n))`. QUEUED.
- **#4 value_binding unbound** (`cell-crypto/value_link_zk.rs:470`) — REAL constraint gap but UNWIRED (0
  non-test consumers) = a named seam; danger is the DOC asserting a binding it doesn't deliver. Fix = correct
  the doc + forbid-wiring guard until bound. QUEUED (doc/guard, not a live hole).
  Also latent/deprecated (discounted): addressing.rs:341, constitution.rs:168, storage/blinded+operator (deprecated).
- **Tier-2 silent-gate + Tier-3 correctness + item-22 postcard-class (~15 sites) + item-24 CLI fail-open**:
  proven-pattern applications, QUEUED to fan out path-limited when a build lane frees (lock ceiling ~2).
  Headliners: watcher.rs:363 credits on RPC balance (never calls the trustless verifier — the "Discord
  pay on MockWatcher" class); cipherclerk.rs:2852 PQ-sign `unwrap_or_default` masks a signing failure;
  erasure.rs:195 RS-encode error swallowed; presentation.rs:446 revealed-facts commitment only ~30-bit.
- Hollow-test batch (item 23a-f) → fix lane (aafb4663). Efficiency/dup deprioritized (topological_subset
  Θ(P·N)/round; hex_decode_32 duplicated 8-9×).
- Sign-floor CI step ~22 min via `CryptoVerifyAll`; narrow to `Dregg2.Crypto.AcvpKats` = ~130 s.
- `check-emit-gate-weld.py` RED on main — real descriptor drift from another lane's circuit refactor.

## In flight
- **FINDING-2 sweep: ~20 injective-hash floor carriers re-grounding** — 3 empowered lanes (clusters:
  1=Poseidon2WideCR/Compress8CR/compress4Injective; 2=StateCommit/Factory/CommitmentBinding/
  MacaroonDischarge; 3=QueueRoot/PreRotation/Council/FriVerifier/Sponge/Blake3/Beacon/DomainSep).
  These are false-as-named at deployed params, used as free HYPOTHESES, none re-grounded. Template =
  the just-landed `HermineHashCRRegrounded` (4fe326cce) + `HashFloorHonesty` + `FloorRegroundedConsumers`.
  ⚑ LESSON (ember): dispatch a surfaced backlog to empowered agents IMMEDIATELY — logging it =
  it never gets done. [[feedback-swarm-delegate-identified-work-immediately]]

## Done log
- 14:1x — **28-red Emit-refine campaign: 25/28 REPAIRED + pushed** (`c6d6556ee`,`59b10638b`,`e0e6a7e50`,
  `7d1cf1136`,`3dd04f611`,`4ee46579d`,`5563d2b5a`): root cause = denotations drifted ℤ`=0`→BabyBear
  congruence `≡0 [ZMOD p]` + `factCommitLookup` arity-2→arity-4 blinded, invisible because the modules are
  outside the `Dregg2` glob (built nowhere). Faithful mod-p fix, kernel-green, `#assert_axioms`-clean,
  mutation-canaried. ⚑ FOUND: a COMMITTED MERGE CONFLICT on main (`PredicatesRelationalCompoundRefine.lean`
  18 markers + `Rung2Full` 12) from `ddd2408c5` (07-15 fresh-cut), sat broken for days (dark orphan). →
  resolve-lane a4ec7a4d (conflict + mod-p, completes 28/28). The now-wired `Dregg2.Claims`/76-module gate
  catches this class going forward.
- 14:0x — **Rust soundness harvest** (falsifier-first, all pushed): **#1 fail-OPEN consensus hole FIXED**
  (`a3ea501ec` — solo now keys on RAW admitted count, fail-closed on collapsed PQ-projection; falsifier on
  the EXECUTION path RED→GREEN + liveness companion + canary). **#6 overflow FIXED** both sites
  (`cff29ccde` — checked_add + falsifiers). **#2 bridge-receipt** = real primitive hole but BOUNDARY-CLOSED
  (BridgeFinalize retired in dregg3, zero prod callers) → hardened defensively (`cff29ccde`) — my over-alarm,
  corrected. **#3 predicate forgery** = LIVE, falsifier tests + doc-fix landed (`214e531a9`); full fix = a
  circuit PI change, flagged for ember (see above). Dispatched next: isolated Tier-2/3 (erasure/doctor/
  fee_policy/ring_trade).
- 13:5x — **28-red dark Emit-refine repairs landing** (`c6d6556ee`, `3dd04f611`, pushed): field-faithful
  mod-p migration for the drifted refinement modules + `FinKernelStep` default + the Gt/Lt/Le/Neq predicate
  refines. These modules were unreachable from the `Dregg2` root (built nowhere) — a lane is repairing the
  drift so they can join the now-wired `Dregg2.Claims`/76-module gates. Rust fix lanes (#1 fail-open consensus,
  #3 predicate forgery, #2/#6 isolated, hollow tests) still in flight, falsifier-first.
- 13:2x — **Tree-wide ⊤-class defect re-grounded** (`7beec0c6e`, pushed, main green 9743): the 6 earlier
  `*Regrounded` files that rested on bare `CollisionResistant` (= `HashCRHardQuant F ⊤`, false at any
  compressing family) now condition on `HashCRHardQuant F Eff` with explicit undischarged `Eff` — via
  `_eff` siblings routing the finder-advantage=game-advantage identity, canaried. Surfaced 1 more site
  (`WireAkeRegrounded:99`, same class, 1-line pattern) → DISPATCHED immediately (aea6ebd lane).
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
