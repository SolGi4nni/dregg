# The Dark Bazaar — a private, proved game economy

*North star and current implementation ledger. Re-grounded 2026-07-22 at
`6d0e024f19` from the commit graph, current source/tests, `HORIZONLOG.md`,
the fhEgg handoff, and the compacted-session record recovered with `cv`.
The mixed checkpoint `7ba02bc122` is useful WIP, not evidence that every
contained lane is gated. Uncommitted frontend/game edits are excluded.*

Companions:
`HANDOFF-FHEGG-FEASIBILITY-CODEX.md` for the detailed cryptographic and
protocol ledger, `FHEGG-RESEARCH-FRONTIER-2026-07-22.md` for the proving-stack
and threshold-FHE research program, and `HORIZONLOG.md` for the chronological
burn-down.

## 0. The image, and the exact sentence we can say today

Figures walk luminous threads across a black field. Each player sees their own
thread and the fixed lights where proofs anchor; no public surface receives the
private route between them.

The north star remains:

> The dealer cannot see the cards, the players cannot see each other, and every
> deal carries a proof that the declared rule was followed.

The implementation now reaches much farther than the original 2026-07-18
“crawl” document:

> One authority-bound Dark Bazaar game can be mounted through web, Telegram,
> and Discord; its public journey is viewer-blind; finalized private receipts
> are consumed by a durable private worker; and an exact receipted consequence
> can change an authenticated Dungeon world.

That sentence is real. The stronger sentence—*the entire live market is
house-blind, every private representation is proved to be the same opening,
and a committee finalizes the full shielded result*—is still the apex, not a
shipped claim.

### Status vocabulary

- **LIVE PATH** — present in the production call graph, with focused hostile
  tests or a captured gate.
- **GATED SUBSTRATE** — executable and tested, but not the complete live
  product boundary.
- **BANKED WIP** — committed so it can be continued, without a composed green
  claim.
- **FRONTIER** — the relation, protocol, or product remains to be built.

## 1. The four halls, regraded (re-grounded 2026-07-25 against the code)

*This table was stale in BOTH directions. It understated the crypto — the halls now have viewer-blind
`Offering`s that run house-blind end-to-end under a collective key (n−1 refused), oracle-validated. And it
overstated the product — none of that runs on a live path yet: the ceremonies are SIMULATED in one process,
the halls are unregistered (surface only in tests), and the one "LIVE" hall's actual clearing still settles by
plaintext bid revelation. Both truths below.*

| Hall | Mechanic | Current cut (2026-07-25) | The gap to a live game hall |
|---|---|---|---|
| **The Sealed Exchange** | private allocation → receipted winner + one game effect | **LIVE consequence spine; clearing privacy UNWIRED.** The Bazaar journey, viewer-blind publication, durable private-receipt worker, crash recovery, and Dungeon consequence are LIVE (`private_bazaar_worker.rs` → `private_clearing_consequence.rs` → a cap-bounded `SignedTurn`). But the live clearing settles by **plaintext bid revelation**; the N4K4 HidingFRI private-book relation (`circuit-prove/src/dark_bazaar_private.rs`) is proved + emitted + unit-tested but a **test-only producer** — the worker never calls `settle_private_verified`. | Wire the private producer into the live worker; pin `order_root`; lift the fixed N4K4 cap (a new Lean-emitted descriptor); a no-single-viewer producer is a further composition. |
| **The Dark Pool** | constant-product over hidden reserves | **Full viewer-blind Offering + house-blind ceremony RUN — but SIMULATED + unregistered.** `DarkPoolOffering` (`dark_pool_offering.rs:813`, render/render_for) + the threshold-BFV + n-of-n relin collective ceremony execute; the `x·y=k` invariant is verified under the collective key, n−1 refused, unfair swaps caught. The ceremony is **in-process (one machine, simulated parties — its own doc says so)** and the Offering is **not in `CATALOG_KEYS`** (surfaces only in tests). | Register it (→ auto-surfaces on Telegram); make the ceremony **distributed across clients** (each extension holds a share); the swap-*output* needs division (a real crypto gap — start verify-only). |
| **The Oracle Pit** | confidential prediction / quadratic pricing | **Full viewer-blind Offering + house-blind pricing RUN — but SIMULATED + unregistered + no market lifecycle.** `OraclePitOffering` (`oracle_pit.rs:684`) + the quadratic-cost / public-odds pricing run under the collective key (oracle-validated bit-exact). Missing everything that makes it a *market*. | Build order intake, **outcome resolution** (the oracle), settlement/payout, a positions ledger; register; distribute the ceremony. (Lead vertical — most new build.) |
| **The Netting Vault** | hidden guild obligations → reveal only the net | **Crypto RUNS house-blind (test-only); NO Offering yet.** Multilateral netting (conservation + compression) runs under the collective key at guild scale (8 parties, n−1 refused), signed nets, in `fhegg-fhe/tests/` + `metatheory/Market/NettingVault.lean`. **No `Offering` exists** — a proposed panel. | Build `NettingVaultOffering`; wire to the consequence plane; distribute the ceremony. Simplest (additive, no relin). |

> **CORRECTION 2026-07-26 (appended; the Sealed Exchange row above is now stale in the bazaar's
> FAVOUR).** The row says *"the worker never calls `settle_private_verified`"* and *"the live
> clearing settles by plaintext bid revelation."* Both were true when written and were fixed the
> next day by `4aeba707d` (*"market: the proven private-book relation was reachable only from tests
> — the production worker now calls it"*), then `2bab1cfe5`, `e2a517cdf`, `ad88024c8`. The proof is
> genuinely in the supervisor's tick path today:
> `private_bazaar_service.rs:586-588` → `settle_and_capture` (`:124`) →
> `deployment.settle_private_clearing_verified(...)` → `private_clearing.rs:1020
> settle_private_verified`. `docs/deos/DREX-TIER-STATUS-2026-07-24.md:188-198` carries the same
> stale claim and is corrected by the same commits.
>
> **The gap moved; it did not close.** The missing piece is now the *ingress producer*, not the
> proof: `PrivateBazaarSealedIngressQueue::submit`
> (`dreggnet-catalog/src/private_bazaar_ingress.rs:272`) has **zero non-test callers**, so the
> supervisor drains a queue nothing can fill, and a full-filesystem search finds zero instances of
> `sealed-ingress-v1.queue`, `finalized-private-bazaar-v3.spool`, or any `by-blind/*.binding` — the
> hall has never written a byte of durable state. The module names the missing component itself
> (`private_bazaar_live.rs:230-234`: *"This is what a production bid collector holds"*); that
> collector does not exist in this repo. Full inventory:
> `docs/reference/ECONOMY-SCHOLAR-2026-07-26.md` §3.5.

**The crypto keystone — the same-opening apex — is PROVED + EMITTED but a pure UNWIRED SEAM.** A 10-file
kernel-clean Lean family (`FHEGG-SAME-OPENING-APEX.md`) proves the relation that turns *proof-blind* (a trace
builder sees the bids) into *house-blind* (no single party ever does), and it is emitted as a descriptor — but
it has **zero Rust consumers** (no `circuit-prove` call, no registry). Wiring it is what upgrades the halls'
"house-blind" from a threshold-decrypt property to the full apex.

The correct boundary today is: **the game-consequence plane is genuinely LIVE**; the market-clearing
**privacy is proved + running-in-test/simulation but not wired into that plane**; and "no single viewer" is a
**simulated in-process property, not yet a real distributed one**. Turning all three real — hall by hall,
across web/Telegram/Discord, with the player's extension participating in a real distributed FHE ceremony — is
the build (`streamed-cooking-shannon` program plan). The **game gauntlet is the proving ground**: the halls
must survive the full cell/receipt/finality/consequence loop as game mechanics, house-blind and malicious-
secure, before any of it graduates to real "dreggfi" (the `DREGGFI-*` docs) — the game is the honest,
low-stakes testbed where privacy + proof + enactment are exercised end-to-end.

## 2. What the sprint actually landed

### 2.1 One game, not three frontend reimplementations

- `0d87c03cd9`, `cf1e076fe3`, and `60aa8ef29d` mounted the private
  Bazaar journey, unified the player receipt grammar, and joined an exact
  private result to a game consequence.
- `05aed2c8e2`, `cd19363ca8`, `d1b181dec7`, and `ac32f1cc54`
  bind actions, shielded operations, artifacts, and the Telegram/Discord
  adapters to a durable host incarnation, session generation, advertised head,
  and signed authority envelope. An old tab or prior generation cannot be
  silently rewrapped as a fresh action.
- `6d0e024f19` closed a real full-Lean deployment failure: the timed close
  loop now executes on a Lean-registered runtime thread, so the reality gate no
  longer silently refuses an otherwise valid close.

The frontend invariant is now concrete: web, Telegram, and Discord consume the
same catalog/game spine and the same authority-bound session. Rich private
receipts may exist in direct custody; shared cards cannot contain the raw
winner, witness, proof diagnostics, state heads, or private operation payload.

### 2.2 A durable private consequence plane

- `cd3ea449b0` runs the private receipt worker. The worker owns the raw
  finalized evidence and advances a durable
  `Prepared → Dispatching → Applied → Committed` authority journal.
- `9723e14ba5` supervises authenticated receipt discovery; semantic reissue
  can refresh a local envelope without changing the logical settlement core.
- `d08100655b`, `7bd87790fb`, and `ed5c4c5643` authenticate
  crash-recoverable world cells and refuse missing or discontinuous checkpoint
  authority. `190938372b` routes Bazaar reward pricing through the durable
  Dungeon authority rather than a shadow ledger.

The result is not “a UI says you won.” A deployment-pinned settlement can
produce one exactly-once operation against the same authenticated character
world used by the Dungeon/Descent surfaces, while the frontend receives only a
viewer-safe consequence card.

### 2.3 Exact finality is real, but exact v3 is not dark value

- `f8836e4498` executes exact FNSP-v3 at block finality.
- `d5bb140504` closes the private dependent
  claim → CTM1 ingress → ordinary finalization → exact wake path atomically.
  FRC1 persistence/query and CTM1 typed finality are in the same banked wave.
- Exact-v3 verifies a HidingFRI carrier and enforces accumulator continuity,
  accepted-proof custody, durable state, replay, and terminal disposition.

V3 must not be promoted into the final privacy claim. Its public statement
still exposes value/asset/nullifier coordinates, its current live authority is
not the committee-finalized v4 core, and its characterized execution slice is
the exact anti-double-spend/receipt foundation beneath dark value.

### 2.4 The fields-root and Descent quarantine was repaired

- `8113f7a55e` cuts the v11 exact fields-root and ledger-root-v3 epoch. Raw
  `u64` keys and full field bytes are committed faithfully; the concrete
  “add one BabyBear modulus to the source bytes” aliases are regression teeth,
  and populated legacy stores are refused rather than silently reinterpreted.
- `e63baf8fa5` rebuilds the fixed-eight Descent custody census on that exact
  root and installs its canonical-v2 custom-VK door. The HidingFRI proof binds
  the native fields root and the six published custody totals to the declared
  Descent writes.
- `5d538dabc4` emits the exact refusal-fields transition used at the repaired
  boundary.

The previous handoff’s “quarantined census over a lossy folded fields root” is
therefore stale. The census is now meaningful at the repaired v11 epoch; that
does not make every future aggregate-game proof automatically live.

## 3. The shielded cryptographic boundary

### 3.1 The honest whole-note proof

The artifact once mislabeled as the full shielded v4 apex was deliberately
deleted and replaced in `f540ed95a1` by
`shielded-whole-note-swap-substrate-v1` (FWS1). It is a real HidingFRI
relation over one hidden two-input/two-output whole-note swap:

- full-width nullifier and value/asset binding;
- exact predecessor and append paths;
- conservation and output-note root;
- exact before/after state endpoints;
- strict canonical proof decoding and a code-owned hiding verifier.

This is a major proof stone. It is intentionally not named v4 because it does
not carry the semantic apex’s complete 19 Dark-AMM lanes, 27 ring lanes, fixed
FXC4 rule, live output-note installation, or committee finality.

### 3.2 BFV carrier, terminal, and LogUp

The earlier q0 terminal prototype was correctly quarantined because a context
hash did not prove that its private terminal product was the same opening as a
carrier coefficient. The repair wave now contains:

- exact Lean q0 radix/carrier laws and production forward/inverse identities
  (`13357f84c2`, `7c61dbe1a7`, `9066ab2447`);
- a Lean terminal-product/spectral-trace binding
  (`9dbb0bef55`);
- exact public-row LogUp manifests and fixed KAT proofs
  (`057a9e904a`);
- in the mixed checkpoint `7ba02bc122`, a fused one-coordinate HidingFRI
  relation joining the exact 4,096-term private slice to terminal arithmetic.

The parent public terminal remains fail-closed, correctly. The fused cut is one
coordinate, not the complete 98,304-equation private NTT-family terminal, and
the public q0/N=8 LogUp proof is a fixed known-answer relation rather than a
private runtime carrier.

### 3.3 Dealerless is now a typed protocol boundary, not a wish

The FHTRI005 path performs real threshold-BFV candidate generation, keeps
candidate and MAC material in party-local custody, commits the roster/session,
uses a joint beacon, proves the full ordered cross-term identity in Lean, and
durably tombstones protected FHTRI004 rows after one use.

It deliberately stops at `AwaitingCrossTermProvider`. A production
malicious-secure post-quantum chosen-input VOLE/OT provider (or equivalent) is
still required for the distinct-party MAC cross terms. The experimental q0
commitment round also still refuses public ceremony authority: it lacks an
authenticated broadcast and a public same-opening proof between the existing
VSS/Ristretto and q0 commitments. “Dealerless algebra exists” is true;
“the trusted dealer is gone from the live system” is not yet true.

### 3.4 What “house-blind” still requires

The final shielded apex must provide one canonical witness and one accepted
statement that simultaneously proves:

1. the hidden note opening produces the full nullifier and wide value/asset
   commitment;
2. the same opening supplies the BFV/TFHE market computation and any
   conservation/range representation;
3. the complete 19-lane Dark-AMM and 27-lane ring consequence obeys the pinned
   FXC4 rule;
4. the exact accumulator and output-note tree advance atomically;
5. the persistent v4 frame is signer-independent and finalized by the
   federation/committee; and
6. no single prover, dealer, issuer, or frontend gains the whole witness.

Until those six are installed together, “proof consumers cannot see the
witness” and “the house cannot see the witness” remain different claims.

## 4. fhEgg and GPU reality

The sprint substantially expanded Dregg-owned portable GPU work:

- exact BFV odd NTT families and batched validation run through WGPU;
- TFHE comparison/selection, blind rotation/PBS, HidingFRI folds, and several
  MSM/fold paths have exact CPU differentials;
- `e100aae2a1` adds an exact WGPU crossover harness and an optimized
  two-elements-per-thread odd-NTT path;
- `07ccddf4ac` proves the deployed odd-root orders rather than trusting table
  folklore.

This is not a blanket “fhEgg runs on GPU” claim. The full market pipeline is
not one resident schedule; several custody/range-proof paths remain classical
Ristretto/Bulletproof work; the complete BFV terminal is not live; and the new
crossover benchmark is ignored/on-demand until run on the intended discrete
GPU. Performance authority belongs to exact release-mode measurements on hbox
or persvati, after residue-for-residue validation.

## 5. The private-game organ is larger than the Bazaar

The reusable operation is:

> Evaluate a proved rule over hidden player state, reveal only the permitted
> result, and bind that result to the cells, receipts, and world transition
> that enact it.

That organ already has composition material for:

- private guild votes and aggregate preferences;
- role/rating/blocklist-aware matchmaking and raid formation;
- hidden-hand legality and exact private shuffles;
- sealed loot allocation and Dungeon consequences;
- party predicates over hidden inventory, reputation, or history;
- season-end netting and private inter-party bargaining.

Reuse the shared identity, authority epoch, world-cell, receipt, predicate, and
frontend organs. Do not inherit an older crate’s leakage semantics merely
because its public game rule has the right name. The relation should be
Lean-authored or refined where it decides value; Rust/WGPU remains the fast
implementation boundary when the refinement and protocol identity are pinned.

## 6. Baton for the next swarm

The next work is not another mock screen or another detached algebra lemma.
The shortest path to the promise is:

1. finish and gate the canonical shared-witness FXC4/v4 relation, including the
   19+27 consequence lanes and exact output notes;
2. replace `AwaitingCrossTermProvider` with a malicious/PQ, roster-bound,
   one-use cross-term provider and complete authenticated q0 broadcast /
   same-opening authority;
3. install v4 persistence, selector, output-note mutation, and
   signer-independent committee finality beside the live v3 path;
4. run one full deployment-owned Bazaar → finality → private worker → exact
   Dungeon/Descent consequence journey through web, Telegram, and Discord under
   full Lean and the audited PQ backend;
5. keep the private BFV/HidingFRI pipeline resident long enough for the whole
   operation to win, then publish exact cold/warm counters rather than
   kernel-only speedups; and
6. expand from the first raid/allocation into shuffle, vote, matchmaking,
   netting, and Dark-AMM mechanics without forking the shared game spine.

## 7. The pitch, one breath

**The Dark Bazaar is the economy inside Dregg’s dark: one shared game where
hidden player state can produce a publicly checkable, durably enacted result
without becoming public state. The playable organ is now real. The remaining
summit is to make its entire computation—not merely its proof—blind to every
single operator, and to finalize that fact as ordinary Dregg consensus.**
