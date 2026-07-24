# DESIGN FRONTIER CENSUS — 2026-07-16

*A whole-system step-back. Ranks the highest-leverage NEXT architectural moves
across the forward-vision set and the excellence backlog, then turns the top
three into ready-to-drive design briefs. Present-tense for what EXISTS (with
file:line anchors verified at HEAD); explicit "proposed"/"would" for the design.
Every leverage×readiness call is argued, not asserted.*

**Scope note — three tracks are being designed IN PARALLEL and are excluded
here:** the verified layout-optimizer (`docs/DESIGN-verified-layout-optimizer.md`),
the rung-1 launchpad (`docs/deos/DREGG-LAUNCHPAD-DESIGN.md` + the EVM value
contracts), and partial-turn/guarded-holes (`docs/deos/PARTIAL-TURN-LIFT.md`).
This census maps the REST of the frontier and does not restate those three.

**The reading of the moment (from `REORIENT.md` CURRENT-2026-07-09 +
`docs/EXCELLENCE-BACKLOG-2026-07-16.md` + the launch-readiness memory):** the
verified artifact is real and deep, but it is *staged on ember's laptop*. The
one disease has four faces — nothing is a reproducible build, nothing (VK /
protocol) is frozen, nothing value-bearing is deployed, and there are exploitable
value holes at the chain edges. The highest-leverage moves are therefore the ones
that move the system *off the laptop and into a frozen, deployable shape* — not
the ones that add another cathedral. That bias is baked into the ranking below.

---

## PART A — The ranked frontier

Each item: **what it is · what EXISTS toward it (anchored) · leverage × readiness
· the ONE hard part.** Ranked by `leverage × readiness`, launch-critical first.

### Tier 1 — buildable now, launch-critical (drive these)

#### 1. VK-custody content-hashing (the freeze-protocol prerequisite)
**What.** Before any freeze ceremony pins a recursion VK, every component that
feeds the VK hash must be *content-derived*, so a change to the verifier can
never ship under an unchanged VK. **Exists:** `compute_recursive_vk_hash()`
folds four components (`circuit-prove/src/recursive_witness_bundle.rs:146`), but
only the AIR descriptor fingerprint is content-derived (`:137`). `RECURSION_P3_REV`
is a **hand-mirrored string** (`:111`, whose own doc-comment admits "bumping the
rev without bumping this string would silently let old recursive proofs verify
against new code"); `recursive_verifier_source_hash()` hashes a **fixed literal**
`b"dregg-recursive-witness-bundle-verifier-v1"` (`:124`, doc: "In a fuller VK v2
rollout this would be the git-blob-hash of this source file"); and
`RECURSIVE_VK_PROGRAM_BYTES` is a constant label (`:103`). **Leverage: HIGH**
(this IS the "nothing frozen" disease — a freeze that pins mirror-strings freezes
a lie). **Readiness: HIGH** (a self-contained crate, buildable today, no VK
epoch needed — the *point* is to arm it before the epoch). → **BRIEF 1.**
**Hard part:** deriving the verifier fingerprint without a build-time git hook —
either a `build.rs` that git-blob-hashes the source set, or an
`include_str!`-and-hash of a pinned module list, each with its own drift surface.

#### 2. Hybrid-identity binding + federation-id derivation unification
**What.** The consensus wire now signs hybrid ed25519∧ML-DSA-65 (`REORIENT.md`
CURRENT-07-09), and genesis mints the federation id from the **hybrid** roster
(`node/src/genesis.rs` GenesisConfig doc "COUPLED-CORE… `hybrid_id_commitment`
per validator"; `derive_federation_id_hybrid_with_epoch`,
`federation/src/identity.rs:65`). But the **add-validator reroll recomputes the id
ed25519-only**: `node/src/operator_join.rs:177` calls
`derive_federation_id_with_epoch` (ed-only), and `federation/src/federation.rs:290`
does the same on the committee-epoch recompute — while `:182` uses the hybrid
form. So the federation id **forks the instant membership changes**: genesis and
one recompute path speak hybrid, the reroll path speaks ed-only, and the identity
doc itself warns "Genesis and the runtime… MUST agree… or a receipt's carried
`federation_id` will not match and it fails closed" (`identity.rs:55`). The redteam
migrated the impersonation attacks onto this hybrid id (recent commit
`ef65fa9f5`), so a divergent derivation undermines exactly the property the PQ
work exists to provide. **Leverage: HIGH** (VK-epoch-shaped; the bigger question
— whether `Id = H(ed‖ml)` becomes a tree-wide `dregg-types` change vs out-of-band
enrollment — must be *decided before re-genesis*, because re-basing identity after
community state exists is rug-shaped). **Readiness: HIGH** for the fork fix; the
tree-wide decision is a design call. → **BRIEF 2.** **Hard part:** the reroll and
epoch-recompute paths don't currently *carry* the ML-DSA roster to the derivation
site — threading it there is the real work, and the fallback-to-ed-only branch
(`member_ids_hybrid`, `identity.rs:82`) must not silently absorb a
roster-plumbing bug.

#### 3. zkOracle cross-leg binding (DECO money-in soundness)
**What.** `zkOracle_sound` (`metatheory/Dregg2/Crypto/ZkOracle.lean:76`) composes
three conjuncts — the DECO attestation is authentic, the JSON body is well-formed,
the user field is injection-free — but it quantifies over `decoStmt`/`decoPf`,
`body`/`cfgPf`, and `field` as **three independent objects with no connecting
hypothesis** (`:83-89`). The three conjuncts can therefore be about *different
requests*: a genuine attested TLS session, an unrelated well-formed body, and a
third safe field, all "verified" together while describing nothing coherent. The
binding is *absent*, not "an explicit hypothesis." **Leverage: HIGH** — this is
the soundness core of DECO/zkTLS money-in (the 8th fold carrier, the Stripe
fiat-in crown), i.e. the trust root under DreggFi's fiat edge. **Readiness:
MED-HIGH** — the fix is a Lean statement change plus threading a shared witness in
the deployed circuit; no VK epoch, no re-genesis. → **BRIEF 3.** **Hard part:**
naming the *right* shared commitment — DECO's `encode`/`compress` output must be
shown equal to the CFG input's Poseidon2 commitment — and then making the deployed
prover actually publish that shared value as a bound PI, not just asserting the
equality in the model.

#### 4. Reproducible-build fail-closed (P0)
**What.** Fresh clones must build the SAME verified binary. **Exists:**
`scripts/fetch-lean-seed.sh` fetches a prebuilt `libdregg_lean.a`, but when the
`.sha256` sidecar is missing it prints "installing UNVERIFIED" and **installs
anyway** (`:148`-area, the `WARNING: no .sha256 sidecar found` branch). The
`lean-seed.pin` `TAG` has historically been empty (no seed ever cut;
`REORIENT.md` 07-06). **Leverage: HIGH** (a launch-readiness P0 face). **Readiness:
HIGH** for the fail-closed edit (make missing-sidecar an error, not a warning);
the actual *seed cut* is a ceremony on the Lean host, not a design task. Small,
sharp, do-it-now — folded into BRIEF 1's "arm the ratchet now" spirit but a
separate one-line change.

### Tier 2 — high leverage, medium readiness (queue behind Tier 1)

#### 5. Solana bridge value-holes — CLOSED (verify, do not re-open)
The three P1 value-holes the launch audit named are **closed at HEAD** — this
item is a correction, not a lane. `rotate()` now tallies through the
authorized-voter binding `VerifiedStakeTable::tally_authorized` (not the old
`verify_supermajority`; its doc marks the prior use "red-team BR value-hole
HOLE-3, now closed", `solana_provenance.rs:811,831`); `derive_stake_table`
enforces a completeness floor cross-checking supplied stake against the proven
`StakeHistory` sysvar and rejecting a shortfall with
`ProvenanceError::StakeBelowHistoryFloor` (`:530-548`, HOLE-2); and value
release requires the slot proven **rooted** via `tally_authorized_rooted`, with
the exact-slot super-majority explicitly labeled optimistic-confirmation grade
(`solana_trustless.rs:81-104`, HOLE-1). **The stale "3 exploitable holes"
framing in the excellence backlog + launch-readiness memory is superseded by
commit `72561117d`.** Standing lane, if any: a red-team pass that tries to
*re-open* these under the new gates (verify the closures bite), not new fixes.

#### 6. cap-graph GENUINE-NON-AMP descriptor (Lean emit fix)
The non-amp leg doesn't bind the hashed rights felt and its state_commit group-4
chain is misindexed; the tests **pin the wrong behavior** awaiting a Lean emit fix
(`cap_delegation_nonamp_descriptor.rs:411,508`). Latent (unwired) today — but
wired, a prover could confer ANY rights. **Leverage: MED-HIGH** (a soundness
floor of the whole cap model). **Readiness: HIGH** — land the emit fix in
`EffectVmEmitCapReshape.lean`/`EffectVmEmitAttenuateA.lean` and the two red pins
*become* the green. **Hard part:** it needs Lean build cycles and is held for a
careful single driver (backlog "Held for… ember").

#### 7. Game-fold state-binding — "every move is a receipt about THIS cell"
The 2026-07-16 state-binding flip made the deployed chain prover REQUIRE the
in-circuit custom-proof state weld (`HORIZONLOG.md` 07-16), but the flip's STILL
OWED #2 is stark: **the games' custom sub-proofs are not about the cell's roots.**
`dregg-multiway-tug/src/fold.rs`'s PIs are game values (`[card_leaf, root]`), fixed
at lowering time in `game-turn-slice/src/compiler.rs::lower_witnessed_merkle_membership`
before any leg exists — so the two-phase probe that fixed `mpt_holding` does not
lift; the cell roots must be threaded down to the lowering layer. **Leverage:
MED-HIGH** (this is the literal truth of the game thesis). **Readiness: MED** —
and it overlaps the Custom-VK cluster "another terminal is actively driving"
(backlog "Held"), so coordinate before firing. **Hard part:** the roots-at-lowering
design question, reached from product code (`dreggnet-game-board::prove_match`,
the wasm `fold_tug_match_core`).

#### 8. Payments-go-live (Discord/Solana)
Both `PayState` constructors unconditionally build `MockWatcher`
(`discord-bot/src/pay.rs:445`); real on-chain $DREGG/USDC deposits credit no one,
and the bot process loads `DREGG_PAY_SEED` (custodian, not watch-only). **Leverage:
HIGH** for the token economy, **readiness: MED** — construct `SolanaWatcher` from
env, split seed custody into a sweeper, put `MockWatcher` behind a devnet flag.
**Hard part:** the custody split is an ops/security boundary, not just code.

### Tier 3 — the big cutover and the ratchets

#### 9. THE VK-EPOCH FLIP — staged wide/carrier path → deployed default
The buff light client + all 8 fold carriers + the faithful ~124-bit whole-turn
commitment are BUILT, committed, `#assert_axioms`-clean, tooth-gated through real
recursion — but they sit in the **staged wide path**; the deployed default is
still 1-felt for some surfaces and the live federation runs the old chain
(`REORIENT.md` CURRENT-07-05/07-06). **Leverage: HIGHEST** (it is the thing every
Tier-1 item is *preparing*). **Readiness: LOW** — it is an ember-gated ceremony
(fresh `federation_id`, re-point every pin, N3 committee-restart fix first), and
it *depends on* Briefs 1+2 landing first. This is not a design task; it is the
payoff the design tasks unlock. Named here so the ranking is honest about where
the arrow points.

#### 10. The missing-gates ratchet bundle
A docs/code ref-integrity linter (the dominant doc-drift class), plonky3-rev
single-source, gitleaks-in-CI, the S2 `--ignored` deployed-teeth gauntlet, the
`dregg_mcp` effects-catalog exhaustiveness test. **Leverage: MED** (each kills a
whole finding class), **readiness: HIGH** (mostly CHEAP), **arm now while the
corpus is clean** so each ratchets from green. Not a single architectural move but
a standing hygiene layer; drive opportunistically.

### Tier 4 — vision, not buildable-now (name honestly, do not staff yet)

- **FHEGG confidential-finance engine** (`docs/deos/FHEGG-KERNEL.md`,
  `FHEGG-FPGA-ACCELERATOR.md`, four codex rounds). VERY HIGH vision leverage
  (private compute over dregg state); **readiness: LOW** (research frontier — the
  math briefs and codex insight rounds are the current altitude, not a first
  slice). Keep as a codex-driven research lane, not a build brief.
- **DREX / DreggFi exchange** (`docs/deos/DREX-DESIGN.md`, `DREX-ROUTING.md`,
  `DREGGFI-VISION.md`). HIGH vision leverage; **readiness: LOW-MED** — gated on
  the money-in soundness (Brief 3) and the value-hole closures (item 5) being real
  first. Design-rich, build-blocked.
- **Verified light-client universal fold → interchain default**
  (`docs/deos/VERIFIED-LIGHTCLIENT-FOLD-PATH.md`, and the freshest doc in the tree,
  `INTERCHAIN-LIVE-CAMPAIGN.md`, touched 16:00 today). HIGH leverage,
  **readiness: LOW-MED**, and **likely already being driven** (the freshness of
  the campaign doc suggests a live terminal) — census, do not duplicate.
- **ADOS / firmament-desktop / unifying-story productization**
  (`docs/design-frontiers/{ADOS,AGENT-SWARM-UX,UNIFYING-STORY,WEB-FORWARD}.md`,
  `PG-DREGG-DX.md`). HIGH product-vision leverage; **readiness: LOW-MED** — these
  are freshly written design frontiers (today), i.e. the *design* is the current
  deliverable; the build slices they name (the swarm cockpit on
  `starbridge-v2/src/swarm.rs`, pg-dregg Tier-D atomic co-commit) are real but
  large. Downstream of the substrate freeze.
- **GPU prover → prod wiring** (`docs/deos/GPU-PROVER-WIRING-PLAN.md`). The 25×
  mont-mul crack landed (memory: codex-exec, 07-15); MED leverage, MED-HIGH
  readiness for the wiring, but it is a perf lane, not an architectural frontier.

---

## PART B — Three ready-to-drive design briefs

### BRIEF 1 — Content-hash all four recursive-VK components

**The wound.** A freeze ceremony's whole value is that a pinned VK *forces* the
verifier to be the one that was audited. Today three of the four components folded
into `compute_recursive_vk_hash()` are **decorative labels**, so a real change to
the recursion verifier can ship under an unchanged VK hash — the exact custody
property the pin exists to provide, inverted. Arming this BEFORE the freeze is the
difference between freezing the system and freezing a promise.

**The real modules.**
- `circuit-prove/src/recursive_witness_bundle.rs` — `RECURSION_P3_REV` (`:111`,
  hand-mirrored string), `recursive_verifier_source_hash()` (`:123`, hashes a
  fixed literal), `RECURSIVE_VK_PROGRAM_BYTES` (`:103`, constant label),
  `compute_recursive_vk_hash()` (`:135`, the fold — only `air_fp` at `:137` is
  content-derived), and the existing tests `recursive_vk_hash_is_deterministic_and_nontrivial`
  (`:555`) + `unknown_recursive_vk_hash_rejected` (`:527`).
- `scripts/check-p3-rev.sh` (the current WARN-only rev checker the backlog cites)
  and the `wasm/Cargo.toml:252` rev instruction that already disagrees with the CI
  pin (the drift the backlog "RECURSION_P3_REV drift" item recorded).
- Whatever `dregg_cell::vk_v2::canonical_vk_v2` is (the encoding this function
  mirrors inline, `:130`) — the fix must keep byte-identity with it or state why
  it diverges.

**The first slice (proposed).**
1. **Rev from the locked manifest, not a string.** Replace the `RECURSION_P3_REV`
   literal with a value *read from `Cargo.lock`* at build time (a `build.rs` that
   extracts the `p3-recursion` locked rev and emits it as a `const`), so a rev
   bump that isn't reflected is impossible — the source of truth is the thing
   cargo actually built against. Fail the build if the fork source is a local
   `[patch]` with no resolvable rev (the p3-recursion fork-seam is real).
2. **Verifier fingerprint = git-blob-hash of a pinned source set.** Replace the
   fixed-literal hash with a `build.rs` that hashes the exact list of files
   constituting the recursion verifier surface (an explicit manifest, not a glob),
   so editing any of them moves the VK. If a build-time git hook is undesirable in
   the hermetic build, fall back to `include_str!`-and-hash of the same pinned
   list (content, not path).
3. **Program bytes = the real program.** Bind `RECURSIVE_VK_PROGRAM_BYTES` to the
   actual serialized recursion program if one exists, else document precisely why
   the label is sufficient (it may be — but state the argument, don't leave a bare
   constant next to three fixed ones).

**The verification story (the tooth).** A *mutation canary*: a test that takes the
verifier source manifest, flips one byte in one listed file (or simulates the rev
string changing), recomputes the hash, and asserts it **differs** from the pinned
value — and symmetrically that an unrelated file's change does NOT move it (the
manifest is neither too small nor a whole-tree hash). This is the
`minted-proof-integrity-discipline` mutation-canary applied to VK custody: the pin
only counts if it *reds* when the verifier it guards changes. Pair with the P0
fail-closed edit in `fetch-lean-seed.sh` (item 4) so the reproducible-build and
frozen-VK faces of the disease are closed together.

**Vision vs buildable-now:** fully buildable now. No VK epoch, no re-genesis — the
whole point is to arm the ratchet while nothing is frozen yet, so the ceremony
pins content-hashes from day one.

---

### BRIEF 2 — Unify federation-id derivation on the hybrid identity

**The wound.** Genesis commits the federation id to the hybrid (ed∧ML-DSA) roster;
the add-validator reroll recomputes it ed25519-only. The id therefore forks on the
first membership change, and every receipt carrying the old-derivation id fails
closed against the new one — silently splitting a live federation. The redteam
just migrated its impersonation attacks onto the hybrid id, so an ed-only reroll
is a hole under the exact property the PQ work built.

**The real modules.**
- `federation/src/identity.rs` — `derive_federation_id_hybrid_with_epoch` (`:65`),
  `derive_federation_id_with_epoch` (ed-only, `:43`), `member_ids_hybrid` (`:82`,
  the shared per-member id rule with the empty-roster fallback), and the
  impersonation test (`:135`).
- The divergent call sites: `node/src/operator_join.rs:177` (the reroll — ed-only),
  `federation/src/federation.rs:290` (committee-epoch recompute — ed-only) vs
  `:182` (hybrid) and `node/src/genesis.rs` GenesisConfig (hybrid).
- `dregg_types::hybrid_id_commitment` (the `H(ed‖ml)` primitive both forms wrap).
- `federation/src/receipt.rs:350` (receipt-side re-derivation — already hybrid;
  this is the consumer that fails closed on a mismatch).

**The first slice (proposed).**
1. **Route the reroll through the hybrid derivation.** Thread the ML-DSA roster to
   `operator_join.rs:177` and `federation.rs:290` and call
   `derive_federation_id_hybrid_with_epoch`. The `member_ids_hybrid` fallback
   (empty/mismatched roster → ed-only) must be *reachable only* for genuinely
   PQ-less committees, never as a silent absorption of a roster-plumbing bug — so
   the reroll path should assert roster-present when genesis was hybrid.
2. **One conformance test over the SAME roster.** `genesis_id == rerolled_id` when
   the reroll adds-then-removes back to the genesis committee: the id must return
   to the genesis value. And an add-validator reroll's id must equal a *fresh
   genesis over the new roster* — the two derivations of the same membership agree.
3. **Surface the tree-wide decision for ember (do NOT decide it in the lane).**
   Whether `Id = H(ed‖ml)` becomes the canonical `dregg-types` identity everywhere
   (vs out-of-band ML-DSA enrollment) is VK-epoch-shaped and must be settled
   *before* re-genesis. The lane closes the derivation fork; it writes the decision
   up as a HORIZONLOG item with the two options costed, and stops.

**The verification story (the tooth).** Extend the existing impersonation test
(`identity.rs:135`) into a *reroll* attack: an attacker who substitutes a
validator's ML-DSA key must produce a *different* federation id through the reroll
path (today it produces the *same* id, because the reroll ignores ML-DSA — that is
the bug, and the test reds until the fix). Plus the round-trip conformance (add +
remove returns to genesis id). Both must red before the fix and green after.

**Vision vs buildable-now:** the derivation-fork fix is buildable now (Rust, no
epoch). The tree-wide identity re-base is a decision, explicitly deferred to ember
and sequenced before re-genesis — the lane's job is to make that decision *cheap
and safe to take*, not to take it.

---

### BRIEF 3 — Bind the three zkOracle legs to one request

**The wound.** `zkOracle_sound` proves "authentic ∧ well-formed ∧ injection-free"
over three *independent* objects. Nothing forces the attested TLS session, the
JSON body the CFG proof accepts, and the injection-free user field to be the
**same request**. A verifier can therefore assemble a green proof from a genuine
attestation of request A, a well-formed body from request B, and a safe field from
request C — the composition is vacuous exactly where DreggFi's fiat money-in trusts
it most.

**The real modules.**
- `metatheory/Dregg2/Crypto/ZkOracle.lean` — `zkOracle_sound` (`:76`, the three
  unbound quantifiers at `:83-89`), which reduces to
  `DecoUnforgeable.deco_attestation_realizes` (leg 1) and `Cfg.cfg_verify_sound`
  (leg 2). The DECO carrier exposes `KD.encode`/`KD.compress` (the disclosed
  facts); the CFG carrier consumes `⟨jsonGrammar, body⟩`.
- The deployed circuit side: the DECO/zkTLS + CFG-hypergraph prover
  (`docs/deos/ZKORACLE-CFG-HYPERGRAPH.md`, `ZKORACLE-PROVER-STATUS.md`,
  `ZKORACLE-ENDPOINTS.md`) — where the shared commitment must be *published as a
  bound public input*, not merely asserted in Lean.
- `docs/deos/DECO-CARRIER-PLAN.md` / `DECO-PROVER-STATUS.md` for the encode/compress
  ABI the shared witness rides.

**The first slice (proposed).**
1. **Add the binding hypothesis in Lean.** Introduce a shared commitment
   `c : Dg` and hypotheses tying all three legs to it: the DECO statement's
   disclosed-facts commitment `KD.compress (KD.encode decoStmt) = c`, the CFG
   input's Poseidon2 commitment over `body` `= c`, and the user `field`'s
   commitment `= c` (or `field` is a projection of `body`, whichever the real ABI
   supports). `zkOracle_sound` then concludes about *one* request. This is a
   statement change; the proof body threads `c` through the existing `refine`.
2. **Publish `c` as a bound PI in the deployed circuit.** The DECO leg and the CFG
   leg must each expose their commitment to the *same* `c` in their public inputs,
   and the composed verifier must check equality — mirroring how the custom
   state-binding flip (07-16) made the fold enforce in-circuit precisely what the
   executor enforces off-AIR.
3. **Reject the mismatch.** A negative pole: a proof assembled from a DECO
   attestation of one session and a CFG proof of a *different* body must be
   refused *by the binding check*, with the refusal reason asserted (not a bare
   `Err`, per the 07-16 "vacuous negative pole" lesson).

**The verification story (the tooth).** Two poles through the real composed
verifier: (a) honest — one request, all three commitments equal, accepts; (b)
cross-request forgery — a genuine attestation of request A spliced with a
well-formed body of request B, refused *because `c_A ≠ c_B`*, with
`assert`-on-reason so the tooth can't pass vacuously if a width/shape check fires
first. In Lean, a non-vacuity check: the binding hypotheses must be *load-bearing*
(delete one and the theorem no longer proves) — the `minted-proof-integrity`
structural test.

**Vision vs buildable-now:** the Lean binding is buildable now (a statement +
proof-threading change, `#assert_axioms`-checkable). The deployed-circuit PI
binding is real engineering but no VK epoch is forced *if* the shared commitment
can ride existing PI slots; if it needs a new PI, it batches into the next epoch.
State which as the first measurement in the lane.

---

## Cross-links (verified to exist at HEAD)

- `docs/EXCELLENCE-BACKLOG-2026-07-16.md` — the open-lane source (#8 fed-id, #10
  zkOracle, #11-VK custody, #4 bridge, #9 cap-graph, #2 payments).
- `REORIENT.md` CURRENT-2026-07-09 (hybrid identity, stark-kill) + CURRENT-07-05/06
  (the staged wide/carrier path, the VK-epoch flip package).
- `HORIZONLOG.md` 2026-07-16 (the state-binding flip; STILL OWED #1/#2/#3 —
  Lean can't see the tooth, the games aren't about the cell, vacuous negatives).
- `docs/design-frontiers/{ADOS,AGENT-SWARM-UX,PG-DREGG-DX,UNIFYING-STORY,WEB-FORWARD}.md`
  — the DX/UX vision frontier (Tier 4, downstream of the freeze).
- `docs/deos/{FHEGG-KERNEL,DREX-DESIGN,VERIFIED-LIGHTCLIENT-FOLD-PATH,ZKORACLE-CFG-HYPERGRAPH,DECO-CARRIER-PLAN}.md`
  — the research/vision frontier and the zkOracle grounding.

## The honest bottom line

The three excluded tracks build *new capability*. This census finds that the
highest-leverage moves NOT among them are the opposite in character: **they make
what already exists trustworthy enough to freeze and ship.** Briefs 1 and 2 close
the two custody forks (VK, identity) that a freeze/re-genesis would otherwise
cement into a lie; Brief 3 closes the soundness gap under the money-in edge that
DreggFi is built on. None needs a VK epoch or re-genesis to land — each *removes a
reason* the eventual epoch would be unsafe. The cathedral frontiers (FHEGG, DREX,
the ADOS desktop, the universal interchain fold) are real and named, but they are
downstream of a frozen, reproducible, hole-free substrate — and staffing them
before the substrate is frozen is another way to stay green on ember's laptop.
