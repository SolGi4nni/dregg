# dregg game strategy — one sequenced plan (2026-07-12)

Synthesis of three planners (product director · chief strategist/red-team · platform architect), each grounded in code.
Companion to GAME-FUN-AND-INFRA-PLAN.md (the 3-thinker feedback this sequences). This is the strategy of record; a
`[BUILT: path]` tag marks a deliverable that is real code at HEAD (each module's docs carry its own honest scope), while
the phase SUCCESS BARS — human replay signals, real players, revenue — are measurements no tag can satisfy and stay open.

## The through-line: EVERY MOVE IS A RECEIPT
A game turn = an attenuated, proof-carrying capability exercised over owned state, leaving a verifiable receipt — the
SAME object whether you're a PLAYER (fair, no-cheat, un-foolable AI DM) or an AUTHOR (an engine to build a game on). The
strategic consequence that dissolves the product-vs-platform tension: **the flagship game and the platform schema are the
same primitive at two altitudes — the flagship is CUSTOMER ZERO of the schema.** Deck line: *"Author your game's state
and rules once; every player's turn becomes a receipt anyone can verify — the fun and the engine are the same primitive."*

## The call: PRODUCT-FIRST, PLATFORM-SEEDED (not platform-first, not throwaway-product)
Re-sort the "infra": some of it is PRODUCT-CRITICAL PLAYABILITY infra (session keys, a reactive-read path, durable
persistence) — without it the flagship is a demo, not a game — so PULL IT FORWARD into the flagship. Defer only the
AUTHOR-SERVING infra (the general schema + allocator, the SDK, the marketplace), whose ROI is proportional to author
count = zero until there's a hit. Do the cheap fun-fixes NOW regardless. Build the platform primitive AT THE MOMENT the
flagship needs it; generalize only what a SECOND game forces.

## The flagship: "THE DESCENT"
A daily, provably-fair roguelite crawl with an attested DM, played as a crowd, in Discord. *Every day one dungeon,
everyone plays the same seed, you can die, the DM physically can't lie about your HP, your character carries scars +
levels between days, at midnight the leaderboard freezes and a new dungeon is revealed.* Hero fantasy: "I survived
today's Descent — and I can prove it." Retention engine = the 24h daily reveal. Discord-first (the crowd-as-party is
Discord-native); the web catalog = the spectator/provenance surface. Ships on the real circuit-proven executor path ONLY (never the
attested-dm toy blake3 ledger).

## The phases (each: goal · product deliverable · platform deliverable · success bar · the one decision)
### Phase 0 — MAKE IT FUN (days–weeks) [product deliverables BUILT; the human bar open]
- Goal: convert the click-through into "I want to play again." · Product: REAL LOSS (a lethal position routes to a
  terminal DEFEAT passage [WriteOnce `downed` -> END] instead of refusing HP-zero) + FORKING DILEMMAS (risk-it d20-vs-DC
  gating a shortcut + WriteOnce opportunity cost — crown OR key) [BUILT: dungeon-on-dregg/src/bloodgate.rs]; opt-in
  HARDCORE (death WriteOnce-final, persists — a re-opened dead character loads dead) [BUILT:
  dreggnet-offerings/src/character.rs]; CLASS INTO PLAY (spells.rs wired class-gated so a Mage run != a Warrior run)
  [BUILT: dreggnet-gear/src/talents.rs]. · Platform: NONE (the guardrail — resist any schema here). · Success bar
  (OPEN): a HUMAN replay signal — real (non-team) playtesters retry after dying; a crowd audibly argues over a choice.
  · Decision: does opt-in hardcore permadeath ship? (it's what makes the no-cheat leaderboard mean "I PROVABLY
  survived").
### Phase 1 — THE FLAGSHIP (the artifact BUILT; the hit open)
- Goal: one launch-quality, EARNING game with real players. · Product: THE DESCENT [BUILT:
  dreggnet-offerings/src/daily_descent.rs, played live via discord-bot/src/commands/descent.rs] — the daily
  drand-beacon-seeded world (verification is a real quicknet pairing check; fetching the day's round is the named
  client seam); permadeath on the bloodgate pattern; meta-progression over the persistent character [BUILT:
  character.rs]; the ugc-dregg no-cheat leaderboard + a weekly bracket [BUILT: descent_tournament.rs]; the attested
  LLM narrates WITHIN verified rules (AI proposes, world disposes) [attestation wiring BUILT:
  deos-hermes/src/narrator_crown.rs + dungeon-on-dregg's narrate_turn_bedrock_attested — decision #3's named frontier
  is the operational remainder, a live pinned-notary session]. Monetize via AI-narration credits ONLY. · Platform
  (flagship as customer zero): SESSION KEYS + paymaster
  onboarding [BUILT: dreggnet-offerings/src/session.rs — a session key = a caveat-bounded play-cap delegation over
  macaroons; the paymaster binds the real dregg-pay CreditLedger (dreggnet-offerings/tests/session_paymaster.rs)]; a MINIMAL
  reactive-read/INDEXER [BUILT: starbridge-web-surface/src/indexer.rs — the weld of receipt_stream.rs (verified live
  stream) + dregg-query (EDB+CALM+MMR non-omission) into a MaterializedView, with reactive query subscriptions, local
  tx simulation, and MMR non-omission attested answers]; DURABLE PERSISTENCE [BUILT for the load-bearing pieces:
  discord-bot/src/character_store.rs (sqlite CharacterStore) + replay-based session resume
  (dreggnet-offerings/src/resume.rs); the remaining in-memory stores are named seams at their trait boundaries].
  · Success bar (OPEN — and the flagship has no durable public deployment): FIRST REVENUE from real players; a D1/D7
  retention signal; a stranger can verify a run's receipt. · Decision: accessibility posture — ship
  custodial/session-key/passkey/paymaster so a NON-crypto person pays and plays with zero wallet ceremony? (make-or-
  break for a real player base — the Cartridge lesson).
### Phase 2 — EXTRACT THE KEYSTONE (keystone BUILT; the second-game bar open)
- Goal: turn the flagship's hand-rolled state into the general schema, validated by one real game then a second. · Product:
  a SECOND game (different genre) built ON the schema, shipping materially faster BECAUSE the schema exists [the games
  are BUILT: dregg-multiway-tug (its state a dregg-schema-allocated layout) + dregg-automatafl (deps dregg-schema, its
  prove/fold path mirrors game-turn-slice) — see GAME-INFRA-ROADMAP "THE PORTFOLIO"; OPEN: the ships-materially-faster
  measurement]. · Platform: THE KEYSTONE
  [BUILT: dregg-schema] — a crate between authors and cell/program: typed component archetypes (stat->FieldGte+Lte,
  resource->Monotonic, identity->WriteOnce, collection->HeapField, invariant->FieldLteOther) -> an allocator via
  TRANSLATION VALIDATION (untrusted search, CHECKED output): the Legality check (the RotatedLayout.lean Legal-discipline
  — an ill-aligned layout is UNCONSTRUCTABLE) + a refinement discipline (a legal move commits, each illegal move is
  refused, driven per archetype on the real executor) -> a layout + a CellProgram::Cases + a typed API. The crate's own
  honest scope names its seam: these are the Rust translation-validation forms; the Lean-PROVEN Legal obligation over
  this allocator and the game-turn-slice leaf refinement (schema -> allocator -> CellProgram+proofs -> leaf -> fold ->
  verify_history) are the named next resolution. · Success bar (OPEN): the second game reuses the schema unchanged +
  ships in materially less time; the allocator emits a layout+CellProgram+API WITH a refinement proof. · Decision:
  generalization scope — the full verified allocator now, or only the minimal typed-component->layout that TWO games
  provably need? (guardrail: generalize only what 2 games exercised).
### Phase 3 — THE PLATFORM FLYWHEEL (only if 1+2 landed)
- Goal: many authors; a STRANGER ships a dregg game with no team in the loop (the pug bar). · Product: the game-author SDK
  / paved path + docs/guide/; the creator economy (verified authorship + remix lineage [FOUNDATION LANDED] + paid/premium
  + royalties + a marketplace); co-op party-with-roles [BUILT: dreggnet-party — per-seat role caps + an on-ledger loot
  split]. · Platform: the SDK/scaffold (schema->deploy->Offering->Frontend->
  indexer client->session-key play); no-cheat tournaments [BUILT: dreggnet-tournament — brackets advance only on a
  verified win: replay via verify_completion, or the succinct Registry::submit_proof path]; a verifiable asset
  layer [BUILT: dreggnet-asset] (an asset is just another component archetype); game-tick/settlement-tick separation for
  scale. · Success bar: >=1
  EXTERNAL author ships a playable, earning game with no team involvement. · Decision: platform GA gated on >=1 external-
  author success; $DREGG buys SERVICES only.

## Build-vs-adopt
ADOPT the patterns (ECS <- MUD/Dojo; the reactive indexer <- Torii; session keys <- Cartridge) — but dregg's substrate is
BETTER: safe moddability via CAP-CONFINEMENT (a mod is a new TransitionCase under an attenuated cap — structurally can't
touch state outside its grant; pure-EVM/Cairo can't offer this); indexer rows carry NON-OMISSION certificates (MMR range
openings — a client can prove the server hid nothing; no Torii offers this); session keys = macaroon attenuation (no new
trust model). BUILD the dregg-unique moat: the VERIFIED ALLOCATOR + refinement proof (nobody else has a verified emit; on
the LANDED RotatedLayout discipline) + the ATTESTED-AI-DM binding (the documented cure for AI Dungeon's memory cliff).

## Red-team guardrails (vs the documented failure modes)
Tokenomics-first (P2E collapse) -> leaderboard reward is GLORY, not yield; $DREGG buys services never power/features/yield.
Tech-demo-not-a-game -> Phase 0 success bar is a HUMAN replay signal, not a proof shipped. Crypto-native accessibility ->
session-keys pulled FORWARD to Phase 1. AI-DM memory cliff/jailbreak -> the DM is ALWAYS world-resolved; the attestation
crown must be WIRED not a fixture, or don't market "un-jailbreakable." Real-time genres -> the flagship is TURN-BASED,
refuse RTS (the substrate fights it). Over-investing in platform -> the keystone is Phase 2, EXTRACTED from the hit.
Two-substrate fork -> ship on the real-executor path only (never the attested-dm toy ledger). Daily-race cold-start ->
the leaderboard must be fun SOLO day one (beat your own ghost / the global best). In-memory persistence -> durable
persistence is NON-NEGOTIABLE (the character store is durable; any remaining in-memory store is a named seam, never a
shipped dependency of meta-progression).

## The 5 decisions to LOCK
1. LOSS MODEL (Phase 0): ship real loss (lethal->DEFEAT) AND opt-in hardcore permadeath (WriteOnce-final)?
2. ACCESSIBILITY (Phase 1): ship custodial/session-key + passkey + paymaster so a non-crypto player pays+plays at launch?
3. ATTESTED-DM AT LAUNCH (Phase 1): wire the real attestation crown into the game narrator, or launch fixture-only +
   market solely "cost-metered + world-resolved" (never "un-jailbreakable attested")?
4. KEYSTONE TIMING (sequencing): commit the schema+allocator is built AFTER the flagship earns, EXTRACTED from it,
   generalized only to a 2nd game's needs — i.e. platform-first is OFF the table?
5. TOKEN ROLE: $DREGG buys SERVICES only (AI-narration credits, hosting, cosmetics/entry) — never power/features/yield;
   no P2E until retention is proven?

## DECISIONS LOCKED (2026-07-12, ember)
1. SEQUENCING: **FULLY PARALLEL** — push the flagship AND the keystone schema hard at the same time (more ambitious than
   product-first-seeded; both tracks run NOW). The through-line still holds (the flagship is customer zero of the schema),
   but we don't wait for the hit to build the keystone.
2. ONBOARDING: **YES, pulled forward** — session-keys + passkey + paymaster onboarding is a flagship deliverable (a
   non-crypto person plays with zero wallet ceremony; a session key = a caveat-bounded play-cap delegation over macaroons).
3. ATTESTED DM: **WIRE THE REAL CROWN FOR LAUNCH** — light the real MPC-TLS/attestation path (deos-hermes/src/attest.rs zk-live)
   so "provably a real model, injection-free, bound to verified state" is true day one, not a fixture. (The operational
   remainder — a live pinned-notary api session — is the named frontier.)
4. TOKEN: **SERVICES-ONLY, NO P2E** — $DREGG buys AI-narration credits / hosting / cosmetics / entry, NEVER power/features/
   yield; no play-to-earn until retention is proven.

## The call, one line
Do the cheap fun-fixes now; bet the quarter on ONE turn-based, daily-procgen, attested-DM roguelite ("The Descent") that
EARNS and is playable by normal humans (session keys pulled forward); extract the keystone schema FROM that hit as its
first customer; open the platform flywheel only once a second game + an outside author prove it generalizes. Product-
first, platform-seeded — because for dregg, the fun game and the engine are the same receipt.
