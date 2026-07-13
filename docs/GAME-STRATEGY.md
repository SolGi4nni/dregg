# dregg game strategy — one sequenced plan (2026-07-12)

Synthesis of three planners (product director · chief strategist/red-team · platform architect), each grounded in code.
Companion to GAME-FUN-AND-INFRA-PLAN.md (the 3-thinker feedback this sequences).

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
Discord-native); the web catalog = the spectator/provenance surface. Ships on the DEPLOYED executor path ONLY (never the
attested-dm toy blake3 ledger).

## The phases (each: goal · product deliverable · platform deliverable · success bar · the one decision)
### Phase 0 — MAKE IT FUN (days–weeks) [IN FLIGHT]
- Goal: convert the click-through into "I want to play again." · Product: REAL LOSS (a lethal blow -> a terminal DEFEAT
  passage [WriteOnce `downed` -> END] instead of refusing HP-zero at dice_combat.rs); opt-in HARDCORE (death WriteOnce-
  final); FORKING DILEMMAS (risk-it d20-vs-DC + WriteOnce opportunity cost — treasure OR key); CLASS INTO PLAY (wire the
  built-but-unused spells.rs so a Mage run != a Warrior run). · Platform: NONE (the guardrail — resist any schema here).
  · Success bar: a HUMAN replay signal — real (non-team) playtesters retry after dying; a crowd audibly argues over a
  choice. · Decision: does opt-in hardcore permadeath ship? (it's what makes the no-cheat leaderboard mean "I PROVABLY
  survived").
### Phase 1 — THE FLAGSHIP (the hit)
- Goal: one launch-quality, EARNING game with real players. · Product: THE DESCENT — bind a real drand beacon
  (procgen.rs) so today's dungeon is unpredictable-until-revealed; permadeath; meta-progression (wire the proven-but-
  standalone progression.rs to the persistent CellId identity); a public no-cheat leaderboard; the attested LLM narrates
  WITHIN verified rules (AI proposes, world disposes). Monetize via AI-narration credits ONLY. · Platform (flagship as
  customer zero): SESSION KEYS + passkey + paymaster onboarding (a session key = a caveat-bounded play-cap delegation;
  the paymaster = the existing run-credit ledger); a MINIMAL reactive-read/INDEXER (WELD receipt_stream.rs [verified live
  stream] + dregg-query [EDB+CALM+MMR non-omission] into a materialized per-cell view); DURABLE PERSISTENCE (CharacterStore
  /host sessions over redb/pg-dregg — NON-NEGOTIABLE, meta-progression is a lie without it). · Success bar: FIRST REVENUE
  from real players; a D1/D7 retention signal; a stranger can verify a run's receipt. · Decision: accessibility posture —
  ship custodial/session-key/passkey/paymaster so a NON-crypto person pays and plays with zero wallet ceremony? (make-or-
  break for a real player base — the Cartridge lesson).
### Phase 2 — EXTRACT THE KEYSTONE (from the hit)
- Goal: turn the flagship's hand-rolled state into the general schema, validated by one real game then a second. · Product:
  a SECOND game (different genre) built ON the schema, shipping materially faster BECAUSE the schema exists. · Platform:
  THE KEYSTONE — a `dregg-schema` crate between authors and cell/program: 7 typed component archetypes (stat->FieldGte+Lte,
  resource->Monotonic, identity->WriteOnce, timer->temporal, collection->HeapField, invariant->FieldLteOther, counter->
  StrictMonotonic — all present + Lean-twinned) -> a VERIFIED ALLOCATOR via TRANSLATION VALIDATION (untrusted search,
  checked output): a Legality obligation (copied from the LANDED RotatedLayout.lean Legal-discipline — an ill-aligned
  layout is UNCONSTRUCTABLE, a type error) + a refinement obligation (the emitted CellProgram's admitted-turn set <=> the
  declared semantics, on game-turn-slice's rails) -> a layout + a CellProgram::Cases + a typed API. Generalizes compile_
  scene; feeds the ALREADY-BUILT game-turn-slice leaf back-end (schema -> allocator -> CellProgram+proofs -> leaf -> fold ->
  verify_history). · Success bar: the second game reuses the schema unchanged + ships in materially less time; the
  allocator emits a layout+CellProgram+API WITH a refinement proof. · Decision: generalization scope — the full verified
  allocator now, or only the minimal typed-component->layout that TWO games provably need? (guardrail: generalize only
  what 2 games exercised).
### Phase 3 — THE PLATFORM FLYWHEEL (only if 1+2 landed)
- Goal: many authors; a STRANGER ships a dregg game with no team in the loop (the pug bar). · Product: the game-author SDK
  / paved path + docs/guide/; the creator economy (verified authorship + remix lineage [FOUNDATION LANDED] + paid/premium
  + royalties + a marketplace); co-op party-with-roles. · Platform: the SDK/scaffold (schema->deploy->Offering->Frontend->
  indexer client->session-key play); no-cheat tournaments (brackets advance only on verify_completion); a verifiable asset
  layer (an asset is just another component archetype); game-tick/settlement-tick separation for scale. · Success bar: >=1
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
Two-substrate fork -> ship on the DEPLOYED path only. Daily-race cold-start -> the leaderboard must be fun SOLO day one
(beat your own ghost / the global best). Persistence-in-memory-today -> durable persistence is Phase 1 NON-NEGOTIABLE.

## The 5 decisions to LOCK
1. LOSS MODEL (Phase 0): ship real loss (lethal->DEFEAT) AND opt-in hardcore permadeath (WriteOnce-final)?
2. ACCESSIBILITY (Phase 1): ship custodial/session-key + passkey + paymaster so a non-crypto player pays+plays at launch?
3. ATTESTED-DM AT LAUNCH (Phase 1): wire the real attestation crown into the game narrator, or launch fixture-only +
   market solely "cost-metered + world-resolved" (never "un-jailbreakable attested")?
4. KEYSTONE TIMING (sequencing): commit the schema+allocator is built AFTER the flagship earns, EXTRACTED from it,
   generalized only to a 2nd game's needs — i.e. platform-first is OFF the table?
5. TOKEN ROLE: $DREGG buys SERVICES only (AI-narration credits, hosting, cosmetics/entry) — never power/features/yield;
   no P2E until retention is proven?

## The call, one line
Do the cheap fun-fixes now; bet the quarter on ONE turn-based, daily-procgen, attested-DM roguelite ("The Descent") that
EARNS and is playable by normal humans (session keys pulled forward); extract the keystone schema FROM that hit as its
first customer; open the platform flywheel only once a second game + an outside author prove it generalizes. Product-
first, platform-seeded — because for dregg, the fun game and the engine are the same receipt.
