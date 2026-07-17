# The dregg game / roleplay / MUD stack — map (2026-07-12)

From a 4-explorer read-only census. The headline: **the substrate is unusually complete; the gaps are BINDINGS +
a few features, not reinvention.** Two verifiable-game substrates exist and are converging. (Status tags mark where a
census-era gap is code at HEAD; docs/GAME-INFRA-ROADMAP.md carries the wider built-crate map.)

## Two substrates
- **attested-dm/** (Path B) — the RICHEST rules engine + `.dungeon` DSL (rooms/exits/objectives/items/combat/hostile/
  NPC/topic/spell/consumable/status/weapon — first-class DIALOGUE: `Npc`/`GameAction::Talk`/`DialogueRule`; SAVE/LOAD +
  an OVERWORLD of regions with travel gated on verified completion) + UN-JAILBREAKABLE attested narration. BUT on a
  local BLAKE3 toy ledger + fixture attestation. dungeon-on-dregg calls it "the LARP being replaced."
- **spween → dungeon-on-dregg → DungeonOffering → /dungeon** (Path A, the real circuit-proven executor). The universes
  + the proven richer-mechanics modules (combat/dice_combat/skills/spells/progression/dialogue/mud/multicell/
  collective/bloodgate). `narrator.rs` bridges attested-dm's narration attestation onto the real `TurnReceipt`.

## The four layers — what EXISTS (build on these)
- RULES: attested-dm::game (dialogue, combat, spells, loot-with-verifiable-randomness) + dungeon-on-dregg's executor
  mechanics. Dialogue is a first-class typed mechanic on BOTH paths (attested-dm's `DialogueRule`; dungeon-on-dregg's
  dialogue.rs — disposition as real gated cell state, the slice dreggnet-faction generalizes).
- AI: the metered/budgeted Narrator (Bedrock->Nova->gemma->scripted, a hard USD BudgetLedger, per-run $0.05 cap, credit
  gate); the sealed BYO-key layer; the cap-gated confined Hermes brain (receipted). Game narrator is TRUSTED but SAFE
  (the executor resolves, the AI has no authority). The attestation CROWN is WIRED to the game narrator [BUILT:
  deos-hermes/src/narrator_crown.rs — AttestedNarrator over dregg_narrator::Narrator; the injection-free leg proven
  in-circuit, fail-closed; the attestation commitment bound into the turn receipt]. The authentic-provenance leg
  defaults to a self-signed fixture, with the real MPC-TLS path feature-gated (zk-live/tlsn-live) — a provenance
  caveat, not an unwired crown. `Narrator::converse` supports TOOL-CALLING (unused) — the hook for the toolConfig
  route.
- WORLD/SOCIAL: progression.rs (a real gated character sheet — XP/level/class/abilities) is WIRED to the persistent
  per-player identity [BUILT: dreggnet-offerings/src/character.rs — a returning player's sheet loads on open and persists on
  save, keyed by the stable DreggIdentity; durable backing = discord-bot/src/character_store.rs, sqlite]. mud.rs +
  node/src/shared_world.rs (multi-player live receipt-stream sync); collective.rs (the signed party ballot); multicell.rs
  (cross-cell world gating). The one-shot-vs-persistent CRUX resolves as: each run's CELL is deployed fresh +
  identically seeded (identity gives the deterministic cell identity), while the CHARACTER STATE carries across runs
  (the loaded sheet seeds the cell; XP earned from real admitted turns only).
- CONTENT: the spween DSL (Twine/Ink-class: passages/choices/conditions/effects) -> compiler -> real executor teeth;
  procgen-dregg (provably-fair, seed-committed, 6 biomes); ugc-dregg (PUBLISH universe + SUBMIT completion, no-cheat
  leaderboard, content-addressed); the /gallery (durable, re-verifies every row on boot). Monetization = the AI-narrated
  /dungeon (credits gate AI narration). Creator-economy FOUNDATION is built [ugc-dregg: verified author identity —
  ed25519 attestation bound into the UniverseId, a publish claiming another author's key without a valid signature is
  refused — and remix/fork lineage as a content-addressed parent edge, publish_derived refusing an unpublished parent];
  paid/premium universes, royalties, and anti-sybil stay named-not-built. DSL ceiling: no dialogue trees, no arithmetic,
  no in-DSL randomness (var-op-var IS expressible: the `$`-sigil string RHS — `{ gold >= "$price" }` — is the
  cross-variable gate `gold >= price`, lowered to the cross-slot FieldLteOther / HeapFieldLteOther tooth in
  spween-dregg/src/compiler.rs; the native identifier-RHS grammar form is the noted parser follow-up in
  emberian/spween); combat/spells live in Rust, not authorable.

## The census-era gap list — status at HEAD
1. CROSS-RUN CHARACTER PERSISTENCE — [BUILT: dreggnet-offerings/src/character.rs + discord-bot/src/character_store.rs].
   Characters carry + level across runs; XP moves only through the sanctioned gated method (a forged grant is a real
   executor refusal); a hardcore death is WriteOnce-final and loads dead.
2. THE OVERWORLD / persistent MUD — [BUILT: dreggnet-offerings/src/overworld.rs re-homes attested-dm's proven overworld
   design onto the real executor: a RegionMap on a real region cell, travel refused unless the prerequisite clear is
   committed]. The world opens as you honestly clear dungeons. The persistent shared hub is [BUILT: dreggnet-tavern —
   an LFG board + per-patron market stalls, live co-inhabitance between runs on the node's one ledger, re-homing
   node/src/shared_world.rs]. Open: the content-rich town hub (dialogue NPCs — see the roadmap's world #4).
3. NPCs/DIALOGUE ON THE REAL-EXECUTOR PATH — the CellProgram port is built (dungeon-on-dregg/src/dialogue.rs). Open: exposing
   dialogue in the spween DSL (var-op-var itself is expressible today — the `$`-sigil RHS lowers to FieldLteOther /
   HeapFieldLteOther in spween-dregg/src/compiler.rs).
4. ATTESTED AI-DM — the crown-to-game-narrator wiring is [BUILT: deos-hermes/src/narrator_crown.rs — in-game AI
   narration is attested, the injection-free leg proven in-circuit, the commitment bound into the turn receipt], and an
   AI-DM that ACTS is [BUILT: dungeon-on-dregg/src/narrator.rs — BedrockBrain proposes typed Commands through a closed
   confined channel (parse_confined_response admits only the room's finite legal keywords), narration attested via
   narrate_turn_bedrock_attested]. Open: the live pinned-notary operational leg (the default authentic-provenance leg
   is a self-signed fixture) + the toolConfig tool-calling route in converse.
5. CREATOR ECONOMY — foundation [BUILT: ugc-dregg verified authorship + remix/fork lineage, above]. Open: paid/premium
   universes, royalties over the $DREGG rails, anti-sybil, a universe marketplace.
6. DSL EXPRESSIVENESS — [open] dialogue trees, the native identifier-RHS var-op-var grammar form (the `$`-sigil form is
   built, above), expose the Rust mechanics in the author language.

## The HeapAtom AIR (landed)
DeltaEquals + HeapFieldLteOther at caveat PARITY: VK-safe (PI-manifest tags 20/21 —
`SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED` / `SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER` in circuit/src/effect_vm/pi.rs, NOT AIR
polynomials), off the hot carrier-geometry; the cross-key fits the existing 7-felt RotCaveatEntry via the §5b
`RotCaveatEntry.relCaveat?` bridge (metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean; parity test
circuit/tests/heap_caveat_tag_parity.rs). `tagHeapAtom` decodes tag 8 (FIELD_DELTA, EXACT re-eval) to `deltaEquals`
(`heapAdmits_deltaEquals_iff`) and tag 20 to `deltaBounded`. Both remain host-evaluated (the named
HeapCaveatRuntimeDischarge premise) — parity with the existing heap surface, not the register-slot live re-eval (which
structurally can't read a heap key).
