-- Persistent, LEVELING characters — the durable backing of dreggnet-offerings'
-- `character::CharacterStore`, keyed by a player's stable dregg identity (their derived
-- Ed25519 public-key hex). A leveling character now survives a process restart: the four
-- progression slots (xp / level / class / abilities_used) are the persistable
-- `CharacterSheet`, saved by identity and re-loaded on a returning player's next move.
--
-- The /dungeon flow is a COLLECTIVE crawl on the real dregg executor; a player's character
-- earns XP when the party lands a qualifying outcome (bloodying the gate-warden, seizing the
-- hoard). The XP grant + every level-up flows through the REAL gated character turn
-- (`StrictMonotonic(xp)` / `FieldGte(xp, threshold)`), NOT an app-level integer bump — this
-- table only PERSISTS the resulting sheet by identity.
--
-- FAIL-SAFE: a tampered/absent row can never resurrect a FORGED level. `SqliteCharacterStore`
-- validates a loaded sheet against the real progression curve (`xp >= xp_threshold(level)`,
-- a valid class, `level <= MAX_LEVEL`); an ill-formed row loads as a fresh level-1 character.
--
-- NOTE: `Database::connect` also creates this table inline (CREATE TABLE IF NOT EXISTS),
-- matching the bot's schema-in-code pattern; this file documents the schema for the migrations dir.

CREATE TABLE IF NOT EXISTS characters (
    identity_hex   TEXT PRIMARY KEY,            -- the player's derived dregg public-key hex (DreggIdentity)
    xp             INTEGER NOT NULL DEFAULT 0,  -- earned XP (the monotone slot the level-up gate reads)
    level          INTEGER NOT NULL DEFAULT 0,  -- character level (advanced only through XP-gated turns)
    class          INTEGER NOT NULL DEFAULT 0,  -- 0 = unclassed, else 1 warrior / 2 mage / 3 rogue (WriteOnce)
    abilities_used INTEGER NOT NULL DEFAULT 0,  -- the class-ability counter
    updated_at     INTEGER NOT NULL DEFAULT 0   -- unix seconds of the last save (bookkeeping)
);
