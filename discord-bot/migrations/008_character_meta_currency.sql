-- Character META-CURRENCY — the durable backing of the roguelite retention loop's two persistent
-- slots on dreggnet-offerings' `CharacterSheet`: `echoes` (the meta-currency) and `boon` (the
-- persistent unlock). Before this migration the bot's sqlite store persisted xp / level / class /
-- abilities_used / dead but DEFAULTED echoes / boon on load, so a returning player's accrued
-- currency + claimed unlock silently reset on restart. They are now their own columns and survive.
--
-- `echoes` — the META-CURRENCY. Globally `Monotonic` on the hero cell (it only ACCRUES, never spent
--   down); a grant is `StrictMonotonic(echoes)` + `FieldEquals(dead, 1)`, earned ONLY on a real
--   hardcore death, tied to the depth reached (a deeper death banks more). See dungeon_on_dregg::meta.
-- `boon`   — the persistent UNLOCK. Globally `WriteOnce`; a claim is `FieldGte(echoes, BOON_PRICE)`
--   + `WriteOnce(boon)`, bought only with enough accrued echoes. A next run STARTS holding it —
--   this is what makes death ADVANCE you. Lands at the single marker value `BOON_VALUE`.
--
-- FAIL-SAFE: as with the rest of the sheet, a tampered row can never resurrect a FORGED unlock.
-- `SqliteCharacterStore::load` validates the loaded sheet: `boon` is `0` or `BOON_VALUE`, and a
-- claimed boon REQUIRES `echoes >= BOON_PRICE` (echoes is monotone, so the currency that bought the
-- unlock is un-forgeably still present). An ill-formed row loads as a fresh level-1 character.
--
-- NOTE: `Database::connect` also adds these columns inline (CREATE TABLE with the columns, plus a
-- best-effort `ALTER TABLE ... ADD COLUMN` for a pre-existing DB), matching the bot's schema-in-code
-- pattern; this file documents the schema for the migrations dir.

ALTER TABLE characters ADD COLUMN echoes INTEGER NOT NULL DEFAULT 0;  -- the accrued meta-currency (Monotonic)
ALTER TABLE characters ADD COLUMN boon   INTEGER NOT NULL DEFAULT 0;  -- the persistent WriteOnce unlock marker
