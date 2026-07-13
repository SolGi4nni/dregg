-- UGC GALLERY — VERIFIED AUTHOR IDENTITY + REMIX/FORK LINEAGE (creator-economy foundation).
--
-- Additive to 005_ugc_gallery.sql. Two pieces of a universe become VERIFIABLE, not merely
-- labelled, and both survive a restart (re-verified on boot by `commands::gallery::load_registry`):
--
--   * VERIFIED AUTHOR IDENTITY — `author_key_hex` is the publisher's ed25519 public key,
--     and `author_sig_hex` is their ATTESTATION signature over the universe's content
--     commitment. On boot ugc-dregg re-checks the signature (`UniversePlan::attest`) and
--     binds the key into the content address, so authorship is attributable + unforgeable:
--     a publish claiming another author's key without its signature is refused, and a
--     tampered `author_sig_hex` fails re-verification and the row is dropped. `NULL` for a
--     legacy/anonymous universe (author = a bare name only).
--   * REMIX / FORK LINEAGE — `parent_id_hex` is the content address of the universe this
--     one remixes/forks, forming a derivation graph (parent -> child). The parent is bound
--     into the child's own content address, so a tampered link recomputes a different
--     `id_hex` and the row is dropped; and on reload a remix is admitted only once its
--     parent is present (`Registry::publish_derived`). `NULL` for a root universe.
--
-- What a fuller creator economy still needs (named, not built): paid / premium universes +
-- a remix-royalty split over the $DREGG rails, and anti-sybil (staking / rate-limiting a
-- publish). See discord-bot/src/commands/gallery.rs and ugc-dregg's crate docs.
--
-- NOTE: `Database::connect` also adds these columns inline (a fresh DB gets them in the
-- CREATE TABLE; an existing DB via best-effort `ALTER TABLE ... ADD COLUMN`), matching the
-- bot's schema-in-code pattern; this file documents the migration for the migrations dir.

ALTER TABLE ugc_universes ADD COLUMN parent_id_hex  TEXT;  -- remix/fork parent content address (hex); NULL = root
ALTER TABLE ugc_universes ADD COLUMN author_key_hex TEXT;  -- verified author ed25519 public key (hex); NULL = anonymous
ALTER TABLE ugc_universes ADD COLUMN author_sig_hex TEXT;  -- author attestation signature (hex) over the content commitment
