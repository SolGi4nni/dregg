-- pg-dregg — Tier C schema sketch: writes through the verifier (the CHECK tooth).
--
-- =============================================================================
-- ⚠ DESIGN SKETCH — NOT A MIGRATION. See docs/PG-DREGG.md §10 (Tier C).
-- =============================================================================
-- Tier C makes the VERIFIER ITSELF the gate on dregg state: no row exists unless
-- it is the post-image of a turn whose proof verified AND whose pre-state root
-- chains onto the current head. This is the spine invariant (docs/PG-DREGG.md
-- §8) enforced by the database engine, not by trusting the writer:
--
--     Reads are free SQL; state mutates ONLY through verified turns.
--
-- Builds on schema-tierB.sql (the tables). The ONLY door to state is
-- dregg.commit_log; its INSERT trigger runs dregg_verify_turn + the root-chain
-- check, then materializes the post-state. dregg_verify_turn is provided by the
-- pg-dregg extension built with the `tier-c` feature (the embedded STARK/PI
-- verifier — AUTHORIZED, docs/PG-DREGG.md §8.1), or as a C-callout to a
-- co-located node.
--
-- HONEST FAILURE MODE (docs/PG-DREGG.md §10.3): if dregg_verify_turn is stubbed
-- to TRUE, the trigger is dropped, or an app is granted a direct write, the gate
-- is GONE and forged state is silently accepted. Tier C's correctness rests on
-- (a) the verifier being the REAL verifier (the named differential, §4), and
-- (b) this trigger + the privilege lockdown being audited as load-bearing.

CREATE EXTENSION IF NOT EXISTS pg_dregg;   -- built with the `tier-c` feature

-- ===========================================================================
-- 1.  The verifier surface (provided by the extension, `tier-c` feature).
-- ===========================================================================
-- TRUE iff `proof` proves that applying `envelope` to the pre-state produces
-- `receipt` (whose post-state root is receipt's ledger_root), under `vk`.
-- Pure verification: no execution, no Lean executor — the STARK/PI light-client
-- checker + the PI binding. STABLE (depends only on its args + the configured
-- verifying key); fail-closed (any decode/verify error ⇒ FALSE).
--
--   CREATE FUNCTION dregg_verify_turn(envelope bytea, receipt bytea,
--                                     proof bytea, vk bytea)
--     RETURNS boolean STABLE PARALLEL SAFE STRICT;   -- (extension-provided)
--
-- The verifying key (vk) is the database's proof trust root, configured like the
-- issuer key (a GUC, dregg.turn_vk), so a turn cannot point verification at a vk
-- it controls. Passing vk per-row is for the multi-vk case; the GUC is the norm.

-- ===========================================================================
-- 2.  The commit log — the ONE door to state.
-- ===========================================================================
-- An application NEVER writes dregg.cells/memory/capabilities directly (the
-- privilege lockdown in schema-tierB.sql §7 forbids it). The only way state
-- changes is to submit a verified turn here. Even dregg_kernel writes go through
-- the trigger.
CREATE TABLE IF NOT EXISTS dregg.commit_log (
    ordinal    bigint PRIMARY KEY,     -- must be (SELECT coalesce(max(ordinal)+1,0) FROM dregg.turns)
    envelope   bytea NOT NULL,         -- the submitted turn (CallForest / SignedTurn bytes)
    receipt    bytea NOT NULL,         -- the produced TurnReceipt (carries post-state root)
    proof      bytea NOT NULL,         -- the full-turn STARK proof
    vk         bytea NOT NULL,         -- the verifying key the proof is under
    prev_root  bytea NOT NULL,         -- the pre-state root this turn applies to
    submitted_at timestamptz NOT NULL DEFAULT now()
);

-- ===========================================================================
-- 3.  The gate — verify + chain + materialize, atomically.
-- ===========================================================================
-- A row reaches dregg.cells/memory/capabilities ONLY through this trigger, and
-- ONLY after (a) the proof verifies and (b) the root chains. The materialize
-- step derives the post-images from the VERIFIED receipt and upserts them in the
-- SAME transaction — so cells/memory/caps and the turns row commit together or
-- not at all. (dregg.materialize_post_state decodes the receipt into the typed
-- rows; in the embedded build it is an extension function, in the mirror build
-- the node supplies the MirrorBatch. The root-chain check is the Rust
-- mirror::RootChain tooth, proven postgres-free in src/mirror.rs.)
CREATE OR REPLACE FUNCTION dregg.apply_verified_turn() RETURNS trigger
LANGUAGE plpgsql SECURITY DEFINER AS $$
DECLARE
    head_root  bytea;
    next_ord   bigint;
BEGIN
    -- (1) The proof MUST verify. Fail-closed: a stub/forged proof RAISEs.
    IF NOT dregg_verify_turn(NEW.envelope, NEW.receipt, NEW.proof, NEW.vk) THEN
        RAISE EXCEPTION 'dregg: turn proof does not verify — refused (ordinal %)', NEW.ordinal;
    END IF;

    -- (2) The turn MUST chain: its pre-state root equals the current head root,
    --     and its ordinal is the next expected one. (mirror::RootChain in SQL.)
    SELECT ledger_root, ordinal + 1 INTO head_root, next_ord
      FROM dregg.turns ORDER BY ordinal DESC LIMIT 1;
    IF NOT FOUND THEN
        next_ord := 0;                         -- genesis
        head_root := NEW.prev_root;            -- pinned by the configured genesis
    END IF;
    IF NEW.ordinal <> next_ord THEN
        RAISE EXCEPTION 'dregg: ordinal gap — expected %, got % (replay/gap refused)',
            next_ord, NEW.ordinal;
    END IF;
    IF NEW.prev_root IS DISTINCT FROM head_root THEN
        RAISE EXCEPTION 'dregg: turn does not chain to head root — refused (anti-substitution)';
    END IF;

    -- (3) Record the verified turn + materialize its post-state, same txn.
    INSERT INTO dregg.turns(ordinal, height, block_id, block_executed_up_to,
                            turn_hash, creator, receipt_hash, ledger_root, prev_root)
        SELECT * FROM dregg.decode_turn_row(NEW.ordinal, NEW.receipt);
    PERFORM dregg.materialize_post_state(NEW.ordinal, NEW.receipt);
    RETURN NEW;
END $$;

DROP TRIGGER IF EXISTS verify_before_apply ON dregg.commit_log;
CREATE TRIGGER verify_before_apply
    BEFORE INSERT ON dregg.commit_log
    FOR EACH ROW EXECUTE FUNCTION dregg.apply_verified_turn();

-- ===========================================================================
-- 4.  Submitting a turn IS the only write. Apps get INSERT on commit_log only.
-- ===========================================================================
-- Note: the ONLY grant an application needs to change state is INSERT on
-- dregg.commit_log — and even that runs the verifier. They never touch the
-- state tables directly.
GRANT INSERT ON dregg.commit_log TO dregg_kernel;   -- the submit role
REVOKE INSERT, UPDATE, DELETE ON dregg.commit_log FROM PUBLIC;

-- The light client, in SQL: dregg.turns is now a hash chain (each row's
-- ledger_root is the verified post-state of applying the prior root + this
-- turn). A consumer can walk it and re-verify non-omission against the receipt
-- range (dregg-query's AttestedAnswer, docs/PG-DREGG.md §7) — reads are not only
-- free, they can be ATTESTED free.

-- ===========================================================================
-- 5.  Tier D preview (docs/PG-DREGG.md §11) — the executor as a pg function.
-- ===========================================================================
-- With the `tier-d` feature (the embedded executor — AUTHORIZED, §8.1, gated on
-- the pg/Lean process-model spike), submission collapses to EXECUTION:
--
--   SELECT dregg_submit_turn(envelope);   -- runs the kernel, returns the receipt
--
-- and the post-state lands atomically. At that point postgres IS a dregg node:
--   BEGIN;
--     SELECT dregg_submit_turn(pay_invoice_envelope);  -- dregg state changes
--     UPDATE invoices SET paid = true WHERE id = 7;     -- app state changes
--   COMMIT;                                              -- both, or neither.
-- That cross-domain atomicity (kernel + app data in one transaction) is the
-- unique Tier-D payoff no separate node can offer.
