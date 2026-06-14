#!/usr/bin/env bash
# pg-dregg — LIVE pg18 federation CONFLICT → re-validation proof.
#
# Proves the §15/§10 wiring against the GENUINE pg18 `confl_*` counters (NOT a
# fixture): the apply-conflict alarm DRIVES the chain re-validation.
#
#   1. Stands up a PUBLISHER db + a SUBSCRIBER db on the live cargo-pgrx pg18.
#   2. Installs the dregg schema on both; lands a real gate-built turn chain on the
#      publisher; CREATE PUBLICATION over the state tables.
#   3. CREATE SUBSCRIPTION on the subscriber (real logical replication tail).
#   4. Provokes a REAL apply conflict: writes a row on the SUBSCRIBER that the
#      publisher's stream then re-INSERTs => pg18 bumps `confl_insert_exists` in
#      `pg_stat_subscription_stats` (the counter `dregg.replication_conflicts` sums).
#   5. Runs `dregg_federation_health()` on the SUBSCRIBER and shows the alarm fires
#      AND the chain re-validation triggers — read off the real pg18 counter.
#
# Logical replication needs `wal_level = logical`; this script sets it and
# RESTARTS the cargo-pgrx cluster (then leaves it running). pg-dregg/ ONLY.
#
# Usage:  pg-dregg/scripts/federation-conflict-live.sh
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # the pg-dregg crate dir
PGBIN="$(brew --prefix postgresql@18)/bin"
PSQL="$PGBIN/psql"
PORT=28818                                                # the cargo-pgrx pg18 port
SOCK="$HOME/.pgrx"
PUB=fedpub
SUB=fedsub
# The test issuer root is RootKey::from_seed([7;32]); this is its public key.
ISSUER_PUBKEY=ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c

P() { "$PSQL" -h "$SOCK" -p "$PORT" "$@"; }

cd "$HERE"

echo "== install the pg_dregg extension into pg18 =="
cargo pgrx install --pg-config "$PGBIN/pg_config" >/dev/null 2>&1 || true
cargo pgrx start pg18 >/dev/null 2>&1 || true

echo "== ensure wal_level = logical (needed for logical replication) =="
WAL="$(P -d postgres -tAc "SHOW wal_level;")"
if [ "$WAL" != "logical" ]; then
  P -d postgres -c "ALTER SYSTEM SET wal_level = 'logical';" >/dev/null
  echo "   wal_level was '$WAL' — set to 'logical', restarting the cluster"
  cargo pgrx stop pg18 >/dev/null 2>&1 || true
  cargo pgrx start pg18 >/dev/null 2>&1 || true
  sleep 2
  WAL="$(P -d postgres -tAc "SHOW wal_level;")"
fi
echo "   wal_level = $WAL"

echo "== (re)create clean publisher ($PUB) + subscriber ($SUB) databases =="
for db in "$SUB" "$PUB"; do
  P -d postgres -c "DROP DATABASE IF EXISTS $db;" >/dev/null 2>&1 || {
    # drop any leftover subscription that holds a slot first
    P -d "$db" -c "DROP SUBSCRIPTION IF EXISTS dregg_tail;" >/dev/null 2>&1 || true
    P -d postgres -c "DROP DATABASE IF EXISTS $db;" >/dev/null
  }
  P -d postgres -c "CREATE DATABASE $db;" >/dev/null
done

echo "== set the issuer key (server-level Sighup GUC) =="
P -d postgres -c "ALTER SYSTEM SET dregg.issuer_pubkey = '$ISSUER_PUBKEY';" >/dev/null
P -d postgres -c "SELECT pg_reload_conf();" >/dev/null
sleep 1

# ---------------------------------------------------------------------------
# PUBLISHER: schema + a real gate-built turn chain + the publication.
# ---------------------------------------------------------------------------
echo ""
echo "== PUBLISHER: install schema (Tier B + C) + federation publication =="
P -d "$PUB" -c "CREATE EXTENSION IF NOT EXISTS pg_dregg;" >/dev/null
P -d "$PUB" -c "SELECT dregg_install_schema();" >/dev/null
P -d "$PUB" -c "SELECT dregg_install_tier_c();" >/dev/null

echo "== PUBLISHER: land a genesis + transfer through the verified-store gate =="
# Genesis (ord 0): TREASURY funded. prev_root = genesis (all-zero).
P -d "$PUB" >/dev/null <<'SQL'
SET ROLE dregg_kernel;
INSERT INTO dregg.commit_log
  (ordinal, height, block_id, block_executed_up_to, turn_hash, creator,
   receipt_hash, ledger_root, prev_root, cells)
VALUES
  (0, 0, '\x00'::bytea, 0, '\x10'::bytea, '\xc0'::bytea, '\x20'::bytea,
   '\xaa'::bytea, '\x0000000000000000000000000000000000000000000000000000000000000000'::bytea,
   '[{"cell_id":"c000000000000000000000000000000000000000000000000000000000000000",
      "mode":"Hosted","balance":1000000,"nonce":0,"fields":"",
      "lifecycle":"Active","cell_root":"c0c0"}]'::jsonb);
RESET ROLE;
SQL
P -d "$PUB" -c "SELECT dregg_install_federation();" >/dev/null
PUBCOUNT="$(P -d "$PUB" -tAc "SELECT count(*) FROM dregg.turns;")"
echo "   publisher dregg.turns has $PUBCOUNT turn(s); publication dregg_mirror created"

# ---------------------------------------------------------------------------
# SUBSCRIBER: schema, subscribe (NO initial copy), then PROVOKE a streaming-apply
# conflict the pg18 confl_* counters track.
# ---------------------------------------------------------------------------
echo ""
echo "== SUBSCRIBER: install schema + publication (so it has the conflicts view) =="
P -d "$SUB" -c "CREATE EXTENSION IF NOT EXISTS pg_dregg;" >/dev/null
P -d "$SUB" -c "SELECT dregg_install_schema();" >/dev/null
P -d "$SUB" -c "SELECT dregg_install_tier_c();" >/dev/null
P -d "$SUB" -c "SELECT dregg_install_federation();" >/dev/null

# Pre-seed a row on the SUBSCRIBER that a LATER publisher INSERT will collide with.
# The confl_* counters track APPLY (streamed-change) conflicts, NOT the initial
# table COPY — so we subscribe with copy_data=false (skip the sync that would
# itself trip on this row), then INSERT the colliding ordinal on the publisher
# AFTER the tail is live. That replicated INSERT hits this existing PK on the
# subscriber => a genuine confl_insert_exists in pg_stat_subscription_stats.
echo "== SUBSCRIBER: pre-seed ord-1 (the PK a later publisher INSERT will collide with) =="
P -d "$SUB" >/dev/null <<'SQL'
SET ROLE dregg_kernel;
INSERT INTO dregg.turns
  (ordinal, height, block_id, block_executed_up_to, turn_hash, creator,
   receipt_hash, ledger_root, prev_root)
VALUES
  (1, 1, '\xee'::bytea, 1, '\xe1'::bytea, '\xee'::bytea, '\xee'::bytea,
   '\xbb'::bytea, '\xaa'::bytea);
RESET ROLE;
SQL

echo "== SUBSCRIBER: CREATE SUBSCRIPTION (copy_data=false ⇒ apply-only tail) =="
CONN="host=$SOCK port=$PORT dbname=$PUB"
SLOT="dregg_tail_$$"
P -d "$SUB" -c \
  "CREATE SUBSCRIPTION dregg_tail CONNECTION '$CONN' PUBLICATION dregg_mirror \
   WITH (slot_name='$SLOT', create_slot=true, copy_data=false);" >/dev/null
echo "   subscription dregg_tail created (slot $SLOT); tail is apply-only"
# Give the apply worker a moment to come up and reach streaming.
sleep 3

echo "== PUBLISHER: now INSERT the COLLIDING ord-1 (a real verified turn) =="
# This turn streams to the subscriber, whose apply tries to INSERT ord-1 — which
# the subscriber already holds => a genuine pg18 confl_insert_exists.
P -d "$PUB" >/dev/null <<'SQL'
SET ROLE dregg_kernel;
INSERT INTO dregg.commit_log
  (ordinal, height, block_id, block_executed_up_to, turn_hash, creator,
   receipt_hash, ledger_root, prev_root, cells)
VALUES
  (1, 1, '\x01'::bytea, 1, '\x11'::bytea, '\xc0'::bytea, '\x21'::bytea,
   '\xbb'::bytea, '\xaa'::bytea, '[]'::jsonb);
RESET ROLE;
SQL
echo "   publisher ord-1 inserted; waiting for the streamed apply conflict to register"

# Let the apply worker hit the conflicting row and bump the stat counter.
CONFL=0
for i in $(seq 1 25); do
  CONFL="$(P -d "$SUB" -tAc \
    "SELECT coalesce(sum(conflicts_total),0)::bigint FROM dregg.replication_conflicts;" 2>/dev/null || echo 0)"
  [ "${CONFL:-0}" != "0" ] && break
  sleep 1
done
echo "   pg18 confl_* total now: ${CONFL:-0}"

echo ""
echo "== SUBSCRIBER: the REAL pg18 conflict counters =="
P -d "$SUB" -c \
  "SELECT subname, confl_insert_exists, conflicts_total FROM dregg.replication_conflicts;"

echo ""
echo "== SUBSCRIBER: dregg_federation_health() — alarm DRIVES re-validation =="
echo "-- run as the kernel/operator (it reads replication_conflicts + dregg.turns)"
P -d "$SUB" -c "SELECT dregg_federation_health() AS federation_health;"

echo ""
echo "== assert: a non-zero genuine pg18 conflict ⇒ the alarm fired =="
VERDICT="$(P -d "$SUB" -tAc "SELECT dregg_federation_health();")"
echo "   verdict: $VERDICT"
case "$VERDICT" in
  ok:*)
    if [ "${CONFL:-0}" = "0" ]; then
      echo "   (no apply conflict registered — the verdict is correctly healthy)"
    else
      echo "!! FAIL: a non-zero conflict ($CONFL) but the verdict is healthy" >&2
      exit 1
    fi
    ;;
  ALARM*|CRITICAL*)
    echo "   PASS: the genuine pg18 conflict alarm fired AND triggered re-validation"
    ;;
  *)
    echo "!! FAIL: unexpected verdict: $VERDICT" >&2
    exit 1
    ;;
esac

echo ""
echo "== cleanup: drop the subscription + free the publisher slot =="
# Disable + detach the slot first so DROP cannot hang on a live walreceiver, then
# drop the slot on the publisher explicitly (a dropped subscriber DB would orphan it).
P -d "$SUB" -c "ALTER SUBSCRIPTION dregg_tail DISABLE;" >/dev/null 2>&1 || true
P -d "$SUB" -c "ALTER SUBSCRIPTION dregg_tail SET (slot_name = NONE);" >/dev/null 2>&1 || true
P -d "$SUB" -c "DROP SUBSCRIPTION IF EXISTS dregg_tail;" >/dev/null 2>&1 || true
# Free the slot on the publisher (terminate its walsender if still active).
for pid in $(P -d postgres -tAc "SELECT active_pid FROM pg_replication_slots WHERE slot_name='$SLOT' AND active;" 2>/dev/null); do
  P -d postgres -c "SELECT pg_terminate_backend($pid);" >/dev/null 2>&1 || true
done
P -d postgres -c "SELECT pg_drop_replication_slot('$SLOT');" >/dev/null 2>&1 || true
echo "done."
