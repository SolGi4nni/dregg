"""A DURABLE VERIFIED WORKFLOW over pg-dregg, in Python — recurring billing whose
every charge is a capability-gated turn, exactly-once across a crash.

This is the Python face of ``pg-dregg/examples/subscription_billing.rs`` (the
Rust revocation flagship). It drives the SAME shape — a recurring subscription
charge is a *verified turn*, a subscription IS a capability, cancelling refuses
the next charge, and a crash mid-run resumes exactly-once — through the
``dregg.pg`` durable-workflow runner over a live pg-dregg-enabled PostgreSQL.

    # against the local cargo-pgrx pg18 cluster (auto-discovered):
    uv run --extra pg python examples/pg_durable_workflow.py
    # or with an explicit DSN:
    DREGG_PG_DSN='host=127.0.0.1 port=28818 dbname=dregg' python examples/pg_durable_workflow.py

WHAT IS REAL HERE (enforced by the database engine, against live pg18):
  * each charge is enqueued as a verified turn into ``dregg.submit_queue``, a
    DURABLE row (it survives a process crash the instant ``dregg_submit_turn``
    returns);
  * the enqueue is RLS-gated — a role submits ONLY the turns its presented
    capability admits ``submit`` on (``submit_gate``); a charge for a cell the
    token does not authorize is refused by Row-Level Security;
  * the runner drives each step to a terminal outcome and is EXACTLY-ONCE across
    crashes: ``resume`` reconciles against the persisted queue rows and re-drives
    only the uncommitted tail — a committed charge is never double-submitted.

THE HONEST SEAM (``docs/PG-DREGG.md`` §11.4). The transition that *executes* a
queued turn (``pending → executed``) is the **node drainer's** job (it runs each
turn through the real verified Lean executor). This example has no node, so it
uses ``dregg.pg.LocalDrainer`` — a dev-only ``dregg_kernel``-role applicator that
resolves the row but is NOT the verified executor (it writes no cell state). A
production deployment runs the real drainer; the runner code is identical.

The example creates a UNIQUELY-NAMED scratch database, installs pg-dregg there,
runs the whole story, and DROPs it — so it is safe to run anywhere a pg-dregg
cluster is reachable, and leaves no residue.
"""

from __future__ import annotations

import os
import sys
import uuid

try:
    import psycopg
except ModuleNotFoundError:
    print("this example needs psycopg (v3): pip install 'dregg[pg]'", file=sys.stderr)
    sys.exit(2)

from dregg import pg as dpg


# ── cosmetics ──
def rule(title: str) -> None:
    print(f"\n\033[1m\033[36m── {title} " + "─" * max(0, 60 - len(title)) + "\033[0m")


def note(text: str) -> None:
    print(f"    \033[2m({text})\033[0m")


# The test issuer root (RootKey::from_seed([7;32])) the cargo-pgrx cluster is
# configured with cluster-wide; its private seed lets dregg_dev_mint issue tokens
# that verify under the inherited public key.
ISSUER_PUBKEY = "ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c"
ISSUER_PRIVKEY = "07" * 32

# Prefix-stable party cells (so a cap attenuated to a party's hex prefix admits
# exactly that party's cell as an RLS resource — the same convention the Rust
# flagship uses).
def party(tag: int) -> bytes:
    return bytes([tag] + [0x11] * 31)


MERCHANT = party(0x33)
ALICE = party(0xA1)
BOB = party(0xB0)


def discover_admin_dsn() -> str | None:
    explicit = os.environ.get("DREGG_PG_ADMIN_DSN") or os.environ.get("DREGG_PG_DSN")
    if explicit:
        return explicit
    sock = os.path.expanduser("~/.pgrx")
    for dsn in (
        "host=127.0.0.1 port=28818 dbname=postgres",
        f"host={sock} port=28818 dbname=postgres",
        f"host={sock} port=28817 dbname=postgres",
        "host=127.0.0.1 port=28817 dbname=postgres",
    ):
        try:
            with psycopg.connect(dsn, connect_timeout=2) as c:
                with c.cursor() as cur:
                    cur.execute(
                        "SELECT count(*) FROM pg_available_extensions WHERE name='pg_dregg'"
                    )
                    if (cur.fetchone() or [0])[0] >= 1:
                        return dsn
        except Exception:
            continue
    return None


def swap_db(dsn: str, db: str) -> str:
    parts = [p for p in dsn.split() if not p.startswith("dbname=")]
    parts.append(f"dbname={db}")
    return " ".join(parts)


def main() -> int:
    print("\033[1mpg-dregg DURABLE VERIFIED WORKFLOW (Python) — recurring billing, exactly-once, cap-gated\033[0m")
    print('\033[2m"Each charge is a verified turn; a subscription IS a capability; a crash resumes exactly-once."\033[0m')

    admin = discover_admin_dsn()
    if admin is None:
        print(
            "\n\033[33mNO pg-dregg-enabled postgres reachable.\033[0m\n"
            "  This example needs a pg-dregg (pgrx) cluster. Either:\n"
            "    • start the cargo-pgrx cluster (cd pg-dregg && cargo pgrx run pg18), or\n"
            "    • set DREGG_PG_DSN to a database with `CREATE EXTENSION pg_dregg` available.\n"
            "  The pg-dregg-native API surface is unit-tested without a DB "
            "(tests/test_pg_workflow.py); this script is the live-path demo."
        )
        return 0

    db = f"dregg_pywf_demo_{uuid.uuid4().hex[:12]}"
    try:
        with psycopg.connect(admin, autocommit=True) as c:
            c.execute(f'CREATE DATABASE "{db}"')
    except psycopg.OperationalError as exc:
        print(
            f"\n\033[33mCould not connect to the pg-dregg admin DSN ({admin!r}):\033[0m\n"
            f"  {exc}\n"
            "  Set DREGG_PG_DSN to a reachable pg-dregg cluster, or start cargo-pgrx "
            "(cd pg-dregg && cargo pgrx run pg18). The API surface is unit-tested "
            "without a DB (tests/test_pg_workflow.py)."
        )
        return 0
    db_dsn = swap_db(admin, db)
    try:
        return run_story(admin, db, db_dsn)
    finally:
        with psycopg.connect(admin, autocommit=True) as c:
            c.execute(
                "SELECT pg_terminate_backend(pid) FROM pg_stat_activity "
                "WHERE datname = %s AND pid <> pg_backend_pid()",
                (db,),
            )
            c.execute(f'DROP DATABASE IF EXISTS "{db}"')
        print(f"\n\033[2mscratch database {db} dropped (no residue).\033[0m")


def run_story(admin: str, db: str, db_dsn: str) -> int:
    # ── 0. install pg-dregg + the write outbox into the scratch DB ──
    rule("0. install pg-dregg into a scratch database (the spine: writes are verified turns)")
    with psycopg.connect(admin, autocommit=True) as c:
        c.execute(f"ALTER DATABASE \"{db}\" SET dregg.issuer_privkey = '{ISSUER_PRIVKEY}'")
    with psycopg.connect(db_dsn, autocommit=True) as c:
        c.execute("CREATE EXTENSION IF NOT EXISTS pg_dregg")
    with psycopg.connect(db_dsn, autocommit=True) as c:
        cur = c.cursor()
        cur.execute("SELECT dregg_install_schema()")
        print("  " + cur.fetchone()[0])
        cur.execute("SELECT dregg_install_write_outbox()")
        print("  " + cur.fetchone()[0])
        cur.execute("SELECT current_setting('dregg.issuer_pubkey', true)")
        pub = cur.fetchone()[0]
    if pub != ISSUER_PUBKEY:
        print(
            f"\n\033[33mThe cluster's dregg.issuer_pubkey ({pub or 'unset'}) is not the test "
            "root, so dev-minted tokens will not verify. Configure it cluster-wide "
            "(ALTER SYSTEM SET dregg.issuer_pubkey = ...; SELECT pg_reload_conf()) to run "
            "the live story. The runner + RLS surface is exercised by the unit + "
            "live tests regardless.\033[0m"
        )
        return 0
    print(f"  issuer trust root (dregg.issuer_pubkey): {pub[:16]}… (the test root)")

    # ── 1. each subscription IS a capability (mint the per-party submit tokens) ──
    rule("1. a subscription IS a capability — mint each subscriber's submit token")
    with dpg.connect(db_dsn, role=None) as minter:
        # Each subscriber holds a submit cap confined to its OWN cell prefix
        # (granted ⊆ held — the no-amplification shape). Cancelling = revoking it.
        alice_tok = minter.dev_mint("alice", ["submit", "read"], ALICE.hex(), "1 hour")
        bob_tok = minter.dev_mint("bob", ["submit", "read"], BOB.hex(), "1 hour")
        bob_cap_id = minter.cap_id(bob_tok)
    print(f"  ALICE submit cap → resource prefix {ALICE.hex()[:8]}… (her own cell)")
    print(f"  BOB   submit cap → resource prefix {BOB.hex()[:8]}… (his own cell)")
    print(f"  BOB's capability id (the dregg_revoke key): {bob_cap_id[:16]}…")
    note("a subscription is not a boolean column — it is the capability the charge turn must present")

    # A charge turn's bytes. The node drainer decodes + executes these; here they
    # are opaque demo bytes the LocalDrainer marks executed. In production they are
    # real postcard SignedTurn bytes from the SDK builder. Unique per (party,cycle)
    # so each charge is a distinct durable row.
    def charge_turn(party_cell: bytes, cycle: int) -> bytes:
        return b"charge:" + party_cell[:2] + cycle.to_bytes(2, "big") + uuid.uuid4().bytes

    # ── 2. CYCLE 1 — a durable workflow charges both subscribers ──
    rule("2. billing cycle 1 — a DURABLE WORKFLOW charges both subscribers (verified turns)")
    # We bill each subscriber under THEIR OWN token (the recurring charge is the
    # subscriber's standing authorization to be debited — the cap a cancel revokes).
    # Two single-actor workflows, each presenting that subscriber's cap.
    alice_c1 = charge_turn(ALICE, 1)
    bob_c1 = charge_turn(BOB, 1)
    with dpg.connect(db_dsn, token=alice_tok, role="dregg_reader") as pg:
        drainer = dpg.LocalDrainer(pg)
        w = pg.durable_workflow("billing/alice").step("cycle1 charge ALICE", ALICE, alice_c1)
        r = pg.run_durable(w, drainer=drainer, await_timeout=10.0)
        print(f"  ALICE cycle-1: {r.outcomes[0].status.value} (receipt {(_short(r.outcomes[0].receipt_hash))})")
    with dpg.connect(db_dsn, token=bob_tok, role="dregg_reader") as pg:
        drainer = dpg.LocalDrainer(pg)
        w = pg.durable_workflow("billing/bob").step("cycle1 charge BOB", BOB, bob_c1)
        r = pg.run_durable(w, drainer=drainer, await_timeout=10.0)
        print(f"  BOB   cycle-1: {r.outcomes[0].status.value} (receipt {(_short(r.outcomes[0].receipt_hash))})")
    print("→ each charge committed as a durable, capability-gated verified turn.")

    # ── 3. THE REVOCATION BEAT — BOB cancels; the next charge cannot even ENQUEUE ──
    rule("3. ✸ BOB CANCELS — revoke the capability; the next charge is REFUSED at enqueue ✸")
    note("pg-dregg's submit_gate RLS evaluates dregg_admits → authz::decide, which consults the "
         "revocation registry on EVERY call. So a revoked cap fails the WITH CHECK on the very next "
         "INSERT — the cancelled charge cannot even be STAGED. (The drainer ALSO re-checks "
         "dregg_cap_not_revoked at drain — defence-in-depth for a cap revoked AFTER enqueue.)")
    note("SEAM: dregg_revoke's registry is BACKEND-LOCAL (in-process; docs/PG-DREGG.md §3.4) — shared "
         "within ONE postgres backend, not across connections. Instant CROSS-connection revocation needs "
         "the persistent dregg.revoked-table tier. So BOB cancels + charges on the SAME connection (the "
         "faithful demo of the shipped backend-local registry).")
    alice_c2 = charge_turn(ALICE, 2)
    bob_c2 = charge_turn(BOB, 2)
    with dpg.connect(db_dsn, token=alice_tok, role="dregg_reader") as pg:
        drainer = dpg.LocalDrainer(pg)
        w = pg.durable_workflow("billing/alice").step("cycle2 charge ALICE", ALICE, alice_c2)
        r = pg.run_durable(w, drainer=drainer, await_timeout=10.0)
        print(f"    ✓ ALICE charged (subscription active): {r.outcomes[0].status.value}")
    with dpg.connect(db_dsn, token=bob_tok, role="dregg_reader") as pg:
        # BOB hits cancel — revoke on THIS connection's backend-local registry.
        revoked = pg.revoke(bob_tok)
        print(f"  BOB pressed cancel ⇒ dregg_revoke(BOB's cap {(_short(revoked))}) on this backend")
        # His next charge cannot enqueue: the submit_gate's dregg_admits('submit',
        # bob) now denies (the revocation is consulted), so run_durable's enqueue
        # raises a DreggPgError (RLS refusal). No row, no turn, no state change.
        w = pg.durable_workflow("billing/bob").step("cycle2 charge BOB (CANCELLED)", BOB, bob_c2)
        try:
            pg.run_durable(w, drainer=dpg.LocalDrainer(pg), await_timeout=10.0)
            print("    \033[31mSECURITY FAILURE: a cancelled subscriber was charged\033[0m")
            return 1
        except dpg.DreggPgError as e:
            short = str(e).split("[", 1)[0].strip()
            print(f"    ✗ BOB REFUSED at enqueue — {short}")
        # The cancelled charge never even created a queue row.
        staged = pg._rows(
            "SELECT count(*) FROM dregg.submit_queue WHERE signed_turn=%s", (bob_c2,)
        )[0][0]
        assert staged == 0, "BOB's cancelled charge must not even enqueue"
    print("→ a cancelled subscription cannot even STAGE a charge: the revocation is consulted on the very next turn, fail-closed.")
    note("vs a conventional biller: 'is the subscription active?' is application code issuing an UPDATE — a bug can charge a cancelled card. Here it is a verified RLS gate the turn cannot pass.")

    # ── 4. RE-SUBSCRIBE — dregg_unrevoke restores billing on the next turn ──
    rule("4. BOB re-subscribes — revoke→unrevoke→charge on one backend shows billing restored")
    bob_resub = charge_turn(BOB, 3)
    with dpg.connect(db_dsn, token=bob_tok, role="dregg_reader") as pg:
        # Re-revoke then unrevoke on this backend so the beat is self-contained:
        # a revoked cap would refuse, and lifting it restores billing on the NEXT
        # turn — the capability itself never changed, only the revocation registry.
        pg.revoke(bob_tok)
        pg.unrevoke(bob_cap_id)
        print(f"  BOB re-subscribed ⇒ dregg_unrevoke({bob_cap_id[:12]}…)")
        w = pg.durable_workflow("billing/bob").step("re-subscribe charge BOB", BOB, bob_resub)
        r = pg.run_durable(w, drainer=dpg.LocalDrainer(pg), await_timeout=10.0)
        print(f"    ✓ BOB charged again (re-subscribed): {r.outcomes[0].status.value}")
        assert r.all_ok
    print("→ re-subscription is instant: the capability never changed — lifting the revocation restored billing on the next turn.")

    # ── 5. ✸ CRASH mid-run ✸ — a 3-charge cycle dies after step 1; resume exactly-once ──
    rule("5. ✸ CRASH mid-run — a multi-charge cycle dies; RESUME drives it exactly-once ✸")
    # A cycle-4 workflow over THREE charges for ALICE. We drive only the first,
    # then "crash" (drop the connection) — the enqueued rows are durable. On
    # resume, the runner reconciles what committed and re-drives only the tail,
    # double-submitting NOTHING.
    c4 = [charge_turn(ALICE, 40 + i) for i in range(3)]
    # Phase A: a fresh connection, drive ALL THREE but with NO drainer so they
    # enqueue durably and then we "crash" before they execute. Actually we drive
    # step 1 to executed (drainer present) then crash before 2 & 3 by using a
    # single-step workflow, leaving 2 & 3 unstaged — the most honest crash: the
    # process died after committing one charge.
    with dpg.connect(db_dsn, token=alice_tok, role="dregg_reader") as pg:
        drainer = dpg.LocalDrainer(pg)
        w_partial = pg.durable_workflow("billing/alice/cycle4").step("c4 charge #1", ALICE, c4[0])
        pg.run_durable(w_partial, drainer=drainer, await_timeout=10.0)
        print("  the biller charged #1, then CRASHED (the connection drops). The committed charge is durable.")
    # Phase B: a NEW connection (the restarted biller) RESUMES the full 3-charge
    # workflow. Step #1 is recognized as already-committed and SKIPPED; #2 and #3
    # are driven. Exactly-once: #1 is not charged twice.
    with dpg.connect(db_dsn, token=alice_tok, role="dregg_reader") as pg:
        drainer = dpg.LocalDrainer(pg)
        w_full = (
            pg.durable_workflow("billing/alice/cycle4")
            .step("c4 charge #1", ALICE, c4[0])
            .step("c4 charge #2", ALICE, c4[1])
            .step("c4 charge #3", ALICE, c4[2])
        )
        report = pg.resume_durable(w_full, drainer=drainer, await_timeout=10.0)
        statuses = [(o.step.name, o.status.value) for o in report]
        print(f"  recovered + resumed: {statuses}")
        print(f"    committed this resume = {report.committed}, skipped (already done) = {report.skipped}")
        assert report.all_ok, statuses
        assert report.skipped == 1, "exactly-once: charge #1 was skipped, not re-charged"
        assert report.committed == 2, "the uncommitted tail (#2, #3) was driven"
        # Verify against the REAL queue: each of the 3 turns has EXACTLY ONE row.
        for i, turn in enumerate(c4):
            n = pg._rows("SELECT count(*) FROM dregg.submit_queue WHERE signed_turn=%s", (turn,))[0][0]
            assert n == 1, f"charge #{i+1} has {n} rows (exactly-once violated)"
    print("→ recovery is exactly-once: the committed charge was SKIPPED on resume, the tail driven — no charge lost, none double-applied.")

    # ── 6. CAP-GATED READS — the outbox audit trail, RLS-narrowed to the token ──
    rule("6. cap-gated reads — the audit trail (free SQL, RLS-narrowed to the presented token)")
    with dpg.connect(db_dsn, token=alice_tok, role="dregg_reader") as pg:
        subs = pg.outbox()
        alice_subs = [s for s in subs if s.agent == ALICE.hex()]
        print(f"  ALICE's token sees {len(alice_subs)} of her submissions (RLS-gated to her cell):")
        for s in alice_subs:
            print(f"    {s.status:<9} agent={s.agent[:8]}…  receipt={_short(s.receipt_hash)}")
        # ALICE's token does NOT see BOB's submissions (the no-amplification read).
        bob_visible = [s for s in subs if s.agent == BOB.hex()]
        print(f"  ALICE's token sees {len(bob_visible)} of BOB's submissions (cap does not admit his cell)")
        assert bob_visible == [], "ALICE's cap must not surface BOB's rows"
    print("→ a read returns exactly the rows the presented capability admits — the same decision the kernel makes.")

    # ── DONE ──
    rule("DONE — a durable verified workflow ran through pg-dregg, in Python")
    print("\033[1m\033[32m✓ recurring subscription billing, driven from Python over live pg-dregg:\033[0m")
    print("    • each charge a \033[1mdurable, capability-gated verified turn\033[0m (enqueued into dregg.submit_queue);")
    print("    • a subscription IS a \033[1mcapability\033[0m — cancelling it is \033[1mdregg_revoke\033[0m;")
    print("    • a \033[1mcancelled subscriber's next charge was REFUSED\033[0m at enqueue by the submit_gate RLS;")
    print("    • \033[1mre-subscription restored billing\033[0m on the next turn (the cap never changed — only the registry);")
    print("    • the biller \033[1msurvived a crash\033[0m and \033[1mresumed exactly-once\033[0m (a committed charge skipped, the tail driven);")
    print("    • \033[1mcap-gated reads\033[0m narrowed the audit trail to exactly the rows the token admits.")
    print("\n  The Python face of pg_dregg::workflow — \033[2mthe enqueue + RLS + exactly-once are real;\033[0m")
    print("  \033[2mthe pending→executed drain is the node drainer's job (here the LocalDrainer stand-in, §11.4).\033[0m")
    return 0


def _short(h) -> str:
    if not h:
        return "—"
    s = h if isinstance(h, str) else str(h)
    return s[:12] + "…"


if __name__ == "__main__":
    sys.exit(main())
