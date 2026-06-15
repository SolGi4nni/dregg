"""Tests for ``dregg.pg_workflow`` — the durable verified workflow runner.

Two layers, mirroring ``test_pg.py``:

* **Unit** (always run): the runner's enqueue → await → exactly-once loop and the
  ``LocalDrainer`` arms, against a stateful FAKE ``dregg.submit_queue`` (a Python
  dict that mimics the real ``pending → executed | refused`` lifecycle + the
  ``submit_queue_audit`` / base-table reads the runner polls). No database — these
  pin the runner's control flow + reconciliation to the real SQL surface shape.
* **Integration** (``@pytest.mark.pg_integration``, skip-gated): the SAME runner
  driving REAL ``dregg.submit_queue`` rows on a live pg-dregg pg18 cluster — the
  durable enqueue, the ``submit_gate`` RLS, and the crash-resume reconciliation,
  with a ``LocalDrainer`` standing in for the node drainer (the honest seam:
  ``pending → executed`` is the node's job; the stand-in is the kernel-role
  applicator, NOT the verified executor). Swarm-safe: a uniquely-named scratch DB.
"""

from __future__ import annotations

import os
import uuid

import pytest

from dregg import pg as dpg
from dregg import pg_workflow as wf


# ════════════════════ unit: a stateful fake submit_queue ════════════════════
# Mimics the real lifecycle: dregg_submit_turn enqueues a (uuid) row in 'pending'
# with (agent, signed_turn); a "drain" flips it to executed|refused; the runner
# polls submission(id) [base table] and reconciles via the base-table read in
# _iter_prior_submissions. We model exactly those queries.


def _norm(sql) -> str:
    return " ".join(str(sql).split())


class QueueRow:
    def __init__(self, sid, agent_hex, signed_turn, submit_token=None):
        self.id = sid
        self.agent_hex = agent_hex
        self.signed_turn = signed_turn
        self.submit_token = submit_token
        self.status = "pending"
        self.receipt_hash = None
        self.error = None


class FakeQueueCursor:
    def __init__(self, conn):
        self._conn = conn
        self._result = []

    def execute(self, sql, params=()):
        s = _norm(sql)
        self._conn.calls.append((s, tuple(params) if params else ()))
        self._result = self._conn.handle(s, tuple(params) if params else ())

    def fetchone(self):
        return self._result[0] if self._result else None

    def fetchall(self):
        return list(self._result)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


class FakeInfo:
    dbname = "fake"


class FakeQueueConn:
    """A fake connection that maintains an in-memory submit_queue and answers the
    exact queries the runner + LocalDrainer issue."""

    def __init__(self):
        self.calls = []
        self.rows: dict = {}  # id -> QueueRow
        self.closed = False
        self.info = FakeInfo()
        self.role = None
        # The token "presented" for enqueue (what dregg_submit_turn captures into
        # submit_token server-side), and the revoked-token set the drainer's
        # dregg_cap_not_revoked re-check consults.
        self.current_token = None
        self.revoked_tokens: set = set()
        # The audit-relation probe: pretend the base table is the relation (no v7
        # view) so the outbox helper uses the base-table column list.
        self._next_id = 0

    # psycopg-ish surface the helpers use
    def cursor(self):
        return FakeQueueCursor(self)

    def close(self):
        self.closed = True

    @property
    def connection(self):  # for LocalDrainer.pg.connection passthrough in tests
        return self

    def handle(self, sql, params):
        # ── set_config('dregg.token', ...) — capture the presented token ──
        if "set_config" in sql and len(params) >= 2 and params[0] == "dregg.token":
            self.current_token = params[1] or None
            return [(params[1],)]
        # ── dregg_submit_turn enqueue (captures submit_token server-side) ──
        if "dregg_submit_turn" in sql:
            signed_turn, agent = params
            sid = uuid.UUID(int=self._next_id)
            self._next_id += 1
            self.rows[sid] = QueueRow(
                sid, bytes(agent).hex(), bytes(signed_turn), submit_token=self.current_token
            )
            return [(sid,)]
        # ── drainer revocation re-check: read submit_token, then not_revoked ──
        if "SELECT submit_token FROM dregg.submit_queue WHERE id = %s" in sql:
            (sid,) = params
            r = self.rows.get(sid)
            return [(r.submit_token if r else None,)]
        if "dregg_cap_not_revoked" in sql:
            (token,) = params
            return [(token not in self.revoked_tokens,)]
        # ── outbox relation probe: no v7 view ⇒ use base table ──
        if "to_regclass('dregg.submit_queue_audit') IS NOT NULL" in sql:
            return [(False,)]
        # ── submission(id) via base-table fallback (status poll) ──
        if "FROM dregg.submit_queue WHERE id = %s" in sql:
            (sid,) = params
            r = self.rows.get(sid)
            if r is None:
                return []
            # base-table column shape from _outbox_relation fallback:
            # id, encode(agent,'hex'), submitter, status,
            # encode(receipt_hash,'hex'), error, submitted_at, resolved_at
            return [(
                r.id, r.agent_hex, "app", r.status,
                (r.receipt_hash.hex() if r.receipt_hash else None),
                r.error, None, None,
            )]
        # ── resume reconciliation read (_iter_prior_submissions) ──
        if "SELECT encode(agent,'hex'), signed_turn, id, status" in sql:
            out = []
            for r in sorted(self.rows.values(), key=lambda x: x.id.int):
                out.append((
                    r.agent_hex, r.signed_turn, r.id, r.status,
                    (r.receipt_hash.hex() if r.receipt_hash else None),
                ))
            return out
        # ── LocalDrainer: role swap bookkeeping ──
        if "current_setting('role', true)" in sql:
            return [(self.role,)]
        if sql.startswith("SET ROLE"):
            self.role = sql.split("SET ROLE", 1)[1].strip()
            return []
        if sql == "RESET ROLE":
            self.role = None
            return []
        # ── LocalDrainer: resolve a pending row to executed ──
        if "SET status='executed'" in sql:
            receipt, sid = params
            r = self.rows.get(sid)
            if r is not None and r.status == "pending":
                r.status = "executed"
                r.receipt_hash = bytes(receipt)
            return []
        # ── LocalDrainer: resolve to refused ──
        if "SET status='refused'" in sql:
            reason, sid = params
            r = self.rows.get(sid)
            if r is not None and r.status == "pending":
                r.status = "refused"
                r.error = reason
            return []
        # ── LocalDrainer.drain_pending: list pending ──
        if "WHERE status='pending' ORDER BY id" in sql and "signed_turn" in sql:
            return [
                (r.id, r.agent_hex, r.signed_turn)
                for r in sorted(self.rows.values(), key=lambda x: x.id.int)
                if r.status == "pending"
            ]
        return []


def mkpg(conn) -> dpg.Pg:
    return dpg.Pg(conn)  # type: ignore[arg-type]


ALICE = bytes([0xA1] + [0] * 31)
BOB = bytes([0xB0] + [0] * 31)


# ── step building + idempotency keys ──


def test_step_assigns_deterministic_idempotency_keys():
    w = wf.DurableWorkflow("billing")
    w.step("charge alice", ALICE, b"\x01")
    w.step("charge bob", BOB, b"\x02")
    assert [s.idempotency_key for s in w.steps] == [
        "billing:0:charge alice",
        "billing:1:charge bob",
    ]
    # Re-constructing the SAME workflow yields the SAME keys (resume reconciles).
    w2 = wf.DurableWorkflow("billing")
    w2.step("charge alice", ALICE, b"\x01")
    assert w2.steps[0].idempotency_key == "billing:0:charge alice"


def test_step_rejects_non_bytes_turn():
    w = wf.DurableWorkflow("x")
    with pytest.raises(TypeError):
        w.step("bad", ALICE, "not-bytes")  # type: ignore[arg-type]


def test_explicit_idempotency_key_pins_to_domain_id():
    w = wf.DurableWorkflow("billing")
    w.step("charge", ALICE, b"\x01", idempotency_key="invoice-42")
    assert w.steps[0].idempotency_key == "invoice-42"


# ── a fresh run drives every step to executed (with a LocalDrainer) ──


def test_run_drives_all_steps_to_executed():
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_live")  # a non-revoked token (the drain re-check passes)
    drainer = wf.LocalDrainer(pg)
    w = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa").step(
        "charge bob", BOB, b"\xbb"
    )
    report = w.run(pg, drainer=drainer, await_timeout=1.0)
    assert report.all_ok
    assert report.committed == 2
    assert report.skipped == 0
    assert [o.status for o in report] == [wf.StepStatus.EXECUTED, wf.StepStatus.EXECUTED]
    # Each executed step carries a receipt hash from the (stand-in) drainer.
    assert all(o.receipt_hash for o in report)
    # The enqueue went through the real extern.
    assert any("dregg_submit_turn" in c[0] for c in conn.calls)


def test_run_without_drainer_times_out_but_enqueue_is_durable():
    # No drainer + no live node ⇒ the row stays pending ⇒ the runner raises
    # WorkflowError (the enqueue is durable; a resume picks it up). This is the
    # honest "is the drainer running?" failure, not a fake green.
    conn = FakeQueueConn()
    pg = mkpg(conn)
    w = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa")
    with pytest.raises(wf.WorkflowError) as exc:
        w.run(pg, await_timeout=0.15, poll_interval=0.02)
    assert "still pending" in str(exc.value)
    # …but the row WAS enqueued (durable): exactly one pending row exists.
    assert len(conn.rows) == 1
    assert next(iter(conn.rows.values())).status == "pending"


# ── refusal handling: fail-closed by default, collectible on request ──


def test_run_stops_fail_closed_on_a_refused_step():
    conn = FakeQueueConn()
    pg = mkpg(conn)
    # Refuse BOB (model a cancelled subscriber), execute ALICE.
    def refuse(_sid, step):
        return "revoked" if step.agent_hex == BOB.hex() else None

    pg.present_token("dga1_live")
    drainer = wf.LocalDrainer(pg, refuse_predicate=refuse, check_revocation=False)
    w = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa").step(
        "charge bob (CANCELLED)", BOB, b"\xbb"
    ).step("charge carol", bytes([0xc0] + [0] * 31), b"\xcc")
    with pytest.raises(wf.StepRefused) as exc:
        w.run(pg, drainer=drainer, await_timeout=1.0)
    assert exc.value.outcome.step.name == "charge bob (CANCELLED)"
    assert exc.value.outcome.error == "revoked"
    # Carol's step never ran (fail-closed halt) — only alice + bob were enqueued.
    assert len(conn.rows) == 2


def test_run_collects_refusals_when_not_stopping():
    conn = FakeQueueConn()
    pg = mkpg(conn)

    def refuse(_sid, step):
        return "revoked" if step.agent_hex == BOB.hex() else None

    pg.present_token("dga1_live")
    drainer = wf.LocalDrainer(pg, refuse_predicate=refuse, check_revocation=False)
    w = wf.DurableWorkflow("billing").step("alice", ALICE, b"\xaa").step(
        "bob", BOB, b"\xbb"
    )
    report = w.run(pg, drainer=drainer, stop_on_refusal=False, await_timeout=1.0)
    assert not report.all_ok
    assert report.committed == 1
    assert len(report.refused) == 1
    assert report.refused[0].step.name == "bob"
    assert report.refused[0].error == "revoked"


# ── exactly-once: resume reconciles against already-committed rows ──


def test_resume_skips_already_executed_steps():
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_live")
    drainer = wf.LocalDrainer(pg)
    # First run: drive alice to executed, then "crash" before bob (simulate by
    # only running a single-step workflow for alice).
    first = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa")
    first.run(pg, drainer=drainer, await_timeout=1.0)
    assert sum(1 for r in conn.rows.values() if r.status == "executed") == 1
    enqueues_after_first = sum(1 for c in conn.calls if "dregg_submit_turn" in c[0])

    # Now resume the FULL workflow (alice + bob). alice must be SKIPPED (already
    # executed, matched by (agent, signed_turn)); only bob is enqueued + driven.
    full = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa").step(
        "charge bob", BOB, b"\xbb"
    )
    report = full.resume(pg, drainer=drainer, await_timeout=1.0)
    assert report.all_ok
    assert [o.status for o in report] == [wf.StepStatus.SKIPPED, wf.StepStatus.EXECUTED]
    assert report.skipped == 1 and report.committed == 1
    # Exactly-once: alice was NOT re-enqueued — only ONE new submit happened (bob).
    enqueues_after_resume = sum(1 for c in conn.calls if "dregg_submit_turn" in c[0])
    assert enqueues_after_resume == enqueues_after_first + 1


def test_resume_awaits_an_existing_pending_step_without_reenqueue():
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_live")
    # Enqueue alice but DON'T drain it (a crash right after enqueue, before the
    # verdict): the row is pending. A resume must await THAT row, not enqueue a
    # second one.
    w1 = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa")
    try:
        w1.run(pg, await_timeout=0.1, poll_interval=0.02)  # no drainer ⇒ times out
    except wf.WorkflowError:
        pass
    assert len(conn.rows) == 1  # one pending row
    enqueues = sum(1 for c in conn.calls if "dregg_submit_turn" in c[0])
    assert enqueues == 1

    # Resume: a drainer is now available; the runner must reconcile the pending
    # row, NOT re-enqueue, then await it to executed.
    drainer = wf.LocalDrainer(pg)
    w2 = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa")
    report = w2.resume(pg, drainer=drainer, await_timeout=1.0)
    assert report.all_ok
    assert report.outcomes[0].status is wf.StepStatus.EXECUTED
    # Still exactly ONE enqueue total (no double-submit on resume).
    enqueues2 = sum(1 for c in conn.calls if "dregg_submit_turn" in c[0])
    assert enqueues2 == 1
    assert len(conn.rows) == 1


def test_resume_on_a_fresh_db_runs_everything():
    # Resume with nothing committed yet == a normal run (no rows to skip).
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_live")
    drainer = wf.LocalDrainer(pg)
    w = wf.DurableWorkflow("billing").step("a", ALICE, b"\xaa").step("b", BOB, b"\xbb")
    report = w.resume(pg, drainer=drainer, await_timeout=1.0)
    assert report.committed == 2 and report.skipped == 0


# ── revocation bites at DRAIN (the real pg-dregg write-path semantics) ──


def test_drainer_refuses_a_revoked_token_at_drain():
    """A revoked-since-enqueue token: the charge ENQUEUES (the submit_gate admits
    the cap's caveats), but the drainer's revocation re-check refuses it — exactly
    the live ``drainer_refuses_a_revoked_since_enqueue_intent_at_drain`` behavior.
    The workflow step resolves REFUSED with reason 'revoked'; no execution."""
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_bob")  # the token the enqueue captures into submit_token
    conn.revoked_tokens.add("dga1_bob")  # …and it is revoked before drain
    drainer = wf.LocalDrainer(pg)  # check_revocation=True (the default)
    w = wf.DurableWorkflow("billing").step("charge bob (CANCELLED)", BOB, b"\xbb")
    with pytest.raises(wf.StepRefused) as exc:
        w.run(pg, drainer=drainer, await_timeout=1.0)
    assert exc.value.outcome.error == "revoked"
    # The row WAS enqueued (the submit_gate admitted it) but resolved refused.
    assert len(conn.rows) == 1
    assert next(iter(conn.rows.values())).status == "refused"


def test_drainer_executes_a_live_token():
    """The complement: a NON-revoked presented token passes the drain re-check and
    the charge executes."""
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_alice")  # not in revoked_tokens
    drainer = wf.LocalDrainer(pg)
    w = wf.DurableWorkflow("billing").step("charge alice", ALICE, b"\xaa")
    report = w.run(pg, drainer=drainer, await_timeout=1.0)
    assert report.all_ok
    assert next(iter(conn.rows.values())).status == "executed"


def test_drainer_refuses_a_tokenless_row_deny_by_default():
    """A queue row with no submit_token is deny-by-default at drain (the real
    drainer treats a tokenless row as unauthorized)."""
    conn = FakeQueueConn()
    pg = mkpg(conn)
    sid = pg.submit_turn(b"\xaa", ALICE)  # no present_token ⇒ submit_token is NULL
    drainer = wf.LocalDrainer(pg)
    drainer.drain_one(sid, wf.WorkflowStep("a", ALICE, b"\xaa"))
    assert conn.rows[sid].status == "refused"
    assert "no submit token" in (conn.rows[sid].error or "")


# ── the LocalDrainer arms directly ──


def test_local_drainer_drain_pending_resolves_all():
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_live")
    # Enqueue two without draining.
    pg.submit_turn(b"\xaa", ALICE)
    pg.submit_turn(b"\xbb", BOB)
    assert sum(1 for r in conn.rows.values() if r.status == "pending") == 2
    drainer = wf.LocalDrainer(pg)
    n = drainer.drain_pending()
    assert n == 2
    assert all(r.status == "executed" for r in conn.rows.values())


def test_local_drainer_is_idempotent_on_nonpending():
    conn = FakeQueueConn()
    pg = mkpg(conn)
    pg.present_token("dga1_live")
    sid = pg.submit_turn(b"\xaa", ALICE)
    drainer = wf.LocalDrainer(pg)
    drainer.drain_one(sid, wf.WorkflowStep("a", ALICE, b"\xaa"))
    assert conn.rows[sid].status == "executed"
    receipt1 = conn.rows[sid].receipt_hash
    # Draining again must NOT re-resolve (status no longer pending).
    drainer.drain_one(sid, wf.WorkflowStep("a", ALICE, b"\xaa"))
    assert conn.rows[sid].receipt_hash == receipt1


def test_safe_role_rejects_injection():
    assert wf._safe_role("dregg_reader") == "dregg_reader"
    for bad in ["", "1abc", "a-b", "x;y", "drop role", "a" * 64]:
        with pytest.raises(ValueError):
            wf._safe_role(bad)


# ── RunReport semantics ──


def test_run_report_counts():
    s = wf.WorkflowStep("a", ALICE, b"\x01", idempotency_key="k")
    r = wf.RunReport(outcomes=[
        wf.StepOutcome(s, wf.StepStatus.EXECUTED),
        wf.StepOutcome(s, wf.StepStatus.SKIPPED),
        wf.StepOutcome(s, wf.StepStatus.REFUSED, error="revoked"),
    ])
    assert r.committed == 1 and r.skipped == 1 and len(r.refused) == 1
    assert not r.all_ok  # a refusal present
    assert len(r) == 3


# ═══════════════════════════ integration (skip-gated) ═══════════════════════
# The SAME runner against REAL dregg.submit_queue rows on live pg18. Reuses the
# scratch-DB fixture machinery from test_pg.py so the two suites share the live
# cluster discovery + teardown. The honest seam: a LocalDrainer (kernel-role
# applicator) stands in for the node drainer — it resolves the row but is NOT the
# verified executor (it writes no cell state). What IS real here: the durable
# enqueue, the submit_gate RLS, and the crash-resume reconciliation.

PGRX_SOCK = os.path.expanduser("~/.pgrx")
ISSUER_PUBKEY = "ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c"
ISSUER_PRIVKEY = "07" * 32


def _admin_dsn():
    explicit = os.environ.get("DREGG_PG_ADMIN_DSN") or os.environ.get("DREGG_PG_DSN")
    if explicit:
        return explicit
    try:
        import psycopg
    except ModuleNotFoundError:
        return None
    candidates = [
        "host=127.0.0.1 port=28818 dbname=postgres",
        f"host={PGRX_SOCK} port=28818 dbname=postgres",
        f"host={PGRX_SOCK} port=28817 dbname=postgres",
        "host=127.0.0.1 port=28817 dbname=postgres",
    ]
    for dsn in candidates:
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


def _swap_dbname(dsn, dbname):
    parts = [p for p in dsn.split() if not p.startswith("dbname=")]
    parts.append(f"dbname={dbname}")
    return " ".join(parts)


@pytest.fixture(scope="module")
def live_db():
    admin = _admin_dsn()
    if admin is None:
        pytest.skip(
            "no pg-dregg-enabled postgres reachable (set $DREGG_PG_DSN or start the "
            "cargo-pgrx cluster on :28818/:28817 with pg_dregg available)"
        )
    import psycopg

    dbname = f"dregg_sdkwf_{uuid.uuid4().hex[:16]}"
    try:
        with psycopg.connect(admin, autocommit=True) as c:
            c.execute(f'CREATE DATABASE "{dbname}"')
    except psycopg.OperationalError as exc:
        pytest.skip(f"pg-dregg admin DSN unreachable ({admin!r}): {exc}")
    db_dsn = _swap_dbname(admin, dbname)
    try:
        with psycopg.connect(admin, autocommit=True) as c:
            c.execute(f"ALTER DATABASE \"{dbname}\" SET dregg.issuer_privkey = '{ISSUER_PRIVKEY}'")
        with psycopg.connect(db_dsn, autocommit=True) as c:
            c.execute("CREATE EXTENSION IF NOT EXISTS pg_dregg")
        with psycopg.connect(db_dsn, autocommit=True) as c:
            c.execute("SELECT dregg_install_schema()")
            c.execute("SELECT dregg_install_write_outbox()")
        yield db_dsn
    finally:
        with psycopg.connect(admin, autocommit=True) as c:
            c.execute(
                "SELECT pg_terminate_backend(pid) FROM pg_stat_activity "
                "WHERE datname = %s AND pid <> pg_backend_pid()",
                (dbname,),
            )
            c.execute(f'DROP DATABASE IF EXISTS "{dbname}"')


def _has_function(pg, signature):
    return bool(pg._scalar(f"SELECT to_regprocedure('{signature}') IS NOT NULL"))


def _verify_key_is_test_root(pg):
    return pg._scalar("SELECT current_setting('dregg.issuer_pubkey', true)") == ISSUER_PUBKEY


def _mint_submit_token(live_db, agent: bytes, ttl="1 hour"):
    """Mint a submit-scoped token confined to ``agent``'s cell, returning it."""
    with dpg.connect(live_db, role=None) as minter:
        if not _has_function(minter, "dregg_dev_mint(text, text[], text, interval)"):
            pytest.skip("installed pg_dregg predates dregg_dev_mint")
        if not _verify_key_is_test_root(minter):
            pytest.skip("cluster's dregg.issuer_pubkey is not the test root")
        return minter.dev_mint("agent", ["submit"], agent.hex(), ttl)


@pytest.mark.pg_integration
def test_live_durable_workflow_runs_and_completes(live_db):
    """A two-step durable workflow over REAL pg: enqueue two signed turns (durable
    rows), drive them to executed via the LocalDrainer (the node-drainer stand-in),
    and read the audit trail back. The enqueue + RLS + lifecycle are genuine; the
    drain transition is the stand-in (seam named)."""
    alice = bytes([0xA1] + [0] * 31)
    tok = _mint_submit_token(live_db, alice)
    with dpg.connect(live_db, token=tok, role="dregg_reader") as pg:
        drainer = wf.LocalDrainer(pg)
        w = (
            pg.durable_workflow("live-billing")
            .step("charge alice #1", alice, b"\xde\xad\xbe\xef")
            .step("charge alice #2", alice, b"\xfe\xed\xfa\xce")
        )
        report = pg.run_durable(w, drainer=drainer, await_timeout=10.0)
        assert report.all_ok, [(o.step.name, o.status, o.error) for o in report]
        assert report.committed == 2
        # Both rows are 'executed' in the real queue, with receipts.
        subs = {s.id: s for s in pg.outbox()}
        assert sum(1 for s in subs.values() if s.executed) == 2


@pytest.mark.pg_integration
def test_live_durable_workflow_enqueue_is_rls_gated(live_db):
    """A step whose agent the presented token does NOT authorize is refused at
    ENQUEUE by the real submit_gate RLS — the durable workflow cannot even stage a
    turn it has no capability for. (The capability-gated-write property, through
    the runner.)"""
    alice = bytes([0xA1] + [0] * 31)
    bob = bytes([0xB0] + [0] * 31)
    tok = _mint_submit_token(live_db, alice)  # ALICE-only submit token
    with dpg.connect(live_db, token=tok, role="dregg_reader") as pg:
        w = pg.durable_workflow("rls-billing").step("charge bob (unauthorized)", bob, b"\x01")
        with pytest.raises(dpg.DreggPgError) as exc:
            pg.run_durable(w, drainer=wf.LocalDrainer(pg), await_timeout=5.0)
        assert "Row-Level Security" in str(exc.value)


@pytest.mark.pg_integration
def test_live_durable_workflow_resume_is_exactly_once(live_db):
    """Crash-resume exactly-once against REAL rows: run a 2-step workflow but
    'crash' (don't drain) after enqueuing the first step's row, then RESUME the
    full workflow — the runner reconciles the persisted row and drives to
    completion WITHOUT double-enqueuing. The count of submit_queue rows for the
    workflow's first step stays at one across the crash."""
    alice = bytes([0xA1] + [0] * 31)
    bob = bytes([0xB0] + [0] * 31)
    # ALICE+BOB submit token: a single token admitting submit on BOTH cells (a
    # prefix that covers both). Use the empty prefix (all resources) for the demo.
    tok = _mint_submit_token(live_db, b"")  # empty prefix ⇒ submit on any cell
    # Use turn bytes UNIQUE to this test so row counts are isolated from the
    # other integration tests sharing the module-scoped scratch DB (the queue is
    # durable — prior tests' rows legitimately persist).
    alice_turn = b"\xaa\xaa" + uuid.uuid4().bytes
    bob_turn = b"\xbb\xbb" + uuid.uuid4().bytes

    def n_rows(pg, turn):
        return pg._rows(
            "SELECT count(*) FROM dregg.submit_queue WHERE signed_turn = %s", (turn,)
        )[0][0]

    with dpg.connect(live_db, token=tok, role="dregg_reader") as pg:
        # Phase 1: enqueue step 1 only, DON'T drain (simulate a crash post-enqueue).
        w1 = pg.durable_workflow("resume-billing").step("charge alice", alice, alice_turn)
        try:
            pg.run_durable(w1, await_timeout=0.4, poll_interval=0.05)  # no drainer ⇒ times out pending
        except wf.WorkflowError:
            pass
        # Exactly one pending row for alice's turn exists in the REAL queue.
        assert n_rows(pg, alice_turn) == 1
        assert n_rows(pg, bob_turn) == 0

        # Phase 2: resume the FULL workflow with a drainer. Step 1 (alice) must be
        # reconciled (awaited, then executed) WITHOUT a second enqueue; step 2
        # (bob) enqueued + driven. Net new rows for alice's turn = 0.
        drainer = wf.LocalDrainer(pg)
        wfull = (
            pg.durable_workflow("resume-billing")
            .step("charge alice", alice, alice_turn)
            .step("charge bob", bob, bob_turn)
        )
        report = pg.resume_durable(wfull, drainer=drainer, await_timeout=10.0)
        assert report.all_ok, [(o.step.name, o.status, o.error) for o in report]
        # Exactly-once: alice's turn still has ONE row (reconciled, not re-enqueued);
        # bob's turn now has one (newly enqueued + driven).
        assert n_rows(pg, alice_turn) == 1, "exactly-once: alice was reconciled, not re-enqueued"
        assert n_rows(pg, bob_turn) == 1
        # Both this workflow's turns are terminal-executed in the real queue.
        for turn in (alice_turn, bob_turn):
            st = pg._rows(
                "SELECT status FROM dregg.submit_queue WHERE signed_turn = %s", (turn,)
            )[0][0]
            assert st == "executed", f"turn {turn[:4].hex()} not executed: {st}"
