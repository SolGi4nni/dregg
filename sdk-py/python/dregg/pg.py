"""``dregg.pg`` — pg-dregg-native ergonomics for the Python SDK.

A thin, well-typed, ``psycopg``-based binding of the **real** pg-dregg SQL
surface (``pg-dregg/src/lib.rs`` + the ``dregg.*`` schema emitted by
``mirror::ddl::tier_b``). It binds what pg-dregg actually ships — it does not
invent a surface.

THE MODEL pg-dregg enforces (``docs/PG-DREGG.md`` §8, the spine):

    Reads are free SQL; state mutates ONLY through verified turns.

So this module's helpers fall into exactly that shape:

* **connect** — :func:`connect` opens a :class:`Pg`, a context-managed handle
  on a pg-dregg-enabled database. Presenting a capability token
  (:meth:`Pg.present_token`) sets the ``dregg.token`` session GUC and assumes
  the ``dregg_reader`` role, so Row-Level Security actually bites (a superuser
  BYPASSes RLS — see ``docs/QUICKSTART-pg-user.md`` §2).
* **submit a verified turn** — :meth:`Pg.submit_turn` enqueues a signed turn
  into ``dregg.submit_queue`` via the real ``dregg_submit_turn(signed_turn,
  agent)`` extern (RLS-gated by ``dregg_admits('submit', …)``); the node's
  §11.4 drainer applies it through the verified executor. **Postgres never
  executes** — the turn is an intent the node must accept.
* **read state as free SQL** — typed row projections over the shipped views:
  :meth:`Pg.cell_balances` (``dregg.cell_balances``), :meth:`Pg.receipt_chain`
  (``dregg.receipt_chain``), :meth:`Pg.cap_edges` (``dregg.cap_edges``).
* **federation health** — :meth:`Pg.federation_health` calls the real
  ``dregg_federation_health()`` (the conflict-counter-driven chain
  re-validation, ``docs/PG-DREGG.md`` §15).
* **dev-mint / issuer-status** — :meth:`Pg.dev_mint` (``dregg_dev_mint``, DEV
  ONLY, issuer-key discipline intact) and :meth:`Pg.issuer_status`
  (``dregg_issuer_status``).
* **outbox tail** — :meth:`Pg.outbox` reads ``dregg.submit_queue_audit`` (each
  submission's ``status`` walks ``pending → executed | refused``).

``psycopg`` (v3) is imported lazily, so ``import dregg`` never requires it and
the rest of the SDK loads with no database driver installed. Install the extra:
``pip install 'dregg[pg]'`` (or ``psycopg[binary]``).
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from datetime import datetime, timedelta
from types import TracebackType
from typing import TYPE_CHECKING, Any, Optional, Sequence, Union

if TYPE_CHECKING:  # pragma: no cover - typing only
    import psycopg

    from .pg_workflow import DurableWorkflow, RunReport

__all__ = [
    "DreggPgError",
    "Pg",
    "CellBalance",
    "ReceiptRow",
    "CapEdge",
    "Submission",
    "connect",
    "READER_ROLE",
    "KERNEL_ROLE",
    "TOKEN_GUC",
]

# A 32-byte identifier the SQL surface accepts as ``bytea``: a 64-char hex
# ``str`` or 32 raw ``bytes`` (the same ``Bytes32`` convention the native
# module uses).
Bytes32 = Union[str, bytes]

# ── the names baked into the pg-dregg DDL (mirror::ddl::tier_b) ──
#: The session GUC the ``dregg_admits`` policies read the presented token from.
TOKEN_GUC = "dregg.token"
#: The application role: ``SELECT`` only, RLS-gated. Bare connections become
#: this so the M1 capability policies filter (a superuser BYPASSes RLS).
READER_ROLE = "dregg_reader"
#: The verified writer (``BYPASSRLS``). Reading the outbox/audit as the kernel
#: sees every row; an application sees only its own submissions.
KERNEL_ROLE = "dregg_kernel"


# Base the pg error on the native ``DreggError`` when the compiled module is
# importable, so ``except dregg.DreggError`` also catches pg errors — but never
# hard-require it (the pg module stays usable with no native ``.so`` built). The
# base must be chosen AT class creation (a C-extension base cannot be swapped in
# via ``__bases__`` after the fact), hence this branch.
try:  # pragma: no cover - environment-dependent
    from .dregg import DreggError as _DreggErrorBase  # type: ignore
except Exception:  # pragma: no cover - the standalone path
    _DreggErrorBase = Exception  # type: ignore[assignment,misc]


class DreggPgError(_DreggErrorBase):  # type: ignore[valid-type,misc]
    """A pg-dregg SDK error (a bad connection, a missing extension surface, or
    an RLS refusal surfaced as a clear message). Subclasses the native
    ``dregg.DreggError`` when the compiled module is present, so a single
    ``except dregg.DreggError`` catches both."""


def _to_bytea(value: Bytes32, *, what: str = "identifier") -> bytes:
    """Coerce a 64-char hex ``str`` or 32 raw ``bytes`` to the ``bytes`` psycopg
    binds as ``bytea``. Raises :class:`ValueError` on a bad shape — fail loud,
    never silently truncate."""
    if isinstance(value, bytes):
        return value
    if isinstance(value, str):
        s = value[2:] if value.startswith(("\\x", "0x")) else value
        try:
            return bytes.fromhex(s)
        except ValueError as exc:
            raise ValueError(f"{what} hex is not valid: {value!r}") from exc
    raise TypeError(f"{what} must be 64-char hex str or 32 bytes, got {type(value).__name__}")


# ───────────────────────── typed row projections ─────────────────────────
# Each mirrors one shipped view's column shape exactly (the names are pinned by
# ``pg-dregg/sql/schema-tierB.sql`` and the ``emitted_ddl_agrees_with_committed_sql_file``
# test). The views are hex-keyed already; the SQL the helpers build names the
# columns explicitly so a view-shape drift is a loud failure, not a silent one.


@dataclass(frozen=True)
class CellBalance:
    """A row of ``dregg.cell_balances`` — the "show me the money" view, hex-keyed
    and balance-first (``SELECT cell, balance, nonce, lifecycle, last_ordinal``)."""

    cell: str  # encode(cell_id, 'hex')
    balance: int
    nonce: int
    lifecycle: str
    last_ordinal: int


@dataclass(frozen=True)
class ReceiptRow:
    """A row of ``dregg.receipt_chain`` — the turn hash chain a light client
    walks (each row's ``prev_root`` equals the prior row's ``ledger_root`` — the
    ``RootChain`` anti-substitution tooth, surfaced as SQL)."""

    ordinal: int
    height: int
    creator: str  # encode(creator, 'hex')
    prev_root: str  # encode(prev_root, 'hex')
    ledger_root: str  # encode(ledger_root, 'hex')
    committed_at: Optional[datetime]


@dataclass(frozen=True)
class CapEdge:
    """A row of ``dregg.cap_edges`` — the delegation graph (``src → dst``). A
    ``WITH RECURSIVE`` walk over it is the no-amplification audit surface (a
    child's ``allowed_effects`` ⊆ its grantor's)."""

    src: str  # encode(holder, 'hex')
    dst: str  # encode(target, 'hex')
    slot: int
    permissions: Any  # jsonb (decoded by psycopg)
    expires_at: Optional[int]


@dataclass(frozen=True)
class Submission:
    """A row of ``dregg.submit_queue_audit`` — a submitted turn and its outcome.
    ``status`` walks ``pending → executed | refused`` as the node drains the
    queue; ``receipt_hash`` / ``error`` carry the result back (§11.4)."""

    id: Any  # uuid (uuidv7 on pg18 — temporally sortable)
    agent: str  # encode(agent, 'hex')
    submitter: str
    status: str
    receipt_hash: Optional[str]
    error: Optional[str]
    submitted_at: Optional[datetime]
    resolved_at: Optional[datetime]
    # pg18-only audit columns (present iff the view ships them; None on pg17).
    id_version: Optional[int] = None
    enqueued_at: Optional[datetime] = None
    queue_latency: Optional[timedelta] = None

    @property
    def pending(self) -> bool:
        return self.status == "pending"

    @property
    def executed(self) -> bool:
        return self.status == "executed"

    @property
    def refused(self) -> bool:
        return self.status == "refused"


# ──────────────────────────── the connection ─────────────────────────────


def connect(
    conninfo: Optional[str] = None,
    *,
    token: Optional[str] = None,
    role: Optional[str] = READER_ROLE,
    autocommit: bool = True,
    **kwargs: Any,
) -> "Pg":
    """Open a :class:`Pg` handle on a pg-dregg-enabled database.

    :param conninfo: a libpq conninfo string / URL. Defaults to ``$DREGG_PG_DSN``
        then ``$DATABASE_URL``; if neither is set, psycopg's own environment
        (``PGHOST``/``PGPORT``/``PGDATABASE``/…) applies.
    :param token: a ``dga1_…`` capability token to present immediately (sets the
        ``dregg.token`` GUC for the session). May be presented later with
        :meth:`Pg.present_token`.
    :param role: the role to assume after connecting so RLS bites — defaults to
        ``dregg_reader``. Pass ``None`` to stay the connecting role (e.g. when
        connecting AS ``dregg_kernel`` to drain the outbox, or as a superuser for
        admin). A superuser BYPASSes RLS regardless.
    :param autocommit: psycopg autocommit (default ``True`` — each statement is
        its own transaction, matching the "instant revocation between statements"
        semantics; set ``False`` to manage transactions yourself).
    :param kwargs: forwarded to ``psycopg.connect`` (e.g. ``connect_timeout``).
    """
    psycopg = _import_psycopg()
    dsn = conninfo or os.environ.get("DREGG_PG_DSN") or os.environ.get("DATABASE_URL")
    # psycopg.connect("") uses the libpq environment; an explicit None is not
    # accepted, so pass an empty string when nothing is configured.
    conn = psycopg.connect(dsn if dsn is not None else "", autocommit=autocommit, **kwargs)
    pg = Pg(conn)
    if role is not None:
        pg.set_role(role)
    if token is not None:
        pg.present_token(token)
    return pg


def _import_psycopg() -> "psycopg":
    try:
        import psycopg  # noqa: F401

        return psycopg
    except ModuleNotFoundError as exc:  # pragma: no cover - import-guard
        raise DreggPgError(
            "dregg.pg needs psycopg (v3). Install it with "
            "`pip install 'dregg[pg]'` or `pip install 'psycopg[binary]'`."
        ) from exc


class Pg:
    """A context-managed handle on a pg-dregg database.

    Wraps a ``psycopg.Connection``. The free-SQL read helpers build parameterized
    queries over the shipped ``dregg.*`` views; the write/admin helpers call the
    real ``#[pg_extern]`` functions. Use as a context manager so the connection
    (and any presented token, if session-local) is released on exit::

        with dregg.pg.connect("host=/var/run/postgresql dbname=dregg") as pg:
            pg.present_token(tok)
            for c in pg.cell_balances():
                print(c.cell, c.balance)
    """

    def __init__(self, conn: "psycopg.Connection") -> None:
        self._conn = conn

    # ── lifecycle ──
    @property
    def connection(self) -> "psycopg.Connection":
        """The underlying ``psycopg.Connection`` (escape hatch for raw SQL)."""
        return self._conn

    def close(self) -> None:
        self._conn.close()

    def __enter__(self) -> "Pg":
        return self

    def __exit__(
        self,
        exc_type: Optional[type[BaseException]],
        exc: Optional[BaseException],
        tb: Optional[TracebackType],
    ) -> None:
        self.close()

    # ── small SQL helpers (parameterized, fail-closed on errors) ──
    def _scalar(self, sql: str, params: Sequence[Any] = ()) -> Any:
        with self._conn.cursor() as cur:
            cur.execute(sql, params)  # type: ignore[arg-type]
            row = cur.fetchone()
            return None if row is None else row[0]

    def _rows(self, sql: str, params: Sequence[Any] = ()) -> list[tuple]:
        with self._conn.cursor() as cur:
            cur.execute(sql, params)  # type: ignore[arg-type]
            return cur.fetchall()

    # ── presenting authority (the capability the rows are gated by) ──
    def present_token(self, token: str, *, local: bool = False) -> None:
        """Present a ``dga1_…`` capability token for the session by setting the
        ``dregg.token`` GUC (``set_config('dregg.token', token, local)``). The
        ``dregg_admits`` RLS policies read it. With ``local=True`` it is
        transaction-local (clears at commit) — prefer that on a pooled
        connection. Remember a superuser BYPASSes RLS; assume ``dregg_reader``
        (the default in :func:`connect`) so the policy fires."""
        self._scalar("SELECT set_config(%s, %s, %s)", (TOKEN_GUC, token, local))

    def clear_token(self, *, local: bool = False) -> None:
        """Clear the presented token (present the empty string ⇒ deny-by-default)."""
        self._scalar("SELECT set_config(%s, %s, %s)", (TOKEN_GUC, "", local))

    def current_token(self) -> Optional[str]:
        """The token currently presented (``current_setting('dregg.token', true)``),
        or ``None`` if none is set."""
        tok = self._scalar("SELECT current_setting(%s, true)", (TOKEN_GUC,))
        return tok or None

    def set_role(self, role: str) -> None:
        """``SET ROLE`` — assume ``role`` so RLS is enforced as that role
        (``dregg_reader`` for applications). Identifier-validated then quoted."""
        self._scalar("SELECT set_config('role', %s, false)", (_validate_ident(role),))

    def reset_role(self) -> None:
        self._scalar("RESET ROLE")

    # ── free-SQL reads (typed projections of the shipped views) ──
    def cell_balances(
        self,
        *,
        order_by_balance: bool = True,
        limit: Optional[int] = None,
    ) -> list[CellBalance]:
        """``dregg.cell_balances`` — the ledger, hex-keyed and balance-first. Only
        the cells the presented token admits ``read`` on are returned (read-side
        RLS). ``order_by_balance`` sorts richest-first (default)."""
        sql = (
            "SELECT cell, balance, nonce, lifecycle, last_ordinal "
            "FROM dregg.cell_balances"
        )
        if order_by_balance:
            sql += " ORDER BY balance DESC"
        if limit is not None:
            sql += " LIMIT %s"
            rows = self._rows(sql, (int(limit),))
        else:
            rows = self._rows(sql)
        return [CellBalance(*r) for r in rows]

    def cell_balance(self, cell: Bytes32) -> Optional[CellBalance]:
        """One cell's row from ``dregg.cell_balances`` by id, or ``None`` if it is
        absent / not admitted by the presented token."""
        cell_hex = _to_bytea(cell, what="cell id").hex()
        rows = self._rows(
            "SELECT cell, balance, nonce, lifecycle, last_ordinal "
            "FROM dregg.cell_balances WHERE cell = %s",
            (cell_hex,),
        )
        return CellBalance(*rows[0]) if rows else None

    def receipt_chain(self, *, limit: Optional[int] = None) -> list[ReceiptRow]:
        """``dregg.receipt_chain`` — the turn hash chain in ordinal order. Walk it
        to verify non-omission: each row's ``prev_root`` is the prior row's
        ``ledger_root``. RLS-gated (the turns of agents you may ``read``)."""
        sql = (
            "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at "
            "FROM dregg.receipt_chain ORDER BY ordinal"
        )
        if limit is not None:
            sql += " LIMIT %s"
            rows = self._rows(sql, (int(limit),))
        else:
            rows = self._rows(sql)
        return [ReceiptRow(*r) for r in rows]

    def chain_head(self) -> Optional[ReceiptRow]:
        """The latest turn in ``dregg.receipt_chain`` (the chain head), or ``None``
        on a genesis (empty) ledger."""
        rows = self._rows(
            "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at "
            "FROM dregg.receipt_chain ORDER BY ordinal DESC LIMIT 1"
        )
        return ReceiptRow(*rows[0]) if rows else None

    def cap_edges(self, *, src: Optional[Bytes32] = None) -> list[CapEdge]:
        """``dregg.cap_edges`` — the delegation graph. With ``src`` given, only the
        edges out of that holder cell. RLS-gated (edges held by cells you may
        ``read``)."""
        if src is not None:
            src_hex = _to_bytea(src, what="src cell").hex()
            rows = self._rows(
                "SELECT src, dst, slot, permissions, expires_at "
                "FROM dregg.cap_edges WHERE src = %s",
                (src_hex,),
            )
        else:
            rows = self._rows(
                "SELECT src, dst, slot, permissions, expires_at FROM dregg.cap_edges"
            )
        return [CapEdge(*r) for r in rows]

    def conservation_total(self) -> int:
        """``SELECT sum(balance) FROM dregg.cells`` — value conserved across the
        ledger (over the cells the presented token admits). Returns ``0`` on an
        empty ledger."""
        total = self._scalar("SELECT coalesce(sum(balance), 0) FROM dregg.cells")
        return int(total)

    # ── the write path: submit a verified turn (the node drains it) ──
    def submit_turn(self, signed_turn: bytes, agent: Bytes32) -> Any:
        """Submit a SIGNED turn FROM postgres via ``dregg_submit_turn(signed_turn,
        agent)`` (``docs/PG-DREGG.md`` §11). ``signed_turn`` is the postcard
        ``SignedTurn`` bytes; ``agent`` is the turn's agent cell id.

        Enqueues the turn into ``dregg.submit_queue`` and returns the submission
        ``uuid``. The enqueue is RLS-gated by ``dregg_admits('submit',
        encode(agent,'hex'))`` — a role submits only the turns its presented
        capability authorizes; otherwise Row-Level Security refuses the INSERT
        (raises :class:`DreggPgError`). **Postgres never executes** — the node's
        §11.4 drainer applies the turn through the verified executor; poll
        :meth:`outbox` / :meth:`submission` for the outcome (``status`` walks
        ``pending → executed | refused``).

        Note: ``dregg_submit_turn`` is NOT ``SECURITY DEFINER`` — it runs as the
        calling role so the ``WITH CHECK`` policy bites. Present a ``submit``
        token and assume ``dregg_reader`` first."""
        if not isinstance(signed_turn, (bytes, bytearray)):
            raise TypeError("signed_turn must be the postcard SignedTurn bytes")
        agent_b = _to_bytea(agent, what="agent cell")
        try:
            return self._scalar(
                "SELECT dregg_submit_turn(%s, %s)", (bytes(signed_turn), agent_b)
            )
        except Exception as exc:  # surface an RLS refusal as a clear dregg error
            raise _wrap_pg_error(exc, "dregg_submit_turn (enqueue)") from exc

    def enqueue_turn(self, signed_turn: bytes, agent: Bytes32) -> Any:
        """Enqueue a signed turn by a direct ``INSERT INTO dregg.submit_queue``
        (the explicit form ``dregg_submit_turn`` wraps). Same RLS gate
        (``submit_gate``), returns the generated id. Prefer :meth:`submit_turn`;
        this exists for callers that want the raw INSERT path."""
        agent_b = _to_bytea(agent, what="agent cell")
        if not isinstance(signed_turn, (bytes, bytearray)):
            raise TypeError("signed_turn must be the postcard SignedTurn bytes")
        try:
            return self._scalar(
                "INSERT INTO dregg.submit_queue (agent, signed_turn) "
                "VALUES (%s, %s) RETURNING id",
                (agent_b, bytes(signed_turn)),
            )
        except Exception as exc:
            raise _wrap_pg_error(exc, "submit_queue INSERT") from exc

    # ── the outbox tail (each submission + its drain outcome) ──
    def outbox(self, *, limit: Optional[int] = None) -> list[Submission]:
        """Tail the submit-queue audit surface — every submission you may see and
        its outcome, ordered by ``id`` (= arrival order on pg18, where the key is a
        ``uuidv7``). RLS-gated by the same ``submit`` admission, so a submitter
        sees its own turns' statuses.

        Prefers ``dregg.submit_queue_audit`` (the pg18 view, which recovers the
        enqueue time + version FROM the ``uuidv7`` key into ``id_version`` /
        ``enqueued_at`` / ``queue_latency``); falls back to the base
        ``dregg.submit_queue`` table where the view is absent (older / pg17
        installs, whose ``uuid_extract_*`` are unavailable), leaving those audit
        columns ``None``."""
        relation, cols, has_v7 = self._outbox_relation()
        sql = f"SELECT {cols} FROM {relation} ORDER BY id"
        if limit is not None:
            sql += " LIMIT %s"
            rows = self._rows(sql, (int(limit),))
        else:
            rows = self._rows(sql)
        return [self._submission(r, has_v7) for r in rows]

    def submission(self, submission_id: Any) -> Optional[Submission]:
        """One submission by id from the audit surface (poll it after
        :meth:`submit_turn`), or ``None`` if absent / not admitted."""
        relation, cols, has_v7 = self._outbox_relation()
        rows = self._rows(
            f"SELECT {cols} FROM {relation} WHERE id = %s",
            (submission_id,),
        )
        return self._submission(rows[0], has_v7) if rows else None

    def _outbox_relation(self) -> tuple[str, str, bool]:
        """Pick the outbox read source + its column list. The pg18 audit VIEW is
        preferred (it carries the ``uuidv7``-derived audit columns); the base
        TABLE is the fallback. Cached on the connection (the schema does not change
        under us). Returns ``(relation, column_list, has_v7_columns)``."""
        cached = getattr(self, "_outbox_rel_cache", None)
        if cached is not None:
            return cached
        base_cols = "id, agent, submitter, status, receipt_hash, error, submitted_at, resolved_at"
        view_present = self._scalar(
            "SELECT to_regclass('dregg.submit_queue_audit') IS NOT NULL"
        )
        if view_present:
            relation = "dregg.submit_queue_audit"
            # The view already renders agent as hex; check the v7 columns.
            has_v7 = bool(self._scalar(
                "SELECT count(*) FROM information_schema.columns "
                "WHERE table_schema='dregg' AND table_name='submit_queue_audit' "
                "AND column_name='id_version'"
            ))
            cols = base_cols + (", id_version, enqueued_at, queue_latency" if has_v7 else "")
        else:
            # Fall back to the base table: agent is bytea, so render it as hex to
            # match the Submission shape; no v7 audit columns.
            relation = "dregg.submit_queue"
            cols = (
                "id, encode(agent,'hex') AS agent, submitter, status, "
                "encode(receipt_hash,'hex') AS receipt_hash, error, "
                "submitted_at, resolved_at"
            )
            has_v7 = False
        result = (relation, cols, has_v7)
        self._outbox_rel_cache = result  # type: ignore[attr-defined]
        return result

    @staticmethod
    def _submission(row: tuple, has_v7: bool) -> Submission:
        (sid, agent, submitter, status, receipt_hash, error, submitted_at, resolved_at) = row[:8]
        kw: dict[str, Any] = {}
        if has_v7 and len(row) >= 11:
            kw = {
                "id_version": row[8],
                "enqueued_at": row[9],
                "queue_latency": row[10],
            }
        return Submission(
            id=sid,
            agent=agent,
            submitter=submitter,
            status=status,
            receipt_hash=receipt_hash,
            error=error,
            submitted_at=submitted_at,
            resolved_at=resolved_at,
            **kw,
        )

    # ── federation health ──
    def federation_health(self) -> str:
        """``dregg_federation_health()`` — the subscriber-side federation health
        check (``docs/PG-DREGG.md`` §15): the pg18 apply-conflict counters DRIVE
        the chain re-validation. Returns the one-line verdict, one of
        ``'ok: federation healthy — …'`` / ``'ALARM (…) but chain re-validates: …'``
        / ``'CRITICAL (…) AND chain REFUSED: …'``."""
        return self._scalar("SELECT dregg_federation_health()")

    def federation_health_ok(self) -> bool:
        """``True`` iff :meth:`federation_health` reports the healthy verdict (no
        apply conflicts). A convenience over the text for alerting."""
        return self.federation_health().startswith("ok:")

    def revalidate_replicated_chain(self) -> str:
        """``dregg_revalidate_replicated_chain()`` — the subscriber re-validation
        sweep over the replicated ``dregg.turns`` (the anti-substitution tooth,
        run locally). ``'ok: N turns re-validated, head=…'`` or
        ``'REFUSED: …'``."""
        return self._scalar("SELECT dregg_revalidate_replicated_chain()")

    # ── issuer status + dev mint ──
    def issuer_status(self) -> str:
        """``dregg_issuer_status()`` — the database's dregg key configuration in
        one line, so the silent fail-closed mode ("no issuer key ⇒ everything
        denies") is discoverable. Run it first when "all my rows vanished". The
        private key is never reported."""
        return self._scalar("SELECT dregg_issuer_status()")

    def dev_mint(
        self,
        subject: str,
        actions: Sequence[str],
        resource_prefix: str,
        ttl: Union[timedelta, str],
    ) -> str:
        """``dregg_dev_mint(subject, actions[], resource_prefix, ttl interval)`` —
        **DEV ONLY.** Compose the common capability shape (``action ∈ actions``
        confined to ``resource_prefix``, expiring ``ttl`` from now, naming
        ``subject``) and mint a ``dga1_…`` token, so a newcomer never hand-writes
        ``Pred`` JSON.

        Issuer-key discipline is intact: it routes through the same mint path as
        ``dregg_mint`` and RAISES (no silent token) if ``dregg.issuer_privkey`` is
        not configured — the production posture (mint out-of-database, the private
        key never in pg) is unchanged. ``ttl`` is a :class:`datetime.timedelta` or
        a postgres interval literal (e.g. ``'1 hour'``). Empty ``actions`` mints a
        deliberately-useless token (admits nothing)."""
        acts = list(actions)
        ttl_param: Any
        if isinstance(ttl, timedelta):
            ttl_param = ttl
        else:
            # An interval LITERAL like '1 hour' — cast in SQL so the driver does
            # not have to round-trip a string as ``interval``.
            return self._dev_mint_with_literal_ttl(subject, acts, resource_prefix, str(ttl))
        try:
            return self._scalar(
                "SELECT dregg_dev_mint(%s, %s, %s, %s)",
                (subject, acts, resource_prefix, ttl_param),
            )
        except Exception as exc:
            raise _wrap_pg_error(exc, "dregg_dev_mint") from exc

    def _dev_mint_with_literal_ttl(
        self, subject: str, actions: list[str], resource_prefix: str, ttl_literal: str
    ) -> str:
        try:
            return self._scalar(
                "SELECT dregg_dev_mint(%s, %s, %s, %s::interval)",
                (subject, actions, resource_prefix, ttl_literal),
            )
        except Exception as exc:
            raise _wrap_pg_error(exc, "dregg_dev_mint") from exc

    # ── direct capability decisions (the M1 functions, offline-verified) ──
    def cap_admits(self, token: str, action: str, resource: str, now: Optional[int] = None) -> bool:
        """``dregg_cap_admits(token, action, resource, now)`` — TRUE iff the
        credential admits ``action`` on ``resource`` at ``now`` (unix seconds;
        defaults to the database clock). Verified offline against the issuer key,
        not revoked. Fail-closed."""
        if now is None:
            now = int(self._scalar("SELECT extract(epoch from now())::bigint"))
        return bool(self._scalar(
            "SELECT dregg_cap_admits(%s, %s, %s, %s)", (token, action, resource, int(now))
        ))

    def cap_explain(self, token: str, action: str, resource: str, now: Optional[int] = None) -> Optional[str]:
        """``dregg_cap_explain(...)`` — the human-readable decision reason
        (``'allowed'`` or the first violated requirement / ``'revoked'`` / ``'no
        issuer key configured'``). For debugging why a row was filtered."""
        if now is None:
            now = int(self._scalar("SELECT extract(epoch from now())::bigint"))
        return self._scalar(
            "SELECT dregg_cap_explain(%s, %s, %s, %s)", (token, action, resource, int(now))
        )

    def cap_subject(self, token: str) -> Optional[str]:
        """``dregg_cap_subject(token)`` — the confined subject the token names, or
        ``None`` if its chain does not verify under the issuer key."""
        return self._scalar("SELECT dregg_cap_subject(%s)", (token,))

    def cap_id(self, token: str) -> Optional[str]:
        """``dregg_cap_id(token)`` — the stable per-credential id the revocation
        registry keys on, or ``None`` if the token does not decode."""
        return self._scalar("SELECT dregg_cap_id(%s)", (token,))

    def revoke(self, token: str) -> Optional[str]:
        """``dregg_revoke(token)`` — revoke the presented credential; returns the
        revoked id (denied on the very next row-check), or ``None`` if it does not
        decode."""
        try:
            return self._scalar("SELECT dregg_revoke(%s)", (token,))
        except Exception as exc:
            raise _wrap_pg_error(exc, "dregg_revoke") from exc

    def unrevoke(self, cap_id: str) -> bool:
        """``dregg_unrevoke(id)`` — lift a revocation by id."""
        try:
            return bool(self._scalar("SELECT dregg_unrevoke(%s)", (cap_id,)))
        except Exception as exc:
            raise _wrap_pg_error(exc, "dregg_unrevoke") from exc

    # ── one-call schema install (the dregg-developer entry points) ──
    def install_schema(self) -> str:
        """``dregg_install_schema()`` — install the Tier-B store (tables + the
        query-surface views + read-side RLS + the write-lockdown role model).
        Idempotent. Run by a DBA/migration role, not an application role."""
        try:
            return self._scalar("SELECT dregg_install_schema()")
        except Exception as exc:
            raise _wrap_pg_error(exc, "dregg_install_schema") from exc

    def install_write_outbox(self) -> str:
        """``dregg_install_write_outbox()`` — install the write-path outbox
        (``dregg.submit_queue`` + the ``submit_gate`` RLS). Requires
        :meth:`install_schema` first. Idempotent."""
        try:
            return self._scalar("SELECT dregg_install_write_outbox()")
        except Exception as exc:
            raise _wrap_pg_error(exc, "dregg_install_write_outbox") from exc

    # ── durable verified workflows (each step a verified turn, exactly-once) ──
    def durable_workflow(
        self, name: str, *, workflow_id: Optional[str] = None
    ) -> "DurableWorkflow":
        """Open a :class:`~dregg.pg_workflow.DurableWorkflow` — an ordered, named
        sequence of verified turns driven durably through this pg-dregg
        connection. Each step is a signed turn enqueued into ``dregg.submit_queue``
        (RLS-gated), applied by the node drainer through the verified executor,
        and the runner drives it to a terminal outcome with **exactly-once across
        crashes** (resume reconciles against the persisted audit rows). The Python
        face of ``pg_dregg::workflow`` — see ``examples/pg_durable_workflow.py``.

            wf = pg.durable_workflow("monthly-billing")
            wf.step("charge alice", alice_cell, alice_turn_bytes)
            report = wf.run(pg)          # or wf.resume(pg) after a crash
        """
        from .pg_workflow import DurableWorkflow

        return DurableWorkflow(name, workflow_id=workflow_id)

    def run_durable(self, workflow: "DurableWorkflow", **kwargs: Any) -> "RunReport":
        """Run a :class:`~dregg.pg_workflow.DurableWorkflow` from the start against
        this connection (a fresh run). Convenience for ``workflow.run(self,
        **kwargs)``."""
        return workflow.run(self, **kwargs)

    def resume_durable(self, workflow: "DurableWorkflow", **kwargs: Any) -> "RunReport":
        """Resume a :class:`~dregg.pg_workflow.DurableWorkflow` after a crash —
        reconcile against what already committed and re-drive only the uncommitted
        tail (exactly-once). Convenience for ``workflow.resume(self, **kwargs)``."""
        return workflow.resume(self, **kwargs)

    def __repr__(self) -> str:  # pragma: no cover - cosmetic
        info = getattr(self._conn, "info", None)
        target = ""
        if info is not None:
            try:
                target = f" dbname={info.dbname}"
            except Exception:
                target = ""
        return f"<dregg.pg.Pg{target}>"


# ───────────────────────────── small helpers ─────────────────────────────


def _validate_ident(ident: str) -> str:
    """Validate a SQL identifier (a role name) — ``[A-Za-z_][A-Za-z0-9_]*`` and
    short. ``SET ROLE`` cannot be parameterized, so we whitelist the shape rather
    than interpolate arbitrary text. Raises :class:`ValueError` otherwise."""
    if not ident or len(ident) > 63:
        raise ValueError(f"invalid role identifier: {ident!r}")
    if not (ident[0].isalpha() or ident[0] == "_"):
        raise ValueError(f"invalid role identifier (bad first char): {ident!r}")
    if not all(c.isalnum() or c == "_" for c in ident):
        raise ValueError(f"invalid role identifier (bad char): {ident!r}")
    return ident


def _wrap_pg_error(exc: Exception, what: str) -> DreggPgError:
    """Turn a psycopg error into a :class:`DreggPgError` with a clear message.
    An RLS refusal (``new row violates row-level security policy``) is the most
    important one to surface legibly — it means "your capability does not
    authorize this", not a bug."""
    msg = str(exc).strip()
    lower = msg.lower()
    if "row-level security" in lower or "violates row-level security" in lower:
        return DreggPgError(
            f"{what}: refused by Row-Level Security — your presented capability "
            f"does not authorize it (the submit_gate / read policy denied the "
            f"operation). Present a token that admits it, and assume the "
            f"dregg_reader role. [{msg}]"
        )
    if "does not exist" in lower and ("function" in lower or "dregg" in lower):
        return DreggPgError(
            f"{what}: the pg-dregg surface is not installed in this database "
            f"(CREATE EXTENSION pg_dregg; SELECT dregg_install_schema();). [{msg}]"
        )
    return DreggPgError(f"{what}: {msg}")


# ─────────── re-export the durable-workflow surface under dregg.pg ───────────
# So a user reaches the whole pg-dregg-native surface from one import:
#   from dregg import pg
#   wf = pg.DurableWorkflow("billing"); wf.step(...); wf.run(conn)
# The module is imported at the bottom (after Pg is defined) to avoid a cycle —
# pg_workflow imports Pg only under TYPE_CHECKING.
from .pg_workflow import (  # noqa: E402
    DurableWorkflow,
    LocalDrainer,
    RunReport,
    StepOutcome,
    StepRefused,
    StepStatus,
    WorkflowError,
    WorkflowStep,
)

__all__ += [
    "DurableWorkflow",
    "WorkflowStep",
    "StepStatus",
    "StepOutcome",
    "RunReport",
    "WorkflowError",
    "StepRefused",
    "LocalDrainer",
]
