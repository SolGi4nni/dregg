"""``dregg.pg.workflow`` — durable verified workflows over pg-dregg.

A **durable workflow** is an ordered, named sequence of verified turns driven
through the pg-dregg write spine (``docs/PG-DREGG.md`` §8/§11): each step is a
signed turn enqueued into ``dregg.submit_queue`` (RLS-gated by
``dregg_admits('submit', agent)``), which the node's drainer applies through the
real verified executor (``pending → executed | refused``). The runner here is the
Python face of the shipped ``pg_dregg::workflow`` API (``Workflow`` / ``Step`` /
``WorkflowEngine`` / ``run_durable`` / ``resume_durable`` / ``recover_from_durable``
— ``pg-dregg/examples/subscription_billing.rs`` is its behavioral reference), but
realized over the **live, persisted** submit-queue rows rather than the Rust
engine's in-memory ``MemLog``. That distinction is the whole point of *durable*:
the durability that survives a crash lives in the committed
``dregg.submit_queue`` rows, which only the SQL path reaches.

THE THREE PROPERTIES the runner gives a Python user (the lane's deliverable):

* **(a) a durable verified workflow** — :meth:`DurableWorkflow.run` enqueues each
  step's signed turn and drives it to a terminal outcome. The enqueue is a
  committed pg row (durable the instant ``dregg_submit_turn`` returns), so a
  process crash mid-run loses the in-memory runner but **not** the enqueued
  turns.
* **exactly-once across crashes** — :meth:`DurableWorkflow.resume` reconciles the
  workflow against what is ALREADY in ``dregg.submit_queue_audit``: a step whose
  turn already enqueued/executed is **skipped, never re-submitted** (the fast
  path), and even if a stale step *were* re-submitted, the node's chain tooth
  refuses it as a replay (the backstop). This is the same dual enforcement the
  Rust ``resume_durable`` documents ("we skip by index … the chain is the
  backstop"), keyed here by a per-step **idempotency key** the runner stamps so a
  resumed run recognizes its own already-committed steps.
* it composes with **(b) cap-gated reads** and **(c) verified writes** from
  :mod:`dregg.pg` unchanged — a workflow reads state back as free SQL
  (:meth:`dregg.pg.Pg.cell_balances`) and every write IS a verified turn.

THE HONEST SEAM (named, per ``docs/PG-DREGG.md`` §11.4 / §13). The
soundness-load-bearing halves — the durable enqueue, the ``submit_gate`` RLS, and
the audit-reconciliation that makes resume exactly-once — are **real and enforced
by the database engine** and are exercised against live pg18. The transition that
*executes* a queued turn (``pending → executed``, writing the receipt) is the
**node drainer's** job (M3: ``node/src/pg_submit_drainer.rs`` →
``execute_via_producer`` → the real Lean executor). Where no live node/drainer is
running, :class:`LocalDrainer` stands in for it for dev + tests — it is a
deliberately-minimal ``dregg_kernel``-role applicator that marks a row executed,
NOT the verified executor, and it says so. A production deployment runs the real
drainer and never touches :class:`LocalDrainer`.
"""

from __future__ import annotations

import time
import uuid
from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING, Any, Callable, Iterable, Optional, Sequence

if TYPE_CHECKING:  # pragma: no cover - typing only
    from .pg import Pg, Submission

__all__ = [
    "StepStatus",
    "WorkflowStep",
    "DurableWorkflow",
    "StepOutcome",
    "RunReport",
    "WorkflowError",
    "StepRefused",
    "LocalDrainer",
]


# The GUC key (a namespaced custom setting, no pre-registration needed) the
# runner stamps each step's idempotency key into, so the node-side drainer (or
# the LocalDrainer) and a resumed run can both read it off the enqueued row's
# ``submit_token`` is NOT it — that is the bearer cap; the idempotency key rides
# in the turn bytes' framing instead (see WorkflowStep.idempotency_key). We keep
# the key client-side and reconcile via the audit view, because the live
# ``dregg.submit_queue`` carries no dedup column (by design — idempotency is the
# chain tooth's job; the runner's resume is the fast path over it).


class StepStatus(str, Enum):
    """Where a step is in the ``pending → executed | refused`` lifecycle, plus
    the client-side ``skipped`` (a resume recognized it as already-committed) and
    ``unsubmitted`` (not yet enqueued)."""

    UNSUBMITTED = "unsubmitted"
    PENDING = "pending"
    EXECUTED = "executed"
    REFUSED = "refused"
    SKIPPED = "skipped"

    @property
    def terminal(self) -> bool:
        """``True`` once the step will not change again (``executed`` / ``refused``
        / ``skipped``)."""
        return self in (StepStatus.EXECUTED, StepStatus.REFUSED, StepStatus.SKIPPED)

    @property
    def ok(self) -> bool:
        """``True`` iff the step reached state (``executed`` or, on resume,
        recognized as an already-committed ``skipped``)."""
        return self in (StepStatus.EXECUTED, StepStatus.SKIPPED)


# A 32-byte cell id: a 64-char hex ``str`` or 32 raw ``bytes`` (the same
# convention :mod:`dregg.pg` uses).
Bytes32 = Any


@dataclass(frozen=True)
class WorkflowStep:
    """One step of a durable workflow — the declarative description of ONE
    verified turn, the Python face of ``pg_dregg::workflow::Step``.

    A step states *who acts* (:attr:`agent`, the cell whose capability the turn's
    ``submit`` is gated on — what the ``submit_gate`` RLS checks and what the turn
    records as ``creator``) and *the signed turn bytes* (:attr:`signed_turn`, the
    postcard ``SignedTurn`` the node drainer executes). It carries an
    :attr:`idempotency_key` — a stable, deterministic id for THIS logical step in
    THIS workflow — so a resumed run can recognize the step's already-committed
    submission in the audit view and skip it (exactly-once's fast path).

    The runner does not interpret :attr:`signed_turn`; it is opaque bytes the
    drainer decodes. Build it with the native ``Identity.turn(...).…​.sign()`` (a
    real ``SignedTurn``) or, for a flow whose turns the node synthesizes, any
    agreed encoding the drainer understands.
    """

    name: str
    agent: Bytes32
    signed_turn: bytes
    #: A stable id for this logical step in this workflow run. Defaults (via
    #: :meth:`DurableWorkflow.step`) to ``f"{workflow_id}:{index}:{name}"`` —
    #: deterministic, so re-running the SAME workflow produces the SAME keys and a
    #: resume reconciles. Override to pin idempotency to a domain id (an invoice
    #: number, a billing-cycle tag) so the same business action is never charged
    #: twice even across distinct runner invocations.
    idempotency_key: str = ""

    def __post_init__(self) -> None:
        if not isinstance(self.signed_turn, (bytes, bytearray)):
            raise TypeError(
                f"step {self.name!r}: signed_turn must be the postcard SignedTurn "
                f"bytes, got {type(self.signed_turn).__name__}"
            )

    @property
    def agent_hex(self) -> str:
        """The acting agent's cell id as a canonical 64-char hex ``str``,
        regardless of whether :attr:`agent` was given as hex or raw bytes. The
        stable key a refusal predicate / reconciliation should compare on (so a
        consumer never has to guess the bytes-vs-hex shape)."""
        return _agent_hex(self.agent)


@dataclass
class StepOutcome:
    """The result of driving one :class:`WorkflowStep` — its terminal
    :class:`StepStatus`, the submission id (a ``uuid``), and the receipt hash (on
    ``executed``) or error (on ``refused``)."""

    step: WorkflowStep
    status: StepStatus
    submission_id: Optional[Any] = None
    receipt_hash: Optional[str] = None
    error: Optional[str] = None

    @property
    def ok(self) -> bool:
        return self.status.ok


@dataclass
class RunReport:
    """The outcome of a whole :meth:`DurableWorkflow.run` / :meth:`resume`.

    Mirrors ``pg_dregg::workflow::RunOutcome`` (``committed`` / ``skipped`` /
    ``head``) and adds the per-step :class:`StepOutcome` trail. ``committed`` is
    the number of steps that reached state in THIS call; ``skipped`` is the number
    a resume recognized as already-committed and did not re-submit;
    ``committed + skipped == len(workflow)`` once a run returns without a refusal."""

    outcomes: list[StepOutcome] = field(default_factory=list)

    @property
    def committed(self) -> int:
        return sum(1 for o in self.outcomes if o.status is StepStatus.EXECUTED)

    @property
    def skipped(self) -> int:
        return sum(1 for o in self.outcomes if o.status is StepStatus.SKIPPED)

    @property
    def refused(self) -> list[StepOutcome]:
        return [o for o in self.outcomes if o.status is StepStatus.REFUSED]

    @property
    def all_ok(self) -> bool:
        """``True`` iff every step reached state (none refused, none left
        pending)."""
        return bool(self.outcomes) and all(o.ok for o in self.outcomes)

    def __iter__(self):
        return iter(self.outcomes)

    def __len__(self) -> int:
        return len(self.outcomes)


class WorkflowError(Exception):
    """A durable-workflow runner error (a step left pending past its deadline, a
    workflow that cannot make progress). Subclasses of
    :class:`dregg.pg.DreggPgError` are raised for the pg-layer faults (an RLS
    refusal at enqueue); this names the *workflow-level* faults."""


class StepRefused(WorkflowError):
    """A step's turn was REFUSED by the verified spine (the drainer rejected it:
    a revoked capability, a turn that does not chain, a malformed envelope). The
    :attr:`outcome` carries the reason. ``run`` raises this by default
    (fail-closed) so a refused charge stops the workflow; pass
    ``stop_on_refusal=False`` to collect refusals into the report instead."""

    def __init__(self, outcome: StepOutcome) -> None:
        self.outcome = outcome
        super().__init__(
            f"workflow step {outcome.step.name!r} REFUSED by the verified spine: "
            f"{outcome.error or 'no reason given'} "
            f"(the turn could not pass AUTHZ/CHAIN — e.g. a revoked capability or a "
            f"replayed/non-chaining turn)"
        )


class DurableWorkflow:
    """An ordered, named sequence of verified turns driven durably through
    pg-dregg — the Python face of ``pg_dregg::workflow::Workflow`` + the durable
    ``run``/``resume`` driver.

    Build it by appending steps, then :meth:`run` it against a
    :class:`dregg.pg.Pg`. The runner:

    1. **enqueues** each step's signed turn via ``dregg_submit_turn`` (durable the
       instant it returns; RLS-gated by the presented capability);
    2. **awaits** the node drainer's terminal verdict on it
       (``pending → executed | refused``), polling ``dregg.submit_queue_audit``;
    3. **stops fail-closed** on a refusal (a cancelled subscriber's charge is
       refused → the workflow halts), unless told to collect refusals.

    EXACTLY-ONCE ACROSS CRASHES is :meth:`resume`: it reads what already committed
    for this workflow (by the per-step :attr:`~WorkflowStep.idempotency_key`,
    reconciled against the audit view) and re-drives only the uncommitted tail.
    Because the workflow id + step index are deterministic, re-constructing the
    SAME workflow and calling :meth:`resume` after a crash continues exactly where
    it stopped — a committed step is skipped, never double-submitted.

        wf = (dregg.pg.DurableWorkflow("monthly-billing")
                  .step("charge alice", alice, alice_turn)
                  .step("charge bob",   bob,   bob_turn))
        report = wf.run(pg)            # drives both to executed
        # …process crashes, restarts…
        report = wf.resume(pg)         # skips alice (already committed), re-drives bob
    """

    def __init__(self, name: str, *, workflow_id: Optional[str] = None) -> None:
        #: The workflow's name (for provenance / logging).
        self.name = name
        #: A stable id binding this workflow's steps' idempotency keys together.
        #: Defaults to the name (so re-constructing the named workflow reconciles);
        #: pass an explicit per-run id to isolate two concurrent runs of the same
        #: named workflow.
        self.workflow_id = workflow_id or name
        self.steps: list[WorkflowStep] = []

    # ── building ──
    def step(
        self,
        name: str,
        agent: Bytes32,
        signed_turn: bytes,
        *,
        idempotency_key: Optional[str] = None,
    ) -> "DurableWorkflow":
        """Append a step (chainable). ``agent`` is the acting cell id (hex str or
        32 bytes); ``signed_turn`` is the postcard ``SignedTurn`` bytes the node
        executes. The idempotency key defaults to a deterministic
        ``"{workflow_id}:{index}:{name}"`` — stable across re-runs so a resume
        reconciles; override to pin it to a domain id."""
        idx = len(self.steps)
        key = idempotency_key or f"{self.workflow_id}:{idx}:{name}"
        self.steps.append(
            WorkflowStep(name=name, agent=agent, signed_turn=signed_turn, idempotency_key=key)
        )
        return self

    def add(self, step: WorkflowStep) -> "DurableWorkflow":
        """Append a pre-built :class:`WorkflowStep` (chainable). If its
        idempotency key is empty, a deterministic one is assigned."""
        if not step.idempotency_key:
            idx = len(self.steps)
            step = WorkflowStep(
                name=step.name,
                agent=step.agent,
                signed_turn=step.signed_turn,
                idempotency_key=f"{self.workflow_id}:{idx}:{step.name}",
            )
        self.steps.append(step)
        return self

    def __len__(self) -> int:
        return len(self.steps)

    # ── driving ──
    def run(
        self,
        pg: "Pg",
        *,
        drainer: "Optional[LocalDrainer]" = None,
        stop_on_refusal: bool = True,
        await_timeout: float = 10.0,
        poll_interval: float = 0.05,
    ) -> RunReport:
        """Drive every step from the start (a fresh run — no reconciliation).

        :param pg: a :class:`dregg.pg.Pg` with a ``submit`` capability presented
            and the ``dregg_reader`` role assumed (so ``submit_gate`` bites).
        :param drainer: an optional :class:`LocalDrainer` to apply queued turns
            where no live node drainer runs (dev/test only — it is NOT the
            verified executor; see the module seam note). Production leaves this
            ``None`` and relies on the node drainer.
        :param stop_on_refusal: raise :class:`StepRefused` on the first refused
            step (default, fail-closed — a refused charge halts the run). Set
            ``False`` to collect refusals into the report and keep going.
        :param await_timeout: seconds to wait for a step's terminal verdict before
            raising :class:`WorkflowError` (leaving the step pending — durable, so
            a later :meth:`resume` picks it up).
        :param poll_interval: seconds between audit-view polls.
        """
        return self._drive(
            pg,
            reconcile=False,
            drainer=drainer,
            stop_on_refusal=stop_on_refusal,
            await_timeout=await_timeout,
            poll_interval=poll_interval,
        )

    def resume(
        self,
        pg: "Pg",
        *,
        drainer: "Optional[LocalDrainer]" = None,
        stop_on_refusal: bool = True,
        await_timeout: float = 10.0,
        poll_interval: float = 0.05,
    ) -> RunReport:
        """Resume the workflow after a crash — reconcile against what already
        committed and re-drive only the uncommitted tail (exactly-once).

        Reads the submissions already present for this workflow's steps (by
        idempotency key, via :meth:`_committed_keys`), marks each already-executed
        step ``skipped``, and drives the rest. Same parameters as :meth:`run`."""
        return self._drive(
            pg,
            reconcile=True,
            drainer=drainer,
            stop_on_refusal=stop_on_refusal,
            await_timeout=await_timeout,
            poll_interval=poll_interval,
        )

    # ── internals ──
    def _drive(
        self,
        pg: "Pg",
        *,
        reconcile: bool,
        drainer: "Optional[LocalDrainer]",
        stop_on_refusal: bool,
        await_timeout: float,
        poll_interval: float,
    ) -> RunReport:
        report = RunReport()
        already = self._committed_keys(pg) if reconcile else {}
        for step in self.steps:
            prior = already.get(step.idempotency_key)
            if prior is not None and prior.status in ("executed", "skipped"):
                # The step already committed in a prior (crashed) run — skip it.
                report.outcomes.append(
                    StepOutcome(
                        step=step,
                        status=StepStatus.SKIPPED,
                        submission_id=prior.submission_id,
                        receipt_hash=prior.receipt_hash,
                    )
                )
                continue
            outcome = self._drive_one(
                pg,
                step,
                drainer=drainer,
                await_timeout=await_timeout,
                poll_interval=poll_interval,
                resubmit_pending=prior,
            )
            report.outcomes.append(outcome)
            if outcome.status is StepStatus.REFUSED and stop_on_refusal:
                raise StepRefused(outcome)
        return report

    def _drive_one(
        self,
        pg: "Pg",
        step: WorkflowStep,
        *,
        drainer: "Optional[LocalDrainer]",
        await_timeout: float,
        poll_interval: float,
        resubmit_pending: "Optional[_PriorSubmission]" = None,
    ) -> StepOutcome:
        """Enqueue ``step`` (unless a prior pending submission for it exists) and
        await its terminal verdict."""
        if resubmit_pending is not None and resubmit_pending.status == "pending":
            # A prior run enqueued it but crashed before the verdict; do NOT
            # re-enqueue (that would be a double-submit). Await the existing row.
            submission_id = resubmit_pending.submission_id
        else:
            submission_id = pg.submit_turn(step.signed_turn, step.agent)
        # If a dev-time drainer is supplied, let it apply the queued turn (the
        # node drainer's stand-in). With a live node running, this is a no-op and
        # the real drainer resolves the row.
        if drainer is not None:
            drainer.drain_one(submission_id, step)
        return self._await_outcome(
            pg, step, submission_id, await_timeout=await_timeout, poll_interval=poll_interval
        )

    def _await_outcome(
        self,
        pg: "Pg",
        step: WorkflowStep,
        submission_id: Any,
        *,
        await_timeout: float,
        poll_interval: float,
    ) -> StepOutcome:
        """Poll ``dregg.submit_queue_audit`` for the submission until it reaches a
        terminal status or the deadline passes."""
        deadline = time.monotonic() + await_timeout
        while True:
            sub = pg.submission(submission_id)
            if sub is not None and sub.status == "executed":
                return StepOutcome(
                    step=step,
                    status=StepStatus.EXECUTED,
                    submission_id=submission_id,
                    receipt_hash=sub.receipt_hash,
                )
            if sub is not None and sub.status == "refused":
                return StepOutcome(
                    step=step,
                    status=StepStatus.REFUSED,
                    submission_id=submission_id,
                    error=sub.error,
                )
            if time.monotonic() >= deadline:
                raise WorkflowError(
                    f"workflow step {step.name!r} (submission {submission_id}) is "
                    f"still pending after {await_timeout:.1f}s — no drainer applied "
                    f"it. The enqueue is durable; a later resume() will pick it up. "
                    f"(Is the node drainer running? For dev, pass a LocalDrainer.)"
                )
            time.sleep(poll_interval)

    def _committed_keys(self, pg: "Pg") -> "dict[str, _PriorSubmission]":
        """Read the submissions already present for THIS workflow's steps and key
        them by idempotency key, so :meth:`resume` knows what to skip.

        The live ``dregg.submit_queue`` carries no idempotency column (idempotency
        is the chain tooth's job; this is the fast-path reconciliation over it), so
        the runner correlates by matching each step's ``(agent, signed_turn)``
        against the outbox rows the presented capability can see. A step whose
        exact ``(agent, signed_turn)`` already appears executed is recognized as
        committed; a pending one is awaited rather than re-enqueued. This is a
        conservative reconciliation — it never skips a step it cannot positively
        match, so the worst case is a chain-refused re-submit (the backstop), never
        a lost step."""
        # Map (agent_hex, signed_turn_bytes) -> the most-relevant prior submission.
        want: dict[tuple[str, bytes], WorkflowStep] = {}
        for step in self.steps:
            want[(_agent_hex(step.agent), bytes(step.signed_turn))] = step
        found: dict[str, _PriorSubmission] = {}
        # The audit view does not carry signed_turn; correlate via the base table
        # the runner can read (RLS-gated to the presented cap). We read agent+id+
        # status+receipt and match signed_turn from the base submit_queue.
        for agent_hex, turn_bytes, sid, status, receipt in _iter_prior_submissions(pg):
            step = want.get((agent_hex, turn_bytes))
            if step is None:
                continue
            prior = found.get(step.idempotency_key)
            # Prefer a terminal/executed row over a pending one if duplicates exist.
            if prior is None or (status == "executed" and prior.status != "executed"):
                found[step.idempotency_key] = _PriorSubmission(
                    submission_id=sid, status=status, receipt_hash=receipt
                )
        return found


@dataclass
class _PriorSubmission:
    submission_id: Any
    status: str
    receipt_hash: Optional[str] = None


def _agent_hex(agent: Bytes32) -> str:
    if isinstance(agent, (bytes, bytearray)):
        return bytes(agent).hex()
    s = str(agent)
    return s[2:] if s.startswith(("\\x", "0x")) else s


def _iter_prior_submissions(
    pg: "Pg",
) -> "Iterable[tuple[str, bytes, Any, str, Optional[str]]]":
    """Yield ``(agent_hex, signed_turn_bytes, id, status, receipt_hash_hex)`` for
    every submission the presented capability can see — read straight from the
    base ``dregg.submit_queue`` (RLS-gated by the ``submit_read`` policy). Used by
    resume-reconciliation to correlate a step to its already-committed row by its
    exact ``(agent, signed_turn)``."""
    rows = pg._rows(  # type: ignore[attr-defined]
        "SELECT encode(agent,'hex'), signed_turn, id, status, encode(receipt_hash,'hex') "
        "FROM dregg.submit_queue ORDER BY id"
    )
    for agent_hex, signed_turn, sid, status, receipt in rows:
        yield (
            agent_hex,
            bytes(signed_turn) if signed_turn is not None else b"",
            sid,
            status,
            receipt,
        )


# ───────────────────────── the dev/test drainer stand-in ─────────────────────


class LocalDrainer:
    """A **dev/test stand-in** for the node's submit-queue drainer — NOT the
    verified executor.

    The real write path (``docs/PG-DREGG.md`` §11.4) is: a pg-user enqueues a
    signed turn; the **node's drainer** (``dregg_kernel`` role) decodes it, runs it
    through the real verified Lean executor (``execute_via_producer``), materializes
    the post-state, and stamps the queue row ``executed`` (with the receipt) or
    ``refused``. That drainer is node-side M3 work and is the only thing that turns
    a queued *intent* into verified *state*.

    Where no live node is running (a bare ``cargo pgrx`` cluster, a unit/dev box),
    this stand-in lets the durable-workflow *runner* be driven end-to-end against
    real pg18: it assumes the ``dregg_kernel`` role (BYPASSRLS, the only writer)
    and resolves a pending row to ``executed`` with a synthetic receipt hash — so
    the runner's enqueue → await → exactly-once loop is exercised against genuine
    persisted rows. It performs **no turn verification and writes no cell state**;
    it is explicitly a transport stub for the drain transition. A
    :attr:`refuse_predicate` lets a test drive the *refused* arm (e.g. "a turn for a
    cancelled agent is refused"), modelling the spine's fail-closed behavior
    without a real executor.

    Use it ONLY in dev/test. In production the node drainer does this, and the
    runner is called with ``drainer=None``.

    REVOCATION re-check (faithful to the real drainer). Like the node drainer
    (``dregg-pg``'s ``dregg_drain_once``, the
    ``drainer_refuses_a_revoked_since_enqueue_intent_at_drain`` test), this
    stand-in re-checks the row's persisted ``submit_token`` against the revocation
    registry (``dregg_cap_not_revoked``) BEFORE resolving — so a capability revoked
    AFTER enqueue but before drain causes the queued turn to resolve ``refused``
    (reason ``"revoked"``), never executed. This is where pg-dregg's
    instant-revocation actually bites in the write path: NOT at enqueue (the
    ``submit_gate`` checks only the cap's caveats), but at the drain re-check. Pass
    ``check_revocation=False`` to disable it (e.g. to model a deployment with no
    revocation tier)."""

    def __init__(
        self,
        pg: "Pg",
        *,
        refuse_predicate: Optional[Callable[[Any, WorkflowStep], Optional[str]]] = None,
        receipt_of: Optional[Callable[[WorkflowStep], bytes]] = None,
        check_revocation: bool = True,
    ) -> None:
        """:param pg: a :class:`dregg.pg.Pg` connected AS (or able to assume) the
            ``dregg_kernel`` role — the only role that may UPDATE the queue.
        :param refuse_predicate: ``(submission_id, step) -> reason | None`` — return
            a reason string to drive the *refused* arm for that step (models a
            non-chaining / malformed-envelope refusal), or ``None`` to execute it.
            Runs IN ADDITION to the revocation re-check.
        :param receipt_of: ``(step) -> 32 bytes`` to use as the synthetic
            receipt hash; defaults to a uuid-derived 32-byte value.
        :param check_revocation: re-check the row's ``submit_token`` against
            ``dregg_cap_not_revoked`` and refuse a revoked intent (default; the real
            drainer's behavior)."""
        self._pg = pg
        self._refuse = refuse_predicate
        self._receipt_of = receipt_of
        self._check_revocation = check_revocation

    def drain_one(self, submission_id: Any, step: WorkflowStep) -> None:
        """Resolve one pending submission as the kernel role: ``executed`` (with a
        receipt) unless the row's token is revoked or :attr:`refuse_predicate`
        returns a reason, in which case ``refused``. Idempotent: a row not
        currently ``pending`` is left untouched (so a re-drive after a crash never
        double-resolves)."""
        reason = self._revocation_reason(submission_id) if self._check_revocation else None
        if reason is None and self._refuse is not None:
            reason = self._refuse(submission_id, step)
        # Run the UPDATE as the kernel role. We use a short explicit role swap so
        # the caller's reader role/token are restored afterward.
        conn = self._pg.connection
        with conn.cursor() as cur:
            cur.execute("SELECT current_setting('role', true)")
            prev = (cur.fetchone() or [None])[0]
            try:
                cur.execute("SET ROLE dregg_kernel")
                if reason is None:
                    receipt = (
                        self._receipt_of(step)
                        if self._receipt_of is not None
                        else uuid.uuid4().bytes + uuid.uuid4().bytes[:16]
                    )
                    cur.execute(
                        "UPDATE dregg.submit_queue "
                        "SET status='executed', receipt_hash=%s, resolved_at=now() "
                        "WHERE id=%s AND status='pending'",
                        (bytes(receipt), submission_id),
                    )
                else:
                    cur.execute(
                        "UPDATE dregg.submit_queue "
                        "SET status='refused', error=%s, resolved_at=now() "
                        "WHERE id=%s AND status='pending'",
                        (reason, submission_id),
                    )
            finally:
                # Restore the prior role (RESET ROLE drops to the session role;
                # re-assume the reader if that is what we came in as).
                if prev and prev not in ("none", "None"):
                    cur.execute("SET ROLE " + _safe_role(prev))
                else:
                    cur.execute("RESET ROLE")

    def _revocation_reason(self, submission_id: Any) -> Optional[str]:
        """Re-check the queued row's persisted ``submit_token`` against the
        revocation registry (the real drainer's defence-in-depth). Returns
        ``"revoked"`` if the token is revoked (so the intent is refused), else
        ``None``. A NULL/absent token is deny-by-default ⇒ ``"revoked (no token)"``
        (the real drainer treats a tokenless row as unauthorized)."""
        conn = self._pg.connection
        with conn.cursor() as cur:
            cur.execute("SELECT current_setting('role', true)")
            prev = (cur.fetchone() or [None])[0]
            try:
                cur.execute("SET ROLE dregg_kernel")
                cur.execute(
                    "SELECT submit_token FROM dregg.submit_queue WHERE id = %s",
                    (submission_id,),
                )
                row = cur.fetchone()
                token = row[0] if row else None
                if not token:
                    return "revoked (no submit token — deny-by-default)"
                cur.execute("SELECT dregg_cap_not_revoked(%s)", (token,))
                not_revoked = (cur.fetchone() or [True])[0]
                return None if not_revoked else "revoked"
            finally:
                if prev and prev not in ("none", "None"):
                    cur.execute("SET ROLE " + _safe_role(prev))
                else:
                    cur.execute("RESET ROLE")

    def drain_pending(self, *, limit: Optional[int] = None) -> int:
        """Drain ALL currently-pending rows the kernel can see (arrival order),
        returning how many it resolved. The poll-loop form a real drainer runs;
        here it lets a test resolve a batch at once. Returns the count executed +
        refused."""
        conn = self._pg.connection
        resolved = 0
        with conn.cursor() as cur:
            cur.execute("SET ROLE dregg_kernel")
            try:
                sql = (
                    "SELECT id, encode(agent,'hex'), signed_turn FROM dregg.submit_queue "
                    "WHERE status='pending' ORDER BY id"
                )
                if limit is not None:
                    sql += f" LIMIT {int(limit)}"
                cur.execute(sql)
                pend = cur.fetchall()
            finally:
                cur.execute("RESET ROLE")
        for sid, agent_hex, signed_turn in pend:
            step = WorkflowStep(
                name=f"drain:{sid}",
                agent=agent_hex,
                signed_turn=bytes(signed_turn) if signed_turn is not None else b"",
            )
            self.drain_one(sid, step)
            resolved += 1
        return resolved


def _safe_role(role: str) -> str:
    if not role or len(role) > 63 or not (role[0].isalpha() or role[0] == "_"):
        raise ValueError(f"refusing to restore unsafe role identifier: {role!r}")
    if not all(c.isalnum() or c == "_" for c in role):
        raise ValueError(f"refusing to restore unsafe role identifier: {role!r}")
    return role
