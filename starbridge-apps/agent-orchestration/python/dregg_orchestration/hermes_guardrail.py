"""Native dregg mandate enforcement for the **hermes-agent** loop (``~/pug/hermes-agent``).

Hermes already serializes "an agent did X" at ONE place: its tool-call guardrail
(``agent/tool_guardrails.py`` — ``ToolCallGuardrailController.before_call`` returns a
``ToolGuardrailDecision`` with ``allows_execution``). That is the exact seam the dregg record names: today
a heuristic failure-counter; with dregg a CAP-GATED, BUDGET-METERED, RECEIPTED decision. This module is the
weld — a drop-in guardrail that runs every hermes tool call through a dregg :class:`Orchestration` mandate
BEFORE it executes, so a worker (a hermes subagent) can never invoke a tool outside its granted scope or
over its budget. The enforcement hermes (like the other three integrators) left as an honest gap, closed at
its own boundary, in its own language.

## How it embeds (zero hermes core edits required)

``DreggToolGuardrail`` produces a ``ToolGuardrailDecision``-SHAPED object (``action`` ∈
``{allow, block}``, ``.allows_execution``, ``.to_metadata()``) — duck-compatible with hermes's own
decision. Two integration modes:

* **Wrap** an existing ``ToolCallGuardrailController`` (:func:`wrap_controller`): the dregg mandate runs
  FIRST (a refusal short-circuits to ``block``); if it admits, hermes's own heuristic guardrail runs. Both
  teeth bite. This is the recommended weld — hermes keeps its loop, dregg adds the verified gate.
* **Standalone**: call :meth:`DreggToolGuardrail.before_call` directly from any loop's dispatch.

The mandate is per-WORKER (a hermes subagent's identity); a single-agent hermes is the degenerate
one-worker case. The audit (:meth:`DreggToolGuardrail.audit`) proves, after the run, that no agent exceeded
its mandate — the property a stranger verifies without trusting the loop.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional

from . import Mandate, MandateError, Orchestration


@dataclass(frozen=True)
class DreggGuardrailDecision:
    """A ``ToolGuardrailDecision``-compatible verdict (duck-typed to hermes's
    ``agent.tool_guardrails.ToolGuardrailDecision``): ``action`` ∈ ``{allow, block}``,
    ``.allows_execution``, ``.to_metadata()``."""

    action: str = "allow"  # allow | block
    code: str = "allow"
    message: str = ""
    tool_name: str = ""
    digest_hex: str = ""

    @property
    def allows_execution(self) -> bool:
        return self.action == "allow"

    @property
    def should_halt(self) -> bool:
        return self.action == "block"

    def to_metadata(self) -> dict[str, Any]:
        return {
            "action": self.action,
            "code": self.code,
            "message": self.message,
            "tool_name": self.tool_name,
            "dregg_digest": self.digest_hex,
            "enforced_by": "dregg-mandate",
        }


class DreggToolGuardrail:
    """A dregg-mandate tool guardrail for a hermes worker.

    Construct with the coordinator's mandate + the per-worker mandates (each ``⊑`` the coordinator's), then
    call :meth:`before_call` from hermes's dispatch with the worker's identity, the tool name, and the
    parsed args. An in-mandate call returns ``allow``; an out-of-mandate or unclassified call returns
    ``block`` (fail-closed, before the tool runs) with a precise reason hermes surfaces to the model.
    """

    def __init__(self, orchestration: Orchestration):
        self.orch = orchestration

    @classmethod
    def for_single_worker(cls, mandate: Mandate, worker: str = "hermes") -> "DreggToolGuardrail":
        """The degenerate single-agent case: one worker whose mandate IS the whole budget (the coordinator
        and the worker are the same authority). Use this to gate a plain (non-swarm) hermes run."""
        return cls(Orchestration(coordinator=mandate, worker_mandates={worker: mandate}))

    def before_call(
        self,
        tool_name: str,
        args: Mapping[str, object] | None,
        worker: str = "hermes",
    ) -> DreggGuardrailDecision:
        """THE GATE — run hermes's pending tool call through the dregg mandate before it executes.

        Returns an ``allow`` decision (metered + logged) if the call is in-mandate; a ``block`` decision
        (fail-closed, nothing metered) if the tool is outside the worker's scope, over its budget, or
        unclassified. The ``message`` is the precise refusal hermes shows the model so it can self-correct.
        """
        try:
            entry = self.orch.authorize_call(worker, tool_name, args)
        except MandateError as e:
            return DreggGuardrailDecision(
                action="block",
                code="dregg_out_of_mandate",
                message=str(e),
                tool_name=tool_name,
            )
        return DreggGuardrailDecision(
            action="allow",
            code="dregg_authorized",
            message=f"authorized: {tool_name} ({entry.tool.value}), spent {entry.spent_after}",
            tool_name=tool_name,
            digest_hex=entry.digest_hex,
        )

    def audit(self):
        """Prove no worker exceeded its mandate over the whole run (delegates to
        :meth:`Orchestration.audit`). Raises :class:`MandateError` on any breach; returns ``AuditOk``."""
        return self.orch.audit()


def wrap_controller(
    controller: Any,
    guardrail: DreggToolGuardrail,
    worker: str = "hermes",
):
    """Wrap a hermes ``ToolCallGuardrailController`` so the dregg mandate runs FIRST on ``before_call``.

    Returns a thin proxy whose ``before_call(tool_name, args)`` (a) runs the dregg mandate gate — a
    refusal short-circuits to a ``block`` decision (the tool never runs); (b) on dregg-admit, delegates to
    the wrapped controller's own ``before_call`` (hermes keeps its heuristic failure-guardrail). Every
    other attribute/method is forwarded unchanged, so the proxy is a drop-in for ``self._tool_guardrails``
    in ``run_agent.py`` — no hermes core edit, both teeth biting.
    """

    class _DreggGuardedController:
        def __init__(self) -> None:
            self._inner = controller
            self._dregg = guardrail
            self._worker = worker

        def before_call(self, tool_name: str, args: Optional[Mapping[str, object]]):
            verdict = self._dregg.before_call(tool_name, args, worker=self._worker)
            if not verdict.allows_execution:
                return verdict  # dregg blocks — the tool never runs.
            # dregg authorized; let hermes's own guardrail have its say (failure-counter, no-progress).
            return self._inner.before_call(tool_name, args)

        def dregg_audit(self):
            return self._dregg.audit()

        def __getattr__(self, name: str) -> Any:
            # Forward everything else (after_call, reset_for_turn, halt_decision, …) to hermes's controller.
            return getattr(self._inner, name)

    return _DreggGuardedController()


__all__ = [
    "DreggGuardrailDecision",
    "DreggToolGuardrail",
    "wrap_controller",
]
