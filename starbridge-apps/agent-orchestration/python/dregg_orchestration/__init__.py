"""dregg_orchestration — a verified mandate gate for ANY Python agent loop.

This is the native Python face of the dregg agent-orchestration substrate: it lets an agent loop (hermes,
or any tool-calling loop) gate EVERY tool call through an attenuable mandate, so a worker can never invoke
a tool outside its granted scope or over its budget — the enforcement the four ADOS integrators all
punted on, at the exact seam (the tool-call boundary).

It is a FAITHFUL MIRROR of the canonical Rust development
``starbridge-apps/agent-orchestration/src/{lib.rs,mcp.rs}``:

* ``Tool`` / ``Mandate`` mirror the Rust ``Tool`` / ``Mandate`` (the attenuation triple
  ``tools ∧ budget ∧ sub_task`` with the ``granted ⊑ held`` lattice — the proven non-amplification);
* ``tool_for_mcp_name`` mirrors the Rust ``mcp::tool_for_mcp_name`` (the MCP-name → capability map);
* ``content_address`` mirrors the Rust ``McpToolCall::digest`` (``blake3(name ‖ canonical-json(args))``);
* ``audit_run`` mirrors the Rust ``audit_run`` (re-derive the run, prove no agent exceeded its mandate).

The Rust crate is the SOURCE OF TRUTH; ``tests/test_differential.py`` pins this mirror against vectors the
Rust ``#[test]``s also assert, so drift on either side fails. The Rust executor remains the place a
verified TURN is actually committed (via the ``dregg`` sdk-py binding's ``AuthorizedTurn.submit``); this
package is the in-loop GATE + the off-loop AUDIT — the decision and the proof, in the loop's own language.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from typing import Iterable, Mapping, Optional


class Tool(str, Enum):
    """A capability an agent's tool exercises — the scope axis of a :class:`Mandate`.

    Mirrors the Rust ``Tool`` enum. A coordinator holds a broad tool-set; a worker is handed a narrowed
    subset (``write``/``spend`` dropped for a read-only researcher).
    """

    READ = "read"
    SEARCH = "search"
    SUMMARIZE = "summarize"
    WRITE = "write"
    SPEND = "spend"


# The MCP-name → (capability, default cost) map — the EXACT mirror of the Rust ``mcp::tool_for_mcp_name``.
# An unknown tool is absent (``None``) and is refused (fail-closed: a tool the policy does not classify
# cannot run under a mandate). A deployment overrides this for its own toolset.
_MCP_TOOL_MAP: dict[str, tuple[Tool, int]] = {
    # Read (fetch a doc / url / file) — least-privilege baseline.
    "fetch": (Tool.READ, 50),
    "read_file": (Tool.READ, 50),
    "read": (Tool.READ, 50),
    "get": (Tool.READ, 50),
    "http_get": (Tool.READ, 50),
    # Search (query an index / corpus / filesystem).
    "search": (Tool.SEARCH, 100),
    "grep": (Tool.SEARCH, 100),
    "web_search": (Tool.SEARCH, 100),
    "find": (Tool.SEARCH, 100),
    "query": (Tool.SEARCH, 100),
    # Summarize / transform.
    "summarize": (Tool.SUMMARIZE, 150),
    "transform": (Tool.SUMMARIZE, 150),
    "extract": (Tool.SUMMARIZE, 150),
    "synthesize": (Tool.SUMMARIZE, 150),
    # Write (mutate the shared workspace) — privileged.
    "write_file": (Tool.WRITE, 200),
    "edit": (Tool.WRITE, 200),
    "apply_patch": (Tool.WRITE, 200),
    "write": (Tool.WRITE, 200),
    "put": (Tool.WRITE, 200),
    # Spend (pay an external API / move treasury) — most privileged.
    "transfer": (Tool.SPEND, 300),
    "pay": (Tool.SPEND, 300),
    "purchase": (Tool.SPEND, 300),
    "spend": (Tool.SPEND, 300),
    "charge": (Tool.SPEND, 300),
}


@dataclass(frozen=True)
class ToolBinding:
    """The capability an MCP tool exercises + its default metered cost (the Rust ``ToolBinding``)."""

    tool: Tool
    cost: int


def tool_for_mcp_name(mcp_name: str) -> Optional[ToolBinding]:
    """Classify an MCP tool name into the capability it exercises + a default cost, or ``None`` if the
    policy does not classify it (fail-closed). The exact mirror of the Rust ``mcp::tool_for_mcp_name``."""
    hit = _MCP_TOOL_MAP.get(mcp_name)
    if hit is None:
        return None
    return ToolBinding(tool=hit[0], cost=hit[1])


def canonical_args(args: Mapping[str, object] | None) -> str:
    """Sorted, compact JSON of tool arguments — the canonical form bound into the content-address.

    Mirrors hermes's own ``canonical_tool_args`` (sorted keys, compact separators) so the digest a dregg
    receipt binds is the SAME bytes hermes's guardrail signs.
    """
    return json.dumps(
        args or {},
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    )


def content_address(name: str, args: Mapping[str, object] | None) -> bytes:
    """``blake3(name ‖ canonical-json(args))`` — the content-address a verified step binds, so the receipt
    proves the EXACT tool + arguments the worker ran. Mirrors the Rust ``McpToolCall::digest``.

    blake3 is preferred (the Rust side uses it); if the ``blake3`` package is unavailable we fall back to
    sha256 with a distinct domain tag so the two never collide (the differential test pins the blake3
    vector when blake3 is present).
    """
    payload = b"dregg-mcp-tool-call\x01" + name.encode("utf-8") + b"\x00" + canonical_args(args).encode("utf-8")
    try:
        import blake3  # type: ignore

        return blake3.blake3(payload).digest()
    except Exception:
        return hashlib.sha256(b"dregg-mcp-fallback-sha256\x01" + payload).digest()


@dataclass(frozen=True)
class Mandate:
    """An attenuable mandate the coordinator confers on a worker — the Rust ``Mandate`` (the triple
    ``tools ∧ budget ∧ sub_task`` with the ``granted ⊑ held`` lattice).

    The worker may invoke ONLY the tools it lists, may spend AT MOST ``budget``, and is scoped to
    ``sub_task``. ``le`` is the attenuation order (``granted ⊑ held``); ``attenuate`` derives a mandate
    ``⊑`` this one (never wider — the ``derive_no_amplify`` discipline).
    """

    tools: frozenset[Tool]
    budget: int
    sub_task: str = ""

    @classmethod
    def coordinator(cls, tools: Iterable[Tool], budget: int, task: str = "") -> "Mandate":
        """The coordinator's broad mandate — all the tools it is willing to delegate + the full budget."""
        return cls(tools=frozenset(tools), budget=int(budget), sub_task=task)

    def le(self, held: "Mandate") -> bool:
        """``granted ⊑ held`` — ``self.tools ⊆ held.tools`` AND ``self.budget <= held.budget``. The
        non-amplification order (the Rust ``Mandate::le`` / ``worker_authority_subset_orchestrator``)."""
        return self.tools <= held.tools and self.budget <= held.budget

    def attenuate(self, request_tools: Iterable[Tool], request_budget: int, sub_task: str = "") -> "Mandate":
        """Derive a worker mandate ⊑ this one: INTERSECT the requested tools with what is held, CLAMP the
        requested budget to what is held. The result is GUARANTEED ``⊑ self`` (the Rust
        ``Mandate::attenuate`` / ``derive_no_amplify``)."""
        requested = frozenset(request_tools)
        return Mandate(
            tools=requested & self.tools,
            budget=min(int(request_budget), self.budget),
            sub_task=sub_task,
        )

    def authorizes(self, tool: Tool, prior_spent: int, cost: int) -> bool:
        """Whether this mandate authorizes invoking ``tool`` at ``cost`` given the worker's
        ``prior_spent`` — ``tool ∈ self.tools`` AND ``prior_spent + cost <= self.budget``. Fail-closed on
        each axis (the Rust ``Mandate::authorizes``)."""
        return tool in self.tools and (prior_spent + cost) <= self.budget


class MandateError(Exception):
    """A tool call was refused by a mandate — the in-the-fire-path refusal (the Rust
    ``OrchestrationError::OutOfMandate`` / ``McpStepError``)."""


@dataclass
class WorkerState:
    """A worker's conferred mandate + running spend (the engine's per-worker state)."""

    mandate: Mandate
    spent: int = 0


@dataclass
class LoggedCall:
    """One committed tool call in the audit log — the call, the worker, the running spend after it, and
    the content-address (the receipt's audit payload). Mirrors the Rust ``LoggedStep`` (the receipt is
    committed via the ``dregg`` sdk-py binding when a verified TURN is wanted)."""

    worker: str
    tool: Tool
    cost: int
    name: str
    digest_hex: str
    spent_after: int


class Orchestration:
    """A verified mandate gate over a worker swarm — the in-loop decision + the off-loop audit.

    The coordinator holds a broad mandate; each worker holds an attenuated mandate (``⊑`` the
    coordinator's — refused at construction otherwise). ``authorize_call`` is the GATE an agent loop calls
    before EVERY tool invocation: an in-mandate call is admitted (and metered + logged), an out-of-mandate
    or unclassified call raises :class:`MandateError` — fail-closed, before the tool runs. ``audit`` proves
    no worker exceeded its mandate over the whole run.

    This is the substrate, not a new loop: the loop body (perceive/plan/act/reflect) is the integrator's;
    dregg owns the one seam — the tool-call/verdict record — and makes it provably authorized + budgeted.
    """

    def __init__(self, coordinator: Mandate, worker_mandates: Mapping[str, Mandate]):
        for name, m in worker_mandates.items():
            if not m.le(coordinator):
                raise MandateError(
                    f"worker {name!r} mandate is NOT ⊑ the coordinator's (amplification): "
                    f"{sorted(t.value for t in m.tools)}/{m.budget} ⊄ "
                    f"{sorted(t.value for t in coordinator.tools)}/{coordinator.budget}"
                )
        self.coordinator = coordinator
        self.workers: dict[str, WorkerState] = {
            name: WorkerState(mandate=m) for name, m in worker_mandates.items()
        }
        self.log: list[LoggedCall] = []

    def spent(self, worker: str) -> int:
        """A worker's running cumulative spend."""
        return self.workers[worker].spent

    def authorize_call(self, worker: str, mcp_name: str, args: Mapping[str, object] | None = None) -> LoggedCall:
        """THE GATE — authorize a worker's tool call against its mandate, then meter + log it.

        Fail-closed on three axes (each a real refusal, before the tool runs):
          * an UNKNOWN tool (not classified by :func:`tool_for_mcp_name`) ⇒ :class:`MandateError`;
          * a tool outside the worker's granted scope ⇒ :class:`MandateError`;
          * a spend over the worker's sub-budget ⇒ :class:`MandateError`.

        On admit, the call is metered (the worker's spend advances) and a :class:`LoggedCall` binding the
        content-address (``blake3(name ‖ args)``) is appended to the audit log + returned. The caller then
        runs the tool — knowing it was authorized — and (optionally) commits the verified turn via the
        ``dregg`` sdk-py binding so the receipt chain is the durable proof.
        """
        if worker not in self.workers:
            raise MandateError(f"unknown worker {worker!r}")
        binding = tool_for_mcp_name(mcp_name)
        if binding is None:
            raise MandateError(
                f"MCP tool {mcp_name!r} is not classified by the orchestration policy (fail-closed)"
            )
        ws = self.workers[worker]
        if binding.tool not in ws.mandate.tools:
            raise MandateError(
                f"out-of-mandate: {worker} may not invoke {mcp_name!r} ({binding.tool.value}) — "
                f"granted scope {{{', '.join(sorted(t.value for t in ws.mandate.tools))}}}"
            )
        if not ws.mandate.authorizes(binding.tool, ws.spent, binding.cost):
            raise MandateError(
                f"out-of-mandate: {worker} spend {ws.spent}+{binding.cost} would breach "
                f"sub-budget {ws.mandate.budget}"
            )
        ws.spent += binding.cost
        digest_hex = content_address(mcp_name, args)[:8].hex()
        entry = LoggedCall(
            worker=worker,
            tool=binding.tool,
            cost=binding.cost,
            name=mcp_name,
            digest_hex=digest_hex,
            spent_after=ws.spent,
        )
        self.log.append(entry)
        return entry

    def audit(self) -> "AuditOk":
        """Re-derive the whole run from the log and PROVE no worker exceeded its mandate — the Rust
        ``audit_run``: (1) every worker mandate ``⊑`` the coordinator's (checked at construction);
        (2) per-call mandate re-check, re-deriving each worker's running spend (a forged meter is caught);
        (3) Σ spend ≤ the coordinator's budget. Returns :class:`AuditOk` or raises :class:`MandateError`."""
        running: dict[str, int] = {name: 0 for name in self.workers}
        for i, entry in enumerate(self.log):
            m = self.workers[entry.worker].mandate
            if entry.tool not in m.tools:
                raise MandateError(f"call #{i}: {entry.worker} invoked {entry.tool.value} outside its scope")
            if not m.authorizes(entry.tool, running[entry.worker], entry.cost):
                raise MandateError(
                    f"call #{i}: {entry.worker} running spend "
                    f"{running[entry.worker]}+{entry.cost} exceeds sub-budget {m.budget}"
                )
            running[entry.worker] += entry.cost
            if running[entry.worker] != entry.spent_after:
                raise MandateError(
                    f"call #{i}: {entry.worker} logged spend {entry.spent_after} != re-derived "
                    f"{running[entry.worker]} (meter forged)"
                )
        total = sum(running.values())
        if total > self.coordinator.budget:
            raise MandateError(f"Σ spend {total} exceeds swarm budget {self.coordinator.budget}")
        return AuditOk(
            calls=len(self.log),
            spent=dict(running),
            budget=self.coordinator.budget,
        )


@dataclass(frozen=True)
class AuditOk:
    """A clean audit verdict — the proof a light client gets back (the Rust ``AuditOk``)."""

    calls: int
    spent: Mapping[str, int]
    budget: int


__all__ = [
    "Tool",
    "ToolBinding",
    "tool_for_mcp_name",
    "canonical_args",
    "content_address",
    "Mandate",
    "MandateError",
    "Orchestration",
    "LoggedCall",
    "AuditOk",
]
