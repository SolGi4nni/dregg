"""Type stubs for the `dregg` Python SDK (the pyo3 extension module).

The two-noun, authorization-first surface, verbatim from the Rust SDK:

    Identity → .turn() → typed verbs → .sign() → .submit() → Receipt

An unauthorized act is inexpressible: nothing leaves `.sign()` until it is a
real Ed25519-signed canonical `SignedTurn`.
"""

from typing import Any, Iterator, Optional, Union

# A 32-byte identifier: a 64-char hex `str` or 32 raw `bytes`.
Bytes32 = Union[str, bytes]

class DreggError(Exception):
    """Base error for the dregg SDK (I/O, profile store, node transport)."""

class DreggRefused(DreggError):
    """The system said no — a refusal from the signing surface or the node,
    carrying the reason and the faithful explanation of what was attempted."""

# ─── Identity (Noun 0: who acts) ───

class Identity:
    """A named local Ed25519 identity from the shared `$DREGG_HOME` profile
    store (`~/.dregg/profiles/<name>.json`, the same files `dregg id` and the
    Rust SDK read)."""

    @staticmethod
    def from_profile(name: str) -> "Identity":
        """Load a named profile from the local store."""
    @staticmethod
    def create(name: str) -> "Identity":
        """Create a named profile with a fresh random seed (refuses an existing
        name) and return its identity. Does not change the active profile."""
    @staticmethod
    def active() -> "Identity":
        """The active profile (`DREGG_PROFILE` env override → the persistent
        `dregg id use` default). Raises DreggError when none is configured."""
    @property
    def name(self) -> Optional[str]: ...
    @property
    def public_key(self) -> str:
        """Hex Ed25519 public key."""
    @property
    def cell_id(self) -> str:
        """Hex CellId in the default federation domain — the agent cell this
        identity acts and pays as."""
    def turn(
        self,
        node_url: str,
        federation_id: Optional[Bytes32] = ...,
        devnet_key: Optional[str] = ...,
    ) -> "TurnBuilder":
        """Open a turn builder against `node_url`. `federation_id` pins the
        signing domain; `devnet_key` is the operator credential for the gated
        ingress (else `$DREGG_API_TOKEN`)."""
    def trustline(
        self, node_url: str, devnet_key: Optional[str] = ...
    ) -> "Trustline":
        """The trustline organ (ORGANS §1) bound to `node_url`."""
    def channels(
        self, node_url: str, devnet_key: Optional[str] = ...
    ) -> "Channels":
        """The channels organ (ORGANS §4) bound to `node_url`."""
    def mailbox(self, relay_url: str) -> "Mailbox":
        """This identity's mailbox (ORGANS §2) on the relay at `relay_url`."""

# ─── TurnBuilder → AuthorizedTurn → Receipt (the one shape) ───

class TurnBuilder:
    """The typed verb builder: stage effects, then `.sign()`. There is no
    submit on this type — only a signed turn can travel."""

    def transfer(self, to: Bytes32, amount: int) -> "TurnBuilder":
        """Transfer `amount` computrons from the acting cell to `to`."""
    def transfer_from(
        self, from_: Bytes32, to: Bytes32, amount: int
    ) -> "TurnBuilder":
        """Transfer with an explicit source cell (executor still checks
        authority)."""
    def write(self, index: int, value: Union[int, Bytes32]) -> "TurnBuilder":
        """Write state slot `index` of the acting cell (int → little-endian
        field, or 32 bytes / hex for a full field element)."""
    def write_u64(self, index: int, value: int) -> "TurnBuilder":
        """`write` with a numeric value."""
    def grant(
        self,
        to: Bytes32,
        target: Optional[Bytes32] = ...,
        permissions: str = ...,
        slot: int = ...,
        expires_at: Optional[int] = ...,
    ) -> "TurnBuilder":
        """Grant a capability from the acting cell to `to` (non-amplifying).
        `permissions` is one of none/signature/proof/either/impossible."""
    def increment_nonce(self) -> "TurnBuilder":
        """Bump the acting cell's nonce (a deliberate no-op state advance)."""
    def method(self, name: str) -> "TurnBuilder":
        """Set the action's method verb (default "execute")."""
    def fee(self, fee: int) -> "TurnBuilder":
        """Set the turn fee (computron budget; default 10_000)."""
    def memo(self, memo: str) -> "TurnBuilder":
        """Attach a memo string."""
    def nonce(self, nonce: int) -> "TurnBuilder":
        """Pin the turn nonce explicitly (else `.sign()` fetches the live
        nonce)."""
    def valid_until(self, unix_secs: int) -> "TurnBuilder":
        """Pin the validity horizon (unix seconds). Default now + 3600."""
    def sign(self) -> "AuthorizedTurn":
        """Sign the staged turn, yielding an AuthorizedTurn ready to
        `.submit()`. Refuses an empty turn."""
    def __len__(self) -> int: ...

class AuthorizedTurn:
    """A signed, ready-to-submit turn. Inspect with `.explain()`; execute with
    `.submit()`."""

    def explain(self) -> str:
        """The clerk's faithful, total explanation of exactly what was signed."""
    @property
    def turn_hash(self) -> str: ...
    @property
    def signer(self) -> str: ...
    def to_bytes(self) -> bytes:
        """The canonical wire bytes (postcard `SignedTurn`)."""
    def submit(self) -> "Receipt":
        """Execute the turn on the node and return the Receipt. Raises
        DreggRefused when the node rejects (the message carries the reason +
        the explanation)."""

class Receipt:
    """Proof-of-execution for one committed turn, dict-like over the node's
    JSON, with the STARK proof lazily fetched."""

    @property
    def turn_hash(self) -> str: ...
    @property
    def receipt_hash(self) -> Optional[str]: ...
    @property
    def has_proof(self) -> bool: ...
    def proof(self, node_url: Optional[str] = ...) -> Optional[Any]:
        """Lazily fetch the composed full-turn STARK, or None while pending."""
    def to_dict(self) -> dict[str, Any]: ...
    def keys(self) -> list[str]: ...
    def get(self, key: str, default: Any = ...) -> Any: ...
    def __getitem__(self, key: str) -> Any: ...
    def __contains__(self, key: str) -> bool: ...
    def __len__(self) -> int: ...

# ─── The receipt nervous system ───

class ReceiptStream:
    """A blocking iterator of Receipts over the node's SSE broadcast.
    Reconnects with backoff + Last-Event-ID resume; iterate forever or
    `break`."""

    def __iter__(self) -> "ReceiptStream": ...
    def __next__(self) -> Receipt: ...

def subscribe(
    node_url: str, cell: Optional[Bytes32] = ..., kind: Optional[str] = ...
) -> ReceiptStream:
    """Subscribe to a node's committed-receipt broadcast. `cell` filters to one
    cell; `kind` to one effect kind (e.g. "transfer", "set_field")."""

# ─── The organs (ORGANS.md) ───

class Trustline:
    """The bilateral line of credit (ORGANS §1). Operator-gated."""

    def open(
        self, holder: Bytes32, line: int, salt: Optional[str] = ...
    ) -> dict[str, Any]: ...
    def draw(
        self, trustline: Bytes32, amount: int, digest: Optional[str] = ...
    ) -> dict[str, Any]: ...
    def repay(self, trustline: Bytes32, amount: int) -> dict[str, Any]: ...
    def settle(self, trustline: Bytes32) -> dict[str, Any]: ...
    def close(self, trustline: Bytes32) -> dict[str, Any]: ...
    def status(self, trustline: Bytes32) -> dict[str, Any]: ...

class Channels:
    """The group-key epoch lift (ORGANS §4). Operator-gated."""

    def create(
        self, tag: int, members: list[dict[str, Bytes32]]
    ) -> dict[str, Any]: ...
    def join(
        self, channel: Bytes32, member: dict[str, Bytes32]
    ) -> dict[str, Any]: ...
    def remove(self, channel: Bytes32, member: Bytes32) -> dict[str, Any]: ...
    def rekey(self, channel: Bytes32) -> dict[str, Any]: ...
    def post(
        self,
        channel: Bytes32,
        epoch: int,
        nonce: Bytes32,
        ciphertext: Union[str, bytes],
    ) -> dict[str, Any]: ...
    def status(self, channel: Bytes32) -> dict[str, Any]: ...
    def messages(self, channel: Bytes32) -> "SseJsonStream": ...

class Mailbox:
    """A hosted inbox over the relay (ORGANS §2). Membership ops are
    owner-signed; sealing/custody-verification happen outside pure Python."""

    @property
    def owner(self) -> str: ...
    def relay_status(self) -> dict[str, Any]: ...
    def subscribe(
        self, capacity: Optional[int] = ..., min_deposit: Optional[int] = ...
    ) -> dict[str, Any]: ...
    def unsubscribe(self) -> dict[str, Any]: ...
    def send(
        self, dest: Bytes32, ciphertext: Union[str, bytes], deposit: int
    ) -> dict[str, Any]: ...
    def drain(self, max: int = ...) -> dict[str, Any]: ...
    def inbox_status(self) -> dict[str, Any]: ...

class AttestedQuery:
    """The light-client read surface (Noun 2's Python face). No identity, no
    signing — fetches federation-attested artifacts to verify elsewhere."""

    def __init__(self, node_url: str) -> None: ...
    def attested_roots(self) -> list[dict[str, Any]]: ...
    def checkpoint(self) -> dict[str, Any]: ...
    def checkpoint_at(self, height: int) -> dict[str, Any]: ...
    def turn_proof(self, turn_hash: str) -> Optional[dict[str, Any]]: ...

class SseJsonStream:
    """A blocking iterator over a node SSE route, yielding each event's `data:`
    JSON payload. Reconnects with backoff + Last-Event-ID resume."""

    def __iter__(self) -> "SseJsonStream": ...
    def __next__(self) -> Any: ...

def faucet(
    node_url: str,
    recipient: Bytes32,
    amount: int,
    public_key: Optional[Bytes32] = ...,
    devnet_key: Optional[str] = ...,
) -> dict[str, Any]:
    """Devnet faucet (`POST /api/faucet`): materialize a hosted cell and/or
    claim computrons. Pass `public_key=` to install a real owner key."""

# ─── explain / profiles / kernel ───

def explain(turn: Union[AuthorizedTurn, TurnBuilder]) -> str:
    """The clerk's faithful rendering of a turn (an AuthorizedTurn = exactly
    what was signed, or a TurnBuilder = a DRAFT rendering)."""

def list_profiles() -> list[dict[str, Any]]:
    """List the local profile store (name / public_key / created_at / active)."""

def kernel() -> dict[str, Any]:
    """Report which kernel this module embeds — and PROVE it by running one
    verified transfer through it (`{lean, producer, verified_step_ok,
    verified_step_out}`)."""

# ─── dregg.program — the cell-program constraint language ───

class program:
    class Constraint:
        def __repr__(self) -> str: ...

    @staticmethod
    def sender_is(pk: Bytes32) -> "program.Constraint": ...
    @staticmethod
    def sender_in_slot(index: int) -> "program.Constraint": ...
    @staticmethod
    def balance_gte(min: int) -> "program.Constraint": ...
    @staticmethod
    def balance_lte(max: int) -> "program.Constraint": ...
    @staticmethod
    def preimage_gate(
        commitment_index: int, hash_kind: str = ...
    ) -> "program.Constraint": ...
    @staticmethod
    def immutable(index: int) -> "program.Constraint": ...
    @staticmethod
    def write_once(index: int) -> "program.Constraint": ...
    @staticmethod
    def any_of(variants: list["program.Constraint"]) -> "program.Constraint": ...
    @staticmethod
    def descriptor(
        constraints: list["program.Constraint"],
    ) -> dict[str, Any]: ...

# ─── dregg.deploy — DreggDL, the checkable deployment spec (CapDL for dregg) ───
#
# A thin binding over the REAL `dregg-deploy` pipeline (parse →
# `Lowered::from_deployment` → `dregg_userspace_verify::analyze`). Author a
# deployment (TOML, or JSON when the text starts with `{`) and `check` it for
# the four static guarantees — conservation, non-amplification, well-formedness,
# ring-balance — over the WHOLE declared authority layout before spending gas,
# exactly like the `dregg-deploy check` CLI. Nothing is reimplemented in Python.

class deploy:
    @staticmethod
    def check(text: str, ring: bool = False) -> dict[str, Any]:
        """Parse DreggDL → lower to the real `CallForest` → run the static
        assurance over the whole authority layout → return the verdict dict:

            {
              "pass": bool,
              "assurance": {
                "pass": bool,
                "conservation":    {"pass": bool, "findings": [...]},
                "no_amplification":{"pass": bool, "findings": [...]},
                "wellformed":      {"pass": bool, "findings": [...]},
                "ring_balance":    {"pass": bool, "findings": [...]},
                "findings": [ {"guarantee", "message",
                               "locus": {"node_path", "effect_index",
                                         "asset", "display"}}, ... ],
              },
              "factories": [ {"ref": str, "factory_vk": hex}, ... ],
              "cells":     [ {"name": str, "cell_id": hex}, ... ],
              "turn_count": int,
            }

        `ring=True` also runs the ring-balance check. Raises `DreggError`
        (naming the offending row) on a parse / lowering error."""

    @staticmethod
    def lower(text: str) -> dict[str, Any]:
        """Run only the real `Lowered::from_deployment` lowering and return the
        resolved artifact:

            {"forest": {CallForest JSON}, "federation_id": hex,
             "factories": [{"ref", "factory_vk"}],
             "cells": [{"name", "cell_id"}]}

        The `forest` is the ordered births → funds → grants the checker
        consumes — the same lowering the SDK replays through its turn builders."""
