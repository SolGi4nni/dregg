"""Smoke tests for the `dregg` Python SDK.

No live node: everything here is either pure construction (profiles in a
temp DREGG_HOME, offline signing with pinned federation_id/nonce) or runs
against a tiny in-process mock node (http.server). The devnet path lives in
examples/quickstart.py.
"""

import json
import os
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import pytest

import dregg
from dregg import program

FED = "00" * 32


@pytest.fixture(autouse=True)
def temp_dregg_home(tmp_path, monkeypatch):
    """Point the profile store at a fresh temp dir for every test."""
    monkeypatch.setenv("DREGG_HOME", str(tmp_path / "dregg-home"))
    monkeypatch.delenv("DREGG_PROFILE", raising=False)
    monkeypatch.delenv("DREGG_API_TOKEN", raising=False)


# ─── identity / profiles ───


def test_create_and_load_profile():
    ident = dregg.Identity.create("ember-py")
    assert ident.name == "ember-py"
    assert len(ident.public_key) == 64
    assert len(ident.cell_id) == 64

    again = dregg.Identity.from_profile("ember-py")
    assert again.public_key == ident.public_key
    assert again.cell_id == ident.cell_id


def test_duplicate_profile_refused():
    dregg.Identity.create("dupe")
    with pytest.raises(dregg.DreggRefused):
        dregg.Identity.create("dupe")


def test_missing_profile_errors():
    with pytest.raises(dregg.DreggError):
        dregg.Identity.from_profile("ghost")


def test_active_profile_via_env(monkeypatch):
    dregg.Identity.create("envy")
    monkeypatch.setenv("DREGG_PROFILE", "envy")
    ident = dregg.Identity.active()
    assert ident.public_key == dregg.Identity.from_profile("envy").public_key


def test_no_active_profile_errors():
    with pytest.raises(dregg.DreggError):
        dregg.Identity.active()


def test_profile_store_is_shared_with_rust_sdk(tmp_path):
    """The golden derivation vector mirrored from sdk/src/profiles.rs and
    cli/src/commands/id.rs: a profile file with seed 00 01 02 … 3f must load
    to this exact key. If the binding drifts from the store, this fails."""
    profiles_dir = os.path.join(os.environ["DREGG_HOME"], "profiles")
    os.makedirs(profiles_dir, exist_ok=True)
    seed_hex = bytes(range(64)).hex()
    record = {
        "version": 1,
        "name": "golden",
        "seed_hex": seed_hex,
        "public_key_hex": "ignored-on-load",
        "created_at": 0,
    }
    with open(os.path.join(profiles_dir, "golden.json"), "w") as f:
        json.dump(record, f)

    ident = dregg.Identity.from_profile("golden")
    assert (
        ident.public_key
        == "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a"
    )


def test_list_profiles():
    dregg.Identity.create("alpha")
    dregg.Identity.create("beta")
    names = {p["name"] for p in dregg.list_profiles()}
    assert {"alpha", "beta"} <= names


# ─── builder / sign (pure construction: federation_id + nonce pinned) ───


def offline_builder(name="builder"):
    ident = dregg.Identity.create(name)
    return ident, ident.turn("http://offline.invalid", federation_id=FED)


def test_empty_turn_refused():
    _, t = offline_builder("empty")
    with pytest.raises(dregg.DreggRefused) as exc:
        t.nonce(0).sign()
    assert "no effects staged" in str(exc.value)


def test_sign_transfer_offline():
    ident, t = offline_builder("xfer")
    to = "28" * 32
    signed = t.transfer(to, 100).fee(5000).memo("hi from python").nonce(0).sign()
    assert len(signed.turn_hash) == 64
    assert signed.signer == ident.public_key
    text = signed.explain()
    assert "transfer" in text.lower()
    body = signed.to_bytes()
    assert isinstance(body, bytes) and len(body) > 0


def test_builder_chains_and_counts_effects():
    _, t = offline_builder("chain")
    t = (
        t.transfer("11" * 32, 1)
        .write_u64(0, 42)
        .write(1, b"\x07" * 32)
        .grant("22" * 32)
        .increment_nonce()
        .method("execute")
    )
    assert len(t) == 5


def test_write_accepts_int_and_bytes_and_hex():
    _, t = offline_builder("writes")
    t = t.write(0, 7).write(1, "aa" * 32).write(2, b"\x01" * 32)
    assert len(t) == 3
    with pytest.raises(ValueError):
        t.write(3, b"too-short")


def test_explain_draft_and_signed():
    _, t = offline_builder("expl")
    t = t.transfer("33" * 32, 9)
    draft = dregg.explain(t)
    assert draft.startswith("DRAFT")
    signed = t.nonce(0).sign()
    assert dregg.explain(signed) == signed.explain()
    with pytest.raises(TypeError):
        dregg.explain("not a turn")


def test_signing_is_deterministic_per_turn():
    """Same staged turn, same key, same nonce → same turn hash (the
    signature covers the canonical Turn::hash)."""
    ident = dregg.Identity.create("det")
    mk = lambda: (
        ident.turn("http://offline.invalid", federation_id=FED)
        .transfer("44" * 32, 5)
        .nonce(3)
        .valid_until(1_700_000_000)
        .sign()
    )
    assert mk().turn_hash == mk().turn_hash


# ─── program atoms ───


def test_program_atoms_construct():
    atoms = [
        program.sender_is("ab" * 32),
        program.sender_in_slot(1),
        program.balance_gte(100),
        program.balance_lte(0),
        program.preimage_gate(2),
        program.preimage_gate(2, "poseidon2"),
        program.write_once(0),
        program.immutable(3),
    ]
    for a in atoms:
        assert "Constraint(" in repr(a)
    combined = program.any_of([program.sender_is("ab" * 32), program.balance_gte(1)])
    assert "AnyOf" in repr(combined)


def test_program_descriptor_is_content_addressed():
    a = program.descriptor([program.sender_is("01" * 32), program.balance_gte(10)])
    a2 = program.descriptor([program.sender_is("01" * 32), program.balance_gte(10)])
    b = program.descriptor([program.sender_is("02" * 32), program.balance_gte(10)])
    assert a["factory_vk"] == a2["factory_vk"]
    assert a["factory_vk"] != b["factory_vk"]
    assert a["child_program_vk"] != b["child_program_vk"]
    assert a["constraints"] == 2


def test_bad_hash_kind_rejected():
    with pytest.raises(ValueError):
        program.preimage_gate(0, "md5")


# ─── mock node: submit / receipt / proof / subscribe ───


class MockNode(BaseHTTPRequestHandler):
    node_pubkey = "11" * 32
    submits = []
    reject_with = None
    proof_for = {}
    sse_events = []

    def log_message(self, *args):
        pass

    def _json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("content-type", "application/json")
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path == "/api/node/identity":
            self._json(
                {
                    "public_key": self.node_pubkey,
                    "agent_cell": "22" * 32,
                    "unlocked": True,
                }
            )
        elif self.path.startswith("/api/cell/"):
            self._json({"found": True, "balance": 1000, "nonce": 7})
        elif self.path.startswith("/api/turn/") and self.path.endswith("/proof"):
            turn_hash = self.path.split("/")[3]
            if turn_hash in MockNode.proof_for:
                self._json(MockNode.proof_for[turn_hash])
            else:
                self._json({"error": "not found"}, code=404)
        elif self.path.startswith("/api/events/stream"):
            self.send_response(200)
            self.send_header("content-type", "text/event-stream")
            self.end_headers()
            for i, ev in enumerate(MockNode.sse_events):
                payload = f": hb\nevent: receipt\nid: {i}\ndata: {json.dumps(ev)}\n\n"
                self.wfile.write(payload.encode())
                self.wfile.flush()
            time.sleep(0.2)  # hold briefly so the client reads everything
        else:
            self._json({"error": "not found"}, code=404)

    def do_POST(self):
        if self.path == "/api/turns/submit-signed":
            n = int(self.headers.get("content-length", "0"))
            body = self.rfile.read(n)
            MockNode.submits.append(
                {
                    "content_type": self.headers.get("content-type"),
                    "body_len": len(body),
                }
            )
            if MockNode.reject_with is not None:
                self._json(
                    {
                        "accepted": False,
                        "turn_hash": "ee" * 32,
                        "error": MockNode.reject_with,
                    }
                )
            else:
                self._json(
                    {
                        "accepted": True,
                        "turn_hash": "ab" * 32,
                        "signer": "cd" * 32,
                        "action_count": 1,
                        "proof_status": "proof_pending",
                        "has_witness": True,
                        "witness_count": 1,
                        "error": None,
                    }
                )
        else:
            self._json({"error": "not found"}, code=404)


@pytest.fixture
def mock_node():
    MockNode.submits = []
    MockNode.reject_with = None
    MockNode.proof_for = {}
    MockNode.sse_events = []
    server = ThreadingHTTPServer(("127.0.0.1", 0), MockNode)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    yield f"http://127.0.0.1:{server.server_port}"
    server.shutdown()
    server.server_close()


def test_submit_against_mock_node(mock_node):
    ident = dregg.Identity.create("submitter")
    receipt = ident.turn(mock_node).transfer("55" * 32, 10).sign().submit()

    # The wire envelope was the canonical octet-stream SignedTurn.
    assert MockNode.submits[0]["content_type"] == "application/octet-stream"
    assert MockNode.submits[0]["body_len"] > 0

    # Receipt: dict-like noun.
    assert receipt.turn_hash == "ab" * 32
    assert receipt["action_count"] == 1
    assert receipt.get("witness_count") == 1
    assert receipt.get("missing", "fallback") == "fallback"
    assert "accepted" in receipt
    assert "turn_hash" in receipt.keys()
    assert receipt.has_proof is False
    with pytest.raises(KeyError):
        receipt["nope"]
    assert receipt.to_dict()["proof_status"] == "proof_pending"


def test_refusal_raises_and_teaches(mock_node):
    MockNode.reject_with = "rejected: program violation on cell 99: affine sum 1 > 0"
    ident = dregg.Identity.create("refusee")
    with pytest.raises(dregg.DreggRefused) as exc:
        ident.turn(mock_node).transfer("66" * 32, 10).sign().submit()
    msg = str(exc.value)
    assert "program violation" in msg
    assert "what was signed" in msg  # the explain rides the refusal


def test_proof_lazy_fetch(mock_node):
    ident = dregg.Identity.create("prover")
    receipt = ident.turn(mock_node).write_u64(0, 1).sign().submit()
    assert receipt.proof() is None  # pending: 404 from the node

    MockNode.proof_for["ab" * 32] = {
        "turn_hash": "ab" * 32,
        "proof_len": 4,
        "proof_hex": "deadbeef",
    }
    proof = receipt.proof()
    assert proof["proof_hex"] == "deadbeef"
    # Cached: clearing the mock does not lose the fetched proof.
    MockNode.proof_for.clear()
    assert receipt.proof()["proof_len"] == 4


def test_sign_fetches_node_nonce(mock_node):
    """Without .nonce(n) the builder pulls the live cell nonce (mock: 7).

    Both turns pin the same federation_id and valid_until; Ed25519 signing
    is deterministic, so the turn hashes agree iff the live fetch saw 7."""
    ident = dregg.Identity.create("noncer")
    mk = lambda b: b.transfer("77" * 32, 1).valid_until(1)
    signed_live = mk(ident.turn(mock_node, federation_id=FED)).sign()
    signed_pinned = mk(ident.turn(mock_node, federation_id=FED)).nonce(7).sign()
    assert signed_live.turn_hash == signed_pinned.turn_hash
    signed_other = mk(ident.turn(mock_node, federation_id=FED)).nonce(8).sign()
    assert signed_other.turn_hash != signed_live.turn_hash


def test_subscribe_yields_receipts(mock_node):
    MockNode.sse_events = [
        {"chain_index": 1, "receipt_hash": "aa" * 32, "turn_hash": "bb" * 32,
         "kinds": ["transfer"], "has_proof": False},
        {"chain_index": 2, "receipt_hash": "cc" * 32, "turn_hash": "dd" * 32,
         "kinds": ["set_field"], "has_proof": True},
    ]
    stream = dregg.subscribe(mock_node, kind="transfer")
    it = iter(stream)
    first = next(it)
    second = next(it)
    assert first.turn_hash == "bb" * 32
    assert first.receipt_hash == "aa" * 32
    assert first.has_proof is False
    assert second.turn_hash == "dd" * 32
    assert second.has_proof is True


# ─── kernel: this build embeds the verified Lean kernel ───


def test_kernel_is_lean():
    """The whole point of the shared link mode: the Python module runs the REAL
    verified Lean kernel, not the Rust fallback. verified_step_ok is a live call
    through the proved Exec.recKExec (transfer 5: 50/10 → 45/15)."""
    k = dregg.kernel()
    assert k["lean"] is True
    assert k["producer"] == "lean"
    assert k["verified_step_ok"] is True
    assert '"ok":1' in k["verified_step_out"]
