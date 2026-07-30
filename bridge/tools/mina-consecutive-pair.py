#!/usr/bin/env python3
"""
`mina-consecutive-pair` — capture a CONSECUTIVE pair of devnet protocol states
and emit them as `Dregg2/Bridge/MinaStateHashRealBlock.lean`.

⚑ WHY A PAIR, AND WHY THIS IS THE STRONGEST AVAILABLE REALITY GATE
==================================================================

`Dregg2/Bridge/MinaStateHashDerive.lean` re-derives a Mina block's `state_hash`
from its binprot bytes. Every PRIMITIVE in that derivation is anchored to
ground truth outside the repo — the two Poseidon salts against openmina's own
pinned regression constants, SHA-256 against `hashlib`, Poseidon against six
o1js gold vectors. What is NOT anchored by any of that is the ORDER: roughly
30 field elements and 1,400 packed bits, assembled from four places where
`Body.to_input` deliberately disagrees with the binprot record order.

The obvious way to check the order is to compare against someone else's
`state_hash` for the same block. That needs an oracle — openmina compiled, or
an explorer's API, or a base58 decode of a value someone published.

**It does not need one.** `state_hash` is not on Mina's peer-to-peer wire at
all: every node computes it, which is why `get_best_tip` never sends it. But
`previous_state_hash` IS on the wire, in the clear, as the first 32 bytes of
every `Protocol_state.Value`. So for a consecutive pair (N, N+1):

    derive_state_hash(block_N) == block_{N+1}.previous_state_hash

Both sides came from the daemon. Neither we nor any transcription of ours is
in the loop. If any of the four order traps or the two leaf facts (253-bit VRF
truncation, big-endian ledger hash into SHA-256) is wrong, the left side is a
different 254-bit number and the equation fails. There is no way to pass this
by accident.

⚑ It also fails if the DECODER is wrong in a way the existing 540186 gate
cannot see: a field-order slip inside `Blockchain_state` still lands on byte
1544 (that gate's "exact fit" check) but moves the preimage.

USAGE
=====

    bridge/tools/mina-consecutive-pair.py

Polls `mina-besttip.py` until it has seen two tips whose `blockchain_length`
differ by exactly 1, then writes the Lean module. Devnet produces a block every
~3 minutes, so expect one to two polls plus a wait; `--max-minutes` caps it.

    --max-minutes N   give up after N minutes (default 25)
    --interval N      seconds between polls (default 45)
    --out PATH        where to write the Lean module
                      (default: metatheory/Dregg2/Bridge/MinaStateHashRealBlock.lean)

It writes NOTHING unless it has a genuine consecutive pair. A partial or
same-height capture is an exit code, never a file — a fixture that is not what
it claims is worse than no fixture.

⚑ WHAT THIS SCRIPT DECIDES: nothing. It is I/O plus one integer comparison
(`len(child) == len(parent) + 1`) to know whether it has a pair. It does not
compute a state hash, does not know which bytes are which field beyond the
three integers it prints for the log, and cannot make anything accept. The
derivation and the equation are both in Lean. Devnet only; no keys, nothing
persisted.
"""

import argparse
import importlib.util
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
BESTTIP = os.path.join(HERE, "mina-besttip.py")
REPO = os.path.dirname(os.path.dirname(HERE))
DEFAULT_OUT = os.path.join(
    REPO, "metatheory", "Dregg2", "Bridge", "MinaStateHashRealBlock.lean"
)

PALLAS_BASE_MODULUS = 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001


def log(*a):
    print("[pair]", *a, flush=True, file=sys.stderr)


def fetch():
    """One `get_best_tip`. Returns the response payload from the Option tag onward."""
    r = subprocess.run(
        [sys.executable, BESTTIP, "--emit-protocol-state"],
        capture_output=True,
    )
    if r.returncode != 0 or not r.stdout:
        log("fetch failed (rc=%d, %d bytes)" % (r.returncode, len(r.stdout)))
        return None
    return r.stdout


# ---------------------------------------------------------------------------
# ⚑ THE PROTOCOL STATE IS A PREFIX OF WHAT THE PEER SENDS.
#
# `mina-besttip.py --emit-protocol-state` hands over the whole `get_best_tip`
# response payload from the Option tag onward: the `Protocol_state.Value` and
# then the rest of the block (header, the entire staged-ledger diff) and the
# proof. Measured on the 540221/540222 pair: 108,140 and 312,394 bytes, of which
# the protocol state is 1,544 each. Embedding the whole payload as a Lean list
# literal is a ~17,600-line file that heartbeats out at `whnf` during
# ELABORATION, before any theorem runs -- which is exactly what the first
# version of this script produced, and the cascading "unknown identifier
# devnetParent" was that def having failed rather than a binding bug.
#
# So we decode, and truncate to the byte count the decode consumed. That also
# retires the height heuristic this file used to carry: the decoder knows.
#
# ⚑ The decoder is IMPORTED from `mina-state-hash-crosscheck.py`, not copied.
# One binprot reader in `tools/`, as there is one in Lean.
# ---------------------------------------------------------------------------

_spec = importlib.util.spec_from_file_location(
    "mina_state_hash_crosscheck", os.path.join(HERE, "mina-state-hash-crosscheck.py")
)
_cc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_cc)


def parse(buf):
    """Decode the protocol-state prefix. Returns (record, prefix_length) or None."""
    try:
        return _cc.decode(buf)
    except Exception as e:
        log("decode failed: %s: %s" % (type(e).__name__, e))
        return None


LEAN_HEADER = '''/-
# Dregg2.Bridge.MinaStateHashRealBlock — ⚑ **THE REALITY GATE FOR A TIP'S IDENTITY.**

`Bridge.MinaStateHashDerive` re-derives `state_hash` from the wire bytes. Every PRIMITIVE it uses is
anchored outside this repo — both Poseidon salts against openmina's own pinned regression constants,
SHA-256 against `hashlib` at two blocks, Poseidon against six o1js golds. What none of that anchors
is the **ORDER**: ~30 field elements and ~1,400 packed bits, assembled across four places where
`Body.to_input` deliberately disagrees with the binprot record order, plus two leaf facts (the
253-bit VRF truncation and the big-endian ledger hash into SHA-256) that a structure-level read gets
wrong. This module is where the order meets a real chain.

## ⚑ It takes NO ORACLE, and that is the point

`state_hash` is not on Mina's peer-to-peer wire — every node computes it, which is why
`get_best_tip` never sends one. But `previous_state_hash` IS on the wire, in the clear, as the first
32 bytes of every `Protocol_state.Value`. So for a CONSECUTIVE pair:

```text
    deriveStateHash(block_N)  =  block_{N+1}.previous_state_hash
```

Both sides came from the daemon. No transcription of ours is on either side, no explorer is asked,
nothing is compiled but this. A comparison against a value we or openmina computed would be a
differential against another implementation; this is a differential against **the chain**.

If any of the four order traps is wrong, or the VRF is read as 256 bits, or the ledger hash goes
into SHA-256 little-endian, the left side is a different 254-bit number and this file goes red.

## ⚑ And it catches what the 540186 gate structurally cannot

`MinaBinprotRealBlock` checks that the decoder lands on byte 1544 and that the eight fields `select`
reads have openmina's values. A field-order slip *inside* `Blockchain_state` — two adjacent field
elements swapped, say — passes both: the byte count is identical and `select` reads none of them.
It moves the hash preimage. This gate sees it.

## Kernel, and what that costs

⚑ Every theorem below is kernel `decide` — `native_decide` appears nowhere. The generator used to
emit it; that was a tool left behind when the modules were converted on 2026-07-30, which is how a
retired pattern reintroduces itself. Each derivation costs ~9 s of kernel (measured), so the file
states ONE derivation per theorem and gets both refusal polarities for free by instantiating
`MinaStateHashDerive.the_guard_accepts_the_derived_and_refuses_the_rest` — a `∀` over every wrong
hash, which is strictly stronger than sampling two neighbours and costs nothing.

⚑ Only the 1,544-byte PROTOCOL STATE is embedded, not the whole `get_best_tip` payload. The payload
is the protocol state followed by the rest of the block and the proof — 108 KB and 312 KB on the
captured pair — and embedding that produced a 17,600-line file that heartbeat out at `whnf` during
elaboration, before a single theorem ran.

Captured by `bridge/tools/mina-consecutive-pair.py` over Mina's own protocol
(`TCP → pnet → Noise XX → yamux → coda/rpcs/0.0.1 → get_best_tip v2`). REGENERATE, do not edit.
-/
import Dregg2.Bridge.MinaBinprotRealBlock

set_option autoImplicit false
-- ⚑ MEASURED: the Poseidon reductions exhaust 40000 with "maximum recursion depth has been
-- reached" — a limit, not a timeout. Same value as `MinaStateHashDerive`, for the same reason.
set_option maxRecDepth 1000000

namespace Dregg2.Bridge.MinaStateHashRealBlock

open Dregg2.Bridge.MinaBinprot
open Dregg2.Bridge.MinaStateHashDerive

'''


def lean_bytes(name, buf, doc):
    lines = []
    for i in range(0, len(buf), 24):
        lines.append("  " + ", ".join(str(b) for b in buf[i : i + 24]) + ",")
    body = "\n".join(lines).rstrip(",")
    return "/-- %s -/\ndef %s : List Nat := [\n%s]\n" % (doc, name, body)


def emit(path, parent, child, hp, hc, want):
    parts = [LEAN_HEADER]
    parts.append(
        lean_bytes(
            "devnetParent",
            parent,
            "The parent block's `Protocol_state.Value.Stable.V2`, %d bytes, height %s."
            % (len(parent), hp),
        )
    )
    parts.append("\n")
    parts.append(
        lean_bytes(
            "devnetChild",
            child,
            "The CHILD block's `Protocol_state.Value.Stable.V2`, %d bytes, height %s. Its first 32 "
            "bytes are the parent's identity, as the daemon computed it." % (len(child), hc),
        )
    )
    parts.append(
        r'''

/-- The child's `previous_state_hash`, as the daemon computed it. ⚑ This is the ORACLE and it is a
field of the wire, not a value anyone in this repo produced. -/
def childPreviousStateHash : Nat := %d

/-- ⚑ **THE EQUATION.** The identity we compute for the parent, from the parent's bytes, IS the
identity the daemon put in the child's header. Nothing on either side is ours: the left is our
derivation over bytes a peer served, the right is a field of another block the same peer served.

This is the only claim in the tree that can REFUTE the ~1,400-bit order of `Body.to_input`. -/
theorem the_derived_state_hash_is_the_one_the_chain_recorded :
    deriveStateHash devnetParent = some childPreviousStateHash := by decide

/-- The child's own first 32 bytes really are that number, little-endian — so the oracle is read
off the wire and not asserted. -/
theorem the_oracle_is_the_childs_first_thirty_two_bytes :
    leNat (devnetChild.take 32) = childPreviousStateHash := by decide

/-- ⚑ **BOTH POLARITIES, ON REAL BYTES, FOR THE PRICE OF NEITHER.** The honest pair is accepted and
**every** other served hash is refused — a `∀`, not two sampled neighbours — by instantiating the
general guard theorem at the equation above. No second derivation, and a strictly stronger claim
than re-deriving twice would have bought. -/
theorem the_guard_discriminates_on_real_devnet_bytes :
    stateHashMatches devnetParent childPreviousStateHash = true
    ∧ ∀ x, x ≠ childPreviousStateHash → stateHashMatches devnetParent x = false :=
  the_guard_accepts_the_derived_and_refuses_the_rest devnetParent childPreviousStateHash
    the_derived_state_hash_is_the_one_the_chain_recorded

/-- ⚑ **AND IT IS REFUTABLE.** One flipped byte inside the `Blockchain_state` — the region the
fork-choice gate never reads — moves the derived identity.

This is the mutation that matters, and it is the one `MinaBinprotRealBlock` is structurally BLIND
to: the byte count is unchanged, so its exact-fit check passes, and `select` reads nothing there, so
every field assertion passes too. -/
theorem a_flipped_byte_in_the_blockchain_state_moves_the_identity :
    deriveStateHash (devnetParent.set 200 ((devnetParent.getD 200 0 + 1) %% 128))
      ≠ some childPreviousStateHash := by decide

/-- And in `previous_state_hash` itself, which enters the OUTER Poseidon rather than the body. -/
theorem a_flipped_byte_in_the_parent_link_moves_the_identity :
    deriveStateHash (devnetParent.set 0 ((devnetParent.getD 0 0 + 1) %% 128))
      ≠ some childPreviousStateHash := by decide

/-- A truncated protocol state is a REFUSAL, not a hash of what did arrive. -/
theorem a_truncated_protocol_state_is_refused :
    deriveStateHash (devnetParent.take (devnetParent.length - 1)) = none := by decide

/-- ⚑ **AND THE CHILD'S BYTES DO NOT HAVE THE PARENT'S IDENTITY.** Two real blocks, one real hash,
and the PAIRING is what is checked — the case an accepted-carrier design structurally cannot see. -/
theorem the_child_does_not_have_the_parents_identity :
    stateHashMatches devnetChild childPreviousStateHash = false := by decide

/-! ## axiom hygiene — ⚑ **ALL KERNEL.** No `native_decide`, no `sorry`, no axioms. -/

#assert_axioms the_derived_state_hash_is_the_one_the_chain_recorded
#assert_axioms the_oracle_is_the_childs_first_thirty_two_bytes
#assert_axioms the_guard_discriminates_on_real_devnet_bytes
#assert_axioms a_flipped_byte_in_the_blockchain_state_moves_the_identity
#assert_axioms a_flipped_byte_in_the_parent_link_moves_the_identity
#assert_axioms a_truncated_protocol_state_is_refused
#assert_axioms the_child_does_not_have_the_parents_identity

end Dregg2.Bridge.MinaStateHashRealBlock
'''
        % want
    )
    with open(path, "w") as f:
        f.write("".join(parts))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-minutes", type=float, default=25.0)
    ap.add_argument("--interval", type=float, default=45.0)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--from-lean", default=None,
                    help="re-emit from an already-generated module instead of capturing")
    args = ap.parse_args()

    if args.from_lean:
        return reemit(args.from_lean, args.out)

    deadline = time.time() + args.max_minutes * 60
    seen = {}  # blockchain_length -> the TRUNCATED protocol state

    while time.time() < deadline:
        buf = fetch()
        if buf is not None:
            got = parse(buf)
            if got is None:
                log("payload did not decode; discarding rather than embedding it")
            else:
                rec, used = got
                h = rec["cs"]["bl"]
                ps = buf[:used]
                if h not in seen:
                    log("captured height %d: payload %d bytes, protocol state %d"
                        % (h, len(buf), used))
                seen[h] = ps
                for lo in (h - 1, h):
                    hi = lo + 1
                    if lo in seen and hi in seen:
                        return finish(args.out, seen[lo], seen[hi], lo, hi)
        remaining = deadline - time.time()
        if remaining <= 0:
            break
        log("heights so far: %s; sleeping %.0fs" % (sorted(seen), min(args.interval, remaining)))
        time.sleep(min(args.interval, remaining))

    log("NO CONSECUTIVE PAIR within %.1f minutes; heights seen: %s"
        % (args.max_minutes, sorted(seen)))
    log("writing nothing: a fixture that is not what it claims is worse than no fixture")
    return 1


def finish(out, parent, child, hp, hc):
    """Emit, after saying out loud what the Lean gate is about to decide."""
    want = int.from_bytes(child[:32], "little")
    if want >= PALLAS_BASE_MODULUS:
        log("child previous_state_hash is not canonical; refusing to write")
        return 1
    log("CONSECUTIVE PAIR: %d -> %d  (protocol states %d and %d bytes)"
        % (hp, hc, len(parent), len(child)))
    log("child.previous_state_hash = %d" % want)

    # ⚑ This script's OWN verdict, logged and never substituted for the gate's. It shares the
    # reading with the Lean, so agreement here is not evidence -- it is a heads-up about what the
    # build is about to say. A DISAGREEMENT here would mean the two renderings have drifted, and
    # the honest thing is still to write the file and let the kernel report it.
    try:
        rec, _ = _cc.decode(parent)
        mine = _cc.state_hash(rec)
        log("python rendering says: %s" % ("MATCH" if mine == want else "MISMATCH -> %d" % mine))
    except Exception as e:
        log("python rendering could not run (%s); the Lean gate is the verdict anyway" % e)

    emit(out, parent, child, hp, hc, want)
    log("wrote %s (%d bytes)" % (out, os.path.getsize(out)))
    log("now: (cd metatheory && lake build Dregg2.Bridge.MinaStateHashRealBlock)")
    return 0


def reemit(src_path, out):
    """Recover a captured pair from a previously generated module and emit again.

    ⚑ Exists because the capture is the expensive, non-reproducible half: devnet moves on, and a
    generator bug should never cost a fresh 25-minute poll. It also truncates payloads that an
    older generator embedded whole.
    """
    import re as _re
    src = open(src_path).read()

    def grab(name):
        i = src.index("def %s : List Nat := [" % name)
        j = src.index("]", i)
        head = "def %s : List Nat := [" % name
        return bytes(int(x) for x in _re.findall(r"\d+", src[i + len(head):j]))

    par, chi = grab("devnetParent"), grab("devnetChild")
    gp, gc = parse(par), parse(chi)
    if gp is None or gc is None:
        log("recovered bytes do not decode; refusing")
        return 1
    (rp, up), (rc, uc) = gp, gc
    hp, hc = rp["cs"]["bl"], rc["cs"]["bl"]
    if hc != hp + 1:
        log("recovered blocks are NOT consecutive (%d, %d); refusing" % (hp, hc))
        return 1
    log("recovered %d -> %d; truncating %d/%d payload bytes to %d/%d protocol state"
        % (hp, hc, len(par), len(chi), up, uc))
    return finish(out, par[:up], chi[:uc], hp, hc)


if __name__ == "__main__":
    sys.exit(main())
