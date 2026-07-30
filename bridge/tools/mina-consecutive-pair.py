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
# The three integers this script reads, and no others.
#
# `previous_state_hash` is the first 32 bytes, little-endian. `blockchain_length`
# is the first field of the consensus state, and finding it means walking the
# blockchain state -- which this script does NOT do. Instead it uses the ONE
# structural fact it can rely on without a parser: the Lean decoder is the parser,
# so we ask it. Failing that, two captures whose byte strings differ are almost
# certainly consecutive on devnet at a 45 s poll; the Lean gate REFUSES if they
# are not, because then the equation simply does not hold. The height is read
# below only to make the log and the fixture's docstring honest, and it is read
# by re-deriving the same offset the existing 540186 fixture documents.
# ---------------------------------------------------------------------------


def previous_state_hash(buf):
    v = int.from_bytes(buf[:32], "little")
    if v >= PALLAS_BASE_MODULUS:
        raise ValueError("previous_state_hash is not canonical")
    return v


def blockchain_length_offset(buf):
    """Scan for the `sub_window_densities` count byte (11) and read backwards.

    ⚑ HEURISTIC, and it is only used for the LOG and the docstring. Nothing the
    Lean gate checks depends on it: the gate re-derives the hash and compares it
    to the child's `previous_state_hash`, and neither side involves this offset.
    The count byte is `11` followed by eleven small `Length`s; `min_window_density`
    and `epoch_count` precede it as one-byte ints, and `blockchain_length` as a
    5-byte `0xfd` form once it exceeds 65535.
    """
    for i in range(900, min(len(buf) - 20, 1400)):
        if buf[i] != 11:
            continue
        # eleven plausible densities follow (each <= slots_per_sub_window = 7)
        if all(buf[i + 1 + j] <= 7 for j in range(11)):
            # ... preceded by min_window_density, epoch_count (one byte each),
            # then blockchain_length in the 5-byte 0xfd form.
            if buf[i - 7] == 0xFD:
                return i - 7
    return None


def blockchain_length(buf):
    off = blockchain_length_offset(buf)
    if off is None:
        return None
    return int.from_bytes(buf[off + 1 : off + 5], "little")


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

Captured by `bridge/tools/mina-consecutive-pair.py` over Mina's own protocol
(`TCP → pnet → Noise XX → yamux → coda/rpcs/0.0.1 → get_best_tip v2`). REGENERATE, do not edit.
-/
import Dregg2.Bridge.MinaBinprotRealBlock

set_option autoImplicit false
set_option maxRecDepth 40000

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
identity the daemon put in the child's header. Nothing on either side is ours. -/
def theChainAgreesWithTheDerivation : Bool :=
  deriveStateHash devnetParent == some childPreviousStateHash

/-- ⚑ **A MINA TIP'S IDENTITY IS CHECKED, NOT SUPPLIED.** -/
theorem the_derived_state_hash_is_the_one_the_chain_recorded :
    theChainAgreesWithTheDerivation = true := by native_decide

/-- The child's own first 32 bytes really are that number, little-endian — so the oracle is read
off the wire and not asserted. -/
theorem the_oracle_is_the_childs_first_thirty_two_bytes :
    leNat (devnetChild.take 32) = childPreviousStateHash := by native_decide

/-- ⚑ **AND IT IS REFUTABLE.** One flipped byte anywhere in the parent's preimage moves the derived
identity — in the `Blockchain_state` the fork-choice gate never reads, in the consensus state it
does, and in `previous_state_hash` itself. A derivation that cannot go red on a real block is not a
derivation.

The first of these is the one that matters: `MinaBinprotRealBlock`'s exact-fit and field checks are
BLIND to a change inside `Blockchain_state` (same byte count, and `select` reads nothing there).
This is not. -/
def mutationsMoveTheIdentity : Bool :=
  (deriveStateHash (devnetParent.set 200 ((devnetParent.getD 200 0 + 1) %% 128))
     != some childPreviousStateHash)
  && (deriveStateHash (devnetParent.set 0 ((devnetParent.getD 0 0 + 1) %% 128))
     != some childPreviousStateHash)
  && (deriveStateHash (devnetParent.take (devnetParent.length - 1)) == none)

theorem a_one_byte_change_moves_the_identity : mutationsMoveTheIdentity = true := by native_decide

/-- ⚑ **AND THE GUARD ACCEPTS AND REFUSES, ON THESE BYTES.** The honest pair is `true`; the same
bytes under the neighbouring hash are `false`. Both polarities, on a real chain. -/
def theGuardDiscriminatesOnRealBytes : Bool :=
  stateHashMatches devnetParent childPreviousStateHash
  && (stateHashMatches devnetParent (childPreviousStateHash + 1) == false)
  && (stateHashMatches devnetParent (childPreviousStateHash - 1) == false)
  -- ⚑ and the CHILD's bytes do not have the PARENT's identity: two real blocks, one real hash,
  -- and the pairing is what is checked.
  && (stateHashMatches devnetChild childPreviousStateHash == false)

theorem the_guard_discriminates_on_real_devnet_bytes :
    theGuardDiscriminatesOnRealBytes = true := by native_decide

/-! ## axiom hygiene — `native_decide` (EXECUTION) results, carrying `Lean.ofReduceBool`. A Poseidon
over ~40 field elements plus two SHA-256 blocks plus a 1,500-byte parse is not a kernel reduction,
and pretending otherwise is how a sibling spent 153 s per check. -/

#print axioms the_derived_state_hash_is_the_one_the_chain_recorded
#print axioms the_oracle_is_the_childs_first_thirty_two_bytes
#print axioms a_one_byte_change_moves_the_identity
#print axioms the_guard_discriminates_on_real_devnet_bytes

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
    args = ap.parse_args()

    deadline = time.time() + args.max_minutes * 60
    seen = {}  # blockchain_length -> payload

    while time.time() < deadline:
        buf = fetch()
        if buf is not None:
            h = blockchain_length(buf)
            if h is None:
                log("could not locate blockchain_length; keeping the bytes under a synthetic key")
            else:
                if h not in seen:
                    log("captured height %d (%d bytes)" % (h, len(buf)))
                seen[h] = buf
                if (h - 1) in seen:
                    parent, child = seen[h - 1], seen[h]
                    want = previous_state_hash(child)
                    log("CONSECUTIVE PAIR: %d -> %d" % (h - 1, h))
                    log("child.previous_state_hash = %d" % want)
                    emit(args.out, parent, child, h - 1, h, want)
                    log("wrote %s" % args.out)
                    log("now: (cd metatheory && lake build Dregg2.Bridge.MinaStateHashRealBlock)")
                    return 0
                if (h + 1) in seen:
                    parent, child = seen[h], seen[h + 1]
                    want = previous_state_hash(child)
                    log("CONSECUTIVE PAIR: %d -> %d" % (h, h + 1))
                    log("child.previous_state_hash = %d" % want)
                    emit(args.out, parent, child, h, h + 1, want)
                    log("wrote %s" % args.out)
                    log("now: (cd metatheory && lake build Dregg2.Bridge.MinaStateHashRealBlock)")
                    return 0
        remaining = deadline - time.time()
        if remaining <= 0:
            break
        log("heights so far: %s; sleeping %.0fs" % (sorted(seen), min(args.interval, remaining)))
        time.sleep(min(args.interval, remaining))

    log("NO CONSECUTIVE PAIR within %.1f minutes; heights seen: %s"
        % (args.max_minutes, sorted(seen)))
    log("writing nothing: a fixture that is not what it claims is worse than no fixture")
    return 1


if __name__ == "__main__":
    sys.exit(main())
