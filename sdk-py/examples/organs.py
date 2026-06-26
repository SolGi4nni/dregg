"""The organ nouns in Python — trustline, channels, mailbox, attested-query.

These are the higher primitives (docs/ORGANS.md): the ergonomic Python face of
the node's operator-local services. The node computes the per-cell factory
descriptors and seal fan-outs the wire layer does not carry; these clients
drive them. The enforcement tooth is the executor-installed cell program.

The operator-gated organs (trustline, channels) need the node operator's
credential — pass `devnet_key=` (or set `$DREGG_API_TOKEN`). The relay
(mailbox) is owner-signed; the attested-query reads are public.

    DREGG_API_TOKEN=... DREGG_NODE_URL=https://devnet… python examples/organs.py
"""

import os

import dregg

NODE = os.environ.get("DREGG_NODE_URL", "http://localhost:8421")
RELAY = os.environ.get("DREGG_RELAY_URL", "http://localhost:3100")
KEY = os.environ.get("DREGG_API_TOKEN")


def ensure(name: str) -> dregg.Identity:
    """Load a named profile, creating it on first run."""
    try:
        return dregg.Identity.from_profile(name)
    except dregg.DreggError:
        return dregg.Identity.create(name)


issuer = ensure("organs-issuer")
holder = ensure("organs-holder")
print(f"issuer: {issuer.cell_id[:16]}…   holder: {holder.cell_id[:16]}…")

# ── Attested query — the public read surface (no identity, no signing) ──
aq = dregg.AttestedQuery(NODE)
try:
    cp = aq.checkpoint()
    print(f"\ncheckpoint @ height {cp.get('height')} — {cp.get('qc_votes')} qc votes")
except dregg.DreggError as e:
    print(f"\n(checkpoint read unavailable: {e})")

# ── Trustline — the bilateral line of credit (ORGANS §1) ──
if KEY:
    tl = issuer.trustline(NODE, devnet_key=KEY)
    line = tl.open(holder.cell_id, 1000)            # four-turn funded birth
    print(f"\ntrustline opened: {line['trustline'][:16]}…  line={line['line']}")
    tl.draw(line["trustline"], 250)                 # debit the shared counter
    tl.repay(line["trustline"], 100)                # restore the line
    pos = tl.status(line["trustline"])
    print(f"  drawn={pos['drawn']} remaining={pos['remaining']} open={pos['open']}")

    # ── Channels — the group-key epoch lift (ORGANS §4) ──
    # seal_pk is each member's X25519 public key; compute it with the Rust SDK
    # / node tooling (the TS wire layer carries no X25519). Here we only show
    # the SHAPE — a real run supplies real seal keys.
    # ch = issuer.channels(NODE, devnet_key=KEY)
    # g = ch.create(7, [{"cell": holder.cell_id, "seal_pk": holder_seal_hex}])
    # ch.remove(g["channel"], holder.cell_id)   # darkened in ONE epoch step
else:
    print("\n(no DREGG_API_TOKEN — skipping operator-gated trustline/channels)")

# ── Mailbox — a hosted inbox over the relay (ORGANS §2) ──
# Membership ops are Ed25519-signed by the owner; sealing/custody-verification
# happen outside pure Python (bring sealed ciphertext, recompute content_hash).
print(f"\nmailbox owner (inbox id): {holder.mailbox(RELAY).owner[:16]}…")
print("(subscribe/drain need a running relay; see docs/ORGANS.md §2)")
