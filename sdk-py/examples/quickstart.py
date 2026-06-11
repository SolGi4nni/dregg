"""dregg in 15 lines of Python — mirrors QUICKSTART.md against the devnet.

Run after `maturin develop` (or installing the wheel):

    DREGG_API_TOKEN=... python examples/quickstart.py

The devnet protects the /api/turns/* ingress behind a bearer token; reads
and the receipt stream are public. Without a token this still demonstrates
identity, building, signing, and the faithful explain — only `.submit()`
needs the ingress.
"""

import os
import sys

import dregg

NODE = os.environ.get("DREGG_NODE_URL", "https://devnet.dregg.fg-goose.online")

# 1. A named identity (shared store with `dregg id create/use` and the Rust
#    SDK: ~/.dregg/profiles/<name>.json).
try:
    ident = dregg.Identity.from_profile("quickstart-py")
except dregg.DreggError:
    ident = dregg.Identity.create("quickstart-py")
print(f"identity  : {ident.name} ({ident.public_key[:16]}…)")
print(f"agent cell: {ident.cell_id}")

# 2. Build → sign. The system never signs blind: read the clerk's faithful
#    explanation of exactly what the signature covers.
recipient = "28c2cba0ccfd29e8c2cb2773f398dfb652a94fa49dbcb143643cd4df847a076f"
signed = (
    ident.turn(NODE)
    .transfer(recipient, 100)
    .memo("hello from the python sdk")
    .sign()
)
print("\n--- what was signed ---")
print(signed.explain())

# 3. Submit. A refusal raises DreggRefused carrying the node's reason and
#    the explanation — the system teaches when it says no.
if not os.environ.get("DREGG_API_TOKEN"):
    print("(no DREGG_API_TOKEN set; skipping submit — see QUICKSTART.md §3)")
    sys.exit(0)

try:
    receipt = signed.submit()
except dregg.DreggRefused as refusal:
    print(f"refused:\n{refusal}")
    sys.exit(1)

print(f"\ncommitted : {receipt.turn_hash}")
print(f"as dict   : {receipt.to_dict()}")
proof = receipt.proof()
print(f"proof     : {'attached, ' + str(proof['proof_len']) + ' bytes' if proof else 'pending (the STARK is additive attestation)'}")

# 4. The receipt nervous system: watch the next few commits land, live.
print("\nwatching the receipt stream (ctrl-c to stop)…")
for i, r in enumerate(dregg.subscribe(NODE)):
    print(f"  receipt: turn={r.turn_hash[:16]}… kinds={r.get('kinds')}")
    if i >= 4:
        break
