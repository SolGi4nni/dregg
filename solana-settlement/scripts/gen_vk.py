#!/usr/bin/env python3
"""DEPRECATED shim — kept so the old path still works.

The Solana `vk.rs` is no longer generated here from the Solidity verifier. It is now
emitted, together with the EVM and Cosmos VK encodings, from the ONE canonical spec
`chain/codegen/dregg_vk.json` by `chain/codegen/gen_verifiers.py`. This shim just
delegates there, so there is a single source and the three chains cannot drift.

  Regenerate all three verifiers:  python3 chain/codegen/gen_verifiers.py
"""
import pathlib
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parents[2]

if __name__ == "__main__":
    print(
        "gen_vk.py is DEPRECATED: the Solana/EVM/Cosmos VKs are generated together "
        "from chain/codegen/dregg_vk.json.\nDelegating to chain/codegen/gen_verifiers.py ...",
        file=sys.stderr,
    )
    sys.exit(
        subprocess.run(
            [sys.executable, str(REPO / "chain/codegen/gen_verifiers.py")]
        ).returncode
    )
