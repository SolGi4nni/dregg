#!/usr/bin/env python3
r"""Author and assemble the Path of Angels Galley activated-content artifacts.

This script is CEREMONY TOOLING, not semantics.  It carries no reducer, no
transition, and no validity rule.  It emits candidate bytes; the authority that
accepts or refuses them is Lean:

  * `ActivatedContent.decodeManifest` (metatheory/.../ActivatedContent.lean:259)
    parses the manifest, RE-ENCODES it with `Manifest.toJson`, and demands byte
    equality (`decodeManifest_reencodes`, :262).  A manifest this script gets
    wrong is refused, not reinterpreted.
  * `GalleyMaintenanceDailyRuntime.decodePolicy` (…Runtime.lean:575) does the
    same for the embedded policy component (`decodePolicy_reencodes`, :578).
  * every component `sha256` is recomputed from `bytes_utf8` by Lean
    (`Component.validB`, ActivatedContent.lean:157) and the manifest root is
    recomputed by `manifestRoot?` (:129).

So the only thing this file can do wrong is produce something that refuses.

WHAT IT WRITES (all under poa/artifacts/galley/epoch-1/)

  policy.json    the exact `PolicyWire.toJson` bytes of the authored Galley
                 policy component, NO trailing newline.
  manifest.json  the exact `Manifest.toJson` bytes of the one-component
                 activated-content manifest that embeds policy.json verbatim,
                 NO trailing newline.  This is the file the node installs.
  world.json     provenance: the content_root the curator must sign, the
                 component digest, and every preimage used below.  It is NOT
                 consumed by any program; the authoritative world identity the
                 curator signs comes from `dregg-node poa-galley-world-preview`,
                 which derives `activation_digest` through poa-curator rather
                 than reimplementing it here.

BYTE DISCIPLINE

Lean's `String.quote` (Init/Data/Repr.lean:400) escapes exactly `"` -> `\"`,
`\` -> `\\`, `\n`, `\t`, and emits `\xNN` (NOT valid JSON) for any byte <= 0x1f
or 0x7f.  Python's `json.dumps` agrees with it on `"` and `\` and on nothing
else that could appear here, so this script REFUSES any authored byte outside
printable ASCII rather than emitting something whose two encoders disagree.

USAGE
  scripts/poa-galley-content.py emit    # (re)write the three artifacts
  scripts/poa-galley-content.py check   # recompute and diff; exit 1 on drift
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT_DIR = os.path.join(REPO, "poa", "artifacts", "galley", "epoch-1")
DEPLOYMENT = os.path.join(REPO, "poa", "deployments", "epoch-1", "poa-devnet.json")
RUNTIME_LEAN = os.path.join(
    REPO, "metatheory", "Dregg2", "Games", "PathOfAngels",
    "GalleyMaintenanceDailyRuntime.lean",
)

MANIFEST_FORMAT = "POA-ACTIVATED-CONTENT-MANIFEST-1"          # ActivatedContent.lean:53
GALLEY_POLICY_COMPONENT = "poa.galley-maintenance-daily.policy.v1"  # :54
CONTENT_EPOCH = 1

# `content_session` follows the POAG1 convention of an ASCII tag zero-padded to
# 32 bytes — Signal's is b"POA-SIG-1" (poa/artifacts/poag1/catalog.json).
CONTENT_SESSION_TAG = b"POA-GALLEY-1"

DERIVE_DOMAIN = b"POA-GALLEY-CONTENT-V1"


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def preimage(federation_id: str, field: str, label: str) -> bytes:
    """Every authored digest below is SHA-256 of exactly these bytes, so a reader
    can recompute any of them without trusting this file."""
    return b"\x00".join([
        DERIVE_DOMAIN,
        federation_id.encode("ascii"),
        str(CONTENT_EPOCH).encode("ascii"),
        field.encode("ascii"),
        label.encode("ascii"),
    ])


def ascii_only(name: str, value: str) -> str:
    for ch in value:
        if not (0x20 <= ord(ch) <= 0x7E):
            raise SystemExit(
                f"{name} contains byte {ord(ch):#04x}; Lean's String.quote would "
                "emit a \\xNN escape that is not valid JSON"
            )
    return value


def quote(value: str) -> str:
    """JSON string literal, agreeing with Lean `String.quote` on printable ASCII."""
    return json.dumps(ascii_only("component bytes", value), ensure_ascii=False)


# ---------------------------------------------------------------------------
# THE AUTHORED CONTENT
#
# The Galley Maintenance Daily as it ships: a station galley that must be
# provisioned every day, and every angel who passes through stands exactly one
# watch.  Twenty-four watches provision it.  There is no advantage state — the
# shipped Runtime carries none (see the zero anchors below).
# ---------------------------------------------------------------------------

DIGEST_LABELS = {
    "daily_id": "the-galley-maintenance-daily/first-light",
    "genesis_head": "stream-genesis-head/first-light",
    "event_id": "daily-event/first-light",
    "public_activity_id": "activity/stand-a-watch-in-the-galley",
    "scene_content_id": "scene/the-galley-at-first-light",
    "public_action_content_id": "action/stand-a-watch",
    "sponsor_action_content_id": "action/holder-sponsorship-unreachable",
    "complete_content_id": "scene/the-galley-provisioned",
}

# Inert by construction.  `reduce_preserves_advantage_anchors`
# (…Runtime.lean:716) proves these four fields are identical across every
# accepted transition, and the shipped Runtime has no power/loot/canon state for
# them to root.  A derived nonzero digest here would claim a tree that does not
# exist, so they are the zero root and revision 0.
ZERO_ROOT = "00" * 32

PUBLIC_SERVICE = 1        # one visitor stands one watch
SPONSOR_SERVICE = 1       # the sponsor path is structurally unreachable (G7)
SERVICE_TARGET = 24       # twenty-four watches provision the galley; MAX_EVENTS is 64

# Inert in the shipped Runtime: `dregg_mint` and `snapshot_slot` are encoded,
# decoded and digested, and read by nothing (grep: …Runtime.lean:102,265,431 and
# no other site).  Authoring a nonzero mint would assert a mint that no code
# performs, so they are zero.
DREGG_MINT = 0
SNAPSHOT_SLOT = 0


def build_policy(deployment_id: str, federation_id: str, rules_digest: str) -> tuple[str, dict]:
    """Return the exact `PolicyWire.toJson` bytes and the preimage record.

    KEY ORDER IS THE WIRE.  This order is `PolicyWire.toJson`
    (…Runtime.lean:260-281); any other order refuses in `canonicalDecode`.
    """
    digests = {
        field: sha256_hex(preimage(federation_id, field, label))
        for field, label in DIGEST_LABELS.items()
    }
    policy = (
        "{"
        f'"deployment_id":"{deployment_id}"'
        f',"federation_id":"{federation_id}"'
        f',"daily_id":"{digests["daily_id"]}"'
        f',"genesis_head":"{digests["genesis_head"]}"'
        f',"dregg_mint":{DREGG_MINT}'
        f',"snapshot_slot":{SNAPSHOT_SLOT}'
        f',"content_epoch":{CONTENT_EPOCH}'
        f',"event_id":"{digests["event_id"]}"'
        f',"rules_digest":"{rules_digest}"'
        f',"public_activity_id":"{digests["public_activity_id"]}"'
        f',"scene_content_id":"{digests["scene_content_id"]}"'
        f',"public_action_content_id":"{digests["public_action_content_id"]}"'
        f',"sponsor_action_content_id":"{digests["sponsor_action_content_id"]}"'
        f',"complete_content_id":"{digests["complete_content_id"]}"'
        f',"public_service":{PUBLIC_SERVICE}'
        f',"sponsor_service":{SPONSOR_SERVICE}'
        f',"service_target":{SERVICE_TARGET}'
        f',"power_root":"{ZERO_ROOT}"'
        f',"loot_root":"{ZERO_ROOT}"'
        f',"canon_root":"{ZERO_ROOT}"'
        f',"canon_revision":0'
        "}"
    )
    record = {
        field: {
            "label": label,
            "preimage_utf8": preimage(federation_id, field, label).decode("ascii").replace("\x00", "\\0"),
            "sha256": digests[field],
        }
        for field, label in DIGEST_LABELS.items()
    }
    return ascii_only("policy", policy), record


def build_manifest(federation_id: str, content_session: str, policy: str) -> str:
    """Return the exact `Manifest.toJson` bytes (ActivatedContent.lean:119)."""
    component_sha256 = sha256_hex(policy.encode("utf-8"))
    manifest = (
        "{"
        f'"format":"{MANIFEST_FORMAT}"'
        ',"scope":{'
        f'"federation_id":"{federation_id}"'
        f',"content_session":"{content_session}"'
        f',"content_epoch":{CONTENT_EPOCH}'
        "}"
        ',"legacy_whole_pack_sha256":null'
        ',"components":[{'
        f'"name":"{GALLEY_POLICY_COMPONENT}"'
        f',"sha256":"{component_sha256}"'
        f',"bytes_utf8":{quote(policy)}'
        "}]}"
    )
    return manifest


def assemble() -> dict[str, str]:
    with open(DEPLOYMENT, "rb") as handle:
        deployment = json.loads(handle.read())
    deployment_id = deployment["deployment_id"]
    federation_id = deployment["federation_id"]
    with open(RUNTIME_LEAN, "rb") as handle:
        rules_digest = sha256_hex(handle.read())
    content_session = (
        CONTENT_SESSION_TAG.hex() + "00" * (32 - len(CONTENT_SESSION_TAG))
    )

    policy, preimages = build_policy(deployment_id, federation_id, rules_digest)
    manifest = build_manifest(federation_id, content_session, policy)
    world = {
        "schema": "POA-GALLEY-CONTENT-PROVENANCE-V1",
        "note": (
            "Provenance only. The world identity the curator signs is emitted by "
            "`dregg-node poa-galley-world-preview`, which derives activation_digest "
            "from the verified POAG1 content-epoch envelope through poa-curator."
        ),
        "deployment_id": deployment_id,
        "federation_id": federation_id,
        "content_session": content_session,
        "content_session_ascii_tag": CONTENT_SESSION_TAG.decode("ascii"),
        "content_epoch": CONTENT_EPOCH,
        "content_root": sha256_hex(manifest.encode("utf-8")),
        "component_name": GALLEY_POLICY_COMPONENT,
        "component_sha256": sha256_hex(policy.encode("utf-8")),
        "rules_digest": {
            "source": "metatheory/Dregg2/Games/PathOfAngels/GalleyMaintenanceDailyRuntime.lean",
            "sha256": rules_digest,
            "note": (
                "SHA-256 of the exact shipped-runtime source at authoring time. It is "
                "bound into every action-token preimage (…Runtime.lean:793) and is "
                "verified against nothing at runtime; editing that file makes this "
                "artifact stale and requires re-emitting and a new signed activation."
            ),
        },
        "derived_digest_preimages": preimages,
        "service": {
            "public_service": PUBLIC_SERVICE,
            "sponsor_service": SPONSOR_SERVICE,
            "service_target": SERVICE_TARGET,
            "note": (
                "Completion is localServiceTotal >= service_target (…Runtime.lean:845); "
                "one distinct player per public play, so 24 players provision the galley "
                "inside the 64-event MAX_EVENTS cap."
            ),
        },
    }
    return {
        "policy.json": policy,
        "manifest.json": manifest,
        "world.json": json.dumps(world, indent=2, sort_keys=False) + "\n",
    }


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else "emit"
    if mode not in {"emit", "check"}:
        print(__doc__)
        return 2
    files = assemble()
    if mode == "emit":
        os.makedirs(OUT_DIR, exist_ok=True)
        for name, body in files.items():
            with open(os.path.join(OUT_DIR, name), "w", encoding="utf-8", newline="") as handle:
                handle.write(body)
            print(f"wrote {os.path.relpath(os.path.join(OUT_DIR, name), REPO)} "
                  f"({len(body.encode('utf-8'))} bytes)")
        print(f"content_root  = {sha256_hex(files['manifest.json'].encode('utf-8'))}")
        print(f"component_sha = {sha256_hex(files['policy.json'].encode('utf-8'))}")
        return 0
    drift = 0
    for name, body in files.items():
        path = os.path.join(OUT_DIR, name)
        try:
            with open(path, "rb") as handle:
                on_disk = handle.read()
        except FileNotFoundError:
            print(f"MISSING {name}")
            drift += 1
            continue
        if on_disk != body.encode("utf-8"):
            print(f"DRIFT {name}")
            drift += 1
    if drift:
        print("re-run `scripts/poa-galley-content.py emit`; a signed activation "
              "must be re-issued because content_root changes")
        return 1
    print("poa galley content artifacts are byte-exact")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
