#!/usr/bin/env bash
# check-p3-rev.sh -- enforce that every hardcoded emberian/plonky3-recursion
# fork rev in the repo matches the single source of truth, scripts/p3-rev.env.
#
# The fork rev resolves the whole workspace's recursion crates and thus the
# compiled verifier. It is pinned in the AUTHORITATIVE workspace deps (root
# Cargo.toml [workspace.dependencies] p3-recursion/p3-circuit/...) and mirrored
# into several CI workflows (sibling-clone REV) and wasm/Cargo.toml's comment.
# All of these MUST stay in lockstep or the built verifier forks silently.
#
# Scoping: root Cargo.toml ALSO pins base upstream Plonky3/Plonky3 at a different
# 40-hex rev, so its p3-recursion rev is isolated by matching only
# `plonky3-recursion` lines (never a blind grep of the whole file). For the CI
# workflows + wasm/Cargo.toml the only 40-hex tokens present are the fork rev.
#
# ALSO enforced (was WARN-only until 2026-07-24): the VK-hash constant
# RECURSION_P3_REV in circuit-prove/src/recursive_witness_bundle.rs. It is the
# proving-system id folded into compute_recursive_vk_hash() -- the value
# lookup_recursive_vk() accepts on, i.e. the light-client trust anchor.
#
# It was excluded as "a VK-epoch event on a human-gated track". That reasoning did
# not survive contact with the code: compute_recursive_vk_hash() is recomputed by
# BOTH producer and verifier from this same constant, and NO golden/frozen hash of
# it exists anywhere in the tree -- so reconciling the string re-keys a value
# nothing external pins. The apex governance anchor DREGG_APEX_RECURSION_VK is a
# blake3 fingerprint of VK MATERIAL (recursion_vk_fingerprint) and does not read
# this constant at all. VK-CEREMONY.md's own cutover lists the reconcile as step
# (3) of §6.1, independent of ceremony output -- it was bundled into a BLOCKED
# ceremony, which is how it stayed drifted while the gate could not fail.
#
# A gate that cannot fail is not a gate (cf. scripts/check-mirror-gates.sh: "a
# gate that cannot bark is worse than none"), and this is the one consumer whose
# drift is directly security-relevant. It FAILS here.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
env_file="$repo_root/scripts/p3-rev.env"

if [[ ! -f "$env_file" ]]; then
  echo "FAIL: single-source env missing: $env_file" >&2
  exit 1
fi
# shellcheck source=/dev/null
. "$env_file"

if [[ ! "${P3_REV:-}" =~ ^[0-9a-f]{40}$ ]]; then
  echo "FAIL: P3_REV in $env_file is not a 40-hex rev: '${P3_REV:-<unset>}'" >&2
  exit 1
fi

status=0

# --- Consumers whose ONLY 40-hex tokens are the fork rev: grep the whole file.
blind_files=(
  ".github/workflows/extension.yml"
  ".github/workflows/publish-sdk-ts.yml"
  ".github/workflows/pages.yml"
  "wasm/Cargo.toml"
)
for rel in "${blind_files[@]}"; do
  f="$repo_root/$rel"
  if [[ ! -f "$f" ]]; then
    echo "FAIL: consumer file missing: $rel" >&2
    status=1
    continue
  fi
  # A lockstep gate whose grep matches NOTHING passes having checked nothing: if a
  # consumer silently loses its pinned rev (line deleted / comment dropped / dep
  # restructured), the loop body never runs and no mismatch is reported. Count the
  # matches and FAIL LOUD on zero — a vanished mirror is a lockstep break, not a pass.
  seen=0
  while IFS= read -r rev; do
    [[ -z "$rev" ]] && continue
    seen=$((seen + 1))
    if [[ "$rev" != "$P3_REV" ]]; then
      echo "FAIL: $rel pins plonky3 rev $rev, expected $P3_REV" >&2
      status=1
    fi
  done < <(grep -ioE '[0-9a-f]{40}' "$f" | sort -u)
  if [[ "$seen" -eq 0 ]]; then
    echo "FAIL: $rel no longer contains the pinned fork rev — the lockstep gate would" >&2
    echo "      otherwise PASS having checked nothing here. Restore the pin, or drop $rel" >&2
    echo "      from blind_files if it is intentionally no longer a mirror." >&2
    status=1
  fi
done

# --- Authoritative workspace pin: isolate the plonky3-recursion rev only
# (base Plonky3/Plonky3 is legitimately a different rev in the same file).
cargo="$repo_root/Cargo.toml"
if [[ ! -f "$cargo" ]]; then
  echo "FAIL: root Cargo.toml missing" >&2
  status=1
else
  seen=0
  while IFS= read -r rev; do
    [[ -z "$rev" ]] && continue
    seen=$((seen + 1))
    if [[ "$rev" != "$P3_REV" ]]; then
      echo "FAIL: root Cargo.toml pins plonky3-recursion rev $rev, expected $P3_REV" >&2
      status=1
    fi
  done < <(grep 'plonky3-recursion' "$cargo" | grep -ioE '[0-9a-f]{40}' | sort -u)
  # The AUTHORITATIVE pin. If this yields zero (the `plonky3-recursion` dep line was
  # renamed or removed), the gate anchors on nothing and every consumer check above is
  # meaningless — the whole gate silently greens. That is the exact failure this gate
  # exists to prevent, turned on itself. FAIL LOUD.
  if [[ "$seen" -eq 0 ]]; then
    echo "FAIL: root Cargo.toml yielded NO plonky3-recursion rev — the authoritative pin" >&2
    echo "      the entire lockstep gate anchors on has vanished (dep renamed/removed?)." >&2
    echo "      The gate cannot verify lockstep against a missing source of truth." >&2
    status=1
  fi
fi

# --- ENFORCED: the VK-hash constant. This is the MOST load-bearing consumer, not
# the least: RECURSION_P3_REV is folded into compute_recursive_vk_hash(), the value
# lookup_recursive_vk() accepts on -- the light-client trust anchor's proving-system id.
vk="$repo_root/circuit-prove/src/recursive_witness_bundle.rs"
if [[ ! -f "$vk" ]]; then
  echo "FAIL: VK-hash consumer missing: circuit-prove/src/recursive_witness_bundle.rs" >&2
  status=1
else
  vk_rev="$(grep 'RECURSION_P3_REV' "$vk" | grep -ioE '[0-9a-f]{40}' | head -1 || true)"
  if [[ -z "$vk_rev" ]]; then
    echo "FAIL: RECURSION_P3_REV in recursive_witness_bundle.rs carries no 40-hex rev --" >&2
    echo "      the VK-hash proving-system id has vanished and this check would otherwise" >&2
    echo "      PASS having checked nothing (same vanished-pin class as above)." >&2
    status=1
  elif [[ "$vk_rev" != "$P3_REV" ]]; then
    echo "FAIL: RECURSION_P3_REV in recursive_witness_bundle.rs is $vk_rev, not $P3_REV" >&2
    echo "      The deployed recursive VK hash therefore advertises a proving system that" >&2
    echo "      is NOT the one compiled in (Cargo.lock resolves $P3_REV). Old recursive" >&2
    echo "      proofs built against $vk_rev stay indistinguishable-by-VK-hash from" >&2
    echo "      current ones -- the exact failure this constant exists to prevent." >&2
    echo "      FIX: reconcile the constant with the rev Cargo.lock establishes." >&2
    echo "      This re-keys compute_recursive_vk_hash(), which NOTHING external pins" >&2
    echo "      (lookup_recursive_vk recomputes it; the apex anchor DREGG_APEX_RECURSION_VK" >&2
    echo "      is a fingerprint of VK MATERIAL and is unaffected). It is not a ceremony." >&2
    status=1
  fi
fi

if [[ "$status" -eq 0 ]]; then
  echo "OK: all lockstep plonky3-recursion revs match P3_REV=$P3_REV"
fi
exit "$status"
