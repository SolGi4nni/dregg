#!/usr/bin/env bash
# check-vk-pin-literals.sh — every `*_VK_LANES` literal, resolved against the served tree IN LEAN.
#
# ⚑ WHAT THIS IS THE PAYOFF OF. A `vk_pin` is nine `Faithful9` lanes of a descriptor's semantic
# fingerprint. Until `Dregg2.Circuit.DescriptorCanonical` landed, an AIR author could not produce
# that value in Lean at all — the canonical ENCODER was Rust-only — so fourteen `*_VK_LANES`
# constants across seven modules are digits somebody ran a Rust tool for and TYPED IN.
#
# `metatheory/CheckVkPinLiterals.lean` recomputes the whole chain in Lean, with no Rust anywhere in
# the path, for every served descriptor, and asks of each literal: WHICH SERVED DESCRIPTOR DO YOU
# PIN? It resolves BY VALUE — there is no literal-to-file table anywhere, because a stale map is
# invisible in exactly the way the literals are.
#
# HARD failures:
#   * a literal that is not nine non-negative lanes;
#   * a deliberate `FORGED_*` falsifier that MATCHES a served descriptor — a forged pin naming a
#     real program is a falsifier that has stopped falsifying, and the leg it powers became
#     satisfiable while its refusal test kept reporting green.
#
# ⚠ It does NOT adjudicate a live literal that matches nothing. Which literal is wrong versus which
# descriptor moved is a question about THIS tree, not a fact, and
# `circuit/tests/vk_pin_closure_over_the_served_tree.rs` already carries that verdict — a second copy
# would be a twin, not a second witness. Pass `--strict` to make it exit 1.
#
# ⚠ NEVER runs a descriptor regen. `DREGG_DESCRIPTOR_ROOT` retargets it at a materialised tree.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DESC_ROOT="${DREGG_DESCRIPTOR_ROOT:-$ROOT/circuit/descriptors}"

cd "$ROOT/metatheory"
lake build Dregg2.Circuit.DescriptorCanonicalJson
exec lake env lean --run CheckVkPinLiterals.lean "$DESC_ROOT" "$@"
