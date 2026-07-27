#!/usr/bin/env bash
# scripts/ci.sh — portable, OS-detecting, from-scratch build + honest verify gate
# for drorb. One command a fresh checkout (macOS or Linux) can run to reproduce
# the whole verification: it builds the FFI prerequisites, runs the HONEST
# from-scratch proof build, a tree-wide `sorry`/`sorryAx` scan, links the native
# dataplane, and (unless --quick) drives the conformance suite — failing on any
# real regression.
#
# Usage:
#   scripts/ci.sh            full gate: build + sorry-scan + dataplane link + conformance
#   scripts/ci.sh --quick    fast gate: build + sorry-scan + dataplane link (skip conformance)
#   scripts/ci.sh --cross-nat  ALSO run the cross-NAT hole-punching gate
#                            (scripts/cross-nat-tailnet.sh selftest). OPT-IN: it needs
#                            root, Linux netns and a free 10.77.0.0/16, so it cannot be
#                            the default. Combinable with --quick. Without it the gate
#                            is NOT run and this script SAYS SO — the cross-NAT result
#                            is otherwise a dated my-hand claim that nothing re-checks.
#   scripts/ci.sh --help
#
# Environment (auto-set to the project convention when unset; override to point
# elsewhere):
#   HACL_DIST   HACL*/EverCrypt gcc-compatible dist. Must contain libevercrypt.a
#               and the extracted EverCrypt_*.h headers.
#               Default: $HOME/src/hacl-star/dist/gcc-compatible
#   KRML        KaRaMeL runtime headers (for the crypto shims).
#               Default: $(dirname "$HACL_DIST")/karamel
#   QUIC_VENV   Python venv with aioquic for the QUIC/H3 conformance client
#               (optional; those scenarios SKIP cleanly without it).
#
# The honest gate is FROM-SCRATCH (`rm -rf .lake/build && lake build`), never an
# incremental rebuild: stale oleans can mask a proof that no longer closes, so a
# green incremental build is not evidence. See BUILD.md.
set -euo pipefail

# --------------------------------------------------------------------------- #
# Locate the repo root (this script lives in scripts/).
# --------------------------------------------------------------------------- #
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

QUICK=0
CROSSNAT=0
for arg in "$@"; do
  case "$arg" in
    --quick) QUICK=1 ;;
    --cross-nat) CROSSNAT=1 ;;
    -h|--help)
      sed -n '2,32p' "$HERE/ci.sh" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) echo "ci.sh: unknown argument: $arg (try --help)" >&2; exit 2 ;;
  esac
done

# --------------------------------------------------------------------------- #
# Pretty logging.
# --------------------------------------------------------------------------- #
if [ -t 1 ]; then B=$'\033[1m'; G=$'\033[32m'; R=$'\033[31m'; Y=$'\033[33m'; Z=$'\033[0m'
else B=''; G=''; R=''; Y=''; Z=''; fi
step() { printf '\n%s== %s ==%s\n' "$B" "$*" "$Z"; }
ok()   { printf '%s  ok:%s %s\n' "$G" "$Z" "$*"; }
warn() { printf '%s  note:%s %s\n' "$Y" "$Z" "$*"; }
die()  { printf '%s  error:%s %s\n' "$R" "$Z" "$*" >&2; exit 1; }

# --------------------------------------------------------------------------- #
# The cross-NAT hole-punching gate (opt-in: --cross-nat).
#
# scripts/cross-nat-tailnet.sh selftest stands up two Linux netns each behind its
# OWN MASQUERADE NAT with no route between their private addresses, PROVES that
# isolation, enrols two stock tailscale clients against a drorb plane, asserts a
# `direct` path in BOTH directions to the far NAT's PUBLIC address, re-proves the
# isolation while the path is up, and tears everything down. It needs root, so it
# cannot run by default.
#
# It exits 77 when a PREREQUISITE is absent. That is reported LOUDLY, with the
# reason the harness printed — a gate that quietly no-ops is exactly how the
# cross-NAT row became a dated my-hand result nothing re-checked. When the flag is
# not passed at all, we say that too.
# --------------------------------------------------------------------------- #
cross_nat_gate() {
  if [ "$CROSSNAT" -ne 1 ]; then
    step "cross-NAT hole-punching gate"
    warn "NOT RUN — opt-in. It needs root + Linux netns + a free 10.77.0.0/16."
    warn "Run it with:  scripts/ci.sh --cross-nat     (or: sudo -v && bash scripts/cross-nat-tailnet.sh selftest)"
    warn "Until it runs, the cross-NAT row in docs/gateway/tailnet-05-homelab-quickstart.md is a DATED result, not a checked one."
    return 0
  fi
  step "cross-NAT hole-punching gate (scripts/cross-nat-tailnet.sh selftest)"
  local rc=0
  bash "$ROOT/scripts/cross-nat-tailnet.sh" selftest || rc=$?
  case "$rc" in
    0)  ok "two stock clients behind two separate NATs reached a DIRECT path, both ways; isolation proven before and during; topology torn down clean" ;;
    77) warn "SKIPPED — a prerequisite is absent (the harness printed the reason above)."
        warn "This is a SKIP, not a pass: the cross-NAT claim was NOT re-checked in this run." ;;
    *)  die "cross-NAT gate FAILED (exit $rc). The hole-punching result did NOT reproduce." ;;
  esac
}

OS="$(uname -s)"

# --------------------------------------------------------------------------- #
# Environment: PATH (elan), HACL_DIST, and the per-OS library search paths.
# --------------------------------------------------------------------------- #
step "environment"

# Put the elan-managed `lean`/`lake` and the rustup-managed `cargo` on PATH if
# they are not already there (a non-interactive shell often lacks both).
for d in "$HOME/.elan/bin" "$HOME/.cargo/bin"; do
  if [ -d "$d" ]; then
    case ":$PATH:" in
      *":$d:"*) ;;
      *) PATH="$d:$PATH" ;;
    esac
  fi
done
export PATH

export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export KRML="${KRML:-$(dirname "$HACL_DIST")/karamel}"
# -levercrypt at the exe/host link is resolved via LIBRARY_PATH — no hard-coded -L.
export LIBRARY_PATH="$HACL_DIST${LIBRARY_PATH:+:$LIBRARY_PATH}"
if [ "$OS" = "Darwin" ]; then
  export DYLD_LIBRARY_PATH="$HACL_DIST${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
else
  export LD_LIBRARY_PATH="$HACL_DIST${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
fi

printf '  OS:         %s\n'  "$OS"
printf '  repo:       %s\n'  "$ROOT"
printf '  HACL_DIST:  %s\n'  "$HACL_DIST"

# --- required tools ---
missing=0
for tool in lean lake cargo cc ar python3; do
  if command -v "$tool" >/dev/null 2>&1; then
    ok "$tool -> $(command -v "$tool")"
  else
    warn "$tool NOT found"
    missing=1
  fi
done
[ "$missing" -eq 0 ] || die "missing required tool(s). See BUILD.md for the dependency list.
  - lean/lake: install elan (https://github.com/leanprover/elan); it puts them under \$HOME/.elan/bin
  - cargo:     install the Rust toolchain (rustup); the repo pins a nightly in rust-toolchain.toml
  - cc/ar:     a C toolchain (Xcode CLT on macOS, build-essential on Linux)
  - python3:   for the sorry-scan and the conformance driver"

# --- HACL*/EverCrypt (the one heavy external dependency) ---
if [ ! -d "$HACL_DIST" ]; then
  die "HACL_DIST does not exist: $HACL_DIST
  Build/extract HACL*/EverCrypt there, or set HACL_DIST to your dist. See BUILD.md (\"HACL*/EverCrypt\")."
fi
[ -f "$HACL_DIST/libevercrypt.a" ] || die "libevercrypt.a not found under HACL_DIST=$HACL_DIST
  Build it once:  ( cd \"\$HACL_DIST\" && ./configure && make -j libevercrypt.a )   (see BUILD.md)"
[ -f "$HACL_DIST/EverCrypt_AEAD.h" ] || die "EverCrypt headers not found under HACL_DIST=$HACL_DIST (is this the gcc-compatible dist?)"
ok "libevercrypt.a + EverCrypt headers present"

lean --version | sed 's/^/  /'

# --------------------------------------------------------------------------- #
# The honest FROM-SCRATCH proof gate. `lake build` (bare) builds every
# @[default_target] verified library. We wipe .lake/build first so no stale
# olean can mask a proof that no longer closes. FFI objects live under ffi/ and
# libaes_fallback.a under target/, so neither is disturbed by this wipe.
# --------------------------------------------------------------------------- #
step "from-scratch proof build (rm -rf .lake/build && lake build)"
rm -rf .lake/build
lake build
ok "lake build: all default proof targets compiled from scratch"

# --------------------------------------------------------------------------- #
# Tree-wide sorry / sorryAx scan. Comments and docstrings routinely SAY "no
# `sorry`" / "0-sorry"; a naive grep trips on those. We strip Lean comments
# (nested /- -/ blocks and -- lines) first, then look for a bare sorry/sorryAx
# token in the actual code. `admit` is used only as an identifier here (a Reply
# constructor / a def name), never as a tactic, so it is intentionally not
# scanned.
# --------------------------------------------------------------------------- #
step "tree-wide sorry / sorryAx scan"
python3 - "$ROOT" <<'PY'
import sys, re, os
root = sys.argv[1]
def strip(src):
    out=[]; i=0; n=len(src); depth=0
    while i<n:
        two=src[i:i+2]
        if depth==0 and two=='--':
            j=src.find('\n', i)
            if j<0: break
            out.append('\n'); i=j+1; continue
        if two=='/-':
            depth+=1; i+=2; continue
        if two=='-/' and depth>0:
            depth-=1; i+=2; continue
        if depth>0:
            out.append('\n' if src[i]=='\n' else ' '); i+=1; continue
        out.append(src[i]); i+=1
    return ''.join(out)
pat=re.compile(r'\b(sorry|sorryAx)\b')
hits=[]
for dirpath,dirs,files in os.walk(root):
    dirs[:]=[d for d in dirs if d not in ('.lake','target','.git','venv','__pycache__')]
    for f in files:
        if not f.endswith('.lean'): continue
        p=os.path.join(dirpath,f)
        try: src=open(p,encoding='utf-8').read()
        except Exception: continue
        code=strip(src)
        for m in pat.finditer(code):
            ln=code[:m.start()].count('\n')+1
            hits.append(f"{os.path.relpath(p,root)}:{ln}: {m.group(0)}")
if hits:
    print("FOUND literal sorry/sorryAx in code (not comments):", file=sys.stderr)
    for h in hits: print("  "+h, file=sys.stderr)
    sys.exit(1)
print(f"  clean: 0 literal sorry/sorryAx across .lean sources")
PY
ok "sorry-scan clean"

# --------------------------------------------------------------------------- #
# Axiom manifest + vacuity gates. The sorry-scan above is TEXTUAL: it proves no
# `sorry` token is written in a source file. It says nothing about what the
# proofs actually DEPEND on. `#print axioms` — 2,200-odd invocations across this
# tree — says nothing either: it writes to the info stream and cannot fail a
# build. scripts/axiom-manifest.sh is the gate for the declarations that widen
# the trust surface:
#   * every `axiom` declaration, diffed against the committed AXIOMS.txt (a new
#     one fails CI until it is reviewed in);
#   * theorems whose statement is literally `a = a` (true of EVERY definition, so
#     the NAME is the only thing making a claim) — must be zero;
#   * `∃ y, f … = y` function-hood restatements — ratcheted, may not grow;
#   * `opaque`/`@[extern]` seams with no axiom constraining them — reported.
# The per-theorem footprint gate is `#assert_axioms` (see Hygiene.lean), which
# lives in the .lean sources and is enforced by `lake build` above.
# --------------------------------------------------------------------------- #
step "axiom manifest + vacuity gates"
bash scripts/axiom-manifest.sh
ok "axiom manifest matches AXIOMS.txt; no vacuous theorems"

# --------------------------------------------------------------------------- #
# Reachability. `@[export]` symbols that no host call site reaches are proofs we
# paid for and do not ship; modules outside the archive closure are proofs CI
# does not even typecheck. Both accumulated silently until an audit found 41 of
# 109 exports orphaned and ~190 WebSocket theorems unreachable on the default
# reactor. The audit is pure source analysis (~1s, no build) and regenerates
# docs/gateway/REACHABILITY.md; --check fails when that doc is stale or when the
# orphan count rises above the ratchet in the wrapper.
# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Operator config. Two failure modes with long fuses: a DRORB_* flag that only
# some reactors honor (that is how DRORB_GATEWAY went unhonored by the SHIPPED
# reactor for months), and a DRORB_SPAN whose serve twin does not answer the ACME
# HTTP-01 challenge — a server that works perfectly until the certificate expires
# ~90 days later. Both are ratcheted here rather than left to memory.
# --------------------------------------------------------------------------- #
step "operator-config ratchet (DRORB_* by reactor + DRORB_SPAN ACME guard)"
bash scripts/env-flag-audit.sh --check
ok "no silently reactor-scoped flag; the DRORB_SPAN ACME guard matches serve.rs and the driven audit"

step "reachability audit (orphaned exports ratchet)"
bash scripts/reachability-audit.sh --check
ok "no new orphaned exports; REACHABILITY.md current"

# --------------------------------------------------------------------------- #
# FFI prerequisites. These object files and the AES fallback archive are what
# the native dataplane host (crates/dataplane/build.rs) and the `orb*` exes link
# against; conformance/run.sh assumes they already exist. A fresh checkout has
# none, so build them here (idempotent; each script is a no-op re-run).
# --------------------------------------------------------------------------- #
step "FFI prerequisites"
# The portable AES-GCM fallback static archive (target/release/libaes_fallback.a).
cargo build --release -p aes-fallback
ok "libaes_fallback.a"
# The C shims the deployed serve closure reaches (CGI spawn, HACL*/EverCrypt
# crypto seam, TCP byte-mover for the TLS front door, RSA/ECDSA cert signer).
bash ffi/build-cgi-shim.sh
bash ffi/build-crypto-shim.sh
bash ffi/build-pq-stub.sh
bash ffi/build-derp-net.sh
bash ffi/build-tls-p256-shim.sh
# mac_io.o + mac_udp.o (the native multi-protocol/QUIC servers; mac_udp.o also
# carries the QUIC header-protection ChaCha20 the datagram closure references).
# Both compile on Linux too (POSIX sockets; EverCrypt via __has_include).
bash ffi/build-mac-multi.sh
ok "C shims (cgi, crypto, derp_net, tls_p256, mac_io, mac_udp)"
# Linux only: the glibc>=2.38 C23 alias shim for aws-lc's __isoc23_* references
# at the leanc exe link (the Lean toolchain glibc predates them). No-op on macOS.
if [ "$OS" != "Darwin" ]; then
  bash ffi/build-glibc-compat.sh
  ok "glibc_isoc23_compat.o (Linux)"
fi

# --------------------------------------------------------------------------- #
# Serve-closure export object that build-dataplane-lib.sh's `find` needs but does
# not build itself. `Reactor.ServeArr` (archived explicitly) references
# `Reactor.serializeHeadAcc` / `initialize_Reactor_SerializeFast` from
# `Reactor.SerializeFast`, whose `.c.o.export` no orb exe pulls and no explicit
# target in build-dataplane-lib.sh builds. On a WARM tree the object exists
# incidentally (some earlier build compiled it); on a FROM-SCRATCH tree it is
# absent and the host link fails undefined. We compile it here so it is on disk
# before build-dataplane-lib.sh's `find` runs (it never wipes .lake/build, so this
# also fixes run.sh's build-dataplane-lib.sh call in full mode).
# NOTE for the dataplane lane: folding `lake build Reactor.SerializeFast:c.o.export`
# into ffi/build-dataplane-lib.sh (next to its Reactor.ServeArr line) is the
# proper home for this; it lives here to avoid editing another lane's file.
# --------------------------------------------------------------------------- #
step "serve-closure export objects (from-scratch archive completeness)"
lake build Reactor.SerializeFast:c.o.export
ok "Reactor.SerializeFast:c.o.export"

# --------------------------------------------------------------------------- #
# Native serve link. Building the orb exes compiles the whole deployed-serve
# closure to C: `orb` (byte-stream serve), `orb-mac-multi` (native multi-proto),
# and `orb-quic` (the datagram/QUIC header-protection fork). build-dataplane-lib.sh
# then archives EVERY .c.o.export it finds into libdrorb.a and builds only the
# closure DELTA explicitly, so ALL THREE exes must be built first or the host link
# fails on closure symbols (`serializeHeadAcc`, `drorb_serve_datagram`, ...). This
# is exactly conformance/run.sh's build order — so in full mode we let run.sh own
# it (identical work), and do it here only for --quick, where it is the link gate.
# --------------------------------------------------------------------------- #
if [ "$QUICK" -eq 1 ]; then
  step "native dataplane link (libdrorb.a + Rust host)"
  lake build orb orb-mac-multi orb-quic
  bash ffi/build-dataplane-lib.sh
  cargo build --release
  ok "orb exes + dataplane host + workspace crates built"
  # The archive is the ONLY thing carrying the proofs into the binary, and a bare
  # `lake build` does not cut it. Assert here that what we just linked is not older
  # than its own Lean, so a --quick gate cannot bless a host running previous proofs.
  bash scripts/archive-freshness.sh --check
  step "conformance"
  warn "--quick: skipping conformance suite"
  cross_nat_gate
  step "RESULT"; ok "quick gate PASSED (build + sorry-scan + dataplane link)"
  exit 0
fi

# --------------------------------------------------------------------------- #
# Conformance. run.sh (SKIP_BUILD unset) builds the orb exes + libdrorb.a + the
# Rust dataplane + proxy_backend + h2c-host (the .lake/build wipe above deleted
# the exes, so it rebuilds them; the FFI prerequisites they link were built
# above) and drives the base + parity suites. Neither driver exits non-zero on a
# scenario FAIL (they always write JSON and return 0), so we read the JSON FAIL
# counts and fail the gate on any real FAIL. UNWIRED (proven-but-not-connected)
# and SKIPPED (e.g. aioquic/h2spec absent) are accepted — diagnostics, not
# failures.
# --------------------------------------------------------------------------- #
step "conformance suite (conformance/run.sh)"
bash conformance/run.sh

# --------------------------------------------------------------------------- #
# ARCHIVE FRESHNESS. Every number below this line is a measurement of whatever
# Lean is inside libdrorb.a — and `lake build` does not put it there
# (ffi/build-dataplane-lib.sh does). A green proof build plus a green cargo build
# can therefore certify a binary running the PREVIOUS proofs, with nothing in the
# pipeline noticing. Checked AFTER run.sh (which cuts the archive) and BEFORE the
# verdict is read, so a stale archive invalidates the conformance result loudly
# instead of silently.
# --------------------------------------------------------------------------- #
step "archive freshness (libdrorb.a vs its Lean closure)"
bash scripts/archive-freshness.sh --check

step "conformance verdict"
python3 - "$ROOT" <<'PY'
import json, os, sys
root=sys.argv[1]
def load(rel):
    p=os.path.join(root,"conformance",rel)
    if not os.path.exists(p): return None
    return json.load(open(p))
bad=0
for label, rel in (("base suite","results.json"), ("parity harness","results_parity.json")):
    d=load(rel)
    if d is None:
        print(f"  {label}: MISSING {rel}", file=sys.stderr); bad=1; continue
    c=d.get("counts",{})
    total=len(d.get("scenarios",[]))
    line=f"  {label}: total={total}  " + "  ".join(f"{k}={c.get(k,0)}" for k in ("PASS","FAIL","UNWIRED","SKIPPED"))
    print(line)
    if c.get("FAIL",0)>0:
        print(f"    -> {c['FAIL']} FAIL in {label}", file=sys.stderr); bad=1
sys.exit(1 if bad else 0)
PY
ok "conformance: no FAIL"

cross_nat_gate

step "RESULT"
ok "full gate PASSED (from-scratch build + sorry-scan + dataplane link + conformance)"
