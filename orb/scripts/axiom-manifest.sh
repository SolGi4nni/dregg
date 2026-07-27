#!/usr/bin/env bash
# scripts/axiom-manifest.sh — the trust surface as a COMMITTED, DIFFED artifact.
#
# `#print axioms` writes to the info stream and can never fail a build, so the
# 2,200-odd audit sites in this tree are documentation, not a gate. This script
# is the gate for the other half of the trust surface: the DECLARATIONS that
# widen it.
#
#   1. axiom manifest (GATE) — every real `axiom` declaration in the tree,
#      fully qualified, sorted, diffed against the committed AXIOMS.txt. A new
#      `axiom` anywhere fails CI until it is reviewed into the manifest.
#   2. vacuity scan (GATE) — theorems whose statement is literally `a = a`.
#      Such a theorem holds for EVERY definition of the same arity, so its NAME
#      is the only thing carrying a claim. Must be zero.
#   3. function-hood restatements (RATCHET) — `∃ y, f … = y`. Same defect, older
#      and more diffuse; the count may not grow.
#   4. unpinned `opaque` (REPORT) — an `opaque`/`@[extern]` definition with no
#      axiom mentioning it is a seam whose behaviour is wholly unconstrained:
#      nothing in Lean says what the C on the other side does. Counted and
#      listed, not gated (the number is a finding, not a regression).
#
# Usage:
#   scripts/axiom-manifest.sh            check against AXIOMS.txt (exit 1 on drift)
#   scripts/axiom-manifest.sh --write    regenerate AXIOMS.txt
#   scripts/axiom-manifest.sh --list-opaque   also print every unpinned opaque
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

MODE=check
LIST_OPAQUE=0
for arg in "$@"; do
  case "$arg" in
    --write) MODE=write ;;
    --list-opaque) LIST_OPAQUE=1 ;;
    -h|--help) sed -n '2,28p' "$HERE/axiom-manifest.sh" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "axiom-manifest.sh: unknown argument: $arg (try --help)" >&2; exit 2 ;;
  esac
done

# The number of `∃ y, f … = y` function-hood restatements known to the tree when
# this ratchet was installed. These are vacuous in exactly the way `a = a` is —
# they hold for every function — but they predate the gate and live in modules
# this lane does not own. The count may DROP (fix them) and may never GROW.
#   H2/Stream.lean step_total, Tls/Theorems.lean step_total,
#   Wireguard.lean step_total, Proto/Theorems.lean step_total, ...
EXISTS_VACUOUS_BASELINE=${EXISTS_VACUOUS_BASELINE:-14}

if [ -t 1 ]; then B=$'\033[1m'; G=$'\033[32m'; R=$'\033[31m'; Y=$'\033[33m'; Z=$'\033[0m'
else B=''; G=''; R=''; Y=''; Z=''; fi
step() { printf '\n%s== %s ==%s\n' "$B" "$*" "$Z"; }
ok()   { printf '%s  ok:%s %s\n' "$G" "$Z" "$*"; }
warn() { printf '%s  note:%s %s\n' "$Y" "$Z" "$*"; }
bad()  { printf '%s  error:%s %s\n' "$R" "$Z" "$*" >&2; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

python3 - "$ROOT" "$WORK" <<'PY'
import sys, os, re

root, work = sys.argv[1], sys.argv[2]

SKIP_DIRS = {'.lake', 'target', '.git', 'venv', '__pycache__', 'node_modules'}

def strip_comments(src):
    """Blank out Lean comments (nested /- -/ and -- lines) but keep offsets, so
    line numbers stay exact. Same shape as the sorry-scan in scripts/ci.sh:
    docstrings routinely SAY "axiom" and "opaque", and a naive grep believes
    them."""
    out = []; i = 0; n = len(src); depth = 0
    while i < n:
        two = src[i:i+2]
        if depth == 0 and two == '--':
            j = src.find('\n', i)
            if j < 0:
                out.append(' ' * (n - i)); break
            out.append(' ' * (j - i)); i = j; continue
        if two == '/-':
            depth += 1; out.append('  '); i += 2; continue
        if two == '-/' and depth > 0:
            depth -= 1; out.append('  '); i += 2; continue
        if depth > 0:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)

def lean_files():
    for dp, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in sorted(files):
            if f.endswith('.lean'):
                yield os.path.join(dp, f)

IDENT = r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'!?α-ωΑ-Ω₀-₉]*"
NS_RE   = re.compile(r'^\s*namespace\s+(' + IDENT + r'(?:\.' + IDENT + r')*)', re.M)
END_RE  = re.compile(r'^\s*end\b\s*(' + IDENT + r'(?:\.' + IDENT + r')*)?', re.M)
AX_RE   = re.compile(r'^([ \t]*)axiom\s+(' + IDENT + r'(?:\.' + IDENT + r')*)', re.M)
OPQ_RE  = re.compile(r'^([ \t]*)(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*opaque\s+('
                     + IDENT + r'(?:\.' + IDENT + r')*)', re.M)
# A declaration head: where an `axiom`/`opaque` statement stops.
DECL_HEAD = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    r'(theorem|lemma|def|abbrev|instance|axiom|opaque|structure|inductive|class|example|namespace|end|'
    r'@\[|#|open|section|universe|variable|macro|syntax|elab|attribute|deriving|set_option|/-!)')

def namespace_at(code, pos):
    """The namespace prefix in effect at character offset `pos`."""
    stack = []
    for m in re.finditer(r'^\s*(namespace|end)\b[ \t]*(' + IDENT + r'(?:\.' + IDENT + r')*)?', code, re.M):
        if m.start() >= pos:
            break
        kw, nm = m.group(1), m.group(2)
        if kw == 'namespace' and nm:
            stack.append(nm)
        elif kw == 'end':
            if nm and stack and stack[-1] == nm:
                stack.pop()
            elif nm and nm in stack:
                while stack and stack.pop() != nm:
                    pass
            # a bare `end` closes a `section`; namespaces here are always named
    return '.'.join(stack)

def stmt_after(code, start):
    """The declaration text starting at `start`, up to the next declaration head."""
    lines = code[start:].split('\n')
    out = [lines[0]]
    for ln in lines[1:]:
        if ln.strip() and DECL_HEAD.match(ln):
            break
        out.append(ln)
        if len(out) > 60:
            break
    return '\n'.join(out)

axioms = []            # (relpath, fullname, statement text)
opaques = []           # (relpath, fullname, has_extern)
vac_eq = []            # (relpath, line, name, conclusion)
vac_ex = []            # (relpath, line, name, conclusion)

THM_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*(?:theorem|lemma)\s+('
                    + IDENT + r'(?:\.' + IDENT + r')*)', re.M)

for path in lean_files():
    rel = os.path.relpath(path, root)
    raw = open(path, encoding='utf-8', errors='replace').read()
    code = strip_comments(raw)

    for m in AX_RE.finditer(code):
        ns = namespace_at(code, m.start())
        full = (ns + '.' + m.group(2)) if ns else m.group(2)
        axioms.append((rel, full, stmt_after(code, m.start())))

    for m in OPQ_RE.finditer(code):
        ns = namespace_at(code, m.start())
        full = (ns + '.' + m.group(2)) if ns else m.group(2)
        # look back a little for an @[extern ...] attribute on the same decl
        back = code[max(0, m.start() - 200):m.start()]
        raw_back = raw[max(0, m.start() - 400):m.start() + 200]
        opaques.append((rel, full, 'extern' in raw_back.split('opaque')[0][-200:]))

    # Hygiene/SelfTest.lean deliberately DECLARES vacuous fixtures so that
    # `#assert_nonvacuous` can be shown rejecting them (under `#guard_msgs`).
    # Its vacuity is the test, not a defect.
    if rel.replace(os.sep, '/') == 'Hygiene/SelfTest.lean':
        continue

    lines = code.split('\n')
    for m in THM_RE.finditer(code):
        ln0 = code[:m.start()].count('\n')
        chunk = '\n'.join(lines[ln0:ln0 + 16])
        i = chunk.find(':=')
        if i < 0:
            continue
        stmt = chunk[:i]
        j = stmt.rfind(':')
        if j < 0:
            continue
        concl = ' '.join(stmt[j + 1:].split())
        eq = re.match(r'^(.*\S)\s*=\s*(.*\S)$', concl)
        if eq and eq.group(1) == eq.group(2):
            vac_eq.append((rel, ln0 + 1, m.group(1), concl))
            continue
        ex = re.match(r'^∃\s*(' + IDENT + r')\s*,\s*(.*\S)\s*=\s*(.*\S)$', concl)
        if ex:
            v, lhs, rhs = ex.group(1), ex.group(2), ex.group(3)
            if (rhs == v and not re.search(r'\b' + re.escape(v) + r'\b', lhs)) or \
               (lhs == v and not re.search(r'\b' + re.escape(v) + r'\b', rhs)):
                vac_ex.append((rel, ln0 + 1, m.group(1), concl))

# --- manifest -------------------------------------------------------------
with open(os.path.join(work, 'axioms.txt'), 'w') as f:
    f.write("# drorb axiom manifest — every `axiom` DECLARATION in the tree.\n")
    f.write("# Regenerate with: scripts/axiom-manifest.sh --write\n")
    f.write("# Each line widens the trust surface: it is a Prop the kernel accepts\n")
    f.write("# without proof. Adding one is a REVIEW event, not a build detail.\n")
    f.write("#\n")
    f.write("# format:  <fully-qualified name>\\t<file>\n")
    for rel, full, _ in sorted(set((r, n, '') for r, n, _ in axioms)):
        f.write(f"{full}\t{rel}\n")

# --- unpinned opaques -----------------------------------------------------
ax_text = '\n'.join(t for _, _, t in axioms)
ax_tokens = set(re.findall(IDENT, ax_text))
unpinned = []
for rel, full, ext in sorted(set(opaques)):
    base = full.split('.')[-1]
    if base not in ax_tokens and full not in ax_text:
        unpinned.append((rel, full, ext))

with open(os.path.join(work, 'opaque.txt'), 'w') as f:
    for rel, full, ext in unpinned:
        f.write(f"{full}\t{rel}\t{'extern' if ext else '-'}\n")

with open(os.path.join(work, 'vacuous_eq.txt'), 'w') as f:
    for rel, ln, nm, c in vac_eq:
        f.write(f"{rel}:{ln}: {nm}  ::  {c}\n")
with open(os.path.join(work, 'vacuous_exists.txt'), 'w') as f:
    for rel, ln, nm, c in vac_ex:
        f.write(f"{rel}:{ln}: {nm}  ::  {c}\n")

with open(os.path.join(work, 'counts.txt'), 'w') as f:
    f.write(f"axioms={len(set((r, n) for r, n, _ in axioms))}\n")
    f.write(f"opaque_total={len(set(opaques))}\n")
    f.write(f"opaque_unpinned={len(unpinned)}\n")
    f.write(f"vacuous_eq={len(vac_eq)}\n")
    f.write(f"vacuous_exists={len(vac_ex)}\n")
PY

# shellcheck disable=SC1090
. "$WORK/counts.txt"

step "axiom manifest"
if [ "$MODE" = write ]; then
  cp "$WORK/axioms.txt" "$ROOT/AXIOMS.txt"
  ok "wrote AXIOMS.txt ($axioms axiom declarations)"
else
  if [ ! -f "$ROOT/AXIOMS.txt" ]; then
    bad "AXIOMS.txt is missing. Generate it: scripts/axiom-manifest.sh --write"
    exit 1
  fi
  if ! diff -u "$ROOT/AXIOMS.txt" "$WORK/axioms.txt" > "$WORK/axioms.diff"; then
    bad "AXIOM DRIFT — the tree's axiom declarations no longer match AXIOMS.txt:"
    sed 's/^/    /' "$WORK/axioms.diff" >&2
    bad "An added line is a NEW unproved assumption. Review it, then re-run with --write."
    exit 1
  fi
  ok "$axioms axiom declarations, manifest matches AXIOMS.txt"
fi

step "vacuity scan (statement is literally \`a = a\`)"
if [ "$vacuous_eq" -ne 0 ]; then
  bad "$vacuous_eq theorem(s) whose statement is \`a = a\` — true of EVERY definition:"
  sed 's/^/    /' "$WORK/vacuous_eq.txt" >&2
  bad "Prove the property the NAME claims, or delete the theorem."
  exit 1
fi
ok "0 \`a = a\` theorems"

step "function-hood restatements (\`∃ y, f … = y\`) — ratchet"
printf '  found: %s (baseline %s)\n' "$vacuous_exists" "$EXISTS_VACUOUS_BASELINE"
if [ "$vacuous_exists" -gt "$EXISTS_VACUOUS_BASELINE" ]; then
  bad "the count GREW past the baseline; new ones:"
  sed 's/^/    /' "$WORK/vacuous_exists.txt" >&2
  exit 1
fi
[ "$vacuous_exists" -eq 0 ] || sed 's/^/    /' "$WORK/vacuous_exists.txt"
ok "no growth in function-hood restatements"

step "unpinned \`opaque\` seams (report)"
printf '  opaque declarations:        %s\n' "$opaque_total"
printf '  with NO axiom mentioning them: %s\n' "$opaque_unpinned"
warn "an unpinned opaque is a seam whose behaviour is wholly unconstrained:"
warn "nothing in Lean says what the definition (or the C behind @[extern]) does."
if [ "$LIST_OPAQUE" -eq 1 ]; then
  sed 's/^/    /' "$WORK/opaque.txt"
fi

step "RESULT"
ok "axiom manifest + vacuity gates PASSED"
