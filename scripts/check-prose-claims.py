#!/usr/bin/env python3
"""check-prose-claims.py — A CLAIM THE CODE DOES NOT CARRY.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
This tree has instruments for proofs, gates, carriers, rows, callers, ignores, fences,
manifests and copy. It has none for PROSE. Every wound below was found by a person
reading carefully, and none by a check — measured 2026-07-30, six in one day:

  1  `DreggFederation.advanceState` was documented "if this method executes
     successfully, the state transition was cryptographically verified" on a method
     whose file contains ZERO occurrences of `.verify(`, `Proof<`, `ZkProgram`,
     `SelfProof` and `DynamicProof`. It is a monotonic counter with a signature-free
     setter.
  2  The same file's class doc said `nullifierRoot` "prevents double-withdrawal" over
     a field set to `Field(0)` at init and NEVER READ AGAIN, and said the relay
     authority "can be rotated via governance proof" — naming a method that does not
     exist. ⚑ The doc was hiding a LIVE HOLE, not overstating a weak one.
  3  `ivc_turn_chain.rs` said child-circuit identity was "CLOSED";
     `plonky3_recursion_impl.rs` said the harness "does NOT (cannot, harness-side)
     pin" it. Two of our own comments, contradicting.
  4  `MinaBinprot` §7 said "the kernel will not reduce at these sizes", justifying
     `native_decide` across sixteen theorems. Measured: the whole file is 30 seconds.
  5  A `630×` kernel→compiled ratio every downstream cost derived from. Measured: 359×.
  6  `PastaMsmSliced`'s `loConstGate`/`hiConstGate` carried a comment claiming they
     stopped a forgery that a per-row literal had already made unreachable.

⚠ IT CATCHES TWO OF THE SIX, AND THAT NUMBER IS MEASURED, NOT CLAIMED.
`--historical` replays all six from git as they were BEFORE repair and prints which
fired. On 2026-07-30 it reads:

    CAUGHT  1  DreggFederation.advanceState 'cryptographically verified'   [R1 R2 R2b]
    CAUGHT  2  the same file's header: nullifierRoot 'prevents ...'        [R2 R2b]
    missed  3, 4, 5, 6

Specimens 3, 5 and 6 need a READER and are named under THE BLIND SPOTS below. Specimen
4 (an unmeasured performance excuse justifying `native_decide`) is mechanical in
principle and is NOT implemented: this tree has 701 `native_decide` sites across 317
files and 17 kernel-performance excuses, most of them TRUE (`Std.Range.forIn`'s
well-founded recursion really does not reduce), so the rule separates true from false
only by asking whether a number and a unit sit beside the excuse. That is a real gate
and it is a different one; it is not smuggled in here as a wall of amber.

Against `main` it is not idle: the first full run harvested TWELVE stale structural
claims under R3, listed in `scripts/prose-claims-allow.tsv`.

═══ THE RULES ═════════════════════════════════════════════════════════════════════
R1  A CRYPTO CLAIM IN A FILE WITH NO CRYPTO IN IT. A function or module doc makes a
    CRYPTOGRAPHIC VERIFICATION claim — "cryptographically verified", "recursive proof",
    "verifies the signature", "requires a valid proof" — and the file's CODE contains
    no token of that mechanism's vocabulary.
    ⚠ NOT a bare-verb scan. "ensures", "requires" and "guarantees" are ordinary English
      and a gate keyed on them reds on hundreds of honest docstrings.
    ⚠ FILE-scoped, not declaration-scoped, and MEASURED that way: scoped to the
      declaration's own body it reported 34 sites on `main` and every one read honest
      (a constructor documenting a parameter checked elsewhere; a `parse` whose
      verification lives inside `BiscuitToken::from_encoded`). Scoped to the file it
      reports ZERO — which is how specimen 1 was actually established, by a grep over
      the file for `.verify(`/`Proof<`/`ZkProgram`/`SelfProof`/`DynamicProof`.
    ⚠ A NEGATED claim is a DISCLAIMER, and this tree writes them precisely ("does NOT
      verify signatures", "actor NOT cryptographically verified"). 14 of the first
      run's 80 hits were disclaimers. They do not fire.
    ⚠ A QUOTED claim is a claim being REPORTED. Blanked before matching — the
      self-test caught R1 firing on a sentence about this very disease.

R2  A PROTECTIVE CLAIM ON A FIELD NOTHING READS. A doc line says identifier X
    "prevents" / "guards against" / "precludes" something; X is declared in the file,
    WRITTEN in the file, and never READ in it. A field nobody reads cannot prevent
    anything. Specimen 2 exactly, and the one that mattered most: the sentence was not
    a weak description of a real guard, it was the only evidence a guard was intended.
    ⚠ The identifier must be NAMED AS ONE — backticked, or the subject of a `- name:`
      bullet. Free English words that collide with field names produced every false
      positive this rule had.
    ⚠ "blocks" and "stops" are NOT protective verbs here. In this tree "block" is a
      noun on nearly every line that contains it.

R2b A CAPABILITY A CLASS OR MODULE HEADER CLAIMS AND NOTHING DECLARES. "Relay
    authority can be rotated via governance proof", in a file with no `rotate` in it
    anywhere. Class and module docs only — scoped wider it fired on an enum variant
    literally named `CanRevoke`.

R3  A STALE STRUCTURAL CLAIM, against the real import graph. "NOT imported by
    `Dregg2.lean`" in a module `Dregg2.lean` imports at line 1428. In this tree that
    sentence decides whether a reader believes a module's `#assert_axioms`/`#guard`
    KATs run in any CI target, so a stale one is not cosmetic. TWELVE live on `main`.

═══ THE BLIND SPOTS, NAMED ════════════════════════════════════════════════════════
  * 3 (two comments contradicting) was PROTOTYPED, MEASURED and REJECTED.
    `--contradiction-probe` keeps the rejected rule runnable so the verdict stays
    checkable instead of remembered: keying a status word to the identifiers on its
    line and looking for those identifiers under a negative-capability word elsewhere
    yields 1,589,852 pairs on this tree. A gate people disable is worse than none.
  * 5 (a projected ratio nothing measured) needs someone to notice that a number's
    stated source appears in exactly one sentence in the tree — the one that derives
    the number from it. That is a judgement about EVIDENCE; no token count reaches it.
  * 6 (a gate defending against a forgery that was already unreachable) took a THEOREM
    to establish. A scanner that could see it would be a prover.
  * R1's own hole: a false claim in a file where a SIBLING function does real crypto
    reads as clean. R1 catches the module that claims a mechanism it does not have,
    not the function that borrows its neighbour's.
  * R2's own hole: a field read only in ANOTHER crate. Requiring an in-file WRITE is
    what keeps a `types.rs` from reading as a wall of unguarded fields, and it is also
    why a field written in one module and guarded in another is invisible here.

═══ THE NEIGHBOUR ════════════════════════════════════════════════════════════════
`scripts/mirror-gates/mirror_gates.py`'s gate D2 is the closest existing instrument —
"prose claims a mechanism; this asserts the mechanism exists". It is Rust-only and its
three rules are about CITATION of a named symbol (a doc calling something module-private
that is `pub use`d; a doc naming a consumer that does not consume). It does not read
TypeScript or Lean and has no rule about verifying verbs, unread fields or the import
graph. This is a sibling, not a duplicate, and it was checked before writing.

═══ THE EXEMPTION LIST IS A RATCHET, NOT A MUTE ═══════════════════════════════════
`scripts/prose-claims-allow.tsv`, one row per site, TAB-separated:

    path <TAB> rule <TAB> the claim text, escaped to one line <TAB> why it stays

Keyed by the TEXT, not a line number — lanes move lines all day. A row whose text no
longer appears at that path FAILS, so a repaired doc retires its own exemption. A reason
under 20 characters FAILS, and an empty text key FAILS (it would mute a whole path).
A row whose reason begins `HARVEST ` records a TRUE finding nobody has repaired yet;
those are printed on EVERY run and capped by `HARVEST_CEILING` here in reviewed code, so
the baseline can shrink without ceremony and cannot grow without a visible diff.

═══ USAGE ═════════════════════════════════════════════════════════════════════════
    python3 scripts/check-prose-claims.py                # the gate (~25 s, no cargo)
    python3 scripts/check-prose-claims.py --self-test    # can it go red?
    python3 scripts/check-prose-claims.py --historical   # score against the six
    python3 scripts/check-prose-claims.py --contradiction-probe   # the rejected rule
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOW = ROOT / "scripts" / "prose-claims-allow.tsv"
MIN_REASON = 20
# ⚑ A CEILING ON THE BASELINE, IN REVIEWED CODE. `HARVEST` rows in the allowlist are
# TRUE findings that are recorded rather than repaired — green on arrival, red on the
# next one. That is only honest while the count cannot drift upward quietly, so the
# number lives here and not in the data it governs. 12 on 2026-07-30, all of them the
# stale "NOT imported by the `Dregg2` root" class; lower it as they are fixed.
HARVEST_CEILING = 12

# Directories that are not ours to hold to a claim.
SKIP_DIRS = {
    "target", "vendor", "node_modules", ".git", ".lake", "build", "dist",
    "old-docs", "site-old-scavenge", "ts-sdk.archived", ".docs-history-noclaude",
}

# ⚠ CHEAP LITERAL GATES in front of the expensive alternations. Every CRYPTO_CLAIM
# alternative contains one of R1_LITERALS and every PROTECTIVE one contains an
# R2_LITERAL, so these narrow nothing — they just stop a verbose regex from walking
# 85 MB of source that cannot match it. `in` on a str is memmem; the alternation is not.
R1_LITERALS = ("cryptograph", "recursiv", "verif", "proof", "signatur", "snark",
               "stark", "attestation", "witness")
R2_LITERALS = ("prevent", "guard", "preclud", "forbid", "rule", "impossible",
               "defend")

# ── FLOORS ────────────────────────────────────────────────────────────────────────
# A NEGATIVE assertion passes just as happily when its own reader is broken. These are
# the populations a working reader sees on this tree; falling under one means the
# scanner went blind, not that the tree got clean.
MIN_RS_FILES = 3000
MIN_TS_FILES = 40
MIN_CLAIM_FILES = 400
MIN_UNITS = 8000
MIN_LEAN_FILES = 1500
# ⚠ EDGES, not files. A reader that opens every Lean file and parses none of their
# imports counts 2,203 files and reports the tree clean — which is exactly what a 64 KB
# header slice did to this gate while it was being written (see `lean_header_imports`).
MIN_IMPORT_EDGES = 6000


# ══════════════════════════════════════════════════════════════════════════════════
# Source blanking — comments and strings out, offsets preserved.
# ══════════════════════════════════════════════════════════════════════════════════
_NOISE_START = re.compile(r'//|/\*|r#*"|"|`|\'')
# ⚠ `.match(text, i)`, never `.match(text[i:])`: the slice copies the remainder of the
# file at every apostrophe, and this tree's comments are English prose.
_CHAR_LIT = re.compile(r"'(?:\\.|[^\\'\n])'")
_NOT_NL = re.compile(r"[^\n]")


def _blank(span: str) -> str:
    return _NOT_NL.sub(" ", span)


def strip_noise(text: str) -> str:
    """Blank comments, string and char literals, PRESERVING offsets.

    Reused shape from `check-production-callers.py`, and for its reason: this tree's
    doc comments name identifiers constantly, so counting reads over raw source reports
    a field that is read when the only thing reading it is the sentence under audit.

    ⚠ Order matters and the naive version is wrong in the direction that HIDES things —
    stripping `/*...*/` before line comments lets a `/*` inside a `//` line (a glob, a
    path) open a block comment that runs to the next `*/` anywhere later in the file.
    ⚠ It is a SCANNER, not a per-character loop: the per-character version measured
    ~50 s on this tree, which is not a tier-0 budget, and a gate that does not run in
    the everyday set is not a gate.
    """
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        m = _NOISE_START.search(text, i)
        if not m:
            out.append(text[i:])
            break
        out.append(text[i : m.start()])
        i = m.start()
        tok = m.group(0)

        if tok == "//":
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(_blank(text[i:j]))
            i = j
        elif tok == "/*":
            depth, j = 0, i
            while j < n:
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(_blank(text[i:j]))
            i = j
        elif tok.startswith("r") and tok.endswith('"'):
            hashes = tok[1:-1]
            close = text.find('"' + hashes, i + len(tok))
            j = n if close == -1 else close + 1 + len(hashes)
            out.append(_blank(text[i:j]))
            i = j
        elif tok == "'":
            # A Rust lifetime (`'a`) is not a char literal. Only `'x'` / `'\n'` are.
            mm = _CHAR_LIT.match(text, i)
            if mm:
                out.append(_blank(mm.group(0)))
                i += len(mm.group(0))
            else:
                out.append("'")
                i += 1
        else:  # '"' or '`'
            q = tok
            j = i + 1
            while j < n:
                c = text[j]
                if c == "\\":
                    j += 2
                elif c == q:
                    j += 1
                    break
                elif c == "\n" and q == '"':
                    break  # an unterminated quote; do not eat the file
                else:
                    j += 1
            out.append(_blank(text[i:j]))
            i = j
    return "".join(out)


# ══════════════════════════════════════════════════════════════════════════════════
# Unit extraction — a doc comment plus the declaration it is attached to.
# ══════════════════════════════════════════════════════════════════════════════════
@dataclass
class Unit:
    path: str
    lang: str          # "rs" | "ts"
    name: str
    kind: str          # "item" | "module"
    doc: str           # the doc comment text
    doc_line: int      # 1-based line of the first doc line
    body: str          # the declaration's own body, blanked
    is_callable: bool = False   # a fn/method — the only thing that can PERFORM a check
    doc_lines: list[tuple[int, str]] = field(default_factory=list)


DECL_NAME_RS = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:default\s+)?(?:const\s+)?(?:async\s+)?"
    r"(?:unsafe\s+)?(?:extern\s+\"[^\"]*\"\s+)?"
    r"(fn|struct|enum|trait|impl|type|const|static|mod|macro_rules!)\s+([A-Za-z_][A-Za-z0-9_]*)"
)
DECL_FIELD_RS = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?([a-z_][A-Za-z0-9_]*)\s*:")

DECL_TS = re.compile(
    r"^\s*(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*"
    r"(?:export\s+)?(?:declare\s+)?(?:abstract\s+)?"
    r"(?:public\s+|private\s+|protected\s+|readonly\s+|static\s+)*"
    r"(?:(class|interface|enum|function|const|let|var|type)\s+)?"
    r"(?:async\s+)?(?:get\s+|set\s+)?([A-Za-z_$][A-Za-z0-9_$]*)"
)


def _brace_body(blank: str, start_off: int) -> str:
    """From `start_off`, return the text through the matching close brace.

    A declaration with no `{` before its `;` is a field or a signature — its body is
    the statement, and that is the honest answer rather than swallowing the next item.
    """
    n = len(blank)
    i = start_off
    while i < n and blank[i] not in "{;":
        i += 1
    if i >= n or blank[i] == ";":
        return blank[start_off : min(i + 1, n)]
    depth = 0
    j = i
    while j < n:
        if blank[j] == "{":
            depth += 1
        elif blank[j] == "}":
            depth -= 1
            if depth == 0:
                return blank[start_off : j + 1]
        j += 1
    return blank[start_off:]


def extract_units(path: str, text: str) -> list[Unit]:
    lang = "rs" if path.endswith(".rs") else "ts"
    blank = strip_noise(text)
    lines = text.split("\n")
    # byte offset of the start of each line
    offs, acc = [], 0
    for ln in lines:
        offs.append(acc)
        acc += len(ln) + 1

    units: list[Unit] = []
    module_doc: list[tuple[int, str]] = []
    i = 0
    while i < len(lines):
        ln = lines[i]
        s = ln.strip()

        # ── module-level doc ────────────────────────────────────────────────────
        if lang == "rs" and s.startswith("//!"):
            j = i
            block: list[tuple[int, str]] = []
            while j < len(lines) and lines[j].strip().startswith("//!"):
                block.append((j + 1, lines[j].strip()[3:].strip()))
                j += 1
            module_doc.extend(block)
            i = j
            continue

        # ── an attached doc comment ─────────────────────────────────────────────
        block = []
        j = i
        if lang == "rs" and s.startswith("///"):
            while j < len(lines) and lines[j].strip().startswith("///"):
                block.append((j + 1, lines[j].strip()[3:].strip()))
                j += 1
        elif s.startswith("/**") and not s.startswith("/**/"):
            while j < len(lines):
                t = lines[j].strip()
                cleaned = re.sub(r"^/\*\*|^\*/|^\*|\*/$", "", t).strip()
                block.append((j + 1, cleaned))
                if "*/" in t and not (j == i and t == "/**"):
                    j += 1
                    break
                j += 1
        if not block:
            i += 1
            continue

        # skip attributes and blank lines to reach the declaration
        k = j
        while k < len(lines) and (
            not lines[k].strip()
            or lines[k].strip().startswith("#[")
            or lines[k].strip().startswith("#!")
            or (lang == "rs" and lines[k].strip().startswith("///"))
        ):
            k += 1
        if k >= len(lines):
            i = j
            continue

        decl = lines[k]
        name, kind, callable_ = "", "item", False
        if lang == "rs":
            m = DECL_NAME_RS.match(decl)
            if m:
                name, kind = m.group(2), ("module" if m.group(1) == "mod" else "item")
                callable_ = m.group(1) == "fn"
            else:
                m2 = DECL_FIELD_RS.match(decl)
                name = m2.group(1) if m2 else decl.strip()[:40]
        else:
            m = DECL_TS.match(decl)
            if m:
                name = m.group(2)
                kind = "module" if m.group(1) in ("class", "interface") else "item"
                callable_ = bool(
                    m.group(1) == "function"
                    or re.search(r"\b" + re.escape(name) + r"\s*(<[^>]*>)?\s*\(", decl)
                )
            else:
                name = decl.strip()[:40]

        body = _brace_body(blank, offs[k])
        doc_text = "\n".join(t for _, t in block)
        units.append(
            Unit(path, lang, name, kind, doc_text, block[0][0], body, callable_, block)
        )
        i = j

    if module_doc:
        units.append(
            Unit(
                path,
                lang,
                "(module)",
                "module",
                "\n".join(t for _, t in module_doc),
                module_doc[0][0],
                blank,
                True,  # a module doc's "body" is the whole file: it CAN carry a mechanism
                module_doc,
            )
        )
    return units


# ══════════════════════════════════════════════════════════════════════════════════
# R1 — a cryptographic claim with no mechanism under it.
# ══════════════════════════════════════════════════════════════════════════════════
# ⚠ Every alternative here NAMES A CRYPTOGRAPHIC MECHANISM. A bare "ensures" or
# "requires" is ordinary English; a gate keyed on those reds on hundreds of honest
# docstrings on its first run and gets switched off by lunchtime.
CRYPTO_CLAIM = re.compile(
    r"""
      cryptographic(?:ally)?\s+(?:verif\w+|check\w+|enforc\w+|guarantee\w+|sound|bound|proven|prov\w+)
    | (?:was|is|are|were|been)\s+cryptographically\s+\w+
    | recursive(?:ly)?\s+(?:proof|proofs|verif\w+)
    | verif(?:y|ies|ied)\s+(?:a\s+|the\s+|each\s+)?(?:recursive\s+|zk\s+|valid\s+)?
      (?:proof|proofs|signature|signatures|snark|stark|witness|attestation)
    | (?:proof|signature|snark|stark|attestation)s?\s+(?:is|are|was|were|has\s+been|have\s+been)\s+verif\w+
    | requires?\s+(?:a\s+|the\s+)?(?:valid\s+)?(?:recursive\s+|zk\s+)?(?:proof|signature|snark|stark)\b
    | zk-?\s?proof\s+(?:verif|check)\w+
    | proof-gated
    | (?:verified|checked|attested)\s+by\s+(?:\w+(?:'s)?\s+){0,3}(?:proof|verifier|signature|snark|stark)
    """,
    re.I | re.X,
)

# ⚠ o1js's proof API is a CLOSED, NAMED vocabulary, so the TS set is exactly the one the
# specimen's grep used — `.verify(`, `Proof<`, `ZkProgram`, `SelfProof`, `DynamicProof` —
# plus the key/signature types. It deliberately does NOT count a DECLARATION named
# `verifyMembership`: naming a method "verify" is the claim under audit, not the
# mechanism answering it, and counting it would have laundered specimen 1 clean.
MECH_TS = re.compile(
    r"\b(?:Proof|SelfProof|DynamicProof|ZkProgram|VerificationKey|verificationKey"
    r"|Signature|Nullifier|MerkleWitness|MerkleMapWitness)\b"
    r"|\.verify\s*\("
)
# ⚠ Rust's is OPEN — verification is spelled `BiscuitToken::from_encoded(enc, pk)` and
# `Spk::parse` — so the Rust set is broad on purpose and counts a file's crypto IMPORTS
# too. It is SUBSTRING matching, not word boundaries: this tree spells mechanisms in
# composites (`binding_proof: TurnChainBindingProof`, `verify_vm_descriptor2`), and the
# word-boundary version reported `WholeChainProof` as a struct with no proof in it.
MECH_RS = re.compile(
    r"verif|proof|prover|prove_|signature|signing|signer|snark|stark|attest|witness"
    r"|sign_|_sign\b|\bsig\b|_sig\b|sig_|\bvk\b|_vk\b|vk_|merkle|nullifier|commitment"
    r"|ed25519|ecdsa|schnorr|dilithium|ml_dsa|mldsa|poseidon|blake3|sha2|sha256|hmac"
    r"|keypair|pubkey|public_key|PublicKey|SecretKey|SigningKey|Hasher|digest",
    re.I,
)


# ⚠ A DISCLAIMER IS NOT A CLAIM. This tree states absences constantly and precisely —
# "does NOT verify signatures", "present/absent but not cryptographically checked",
# "actor NOT cryptographically verified". Measured on the first full run those were 14 of
# 80 R1 hits, and every one of them was a sentence doing exactly what this gate wants
# sentences to do. Firing on them would teach a reader that honesty trips the gate.
NEGATED = re.compile(
    r"\b(not|NOT|never|no|without|nothing|neither|un-?verified|un-?checked|un-?proven"
    r"|cannot|can\s+not|does\s+n[o']t|is\s+n[o']t|are\s+n[o']t|lacks?|absent|missing)\b"
)


# ⚠ A QUOTED claim is a claim being REPORTED, not made. This repo writes about its own
# prose constantly — `a docstring that says "cryptographically verified" is a claim` —
# and its own self-test caught R1 firing on exactly that sentence. Quoted spans are
# blanked before matching; backticked spans are NOT, because a code span is how a doc
# names the identifier a claim is about and R2 needs it.
_QUOTED = re.compile(r"\"[^\"]{0,200}\"|\u201c[^\u201d]{0,200}\u201d")


def unquote(text: str) -> str:
    return _QUOTED.sub(lambda m: " " * len(m.group(0)), text)


def rule_r1(u: Unit, ctx: FileCtx) -> list[tuple[str, str]]:
    """A cryptographic claim in a FILE that has none of that mechanism's vocabulary.

    ⚠ FILE-SCOPED, NOT DECLARATION-SCOPED, and the difference is the whole gate. Scoped
    to the declaration's own body this reported 34 sites on `main` and every one I read
    was honest: a constructor whose `- \\`participant_keys\\`:` bullet says signatures are
    checked against them SOMEWHERE ELSE; a `parse` whose verification happens inside
    `BiscuitToken::from_encoded`. Scoped to the file it reports ONE — because the thing
    specimen 1 actually was is a MODULE that names a four-stage recursive proof pipeline
    and contains no proof vocabulary at all. That is how it was established (by grep,
    over the file) and it is how it is checked.

    THE PRICE, said plainly: a false claim in a file where a SIBLING function does real
    crypto reads as clean here. R1 catches the module that claims a mechanism it does
    not have, not the function that borrows its neighbour's.

    ⚠ FUNCTIONS AND MODULE DOCS ONLY. A FIELD's doc — `/// The federation root the proof
    was verified against.` — states the field's PROVENANCE, not a mechanism it runs;
    field, const and type docs were 39 of the first run's 80 hits and all 39 read
    honest.
    """
    hits = []
    if not u.is_callable:
        return hits
    if ctx.has_mech or not CRYPTO_CLAIM.search(unquote(u.doc)):
        return hits
    for lineno, text in u.doc_lines:
        m = CRYPTO_CLAIM.search(unquote(text))
        if not m:
            continue
        # the sentence around the match, so a disclaimer three paragraphs away does not
        # launder a claim and a negation in the claim itself does not read as one
        lo = max(0, m.start() - 120)
        if NEGATED.search(text[lo : m.end() + 60]):
            continue
        hits.append((f"{u.path}:{lineno}", text.strip()))
        break  # one finding per declaration; the doc is the unit, not the line
    return hits


# ══════════════════════════════════════════════════════════════════════════════════
# R2 — a protective claim on a field nothing reads.
# ══════════════════════════════════════════════════════════════════════════════════
# ⚠ `blocks` and `stops` are OUT, and deliberately. In this tree "block" is a NOUN on
# almost every line that contains it — `block.time`, "Block deadline", "Per Cav-Codex
# Block 3", "the first squeeze block" — and including it made R2 report five fields as
# unguarded whose docs were not making a protective claim at all. A protective verb has
# to be one that cannot be read as a noun here.
PROTECTIVE = re.compile(
    r"\b(prevents?|preventing|guards?\s+against|guarding\s+against"
    r"|makes?\s+\w+\s+impossible|rules?\s+out|forbids?|precludes?|defends?\s+against)\b",
    re.I,
)
# ⚠ The identifier must be NAMED AS AN IDENTIFIER, not merely be an English word that
# happens to collide with a field name. `fhegg-fhe/src/additive.rs` says "the exact-integer
# grid the BFV fold operates over — PROVABLY forbids a mint", and `fold` is also a struct
# field in that file; the sentence is about the integer gate and not about the field at
# all. So: backticked (`nullifierRoot`), or the SUBJECT of a `- name:` bullet, which is
# how specimen 2's state-layout list named its fields.
IDENT_BACKTICK = re.compile(r"`([A-Za-z_$][A-Za-z0-9_$]*)`")
IDENT_BULLET = re.compile(r"^\s*[-*+]?\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*:")


def claim_identifiers(text: str) -> list[str]:
    out = list(IDENT_BACKTICK.findall(text))
    m = IDENT_BULLET.match(text)
    if m:
        out.append(m.group(1))
    return out

# A WRITE of `X` in this file. R2 needs one: without it the file merely DECLARES the
# field and every read lives in another crate, which is the ordinary shape of a
# `types.rs` and not a wound. `nullifierRoot` had `this.nullifierRoot.set(Field(0))` —
# this file wrote it, this file never read it, and nothing else could have.
def _write_count(blank: str, ident: str) -> int:
    pat = (
        rf"\b{re.escape(ident)}\s*\.\s*set\s*\("            # o1js State.set
        rf"|\b{re.escape(ident)}\s*=[^=]"                   # plain assignment
        rf"|\bset_{re.escape(ident)}\s*\(|\b{re.escape(ident)}_mut\s*\("
    )
    return len(re.findall(pat, blank))

# What counts as a WRITE of `X` — everything else that names X is a read.
def _read_count(blank: str, ident: str, lang: str) -> int:
    reads = 0
    for m in re.finditer(rf"\b{re.escape(ident)}\b", blank):
        a, b = m.start(), m.end()
        tail = blank[b : b + 30]
        head = blank[max(0, a - 30) : a]
        if lang == "ts":
            if re.match(r"\s*\.\s*set\s*\(", tail):
                continue
            if re.match(r"\s*=\s*State\s*<", tail):
                continue  # the declaration
        if re.match(r"\s*=[^=]", tail):
            continue  # plain assignment
        if re.search(r"\b(let|const|var|state|pub)\s*(\([^)]*\))?\s*$", head):
            continue  # the declaration
        reads += 1
    return reads


DECLARED_STATE = re.compile(r"@state\([^)]*\)\s+([A-Za-z_$][\w$]*)")
DECLARED_FIELD = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?([a-z_][a-z0-9_]{3,})\s*:", re.M)


class FileCtx:
    """Per-file state computed ONCE.

    ⚠ Not an optimisation for its own sake. Recomputing the declared-field set inside
    the per-declaration loop measured 36 s on SIX FILES — a multi-line regex over a
    200 KB source, 259 times. A tier-0 gate that takes minutes is a gate someone moves
    to nightly and then stops reading.
    """

    def __init__(self, blank: str, lang: str):
        self.blank = blank
        self.lang = lang
        self._declared: set[str] | None = None
        self._reads: dict[str, int] = {}
        self._writes: dict[str, int] = {}
        # ⚠ Cached, not recomputed per declaration. The mechanism regex is long and
        # case-insensitive; running it over the whole file once per documented
        # declaration (~20,000 of them) put the full scan past two minutes.
        self.has_mech = bool((MECH_TS if lang == "ts" else MECH_RS).search(blank))

    @property
    def declared(self) -> set[str]:
        if self._declared is None:
            self._declared = set(DECLARED_STATE.findall(self.blank)) | set(
                DECLARED_FIELD.findall(self.blank)
            )
        return self._declared

    def reads(self, ident: str) -> int:
        if ident not in self._reads:
            self._reads[ident] = _read_count(self.blank, ident, self.lang)
        return self._reads[ident]

    def writes(self, ident: str) -> int:
        if ident not in self._writes:
            self._writes[ident] = _write_count(self.blank, ident)
        return self._writes[ident]


def rule_r2(u: Unit, ctx: FileCtx) -> list[tuple[str, str]]:
    hits = []
    if not PROTECTIVE.search(u.doc) or not ctx.declared:
        return hits
    for lineno, text in u.doc_lines:
        if not PROTECTIVE.search(text):
            continue
        for ident in claim_identifiers(text):
            if ident not in ctx.declared:
                continue
            if ctx.writes(ident) == 0:
                continue  # this file does not own the field; its readers are elsewhere
            if ctx.reads(ident) == 0:
                hits.append(
                    (
                        f"{u.path}:{lineno}",
                        f"`{ident}` is WRITTEN here and never READ — {text.strip()}",
                    )
                )
    return hits


# R2b — a capability the file does not declare.
CAPABILITY = re.compile(
    r"\bcan\s+be\s+(rotated|revoked|paused|upgraded|slashed|withdrawn|frozen|migrated|reassigned)\b",
    re.I,
)
CAP_STEM = {
    "rotated": "rotat", "revoked": "revok", "paused": "paus", "upgraded": "upgrad",
    "slashed": "slash", "withdrawn": "withdraw", "frozen": "freeze", "migrated": "migrat",
    "reassigned": "reassign",
}


def rule_r2b(u: Unit, ctx: FileCtx) -> list[tuple[str, str]]:
    """A capability the file's code never names.

    ⚠ MODULE AND CLASS DOCS ONLY, and the STEM ANYWHERE IN THE CODE clears it. Scoped
    wider it reported three sites on `main` and all three were honest: an enum variant
    literally called `CanRevoke` whose doc says "can be revoked" (the declaration IS the
    capability), a `persist` schema const, and a fn doc saying referenced cells "can be
    frozen-checked". Specimen 2's shape is a SECURITY MODEL enumerated in a class header
    — "Relay authority can be rotated via governance proof" — where the whole file has
    no `rotate` in it anywhere.
    """
    hits = []
    if u.kind != "module" or not CAPABILITY.search(u.doc):
        return hits
    for lineno, text in u.doc_lines:
        for m in CAPABILITY.finditer(text):
            stem = CAP_STEM[m.group(1).lower()]
            if re.search(rf"(?i){stem}", ctx.blank):
                continue
            hits.append(
                (f"{u.path}:{lineno}", f"no `{stem}*` declaration — {text.strip()}")
            )
    return hits


# ══════════════════════════════════════════════════════════════════════════════════
# R3 — a stale structural claim, checked against the real import graph.
# ══════════════════════════════════════════════════════════════════════════════════
NOT_IMPORTED = re.compile(
    r"(?:NOT|not)\s+imported\s+(?:by|from)\s+(?:the\s+)?[`'\"]?([A-Za-z0-9_./]+)",
)


def lean_module_of(path: Path) -> str:
    rel = path.relative_to(ROOT / "metatheory")
    return str(rel.with_suffix("")).replace(os.sep, ".")


LEAN_IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)")


def lean_header_imports(text: str) -> set[str]:
    """Every `import` in a Lean file, by walking the header and stopping at the body.

    ⚠ THE OBVIOUS SHORTCUT IS WRONG HERE AND IT WENT SILENTLY WRONG. Slicing the first
    64 KB and running one `re.M` findall looks equivalent — Lean requires all imports
    before any command — but `metatheory/Dregg2.lean` is 1.25 MB with its last import on
    LINE 1674, because every import carries a paragraph of annotation. The truncated
    version read ~90 of ~1,600 edges, R3's whole harvest went to ZERO, and the run
    printed `OK`. That is the fail-open shape this file exists to catch, arriving inside
    the file itself. The `MIN_IMPORT_EDGES` floor below is what makes it impossible to
    ship again.
    """
    out: set[str] = set()
    depth = 0
    for line in text.split("\n"):
        t = line.strip()
        if depth:
            depth += t.count("/-") - t.count("-/")
            continue
        if not t or t.startswith("--"):
            continue
        if t.startswith("/-"):
            depth = 1 + t.count("/-", 2) - t.count("-/")
            continue
        m = LEAN_IMPORT.match(t)
        if m:
            out.add(m.group(1))
            continue
        break  # the first real command: the import block is over
    return out


def build_lean_graph() -> tuple[dict[str, set[str]], dict[str, Path], dict[str, str]]:
    """The import graph plus every module's text, read ONCE.

    ⚠ Each Lean file was being opened twice — once for its imports, once for its prose —
    and this tree's Lean files run to hundreds of kilobytes. Reading once and slicing the
    header for the import scan is most of this rule's cost.
    """
    graph: dict[str, set[str]] = {}
    files: dict[str, Path] = {}
    texts: dict[str, str] = {}
    for p in (ROOT / "metatheory").rglob("*.lean"):
        if any(part in SKIP_DIRS for part in p.parts):
            continue
        mod = lean_module_of(p)
        try:
            text = p.read_text(errors="replace")
        except OSError:
            continue
        files[mod] = p
        texts[mod] = text
        graph[mod] = lean_header_imports(text)
    return graph, files, texts


def reaches(graph: dict[str, set[str]], src: str, dst: str) -> bool:
    seen, stack = set(), [src]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        for nxt in graph.get(cur, ()):
            if nxt == dst:
                return True
            stack.append(nxt)
    return False


def rule_r3(
    graph: dict[str, set[str]], files: dict[str, Path], texts: dict[str, str]
) -> list[tuple[str, str]]:
    hits = []
    for mod, path in sorted(files.items()):
        text = texts[mod]
        if "imported" not in text:
            continue
        for i, line in enumerate(text.split("\n"), 1):
            m = NOT_IMPORTED.search(line)
            if not m:
                continue
            raw = m.group(1).strip("`'\".")
            # "Dregg2.lean" / "metatheory/Dregg2.lean" / "Dregg2" / "DyckStackRefine"
            cand = raw.replace("metatheory/", "").replace("/", ".")
            if cand.endswith(".lean"):
                cand = cand[: -len(".lean")]
            target = None
            if cand in files:
                target = cand
            else:
                tail = [k for k in files if k.split(".")[-1] == cand.split(".")[-1]]
                if len(tail) == 1:
                    target = tail[0]
            if target is None or target == mod:
                continue
            if reaches(graph, target, mod):
                direct = " (DIRECTLY)" if mod in graph.get(target, ()) else " (transitively)"
                hits.append(
                    (
                        f"{str(path.relative_to(ROOT))}:{i}",
                        f"`{target}` DOES import `{mod}`{direct} — {line.strip()[:150]}",
                    )
                )
    return hits


# ══════════════════════════════════════════════════════════════════════════════════
# The allowlist.
# ══════════════════════════════════════════════════════════════════════════════════
@dataclass
class AllowRow:
    path: str
    rule: str
    text: str
    reason: str
    used: bool = False

    @property
    def is_harvest(self) -> bool:
        return self.reason.startswith("HARVEST ")


def load_allow() -> tuple[list[AllowRow], list[str]]:
    rows, errs = [], []
    if not ALLOW.exists():
        return rows, ["missing allowlist: scripts/prose-claims-allow.tsv"]
    for i, line in enumerate(ALLOW.read_text().split("\n"), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            errs.append(f"{ALLOW.name}:{i}: need 4 TAB-separated fields, got {len(parts)}")
            continue
        p, rule, text, reason = (x.strip() for x in parts)
        if not text:
            errs.append(f"{ALLOW.name}:{i}: the claim-text key is empty — that row mutes "
                        "every finding at that path, which is not an exemption")
            continue
        if len(reason) < MIN_REASON:
            errs.append(
                f"{ALLOW.name}:{i}: reason is {len(reason)} chars, needs >= {MIN_REASON} — "
                f'"{reason}"'
            )
            continue
        rows.append(AllowRow(p, rule, text, reason))
    harvest = sum(1 for r in rows if r.is_harvest)
    if harvest > HARVEST_CEILING:
        errs.append(
            f"{ALLOW.name}: {harvest} HARVEST rows, ceiling is {HARVEST_CEILING}. A "
            "HARVEST row records a TRUE finding this gate made and nobody has repaired. "
            "Raising the ceiling is allowed and is a visible diff; adding a row without "
            "raising it is how a baseline becomes a mute."
        )
    return rows, errs


def allowed(rows: list[AllowRow], rule: str, loc: str, text: str) -> bool:
    path = loc.split(":")[0]
    for r in rows:
        if r.rule == rule and r.path == path and r.text in text:
            r.used = True
            return True
    return False


# ══════════════════════════════════════════════════════════════════════════════════
# The scan.
# ══════════════════════════════════════════════════════════════════════════════════
def iter_sources(root: Path, exts=(".rs", ".ts")):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS and not d.startswith(".")]
        for fn in filenames:
            if fn.endswith(exts) and not fn.endswith(".d.ts"):
                yield Path(dirpath) / fn


@dataclass
class Scan:
    findings: list[tuple[str, str, str]] = field(default_factory=list)  # rule, loc, text
    rs_files: int = 0
    ts_files: int = 0
    claim_files: int = 0
    units: int = 0
    lean_files: int = 0
    import_edges: int = 0


def scan(root: Path, do_r3: bool = True) -> Scan:
    out = Scan()
    for p in iter_sources(root):
        try:
            text = p.read_text(errors="replace")
        except OSError:
            continue
        if p.suffix == ".rs":
            out.rs_files += 1
        else:
            out.ts_files += 1
        # ── PRE-FILTER ────────────────────────────────────────────────────────────
        # No claim vocabulary anywhere in the raw text means no rule here can fire, so
        # the per-line declaration walk is skipped. This is what makes the sweep a
        # tier-0 cost rather than a nightly one: ~4,300 files walked, a few hundred
        # parsed. It is a SUPERSET test on the raw text (comments included) — never a
        # narrowing of what the rules see once a file is in.
        low = text.lower()
        may_r2 = any(t in low for t in R2_LITERALS) and PROTECTIVE.search(text)
        may_r2b = "can be" in low and CAPABILITY.search(text)
        may_r1 = any(t in low for t in R1_LITERALS) and CRYPTO_CLAIM.search(text)
        if not (may_r1 or may_r2 or may_r2b):
            continue
        rel = str(p.relative_to(root))
        blank = strip_noise(text)
        ctx = FileCtx(blank, "rs" if p.suffix == ".rs" else "ts")
        if not (may_r2 or may_r2b) and ctx.has_mech:
            continue  # only R1 was possible and the file carries its mechanism
        out.claim_files += 1
        units = extract_units(rel, text)
        out.units += len(units)
        for u in units:
            for loc, t in rule_r1(u, ctx):
                out.findings.append(("R1", loc, t))
            for loc, t in rule_r2(u, ctx):
                out.findings.append(("R2", loc, t))
            for loc, t in rule_r2b(u, ctx):
                out.findings.append(("R2b", loc, t))
    if do_r3 and (root / "metatheory").is_dir():
        graph, files, texts = build_lean_graph()
        out.lean_files = len(files)
        out.import_edges = sum(len(v) for v in graph.values())
        for loc, t in rule_r3(graph, files, texts):
            out.findings.append(("R3", loc, t))
    return out


def report(sc: Scan, rows: list[AllowRow], check_floors: bool) -> int:
    errs = []
    live = []
    for rule, loc, text in sc.findings:
        if allowed(rows, rule, loc, text):
            continue
        live.append((rule, loc, text))

    print(
        f"scanned  {sc.rs_files} .rs  {sc.ts_files} .ts  "
        f"{sc.lean_files} .lean ({sc.import_edges} import edges)   "
        f"parsed  {sc.claim_files} files carrying claim vocabulary"
        f"  ({sc.units} documented declarations)"
    )
    if check_floors:
        for got, floor, what in (
            (sc.rs_files, MIN_RS_FILES, "Rust files"),
            (sc.ts_files, MIN_TS_FILES, "TypeScript files"),
            (sc.claim_files, MIN_CLAIM_FILES, "files carrying claim vocabulary"),
            (sc.units, MIN_UNITS, "documented declarations"),
            (sc.lean_files, MIN_LEAN_FILES, "Lean files"),
            (sc.import_edges, MIN_IMPORT_EDGES, "Lean import edges"),
        ):
            if got < floor:
                errs.append(
                    f"FLOOR: saw {got} {what}, expected >= {floor} — the reader is blind, "
                    "not the tree clean"
                )

    harvest = [r for r in rows if r.is_harvest]
    if harvest:
        print(f"\nharvest  {len(harvest)} TRUE findings baselined and NOT repaired "
              f"(ceiling {HARVEST_CEILING}) — see {ALLOW.name}")
        for r in sorted(harvest, key=lambda x: x.path):
            print(f"    [{r.rule}] {r.path}")

    stale = [r for r in rows if not r.used]
    for r in stale:
        errs.append(
            f"STALE EXEMPTION {ALLOW.name}: {r.path} [{r.rule}] no longer carries "
            f'"{r.text[:60]}" — delete the row'
        )

    if live:
        print()
        for rule, loc, text in sorted(live):
            print(f"  [{rule}] {loc}\n        {text[:200]}")
    print()
    print(f"findings {len(live)}   exempted {sum(1 for r in rows if r.used)}")
    for e in errs:
        print(f"  ! {e}")
    if live or errs:
        print("\nFAIL — a claim above is not carried by the code under it.")
        return 1
    print("OK — every cryptographic claim, protective claim and structural claim "
          "checked has its mechanism.")
    return 0


# ══════════════════════════════════════════════════════════════════════════════════
# --historical — score against the six specimens, as they were BEFORE repair.
# ══════════════════════════════════════════════════════════════════════════════════
SPECIMENS = [
    ("1  DreggFederation.advanceState 'cryptographically verified'",
     "bc504032d^", "bridge/mina-zkapp/src/DreggFederation.ts", True),
    ("2  the same file's header: nullifierRoot 'prevents double-withdrawal'",
     "bc504032d^", "bridge/mina-zkapp/src/DreggFederation.ts", True),
    ("3  ivc_turn_chain 'CLOSED' vs plonky3_recursion_impl 'cannot'",
     "dea0e1f22^", "circuit-prove/src/ivc_turn_chain.rs", False),
    ("4  MinaBinprot §7 'the kernel will not reduce at these sizes'",
     "d9e8b0cd7^", "metatheory/Dregg2/Bridge/MinaBinprot.lean", False),
    ("5  the 630x kernel->compiled ratio nothing measured",
     "90cedda2b^", "docs/MINA-CHECKPOINT-CADENCE.md", False),
    ("6  PastaMsmSliced loConstGate/hiConstGate vs an unreachable forgery",
     "24e9bc2f9^", "metatheory/Dregg2/Circuit/Emit/PastaMsmSliced.lean", False),
]


def historical() -> int:
    print("═══ THE SIX SPECIMENS, AS THEY WERE BEFORE REPAIR ═══\n")
    caught = 0
    expected_caught = 0
    wrong = []
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for label, rev, path, expect in SPECIMENS:
            try:
                blob = subprocess.run(
                    ["git", "show", f"{rev}:{path}"],
                    cwd=ROOT, capture_output=True, text=True, check=True,
                ).stdout
            except subprocess.CalledProcessError:
                print(f"  ??  {label}\n      could not read {rev}:{path}")
                continue
            dst = tmp / path
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(blob)

            hits = []
            if path.endswith((".rs", ".ts")):
                ctx = FileCtx(strip_noise(blob), "rs" if path.endswith(".rs") else "ts")
                for u in extract_units(path, blob):
                    hits += [("R1", l, t) for l, t in rule_r1(u, ctx)]
                    hits += [("R2", l, t) for l, t in rule_r2(u, ctx)]
                    hits += [("R2b", l, t) for l, t in rule_r2b(u, ctx)]
            # R3 needs the graph, and the graph is HEAD's; the two live R3 findings are
            # reported by the ordinary scan, so they are not replayed here.

            if expect:
                expected_caught += 1
            mark = "CAUGHT" if hits else "missed"
            if hits:
                caught += 1
            agree = (bool(hits) == expect)
            if not agree:
                wrong.append(label)
            print(f"  {mark:7s} {'(as designed)' if agree else '(!! DISAGREES WITH THE DESIGN)'}  {label}")
            for rule, loc, t in hits[:3]:
                print(f"            [{rule}] {loc}  {t[:120]}")
    print(f"\n  {caught} of {len(SPECIMENS)} flagged; {expected_caught} are the ones "
          "this gate targets, so the score and the design agree.")
    if wrong:
        print("\n  ⚠ THE DESIGN AND THE MEASUREMENT DISAGREE on: " + "; ".join(wrong))
        print("  Either a rule regressed or its stated scope is wrong. Both are failures.")
        return 1
    print("  3, 5 and 6 need a READER; 4 is a different gate. All four are named in the")
    print("  module header rather than left to be discovered as a gap.")
    print("\n  ⚠ R3 IS NOT REPLAYED HERE. It resolves against HEAD's import graph, so a"
          "\n  historical file would be checked against a graph it never lived in. Its"
          "\n  evidence is the ORDINARY run, which harvested twelve live findings, and the"
          "\n  synthetic graphs in --self-test.")
    return 0


# ══════════════════════════════════════════════════════════════════════════════════
# --contradiction-probe — the rule that was PROTOTYPED AND REJECTED, kept runnable.
# ══════════════════════════════════════════════════════════════════════════════════
CLOSED_WORD = re.compile(r"\b(CLOSED|RESOLVED|FIXED|no longer|now pinned)\b")
NEGATIVE_WORD = re.compile(r"\b(does NOT|cannot|can not|is NOT|never|un(pinned|checked))\b")


def contradiction_probe() -> int:
    """The cheap approximation of specimen 3, MEASURED so the rejection is checkable.

    Keys a status word to the identifiers on its line and looks for the same
    identifiers under a negative-capability word in another file. If the count printed
    here is large, this rule cries wolf and must not ship — which is what happened.
    """
    pos: dict[str, list[str]] = {}
    neg: dict[str, list[str]] = {}
    for p in iter_sources(ROOT):
        try:
            text = p.read_text(errors="replace")
        except OSError:
            continue
        rel = str(p.relative_to(ROOT))
        for i, line in enumerate(text.split("\n"), 1):
            s = line.strip()
            if not (s.startswith("//") or s.startswith("*") or s.startswith("/*")):
                continue
            keys = {w for w in re.findall(r"\b[a-z][a-z_]{5,}\b", s.lower())}
            if CLOSED_WORD.search(line):
                for k in keys:
                    pos.setdefault(k, []).append(f"{rel}:{i}")
            if NEGATIVE_WORD.search(line):
                for k in keys:
                    neg.setdefault(k, []).append(f"{rel}:{i}")
    pairs = 0
    shown = 0
    for k, plist in sorted(pos.items()):
        nlist = neg.get(k)
        if not nlist:
            continue
        for a in plist:
            for b in nlist:
                if a.split(":")[0] == b.split(":")[0]:
                    continue
                pairs += 1
                if shown < 12:
                    print(f"  {k:24s} {a}  vs  {b}")
                    shown += 1
    print(f"\n  {pairs} contradicting pairs on the tree by this rule.")
    print("  A gate people disable is worse than none. This one is NOT shipped;")
    print("  specimen 3 stays in THE BLIND SPOTS, by name.")
    return 0


# ══════════════════════════════════════════════════════════════════════════════════
# --self-test — can it go red?
# ══════════════════════════════════════════════════════════════════════════════════
FAULTS = [
    ("R1 crypto claim, no mechanism", "ts", "faults/a.ts", """
export class Thing {
  /**
   * Advance the root.
   *
   * If this method executes successfully, the state transition was
   * cryptographically verified.
   */
  advance(oldRoot: Field, newRoot: Field) {
    this.root.set(newRoot);
  }
}
"""),
    ("R1 crypto claim in Rust, no mechanism", "rs", "faults/b.rs", """
/// Accept the header. The caller must supply a recursive proof and this
/// function verifies the proof before returning.
pub fn accept(h: Header) -> bool {
    h.height > 0
}
"""),
    ("R2 protective claim on a write-only field", "ts", "faults/c.ts", """
/**
 * A contract.
 * - nullifierRoot: Merkle root of spent nullifiers (prevents double-withdrawal)
 */
export class C {
  @state(Field) nullifierRoot = State<Field>();
  init() { this.nullifierRoot.set(Field(0)); }
}
"""),
    ("R2b a capability with no declaration", "ts", "faults/d.ts", """
/**
 * Holds the relay.
 * - Relay authority can be rotated via governance proof
 */
export class D {
  @state(Field) relayAuthority = State<Field>();
  read() { return this.relayAuthority.get(); }
}
"""),
]

QUIET = [
    ("a crypto claim WITH its mechanism", "ts", "quiet/a.ts", """
export class Ok {
  /** Verifies the proof and advances. Requires a valid proof. */
  advance(p: DynamicProof<Field, Field>) {
    p.verify();
  }
}
"""),
    ("a protective claim on a field that IS read", "ts", "quiet/b.ts", """
/**
 * - seen: set of seen ids (prevents replay)
 */
export class Ok2 {
  @state(Field) seen = State<Field>();
  use() { const s = this.seen.getAndRequireEquals(); s.assertEquals(Field(1)); }
}
"""),
    ("ordinary English: 'ensures', 'requires', 'guarantees'", "rs", "quiet/c.rs", """
/// Ensures the buffer is large enough. Requires the caller to hold the lock.
/// This guarantees no reallocation happens during the loop.
pub fn reserve(&mut self, n: usize) { self.buf.reserve(n); }
"""),
    ("prose ABOUT the disease, in a comment", "rs", "quiet/d.rs", """
/// A docstring that says "cryptographically verified" is a claim, and this
/// module's job is to notice one. See `verify_claim` for the mechanism.
pub fn note() -> &'static str { "verify" }
"""),
]


def _self_test_r3() -> int:
    """R3 against synthetic import graphs, plus the header-truncation regression.

    ⚠ The last case is not decoration. While this gate was being written, the import
    scan sliced the first 64 KB of each Lean file — plenty for any real import block,
    except `metatheory/Dregg2.lean`, which is 1.25 MB because every import carries a
    paragraph of annotation and whose last import is on LINE 1674. R3's entire harvest
    silently went to zero and the run printed `OK`. Both the fix and the floor that
    makes it un-shippable are checked here.
    """
    bad = 0
    graph = {
        "Root": {"Mid", "Honest"},
        "Mid": {"Leaf"},
        "Leaf": set(),
        "Honest": set(),
        "Orphan": set(),
    }
    files = {k: ROOT / f"metatheory/{k}.lean" for k in graph}

    def run(texts):
        return rule_r3(graph, files, texts)

    cases = [
        ("R3 a DIRECT stale claim", True,
         {"Mid": "-- NOT imported by `Root`\n", **{k: "" for k in graph if k != "Mid"}}),
        ("R3 a TRANSITIVE stale claim", True,
         {"Leaf": "/-! not imported from `Root` -/\n", **{k: "" for k in graph if k != "Leaf"}}),
        ("an HONEST 'NOT imported' claim stays quiet", False,
         {"Orphan": "-- NOT imported by `Root`\n", **{k: "" for k in graph if k != "Orphan"}}),
        ("a claim about a module that does not exist stays quiet", False,
         {"Mid": "-- NOT imported by `NoSuchModule`\n", **{k: "" for k in graph if k != "Mid"}}),
    ]
    for label, want_red, texts in cases:
        hits = run(texts)
        if bool(hits) == want_red:
            print(f"  {'RED   ' if want_red else 'quiet '} {label}")
        else:
            print(f"  ⚠ {'MISS' if want_red else 'WOLF'}  {label}")
            bad += 1

    # the 64 KB truncation, replayed
    big = "\n".join(
        [f"import Dregg2.Filler{i} -- {'x' * 900}" for i in range(200)]
        + ["import Dregg2.TheLastOne", "", "def f := 1"]
    )
    assert len(big) > 65536, "the regression fixture must exceed the old truncation point"
    got = lean_header_imports(big)
    if "Dregg2.TheLastOne" in got and len(got) == 201:
        print(f"  RED    a 1.25 MB-shaped header is read WHOLE ({len(got)} edges, "
              "not the ~70 a 64 KB slice saw)")
    else:
        print(f"  ⚠ MISS the header scan lost imports past 64 KB ({len(got)} edges)")
        bad += 1
    return bad


def _self_test_allowlist() -> int:
    """The exemption list must refuse to be a mute."""
    bad = 0
    import io
    global ALLOW
    real = ALLOW
    cases = [
        ("a reason under 20 chars is REFUSED", "a/b.rs\tR1\tsome claim\tfine\n", True),
        ("an empty claim-text key is REFUSED", "a/b.rs\tR1\t\ta perfectly long reason here\n", True),
        ("a three-field row is REFUSED", "a/b.rs\tR1\tsome claim\n", True),
        ("a well-formed row is accepted",
         "a/b.rs\tR1\tsome claim\tthis claim is true because the mechanism is one call away\n",
         False),
        ("HARVEST rows past the ceiling are REFUSED",
         "".join(f"a/b{i}.rs\tR1\tclaim {i}\tHARVEST 2026-07-30: a true finding, "
                 f"routed to its owner lane\n" for i in range(HARVEST_CEILING + 1)),
         True),
    ]
    with tempfile.TemporaryDirectory() as td:
        for label, body, want_err in cases:
            f = Path(td) / "allow.tsv"
            f.write_text(body)
            ALLOW = f
            try:
                _, errs = load_allow()
            finally:
                ALLOW = real
            if bool(errs) == want_err:
                print(f"  {'RED   ' if want_err else 'quiet '} {label}")
            else:
                print(f"  ⚠ {'MISS' if want_err else 'WOLF'}  {label}: {errs}")
                bad += 1
    return bad


def self_test() -> int:
    print("═══ CAN IT GO RED? ═══\n")
    bad = 0
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for label, lang, rel, src in FAULTS:
            p = tmp / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(src)
            ctx = FileCtx(strip_noise(src), lang)
            hits = []
            for u in extract_units(rel, src):
                hits += [("R1", l, t) for l, t in rule_r1(u, ctx)]
                hits += [("R2", l, t) for l, t in rule_r2(u, ctx)]
                hits += [("R2b", l, t) for l, t in rule_r2b(u, ctx)]
            if hits:
                print(f"  RED    {label}")
                for rule, loc, t in hits[:2]:
                    print(f"           [{rule}] {t[:110]}")
            else:
                print(f"  ⚠ MISS {label}  — the gate did not fire on its own fault")
                bad += 1

        print()
        for label, lang, rel, src in QUIET:
            p = tmp / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(src)
            ctx = FileCtx(strip_noise(src), lang)
            hits = []
            for u in extract_units(rel, src):
                hits += [("R1", l, t) for l, t in rule_r1(u, ctx)]
                hits += [("R2", l, t) for l, t in rule_r2(u, ctx)]
                hits += [("R2b", l, t) for l, t in rule_r2b(u, ctx)]
            if hits:
                print(f"  ⚠ WOLF {label}")
                for rule, loc, t in hits[:2]:
                    print(f"           [{rule}] {t[:110]}")
                bad += 1
            else:
                print(f"  quiet  {label}")

    # ── R3, which the source-file fixtures above cannot reach ────────────────────
    print()
    bad += _self_test_r3()

    # ── the allowlist's own discipline ───────────────────────────────────────────
    print()
    bad += _self_test_allowlist()

    # The floors must be able to go red too: a blinded reader must not read as clean.
    print()
    blind = Scan(rs_files=1, ts_files=1, claim_files=1, units=1, lean_files=1,
                 import_edges=1)
    rc = report(blind, [], check_floors=True)
    if rc == 0:
        print("  ⚠ MISS a blinded reader reported CLEAN")
        bad += 1
    else:
        print("  RED    a blinded reader is a FAILURE, not a pass")

    print()
    if bad:
        print(f"SELF-TEST FAILED: {bad} problem(s).")
        return 1
    print("SELF-TEST OK — every fault fires, every honest doc stays quiet, "
          "a blind reader fails.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--historical", action="store_true")
    ap.add_argument("--contradiction-probe", action="store_true")
    ap.add_argument("--root", default=str(ROOT))
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    if a.historical:
        return historical()
    if a.contradiction_probe:
        return contradiction_probe()
    rows, errs = load_allow()
    if errs:
        for e in errs:
            print(f"  ! {e}")
        return 1
    sc = scan(Path(a.root))
    return report(sc, rows, check_floors=(a.root == str(ROOT)))


if __name__ == "__main__":
    sys.exit(main())
