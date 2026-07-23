#!/usr/bin/env python3
"""binding_surface_complete.py — THE COMPLETION PREDICATE for the grounded-reduction sweep.

Run:  python3 scripts/binding_surface_complete.py /Users/ember/dev/breadstuffs/metatheory
Exit 0  <=>  the binding surface is FINISHED.  Prints the five residual counts.
`-v` lists every residual site.

FIVE residual classes (a declaration counted here is work REMAINING, not a bug in the ruler):

A / TIER-1  no declaration STATEMENT mentions a refuted INJECTIVITY floor
            (Poseidon2SpongeCR / compressNInjective / compressInjective) outside the allow-list.
            All three are pure-injectivity carriers, FALSE for any compressing hash.

B / TIER-2  every exported bare-disjunction headline (`*_or_collides`, `*_or_collision`,
            `*_or_collide`, `*_or_forges`, optional `_spec`) has an `*_advantage_bound` sibling.
            A bare disjunction with no advantage bound is a statement that never quantifies the
            collision branch.

C / TIER-3  every `*_advantage_bound` has a `*_from_polyTime` sibling that mentions IsPolyTime.
            (Historical tier: it measured the *pairing* discipline of the IsPolyTime era. Its
            members become tier-E residuals the moment they are paired; both drain to zero when
            sites re-point onto the keyed ROM floor, `Dregg2/Crypto/RomBindingReduction.lean`.)

D / TIER-4  no declaration carries `HashCR` in HYPOTHESIS-BINDER position `(h : HashCR …)`.
            `HashCR` (Dregg2/Crypto/HermineHintMLWE.lean:354) is pure injectivity — the FOURTH
            refuted floor: Dregg2/Circuit/HashFloorHonesty.lean ("TOOTH 3") proves `¬ HashCR cr`
            for any compressing commit-reveal. Binder-position is the strict, interpretable test
            (a `: HashCR` CONCLUSION is a satisfiability witness, not a carrier), and it is kept
            a SEPARATE tier rather than folded into A so A stays comparable across runs.
            `\\bHashCR\\b` never matches `HashCRHardQuant` or `BindingHashCR`.

E / TIER-5  no theorem/lemma instantiates a collision floor at `Eff := IsPolyTime`. That floor is
            proved FALSE at deployed parameters (Dregg2/Exec/SystemRootsBindingReduction.lean:516
            `sysRoots_floor_polyTime_false_babyBear : ¬ HashCRHardQuant (spongeFamily D)
            (IsPolyTime (spongeAnsSize D))`; likewise Metatheory/Open/BlindedSpanHiding.lean:313
            for the preimage floor), so every consumer is VACUOUS at deployed parameters.
            Membership = name ends `_from_polyTime` (the tree's naming convention for the
            instantiation) OR the statement carries both `HashCRHardQuant` and `IsPolyTime`
            (catches misnamed carriers, e.g. `oodCommitmentOpening_advantage_bound`).
            Refutations themselves (`*_false*` names) are the cure, not residuals. The fix for a
            member is the keyed-ROM re-point (`romCarrier_binds` takes NO floor hypothesis);
            deleting the `_from_polyTime` sibling without landing the re-point in the same commit
            is a REGRESSION, not a drain.

Deliberate exclusions: `example` canaries (fail_if_success teeth carry the false floor by design
and export nothing); docstrings (never part of a parsed statement).
"""
import os, re, sys

REFUTED = re.compile(r'Poseidon2SpongeCR|compressNInjective|compressInjective')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|example|structure|class)\s+'
                  r'([A-Za-z_][A-Za-z0-9_.\'!?]*)?')

# TIER-4: HashCR in hypothesis-binder position. \bHashCR\b so HashCRHardQuant / BindingHashCR
# never match; the ¬-refutations never match (no bare `ident : HashCR` shape).
HYP_HASHCR = re.compile(r'[(\[{]\s*[A-Za-z_][A-Za-z0-9_\'₀-₉ ]*\s*:\s*HashCR\b')

# TIER-5: the instantiated-at-IsPolyTime floor.
E_NAME = re.compile(r'_from_polyTime(_|$)')
E_STMT_FLOOR = re.compile(r'\bHashCRHardQuant\b')
E_STMT_EFF = re.compile(r'\bIsPolyTime\b')
ALLOW_E_NAME = re.compile(r'_false_|_false$')   # the refutations ARE the cure machinery

# --- allow-lists: the CURE MACHINERY, which must keep mentioning the refuted floors ---
ALLOW_FILES_A = ('HashFloorHonesty', 'Regrounded', 'VacuitySweepTeeth', 'HardQuantVacuity',
                 'FloorBridge', 'FloorsNonVacuous', 'CryptoFloorTeeth',
                 'Circuit/Poseidon2Binding.lean', 'Circuit/StateCommit.lean')   # definition sites
ALLOW_NAME_A = re.compile(r'_of_injective$|_of_poseidon2CR$|_refutable_|_false_|_iff_|_uninhabitable')
ALLOW_B = re.compile(r'Verify/KeystoneAudit')
ALLOW_B_NAME = re.compile(r'^canary_|^wireCommitR8_binds_or_collides$')
# _or_collides was the only spelling the old ruler saw; _or_collision/_or_collide/_or_forges are
# the same bare-disjunction class and were invisible (12 unpaired sites on 2026-07-23).
OR_SUFFIX = re.compile(r'_or_(?:collides|collision|collide|forges)(_spec)?$')


def decls(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    starts = [(i, m.group(1), m.group(2) or '<anon>')
              for i, l in enumerate(lines) for m in [DECL.match(l)] if m]
    out = []
    for k, (i, kind, name) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        body = '\n'.join(lines[i:end])
        cut = len(body)
        for pat in (r':=', r'\bby\b'):
            m = re.search(pat, body)
            if m:
                cut = min(cut, m.start())
        out.append((i + 1, kind, name, body[:cut], body))
    return out


def main(root):
    files = [os.path.join(dp, f) for dp, dn, fn in os.walk(root)
             if '.lake' not in dp.split(os.sep) for f in fn if f.endswith('.lean')]
    A, B, C, D, E = [], [], [], [], []
    for p in sorted(files):
        rel = os.path.relpath(p, root)
        try:
            ds = decls(p)
        except Exception:
            continue
        names = {n for _, _, n, _, _ in ds}
        for line, kind, name, stmt, body in ds:
            # A -- tier 1: refuted injectivity floors in the statement
            if REFUTED.search(stmt) and not any(a in rel for a in ALLOW_FILES_A) \
               and not ALLOW_NAME_A.search(name):
                A.append(f'{rel}:{line} {name}')
            # B -- tier 2: bare disjunction without an advantage-bound sibling
            m_or = OR_SUFFIX.search(name)
            if kind in ('theorem', 'lemma') and m_or \
               and not ALLOW_B.search(rel) and not ALLOW_B_NAME.search(name):
                stem = name[:m_or.start()]
                if not any(n.startswith(stem) and n.endswith('_advantage_bound') for n in names):
                    B.append(f'{rel}:{line} {name}')
            # C -- tier 3: advantage bound without a discharged-efficiency sibling
            if kind in ('theorem', 'lemma') and name.endswith('_advantage_bound'):
                stem = name[:-len('_advantage_bound')]
                sib = [b for _, _, n, _, b in ds
                       if n.startswith(stem) and n.endswith('_from_polyTime')]
                if not sib or not any('IsPolyTime' in b for b in sib):
                    C.append(f'{rel}:{line} {name}')
            # D -- tier 4: HashCR carried as a hypothesis (the fourth refuted floor)
            if HYP_HASHCR.search(stmt) and not any(a in rel for a in ALLOW_FILES_A) \
               and not ALLOW_NAME_A.search(name):
                D.append(f'{rel}:{line} {name}')
            # E -- tier 5: the refuted IsPolyTime floor, instantiated
            if kind in ('theorem', 'lemma') and not ALLOW_E_NAME.search(name):
                hit_name = bool(E_NAME.search(name))
                hit_stmt = bool(E_STMT_FLOOR.search(stmt)) and bool(E_STMT_EFF.search(stmt))
                if hit_name or hit_stmt:
                    E.append(f'{rel}:{line} {name}')
    print(f'A tier-1 refuted-floor statements   : {len(A)}')
    print(f'B tier-2 unpaired bare disjunctions : {len(B)}')
    print(f'C tier-3 undischarged efficiency    : {len(C)}')
    print(f'D tier-4 HashCR hypothesis carriers : {len(D)}')
    print(f'E tier-5 IsPolyTime floor instances : {len(E)}')
    if '-v' in sys.argv:
        for lbl, xs in (('A', A), ('B', B), ('C', C), ('D', D), ('E', E)):
            for x in xs:
                print(lbl, x)
    return 0 if not (A or B or C or D or E) else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else '.'))
