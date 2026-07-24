#!/usr/bin/env python3
"""binding_surface_complete.py — THE COMPLETION PREDICATE for the grounded-reduction sweep.

Run:  python3 scripts/binding_surface_complete.py /Users/ember/dev/breadstuffs/metatheory
Exit 0  <=>  the binding surface is FINISHED.  Prints the residual counts per tier.
`-v` lists every residual site (tier-A lines carry the floor(s) and the carrier class).

⚑ 2026-07-24 INSTRUMENT REPAIR (adversarial audit of the previous revision found it wrong in BOTH
directions — ~91 false residuals reported, 202+ real refuted-floor carriers hidden).  Changes:
  * A now knows EIGHT refuted floors, not three (each refutation read and confirmed in-tree).
  * A is a BINDER-POSITION test (the floor as a hypothesis the statement carries), not a substring
    test — conclusion-position mentions (satisfiability witnesses, ¬-refutations) are structurally
    excluded instead of name-guessed.
  * A sees `variable (h : Floor)` section binders (Lean auto-includes a variable referenced by a
    declaration, and `include h in` forces it) — carriers the literal-statement scan missed.
  * `example` canaries are excluded from A/D as the docstring always claimed.
  * comments are STRIPPED before parsing (nested `/- -/` + `--`): prose that says `theorem` or
    quotes a binder no longer creates phantom declarations in either direction.
  * C no longer demands a `_from_polyTime` sibling at a floor the tree PROVES FALSE (that rule
    re-created tier E by construction).  The honest successor convention is accepted instead.

FIVE residual classes (a declaration counted here is work REMAINING, not a bug in the ruler):

A / TIER-1  REFUTED-FLOOR CARRIERS: a non-`example` declaration whose statement BINDS a hypothesis
            whose head is one of the EIGHT in-tree-refuted floors, outside the allow-lists.
            The floors, each with its refutation theorem (all read + confirmed 2026-07-24):
              Poseidon2SpongeCR   — Circuit/HashFloorHonesty.poseidon2SpongeCR_false_babyBear
              compressNInjective  — pure injectivity, false for any compressing hash (HashFloorHonesty)
              compressInjective   — pure injectivity, false for any compressing hash (HashFloorHonesty)
              logHashInjective    — Circuit/StateCommitFloorRegrounded.logHashInjective_false_babyBear
              cellLeafInjective   — Circuit/StateCommitFloorRegrounded.cellLeafInjective_false_babyBear
              MSISHard            — Crypto/CryptoFloorTeeth.not_msisHard_of_short_ball (the Boolean
                                    ¬∃-solution floor is false whenever the short ball outnumbers the
                                    codomain — every compressing/deployed A; the honest floor is the
                                    adversary-indexed MSISHardQuant, which never matches \\bMSISHard\\b)
              CollisionResistant  — Crypto/FloorGames.collisionResistant_false_of_compressing
                                    (+ mod2Family_not_CR firing it on the tree's own compressing family)
              HashInjective       — Crypto/FactoryBindingFloorRegrounded §1b (¬ HashInjective at
                                    BLAKE3's real output width; \\b keeps logHashInjective distinct)
              Compress1CR         — Crypto/FactoryBindingFloorRegrounded §1a (compress1CR_false_babyBear;
                                    the Compress2 bundle is UNINHABITABLE at BabyBear)
              Compress8CR         — Circuit/VacuitySweepTeeth:213/:255 refute it AT THE DEPLOYED
                                    Cap8/Heap8 chipAbsorb8 instances (strongest form: not merely
                                    parametric); DeployedCapTree.badChip8_not_CR is the named tooth
            Binder position = `( h : Floor …` / `[ h : Floor …` / `{ h : Floor …` / `⦃ h : Floor …`
            in the statement, OR an in-scope `variable`-declared floor binder that the declaration
            references (or `include`s) and does not `omit` — Lean's auto-include rule, approximated.
            Reported split: per-floor counts, and a heuristic carrier class per site —
              endpoint    the floor hypothesis is APPLIED in the proof (head position, given args):
                          re-pointing it is a real re-proof
              threader    the hypothesis is only PASSED ALONG to callees: a statement rewrite
              dead-binder the hypothesis is never used by the proof: droppable, but the exported
                          statement still carries the refuted floor until it is dropped
            Known, accepted false-negatives (documented, not silent): a floor buried behind `∨` or
            `→` inside a binder (`h : X ∨ MSISHard …` — satisfiable, a weaker class of debt), and
            structure FIELDS typed at a floor (definition-site files are allow-listed anyway).

B / TIER-2  every exported bare-disjunction headline (`*_or_collides`, `*_or_collision`,
            `*_or_collide`, `*_or_forges`, optional `_spec`) has an `*_advantage_bound` sibling.
            A bare disjunction with no advantage bound is a statement that never quantifies the
            collision branch.

C / TIER-3  every `*_advantage_bound` (the conclusion-under-`Eff` shape of the HashCRHardQuant era)
            has an HONEST SUCCESSOR.  The campaign abandoned the `_from_polyTime` discharge — the
            floor it instantiated is PROVED FALSE (see tier E) — so demanding that sibling made C
            unsatisfiable-without-recreating-E.  A bound is DISCHARGED by either route:
              (i)  an in-file theorem/lemma successor on the keyed-ROM floor, named by the tree's
                   convention: `_rom` / `Rom_` / `_keyed` / `Keyed_` segment (e.g.
                   `commitReveal_binds_rom`, `stateCommitRom_binds`, `beacon_binding_rom`);
              (ii) the generic spine: the file names `RomBindingReduction`.`romCarrier_binds` as its
                   successor AND the ruler VERIFIES that theorem exists in-tree with no refuted-floor
                   binder (a pointer is only accepted with its target checked, never on prose alone).
            C reports only the genuinely-undischarged bounds, with the discharge-route split.

D / TIER-4  no declaration carries `HashCR` in HYPOTHESIS-BINDER position `(h : HashCR …)`.
            `HashCR` (Dregg2/Crypto/HermineHintMLWE.lean:354) is pure injectivity — a refuted floor:
            Dregg2/Circuit/HashFloorHonesty.lean ("TOOTH 3") proves `¬ HashCR cr` for any
            compressing commit-reveal.  Kept a SEPARATE tier (its historical drain to 0 is the
            baseline the campaign measures against).  `\\bHashCR\\b` never matches `HashCRHardQuant`
            or `BindingHashCR`.

E / TIER-5  no theorem/lemma instantiates a collision floor at `Eff := IsPolyTime`. That floor is
            proved FALSE at deployed parameters (Dregg2/Exec/SystemRootsBindingReduction.lean:516
            `sysRoots_floor_polyTime_false_babyBear : ¬ HashCRHardQuant (spongeFamily D)
            (IsPolyTime (spongeAnsSize D))`; likewise Metatheory/Open/BlindedSpanHiding.lean:313
            for the preimage floor), so every consumer is VACUOUS at deployed parameters.
            Membership = name ends `_from_polyTime` OR the statement carries both `HashCRHardQuant`
            and `IsPolyTime`.  Refutations themselves (`*_false*` names) are the cure, not residuals.

⚑ FINISHED DOES NOT MEAN C→0 BY DELETION: deleting an `_advantage_bound` without landing its
keyed-ROM successor in the same commit is a REGRESSION, not a drain.  And a ruler change may only
make the measurement MORE TRUE — for every count that drops, the reason must be a demonstrated
false positive, never a hidden site.

Deliberate exclusions: `example` canaries (fail_if_success teeth carry the false floor by design
and export nothing); comments/docstrings (stripped before parsing).
"""
import os, re, sys
from collections import Counter

# --- the refuted floors (tier A). Alternation, longest-prefix first where prefixes overlap.
FLOORS_A = ('Poseidon2SpongeCR', 'compressNInjective', 'compressInjective',
            'logHashInjective', 'cellLeafInjective', 'MSISHard', 'CollisionResistant',
            'HashInjective', 'Compress1CR', 'Compress8CR')
FLOOR_ALT = '|'.join(FLOORS_A)

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|example|structure|class)\s+'
                  r'([A-Za-z_][A-Za-z0-9_.\'!?]*)?')

# TIER-A binder-position: `( h : Floor` / `[ h : Floor` / `{ h : Floor` / `⦃ h : Floor` — possibly
# several space-separated binder names before the colon. Immediate head position after the colon is
# the strict, interpretable test (a `¬ Floor` or `X ∨ Floor` hypothesis never matches: assuming the
# refutation, or a satisfiable disjunction, is not carrying the floor).
# A dotted qualifier prefix is part of the same floor (`StateCommit.compressNInjective`,
# `Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR` — real carrier spellings in-tree).
QUAL = r'(?:[A-Za-z_][A-Za-z0-9_\'!?]*\.)*'
HYP_FLOOR = re.compile(r'[(\[{⦃]\s*([A-Za-z_][A-Za-z0-9_\'₀-₉ ]*?)\s*:\s*' + QUAL
                       + r'(' + FLOOR_ALT + r')\b')

# structure/class FIELDS typed at a floor (`leafInj : cellLeafInjective CH` in a `where` block):
# the LeafRealization/CommitSurface shape — a bundle no deployed hash can inhabit
# (StateCommitFloorRegrounded proves the realization bundles uninhabitable at BabyBear).
FIELD_FLOOR = re.compile(r'^\s*([A-Za-z_][A-Za-z0-9_\'₀-₉]*)\s*:\s*' + QUAL
                         + r'(' + FLOOR_ALT + r')\b', re.MULTILINE)

# `variable (h : Floor …)` / `variable {h : Floor …}` section binders; `include h in` / `omit h in`;
# `local notation "X" => … h …` aliases that smuggle floor binders into statements (the Closure
# files' `Slive`).
VARIABLE_LINE = re.compile(r'^\s*variable\b')
INCLUDE_LINE = re.compile(r'^\s*include\s+([A-Za-z0-9_\'₀-₉ ]+?)\s+in\b')
OMIT_LINE = re.compile(r'^\s*omit\s+([A-Za-z0-9_\'₀-₉ ]+?)\s+in\b')
NOTATION_LINE = re.compile(r'^\s*(?:local\s+)?notation\s+"([^"]+)"\s*=>\s*(.*)$')
SCOPE_OPEN = re.compile(r'^\s*(section\b|namespace\s)')
SCOPE_CLOSE = re.compile(r'^\s*end\b')

# TIER-4: HashCR in hypothesis-binder position. \bHashCR\b so HashCRHardQuant / BindingHashCR
# never match; the ¬-refutations never match (no bare `ident : HashCR` shape).
HYP_HASHCR = re.compile(r'[(\[{⦃]\s*[A-Za-z_][A-Za-z0-9_\'₀-₉ ]*\s*:\s*' + QUAL + r'HashCR\b')

# TIER-5: the instantiated-at-IsPolyTime floor.
E_NAME = re.compile(r'_from_polyTime(_|$)')
E_STMT_FLOOR = re.compile(r'\bHashCRHardQuant\b')
E_STMT_EFF = re.compile(r'\bIsPolyTime\b')
ALLOW_E_NAME = re.compile(r'_false_|_false$')   # the refutations ARE the cure machinery

# --- allow-lists: the CURE MACHINERY, which must keep mentioning the refuted floors ---
ALLOW_FILES_A = ('HashFloorHonesty', 'Regrounded', 'VacuitySweepTeeth', 'HardQuantVacuity',
                 'FloorBridge', 'FloorsNonVacuous', 'CryptoFloorTeeth',
                 'Circuit/Poseidon2Binding.lean', 'Circuit/StateCommit.lean')
# Every entry names a CLASS of cure machinery, justified:
#   _of_injective$ / _of_poseidon2CR$ / _of_poseidon2SpongeCR$ — honest-named conditionals and the
#       OLD⟹NEW strength bridges (`domainSeparatedCR_of_poseidon2SpongeCR`): the suffix IS the label
#       "this stands on the refuted floor" — the seam is declared in the name, kept for the bridge's
#       sake (deleting a bridge deletes the documented relative-strength fact).
#   _refutable_ / _false_ / _false$ / _uninhabitable — refutation/refutability teeth.
#   _iff_ — floor-equivalence bridges (definitional restatements, not new carriers).
#   _not_CR$ — ¬CollisionResistant refutation naming (mod2Family_not_CR shape).
#   _bites$ / _fires$ — falsifiability teeth: the floor MUST appear as a hypothesis so the tooth can
#       show it has force on concrete data (Adversary/Instances *_bites, honest_companion_fires, …).
#       A `_vN` revision suffix keeps the class (grounded_capstone_engine_fires_v2).
#   _breaks_ — reduction teeth exhibiting the break (deployed_fooling_breaks_floor shape).
ALLOW_NAME_A = re.compile(r'_of_injective$|_of_poseidon2CR$|_of_poseidon2SpongeCR$|_refutable_'
                          r'|_false_|_false$|_iff_|_uninhabitable'
                          r'|(_not_CR|_bites|_fires)(_v\d+)?$|_breaks_')
ALLOW_B = re.compile(r'Verify/KeystoneAudit')
ALLOW_B_NAME = re.compile(r'^canary_|^wireCommitR8_binds_or_collides$')
# _or_collides was the only spelling the old ruler saw; _or_collision/_or_collide/_or_forges are
# the same bare-disjunction class and were invisible (12 unpaired sites on 2026-07-23).
OR_SUFFIX = re.compile(r'_or_(?:collides|collision|collide|forges)(_spec)?$')

# TIER-3 successor convention (see header). The name segment, not a bare substring: `Rom`/`Keyed`
# must be a full CamelCase or snake segment so `RomCarrier`-lemma names (`…RomCarrier_len_eq…`)
# never count as the binding successor.
C_SUCCESSOR = re.compile(r'(_rom|Rom)(_|$)|(_keyed|Keyed)(_|$)')
C_GENERIC_PTR = ('RomBindingReduction', 'romCarrier_binds')
C_GENERIC_TARGET = ('Crypto/RomBindingReduction.lean', 'romCarrier_binds')


def strip_comments(text):
    """Blank out nested `/- -/` blocks and `--` line comments, preserving line structure."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
            continue
        if text.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
            continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1
            out.append('  ')
            i += 2
            continue
        c = text[i]
        out.append(c if (depth == 0 or c == '\n') else ' ')
        i += 1
    return ''.join(out)


def parse(path):
    """-> (decls, lines). decls = (line1, kind, name, stmt, proof, include_names, omit_names)."""
    lines = strip_comments(open(path, encoding='utf-8').read()).split('\n')
    starts = [(i, m.group(1), m.group(2) or '<anon>')
              for i, l in enumerate(lines) for m in [DECL.match(l)] if m]
    # include/omit prefixes: attach each `include … in` / `omit … in` line to the next declaration.
    inc, om = {}, {}
    pend_inc, pend_om = [], []
    starts_set = {i for i, _, _ in starts}
    for i, l in enumerate(lines):
        m = INCLUDE_LINE.match(l)
        if m:
            pend_inc += m.group(1).split()
            continue
        m = OMIT_LINE.match(l)
        if m:
            pend_om += m.group(1).split()
            continue
        if i in starts_set:
            if pend_inc:
                inc[i] = pend_inc
                pend_inc = []
            if pend_om:
                om[i] = pend_om
                pend_om = []
    out = []
    for k, (i, kind, name) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        body = '\n'.join(lines[i:end])
        cut = len(body)
        for pat in (r':=', r'\bby\b'):
            m = re.search(pat, body)
            if m:
                cut = min(cut, m.start())
        out.append((i + 1, kind, name, body[:cut], body[cut:],
                    inc.get(i, []), om.get(i, [])))
    return out, lines


def floor_vars(lines):
    """Scope-tracked `variable` floor binders and floor-smuggling notation aliases.
    -> (line1 -> [(binder, floor)], line1 -> [(alias, floor)])."""
    active, aliases, per_line, per_line_al, depth = [], [], {}, {}, 0
    for i, l in enumerate(lines):
        if SCOPE_OPEN.match(l):
            depth += 1
        elif SCOPE_CLOSE.match(l):
            depth = max(0, depth - 1)
            active = [v for v in active if v[0] <= depth]
            aliases = [a for a in aliases if a[0] <= depth]
        elif VARIABLE_LINE.match(l):
            for names, fl in HYP_FLOOR.findall(l):
                for b in names.split():
                    active.append((depth, b, fl))
        else:
            m = NOTATION_LINE.match(l)
            if m:
                nm, body = m.group(1), m.group(2)
                fls = {fl for _, b, fl in active
                       if re.search(r'(?<![A-Za-z0-9_\'])' + re.escape(b)
                                    + r'(?![A-Za-z0-9_\'₀-₉])', body)}
                for fl in fls:
                    aliases.append((depth, nm, fl))
        per_line[i + 1] = [(b, fl) for _, b, fl in active]
        per_line_al[i + 1] = [(nm, fl) for _, nm, fl in aliases]
    return per_line, per_line_al


TOKEN_HEAD = re.compile(r'(?:^|[(\[⟨;,]|:=|\bexact\b|\bapply\b|\brefine\b|·)\s*$')
TOKEN = r'(?<![A-Za-z0-9_\'])%s(?![A-Za-z0-9_\'₀-₉])'


def classify(lit_binders, var_binders, aliases, stmt, proof):
    """Heuristic carrier class.
    endpoint: a floor-hypothesis binder is APPLIED in the proof (head position, given arguments).
    threader: the binder (or a floor-smuggling alias) is only mentioned — in the proof (passed to a
              callee) or in the statement past its binding site (statement-load-bearing).
    dead-binder: never referenced — the hypothesis is droppable as stated."""
    used = False
    for b in lit_binders + var_binders:
        for m in re.finditer(TOKEN % re.escape(b), proof):
            used = True
            pre = proof[max(0, m.start() - 12):m.start()]
            post = proof[m.end():m.end() + 3]
            if re.match(r'\s+[A-Za-z_(⟨.]|\s+_', post) and TOKEN_HEAD.search(pre):
                return 'endpoint'
    if not used:
        # statement-load-bearing: a literal binder re-occurs in the statement past its binding
        # occurrence; a section-variable binder's binding site is elsewhere, so ONE hit counts.
        used = any(len(re.findall(TOKEN % re.escape(b), stmt)) > 1 for b in lit_binders) \
            or any(re.search(TOKEN % re.escape(b), stmt) for b in var_binders) \
            or any(re.search(TOKEN % re.escape(a), stmt + proof) for a in aliases)
    return 'threader' if used else 'dead-binder'


def generic_successor_ok(root):
    """Verify the generic keyed-ROM successor actually exists and carries no refuted floor."""
    path = os.path.join(root, 'Dregg2', 'Crypto', 'RomBindingReduction.lean')
    if not os.path.exists(path):
        return False
    try:
        ds, _ = parse(path)
    except Exception:
        return False
    for _, kind, name, stmt, _, _, _ in ds:
        if kind in ('theorem', 'lemma') and name == C_GENERIC_TARGET[1]:
            return not HYP_FLOOR.search(stmt)
    return False


def main(root):
    files = [os.path.join(dp, f) for dp, dn, fn in os.walk(root)
             if '.lake' not in dp.split(os.sep) for f in fn if f.endswith('.lean')]
    A, B, C, D, E = [], [], [], [], []
    a_floor, a_class = Counter(), Counter()
    a_via_var = 0
    c_infile = c_generic = 0
    gen_ok = generic_successor_ok(root)
    for p in sorted(files):
        rel = os.path.relpath(p, root)
        try:
            ds, lines = parse(p)
        except Exception:
            continue
        raw = None
        vmap, amap = floor_vars(lines)
        names = {n for _, _, n, _, _, _, _ in ds}
        succ_names = [n for _, k, n, _, _, _, _ in ds
                      if k in ('theorem', 'lemma') and C_SUCCESSOR.search(n)]
        for line, kind, name, stmt, proof, inc_names, omit_names in ds:
            # A -- tier 1: refuted floors carried in hypothesis-binder position
            if kind != 'example' and not any(a in rel for a in ALLOW_FILES_A) \
               and not ALLOW_NAME_A.search(name):
                lit_binders, var_binders, aliases, floors = [], [], [], set()
                field_bundle = False
                for bn, fl in HYP_FLOOR.findall(stmt):
                    lit_binders += [b for b in bn.split() if b]
                    floors.add(fl)
                if kind in ('structure', 'class'):
                    for _, fl in FIELD_FLOOR.findall(stmt + proof):
                        floors.add(fl)
                        field_bundle = True
                body = stmt + proof
                for vb, vfl in vmap.get(line, []):
                    if vb in omit_names:
                        continue
                    if vb in inc_names or re.search(TOKEN % re.escape(vb), body):
                        var_binders.append(vb)
                        floors.add(vfl)
                for al, afl in amap.get(line, []):
                    if re.search(TOKEN % re.escape(al), body):
                        aliases.append(al)
                        floors.add(afl)
                if floors:
                    via_var = bool(var_binders or aliases)
                    cls = 'field-bundle' if field_bundle and not (lit_binders or var_binders) \
                        else classify(lit_binders, var_binders, set(aliases), stmt, proof)
                    a_class[cls] += 1
                    a_via_var += via_var
                    for fl in floors:
                        a_floor[fl] += 1
                    A.append(f'{rel}:{line} {name} [{"+".join(sorted(floors))}] {cls}'
                             + (' (via variable)' if via_var else ''))
            # B -- tier 2: bare disjunction without an advantage-bound sibling
            m_or = OR_SUFFIX.search(name)
            if kind in ('theorem', 'lemma') and m_or \
               and not ALLOW_B.search(rel) and not ALLOW_B_NAME.search(name):
                stem = name[:m_or.start()]
                if not any(n.startswith(stem) and n.endswith('_advantage_bound') for n in names):
                    B.append(f'{rel}:{line} {name}')
            # C -- tier 3: advantage bound without an honest keyed-ROM successor
            if kind in ('theorem', 'lemma') and name.endswith('_advantage_bound'):
                if succ_names:
                    c_infile += 1
                else:
                    if raw is None:
                        raw = open(p, encoding='utf-8').read()
                    if gen_ok and all(t in raw for t in C_GENERIC_PTR):
                        c_generic += 1
                    else:
                        C.append(f'{rel}:{line} {name}')
            # D -- tier 4: HashCR carried as a hypothesis (a refuted floor, historical baseline)
            if kind != 'example' and HYP_HASHCR.search(stmt) \
               and not any(a in rel for a in ALLOW_FILES_A) and not ALLOW_NAME_A.search(name):
                D.append(f'{rel}:{line} {name}')
            # E -- tier 5: the refuted IsPolyTime floor, instantiated
            if kind in ('theorem', 'lemma') and not ALLOW_E_NAME.search(name):
                hit_name = bool(E_NAME.search(name))
                hit_stmt = bool(E_STMT_FLOOR.search(stmt)) and bool(E_STMT_EFF.search(stmt))
                if hit_name or hit_stmt:
                    E.append(f'{rel}:{line} {name}')
    print(f'A tier-1 refuted-floor carriers     : {len(A)}')
    print(f'    per floor : '
          + '  '.join(f'{f}={a_floor[f]}' for f in FLOORS_A if a_floor[f]))
    print(f'    per class : endpoint={a_class["endpoint"]} (real re-proofs)  '
          f'threader={a_class["threader"]} (statement rewrites)  '
          f'dead-binder={a_class["dead-binder"]} (droppable hypotheses)  '
          f'field-bundle={a_class["field-bundle"]} (uninhabitable-at-deployment structures)  '
          f'[heuristic; via-section-variable={a_via_var}]')
    print(f'B tier-2 unpaired bare disjunctions : {len(B)}')
    print(f'C tier-3 undischarged advtg bounds  : {len(C)}')
    print(f'    discharged : in-file _rom/_keyed successor={c_infile}  '
          f'generic romCarrier_binds={c_generic} (target verified={gen_ok})')
    print(f'D tier-4 HashCR hypothesis carriers : {len(D)}')
    print(f'E tier-5 IsPolyTime floor instances : {len(E)}')
    if '-v' in sys.argv:
        for lbl, xs in (('A', A), ('B', B), ('C', C), ('D', D), ('E', E)):
            for x in xs:
                print(lbl, x)
    return 0 if not (A or B or C or D or E) else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else '.'))
