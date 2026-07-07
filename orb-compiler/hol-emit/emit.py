#!/usr/bin/env python3
"""emit.py — the HOL4 refinement-script GENERATOR for the compiler lane.

Generalizes the hand-written C1 `boundScanLinkAScript.sml` to a template +
per-primitive fill-ins. Given a primitive DESCRIPTOR (JSON) naming a FAMILY and
its shape, it substitutes into that family's template and writes a HOL4 theory
`<theory>Script.sml` that the HOL4 kernel then rebuilds.

The kernel is the correctness check, exactly as the Lean kernel is for the
front-end DSL: a bad fill-in fails to typecheck / fails to prove; it can never
`cheat`. This is the HOL4-emission analogue of "a bad generation must FAIL to
typecheck, never sorry".

Families:
  region  — real: emits the full four-theorem Link A proof; rebuilds green.
  machine — scaffold: emits SPEC + dispatch AST + relation (all typecheck) and
            states the transition-refinement obligation as a comment.

Usage:
  emit.py <descriptor.json> [<descriptor.json> ...] --out <dir>
  emit.py --all --out <dir>          # every descriptor in descriptors/
"""

import argparse, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_DIR = os.path.join(HERE, "template")
DESC_DIR = os.path.join(HERE, "descriptors")

# ---- the placeholder fill-ins each family's template consumes ---------------

def region_fills(d):
    """Region family: one size local, two offset locals, a signed bounds If."""
    return {
        "DESC_NAME":     d["desc_name"],
        "THEORY":        d["theory"],
        "IMPL_NAME":     d["impl_name"],
        "REL_NAME":      d["rel_name"],
        "DECIDE_NAME":   d["decide_name"],
        "ENCODE_NAME":   d["encode_name"],
        "ARR":           d["arr"],
        "ARR_DECL":      "(%s:num list)" % d["arr"],   # derived
        "OFF":           d["off"],
        "LEN":           d["len"],
        "SIZE_TERM":     d["size_term"],
        "SIZE_VAR":      d["size_var"],
        "OFF_VAR":       d["off_var"],
        "LEN_VAR":       d["len_var"],
        "RESULT_VAR":    d["result_var"],
        "SENTINEL_NUM":  str(d["sentinel_num"]),
        "SENTINEL_WORD": "%dw" % d["sentinel_num"],    # derived
        "DECIDE_SOME":   d["decide_some"],
        "SPEC_AUX":      d.get("spec_aux", ""),
    }

def machine_fills(d):
    """Machine family: a finite-state transition + dispatch AST (scaffold)."""
    return {
        "DESC_NAME":  d["desc_name"],
        "THEORY":     d["theory"],
        "IMPL_NAME":  d["impl_name"],
        "REL_NAME":   d["rel_name"],
        "STEP_NAME":  d["step_name"],
        "ENC_NAME":   d["enc_name"],
        "STATE_VAR":  d["state_var"],
        "OUT_VAR":    d["out_var"],
    }

FAMILIES = {
    "region":  ("region.sml.tmpl",  region_fills),
    "machine": ("machine.sml.tmpl", machine_fills),
}

# ---- the substitution engine (family-agnostic) ------------------------------

def substitute(template, fills):
    out = template
    for k, v in fills.items():
        out = out.replace("{{%s}}" % k, v)
    # any surviving {{...}} is an unfilled hole => a generator bug, fail loud.
    if "{{" in out:
        start = out.index("{{")
        raise SystemExit("emit.py: unfilled placeholder near: %r"
                         % out[start:start + 40])
    return out

def emit(desc_path, out_dir):
    with open(desc_path) as f:
        d = json.load(f)
    fam = d["family"]
    if fam not in FAMILIES:
        raise SystemExit("emit.py: unknown family %r in %s" % (fam, desc_path))
    tmpl_name, fills_fn = FAMILIES[fam]
    with open(os.path.join(TEMPLATE_DIR, tmpl_name)) as f:
        template = f.read()
    text = substitute(template, fills_fn(d))
    out_path = os.path.join(out_dir, d["theory"] + "Script.sml")
    with open(out_path, "w") as f:
        f.write(text)
    print("emit: %-18s [%-7s] -> %s" % (d["desc_name"], fam,
                                        os.path.basename(out_path)))
    return out_path

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("descriptors", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--out", default=os.path.join(HERE, "build"))
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    descs = args.descriptors
    if args.all:
        descs = [os.path.join(DESC_DIR, fn)
                 for fn in sorted(os.listdir(DESC_DIR)) if fn.endswith(".json")]
    if not descs:
        ap.error("give descriptor paths or --all")
    for dp in descs:
        emit(dp, args.out)

if __name__ == "__main__":
    main()
