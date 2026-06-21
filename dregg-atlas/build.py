"""THE DREGG ATLAS site-builder — ingest the crawl data + screenshots +
explainers and emit a self-contained, offline interactive site under site/.

The site is BOTH:
  * a single interactive SPA (index.html + app.js + vendored cytoscape.js) — the
    game tree and the ocap web as live, zoomable graphs with detail panels; and
  * a cross-linked static reference (pages/) — a page per cell, surface, effect,
    and the protocol, browsable without JS.

Run after crawl.py (and shoot.py for screenshots). Regenerable end-to-end:
  python3 crawl.py && python3 shoot.py && python3 build.py
"""
import json
import os
import shutil
import html

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(ROOT, "data")
SITE = os.path.join(ROOT, "site")
SHOTS = os.path.join(ROOT, "screenshots")
EXPL = os.path.join(ROOT, "explainers")
PAGES = os.path.join(SITE, "pages")


def load(name, default):
    p = os.path.join(DATA, name)
    if os.path.exists(p):
        return json.load(open(p))
    return default


def load_explainers():
    out = {}
    if os.path.isdir(EXPL):
        for f in os.listdir(EXPL):
            if f.endswith(".md"):
                out[f[:-3]] = open(os.path.join(EXPL, f)).read()
    return out


def md_to_html(text):
    """A tiny, dependency-free markdown subset (headings, code, lists, bold,
    inline code, paragraphs) — enough for the explainers."""
    lines = text.split("\n")
    out, in_list, in_code = [], False, False
    for ln in lines:
        if ln.strip().startswith("```"):
            if in_code:
                out.append("</code></pre>"); in_code = False
            else:
                out.append("<pre><code>"); in_code = True
            continue
        if in_code:
            out.append(html.escape(ln)); continue
        if ln.startswith("### "):
            out.append(f"<h4>{inline(ln[4:])}</h4>"); continue
        if ln.startswith("## "):
            out.append(f"<h3>{inline(ln[3:])}</h3>"); continue
        if ln.startswith("# "):
            out.append(f"<h2>{inline(ln[2:])}</h2>"); continue
        if ln.strip().startswith("- "):
            if not in_list:
                out.append("<ul>"); in_list = True
            out.append(f"<li>{inline(ln.strip()[2:])}</li>"); continue
        if in_list:
            out.append("</ul>"); in_list = False
        if ln.strip():
            out.append(f"<p>{inline(ln)}</p>")
    if in_list:
        out.append("</ul>")
    if in_code:
        out.append("</code></pre>")
    return "\n".join(out)


def inline(s):
    s = html.escape(s)
    import re
    s = re.sub(r"`([^`]+)`", r"<code>\1</code>", s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    return s


# ---------------------------------------------------------------------------
# assemble the data the SPA reads (inlined so it opens via file://)
# ---------------------------------------------------------------------------

def build_data_js():
    data = {
        "gametree": load("gametree.json", {"meta": {}, "nodes": [], "edges": []}),
        "cells": load("cells.json", {"cells": [], "ocap": {"nodes": [], "edges": []}}),
        "protocol": load("protocol.json", {}),
        "surfaces": load("surfaces.json", []),
        "anomalies": load("anomalies.json", []),
        "explainers": load_explainers(),
    }
    with open(os.path.join(SITE, "data.js"), "w") as f:
        f.write("window.ATLAS = " + json.dumps(data) + ";\n")
    return data


# ---------------------------------------------------------------------------
# static reference pages (browsable without JS, cross-linked to the SPA)
# ---------------------------------------------------------------------------

PAGE_TMPL = """<!doctype html><html><head><meta charset=utf-8>
<title>{title} · dregg atlas</title><link rel=stylesheet href="../atlas.css"></head>
<body class=page><nav class=crumb><a href="../index.html">← atlas</a> / {crumb}</nav>
<main class=doc>{body}</main></body></html>"""


def field_value_html(v):
    t = v.get("t")
    if t == "balance":
        return f'<span class=bal>{v["v"]}</span>'
    if t in ("id", "hash"):
        return f'<span class=id title="{v["v"]}">{v["short"]}</span>'
    if t == "cap-edge":
        return f'→ <span class=id title="{v["target"]}">{v["short"]}</span> slot {v["slot"]}'
    if t == "slot":
        return f'[{v["index"]}] {html.escape(v["hex"])}'
    return html.escape(str(v.get("v", "")))


def face_html(face):
    b = face["body"]
    shape = b["shape"]
    out = [f'<div class=face><h4>{html.escape(face["kind"])} · {html.escape(face["label"])}</h4>']
    if shape == "fields":
        out.append("<table>")
        for fld in b["fields"]["fields"]:
            out.append(f'<tr><td class=k>{html.escape(fld["key"])}</td><td>{field_value_html(fld["value"])}</td></tr>')
        out.append("</table>")
    elif shape == "graph":
        out.append("<table>")
        for e in b.get("edges", []):
            out.append(f'<tr><td class=id>{e["from"]}</td><td>→ <span class=id>{e["to"]}</span> slot {e["slot"]} · {html.escape(e["rights"])}</td></tr>')
        if not b.get("edges"):
            out.append("<tr><td class=muted>(no capability edges)</td></tr>")
        out.append("</table>")
    elif shape == "prose":
        out.append(f'<div class=prose>{html.escape(b["text"])}</div>')
    elif shape == "timeline":
        out.append("<table>")
        for e in b.get("events", []):
            out.append(f'<tr><td class=k>@{e["at"]}</td><td>{html.escape(e["label"])}</td></tr>')
        out.append("</table>")
    else:
        out.append(f'<div class=prose>{html.escape(json.dumps(b, indent=1))}</div>')
    out.append("</div>")
    return "\n".join(out)


def build_cell_pages(data):
    os.makedirs(os.path.join(PAGES, "cells"), exist_ok=True)
    for c in data["cells"].get("cells", []):
        body = [f'<h2>Cell <span class=id>{c["short"]}</span></h2>',
                f'<p class=muted>{c["id"]}</p>',
                f'<p>Halo: {" · ".join(c["halo"])}</p>',
                "<h3>Affordances — messages it understands</h3><table>"]
        for a in c["affordances"]:
            badge = '<span class=ok>● may send</span>' if a["authorized"] else '<span class=no>○ refused</span>'
            body.append(f'<tr><td class=k>{html.escape(a["name"])}</td><td>{html.escape(a["effect"])} <span class=muted>({html.escape(a["required"])})</span></td><td>{badge}</td></tr>')
        body.append("</table><h3>Presentation faces</h3>")
        for face in c["faces"]:
            body.append(face_html(face))
        page = PAGE_TMPL.format(title=f"Cell {c['short']}", crumb=f"cells / {c['short']}",
                                body="\n".join(body))
        open(os.path.join(PAGES, "cells", c["short"].replace("…", "_") + ".html"), "w").write(page)


def build_protocol_page(data):
    p = data["protocol"]
    lat = p.get("auth_required_lattice", {})
    body = ["<h2>Protocol reference</h2>",
            "<h3>The AuthRequired lattice</h3>",
            f'<p class=mono>{html.escape(lat.get("order",""))}</p>',
            f'<p>Tiers: {" · ".join(html.escape(t) for t in lat.get("tiers", []))}</p>',
            f'<p class=muted>{html.escape(lat.get("note",""))}</p>',
            "<h3>The eight verbs</h3><ul>"]
    for v in p.get("the_eight_verbs", []):
        body.append(f"<li>{html.escape(v)}</li>")
    body.append("</ul><h3>Effects seen live</h3><ul>")
    for e in p.get("effects_seen", []):
        body.append(f"<li><code>{html.escape(e)}</code></li>")
    body.append("</ul><h3>Refusal taxonomy</h3><ul>")
    for k, v in p.get("refusal_taxonomy", {}).items():
        body.append(f"<li><strong>{html.escape(k)}</strong>: {html.escape(v)}</li>")
    body.append("</ul>")
    open(os.path.join(PAGES, "protocol.html"), "w").write(
        PAGE_TMPL.format(title="Protocol", crumb="protocol", body="\n".join(body)))


def main():
    os.makedirs(SITE, exist_ok=True)
    os.makedirs(PAGES, exist_ok=True)
    # copy screenshots in
    dst = os.path.join(SITE, "screenshots")
    if os.path.isdir(SHOTS):
        shutil.rmtree(dst, ignore_errors=True)
        shutil.copytree(SHOTS, dst)
    data = build_data_js()
    build_cell_pages(data)
    build_protocol_page(data)
    # the SPA shell + app + css are written by separate template files that
    # this script copies verbatim (kept as real files for easy editing).
    for fn in ("index.html", "app.js", "atlas.css"):
        src = os.path.join(ROOT, "tmpl", fn)
        if os.path.exists(src):
            shutil.copy(src, os.path.join(SITE, fn))
    gt = data["gametree"]["meta"]
    print(f"atlas built → {SITE}/index.html")
    print(f"  game tree: {gt.get('node_count','?')} states / {gt.get('edge_count','?')} transitions")
    print(f"  cells: {len(data['cells'].get('cells', []))} · surfaces: {len(data['surfaces'])} · anomalies: {len(data['anomalies'])}")


if __name__ == "__main__":
    main()
