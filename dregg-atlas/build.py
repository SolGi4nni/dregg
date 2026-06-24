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
UIEXPLORE = os.path.join(ROOT, "ui-explore")


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


def parse_sections(md_text):
    """Split a `## slug` markdown doc into {slug: section_markdown}."""
    sections, cur, buf = {}, None, []
    for ln in md_text.split("\n"):
        if ln.startswith("## "):
            if cur is not None:
                sections[cur] = "\n".join(buf).strip()
            cur = ln[3:].strip()
            buf = []
        else:
            buf.append(ln)
    if cur is not None:
        sections[cur] = "\n".join(buf).strip()
    return sections


def all_sections():
    """Every explainer section across all files, flattened by slug."""
    merged = {}
    for name, text in load_explainers().items():
        if name == "about":
            continue
        for slug, body in parse_sections(text).items():
            merged[slug] = body
    return merged


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
# the COMPONENTS pillar — a census of the vendored gpui-component widget set
# the cockpit is built from. The site-experience lane bakes a fallback so the
# pillar is never empty; the generator lane may replace it with a live, usage-
# cross-linked data/components.json (same shape).
# ---------------------------------------------------------------------------

# group · glyph · one-line role for each gpui-component widget the cockpit can
# render. Groups order the gallery; glyphs are the swatch.
_COMPONENT_CATALOG = {
    "input":         ("input", "⌶", "Rich text field with selection, history and validation — the cockpit's editors, terminals and command bars."),
    "button":        ("input", "▣", "Pressable action with variants (primary/ghost/danger) and sizes."),
    "checkbox":      ("input", "☑", "Boolean toggle."),
    "radio":         ("input", "◉", "Single-choice within a group."),
    "switch":        ("input", "⏻", "On/off toggle."),
    "slider":        ("input", "─", "Continuous value along a track."),
    "select":        ("input", "▼", "Single-select dropdown."),
    "combobox":      ("input", "⌕", "Type-to-filter select."),
    "color_picker":  ("input", "◢", "Pick a colour."),
    "rating":        ("input", "★", "Star rating input."),
    "stepper":       ("input", "±", "Increment/decrement a number."),
    "form":          ("input", "▤", "Grouped fields with labels and validation."),
    "table":         ("data", "▦", "Virtualised columnar grid — the ledger, cell lists, lanes."),
    "tree":          ("data", "⌥", "Collapsible hierarchy — the ocap web, file trees, the inspector."),
    "list":          ("data", "≣", "Virtualised vertical list."),
    "searchable_list": ("data", "⌕", "List with an inline filter."),
    "virtual_list":  ("data", "≣", "Windowed list for very large collections."),
    "description_list": ("data", "≔", "Key/value pairs — the raw-fields face."),
    "chart":         ("data", "▟", "Plotted series — proofs, perf, balances over time."),
    "plot":          ("data", "⋰", "Low-level plotting primitives."),
    "pagination":    ("data", "⋯", "Page through a long collection."),
    "tab":           ("layout", "▭", "Tabbed surface switcher — the cockpit's top nav."),
    "dock":          ("layout", "◳", "Dockable, splittable panes — the editor+terminal cockpit layout."),
    "resizable":     ("layout", "↔", "Drag-to-resize split panes."),
    "sidebar":       ("layout", "▏", "Collapsible side navigation."),
    "scroll":        ("layout", "↕", "Scroll container with custom bars."),
    "accordion":     ("layout", "⋁", "Stacked expandable sections."),
    "collapsible":   ("layout", "⌄", "A single expand/collapse region."),
    "group_box":     ("layout", "▢", "Titled bordered grouping."),
    "separator":     ("layout", "│", "A divider rule."),
    "title_bar":     ("layout", "▔", "Window title bar with controls."),
    "status_bar":    ("layout", "▁", "Bottom status strip."),
    "window_border": ("layout", "▢", "Decorated window frame."),
    "dialog":        ("overlay", "▢", "Modal dialog."),
    "sheet":         ("overlay", "▤", "Slide-in panel."),
    "popover":       ("overlay", "◰", "Anchored floating panel."),
    "hover_card":    ("overlay", "◰", "Rich tooltip on hover."),
    "tooltip":       ("overlay", "▮", "Hint on hover."),
    "menu":          ("overlay", "≡", "Context / dropdown menu."),
    "native_menu":   ("overlay", "≡", "OS-native menu bar."),
    "notification":  ("overlay", "✦", "Transient toast."),
    "alert":         ("overlay", "▲", "Inline status banner."),
    "modal":         ("overlay", "▢", "Blocking overlay."),
    "avatar":        ("display", "◍", "Identity glyph / image."),
    "badge":         ("display", "●", "Count or status pip."),
    "tag":           ("display", "⬭", "Labelled chip."),
    "label":         ("display", "ᴬ", "Static text label."),
    "link":          ("display", "↗", "Hyperlink."),
    "kbd":           ("display", "⌨", "Keyboard-key glyph."),
    "icon":          ("display", "✲", "Vector icon."),
    "progress":      ("display", "▰", "Determinate/indeterminate progress."),
    "spinner":       ("display", "◌", "Busy indicator."),
    "skeleton":      ("display", "▢", "Loading placeholder."),
    "breadcrumb":    ("display", "›", "Path navigation trail."),
    "time":          ("display", "◷", "Time / duration display + picker."),
    "clipboard":     ("display", "⎘", "Copy-to-clipboard affordance."),
    "inspector":     ("dev", "⌗", "The moldable inspector surface."),
    "setting":       ("dev", "⚙", "Settings rows."),
}

# which surfaces render which components — seeded from the cockpit's actual use
# (a surface→widget map). Generous, code-grounded approximations; the generator
# lane can supersede with exact reads.
_SURFACE_COMPONENTS = {
    "home": ["title_bar", "tab", "label", "badge", "icon"],
    "inspector": ["inspector", "tree", "description_list", "tab", "scroll"],
    "inspect-act": ["inspector", "button", "input", "description_list"],
    "graph": ["scroll", "tooltip", "badge"],
    "web-of-cells": ["tree", "tooltip", "badge", "scroll"],
    "objects": ["table", "list", "tag", "scroll"],
    "proofs": ["chart", "table", "badge", "progress"],
    "debugger": ["table", "tree", "button", "tab", "input"],
    "replay": ["slider", "button", "table", "progress"],
    "workspace": ["dock", "resizable", "tab", "sidebar"],
    "wonder": ["icon", "label", "hover_card", "badge"],
    "lanes": ["table", "list", "badge", "progress"],
    "powerbox": ["dialog", "list", "searchable_list", "button"],
    "links-here": ["list", "link", "tag"],
    "organs": ["accordion", "group_box", "badge", "label"],
    "cipherclerk": ["form", "input", "button", "badge"],
    "editor": ["input", "dock", "tab", "scroll", "status_bar"],
    "composer": ["input", "button", "toolbar" if False else "separator"],
    "simulate": ["button", "slider", "chart", "table"],
    "agent": ["input", "list", "avatar", "badge", "spinner"],
    "swarm": ["list", "avatar", "badge", "progress", "table"],
    "shell": ["input", "scroll", "status_bar"],
    "terminal": ["input", "scroll", "status_bar", "tab"],
    "buffer": ["input", "scroll", "tab"],
    "trust": ["table", "badge", "tag", "tree"],
    "docs": ["scroll", "breadcrumb", "link", "sidebar"],
    "time": ["time", "slider", "table"],
    "share": ["dialog", "button", "input", "clipboard"],
    "deos-chat": ["input", "list", "avatar", "badge", "hover_card"],
    "deos-editor": ["input", "dock", "tab", "scroll"],
    "deos-docviewer": ["scroll", "breadcrumb", "sidebar", "link"],
}

# which components drive which protocol verbs (the action-bearing widgets)
_COMPONENT_VERBS = {
    "button": ["Transfer", "GrantCapability", "RevokeCapability", "EmitEvent"],
    "input": ["SetField"],
    "form": ["SetField", "CreateCell"],
    "stepper": ["SetField", "IncrementNonce"],
    "switch": ["SetField"],
    "slider": ["SetField"],
    "dialog": ["GrantCapability", "RevokeCapability"],
}


def components_census(surfaces):
    """Census the vendored gpui-component crate, cross-linked to the surfaces
    that render each widget + the verbs it drives. Falls back to the static
    catalog if the crate isn't checked out beside the repo."""
    surf_for = {}
    for tab, comps in _SURFACE_COMPONENTS.items():
        for c in comps:
            surf_for.setdefault(c, []).append(tab)
    # only emit components whose surface actually exists in surfaces.json
    valid_tabs = {s["tab"] for s in surfaces}
    crate = os.path.join(ROOT, "..", "..", "gpui-component", "crates", "ui", "src")
    present = set(_COMPONENT_CATALOG)
    if os.path.isdir(crate):
        for f in os.listdir(crate):
            nm = f[:-3] if f.endswith(".rs") else f
            if nm in _COMPONENT_CATALOG:
                present.add(nm)
    out = []
    for name in sorted(present):
        group, glyph, summary = _COMPONENT_CATALOG[name]
        surfs = [t for t in surf_for.get(name, []) if t in valid_tabs]
        out.append({
            "name": name,
            "group": group,
            "glyph": glyph,
            "module": f"gpui_component::{name}",
            "summary": summary,
            "surfaces": surfs,
            "verbs": _COMPONENT_VERBS.get(name, []),
        })
    return out


# glyph per generator `kind` (the sibling lane emits richer kinds than the
# fallback's groups; map both into the SPA's swatch).
_KIND_GLYPH = {
    "action": "▣", "input": "⌶", "display": "ᴬ", "feedback": "✦",
    "container": "▢", "navigation": "▭", "overlay": "◰", "data": "▦",
    "layout": "◳", "dev": "⌗", "widgets": "❖",
}


def normalize_components(raw, surfaces):
    """Normalise the components data into the single shape the SPA reads:
      {name, group, glyph, module, summary, surfaces[], verbs[], variants[],
       used_in_deos}
    Accepts the generator's {meta, components:[{name,kind,what,used_surfaces,…}]}
    OR the fallback census list (already in SPA shape)."""
    comps = raw.get("components", raw) if isinstance(raw, dict) else raw
    if not isinstance(comps, list):
        return components_census(surfaces)
    valid_tabs = {s["tab"] for s in surfaces}
    norm_for = {t: t for t in valid_tabs}            # exact
    norm_for.update({t.replace("-", ""): t for t in valid_tabs})  # loose
    out = []
    for c in comps:
        if "summary" in c and "group" in c:          # already SPA-shaped (census)
            out.append(c); continue
        group = c.get("kind") or c.get("group") or "widgets"
        surfs = []
        for t in (c.get("used_surfaces") or c.get("surfaces") or []):
            key = str(t).lower()
            if key in norm_for and norm_for[key] not in surfs:
                surfs.append(norm_for[key])
        out.append({
            "name": c.get("name", "?"),
            "group": group,
            "glyph": c.get("glyph") or _KIND_GLYPH.get(group, "❖"),
            "module": c.get("module") and ("gpui_component::" + c["module"]) or c.get("source", ""),
            "summary": c.get("what") or c.get("summary") or "",
            "surfaces": surfs,
            "verbs": c.get("verbs", []),
            "variants": c.get("variants", []),
            "used_in_deos": bool(c.get("used_in_deos")),
        })
    return out


# ---------------------------------------------------------------------------
# assemble the data the SPA reads (inlined so it opens via file://)
# ---------------------------------------------------------------------------

def build_data_js():
    sections = all_sections()
    # render each section's markdown to html once, for the SPA
    sections_html = {slug: md_to_html(body) for slug, body in sections.items()}
    surfaces = load("surfaces.json", [])
    # attach the full explainer html to each surface (matched by its deep slug,
    # falling back to the tab slug for back-compat).
    for s in surfaces:
        s["explainer_html"] = sections_html.get(s.get("deep", s["tab"]), sections_html.get(s["tab"], ""))
    # the COMPONENTS pillar: the generator lane emits data/components.json (the
    # gpui-component widget catalog, cross-linked to surfaces + verbs). Until it
    # does, fall back to a census of the vendored crate so the pillar populates.
    components = load("components.json", None)
    if components is None:
        components = components_census(surfaces)
    data = {
        "gametree": load("gametree.json", {"meta": {}, "nodes": [], "edges": []}),
        "cells": load("cells.json", {"cells": [], "ocap": {"nodes": [], "edges": []}}),
        "protocol": load("protocol.json", {}),
        "surfaces": surfaces,
        "components": components,
        # the generator may also emit a pre-resolved cross-link graph; the SPA
        # derives one client-side from cells/surfaces/components when absent. The
        # crawler emits `hypermap.json` (the synthesized backbone, or the MCP
        # `map` tool merged in) — carried for the static floor + any consumer.
        "map": load("map.json", load("hypermap.json", None)),
        "hypermap": load("hypermap.json", {"meta": {}, "nodes": [], "edges": []}),
        "explainers": load_explainers(),
        "sections": sections_html,
    }
    with open(os.path.join(SITE, "data.js"), "w") as f:
        f.write("window.ATLAS = " + json.dumps(data) + ";\n")
    return data, sections_html


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


def build_surface_pages(data, sections_html):
    os.makedirs(os.path.join(PAGES, "surfaces"), exist_ok=True)
    # surface→components cross-link (from the components pillar's used_surfaces)
    surf_comps = {}
    for c in (data.get("components", {}) or {}).get("components", []):
        for sid in c.get("used_surfaces", []):
            surf_comps.setdefault(sid, []).append(c["name"])
    for s in data["surfaces"]:
        tab = s["tab"]
        label = s.get("label", tab)
        img = (f'<img src="../../screenshots/{html.escape(s["file"])}" style="width:100%;'
               'border:1px solid #21262d;border-radius:8px;margin:8px 0">') if s.get("file") else \
              '<p class=muted>(no screenshot yet — run shoot.py against the headless-render MCP)</p>'
        comps = surf_comps.get(tab, [])
        comp_line = (f'<p class=muted>Built from: ' +
                     " · ".join(f'<code>{html.escape(n)}</code>' for n in comps) + '</p>') if comps else ""
        body = [f'<h2>{html.escape(label)} <span class=muted>surface</span></h2>',
                img,
                f'<p class=muted>{html.escape(s.get("explainer",""))}</p>',
                comp_line,
                sections_html.get(s.get("deep", tab), sections_html.get(tab, "<p class=muted>(no deep explainer yet)</p>"))]
        open(os.path.join(PAGES, "surfaces", tab + ".html"), "w").write(
            PAGE_TMPL.format(title=label, crumb=f"surfaces / {tab}", body="\n".join(body)))


def build_faces_page(sections_html):
    faces = ["framework", "raw-fields", "graph", "domain-visual", "affordances", "provenance", "invariant", "source"]
    body = ["<h2>The seven presentation faces</h2>",
            "<p class=muted>Every protocol object is <code>Presentable</code> and offers this set of named lenses.</p>"]
    for slug in faces:
        if slug in sections_html:
            body.append(f'<h3 id="{slug}">{slug}</h3>')
            body.append(sections_html[slug])
    open(os.path.join(PAGES, "faces.html"), "w").write(
        PAGE_TMPL.format(title="Faces", crumb="faces", body="\n".join(body)))


def build_protocol_deep_page(sections_html):
    order = ["thesis", "verbs", "substances", "auth-lattice", "refusal", "receipts"]
    body = ["<h2>Protocol — deep reference</h2>"]
    for slug in order:
        if slug in sections_html:
            body.append(f'<h3 id="{slug}">{slug}</h3>')
            body.append(sections_html[slug])
    open(os.path.join(PAGES, "protocol-deep.html"), "w").write(
        PAGE_TMPL.format(title="Protocol (deep)", crumb="protocol-deep", body="\n".join(body)))


def build_components_page(data):
    """The static (JS-free) COMPONENTS reference — the gpui-component widget set,
    grouped by kind, each cross-linked to the deos surfaces that render it. Mirrors
    the SPA Components pillar for the no-JS / archival floor."""
    comp = data.get("components", {}) or {}
    comps = comp.get("components", [])
    meta = comp.get("meta", {})
    groups = {}
    for c in comps:
        groups.setdefault(c.get("group") or c.get("kind") or "widgets", []).append(c)
    body = ["<h2>Components — the visual building blocks</h2>",
            f'<p class=muted>The <code>gpui-component</code> widget set the deos cockpit is '
            f'built from: {meta.get("catalog_count", len(comps))} widgets cataloged'
            + (f', {meta.get("used_in_deos")} used live in the cockpit today' if "used_in_deos" in meta else "")
            + f'. Source: <code>{html.escape(meta.get("source_crate", "~/dev/gpui-component/crates/ui/src"))}</code>.</p>',
            f'<p class=muted>{html.escape(meta.get("note", ""))}</p>']
    for grp in sorted(groups):
        body.append(f'<h3>{html.escape(grp)} · {len(groups[grp])}</h3><table>')
        for c in sorted(groups[grp], key=lambda x: x["name"]):
            used = '<span class=ok>● in deos</span>' if c.get("used_in_deos") else '<span class=muted>○ available</span>'
            surfs = " · ".join(f'<a href="surfaces/{html.escape(s)}.html">{html.escape(s)}</a>'
                               for s in c.get("used_surfaces", [])) or "—"
            vrs = html.escape(", ".join(c.get("variants", [])[:6]))
            body.append(
                f'<tr><td class=k>{html.escape(c["name"])}<div class=muted><code>{html.escape(c.get("module",""))}</code></div></td>'
                f'<td>{html.escape(c.get("what", c.get("summary","")))}'
                f'<div class=muted>variants: {vrs}</div>'
                f'<div class=muted>surfaces: {surfs}</div></td>'
                f'<td>{used}</td></tr>')
        body.append("</table>")
    open(os.path.join(PAGES, "components.html"), "w").write(
        PAGE_TMPL.format(title="Components", crumb="components", body="\n".join(body)))


def main():
    os.makedirs(SITE, exist_ok=True)
    os.makedirs(PAGES, exist_ok=True)
    # copy screenshots in
    dst = os.path.join(SITE, "screenshots")
    if os.path.isdir(SHOTS):
        shutil.rmtree(dst, ignore_errors=True)
        shutil.copytree(SHOTS, dst)
    data, sections_html = build_data_js()
    build_cell_pages(data)
    build_protocol_page(data)
    build_surface_pages(data, sections_html)
    build_components_page(data)
    build_faces_page(sections_html)
    build_protocol_deep_page(sections_html)
    # the SPA shell + app + css are written by separate template files that
    # this script copies verbatim (kept as real files for easy editing).
    for fn in ("index.html", "app.js", "atlas.css"):
        src = os.path.join(ROOT, "tmpl", fn)
        if os.path.exists(src):
            shutil.copy(src, os.path.join(SITE, fn))
    # the vendored graph libraries — copy them in so a fresh checkout / clean
    # site/ is self-contained (the SPA <script src=assets/…> must resolve).
    src_assets = os.path.join(ROOT, "tmpl", "assets")
    if not os.path.isdir(src_assets):
        src_assets = os.path.join(SITE, "assets")   # already-present committed copy
    dst_assets = os.path.join(SITE, "assets")
    if os.path.isdir(src_assets) and os.path.abspath(src_assets) != os.path.abspath(dst_assets):
        os.makedirs(dst_assets, exist_ok=True)
        for f in os.listdir(src_assets):
            shutil.copy(os.path.join(src_assets, f), os.path.join(dst_assets, f))
    # a favicon (inline SVG — the dregg hexagon), so no 404 on load.
    with open(os.path.join(SITE, "favicon.svg"), "w") as f:
        f.write('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32">'
                '<rect width="32" height="32" rx="6" fill="#0d1117"/>'
                '<path d="M16 5l9.5 5.5v11L16 27 6.5 21.5v-11z" fill="none" '
                'stroke="#58a6ff" stroke-width="2"/>'
                '<circle cx="16" cy="16" r="3.5" fill="#3fb950"/></svg>')
    # the IE6 floor (pure HTML 4.01, for any user-agent back to 1996)
    try:
        import ie6 as _ie6; _ie6.build()
    except Exception as _e:
        print(f"  (ie6 floor skipped: {_e})")
    gt = data["gametree"]["meta"]
    print(f"atlas built → {SITE}/index.html")
    print(f"  game tree: {gt.get('node_count','?')} states / {gt.get('edge_count','?')} transitions")
    cm = (data.get("components", {}) or {}).get("meta", {})
    hm = (data.get("hypermap", {}) or {}).get("meta", {})
    print(f"  cells: {len(data['cells'].get('cells', []))} · surfaces: {len(data['surfaces'])} · "
          f"components: {len((data.get('components',{}) or {}).get('components', []))} "
          f"({cm.get('used_in_deos','?')} used live)")
    print(f"  hypermap: {hm.get('node_count','?')} nodes / {hm.get('edge_count','?')} edges")


if __name__ == "__main__":
    main()
