#!/usr/bin/env node
// ============================================================================
// check-verdict-provenance — DOES THE PAGE'S ✓ MEAN WHAT IT SAYS?
//
// ⚑ WHY THIS EXECUTES RATHER THAN GREPS. Every other guard over these files is a
// substring check, and the defect this exists to catch is not a substring: it is a
// verdict whose ORACLE came from the party under test. That is a property of what
// the code DOES, so this loads the real `site/dregg-works/verify-badge.js` into a
// minimal DOM + fetch harness and plays the hostile host: forged bytes, plus a
// node the PAGE names which happily commits blake3(those forged bytes). A badge
// that paints green on that is defeated, and it painted green until 2026-07-30.
//
// It also runs the two polarities that must keep working: the visitor-supplied
// oracle reaches "verified", and a real mismatch still refuses.
//
// Then the same treatment for `transclude.js`, whose oracle is the node alone.
//
// USAGE
//   node scripts/check-verdict-provenance.mjs            # the gate
//   node scripts/check-verdict-provenance.mjs --self-test # prove it can go RED
//
// Exit 0 = every scenario produced the verdict it should. Exit 1 = a surface
// reports a stronger verdict than the one it ran (message names which scenario).
// No cargo, no wasm, no network. Node only.
// ============================================================================
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import vm from "node:vm";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const SELF_TEST = process.argv.includes("--self-test");

const FORGED = "<!doctype html><h1>PWNED</h1>";
const HONEST = "<!doctype html><h1>the real page</h1>";
// blake3 is computed by the script under test; the harness never needs its own.
// The hostile node simply echoes whatever hash it is asked to bless, which is
// exactly the power a host that controls `data-node` has.

let failures = [];
function check(scenario, cond, why) {
  if (!cond) failures.push(`${scenario}: ${why}`);
}

// ── the minimal DOM + fetch harness ────────────────────────────────────────
function makeEl(tag) {
  const el = {
    tagName: String(tag).toUpperCase(),
    _cls: new Set(),
    children: [],
    dataset: {},
    style: {},
    id: "",
    _html: "",
    _text: "",
    get className() { return [...el._cls].join(" "); },
    set className(v) { el._cls = new Set(String(v).split(/\s+/).filter(Boolean)); },
    classList: {
      add: (...c) => c.forEach((x) => el._cls.add(x)),
      remove: (...c) => c.forEach((x) => el._cls.delete(x)),
      toggle: (c) => (el._cls.has(c) ? el._cls.delete(c) : el._cls.add(c)),
      contains: (c) => el._cls.has(c),
    },
    get innerHTML() { return el._html; },
    set innerHTML(v) { el._html = String(v); },
    get textContent() { return el._text; },
    set textContent(v) { el._text = String(v); },
    appendChild: (c) => { el.children.push(c); return c; },
    querySelector: () => null,
    querySelectorAll: () => [],
    setAttribute: () => {},
    getAttribute: () => null,
    addEventListener: () => {},
    removeAttribute: () => {},
    scrollIntoView: () => {},
  };
  return el;
}

function makeWindow({ search, pageCell, pageNode, servedBody, nodeAnswer }) {
  const head = makeEl("head");
  const body = makeEl("body");
  const scriptTag = makeEl("script");
  scriptTag.dataset = {};
  if (pageCell) scriptTag.dataset.cell = pageCell;
  if (pageNode) scriptTag.dataset.node = pageNode;
  scriptTag.src = "/verify-badge.js";

  const document = {
    readyState: "complete",
    currentScript: scriptTag,
    head,
    body,
    createElement: makeEl,
    getElementById: () => null,
    getElementsByTagName: () => [scriptTag],
    querySelector: () => null,
    querySelectorAll: () => [],
    addEventListener: () => {},
  };

  const location = { href: "https://evil.example/" + search, search };

  const win = {
    document,
    location,
    URLSearchParams,
    TextDecoder,
    Uint8Array,
    Promise,
    console,
    setTimeout,
    fetch: async (url) => {
      const u = String(url);
      if (u.indexOf("/api/cell/") >= 0) {
        if (nodeAnswer === null) return { ok: false, status: 404 };
        return {
          ok: true,
          status: 200,
          json: async () => nodeAnswer,
        };
      }
      const bytes = new TextEncoder().encode(servedBody);
      return { ok: true, status: 200, arrayBuffer: async () => bytes.buffer };
    },
  };
  win.window = win;
  win.self = win;
  return win;
}

// The node's answer must be blake3(served) for the "hostile host mints its own
// oracle" scenario, and the script under test is the only blake3 in the tree that
// is guaranteed to agree with itself. So: run once with a deliberately-wrong
// commitment to LEARN the served hash out of the rendered panel, then run again
// with that hash as the commitment. That is exactly the two HTTP requests a
// tampering host would make.
function servedHashOf(src, servedBody) {
  const win = makeWindow({
    search: "",
    pageCell: "aa".repeat(32),
    pageNode: "https://evil-node.example",
    servedBody,
    nodeAnswer: { found: true, fields: ["00".repeat(32)] },
  });
  return runBadge(src, win).then(() => {
    const m = /served bytes — blake3<\/b>([0-9a-f]{64})/.exec(win.__panelHtml || "");
    if (!m) throw new Error("harness could not read the served hash out of the badge panel");
    return m[1];
  });
}

async function runBadge(src, win) {
  const ctx = vm.createContext(win);
  vm.runInContext(src, ctx);
  // The badge's fetches are microtask-chained; drain them.
  for (let i = 0; i < 50; i++) await new Promise((r) => setImmediate(r));
  // The panel is the last element appended to body with a dw-panel class.
  const panel = win.document.body.children.find((c) => c._cls && c._cls.has("dw-panel"));
  const badge = win.document.body.children.find((c) => c._cls && c._cls.has("dw-vbadge"));
  win.__panelHtml = panel ? panel.innerHTML : "";
  win.__badgeCls = badge ? badge.className : "";
  win.__badgeHtml = badge ? badge.innerHTML : "";
  return win;
}

// ── the scenarios ──────────────────────────────────────────────────────────
async function badgeScenarios(src) {
  const forgedHash = await servedHashOf(src, FORGED);

  // 1. ⚑ THE HOSTILE HOST. Forged bytes; the PAGE names the cell and a node that
  //    commits exactly blake3(forged). Every comparison the script makes holds.
  {
    const win = makeWindow({
      search: "",
      pageCell: "cc".repeat(32),
      pageNode: "https://evil-node.example",
      servedBody: FORGED,
      nodeAnswer: { found: true, fields: [forgedHash] },
    });
    await runBadge(src, win);
    const v = win.__DREGG_VERIFY__ || {};
    check(
      "hostile-host",
      v.verdict === undefined,
      `a page-supplied oracle must NOT produce the success word. The host served forged ` +
        `bytes, named a cell and a node that commit them, and every hash matched — a real ` +
        `comparison over an oracle the party under test chose. Got verdict=${JSON.stringify(v.verdict)}`
    );
    check(
      "hostile-host",
      v.state === "consistent",
      `the third state is the whole repair: not a pass, not a refusal. Got state=${JSON.stringify(v.state)}`
    );
    check(
      "hostile-host",
      v.oracle_from_visitor === false,
      "the branchable provenance bit must be false when the page supplied the oracle"
    );
    check(
      "hostile-host",
      /consistency check, not a trust decision/.test(win.__panelHtml),
      "every verdict must PRINT which oracle it used and what that makes it"
    );
    check(
      "hostile-host",
      !/did not trust the host/i.test(win.__panelHtml),
      "the withdrawn claim must stay withdrawn — this is the sentence a stranger acts on"
    );
  }

  // 2. THE TRUST DECISION. Both halves from the visitor's own URL, and they match.
  {
    const honestHash = await servedHashOf(src, HONEST);
    const search = `?dregg-cell=${"dd".repeat(32)}&dregg-node=https%3A%2F%2Fmy-node.example`;
    const win = makeWindow({
      search,
      pageCell: "",
      pageNode: "",
      servedBody: HONEST,
      nodeAnswer: { found: true, fields: [honestHash] },
    });
    await runBadge(src, win);
    const v = win.__DREGG_VERIFY__ || {};
    check(
      "visitor-oracle",
      v.verdict === "verified",
      `a visitor-supplied oracle that matches IS the trust decision and must reach the ` +
        `success word — a gate that cannot go green is not a gate. Got ${JSON.stringify(v.verdict)}`
    );
    check("visitor-oracle", v.state === "ok", `expected state=ok, got ${JSON.stringify(v.state)}`);
    check(
      "visitor-oracle",
      v.oracle_from_visitor === true && v.cell_source === "visitor-url" && v.node_source === "visitor-url",
      "both halves must be reported as visitor-sourced"
    );
  }

  // 3. THE REFUSAL still fires: served bytes ≠ commitment.
  {
    const win = makeWindow({
      search: "",
      pageCell: "ee".repeat(32),
      pageNode: "https://a-node.example",
      servedBody: FORGED,
      nodeAnswer: { found: true, fields: ["11".repeat(32)] },
    });
    await runBadge(src, win);
    const v = win.__DREGG_VERIFY__ || {};
    check("mismatch", v.state === "bad", `a hash mismatch must refuse, got ${JSON.stringify(v.state)}`);
    check("mismatch", v.verdict === undefined, "a refusal must not carry the success word");
  }

  // 4. THE CELL DISAGREEMENT: the visitor's ?dregg-cell= vs the page's data-cell.
  //    Refused BEFORE any comparison — no hashing can repair a page answering to a
  //    different cell than the link that reached it.
  {
    const win = makeWindow({
      search: `?dregg-cell=${"11".repeat(32)}`,
      pageCell: "22".repeat(32),
      pageNode: "https://a-node.example",
      servedBody: HONEST,
      nodeAnswer: { found: true, fields: ["11".repeat(32)] },
    });
    await runBadge(src, win);
    const v = win.__DREGG_VERIFY__ || {};
    check(
      "cell-disagreement",
      v.state === "bad" && v.verdict === undefined,
      `a page declaring a cell other than the one the visitor named must be refused, got ` +
        `state=${JSON.stringify(v.state)}`
    );
  }
}

// ── transclude.js: the oracle is the node, and the reader's must WIN ────────
function transcludeScenarios(src) {
  // A source read, not an execution: transclude's per-element painting needs a
  // real querySelector tree that the badge harness does not model. What must hold
  // structurally is checked here, and it is the part that regressed.
  check(
    "transclude-visitor-node",
    /visitorNode\s*\(/.test(src) && /dregg-node/.test(src),
    "the reader must be able to supply the commitment oracle from their own URL"
  );
  const m = /var\s+elNode\s*=\s*([^;]+);/.exec(src);
  check(
    "transclude-visitor-node",
    m && /yours\s*\?\s*node\.visitor/.test(m[1]),
    "the reader's ?dregg-node= must OUTRANK the per-element data-node — otherwise the " +
      "party under test opts out of the reader's oracle one attribute at a time"
  );
  check(
    "transclude-grading",
    /dt-consistent/.test(src) && /consistency check, not a trust decision/.test(src),
    "a page-chosen node must paint a distinct, labelled state — not the same green as a " +
      "reader-chosen one"
  );
  check(
    "transclude-grading",
    !/paintVerified\s*\(/.test(src),
    "one painter for both positive outcomes, so the grading cannot drift apart"
  );
  // The forgery refusal must survive the change.
  check(
    "transclude-refusal",
    /ContentHashMismatch/.test(src) && /were not rendered/.test(src),
    "the forgery refusal is a neighbouring check and must not be weakened"
  );
}

// ── main ───────────────────────────────────────────────────────────────────
const badgeSrc = readFileSync(path.join(ROOT, "site/dregg-works/verify-badge.js"), "utf8");
const transSrc = readFileSync(path.join(ROOT, "site/dregg-works/transclude.js"), "utf8");

// ⚑ THE SELF-TEST IS THE PROOF THIS GATE CAN GO RED, and it mutates only an
// in-memory copy — the tree is never touched. It reinstates the exact defect:
// the success word written unconditionally on a match.
const badgeUnderTest = SELF_TEST
  ? badgeSrc.replace(
      'if (state === "ok") window.__DREGG_VERIFY__.verdict = "verified";\n      else delete window.__DREGG_VERIFY__.verdict;',
      'window.__DREGG_VERIFY__.verdict = "verified";'
    ).replace('if (match && prov.own) {', 'if (match) {')
  : badgeSrc;

if (SELF_TEST && badgeUnderTest === badgeSrc) {
  console.error(
    "check-verdict-provenance --self-test: the mutation did not apply, so this run proves " +
      "NOTHING about whether the gate can go red. The source it patches has moved; update the " +
      "patch (that is the point of the row existing)."
  );
  process.exit(1);
}

await badgeScenarios(badgeUnderTest);
transcludeScenarios(transSrc);

if (SELF_TEST) {
  if (failures.length === 0) {
    console.error(
      "check-verdict-provenance --self-test: the defect was reinstated and the gate STAYED " +
        "GREEN. A gate that cannot go red is not a gate."
    );
    process.exit(1);
  }
  console.log(
    `check-verdict-provenance --self-test: the reinstated defect produced ${failures.length} ` +
      `red scenario(s), as it must:\n  ` + failures.join("\n  ")
  );
  process.exit(0);
}

if (failures.length) {
  console.error("check-verdict-provenance: A SURFACE REPORTS MORE THAN IT RAN\n");
  for (const f of failures) console.error("  ✗ " + f);
  console.error(
    "\nThese are executed scenarios, not string matches. Each one is a verdict a stranger " +
      "reads and acts on."
  );
  process.exit(1);
}
console.log(
  "verdict-provenance: the badge refuses the hostile-host oracle (consistent, no success " +
    "word), reaches `verified` only on a visitor-supplied oracle, still refuses a hash " +
    "mismatch and a cell disagreement; transclude grades its node's provenance and keeps its " +
    "forgery refusal."
);
