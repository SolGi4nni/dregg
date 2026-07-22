import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
  buildDescentActionMenu,
  mountDescentActionMenu,
} from "../assets/descent-play-actions.mjs";

const ACTIONS = [
  { label: "Take the amber key", turn: "loot", arg: 3, enabled: true },
  { label: "End the run and bank 1 carried relic", turn: "flee", arg: 0, enabled: true },
  { label: "Descend to floor 3", turn: "delve", arg: 0, enabled: false },
  { label: "Exercise the key to way 4", turn: "unlock", arg: 4, enabled: false },
];

test("action menu promotes legal choices while retaining the complete locked catalogue", () => {
  const menu = buildDescentActionMenu(ACTIONS);

  assert.deepEqual(
    menu.available.map(({ label, turn, arg }) => ({ label, turn, arg })),
    [
      { label: "Take the amber key", turn: "loot", arg: 3 },
      { label: "End the run and bank 1 carried relic", turn: "flee", arg: 0 },
    ],
    "the Offering's authored order is preserved for takeable moves",
  );
  assert.deepEqual(
    menu.unavailable.map(({ label }) => label),
    ["Descend to floor 3", "Exercise the key to way 4"],
    "locked moves stay discoverable instead of disappearing",
  );
  assert.equal(menu.availableCount + menu.unavailableCount, ACTIONS.length);
  assert.equal(menu.summary, "2 moves are available now.");
  assert.equal(menu.unavailableLabel, "2 unavailable moves");
  assert.ok(
    menu.unavailable.every(({ reason }) => reason === "Not legal in the current committed state."),
    "the UI explains the decoration generically without mirroring a game rule",
  );
});

test("a settled run exposes no stale clickable action", () => {
  const menu = buildDescentActionMenu(ACTIONS, { ended: true });

  assert.equal(menu.availableCount, 0);
  assert.equal(menu.unavailableCount, ACTIONS.length);
  assert.equal(menu.heading, "Run settled");
  assert.match(menu.summary, /No further moves/);
  assert.ok(menu.unavailable.every(({ reason }) => reason === "The run is already settled."));
});

test("malformed enabled affordances fail closed and input rows are not mutated", () => {
  const malformed = { label: "Forged door", turn: "", arg: "not-an-integer", enabled: true };
  const before = structuredClone(malformed);
  const menu = buildDescentActionMenu([malformed, null]);

  assert.equal(menu.availableCount, 0);
  assert.equal(menu.unavailableCount, 2);
  assert.equal(menu.unavailable[0].reason, "Malformed affordance withheld.");
  assert.equal(menu.unavailable[1].reason, "Malformed affordance withheld.");
  assert.deepEqual(malformed, before, "presentation never rewrites the engine response");
});

class FakeNode {
  constructor(ownerDocument, tagName = "") {
    this.ownerDocument = ownerDocument;
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.attributes = new Map();
    this.dataset = {};
    this.className = "";
    this.textContent = "";
    this.listeners = new Map();
    this.type = "";
  }

  appendChild(child) {
    if (child.tagName === "#FRAGMENT") this.children.push(...child.children);
    else this.children.push(child);
    return child;
  }

  replaceChildren(...children) {
    this.children = [];
    for (const child of children) this.appendChild(child);
  }

  setAttribute(name, value) {
    this.attributes.set(name, String(value));
  }

  addEventListener(name, callback) {
    this.listeners.set(name, callback);
  }

  click() {
    this.listeners.get("click")?.();
  }
}

class FakeDocument {
  createElement(tagName) {
    return new FakeNode(this, tagName);
  }

  createDocumentFragment() {
    return new FakeNode(this, "#fragment");
  }
}

function descendants(node) {
  return [node, ...node.children.flatMap(descendants)];
}

test("mounted menu has semantic primary buttons and an accessible unavailable disclosure", () => {
  const document = new FakeDocument();
  const container = document.createElement("section");
  const chosen = [];

  const menu = mountDescentActionMenu(container, ACTIONS, {
    onChoose: (action) => chosen.push([action.turn, action.arg]),
  });
  const all = descendants(container);
  const buttons = all.filter(({ tagName }) => tagName === "BUTTON");
  const details = all.find(({ tagName }) => tagName === "DETAILS");
  const summary = all.find(({ tagName }) => tagName === "SUMMARY");
  const lockedRows = all.filter(({ tagName }) => tagName === "LI");

  assert.equal(menu.availableCount, 2);
  assert.equal(buttons.length, 2, "only takeable moves are primary buttons");
  assert.equal(container.attributes.get("role"), "region");
  const heading = all.find(({ tagName }) => tagName === "H2");
  const assurance = all.find(({ className }) => className === "nd-action-assurance");
  assert.equal(container.attributes.get("aria-labelledby"), heading.id);
  assert.equal(container.dataset.availableCount, "2");
  assert.equal(container.dataset.unavailableCount, "2");
  assert.match(assurance.textContent, /executor checks/i);
  assert.equal(details.className, "nd-unavailable");
  assert.equal(summary.textContent, "2 unavailable moves");
  assert.match(summary.attributes.get("aria-label"), /Expand to learn/i);
  assert.equal(lockedRows.length, 2, "every disabled affordance remains in the DOM");
  assert.equal(buttons[0].dataset.turn, "loot");
  assert.equal(buttons[0].dataset.arg, "3");
  assert.equal(buttons[0].attributes.get("aria-describedby"), assurance.id);

  buttons[0].click();
  assert.deepEqual(chosen, [["loot", 3]], "the exact normalized turn and arg reach the host");
});

test("the served page imports the helper and carries touch, focus, and narrow-screen CSS", async () => {
  const source = await readFile(
    new URL("../src/descent_play.rs", import.meta.url),
    "utf8",
  );

  assert.match(
    source,
    /\.route\("\/descent\/play\/static\/actions\.js", get\(get_play_actions_js\)\)/,
    "the helper is served from the same-origin play router",
  );
  assert.match(source, /import \{ mountDescentActionMenu \} from "\.\/actions\.js";/);
  assert.match(source, /mountDescentActionMenu\(actionMenu, actions,/);
  assert.match(source, /\.nd-actions button\{min-height:48px;/, "primary moves are touch-sized");
  assert.match(source, /button:focus-visible/, "keyboard focus is strongly visible");
  assert.match(source, /@media\(max-width:620px\)/, "the action layout has a narrow-screen mode");
  assert.match(
    source,
    /\.nd-unavailable li\{flex-direction:column;/,
    "locked labels and explanations stack instead of squeezing on a phone",
  );
});
