import assert from "node:assert/strict";
import { test } from "node:test";
import { resolveTerminalRoute } from "../src/terminal-route.js";

const routes = ["overview", "missions", "galley", "crew", "records", "bazaar", "choir"];

test("canonical hash route wins over a companion query route", () => {
  assert.equal(resolveTerminalRoute({ hash: "#records", search: "?view=missions" }, routes), "records");
});

test("signed companion query links reach their terminal view without a hash", () => {
  assert.equal(resolveTerminalRoute({ search: "?view=missions" }, routes), "missions");
  assert.equal(resolveTerminalRoute({ search: "?view=records" }, routes), "records");
  assert.equal(resolveTerminalRoute({ search: "?view=galley" }, routes), "galley");
});

test("legacy watch link and unknown routes fail closed to overview", () => {
  assert.equal(resolveTerminalRoute({ search: "?view=watch" }, routes), "overview");
  assert.equal(resolveTerminalRoute({ hash: "#missing", search: "?view=missing" }, routes), "overview");
  assert.equal(resolveTerminalRoute({ search: "?view=%00" }, routes), "overview");
  assert.equal(resolveTerminalRoute({ hash: "#missing", search: "?view=records" }, routes), "overview",
    "a non-empty invalid hash cannot silently fall through to a valid query route");
});

test("resolver remains total when a shell has no overview route", () => {
  assert.equal(resolveTerminalRoute({ search: "?view=missing" }, ["one", "two"]), "one");
  assert.equal(resolveTerminalRoute({}, []), null);
});
