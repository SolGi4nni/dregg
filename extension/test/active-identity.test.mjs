import test from "node:test";
import assert from "node:assert/strict";

import { resolveActiveDreggIdentity } from "./.build/active-identity.mjs";

const key = (byte) => Array(32).fill(byte);

function state(overrides = {}) {
  return {
    locked: false,
    uninitialized: false,
    needsPassphraseSetup: false,
    publicKey: key(0xab),
    activeProfile: "default",
    profiles: [{ name: "default", publicKey: key(0xab) }],
    ...overrides,
  };
}

test("active identity returns exact public-only provider shape", () => {
  assert.deepEqual(resolveActiveDreggIdentity(state()), {
    ok: true,
    identity: { publicKeyHex: "ab".repeat(32), profileName: "default" },
  });
  assert.equal(Object.keys(resolveActiveDreggIdentity(state()).identity).sort().join(","), "profileName,publicKeyHex");
});

test("locked, uninitialized, passphrase-incomplete and no-profile states refuse", () => {
  assert.match(resolveActiveDreggIdentity(state({ locked: true })).error, /locked/i);
  assert.match(resolveActiveDreggIdentity(state({ uninitialized: true })).error, /No Dregg identity/i);
  assert.match(resolveActiveDreggIdentity(state({ needsPassphraseSetup: true })).error, /passphrase/i);
  assert.match(resolveActiveDreggIdentity(state({ profiles: [] })).error, /No active Dregg profile/i);
});

test("profile switching changes the public identity and malformed mirrors fail closed", () => {
  const profiles = [
    { name: "default", publicKey: key(0xab) },
    { name: "expedition", publicKey: key(0xcd) },
  ];
  const before = resolveActiveDreggIdentity(state({ profiles }));
  const after = resolveActiveDreggIdentity(state({ profiles, activeProfile: "expedition", publicKey: key(0xcd) }));
  assert.equal(before.identity.publicKeyHex, "ab".repeat(32));
  assert.deepEqual(after, { ok: true, identity: { publicKeyHex: "cd".repeat(32), profileName: "expedition" } });
  assert.match(resolveActiveDreggIdentity(state({ profiles, activeProfile: "expedition" })).error, /inconsistent/i);
  assert.match(resolveActiveDreggIdentity(state({ publicKey: [...key(0xab).slice(0, 31), 256] })).error, /inconsistent/i);
});
