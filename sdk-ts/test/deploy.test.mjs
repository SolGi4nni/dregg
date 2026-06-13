// DreggDL via the TS SDK — the REAL dregg-deploy check through dregg-wasm.
//
// `DeployChecker.check` / `.lower` call the wasm `deploy_check` / `deploy_lower`
// bindings, which run the EXACT `dregg-deploy` pipeline (parse →
// Lowered::from_deployment → dregg_userspace_verify::analyze). Nothing about the
// lowering or the userspace-verify is reimplemented in TypeScript; this test
// confirms the binding reaches the real checker.

import { test } from "node:test";
import assert from "node:assert/strict";

import { loadWasmOracle, sdk } from "./helpers.mjs";

const VALID_ESCROW = `
[federation]
id = "auto"

[[factory]]
ref = "escrow"
default_mode = "hosted"
creation_budget = 100

  [[factory.state_constraint]]
  kind = "write_once"
  slot = 3

  [[factory.allowed_cap_template]]
  permissions = "signature"
  target = "self"
  attenuatable = true

[[cell]]
name = "deal-001"
factory = "escrow"
mode = "hosted"
initial_fields = [ { slot = 3, value = 42 } ]

[[cell]]
name = "operator"
factory = "escrow"

[[cell]]
name = "bank"
factory = "escrow"

[[fund]]
from = "bank"
to = "deal-001"
amount = 1000

[[grant]]
from = "deal-001"
to = "operator"
permissions = "signature"
target = "deal-001"
`;

// `deal` hands `operator` a TRANSFER-ONLY facet (allowed_effects = 2) over
// `deal`; `operator` re-delegates an UNRESTRICTED cap over the SAME target →
// an in-forest amplification that non-amplification (A) catches.
const OVER_GRANTING = `
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

[[grant]]
from = "operator"
to = "sub"
permissions = "signature"
target = "deal"
`;

async function checker() {
  const wasm = await loadWasmOracle();
  const { DeployChecker } = await sdk();
  return new DeployChecker(wasm);
}

test("a valid escrow deployment PASSes the real check through the binding", async () => {
  const deploy = await checker();
  const v = deploy.check(VALID_ESCROW);
  assert.equal(v.pass, true, `valid escrow must pass; findings: ${JSON.stringify(v.assurance.findings)}`);
  // 3 births + 1 fund + 1 grant.
  assert.equal(v.turn_count, 5);
  assert.equal(v.cells.length, 3);
  assert.equal(v.factories.length, 1);
  assert.equal(v.assurance.pass, true);
  for (const c of ["conservation", "no_amplification", "wellformed", "ring_balance"]) {
    assert.equal(v.assurance[c].pass, true, `${c} should pass`);
  }
});

test("resolved ids are deterministic", async () => {
  const deploy = await checker();
  const a = deploy.check(VALID_ESCROW);
  const b = deploy.check(VALID_ESCROW);
  assert.deepEqual(a.cells, b.cells);
  assert.deepEqual(a.factories, b.factories);
});

test("an over-granting deployment FAILs with the located amplification", async () => {
  const deploy = await checker();
  const v = deploy.check(OVER_GRANTING);
  assert.equal(v.pass, false, "an over-granting deployment must fail");
  assert.equal(v.assurance.no_amplification.pass, false, "non-amplification (A) catches the widening");
  const findings = v.assurance.no_amplification.findings;
  assert.ok(findings.length > 0, "the failing check carries findings");
  assert.ok(
    findings.some((f) => f.message.toLowerCase().includes("amplif")),
    `a finding names the amplification; got: ${findings.map((f) => f.message)}`,
  );
  assert.notEqual(findings[0].locus.effect_index, null, "the finding locates the offending grant effect");
});

test("an unknown factory ref throws with the offending name", async () => {
  const deploy = await checker();
  const bad = `
[federation]
id = "auto"
[[cell]]
name = "c"
factory = "does-not-exist"
`;
  assert.throws(() => deploy.check(bad), /does-not-exist/);
});

test("ring=true catches an un-closed settlement ring", async () => {
  const deploy = await checker();
  const openRing = `
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"
[[fund]]
from = "a"
to = "b"
amount = 10
[[fund]]
from = "b"
to = "c"
amount = 10
`;
  const v = deploy.check(openRing, true);
  assert.equal(v.assurance.ring_balance.pass, false, "an un-closed ring fails the ring check");
  const closed = openRing + '\n[[fund]]\nfrom = "c"\nto = "a"\namount = 10\n';
  const vc = deploy.check(closed, true);
  assert.equal(vc.assurance.ring_balance.pass, true, "a closed conserving ring passes");
});

test("lower emits the ordered CallForest", async () => {
  const deploy = await checker();
  const lowered = deploy.lower(VALID_ESCROW);
  assert.ok(lowered.forest && Array.isArray(lowered.forest.roots), "the lowered artifact is a CallForest");
  assert.equal(lowered.forest.roots.length, 5, "3 births + 1 fund + 1 grant");
  assert.equal(lowered.cells.length, 3);
  assert.equal(lowered.factories.length, 1);
  assert.equal(lowered.federation_id, "00".repeat(32), "auto lowers to the all-zeros placeholder");
});

test("the JSON surface parses (leading brace)", async () => {
  const deploy = await checker();
  const dep = {
    federation: { id: "auto", node: "" },
    factory: [{ ref: "f", default_mode: "hosted" }],
    cell: [{ name: "c", factory: "f" }],
  };
  const v = deploy.check(JSON.stringify(dep));
  assert.equal(v.pass, true);
  assert.equal(v.turn_count, 1);
});
