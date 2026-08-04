import assert from "node:assert/strict";
import {
  chmodSync,
  existsSync,
  mkdtempSync,
  mkdirSync,
  readFileSync,
  unlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import test from "node:test";

import {
  POA_DEPLOYMENT_DOMAIN,
  buildManifest,
  verifyFollowerIsolation,
  verifyManifest,
  verifyPublicManifest,
  writeManifestAndConfigs,
} from "../poa-devnet-manifest.mjs";

function key(byte) {
  return Buffer.alloc(32, byte);
}

function fixture() {
  const scratch = mkdtempSync(join(tmpdir(), "poa-devnet-manifest-test-"));
  const root = join(scratch, "poa");
  const mainDataDir = join(scratch, "main");
  mkdirSync(join(root, "bundle"), { recursive: true });
  mkdirSync(join(root, "nodes"), { recursive: true });
  mkdirSync(mainDataDir, { recursive: true });
  const genesis = {
    federation_id: "a1".repeat(32),
    deployment_domain: "pathofangels.network/federation/v1",
    committee_epoch: 0,
    threshold: 3,
    validators: [1, 2, 3].map((byte, index) => ({
      name: `node-${index}`,
      public_key: byte.toString(16).padStart(2, "0").repeat(32),
    })),
    initial_cells: [
      { public_key: "a4".repeat(32), balance: 0 },
      { public_key: "a5".repeat(32), balance: 0 },
    ],
    genesis_moves: [],
    starbridge_cells: [],
  };
  const encoded = `${JSON.stringify(genesis, null, 2)}\n`;
  writeFileSync(join(root, "bundle", "genesis.json"), encoded);
  genesis.validators.forEach((_, index) => {
    writeFileSync(join(root, "bundle", `node-${index}.key`), key(index + 1));
    const dataDir = join(root, "nodes", `node-${index}`);
    mkdirSync(dataDir, { recursive: true });
    writeFileSync(join(dataDir, "node.key"), key(index + 1));
    writeFileSync(join(dataDir, "genesis.json"), encoded);
  });
  return {
    scratch,
    root,
    mainDataDir,
    options: {
      root,
      mainDataDir,
      httpBase: 8421,
      gossipBase: 9421,
      hosts: ["127.0.0.1", "127.0.0.1", "127.0.0.1"],
    },
  };
}

test("genesis wrapper executes its isolation preflight and emits a pinned federation", () => {
  const scratch = mkdtempSync(join(tmpdir(), "poa-devnet-genesis-test-"));
  const root = join(scratch, "poa");
  const mainDataDir = join(scratch, "main");
  const fakeBin = join(scratch, "dregg-node");
  mkdirSync(mainDataDir, { recursive: true });
  writeFileSync(
    fakeBin,
    `#!/usr/bin/env node
const fs = require("node:fs");
const path = require("node:path");
const args = process.argv.slice(2);
const value = (name) => args[args.indexOf(name) + 1];
if (args[0] === "genesis") {
  const output = value("--output");
  const validators = Number(value("--validators"));
  fs.mkdirSync(output, { recursive: true });
  const genesis = {
    federation_id: "${"a1".repeat(32)}",
    deployment_domain: "pathofangels.network/federation/v1",
    committee_epoch: 0,
    threshold: validators,
    validators: Array.from({ length: validators }, (_, index) => ({
      name: \`node-\${index}\`,
      public_key: (index + 1).toString(16).padStart(2, "0").repeat(32),
    })),
    initial_cells: [
      { public_key: "${"a4".repeat(32)}", balance: 0 },
      { public_key: "${"a5".repeat(32)}", balance: 0 },
    ],
    genesis_moves: [],
    starbridge_cells: [],
  };
  fs.writeFileSync(path.join(output, "genesis.json"), JSON.stringify(genesis) + "\\n");
  for (let index = 0; index < validators; index += 1) {
    fs.writeFileSync(path.join(output, \`node-\${index}.key\`), Buffer.alloc(32, index + 1));
  }
  process.exit(0);
}
if (args[0] === "gen-validator-key") {
  const index = Number(path.basename(value("--data-dir")).replace("node-", ""));
  process.stdout.write(JSON.stringify({
    public_key: (index + 1).toString(16).padStart(2, "0").repeat(32),
  }));
  process.exit(0);
}
process.exit(99);
`,
  );
  chmodSync(fakeBin, 0o755);

  const script = join(process.cwd(), "scripts", "poa-devnet.sh");
  const result = spawnSync("bash", [script, "genesis"], {
    encoding: "utf8",
    env: {
      ...process.env,
      POA_ROOT: root,
      POA_MAIN_DATA_DIR: mainDataDir,
      POA_BIN: fakeBin,
      POA_VALIDATORS: "3",
      POA_HTTP_BASE: "8421",
      POA_GOSSIP_BASE: "9421",
    },
  });
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /PoA federation ready/);
  assert.equal(verifyManifest({
    root,
    mainDataDir,
    httpBase: 8421,
    gossipBase: 9421,
    hosts: ["127.0.0.1", "127.0.0.1", "127.0.0.1"],
  }).federation_id, "a1".repeat(32));
});

test("genesis wrapper refuses overlapping storage before invoking dregg-node", () => {
  const scratch = mkdtempSync(join(tmpdir(), "poa-devnet-preflight-test-"));
  const root = join(scratch, "poa");
  const mainDataDir = join(root, "main");
  const marker = join(scratch, "binary-was-invoked");
  const fakeBin = join(scratch, "dregg-node");
  writeFileSync(fakeBin, '#!/bin/sh\n: > "$POA_FAKE_INVOKED"\nexit 99\n');
  chmodSync(fakeBin, 0o755);

  const script = join(process.cwd(), "scripts", "poa-devnet.sh");
  const result = spawnSync("bash", [script, "genesis"], {
    encoding: "utf8",
    env: {
      ...process.env,
      POA_ROOT: root,
      POA_MAIN_DATA_DIR: mainDataDir,
      POA_BIN: fakeBin,
      POA_FAKE_INVOKED: marker,
    },
  });
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /PoA root and main data dir must be disjoint/);
  assert.equal(existsSync(marker), false, "preflight must run before the node binary");
});

test("manifest pins an isolated federation and runnable, non-faucet configs", () => {
  const f = fixture();
  const manifest = writeManifestAndConfigs(f.options);
  assert.equal(manifest.deployment_domain, "pathofangels.network/federation/v1");
  assert.equal(manifest.deployment_domain, POA_DEPLOYMENT_DOMAIN);
  assert.equal(manifest.federation_id, "a1".repeat(32));
  assert.equal(manifest.policy.follower_first, true);
  assert.equal(manifest.policy.faucet_http, false);
  assert.equal(manifest.policy.auto_approve_joins, false);
  assert.equal(manifest.policy.f4_transitive_vouch_rows_live, false);
  assert.equal(manifest.policy.objective_vouch_admission_ready, false);
  assert.equal(manifest.policy.require_lean, true);
  assert.equal(manifest.policy.strand_admission_gate, true);
  assert.equal(manifest.policy.allow_unverified_consensus, false);
  assert.equal(manifest.policy.generic_genesis_value_issued, false);
  assert.deepEqual(
    manifest.nodes.map((node) => node.http.port),
    [8421, 8422, 8423],
  );
  assert.deepEqual(
    manifest.nodes.map((node) => node.gossip.port),
    [9421, 9422, 9423],
  );
  assert.equal(new Set(manifest.nodes.flatMap((node) => [node.http.port, node.gossip.port])).size, 6);

  for (const node of manifest.nodes) {
    const env = readFileSync(join(f.root, node.data_dir, "operator.env"), "utf8");
    assert.match(env, /^POA_DATA_DIR=.+/m);
    assert.match(env, /^POA_ENABLE_FAUCET=0$/m);
    assert.match(env, /^POA_AUTO_APPROVE_JOINS=0$/m);
    assert.match(env, /^POA_PROVE_TURNS=1$/m);
    assert.match(env, /^DREGG_REQUIRE_LEAN=1$/m);
    assert.match(env, /^DREGG_STRAND_ADMISSION_GATE=1$/m);
    assert.match(env, /^DREGG_ALLOW_UNVERIFIED_CONSENSUS=0$/m);
    assert.match(env, /^DREGG_STATUS_EXPOSE_COUNTS=0$/m);
  }
  assert.equal(verifyManifest(f.options).deployment_id, manifest.deployment_id);
});

test("main federation descriptor reuse is refused", () => {
  const f = fixture();
  writeFileSync(
    join(f.mainDataDir, "genesis.json"),
    JSON.stringify({ federation_id: "a1".repeat(32) }),
  );
  assert.throws(() => buildManifest(f.options), /equals the main federation/);
});

test("validator identity reuse with main is refused", () => {
  const f = fixture();
  writeFileSync(join(f.mainDataDir, "node.key"), key(2));
  assert.throws(() => buildManifest(f.options), /PoA key reuse refused/);
});

test("even a dormant faucet identity reused with main is refused", () => {
  const f = fixture();
  writeFileSync(join(f.root, "bundle", "faucet.key"), key(44));
  writeFileSync(join(f.mainDataDir, "faucet.key"), key(44));
  assert.throws(() => buildManifest(f.options), /must not emit a faucet key/);
});

test("auxiliary identity overlap in main genesis is refused even without private key files", () => {
  const f = fixture();
  writeFileSync(
    join(f.mainDataDir, "genesis.json"),
    JSON.stringify({
      federation_id: "b2".repeat(32),
      initial_cells: [{ public_key: "a4".repeat(32) }],
    }),
  );
  assert.throws(() => buildManifest(f.options), /also appears in main genesis/);
});

test("serving validator seeds must be exact copies of the authoritative bundle", () => {
  const f = fixture();
  writeFileSync(join(f.root, "nodes", "node-2", "node.key"), key(1));
  assert.throws(() => buildManifest(f.options), /not byte-identical to its authoritative/);
});

test("duplicate validator seeds inside the authoritative bundle are refused", () => {
  const f = fixture();
  writeFileSync(join(f.root, "bundle", "node-2.key"), key(1));
  writeFileSync(join(f.root, "nodes", "node-2", "node.key"), key(1));
  assert.throws(() => buildManifest(f.options), /bundle validator key reuse refused/);
});

test("serving data dirs must pin exact genesis and omit the devnet auto-admit marker", () => {
  const f = fixture();
  writeFileSync(join(f.root, "nodes", "node-1", "genesis.json"), "{}\n");
  assert.throws(() => buildManifest(f.options), /not byte-identical/);

  const g = fixture();
  writeFileSync(join(g.root, "nodes", "node-1", ".devnet"), "unsafe implicit policy\n");
  assert.throws(() => buildManifest(g.options), /silently enables automatic Join approval/);
});

test("manifest verification catches descriptor changes after generation", () => {
  const f = fixture();
  writeManifestAndConfigs(f.options);
  const genesisPath = join(f.root, "bundle", "genesis.json");
  const genesis = JSON.parse(readFileSync(genesisPath, "utf8"));
  genesis.committee_epoch = 1;
  writeFileSync(genesisPath, JSON.stringify(genesis));
  assert.throws(
    () => verifyManifest(f.options),
    /not byte-identical|pinned genesis, keys, paths, or ports/,
  );
});

test("a follower pins genesis and must reuse neither committee nor main keys", () => {
  const f = fixture();
  writeManifestAndConfigs(f.options);
  const follower = join(f.root, "followers", "deck-447");
  mkdirSync(follower, { recursive: true });
  writeFileSync(follower + "/node.key", key(90));
  writeFileSync(
    follower + "/genesis.json",
    readFileSync(join(f.root, "bundle", "genesis.json")),
  );
  assert.equal(
    verifyFollowerIsolation({ ...f.options, name: "deck-447" }).name,
    "deck-447",
  );

  writeFileSync(follower + "/node.key", key(3));
  assert.throws(
    () => verifyFollowerIsolation({ ...f.options, name: "deck-447" }),
    /follower key reuse refused/,
  );
});

test("public follower verification needs no validator private seeds", () => {
  const f = fixture();
  const manifest = writeManifestAndConfigs(f.options);
  for (let index = 0; index < 3; index += 1) {
    unlinkSync(join(f.root, "bundle", `node-${index}.key`));
    unlinkSync(join(f.root, "nodes", `node-${index}`, "node.key"));
  }
  assert.equal(verifyPublicManifest(f.options).deployment_id, manifest.deployment_id);
  assert.throws(() => verifyManifest(f.options), /missing (bundle )?validator key/);
});

test("public manifest refuses a node data path outside its fixed PoA directory", () => {
  const f = fixture();
  writeManifestAndConfigs(f.options);
  const path = join(f.root, "poa-devnet.json");
  const manifest = JSON.parse(readFileSync(path, "utf8"));
  manifest.nodes[0].data_dir = "../../main";
  writeFileSync(path, `${JSON.stringify(manifest, null, 2)}\n`);
  assert.throws(() => verifyPublicManifest(f.options), /data_dir must be exactly nodes\/node-0/);
});

test("tampered operator config cannot redirect a validator after public verification", () => {
  const f = fixture();
  writeManifestAndConfigs(f.options);
  const path = join(f.root, "nodes", "node-1", "operator.env");
  const config = readFileSync(path, "utf8").replace(
    /^POA_DATA_DIR=.*$/m,
    `POA_DATA_DIR=${f.mainDataDir}`,
  );
  writeFileSync(path, config, { mode: 0o600 });
  chmodSync(path, 0o600);
  assert.throws(
    () => verifyPublicManifest(f.options),
    /does not exactly match the manifest-derived operator configuration/,
  );
});

test("PoA storage cannot contain or be contained by main storage", () => {
  const f = fixture();
  assert.throws(
    () => buildManifest({ ...f.options, mainDataDir: join(f.root, "main") }),
    /must be disjoint/,
  );
});

test("a three-host manifest emits real cross-host gossip peers", () => {
  const f = fixture();
  const manifest = buildManifest({
    ...f.options,
    hosts: ["hbox.poa", "persvati.poa", "cipherclerk.poa"],
  });
  assert.deepEqual(manifest.nodes[0].gossip.peers, ["persvati.poa:9422", "cipherclerk.poa:9423"]);
  assert.deepEqual(manifest.nodes[1].gossip.peers, ["hbox.poa:9421", "cipherclerk.poa:9423"]);
  assert.deepEqual(manifest.nodes[2].gossip.peers, ["hbox.poa:9421", "persvati.poa:9422"]);
});

test("multi-host topology refuses an advertised loopback", () => {
  const f = fixture();
  assert.throws(
    () => buildManifest({ ...f.options, hosts: ["hbox.poa", "127.0.0.1", "cipherclerk.poa"] }),
    /cannot advertise a loopback/,
  );
});

test("three-host operator command preserves key/data paths, bind, and remote peers", () => {
  const f = fixture();
  const hosts = ["hbox.poa", "persvati.poa", "cipherclerk.poa"];
  writeManifestAndConfigs({ ...f.options, hosts });
  const fakeBin = join(f.scratch, "dregg-node");
  writeFileSync(
    fakeBin,
    `#!/bin/sh\nif [ "$1" = gen-validator-key ]; then printf '{"public_key":"${"02".repeat(32)}"}'; exit 0; fi\nexit 99\n`,
  );
  chmodSync(fakeBin, 0o755);
  const script = join(process.cwd(), "scripts", "poa-devnet.sh");
  const result = spawnSync("bash", [script, "operator-command", "1", "100.70.0.2"], {
    encoding: "utf8",
    env: {
      ...process.env,
      POA_ROOT: f.root,
      POA_MAIN_DATA_DIR: f.mainDataDir,
      POA_BIN: fakeBin,
      POA_VALIDATORS: "3",
      POA_HTTP_BASE: "8421",
      POA_GOSSIP_BASE: "9421",
      POA_NODE_HOSTS: hosts.join(","),
    },
  });
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /--data-dir .*\/nodes\/node-1/);
  assert.match(result.stdout, /--key-file node\.key/);
  assert.match(result.stdout, /--bind 100\.70\.0\.2/);
  assert.match(result.stdout, /--port 8422/);
  assert.match(result.stdout, /--gossip-port 9422/);
  assert.match(result.stdout, /--federation-peers hbox\.poa:9421\\,cipherclerk\.poa:9423/);
  assert.match(result.stdout, /^DREGG_REQUIRE_LEAN=1 DREGG_STRAND_ADMISSION_GATE=1 /);
  assert.match(result.stdout, /DREGG_ALLOW_UNVERIFIED_CONSENSUS=0/);
  assert.doesNotMatch(result.stdout, /--enable-faucet|--auto-approve-joins/);
});

test("operator command rejects an inherited unverified-consensus opt-in", () => {
  const f = fixture();
  writeManifestAndConfigs(f.options);
  const fakeBin = join(f.scratch, "dregg-node");
  writeFileSync(
    fakeBin,
    `#!/bin/sh\nif [ "$1" = gen-validator-key ]; then printf '{"public_key":"${"01".repeat(32)}"}'; exit 0; fi\nexit 99\n`,
  );
  chmodSync(fakeBin, 0o755);
  const script = join(process.cwd(), "scripts", "poa-devnet.sh");
  const result = spawnSync("bash", [script, "operator-command", "0"], {
    encoding: "utf8",
    env: {
      ...process.env,
      POA_ROOT: f.root,
      POA_MAIN_DATA_DIR: f.mainDataDir,
      POA_BIN: fakeBin,
      DREGG_ALLOW_UNVERIFIED_CONSENSUS: "1",
    },
  });
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /DREGG_ALLOW_UNVERIFIED_CONSENSUS is forbidden/);
});

test("follower config and printed join command retain the verified-consensus policy", () => {
  const f = fixture();
  const manifest = writeManifestAndConfigs(f.options);
  const fakeBin = join(f.scratch, "dregg-node");
  writeFileSync(
    fakeBin,
    `#!/bin/sh
if [ "$1" = gen-validator-key ]; then
  shift
  data_dir=
  while [ "$#" -gt 0 ]; do
    if [ "$1" = --data-dir ]; then data_dir="$2"; shift 2; else shift; fi
  done
  if [ ! -f "$data_dir/node.key" ]; then dd if=/dev/zero of="$data_dir/node.key" bs=32 count=1 2>/dev/null; fi
  printf '{"public_key":"${"5a".repeat(32)}"}'
  exit 0
fi
exit 99
`,
  );
  chmodSync(fakeBin, 0o755);
  const script = join(process.cwd(), "scripts", "poa-devnet.sh");
  const env = {
    ...process.env,
    POA_ROOT: f.root,
    POA_MAIN_DATA_DIR: f.mainDataDir,
    POA_BIN: fakeBin,
  };
  const init = spawnSync("bash", [script, "follower-init", "deck-447"], {
    encoding: "utf8",
    env,
  });
  assert.equal(init.status, 0, init.stderr);
  const followerEnv = readFileSync(
    join(f.root, "followers", "deck-447", "operator.env"),
    "utf8",
  );
  assert.match(followerEnv, new RegExp(`^POA_DEPLOYMENT_ID=${manifest.deployment_id}$`, "m"));
  assert.match(followerEnv, /^DREGG_REQUIRE_LEAN=1$/m);
  assert.match(followerEnv, /^DREGG_STRAND_ADMISSION_GATE=1$/m);
  assert.match(followerEnv, /^DREGG_ALLOW_UNVERIFIED_CONSENSUS=0$/m);

  const command = spawnSync(
    "bash",
    [script, "follower-command", "deck-447", "hbox.poa:9421", "100.70.0.44"],
    { encoding: "utf8", env },
  );
  assert.equal(command.status, 0, command.stderr);
  assert.match(command.stdout, /^DREGG_REQUIRE_LEAN=1 DREGG_STRAND_ADMISSION_GATE=1 /);
  assert.match(command.stdout, /DREGG_ALLOW_UNVERIFIED_CONSENSUS=0/);
  assert.match(command.stdout, /join --bootstrap hbox\.poa:9421/);
  assert.match(command.stdout, /--prove-turns/);
});
