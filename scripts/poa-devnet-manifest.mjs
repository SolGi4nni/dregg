#!/usr/bin/env node

/**
 * Path of Angels devnet deployment-manifest authority.
 *
 * This file deliberately owns only deployment invariants.  It does not derive a
 * federation, a committee, or a validator identity: `dregg-node genesis` and
 * `dregg-node gen-validator-key` remain the authorities for those objects.  The
 * manifest pins their public outputs and refuses the easy ways an operator could
 * accidentally point PoA at the main federation's identity or storage.
 */

import { createHash } from "node:crypto";
import {
  chmodSync,
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  realpathSync,
  renameSync,
  writeFileSync,
} from "node:fs";
import { dirname, isAbsolute, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

export const POA_DEPLOYMENT_DOMAIN = "pathofangels.network/federation/v1";
export const POA_MANIFEST_SCHEMA = "dregg-poa-devnet-manifest-v1";

const POA_POLICY = Object.freeze({
  follower_first: true,
  descriptor_pinned: true,
  admission: "committee-ratified-manual-v1",
  f4_transitive_vouch_rows_live: false,
  objective_vouch_admission_ready: false,
  prove_turns: true,
  require_lean: true,
  strand_admission_gate: true,
  allow_unverified_consensus: false,
  faucet_http: false,
  auto_approve_joins: false,
  public_private_activity_counts: false,
  shares_main_identity: false,
  shares_main_storage: false,
  generic_genesis_value_issued: false,
});

const HEX32 = /^[0-9a-f]{64}$/;

function fail(message) {
  throw new Error(message);
}

function readJson(path, label = path) {
  let value;
  try {
    value = JSON.parse(readFileSync(path, "utf8"));
  } catch (error) {
    fail(`${label} is not valid JSON: ${error.message}`);
  }
  return value;
}

function sha256Bytes(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function sha256File(path) {
  return sha256Bytes(readFileSync(path));
}

function canonical(path) {
  const absolute = resolve(path);
  if (existsSync(absolute)) return realpathSync(absolute);

  // Resolve the closest existing ancestor.  `realpathSync` on the full path
  // would reject a perfectly valid not-yet-created follower directory.
  const missing = [];
  let cursor = absolute;
  while (!existsSync(cursor)) {
    const parent = dirname(cursor);
    if (parent === cursor) break;
    missing.unshift(relative(parent, cursor));
    cursor = parent;
  }
  const base = existsSync(cursor) ? realpathSync(cursor) : cursor;
  return resolve(base, ...missing);
}

function isSameOrNested(left, right) {
  const rel = relative(left, right);
  return rel === "" || (!rel.startsWith(`..${sep}`) && rel !== ".." && !isAbsolute(rel));
}

export function assertDisjointRoots(poaRoot, mainDataDir) {
  const poa = canonical(poaRoot);
  const main = canonical(mainDataDir);
  if (isSameOrNested(poa, main) || isSameOrNested(main, poa)) {
    fail(
      `PoA root and main data dir must be disjoint (PoA=${poa}, main=${main}); ` +
        "a nested path could reuse node keys or the redb volume",
    );
  }
  return { poa, main };
}

function validatePort(value, name) {
  if (!Number.isInteger(value) || value < 1024 || value > 65535) {
    fail(`${name} must be an integer port in 1024..65535 (got ${value})`);
  }
}

function regularKeyFiles(root) {
  if (!existsSync(root)) return [];
  const found = [];
  const visit = (path) => {
    for (const entry of readdirSync(path, { withFileTypes: true })) {
      const child = join(path, entry.name);
      if (entry.isSymbolicLink()) continue;
      if (entry.isDirectory()) {
        visit(child);
      } else if (entry.isFile() && entry.name.endsWith(".key")) {
        found.push(child);
      }
    }
  };
  visit(root);
  return found.sort();
}

function keyDigests(root) {
  const byDigest = new Map();
  for (const path of regularKeyFiles(root)) {
    const stat = lstatSync(path);
    if (stat.size !== 32) continue;
    const digest = sha256File(path);
    const paths = byDigest.get(digest) ?? [];
    paths.push(path);
    byDigest.set(digest, paths);
  }
  return byDigest;
}

function requireHex32(value, label) {
  if (typeof value !== "string" || !HEX32.test(value)) {
    fail(`${label} must be 32 lowercase hex bytes`);
  }
  return value;
}

function parseGenesis(root) {
  const path = join(root, "bundle", "genesis.json");
  if (!existsSync(path)) fail(`missing authoritative descriptor: ${path}`);
  const genesis = readJson(path, "PoA genesis.json");
  requireHex32(genesis.federation_id, "genesis federation_id");
  if (!Array.isArray(genesis.validators) || genesis.validators.length === 0) {
    fail("genesis validators must be a non-empty array");
  }
  genesis.validators.forEach((validator, index) => {
    requireHex32(validator.public_key, `validators[${index}].public_key`);
  });
  if (!Number.isInteger(genesis.threshold) || genesis.threshold < 1) {
    fail("genesis threshold must be a positive integer");
  }
  if (genesis.deployment_domain !== POA_DEPLOYMENT_DOMAIN) {
    fail(
      `genesis deployment_domain must be ${POA_DEPLOYMENT_DOMAIN}; ` +
        "the public manifest cannot retrofit domain separation onto an unscoped genesis",
    );
  }
  if (!Array.isArray(genesis.initial_cells) || genesis.initial_cells.length !== 2) {
    fail("PoA genesis must contain only its deployment-local issuer and fee wells");
  }
  genesis.initial_cells.forEach((cell, index) => {
    requireHex32(cell.public_key, `initial_cells[${index}].public_key`);
    if (cell.balance !== 0) fail("PoA genesis must issue zero generic devnet value");
  });
  if (!Array.isArray(genesis.genesis_moves) || genesis.genesis_moves.length !== 0) {
    fail("PoA genesis must have no generic devnet genesis moves");
  }
  if (Array.isArray(genesis.starbridge_cells) && genesis.starbridge_cells.length !== 0) {
    fail("PoA genesis must not seed the generic Starbridge demo catalog");
  }
  if (existsSync(join(root, "bundle", "faucet.key"))) {
    fail("PoA empty-economy genesis must not emit a faucet key");
  }
  return { path, genesis };
}

function assertNotMainFederation(poaGenesis, mainDataDir) {
  const mainGenesisPath = join(mainDataDir, "genesis.json");
  if (!existsSync(mainGenesisPath)) return;
  const mainGenesis = readJson(mainGenesisPath, "main genesis.json");
  if (
    typeof mainGenesis.federation_id === "string" &&
    mainGenesis.federation_id === poaGenesis.federation_id
  ) {
    fail(
      `PoA federation_id ${poaGenesis.federation_id} equals the main federation; ` +
        "generate a fresh PoA genesis instead of copying the main descriptor",
    );
  }
  const poaAux = new Set(
    (poaGenesis.initial_cells ?? []).map((cell) => cell.public_key).filter(Boolean),
  );
  for (const cell of mainGenesis.initial_cells ?? []) {
    if (poaAux.has(cell.public_key)) {
      fail(
        `PoA auxiliary genesis identity ${cell.public_key} also appears in main genesis; ` +
          "issuer and fee-well identities must be deployment-scoped",
      );
    }
  }
}

function assertNoMainKeyReuse(poaRoot, mainDataDir) {
  const main = keyDigests(mainDataDir);
  if (main.size === 0) return;
  for (const [digest, poaPaths] of keyDigests(join(poaRoot, "bundle"))) {
    const mainPaths = main.get(digest);
    if (mainPaths) {
      fail(
        `PoA key reuse refused: ${poaPaths[0]} is byte-identical to ${mainPaths[0]}; ` +
          "validator, issuer, fee-well, and faucet identities must not cross deployments",
      );
    }
  }
}

function assertUniqueValidatorKeys(root, validators) {
  const seen = new Map();
  validators.forEach((validator, index) => {
    const bundleKeyPath = join(root, "bundle", `node-${index}.key`);
    const keyPath = join(root, "nodes", `node-${index}`, "node.key");
    if (!existsSync(bundleKeyPath)) fail(`missing bundle validator key: ${bundleKeyPath}`);
    if (!existsSync(keyPath)) fail(`missing validator key: ${keyPath}`);
    const bundleBytes = readFileSync(bundleKeyPath);
    const bytes = readFileSync(keyPath);
    if (bundleBytes.length !== 32) {
      fail(`${bundleKeyPath} must contain exactly one 32-byte Ed25519 seed`);
    }
    if (bytes.length !== 32) fail(`${keyPath} must contain exactly one 32-byte Ed25519 seed`);
    const digest = sha256Bytes(bundleBytes);
    const previous = seen.get(digest);
    if (previous) fail(`bundle validator key reuse refused: ${bundleKeyPath} equals ${previous}`);
    seen.set(digest, bundleKeyPath);
    if (!bundleBytes.equals(bytes)) {
      fail(`${keyPath} is not byte-identical to its authoritative ${bundleKeyPath}`);
    }

    const copiedGenesis = join(root, "nodes", `node-${index}`, "genesis.json");
    if (!existsSync(copiedGenesis)) fail(`missing pinned descriptor: ${copiedGenesis}`);
    if (sha256File(copiedGenesis) !== sha256File(join(root, "bundle", "genesis.json"))) {
      fail(`${copiedGenesis} is not byte-identical to the PoA federation descriptor`);
    }
    if (existsSync(join(root, "nodes", `node-${index}`, ".devnet"))) {
      fail(
        `${join(root, "nodes", `node-${index}`, ".devnet")} must not exist; ` +
          "that marker silently enables automatic Join approval",
      );
    }
  });
}

function normalizeHosts(hosts, validators) {
  const values = Array.isArray(hosts)
    ? hosts
    : typeof hosts === "string" && hosts.length > 0
      ? hosts.split(",")
      : Array.from({ length: validators }, () => "127.0.0.1");
  if (values.length !== validators) {
    fail(`hosts must contain exactly ${validators} entries (got ${values.length})`);
  }
  values.forEach((host, index) => {
    if (typeof host !== "string" || !/^[a-zA-Z0-9.-]+$/.test(host)) {
      fail(`hosts[${index}] must be a DNS name or IPv4 address without a port`);
    }
  });
  const distinct = new Set(values);
  const loopback = (host) => host === "localhost" || host === "127.0.0.1" || host.startsWith("127.");
  if (distinct.size > 1 && values.some(loopback)) {
    fail("a multi-host topology cannot advertise a loopback gossip address");
  }
  return values;
}

function peerList(hosts, gossipBase, self) {
  const validators = hosts.length;
  return Array.from({ length: validators }, (_, index) => index)
    .filter((index) => index !== self)
    .map((index) => `${hosts[index]}:${gossipBase + index}`);
}

export function buildManifest({
  root,
  mainDataDir,
  httpBase = 8421,
  gossipBase = 9421,
  hosts,
}) {
  if (!root || !mainDataDir) fail("root and mainDataDir are required");
  validatePort(httpBase, "httpBase");
  validatePort(gossipBase, "gossipBase");
  const roots = assertDisjointRoots(root, mainDataDir);
  const { path: genesisPath, genesis } = parseGenesis(roots.poa);
  const validators = genesis.validators.length;
  const advertisedHosts = normalizeHosts(hosts, validators);
  if (httpBase + validators - 1 > 65535 || gossipBase + validators - 1 > 65535) {
    fail("validator port range exceeds 65535");
  }
  const allPorts = new Set();
  for (let index = 0; index < validators; index += 1) {
    for (const port of [httpBase + index, gossipBase + index]) {
      if (allPorts.has(port)) fail(`HTTP and gossip port ranges overlap at ${port}`);
      allPorts.add(port);
    }
  }

  assertNotMainFederation(genesis, roots.main);
  assertNoMainKeyReuse(roots.poa, roots.main);
  assertUniqueValidatorKeys(roots.poa, genesis.validators);

  const genesisSha256 = sha256File(genesisPath);
  const deploymentId = sha256Bytes(
    Buffer.from(
      `${POA_DEPLOYMENT_DOMAIN}\0${genesis.federation_id}\0${genesisSha256}`,
      "utf8",
    ),
  );

  return {
    schema: POA_MANIFEST_SCHEMA,
    deployment_domain: POA_DEPLOYMENT_DOMAIN,
    deployment_id: deploymentId,
    federation_id: genesis.federation_id,
    committee_epoch: genesis.committee_epoch ?? 0,
    threshold: genesis.threshold,
    genesis_sha256: genesisSha256,
    descriptor: "bundle/genesis.json",
    policy: { ...POA_POLICY },
    nodes: genesis.validators.map((validator, index) => ({
      index,
      name: `node-${index}`,
      public_key: validator.public_key,
      data_dir: `nodes/node-${index}`,
      http: { bind: "127.0.0.1", port: httpBase + index },
      gossip: {
        advertised_host: advertisedHosts[index],
        port: gossipBase + index,
        peers: peerList(advertisedHosts, gossipBase, index),
      },
    })),
  };
}

function stableJson(value) {
  return `${JSON.stringify(value, null, 2)}\n`;
}

function writeAtomic(path, contents, mode = 0o644) {
  mkdirSync(dirname(path), { recursive: true });
  const temporary = `${path}.tmp-${process.pid}`;
  writeFileSync(temporary, contents, { mode });
  chmodSync(temporary, mode);
  renameSync(temporary, path);
}

function operatorConfig(root, manifest, node) {
  const dataDir = join(root, node.data_dir);
  if (/\r|\n/.test(dataDir)) fail("PoA root must not contain a newline");
  return [
    `POA_DEPLOYMENT_DOMAIN=${manifest.deployment_domain}`,
    `POA_DEPLOYMENT_ID=${manifest.deployment_id}`,
    `POA_FEDERATION_ID=${manifest.federation_id}`,
    `POA_NODE_INDEX=${node.index}`,
    `POA_DATA_DIR=${dataDir}`,
    `POA_HTTP_BIND=${node.http.bind}`,
    `POA_HTTP_PORT=${node.http.port}`,
    `POA_GOSSIP_PORT=${node.gossip.port}`,
    `POA_GOSSIP_HOST=${node.gossip.advertised_host}`,
    `POA_FEDERATION_PEERS=${node.gossip.peers.join(",")}`,
    "POA_PROVE_TURNS=1",
    "POA_ENABLE_FAUCET=0",
    "POA_AUTO_APPROVE_JOINS=0",
    "DREGG_REQUIRE_LEAN=1",
    "DREGG_STRAND_ADMISSION_GATE=1",
    "DREGG_ALLOW_UNVERIFIED_CONSENSUS=0",
    "DREGG_STATUS_EXPOSE_COUNTS=0",
    "DREGG_SEED_DEMO_LEASE=0",
    "",
  ].join("\n");
}

function assertNodePath(root, node, index) {
  const expected = `nodes/node-${index}`;
  if (node.data_dir !== expected) {
    fail(`public manifest node-${index} data_dir must be exactly ${expected}`);
  }
  const dataDir = join(root, expected);
  if (existsSync(dataDir) && !isSameOrNested(root, canonical(dataDir))) {
    fail(`${dataDir} escapes the PoA root through a filesystem link`);
  }
  return dataDir;
}

function assertOperatorConfigs(root, manifest, required) {
  manifest.nodes.forEach((node, index) => {
    const dataDir = assertNodePath(root, node, index);
    if (!required && !existsSync(dataDir)) return;
    const path = join(dataDir, "operator.env");
    if (!existsSync(path)) fail(`missing pinned operator config: ${path}`);
    const stat = lstatSync(path);
    if (!stat.isFile() || stat.isSymbolicLink()) fail(`${path} must be a regular file, not a link`);
    if ((stat.mode & 0o077) !== 0) fail(`${path} must not be readable or writable by group/other`);
    if (readFileSync(path, "utf8") !== operatorConfig(root, manifest, node)) {
      fail(`${path} does not exactly match the manifest-derived operator configuration`);
    }
  });
}

export function writeManifestAndConfigs(options) {
  const manifest = buildManifest(options);
  const root = canonical(options.root);
  writeAtomic(join(root, "poa-devnet.json"), stableJson(manifest));
  for (const node of manifest.nodes) {
    writeAtomic(join(root, node.data_dir, "operator.env"), operatorConfig(root, manifest, node), 0o600);
  }
  return manifest;
}

export function verifyManifest(options) {
  const root = canonical(options.root);
  const path = join(root, "poa-devnet.json");
  if (!existsSync(path)) fail(`missing PoA deployment manifest: ${path}`);
  const actual = readJson(path, "PoA deployment manifest");
  const expected = buildManifest(options);
  if (stableJson(actual) !== stableJson(expected)) {
    fail(
      "PoA deployment manifest does not match the pinned genesis, keys, paths, or ports; " +
        "refusing to run a partially reused deployment",
    );
  }
  assertOperatorConfigs(root, actual, true);
  return actual;
}

function assertPublicManifestShape(manifest, genesis) {
  if (manifest.descriptor !== "bundle/genesis.json") fail("public descriptor path is not canonical");
  if (manifest.threshold !== genesis.threshold) fail("public threshold does not match genesis");
  if (manifest.committee_epoch !== (genesis.committee_epoch ?? 0)) {
    fail("public committee epoch does not match genesis");
  }
  if (stableJson(manifest.policy) !== stableJson(POA_POLICY)) {
    fail("public manifest carries an unknown or weakened PoA operator policy");
  }

  const hosts = manifest.nodes.map((node) => node?.gossip?.advertised_host);
  normalizeHosts(hosts, genesis.validators.length);
  const httpBase = manifest.nodes[0]?.http?.port;
  const gossipBase = manifest.nodes[0]?.gossip?.port;
  validatePort(httpBase, "public http base");
  validatePort(gossipBase, "public gossip base");
  const allPorts = new Set();
  manifest.nodes.forEach((node, index) => {
    if (node.name !== `node-${index}`) fail(`public manifest node-${index} has a non-canonical name`);
    if (node.http?.bind !== "127.0.0.1" || node.http.port !== httpBase + index) {
      fail(`public manifest node-${index} has a non-canonical HTTP endpoint`);
    }
    if (node.gossip?.port !== gossipBase + index) {
      fail(`public manifest node-${index} has a non-canonical gossip port`);
    }
    const expectedPeers = peerList(hosts, gossipBase, index);
    if (stableJson(node.gossip?.peers) !== stableJson(expectedPeers)) {
      fail(`public manifest node-${index} peer set is not derived from the advertised mesh`);
    }
    for (const port of [node.http.port, node.gossip.port]) {
      if (allPorts.has(port)) fail(`public HTTP and gossip ports overlap at ${port}`);
      allPorts.add(port);
    }
  });
}

/** Verify the public follower package without requiring any validator seed. */
export function verifyPublicManifest(options) {
  const roots = assertDisjointRoots(options.root, options.mainDataDir);
  const path = join(roots.poa, "poa-devnet.json");
  if (!existsSync(path)) fail(`missing PoA deployment manifest: ${path}`);
  const manifest = readJson(path, "PoA deployment manifest");
  if (manifest.schema !== POA_MANIFEST_SCHEMA) fail("unknown PoA deployment manifest schema");
  if (manifest.deployment_domain !== POA_DEPLOYMENT_DOMAIN) {
    fail("public manifest has the wrong Path of Angels federation domain");
  }
  const { path: genesisPath, genesis } = parseGenesis(roots.poa);
  const digest = sha256File(genesisPath);
  if (manifest.genesis_sha256 !== digest || manifest.federation_id !== genesis.federation_id) {
    fail("public manifest does not pin this genesis.json");
  }
  const deploymentId = sha256Bytes(
    Buffer.from(`${POA_DEPLOYMENT_DOMAIN}\0${genesis.federation_id}\0${digest}`, "utf8"),
  );
  if (manifest.deployment_id !== deploymentId) fail("public deployment id does not re-derive");
  if (!Array.isArray(manifest.nodes) || manifest.nodes.length !== genesis.validators.length) {
    fail("public manifest committee size does not match genesis");
  }
  assertPublicManifestShape(manifest, genesis);
  manifest.nodes.forEach((node, index) => {
    if (node.public_key !== genesis.validators[index].public_key || node.index !== index) {
      fail(`public manifest node-${index} does not match the genesis committee`);
    }
    const dataDir = assertNodePath(roots.poa, node, index);
    const servedGenesis = join(dataDir, "genesis.json");
    if (existsSync(servedGenesis) && sha256File(servedGenesis) !== digest) {
      fail(`${servedGenesis} does not match the public manifest's genesis bytes`);
    }
  });
  assertNotMainFederation(genesis, roots.main);
  assertNoMainKeyReuse(roots.poa, roots.main);
  assertOperatorConfigs(roots.poa, manifest, false);
  return manifest;
}

function requireFollowerName(name) {
  if (typeof name !== "string" || !/^[a-zA-Z0-9][a-zA-Z0-9._-]{0,62}$/.test(name)) {
    fail("follower name must be 1..63 safe filename characters and begin with alphanumeric");
  }
  return name;
}

/**
 * Verify that a prospective follower is genuinely outside the genesis
 * committee while pinning the exact descriptor it will use to verify catch-up.
 */
export function verifyFollowerIsolation(options) {
  const manifest = verifyPublicManifest(options);
  const root = canonical(options.root);
  const main = canonical(options.mainDataDir);
  const name = requireFollowerName(options.name);
  const followerDir = join(root, "followers", name);
  const keyPath = join(followerDir, "node.key");
  const genesisPath = join(followerDir, "genesis.json");
  if (!existsSync(keyPath)) fail(`missing follower key: ${keyPath}`);
  if (readFileSync(keyPath).length !== 32) fail(`${keyPath} must be exactly 32 bytes`);
  if (!existsSync(genesisPath)) fail(`missing follower descriptor: ${genesisPath}`);
  if (sha256File(genesisPath) !== manifest.genesis_sha256) {
    fail("follower genesis.json does not match the manifest-pinned PoA descriptor");
  }
  if (existsSync(join(followerDir, ".devnet"))) {
    fail("follower .devnet marker refused: it would silently auto-approve other joiners");
  }

  const digest = sha256File(keyPath);
  const poaKeys = keyDigests(join(root, "bundle"));
  if (poaKeys.has(digest)) {
    fail(`follower key reuse refused: ${keyPath} equals ${poaKeys.get(digest)[0]}`);
  }
  const mainKeys = keyDigests(main);
  if (mainKeys.has(digest)) {
    fail(`follower key reuse refused: ${keyPath} equals ${mainKeys.get(digest)[0]}`);
  }
  return { manifest, followerDir, name };
}

function parseOptions(argv) {
  const options = {};
  for (let index = 0; index < argv.length; index += 1) {
    const flag = argv[index];
    const value = argv[index + 1];
    if (!flag.startsWith("--") || value === undefined) fail(`missing value for ${flag}`);
    index += 1;
    switch (flag) {
      case "--root":
        options.root = value;
        break;
      case "--main-data-dir":
        options.mainDataDir = value;
        break;
      case "--http-base":
        options.httpBase = Number(value);
        break;
      case "--gossip-base":
        options.gossipBase = Number(value);
        break;
      case "--name":
        options.name = value;
        break;
      case "--hosts":
        options.hosts = value;
        break;
      default:
        fail(`unknown option: ${flag}`);
    }
  }
  return options;
}

function usage() {
  process.stderr.write(
    "usage: poa-devnet-manifest.mjs {create|verify|verify-public|verify-follower} --root DIR " +
      "--main-data-dir DIR [--http-base N] [--gossip-base N] [--hosts CSV] [--name NAME]\n",
  );
}

async function main() {
  const [command, ...argv] = process.argv.slice(2);
  if (
    command !== "create" &&
    command !== "verify" &&
    command !== "verify-public" &&
    command !== "verify-follower"
  ) {
    usage();
    process.exitCode = 2;
    return;
  }
  const options = parseOptions(argv);
  const manifest =
    command === "create"
      ? writeManifestAndConfigs(options)
      : command === "verify"
        ? verifyManifest(options)
        : command === "verify-public"
          ? verifyPublicManifest(options)
          : verifyFollowerIsolation(options).manifest;
  process.stdout.write(
    `${command === "create" ? "created" : "verified"} PoA deployment ` +
      `${manifest.deployment_id} (federation ${manifest.federation_id})\n`,
  );
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error) => {
    process.stderr.write(`error: ${error.message}\n`);
    process.exitCode = 1;
  });
}
