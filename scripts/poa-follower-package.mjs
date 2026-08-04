#!/usr/bin/env node

/**
 * Verify a key-free Path of Angels follower package and its live status.
 *
 * The deployment descriptor remains authoritative for chain identity.  The
 * release lock adds immutable source, Linux binary and portable OCI-image pins;
 * it never contains a validator seed or makes committee admission trustless.
 */

import { createHash } from "node:crypto";
import {
  existsSync,
  readFileSync,
  readdirSync,
  realpathSync,
  statSync,
} from "node:fs";
import { isAbsolute, join, relative, resolve, sep } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

import {
  POA_DEPLOYMENT_DOMAIN,
  verifyPublicManifest,
} from "./poa-devnet-manifest.mjs";

export const FOLLOWER_PACKAGE_SCHEMA = "pathofangels-follower-package-v1";
const RELEASE_RECEIPT_SCHEMA = "pathofangels-release-receipt-v2";
const HEX32 = /^[0-9a-f]{64}$/;
const GIT_ID = /^(?:[0-9a-f]{40}|[0-9a-f]{64})$/;
const LOCKED_FILES = [
  "poa-devnet.json",
  "bundle/genesis.json",
  "release-receipt.json",
  "image-identity.mjs",
];

function fail(message) {
  throw new Error(message);
}

function readJson(path, label) {
  try {
    return JSON.parse(readFileSync(path, "utf8"));
  } catch (error) {
    fail(`${label} is not valid JSON: ${error.message}`);
  }
}

function sha256(path) {
  return createHash("sha256").update(readFileSync(path)).digest("hex");
}

function requireHex32(value, label) {
  if (typeof value !== "string" || !HEX32.test(value)) fail(`${label} must be 64 lowercase hex`);
  return value;
}

function canonical(path) {
  return existsSync(path) ? realpathSync(path) : resolve(path);
}

function isNested(root, path) {
  const rel = relative(root, path);
  return rel === "" || (!isAbsolute(rel) && rel !== ".." && !rel.startsWith(`..${sep}`));
}

function safeRelative(path) {
  return (
    typeof path === "string" &&
    path.length > 0 &&
    !isAbsolute(path) &&
    !path.split("/").some((part) => part === "" || part === "." || part === "..")
  );
}

function walk(root) {
  const out = [];
  const visit = (dir) => {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      const path = join(dir, entry.name);
      const rel = relative(root, path).split(sep).join("/");
      if (entry.isSymbolicLink()) fail(`follower package contains a symbolic link: ${rel}`);
      if (entry.isDirectory()) visit(path);
      else if (entry.isFile()) out.push(rel);
      else fail(`follower package contains a non-file object: ${rel}`);
    }
  };
  visit(root);
  return out.sort();
}

function assertPublicOnlyPaths(root, pristine) {
  const allowed = new Set([...LOCKED_FILES, "release-lock.json"]);
  for (const path of walk(root)) {
    if (allowed.has(path)) continue;
    if (!pristine && /^followers\/[a-zA-Z0-9][a-zA-Z0-9._-]{0,62}\//.test(path)) continue;
    fail(`public follower package contains an unreceipted or private path: ${path}`);
  }
}

function exactBootstrapPeers(manifest) {
  return manifest.nodes.map((node) => `${node.gossip.advertised_host}:${node.gossip.port}`);
}

function assertExactArray(actual, expected, label) {
  if (
    !Array.isArray(actual) ||
    actual.length !== expected.length ||
    actual.some((value, index) => value !== expected[index])
  ) {
    fail(`${label} does not match the deployment-derived value`);
  }
}

export function verifyFollowerPackage({
  root,
  mainDataDir,
  binary,
  imageInspect,
  pristine = false,
}) {
  if (!root || !mainDataDir) fail("root and mainDataDir are required");
  const packageRoot = canonical(root);
  const lockPath = join(packageRoot, "release-lock.json");
  if (!existsSync(lockPath)) fail(`public follower package lacks release-lock.json: ${lockPath}`);
  assertPublicOnlyPaths(packageRoot, pristine);

  const manifest = verifyPublicManifest({ root: packageRoot, mainDataDir });
  const lock = readJson(lockPath, "follower release lock");
  const receiptPath = join(packageRoot, "release-receipt.json");
  const receipt = readJson(receiptPath, "PoA release receipt");
  if (lock.schema !== FOLLOWER_PACKAGE_SCHEMA) fail("unknown follower package schema");
  if (receipt.schema !== RELEASE_RECEIPT_SCHEMA) fail("unknown PoA release receipt schema");
  if (!Number.isSafeInteger(lock.epoch) || lock.epoch < 1) fail("follower package epoch is invalid");
  if (!Number.isSafeInteger(receipt.content_epoch) || receipt.content_epoch < 1) {
    fail("PoA release receipt content epoch is invalid");
  }
  if (lock.epoch !== receipt.content_epoch) {
    fail("follower package epoch differs from release receipt content epoch");
  }

  const identity = {
    domain: manifest.deployment_domain,
    federation_id: manifest.federation_id,
    deployment_id: manifest.deployment_id,
    genesis_sha256: manifest.genesis_sha256,
  };
  if (identity.domain !== POA_DEPLOYMENT_DOMAIN) fail("follower package uses the wrong deployment domain");
  for (const [field, expected] of Object.entries(identity)) {
    if (lock.deployment?.[field] !== expected) fail(`release lock ${field} differs from deployment`);
  }
  if (
    receipt.deployment_domain !== identity.domain ||
    receipt.federation_id !== identity.federation_id ||
    receipt.deployment_id !== identity.deployment_id ||
    receipt.genesis_sha256 !== identity.genesis_sha256
  ) {
    fail("release receipt identifies a different federation or genesis");
  }

  assertExactArray(
    lock.files?.map((entry) => entry?.path),
    LOCKED_FILES,
    "release lock file set",
  );
  for (const entry of lock.files) {
    if (!safeRelative(entry.path)) fail(`unsafe release-lock path: ${entry.path}`);
    const path = canonical(join(packageRoot, entry.path));
    if (!isNested(packageRoot, path)) fail(`release-lock path escapes package: ${entry.path}`);
    if (!existsSync(path) || !statSync(path).isFile()) fail(`missing locked artifact: ${entry.path}`);
    requireHex32(entry.sha256, `${entry.path} SHA-256`);
    if (sha256(path) !== entry.sha256) fail(`locked artifact digest mismatch: ${entry.path}`);
  }

  const release = lock.release ?? {};
  requireHex32(release.receipt_sha256, "release receipt SHA-256");
  requireHex32(release.linux_gate_receipt_sha256, "Linux gate receipt SHA-256");
  requireHex32(release.node_sha256, "node SHA-256");
  requireHex32(release.source_tree_sha256, "source tree SHA-256");
  requireHex32(release.image_portable_sha256, "portable image SHA-256");
  requireHex32(release.image_identity_tool_sha256, "image identity tool SHA-256");
  if (!GIT_ID.test(release.source_commit ?? "")) fail("source commit is not a Git object id");
  if (!/^sha256:[0-9a-f]{64}$/.test(release.runtime_base_id ?? "")) {
    fail("runtime base id is not an immutable image id");
  }
  if (sha256(receiptPath) !== release.receipt_sha256) fail("release receipt bytes drifted");
  const receiptPairs = [
    ["linux_gate_receipt_sha256", "linux_gate_receipt_sha256"],
    ["node_sha256", "node_sha256"],
    ["source_commit", "source_commit"],
    ["source_tree_sha256", "source_tree_sha256"],
    ["image_reference", "candidate_image"],
    ["image_portable_sha256", "candidate_image_portable_sha256"],
    ["image_identity_tool_sha256", "candidate_image_identity_tool_sha256"],
    ["runtime_base_id", "runtime_base_id"],
  ];
  for (const [lockField, receiptField] of receiptPairs) {
    if (release[lockField] !== receipt[receiptField]) {
      fail(`release lock ${lockField} differs from release receipt`);
    }
  }
  if (
    receipt.proposal_neutral_follow !== undefined &&
    typeof receipt.proposal_neutral_follow !== "boolean"
  ) {
    fail("release receipt proposal_neutral_follow capability is not boolean");
  }
  const receiptedProposalNeutralFollow = receipt.proposal_neutral_follow === true;
  if (release.proposal_neutral_follow !== receiptedProposalNeutralFollow) {
    fail("release lock proposal_neutral_follow differs from release receipt");
  }

  assertExactArray(lock.bootstrap_peers, exactBootstrapPeers(manifest), "bootstrap peer set");
  const boundary = lock.trust_boundary ?? {};
  if (
    boundary.history_verification_from_pinned_genesis !== "cryptographic" ||
    boundary.release_provenance !== "receipt-and-repository-pin" ||
    boundary.admission !== "committee-ratified-manual-v1" ||
    boundary.objective_f4_admission_live !== false
  ) {
    fail("follower package overstates or changes the current trust boundary");
  }

  if (binary) {
    const path = canonical(binary);
    if (!existsSync(path) || !statSync(path).isFile()) fail(`release binary is missing: ${binary}`);
    if (sha256(path) !== release.node_sha256) fail("release binary SHA-256 differs from release lock");
  }
  if (imageInspect) {
    const tool = join(packageRoot, "image-identity.mjs");
    if (sha256(tool) !== release.image_identity_tool_sha256) fail("image identity verifier drifted");
    const result = spawnSync(process.execPath, [tool], {
      input: readFileSync(imageInspect),
      encoding: "utf8",
    });
    if (result.status !== 0) fail(`portable image verification failed: ${result.stderr.trim()}`);
    if (result.stdout.trim() !== release.image_portable_sha256) {
      fail("container image portable SHA-256 differs from release lock");
    }
  }
  return { manifest, lock, receipt };
}

function assertHexKey(value, label) {
  return requireHex32(value, label);
}

export function verifyFollowerStatus({
  manifest,
  release,
  status,
  membership,
  followerPublicKey,
  requireReady = false,
}) {
  const key = assertHexKey(followerPublicKey, "follower public key");
  if (membership?.federation_id !== manifest.federation_id) {
    fail("live follower reports the wrong federation_id");
  }
  if (status?.public_key !== key || membership?.self?.key !== key) {
    fail("live status/membership identity differs from the local follower key");
  }
  if (status.federation_mode !== "full") fail("follower is not running full consensus verification");
  if (status.lean_producer !== true || status.state_producer !== "lean") {
    fail("follower is not using the Lean state producer");
  }
  if (status.full_turn_proving !== true) fail("follower full-turn proving is disabled");
  if (Object.hasOwn(status, "note_count") || Object.hasOwn(status, "revocation_count")) {
    fail("follower exposes private activity counts");
  }
  if (!Array.isArray(membership.participants) || membership.participants.length === 0) {
    fail("membership response has no committee");
  }
  const participants = membership.participants.map((value, index) =>
    assertHexKey(value, `participants[${index}]`),
  );
  if (new Set(participants).size !== participants.length) fail("membership committee contains duplicates");
  if (!Number.isSafeInteger(membership.threshold) || membership.threshold < 1) {
    fail("membership threshold is invalid");
  }
  if (membership.self.participant !== participants.includes(key)) {
    fail("membership self.participant disagrees with the committee list");
  }

  const proposals = Array.isArray(membership.proposals) ? membership.proposals : [];
  const joinProposal = proposals.find((proposal) => proposal?.kind === "join" && proposal.node === key);
  const checks = {
    healthy: status.healthy === true,
    consensus_live: status.consensus_live === true,
    peer_connected: Number.isSafeInteger(status.peer_count) && status.peer_count >= 1,
    history_present:
      Number.isSafeInteger(status.block_count) && status.block_count >= 1 &&
      Number.isSafeInteger(status.dag_height) && status.dag_height >= 1,
    proposal_neutral_follow_supported: release?.proposal_neutral_follow === true,
    no_unratified_self_join: membership.self.participant === true || !joinProposal,
  };
  const ready = Object.values(checks).every(Boolean);
  if (requireReady && !ready) {
    const failed = Object.entries(checks).filter(([, ok]) => !ok).map(([name]) => name);
    fail(`follower is not verification-ready: ${failed.join(", ")}`);
  }
  return {
    ready,
    participant: membership.self.participant,
    proposal_neutral_follow: release?.proposal_neutral_follow === true,
    proposal_block: joinProposal?.proposal_block ?? null,
    federation_id: manifest.federation_id,
    admission: "committee-ratified-manual-v1",
    objective_f4_admission_live: false,
    checks,
  };
}

function parseOptions(argv) {
  const out = {};
  for (let index = 0; index < argv.length; index += 2) {
    const flag = argv[index];
    const value = argv[index + 1];
    if (!flag?.startsWith("--") || value === undefined) fail(`missing value for ${flag ?? "option"}`);
    out[flag.slice(2).replaceAll("-", "_")] = value;
  }
  return out;
}

function bool(value) {
  if (value === undefined) return false;
  if (value === "true" || value === "1") return true;
  if (value === "false" || value === "0") return false;
  fail(`invalid boolean: ${value}`);
}

async function main() {
  const [command, ...argv] = process.argv.slice(2);
  const options = parseOptions(argv);
  if (command === "verify") {
    const result = verifyFollowerPackage({
      root: options.root,
      mainDataDir: options.main_data_dir,
      binary: options.binary,
      imageInspect: options.image_inspect,
      pristine: bool(options.pristine),
    });
    process.stdout.write(
      `verified key-free PoA follower package epoch=${result.lock.epoch} ` +
        `federation=${result.manifest.federation_id} ` +
        `proposal_neutral_follow=${result.lock.release.proposal_neutral_follow}\n`,
    );
    return;
  }
  if (command === "status") {
    const packageResult = verifyFollowerPackage({
      root: options.root,
      mainDataDir: options.main_data_dir,
      binary: options.binary,
    });
    const report = verifyFollowerStatus({
      manifest: packageResult.manifest,
      release: packageResult.lock.release,
      status: readJson(options.status_json, "follower /status"),
      membership: readJson(options.membership_json, "follower /api/membership"),
      followerPublicKey: options.follower_public_key,
      requireReady: bool(options.require_ready),
    });
    process.stdout.write(`${JSON.stringify(report)}\n`);
    return;
  }
  process.stderr.write(
    "usage: poa-follower-package.mjs verify --root DIR --main-data-dir DIR " +
      "[--binary FILE] [--image-inspect JSON] [--pristine true] | " +
      "status --root DIR --main-data-dir DIR --status-json FILE --membership-json FILE " +
      "--follower-public-key HEX [--binary FILE] [--require-ready true]\n",
  );
  process.exitCode = 2;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error) => {
    process.stderr.write(`error: ${error.message}\n`);
    process.exitCode = 1;
  });
}
