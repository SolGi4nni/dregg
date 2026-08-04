import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import {
  chmodSync,
  cpSync,
  mkdtempSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import test from "node:test";

import {
  verifyFollowerPackage,
  verifyFollowerStatus,
} from "../poa-follower-package.mjs";

const checkedPackage = join(process.cwd(), "poa", "deployments", "epoch-1");
const followerKey = "aa".repeat(32);

function fixture() {
  const scratch = mkdtempSync(join(tmpdir(), "poa-follower-package-test-"));
  const root = join(scratch, "epoch-1");
  const mainDataDir = join(scratch, "main");
  cpSync(checkedPackage, root, { recursive: true });
  mkdirSync(mainDataDir);
  return { scratch, root, mainDataDir };
}

function readJson(path) {
  return JSON.parse(readFileSync(path, "utf8"));
}

function writeJson(path, value) {
  writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`);
}

function sha256(path) {
  return createHash("sha256").update(readFileSync(path)).digest("hex");
}

function bindFixtureToBinary(root, binary, { proposalNeutralFollow = true } = {}) {
  const receiptPath = join(root, "release-receipt.json");
  const lockPath = join(root, "release-lock.json");
  const receipt = readJson(receiptPath);
  const lock = readJson(lockPath);
  receipt.node_sha256 = sha256(binary);
  receipt.proposal_neutral_follow = proposalNeutralFollow;
  writeJson(receiptPath, receipt);
  lock.release.node_sha256 = receipt.node_sha256;
  lock.release.proposal_neutral_follow = proposalNeutralFollow;
  lock.release.receipt_sha256 = sha256(receiptPath);
  const entry = lock.files.find((item) => item.path === "release-receipt.json");
  entry.sha256 = lock.release.receipt_sha256;
  writeJson(lockPath, lock);
}

function liveFixture() {
  const manifest = readJson(join(checkedPackage, "poa-devnet.json"));
  const participants = manifest.nodes.map((node) => node.public_key);
  return {
    manifest,
    release: { proposal_neutral_follow: true },
    status: {
      healthy: true,
      peer_count: 2,
      dag_height: 14,
      block_count: 41,
      consensus_live: true,
      federation_mode: "full",
      public_key: followerKey,
      state_producer: "lean",
      lean_producer: true,
      full_turn_proving: true,
    },
    membership: {
      federation_id: manifest.federation_id,
      participants,
      threshold: 3,
      self: { key: followerKey, participant: false },
      proposals: [],
    },
  };
}

test("checked epoch-1 package is key-free and pins the live release", () => {
  const f = fixture();
  const result = verifyFollowerPackage({ ...f, pristine: true });
  assert.equal(
    result.manifest.federation_id,
    "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a",
  );
  assert.equal(
    result.manifest.deployment_id,
    "d933b11beb5adb502cc0511b8124c98192dbbed143ffbb1b5242ff6e0cf97c9e",
  );
  assert.equal(
    result.manifest.genesis_sha256,
    "5766736201a9ede62c79fe9beac04df8f8b5367feec5400c073fd631132bdb7f",
  );
  assert.equal(
    result.lock.release.node_sha256,
    "a9858c0298fa5517ef9d845566f59258c3e39404571a6b1bca77990b9b9bfb9f",
  );
  assert.equal(
    result.lock.release.source_tree_sha256,
    "7961b05444934754bf5d7f7347069470691c651b7215ef4ab8bc2eb1e96a21af",
  );
  assert.equal(
    result.lock.release.image_portable_sha256,
    "2a68d175de50c74f6c5035719a4970f68cbb6e66d53128ea53f6ca8c590996cd",
  );
  assert.equal(result.lock.release.proposal_neutral_follow, false);
  assert.equal(result.lock.release.node_sha256, result.receipt.node_sha256);
  assert.equal(result.lock.release.source_tree_sha256, result.receipt.source_tree_sha256);
  assert.equal(
    result.lock.release.image_portable_sha256,
    result.receipt.candidate_image_portable_sha256,
  );
  const files = readdirSync(join(f.root, "bundle"));
  assert.deepEqual(files, ["genesis.json"]);
});

test("wrong-federation package is refused against the exact genesis", () => {
  const f = fixture();
  const path = join(f.root, "poa-devnet.json");
  const manifest = readJson(path);
  manifest.federation_id = "ff".repeat(32);
  writeJson(path, manifest);
  assert.throws(
    () => verifyFollowerPackage({ ...f, pristine: true }),
    /does not pin this genesis|digest mismatch|different federation/,
  );
});

test("a validator seed smuggled into the public package is refused", () => {
  const f = fixture();
  writeFileSync(join(f.root, "bundle", "node-0.key"), Buffer.alloc(32, 7));
  assert.throws(
    () => verifyFollowerPackage({ ...f, pristine: true }),
    /unreceipted or private path: bundle\/node-0\.key/,
  );
});

test("wrong release binary is refused before a follower can execute it", () => {
  const f = fixture();
  const binary = join(f.scratch, "dregg-node");
  writeFileSync(binary, "not the released Lean-linked node\n", { mode: 0o755 });
  assert.throws(
    () => verifyFollowerPackage({ ...f, binary }),
    /release binary SHA-256 differs/,
  );
});

test("wrong OCI image semantics are refused by the pinned identity tool", () => {
  const f = fixture();
  const inspect = join(f.scratch, "inspect.json");
  writeJson(inspect, [
    {
      Created: "2026-08-04T00:00:00Z",
      Architecture: "amd64",
      Os: "linux",
      Config: {
        User: "dreggnode",
        Env: ["DREGG_REQUIRE_LEAN=0"],
        Entrypoint: ["/usr/local/bin/dregg-node"],
        Labels: {},
      },
      RootFS: { Type: "layers", Layers: [`sha256:${"1".repeat(64)}`] },
    },
  ]);
  assert.throws(
    () => verifyFollowerPackage({ ...f, imageInspect: inspect }),
    /container image portable SHA-256 differs/,
  );
});

test("source provenance drift is refused against the release receipt", () => {
  const f = fixture();
  const path = join(f.root, "release-lock.json");
  const lock = readJson(path);
  lock.release.source_tree_sha256 = "00".repeat(32);
  writeJson(path, lock);
  assert.throws(
    () => verifyFollowerPackage({ ...f }),
    /source_tree_sha256 differs from release receipt/,
  );
});

test("package epoch is bound to the signed-off release content epoch", () => {
  const f = fixture();
  const path = join(f.root, "release-lock.json");
  const lock = readJson(path);
  lock.epoch += 1;
  writeFileSync(path, `${JSON.stringify(lock, null, 2)}\n`);
  assert.throws(
    () => verifyFollowerPackage({ root: f.root, mainDataDir: f.mainDataDir }),
    /package epoch differs from release receipt content epoch/,
  );
});

test("a lock cannot claim proposal-neutral follow for an old receipted binary", () => {
  const f = fixture();
  const path = join(f.root, "release-lock.json");
  const lock = readJson(path);
  lock.release.proposal_neutral_follow = true;
  writeJson(path, lock);
  assert.throws(
    () => verifyFollowerPackage({ root: f.root, mainDataDir: f.mainDataDir }),
    /proposal_neutral_follow differs from release receipt/,
  );
});

test("epoch-1 follower readiness refuses before network traffic", () => {
  const f = fixture();
  const binary = join(f.scratch, "dregg-node");
  writeFileSync(binary, "#!/bin/sh\nexit 97\n");
  chmodSync(binary, 0o755);
  bindFixtureToBinary(f.root, binary, { proposalNeutralFollow: false });
  const result = spawnSync(
    "bash",
    [join(process.cwd(), "scripts", "poa-devnet.sh"), "follower-readiness", "deck-447"],
    {
      encoding: "utf8",
      env: {
        ...process.env,
        POA_ROOT: f.root,
        POA_MAIN_DATA_DIR: f.mainDataDir,
        POA_BIN: binary,
      },
    },
  );
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /pinned PoA release lacks proposal-neutral follow support/);
});

test("synced proposal-neutral non-voter is verification-ready but admission remains manual", () => {
  const live = liveFixture();
  const report = verifyFollowerStatus({
    ...live,
    followerPublicKey: followerKey,
    requireReady: true,
  });
  assert.equal(report.ready, true);
  assert.equal(report.participant, false);
  assert.equal(report.admission, "committee-ratified-manual-v1");
  assert.equal(report.objective_f4_admission_live, false);
  assert.equal(report.proposal_neutral_follow, true);
  assert.equal(report.proposal_block, null);
});

test("live wrong-federation response is refused", () => {
  const live = liveFixture();
  live.membership.federation_id = "ff".repeat(32);
  assert.throws(
    () => verifyFollowerStatus({ ...live, followerPublicKey: followerKey }),
    /wrong federation_id/,
  );
});

test("live identity that differs from the local follower key is refused", () => {
  const live = liveFixture();
  live.membership.self.key = "cc".repeat(32);
  assert.throws(
    () => verifyFollowerStatus({ ...live, followerPublicKey: followerKey }),
    /differs from the local follower key/,
  );
});

test("a follow-only non-member that authored a Join proposal is not readiness-green", () => {
  const live = liveFixture();
  live.membership.proposals = [{
    proposal_block: "bb".repeat(32),
    kind: "join",
    node: followerKey,
    approvals: 0,
    required: 3,
    applied: false,
  }];
  assert.throws(
    () =>
      verifyFollowerStatus({
        ...live,
        followerPublicKey: followerKey,
        requireReady: true,
      }),
    /no_unratified_self_join/,
  );
});

test("release-locked shell flow spools a follower and refuses an unpinned bootstrap", () => {
  const f = fixture();
  const binary = join(f.scratch, "dregg-node");
  writeFileSync(
    binary,
    `#!/bin/sh
if [ "$1" = gen-validator-key ]; then
  shift
  data_dir=
  while [ "$#" -gt 0 ]; do
    if [ "$1" = --data-dir ]; then data_dir="$2"; shift 2; else shift; fi
  done
  if [ ! -f "$data_dir/node.key" ]; then dd if=/dev/zero of="$data_dir/node.key" bs=32 count=1 2>/dev/null; fi
  printf '{"public_key":"${followerKey}"}'
  exit 0
fi
exit 99
`,
  );
  chmodSync(binary, 0o755);
  bindFixtureToBinary(f.root, binary);
  const script = join(process.cwd(), "scripts", "poa-devnet.sh");
  const env = {
    ...process.env,
    POA_ROOT: f.root,
    POA_MAIN_DATA_DIR: f.mainDataDir,
    POA_BIN: binary,
  };
  const verified = spawnSync("bash", [script, "package-verify"], { encoding: "utf8", env });
  assert.equal(verified.status, 0, verified.stderr);

  const initialized = spawnSync("bash", [script, "follower-init", "deck-447"], {
    encoding: "utf8",
    env,
  });
  assert.equal(initialized.status, 0, initialized.stderr);

  const command = spawnSync(
    "bash",
    [script, "follower-command", "deck-447", "100.64.0.3:9423", "100.70.0.44"],
    { encoding: "utf8", env },
  );
  assert.equal(command.status, 0, command.stderr);
  assert.match(command.stdout, /join --follow-only --bootstrap 100\.64\.0\.3:9423/);
  assert.match(command.stdout, /^DREGG_REQUIRE_LEAN=1/);

  const hostile = spawnSync(
    "bash",
    [script, "follower-command", "deck-447", "evil.invalid:9423", "100.70.0.44"],
    { encoding: "utf8", env },
  );
  assert.notEqual(hostile.status, 0);
  assert.match(hostile.stderr, /not pinned by the follower release lock|unrecognized follower bootstrap/);
});
