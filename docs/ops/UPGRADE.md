# UPGRADE — safe redeploy of a new build

How to ship a new build of the node / bot / site without taking the chain
down. The native pipeline is git-ffwd + rebuild-on-box + systemd restart
(`deploy/aws/update.sh`); this runbook adds the discipline around it, and
`deploy/aws/update-gated.sh` mechanizes the discipline: **snapshot → update →
health-gate → auto-revert**.

## The normal path

```sh
ssh box
cd /opt/dregg
sudo -E deploy/aws/update-gated.sh          # snapshot, update.sh, gate, auto-revert
```

What it does (`deploy/aws/update-gated.sh`):
1. snapshots the running release (binaries + git rev) into
   `/opt/dregg-releases/<utc>/` (keeps last 5);
2. runs `deploy/aws/update.sh` (which refuses on a dirty tree, ffwd-merges
   `origin/main`, rebuilds, reinstalls units, restarts — its knobs
   `GATEWAY_ONLY=1` / `SKIP_SITE=1` pass straight through);
3. polls the gateway `/health` and every active `dregg-node@N` member's port
   (from `/etc/dregg/node-N.env`) for up to `HEALTH_TIMEOUT` (120s default);
4. on a failed gate, restores the snapshot binaries, restarts, and re-gates —
   the box ends healthy on the release that worked.

Manual controls: `update-gated.sh releases` (list), `update-gated.sh
rollback [stamp]` (revert now), `update-gated.sh health` (just the gate),
`AUTO_REVERT=0` (gate but never revert automatically).

## Rules of the road

- **State is sacred.** Neither script ever writes `/opt/dregg-data*` — a
  redeploy keeps chain state; wiping is an explicit operator act
  ([DISASTER-RECOVERY.md](DISASTER-RECOVERY.md) §B, backup first).
- **One member at a time.** With an n=3 committee (threshold 3, f=0), a
  restart is a finality pause — keep it short and never overlap two members.
  Restart order: members first (`dregg-node@2`, then `@3`, gate between),
  gateway last. `GATEWAY_ONLY=1` exists for the reverse case.
- **Rollback restores binaries, not the repo.** After an auto-revert the repo
  in `/opt/dregg` is still at the new rev; the deployed binaries are the
  snapshot's. `git -C /opt/dregg log $(cat /opt/dregg-releases/<S>/GIT_REV)..HEAD`
  is exactly the deployed-but-reverted diff. Fix forward or reset — an
  explicit decision either way.
- **Protocol-semantics bumps get staged.** A change to VK / commitment /
  wire formats can make preserved state unloadable or split consensus
  between old and new members. Stage it: upgrade ONE federation member,
  watch `/status` convergence + `dregg_consensus_attested_total` +
  `ConsensusDivergence` for a full epoch of real traffic, then roll the
  rest. If the staged member diverges, binary-rollback that one member —
  the quorum never moved.
- **Watch the gate's blind spots.** `/health` says "up and consensus live";
  it does not say "the bot answered" or "the site deployed." After a full
  (non-`GATEWAY_ONLY`) update, `update.sh` already runs the bot preflight;
  eyeball the Discord bot's `/status` output and the site once.

## After every upgrade

```sh
curl -s http://127.0.0.1:8420/status | jq '{healthy, consensus_live, dag_height, peer_count}'
# and the tripwire that must still read 0:
curl -s http://127.0.0.1:8420/metrics | grep divergence_total
```
