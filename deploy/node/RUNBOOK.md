# deploy/node — the durable hbox devnet node (RUNBOOK)

Stand up the solo `dregg-node` on **hbox** as a systemd **user** unit with a
**persistent** data dir and **linger**, so it survives logout and reboot. This is
**TODO-1** in [`deploy/README.md`](../README.md) and the fix for the incident in
[`deploy/PRACTICES.md`](../PRACTICES.md) §2 — the previous `:8420` node was
hand-run with an ephemeral `--data-dir`, the box was hard-killed by build load,
and **the devnet ledger was permanently lost**. Everything here is the durable
form of the launch already documented in
[`docs/ops/PRIVATE-NODE.md`](../../docs/ops/PRIVATE-NODE.md) and
[`scripts/private-node.sh`](../../scripts/private-node.sh).

**Artifacts this runbook installs**
- Unit: [`deploy/node/dregg-node.service`](dregg-node.service) — user unit, solo
  faucet node, `--prove-turns`, bound `127.0.0.1:8420`, `--data-dir
  %h/.local/state/dregg-node`, `Restart=on-failure`.
- Binary: `~/dev/breadstuffs/target/release/dregg-node`, **built on hbox**
  linking the host-native Lean executor archive.

**Scope (honest).** A SOLO committee-of-one devnet faucet node over the verified
Lean executor, bound to **loopback**. NOT the multi-node federation, NOT an
on-chain settle, NOT a public surface. The node is **never funneled** and
**never binds `0.0.0.0`**. The games' public path is Tailscale Funnel in front of
the *web* unit ([`deploy/games/RUNBOOK-FUNNEL.md`](../games/RUNBOOK-FUNNEL.md)),
not this node.

---

## ⚠ Two hard facts to respect before you touch a box

1. **Never route this through a "gateway-Caddy-over-tailnet" plan.** The edge
   (`100.64.0.x`) and hbox (`skunk-emperor.ts.net`) are on **two tailnets that
   cannot reach each other** ([`deploy/README.md`](../README.md) §"There are TWO
   tailnets"). The only verified public path is `tailscale funnel` on hbox. This
   node stays loopback; nothing here needs cross-tailnet reach.
2. **This node runs a prover; hbox is co-tenant.** `--prove-turns` spawns an
   async STARK prove-pool. Per [`deploy/PRACTICES.md`](../PRACTICES.md) §1 the
   prover is the thing that gets capped — that is why the unit has
   `CPUQuota`/`MemoryMax`. Do not remove those caps on this box.

---

## What is executable-on-hbox-today vs needs-the-box-to-verify

| Step | Status |
|---|---|
| (1) build the Lean-linked node on hbox | **executable on hbox today** (recipe verified in PRIVATE-NODE.md, 2026-07-13) |
| (2) install the user unit + enable-linger | **executable on hbox today** |
| (3) first-boot data-dir init | **executable on hbox today** (unit's `ExecStartPre` does it; or run `init` by hand) |
| (4) start + health-check | **executable on hbox today** |
| (5) simulated-restart durability check | **needs the box to verify** (must run ON hbox; a `systemctl --user restart` + reboot-linger check) |
| (6) re-point the games funnel at it | **executable on hbox today** (steps a.2/a.3 of RUNBOOK-FUNNEL.md against the now-durable node) |

Every command below is run **on hbox** (`ssh hbox`) as the login user unless
marked otherwise. `%h` in the unit = that user's `$HOME` (e.g. `/home/hbox`).

---

## (1) Build the Lean-linked node on hbox  ⟨executable on hbox today⟩

The unit's `ExecStart` is `%h/dev/breadstuffs/target/release/dregg-node`. That
binary links `libdregg_lean.a`, the **Linux-native** archive of the compiled Lean
kernel — it is **not committed** and **cannot be cross-compiled** from macOS (a
Mach-O seed will not link). Build it **on hbox** in `~/dev/breadstuffs` (the tree
`dregg-web-games-funnel.service` already runs from), reusing the box's warm
`.lake`:

```bash
# on hbox
cd ~/dev/breadstuffs
# 1a. build the HEAD Dregg2 :c facets (the executor FFI roots)
cd metatheory
lake build Dregg2.Exec.FFI Dregg2.Exec.DistributedExports Dregg2.Exec.FFIDirect
cd ..
# 1b. seed the ELF archive (leanc → ELF objects → GNU archive libdregg_lean.a)
dregg-lean-ffi/scripts/seed-dregg2-closure.sh
# 1c. build the node against it (fail loud if Lean is missing)
SR="$(cd metatheory && lake env printenv LEAN_SYSROOT)"
DREGG_LEAN_SYSROOT="$SR" DREGG_REQUIRE_LEAN=1 \
  cargo build --release -p dregg-node
```

Heavy builds on hbox go through `swarm-build` (the MemoryMax cgroup —
[`deploy/PRACTICES.md`](../PRACTICES.md) / global practice); the `cargo build`
above is the one line to wrap if the box is busy:
`swarm-build cargo build --release -p dregg-node`.

**Verify the verified executor is linked in** (`> 0` = the proved Lean executor
is spliced, not the marshal-only tripwire):

```bash
nm ~/dev/breadstuffs/target/release/dregg-node | grep -c dregg_exec_full_forest_auth
```

> If you build in the alternate lane `~/dregg-build/privnode` (the path
> PRIVATE-NODE.md uses), either build in `~/dev/breadstuffs` as above, or copy the
> binary to where the unit expects it:
> `cp ~/dregg-build/privnode/target/release/dregg-node ~/dev/breadstuffs/target/release/`.
> The unit's `ExecStart` path is fixed (systemd does not expand env vars in the
> executable path); the binary must be at
> `~/dev/breadstuffs/target/release/dregg-node`.

Full recipe + fail-loud guards: `docs/BUILD-LEAN-LINKED-NODE.md`,
`docs/ops/PRIVATE-NODE.md` §"The verified-executor build".

---

## (2) Install the unit + enable linger  ⟨executable on hbox today⟩

```bash
# on hbox
mkdir -p ~/.config/systemd/user
cp ~/dev/breadstuffs/deploy/node/dregg-node.service ~/.config/systemd/user/
loginctl enable-linger "$USER"        # survives logout AND reboot (PRACTICES §2)
systemctl --user daemon-reload
```

Confirm linger is on (this is the single line that made the games funnel unit
reboot-proof, and its absence is what a hand-run process can never have):

```bash
loginctl show-user "$USER" -p Linger   # → Linger=yes
```

---

## (3) First-boot data-dir init  ⟨executable on hbox today⟩

The unit's `ExecStartPre` runs `dregg-node init --data-dir
%h/.local/state/dregg-node` **once**, only when `node.key` is absent — so a
restart or reboot never re-inits and never wipes state. You can let `enable
--now` (step 4) trigger it, or do it explicitly first to eyeball the genesis:

```bash
# on hbox — optional explicit init (the unit does this for you if you skip it)
~/dev/breadstuffs/target/release/dregg-node init \
  --data-dir ~/.local/state/dregg-node
ls -la ~/.local/state/dregg-node/node.key   # 0600, owner-only (node/src/lib.rs:1793)
```

**This path is the whole point.** `~/.local/state/dregg-node` is a real,
back-up-able directory that **outlives** any `git pull`, `hbuild`/rsync of the
source tree, and any reboot. It is **not** `mktemp -d`. If you would not back it
up, it is not a data dir (PRACTICES §2).

---

## (4) Start + health-check  ⟨executable on hbox today⟩

```bash
# on hbox
systemctl --user enable --now dregg-node
systemctl --user status dregg-node --no-pager
journalctl --user -u dregg-node -n 60 --no-pager
```

In the log expect the verified-executor line (not the marshal-only tripwire):
`verified-executor archive linked: lean_available() is true`. Then check the API
(loopback only):

```bash
curl -fsS http://127.0.0.1:8420/status | jq '{healthy, federation_mode, state_producer, lean_producer, full_turn_proving}'
# → {"healthy":true,"federation_mode":"solo","state_producer":"lean","lean_producer":true,"full_turn_proving":true}
ss -tlnp | grep 8420    # LISTEN 127.0.0.1:8420  — NEVER 0.0.0.0
```

**Prove it is a real node** (execute + prove one faucet Transfer end-to-end).
`scripts/private-node.sh check` does exactly this and works against the
unit-managed node too (it talks to `:8420`, it does not care who started it):

```bash
# on hbox, from the repo
cd ~/dev/breadstuffs && scripts/private-node.sh check
# → EXECUTED: recipient balance = 1000 ... PROVEN: witness_count:1
```

> Note: `scripts/private-node.sh start`/`stop` manage a *hand-run* node with its
> own pid file under `~/dregg-priv/`. Under this unit, **do not** use
> `private-node.sh start/stop` — use `systemctl --user`. `private-node.sh
> status/check/logs` still read the same `:8420` API and are fine. The two must
> not both run: the unit owns `:8420` now.

---

## (5) Verify it survives a restart  ⟨needs the box to verify⟩

This is the durability proof — the property the lost hand-run node never had. Run
it **on hbox**.

```bash
# a) capture the operator cell identity BEFORE the restart
ID_BEFORE=$(curl -fsS http://127.0.0.1:8420/api/node/identity | jq -r .agent_cell)
echo "operator cell before: $ID_BEFORE"

# b) restart the unit and re-check — state must be IDENTICAL (no re-init)
systemctl --user restart dregg-node
sleep 3
ID_AFTER=$(curl -fsS http://127.0.0.1:8420/api/node/identity | jq -r .agent_cell)
echo "operator cell after:  $ID_AFTER"
test "$ID_BEFORE" = "$ID_AFTER" && echo "PASS: same identity — no re-init, state persisted."

# c) confirm the ExecStartPre guard did NOT re-init (idempotent):
journalctl --user -u dregg-node -n 40 --no-pager | grep -i "init" || echo "PASS: no re-init on restart."
```

**Full reboot test** (the real thing the funnel unit passed; `⟨needs the box⟩`
because it reboots hbox — coordinate, hbox is co-tenant):

```bash
# ⚠ reboots the shared box — ONLY when you own the box for a moment.
sudo reboot
# ... after it comes back, WITHOUT logging in as a graphical session:
ssh hbox 'systemctl --user status dregg-node --no-pager | head; curl -fsS http://127.0.0.1:8420/status | jq .healthy'
# → active (running) + true : linger brought it back with its ledger intact.
```

If it does **not** come back after reboot, the cause is almost always linger:
re-check `loginctl show-user "$USER" -p Linger` (step 2).

---

## (6) Re-point the games funnel at the durable node  ⟨executable on hbox today⟩

`dregg-web-games-funnel.service` already sets
`DREGG_NODE_URL=http://127.0.0.1:8420` — the **same loopback address** this unit
binds — so no unit edit is needed. What broke when the old node died is the
node-side **one-time bring-up** (unlock + operator-cell materialize); redo it
against the fresh durable node exactly as
[`deploy/games/RUNBOOK-FUNNEL.md`](../games/RUNBOOK-FUNNEL.md) step (a) prescribes:

```bash
# on hbox — a.2: is the operator cipherclerk unlocked? (loopback devnet w/ no
# passphrase needs NO bearer; skip unlock if unlocked:true)
curl -fsS http://127.0.0.1:8420/api/node/identity | jq '{public_key, agent_cell, unlocked, agent_balance}'

# a.3: faucet-materialize the operator cell ONCE (amount 0 = materialize, no drain)
ID=$(curl -fsS http://127.0.0.1:8420/api/node/identity)
CELL=$(echo "$ID" | jq -r .agent_cell)
PK=$(echo "$ID" | jq -r .public_key)
curl -fsS -X POST -H 'content-type: application/json' \
  --data "{\"recipient\":\"$CELL\",\"amount\":0,\"public_key\":\"$PK\"}" \
  http://127.0.0.1:8420/api/faucet | jq .
# confirm materialized:
curl -fsS http://127.0.0.1:8420/api/node/identity | jq '.agent_balance'   # non-null
```

Now a submitted Descent run **anchors** instead of failing `cell not found`.
Verify a run lands on the node's ledger (RUNBOOK-FUNNEL step e):

```bash
curl -fsS http://127.0.0.1:8420/api/receipts | jq '.[-3:]'
```

The funnel itself (`tailscale funnel --bg 8790`) is unchanged and remains the
**ember-gated** public-exposure flip — this runbook does **not** touch it. The
web unit → this node is pure loopback; the only public edge is Funnel, on the
`skunk-emperor.ts.net` tailnet, exactly as verified live.

---

## Operate

```bash
systemctl --user restart dregg-node          # restart (state persists)
systemctl --user stop dregg-node             # clean stop (stays stopped; Restart=on-failure)
systemctl --user reset-failed dregg-node     # re-arm after a crash-loop brake trip
journalctl --user -u dregg-node -f           # follow logs
```

**Roll back / rebuild the binary:** rebuild per step (1) into
`~/dev/breadstuffs/target/release/dregg-node`, then `systemctl --user restart
dregg-node`. The data dir is untouched by a binary swap.

**Back up the ledger** (the thing that was lost): the state is a plain directory —
`tar czf ~/dregg-node-backup-$(date +%F).tgz -C ~/.local/state dregg-node` while
stopped (or accept an online snapshot's slight inconsistency). This is now
possible *because* the data dir is a real, named path.

---

## Resource caps — tune on the box  ⟨needs the box to verify⟩

The unit ships `CPUQuota=1200%`, `MemoryHigh=8G`, `MemoryMax=16G` on a 24c/123G
co-tenant box. These are **ceilings to prevent an OOM-spiral**, not measured
working sets. Before trusting them as final, watch real proving load on the box:

```bash
systemctl --user status dregg-node --no-pager | grep -E "Memory|CPU|Tasks"
systemd-cgtop --user   # live cgroup usage while `private-node.sh check` proves a turn
```

If proving a cohort turn approaches `MemoryHigh`, raise it — but keep `MemoryMax`
a hard slice well under 123G so the node can never be the cause of the box death
in PRACTICES §1. If the box is under sustained build pressure and you want the
anchor node to stop competing, drop `--prove-turns` from `ExecStart` (or set
`DREGG_PROVE_TURNS` unset via an `EnvironmentFile`) — the node still executes and
commits turns, just without attaching STARK proofs.

---

## What this is NOT (named, separate — do not scope-creep here)

- **Not the multi-node federation.** n=4 validators + blocklace BFT finality need
  a **full-mode** Lean seed (finality/admission exports) + a committee
  `genesis.json` + peers. This solo unit finalizes as a committee-of-one. See
  `docs/OPERATOR-ONBOARDING.md`; the old `N3-RUNBOOK.md` is **quarantined** in
  `deploy/aws/SUPERSEDED/` — the systemd/Caddy/Graviton topology it stands up
  **never ran** (PRACTICES §4). Do not resurrect it.
- **Not public.** No gateway, no Caddy, no DNS, no `0.0.0.0` bind. Loopback only;
  the public edge is Funnel in front of the *web* unit.
- **Not an on-chain settle.** `chain/`, `bridge/` are separate lanes; nothing
  here broadcasts to any chain.
