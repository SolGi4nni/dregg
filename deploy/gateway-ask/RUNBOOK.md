# RUNBOOK — the gateway-ask sidecar: cutover, deploy, rollback

This runbook is the hardened operator procedure for the on-demand-TLS + capability
gateway. It carries the **stage → atomic-swap → paired cold-backup rollback**
discipline so a bad candidate is caught on an alt port before it ever goes live,
and a promotion is a single atomic rename that rollback reverses.

The resident per-surface runbooks (`deploy/aws/README.md`,
`deploy/games/RUNBOOK.md`, `deploy/launchpad/RUNBOOK.md`) describe the hand-written
one-block-per-domain deploys this kit consolidates; follow this one for the
gateway-ask sidecar itself.

## 0. Prerequisites

- `cargo-zigbuild` + `zig` on the dev box (the deploy box compiles nothing).
- The deploy box runs a `gateway-ask` systemd unit that execs
  `/opt/gateway-ask/gateway-ask` with the `.env` (bind, `DREGG_HOSTING_APEX`,
  `DREGG_GATEWAY_AUTH_ROOT_PUBKEY`).
- Caddy on the gateway loads `Caddyfile.on-demand-tls` with the environment from
  `.env` (apex, upstreams, ACME email). `DREGG_GATEWAY_AUTH_ROOT_PUBKEY` is the
  issuer PUBLIC key; unset ⇒ every `/auth` route is fail-closed (`503`).

## 1. Cutover from per-surface blocks → the one on-demand block

Do this ONCE per surface, staged so it is reviewable and reversible:

1. Bring up the sidecar (`deploy.sh all`) and confirm `/healthz` answers.
2. For each site currently in a hardcoded block, ensure a **verified** binding
   exists in the registry (a `verify` turn, or `compose_launch_landing` for a
   launch). Confirm the `ask` says yes:
   `curl -s "http://127.0.0.1:8799/internal/site-exists?domain=<host>"` → `200`.
3. Add the `*.{$HOSTING_APEX}` wildcard block from `Caddyfile.on-demand-tls`
   ALONGSIDE the existing hardcoded blocks (both present, wildcard lower priority
   by specificity). Reload Caddy. Verify the wildcard serves a NEW verified host.
4. Remove the hardcoded block for a migrated host; reload; verify it still serves
   (now via the wildcard + `ask`). Repeat per host. Rollback at any step = restore
   the hardcoded block and reload.

The end state: one wildcard block; a new site is a registry write, not a Caddy
edit.

## 2. Deploy a new sidecar build (stage-gated)

```
export BOX_HOST=<public-dns-or-ip> SSH_KEY=~/.ssh/box.pem
deploy/gateway-ask/deploy.sh all
```

`all` runs, in order:

| step | what happens | failure = |
|------|--------------|-----------|
| `build` | `cargo zigbuild` the linux binary on THIS box | fix locally; nothing shipped |
| `ship`  | rsync binary + config to `$REMOTE_DIR/incoming/` (live binary untouched) | nothing swapped |
| `stage` | boot candidate on `127.0.0.1:$STAGE_PORT`, probe `/healthz` **twice** | candidate rejected; live binary untouched |
| `swap`  | cold-backup live binary → atomic-rename candidate over it → restart → gate | see rollback below |

The `stage` step is the guard: a candidate that will not come up healthy, or
whose health CHANGES across an idempotent restart (it flaps), is rejected here,
before the live service is touched. Only a stable candidate is promotable.

The `swap` step never hands the running service a half-written file: the candidate
is copied to a temp on the same filesystem and `mv`-renamed over the live path
(atomic `rename(2)`). The previous binary is cold-backed-up + checksummed first.

## 3. Rollback

```
deploy/gateway-ask/deploy.sh rollback            # newest cold backup
deploy/gateway-ask/deploy.sh rollback gateway-ask-20260714T090000Z   # a specific one
deploy/gateway-ask/deploy.sh releases            # list the cold backups
```

Rollback verifies the backup against its recorded `sha256` (a corrupt backup is
refused — never install a corrupt rollback), then atomic-renames it over the live
binary and restarts + gates. Make it automatic on a failed deploy:

```
deploy/gateway-ask/deploy.sh swap --auto-rollback
```

If the ROLLED-BACK binary also fails its gate, the problem is the box itself
(disk / memory / the unit / a dependency), not the binary — the script says so and
stops rather than looping.

## 4. Health surfaces

- `GET /healthz` — the sidecar liveness the deploy gate + staging poll.
- `GET /internal/site-exists?domain=<host>` — `200`/`404`; the on-demand-TLS `ask`.
- `GET /auth?cap=<name>` — `200`/`401`/`403`/`503`; the capability gate. `503`
  means no issuer key is configured (fail-closed) — set
  `DREGG_GATEWAY_AUTH_ROOT_PUBKEY` and restart.

## 5. Common failure modes

| symptom | cause | fix |
|---------|-------|-----|
| a real site gets no cert | its binding is not verified (or only pending) | run its `verify` turn; confirm the `ask` returns `200` |
| every `/auth` route returns `503` | no issuer key | set `DREGG_GATEWAY_AUTH_ROOT_PUBKEY` (public key hex) + restart |
| an operator is `401` on a gated surface | no token presented | sign in at `/.dregg-auth/login`; retry with the cookie / bearer |
| `stage` rejects a candidate | it will not come up healthy, or it flaps across restart | read `/tmp/gateway-ask-stage.log` on the box; fix; rebuild |
| a wildcard host 404s at the app | the site app does not know the inbound Host | confirm `site_for_host` resolves it (verified binding) |
