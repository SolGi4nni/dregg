# hbox service hardening (systemd user-unit drop-ins)

Applied 2026-07-17 as `.d/hardening.conf` drop-ins on each hbox user unit, VERIFIED
live (services stay up + connected). The blast radius of the internet-facing web
server (dreggnet-web-server, publicly exposed via Tailscale Funnel + arcade.dregg.net)
is the reason: before this it ran with ZERO sandboxing as the hbox user and could
read every secret on the box.

## What is applied (the user-unit-SAFE subset)
- `NoNewPrivileges`, `PrivateTmp`, `ProtectSystem=strict` (+ `ReadWritePaths` for each
  service's real state dir), `RestrictAddressFamilies=AF_INET AF_INET6 AF_UNIX`,
  `RestrictNamespaces`, `LockPersonality`, `RestrictRealtime`, `RestrictSUIDSGID`,
  `SystemCallFilter=@system-service` (seccomp).
- **The key win — `InaccessiblePaths=~/.config/dregg ~/.ssh`** on the FUNNEL: the
  public web process cannot read the bot secrets (BOT_SECRET, tokens) or ssh keys at
  runtime. EnvironmentFile is read by the MANAGER before the sandbox, so each unit
  still gets its OWN env; the process just cannot read the files afterward.
- FUNNEL only: session caps (`DREGGNET_WEB_MAX_SESSIONS` etc.) — closes the
  previously-unbounded session-minting DoS.

## What is NOT applied (and why)
`ProtectKernelTunables` / `ProtectKernelModules` / `ProtectControlGroups` /
`ProtectClock` / `ProtectHostname` — these require capability drops the hbox USER
manager cannot perform (`status=218/CAPABILITIES`). They only work in SYSTEM units
or with a privileged manager.

## The maturation path (not yet done)
Step 1 (this): user-safe hardening + secret isolation + DoS caps. DONE.
Step 2: privilege-separate — run the internet-facing web server as its OWN user (or
in a container; docker is on hbox) with no read path to the bot secrets at all.
Step 3 (dregg-native): run the public surface inside a grain-jail / confined body —
dogfood our own confinement tech.
