# The infrastructure moved out of this repo

`deploy/edge/` (OpenTofu + compose for the production edge) and `deploy/mirror/`
(the `dregg.gg` resolver's unit + runbook) now live in their own repository:

> **`~/dev/dregg-infra`** — AGPL-3.0-or-later, same license as this repo.

**Why:** topology, firewall rules and box names are operational detail with a
different audience and cadence than the software, and this repo is public.
Infrastructure does not need to ship inside the thing it hosts.

**What did NOT move, and why:**

- `dregg-mirror/` — the resolver **crate**. It is a cargo workspace member and
  product code. The code lives here; how it is *run* lives in `dregg-infra`.
- `deploy/gateway-ask/` — also a workspace member.
- `deploy/README.md` and `deploy/PRACTICES.md` — the **observed state** of the
  boxes and the practices learned by breaking them. Agents working in this repo
  need those at hand; they are knowledge, not provisioning.
- `deploy/{aws,games,hbox,node,ipfs,telegram,observability,genesis,launchpad,webauth-edge}/`
  — not yet triaged. Some is provisioning (belongs in `dregg-infra`), some is
  runbook (belongs here). Move deliberately, not in bulk.

The division to hold: **this repo describes what the machines ARE and what not
to do to them; `dregg-infra` DECLARES them into existence.**
