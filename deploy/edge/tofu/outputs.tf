# What you need after `tofu apply` — the DNS records, and how to get in.

output "public_ip" {
  description = "THE address DNS points at. A floating IP, so it survives rebuilding the anchor."
  value       = hcloud_floating_ip.public.ip_address
}

output "anchor_ip" {
  description = "The anchor's own address (ssh here for exit-node work)."
  value       = hcloud_server.anchor.ipv4_address
}

output "workhorse_ip" {
  description = "The workhorse's own address (ssh here for services)."
  value       = hcloud_server.workhorse.ipv4_address
}

output "dns_records" {
  description = <<-EOT
    Paste these at the registrar. Set TTL 300 while wiring, raise it after.
    The apex A record is the one that matters; everything else can move later.
  EOT
  value       = <<-EOT

    ; ── the resolver: the no-extension click path from X ──────────────────
    dregg.gg.        300  IN  A     ${hcloud_floating_ip.public.ip_address}
    www.dregg.gg.    300  IN  CNAME dregg.gg.
    dregg.gg.        300  IN  CAA   0 issue "letsencrypt.org"

    ; ── the play surface (.app is HSTS-preloaded — HTTPS enforced by browsers) ──
    dregg.app.       300  IN  A     ${hcloud_floating_ip.public.ip_address}
    dregg.app.       300  IN  CAA   0 issue "letsencrypt.org"

    ; ── the market, when it wants a home ──────────────────────────────────
    dregg.fi.        300  IN  A     ${hcloud_floating_ip.public.ip_address}

    ; dregg.tech → point at the site's CloudFront distribution, not here:
    ;   it is document-shaped, like www.dregg.net.
    ; dregg.info / .us / .online / .website → redirect to dregg.net.

  EOT
}

output "next_steps" {
  value = <<-EOT

    1. Point DNS at ${hcloud_floating_ip.public.ip_address} (see `dns_records`).
    2. Ship images — NEVER build on these boxes (deploy/README.md § Where to build):
         ssh persvati 'cd ~/dregg-build/<lane> && cargo build --release -p dregg-node'
         docker save dregg-node:next | gzip | ssh root@${hcloud_server.workhorse.ipv4_address} 'gunzip | docker load'
    3. Bring services up from deploy/edge/compose/ (this repo — not a file that
       lives only on the box, which is the whole point of TODO-4).
    4. Verify the exit node BEFORE cutting AWS over:
         ssh root@${hcloud_server.anchor.ipv4_address} 'tailscale status'
    5. Keep the AWS instance STOPPED, not terminated, for a week. Then kill it.

  EOT
}
