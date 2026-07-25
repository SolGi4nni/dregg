# deploy/edge/tofu — THE EDGE, AS CODE.
#
# This directory exists because of TODO-4 (deploy/README.md): the AWS edge's
# compose stack lives ONLY on that box — "unreviewable, undiffable, one `rm`
# from gone." Every fact below is therefore declared here and nowhere else.
#
# Two boxes, deliberately:
#
#   workhorse — the services (node, resolver, games funnel, bot). Rebuildable.
#   anchor    — the tailnet exit + the DNS target. Boring on purpose.
#
# The split is not tidiness. On the old edge the exit node and the services were
# the SAME box, so `deploy/aws/README.md` carries a shouting warning that
# stopping it "cuts the exit for every peer on the tailnet." Here, rebuilding the
# workhorse never touches the exit, and DNS never has to move.
#
#   tofu init && tofu plan
#
# Never build on these boxes — persvati (CPU) and hbox (GPU) build, and IMAGES
# ship here. See deploy/README.md § "Where to build".

terraform {
  required_version = ">= 1.6"
  required_providers {
    hcloud = {
      source  = "hetznercloud/hcloud"
      version = "~> 1.48"
    }
  }
}

provider "hcloud" {
  token = var.hcloud_token
}

# ── the operator key ────────────────────────────────────────────────────────
resource "hcloud_ssh_key" "operator" {
  name       = "dregg-operator"
  public_key = var.ssh_public_key
}

# ── the network the two boxes share privately ───────────────────────────────
# Services talk over this, not over the public internet, and not over tailscale
# (deploy/README.md: there are TWO tailnets and they are NOT connected — do not
# design anything that assumes otherwise).
resource "hcloud_network" "edge" {
  name     = "dregg-edge"
  ip_range = "10.10.0.0/16"
}

resource "hcloud_network_subnet" "edge" {
  network_id   = hcloud_network.edge.id
  type         = "cloud"
  network_zone = var.network_zone
  ip_range     = "10.10.1.0/24"
}

# ── firewall: default-deny, every open port justified in a comment ──────────
resource "hcloud_firewall" "edge" {
  name = "dregg-edge"

  # SSH. Narrow this to your own address in terraform.tfvars if you have a
  # stable one; the default is open because a locked-out operator is worse.
  rule {
    direction  = "in"
    protocol   = "tcp"
    port       = "22"
    source_ips = var.ssh_source_ips
  }

  # The resolver (dregg.gg) — the no-extension click path from X.
  rule {
    direction  = "in"
    protocol   = "tcp"
    port       = "80"
    source_ips = ["0.0.0.0/0", "::/0"]
  }
  rule {
    direction  = "in"
    protocol   = "tcp"
    port       = "443"
    source_ips = ["0.0.0.0/0", "::/0"]
  }

  # The dregg node. Both halves — the old edge bound 0.0.0.0:8420 AND 9420/udp,
  # and a provider that cannot do arbitrary UDP cannot host this.
  rule {
    direction  = "in"
    protocol   = "tcp"
    port       = "8420"
    source_ips = ["0.0.0.0/0", "::/0"]
  }
  rule {
    direction  = "in"
    protocol   = "udp"
    port       = "9420"
    source_ips = ["0.0.0.0/0", "::/0"]
  }

  # Tailscale's direct-connection port. Without it every tailnet packet falls
  # back to a DERP relay and the exit node gets slow and sad.
  rule {
    direction  = "in"
    protocol   = "udp"
    port       = "41641"
    source_ips = ["0.0.0.0/0", "::/0"]
  }
}

# ── the workhorse: services live here, and it is disposable ─────────────────
resource "hcloud_server" "workhorse" {
  name         = "dregg-workhorse"
  server_type  = var.workhorse_type
  image        = "debian-12"
  location     = var.location
  ssh_keys     = [hcloud_ssh_key.operator.id]
  firewall_ids = [hcloud_firewall.edge.id]
  user_data    = templatefile("${path.module}/cloud-init-workhorse.yaml", { ts_authkey = var.tailscale_authkey })

  network {
    network_id = hcloud_network.edge.id
    ip         = "10.10.1.10"
  }

  labels = {
    role = "workhorse"
    repo = "breadstuffs"
  }

  depends_on = [hcloud_network_subnet.edge]
}

# ── the anchor: the exit node + what DNS points at ─────────────────────────
# Small on purpose. It should be the least interesting machine we own, because
# it is the one whose reboot is felt by every peer.
resource "hcloud_server" "anchor" {
  name         = "dregg-anchor"
  server_type  = var.anchor_type
  image        = "debian-12"
  location     = var.location
  ssh_keys     = [hcloud_ssh_key.operator.id]
  firewall_ids = [hcloud_firewall.edge.id]
  user_data    = templatefile("${path.module}/cloud-init-anchor.yaml", { ts_authkey = var.tailscale_authkey })

  network {
    network_id = hcloud_network.edge.id
    ip         = "10.10.1.5"
  }

  labels = {
    role = "anchor"
    repo = "breadstuffs"
  }

  depends_on = [hcloud_network_subnet.edge]
}

# ── a floating IP, so the DNS target outlives any single machine ────────────
# The AWS EIP is the ONLY reason a stop/start there didn't dangle DNS
# (deploy/aws/README.md says so explicitly). This is that property, declared.
resource "hcloud_floating_ip" "public" {
  type          = "ipv4"
  home_location = var.location
  description   = "dregg public edge — the address DNS points at"
}

resource "hcloud_floating_ip_assignment" "public" {
  floating_ip_id = hcloud_floating_ip.public.id
  server_id      = hcloud_server.anchor.id
}
