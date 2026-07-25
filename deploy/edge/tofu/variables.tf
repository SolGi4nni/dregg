# Knobs. Defaults are the shape we actually want; override in terraform.tfvars.

variable "hcloud_token" {
  description = "Hetzner Cloud API token (project-scoped). Keep it out of git — use TF_VAR_hcloud_token or a tfvars file that is gitignored."
  type        = string
  sensitive   = true
}

variable "ssh_public_key" {
  description = "The operator's SSH public key, installed on both boxes at first boot."
  type        = string
}

variable "ssh_source_ips" {
  description = <<-EOT
    Who may reach port 22. Narrow this to your own address if you have a stable
    one. Open by default because being locked out of the box that serves DNS is
    a worse failure than a filtered SSH port.
  EOT
  type        = list(string)
  default     = ["0.0.0.0/0", "::/0"]
}

variable "location" {
  description = <<-EOT
    Hetzner location. `ash` = Ashburn VA, `hil` = Hillsboro OR, `nbg1`/`fsn1`/`hel1` = EU.
    US for a mostly-US audience; the price is the same either way.
  EOT
  type        = string
  default     = "ash"
}

variable "network_zone" {
  description = "Must match the location's zone: us-east for ash, us-west for hil, eu-central for nbg1/fsn1."
  type        = string
  default     = "us-east"
}

variable "workhorse_type" {
  description = <<-EOT
    The services box. ccx33 = 8 DEDICATED vCPU / 32 GB / 240 GB NVMe (~€49/mo).
    Dedicated rather than shared because proving and serving in the same box is
    what killed hbox once already (deploy/PRACTICES.md §1) — if this box ever
    hosts the games funnel, it should not be fighting a noisy neighbour too.
    Downgrade to cpx41 (~€26) if the first month is quiet.
  EOT
  type        = string
  default     = "ccx33"
}

variable "anchor_type" {
  description = <<-EOT
    The exit node + DNS target. cpx11 = 2 vCPU / 2 GB / 40 GB (~€5/mo).
    Deliberately tiny: it forwards packets and holds an address. Every service
    that grows belongs on the workhorse instead.
  EOT
  type        = string
  default     = "cpx11"
}

variable "tailscale_authkey" {
  description = <<-EOT
    A REUSABLE, PRE-AUTHORIZED tailscale auth key (tailnet A — the 100.64.0.x
    one the edge is the exit for). Generate at
    https://login.tailscale.com/admin/settings/keys with `ephemeral: false`.
    Passed to cloud-init; leave empty to join the tailnet by hand after boot.
  EOT
  type        = string
  default     = ""
  sensitive   = true
}
