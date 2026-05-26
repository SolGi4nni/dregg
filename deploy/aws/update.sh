#!/bin/bash
# dregg gateway node — pull latest and rebuild
set -euo pipefail

echo "=== Updating dregg gateway node ==="

cd /opt/dregg
git fetch origin main
git reset --hard origin/main

echo "Building..."
cargo build --release -p dregg-node

echo "Restarting service..."
sudo systemctl restart dregg-gateway

# Update static site assets
sudo cp -r site/explorer/* /opt/dregg/site/explorer/ 2>/dev/null || true
sudo cp -r site/playground/* /opt/dregg/site/playground/ 2>/dev/null || true

# Check if Caddyfile changed
if ! diff -q deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile &>/dev/null; then
  echo "Caddyfile changed, reloading Caddy..."
  sudo cp deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile
  sudo systemctl reload caddy
fi

echo "=== Update complete ==="
echo "Check status: sudo systemctl status dregg-gateway"
sudo systemctl status dregg-gateway --no-pager -l | head -20
