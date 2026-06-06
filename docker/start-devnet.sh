#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

REBUILD_SITE=false
for arg in "$@"; do
  case "$arg" in
    --rebuild-site) REBUILD_SITE=true ;;
  esac
done

cd "$PROJECT_ROOT"

if [ "$REBUILD_SITE" = true ] || [ ! -d site/dist ] || [ -z "$(ls -A site/dist 2>/dev/null)" ]; then
  echo "Building site..."
  cd site
  npm ci
  npm run build
  cd "$PROJECT_ROOT"
fi

echo "Generating devnet configuration..."
cargo run --release -p dregg-node -- genesis --validators 3 --output docker/devnet-config/

echo ""
echo "Building Docker image..."
docker compose -f docker/docker-compose.yml build

echo ""
echo "Starting 3-node devnet..."
docker compose -f docker/docker-compose.yml up -d

echo ""
echo "Devnet is running!"
echo "  Proxy:      http://localhost:8400  (API, gallery, discharge, site)"
echo "  Node 0 API: http://localhost:8420  (faucet enabled)"
echo "  Node 1 API: http://localhost:8421"
echo "  Node 2 API: http://localhost:8422"
echo "  Gallery:    http://localhost:3040"
echo "  Explorer:   http://localhost:3000"
echo ""
echo "Via proxy (:8400):"
echo "  API:        http://localhost:8400/api/*"
echo "  Gallery:    http://localhost:8400/gallery/*"
echo "  Discharge:  http://localhost:8400/discharge/*"
echo "  Studio:     http://localhost:8400/studio"
echo "  Starbridge: http://localhost:8400/starbridge"
echo "  Apps:       http://localhost:8400/apps"
echo "  Starbridge apps: http://localhost:8400/starbridge-apps/*"
echo ""
echo "Faucet usage:"
echo "  curl -X POST http://localhost:8420/api/faucet \\"
echo "    -H 'Content-Type: application/json' \\"
echo "    -d '{\"recipient\": \"<64-hex-chars>\", \"amount\": 1000}'"
echo ""
echo "To stop: docker compose -f docker/docker-compose.yml down"
echo "To view logs: docker compose -f docker/docker-compose.yml logs -f"