#!/usr/bin/env bash
B="https://devnet.dregg.fg-goose.online"
echo "=== ATTACK 1: malformed JSON body to /turn/submit ==="
curl -s -m 10 -o /dev/null -w "HTTP %{http_code}\n" -X POST "$B/turn/submit" \
  -H 'content-type: application/json' --data '{this is not json'

echo "=== ATTACK 2: /turn/submit without bearer token (protected route) ==="
curl -s -m 10 -X POST "$B/turn/submit" -H 'content-type: application/json' \
  --data '{"agent":"00","actions":[],"nonce":0,"fee":0}' -w "\nHTTP %{http_code}\n" | head -c 400
echo

echo "=== ATTACK 3: oversized body (~16.8MB) to /turn/submit ==="
yes A | head -c 16800000 > /tmp/big.bin
curl -s -m 30 -o /dev/null -w "HTTP %{http_code} sent=%{size_upload}\n" -X POST "$B/turn/submit" \
  -H 'content-type: application/json' --data-binary @/tmp/big.bin

echo "=== ATTACK 4: malformed faucet request ==="
curl -s -m 10 -X POST "$B/api/faucet" -H 'content-type: application/json' \
  --data '{"recipient":"  "}' -w "\nHTTP %{http_code}\n" | head -c 300
echo

echo "=== ATTACK 5: faucet with non-hex / overlong recipient (injection attempt) ==="
curl -s -m 10 -X POST "$B/api/faucet" -H 'content-type: application/json' \
  --data '{"recipient":"../../etc/passwd","amount":999999999999}' -w "\nHTTP %{http_code}\n" | head -c 300
echo

echo "=== ATTACK 6: status/health still healthy after the barrage ==="
curl -s -m 10 "$B/health" | head -c 400
echo

echo "=== ATTACK 7: cipherclerk/mint without auth (privileged op) ==="
curl -s -m 10 -X POST "$B/cipherclerk/mint" -H 'content-type: application/json' \
  --data '{"amount":1000000}' -w "\nHTTP %{http_code}\n" | head -c 200
echo

echo "=== ATTACK 8: path traversal on cell detail ==="
curl -s -m 10 -o /dev/null -w "HTTP %{http_code}\n" "$B/api/cell/..%2F..%2F..%2Fetc%2Fpasswd"
