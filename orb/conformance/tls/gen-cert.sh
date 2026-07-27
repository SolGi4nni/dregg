#!/usr/bin/env bash
# Generate a CA-chained, SAN-bearing Ed25519 leaf certificate for the TLS
# conformance oracle, plus the raw RFC 8032 signing seed the oracle needs.
#   cert.der  — the DER end-entity certificate (leaf), CN + SAN localhost/127.0.0.1
#   chain.der — the DER issuing-CA certificate
#   seed.bin  — the leaf's 32-byte Ed25519 signing seed (RFC 8032 §5.1.5)
set -euo pipefail
cd "$(dirname "$0")"
D=$(mktemp -d)

# Root CA (Ed25519), 10y.
openssl genpkey -algorithm ed25519 -out "$D/ca.key"
openssl req -x509 -new -key "$D/ca.key" -days 3650 -out "$D/ca.crt" \
  -subj "/CN=drorb conformance CA" -addext "basicConstraints=critical,CA:TRUE"

# Leaf (Ed25519), 397d, SAN localhost + 127.0.0.1.
openssl genpkey -algorithm ed25519 -out "$D/leaf.key"
openssl req -new -key "$D/leaf.key" -out "$D/leaf.csr" -subj "/CN=localhost"
cat > "$D/leaf.ext" <<EXT
subjectAltName = DNS:localhost, IP:127.0.0.1
basicConstraints = CA:FALSE
keyUsage = critical, digitalSignature
extendedKeyUsage = serverAuth
EXT
openssl x509 -req -in "$D/leaf.csr" -CA "$D/ca.crt" -CAkey "$D/ca.key" \
  -CAcreateserial -days 397 -extfile "$D/leaf.ext" -out "$D/leaf.crt"

openssl x509 -in "$D/leaf.crt" -outform DER -out cert.der
openssl x509 -in "$D/ca.crt"   -outform DER -out chain.der
cp "$D/leaf.crt" cert.pem
cp "$D/leaf.key" key.pem

# Extract the raw 32-byte Ed25519 seed from the PKCS8 private key: it is the
# 32-byte OCTET STRING inside the privateKey OCTET STRING (last 32 bytes of the
# DER PKCS8 for an Ed25519 key).
openssl pkey -in "$D/leaf.key" -outform DER -out "$D/leaf.pk8"
tail -c 32 "$D/leaf.pk8" > seed.bin

rm -rf "$D"
echo "generated cert.der (leaf, SAN), chain.der (CA), seed.bin ($(wc -c < seed.bin) bytes)"
