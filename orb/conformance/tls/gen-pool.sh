#!/usr/bin/env bash
# Generate the ECDSA-P256 and RSA-PSS-2048 pool certificates the deployed HTTPS
# front door presents to clients that do not accept Ed25519 (curl / LibreSSL /
# browsers). Companion to gen-cert.sh (which makes the Ed25519 default). Each is
# a self-signed leaf with SAN localhost + 127.0.0.1, plus the raw signing-key
# material in the exact form the verified HACL* signer reads:
#
#   ecdsa-cert.der  — the DER end-entity certificate (P-256 leaf)
#   ecdsa-key.bin   — the 32-byte big-endian ECDSA private scalar
#   rsa-cert.der    — the DER end-entity certificate (RSA-2048 leaf)
#   rsa-n.bin       — big-endian RSA modulus
#   rsa-e.bin       — big-endian RSA public exponent
#   rsa-d.bin       — big-endian RSA private exponent
#
# The dataplane loads these by default (conformance/tls/*), or from the
# DRORB_TLS_ECDSA_* / DRORB_TLS_RSA_* environment; the verified chooseCert picks
# among the pool per the client's signature_algorithms. curl -k connects.
set -euo pipefail
cd "$(dirname "$0")"
D=$(mktemp -d)

cat > "$D/leaf.ext" <<EXT
subjectAltName = DNS:localhost, IP:127.0.0.1
basicConstraints = CA:FALSE
keyUsage = critical, digitalSignature
extendedKeyUsage = serverAuth
EXT

# --- ECDSA-P256 leaf (self-signed, SAN), 397d ---
openssl ecparam -name prime256v1 -genkey -noout -out "$D/ec.key"
openssl req -new -x509 -key "$D/ec.key" -days 397 -subj "/CN=localhost" \
  -extensions v3 -config <(cat <<CFG
[req]
distinguished_name = dn
[dn]
[v3]
subjectAltName = DNS:localhost, IP:127.0.0.1
basicConstraints = CA:FALSE
keyUsage = critical, digitalSignature
extendedKeyUsage = serverAuth
CFG
) -out "$D/ec.crt"
openssl x509 -in "$D/ec.crt" -outform DER -out ecdsa-cert.der

# --- RSA-2048 leaf (self-signed, SAN), 397d ---
openssl genrsa -out "$D/rsa.key" 2048
openssl req -new -x509 -key "$D/rsa.key" -days 397 -subj "/CN=localhost" \
  -extensions v3 -config <(cat <<CFG
[req]
distinguished_name = dn
[dn]
[v3]
subjectAltName = DNS:localhost, IP:127.0.0.1
basicConstraints = CA:FALSE
keyUsage = critical, digitalSignature
extendedKeyUsage = serverAuth
CFG
) -out "$D/rsa.crt"
openssl x509 -in "$D/rsa.crt" -outform DER -out rsa-cert.der

# --- Extract the raw key material in the HACL* signer's byte form ---
# The EC scalar and RSA n/e/d come straight out of openssl's `-text` dump; a
# short Python walk turns the hex columns into big-endian bytes (32-byte scalar,
# leading-zero-tolerant RSA components).
EC_TEXT=$(openssl ec -in "$D/ec.key" -text -noout 2>/dev/null)
RSA_TEXT=$(openssl rsa -in "$D/rsa.key" -text -noout 2>/dev/null)

EC_TEXT="$EC_TEXT" RSA_TEXT="$RSA_TEXT" python3 - <<'PY'
import os, re

def hexblock(text, start, end_labels):
    """Collect the ':'-separated hex bytes under a `label:` line."""
    lines = text.splitlines()
    out, grabbing = [], False
    for ln in lines:
        s = ln.strip()
        if s.startswith(start):
            grabbing = True
            continue
        if grabbing:
            if any(s.startswith(e) for e in end_labels) or (ln and not ln[0].isspace()):
                break
            out += [b for b in s.split(":") if b]
    return bytes(int(b, 16) for b in out)

def be_fixed(b, n):
    b = b.lstrip(b"\x00")           # drop any sign/leading zero
    if len(b) > n:
        b = b[-n:]
    return b.rjust(n, b"\x00")

ec = os.environ["EC_TEXT"]
rsa = os.environ["RSA_TEXT"]

scalar = be_fixed(hexblock(ec, "priv:", ["pub:", "ASN1"]), 32)
open("ecdsa-key.bin", "wb").write(scalar)

n = hexblock(rsa, "modulus:", ["publicExponent"])
d = hexblock(rsa, "privateExponent:", ["prime1", "prime2", "exponent1"])
open("rsa-n.bin", "wb").write(n.lstrip(b"\x00") or b"\x00")
open("rsa-e.bin", "wb").write(b"\x01\x00\x01")   # 65537
open("rsa-d.bin", "wb").write(d.lstrip(b"\x00") or b"\x00")

print(f"ecdsa scalar {len(scalar)}B, rsa n {len(n.lstrip(chr(0).encode()))}B "
      f"d {len(d.lstrip(chr(0).encode()))}B")
PY

rm -rf "$D"
echo "generated ecdsa-cert.der + ecdsa-key.bin, rsa-cert.der + rsa-{n,e,d}.bin"
