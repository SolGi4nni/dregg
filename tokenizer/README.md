# tokenizer

X25519 + ChaCha20-Poly1305 sealed-box encryption and HTTP credential proxy.
Implements the [Fly.io Tokenizer](https://fly.io/blog/macaroons-escalated-quickly/)
pattern: guest code never sees plaintext credentials. Instead, it holds a
capability token that the tokenizer daemon uses to unseal and inject secrets
into outbound HTTP requests.

## Overview

The core security property: guest (untrusted) code can make authenticated API
calls without ever having access to the plaintext access token. The flow is:

1. Guest code holds a capability token (macaroon or biscuit) scoped to a
   specific provider and set of scopes.
2. Guest sends the capability token + sealed secret reference to the tokenizer.
3. Tokenizer verifies the capability token via `TokenDb`.
4. Tokenizer decrypts the sealed secret using its Curve25519 private key.
5. Tokenizer injects the plaintext credential into the outbound HTTP request.
6. Guest receives the HTTP response. The plaintext credential is never exposed.

## Key Types

| Type | Description |
|------|-------------|
| `TokenizerKeypair` | X25519 keypair: `generate()`, `from_bytes()`, `unseal()` |
| `SealedSecret` | Encrypted payload: ephemeral public key + nonce + ciphertext |
| `TokenizerProxy` | HTTP proxy: verifies tokens, unseals secrets, forwards requests |
| `TokenizerProxyConfig` | Configuration: keypair, TokenDb, SecretStore, HTTP client |
| `ProxyResponse` | Proxied HTTP response: status, headers, body |

## Encryption

Secrets are encrypted with X25519 Diffie-Hellman key agreement + ChaCha20-Poly1305
AEAD (NaCl sealed-box semantics). The sender's identity is not revealed.

Wire format: `[32-byte ephemeral public key][12-byte nonce][ciphertext + 16-byte tag]`

Total overhead: 60 bytes per sealed secret.

## Usage

### Seal and Unseal

```rust
use dregg_tokenizer::{TokenizerKeypair, SealedSecret};

// Generate a keypair (daemon holds this)
let keypair = TokenizerKeypair::generate();

// Seal a secret using the daemon's public key
let sealed = SealedSecret::seal(b"ghp_secret_token", keypair.public_key())?;

// Unseal with the private key
let plaintext = keypair.unseal(&sealed)?;
assert_eq!(plaintext, b"ghp_secret_token");
```

### HTTP Proxy

```rust
use dregg_tokenizer::{TokenizerProxy, TokenizerProxyConfig};
use std::sync::Arc;

let proxy = TokenizerProxy::new(TokenizerProxyConfig {
    keypair: Arc::new(keypair),
    token_db: Arc::new(token_db),
    secret_store: Arc::new(secret_store),
    http_client: reqwest::Client::new(),
});

// Proxy a request -- credential is injected, never returned to caller
let response = proxy.proxy_request(
    "em2_capability_token...",     // capability token
    "base64_sealed_secret...",     // sealed secret
    "https://api.github.com/user", // target URL
    "bearer",                      // inject mode
    "GET",                         // HTTP method
    vec![],                        // extra headers
    None,                          // body
).await?;
```

### Inject Modes

| Mode | Behavior |
|------|----------|
| `"bearer"` | Sets `Authorization: Bearer <secret>` header |
| `"header:X-API-Key"` | Sets `X-API-Key: <secret>` header |
| `"query:access_token"` | Appends `?access_token=<secret>` to URL |

## Architecture

The tokenizer sits between the guest runtime and external APIs. It depends on
the `token` crate for token verification and `secrets` for secret lookup.

```
Guest runtime (has: capability token only)
  -> Tokenizer (this crate)
    1. Verify capability token (via TokenDb)
    2. Decrypt sealed secret (X25519 + ChaCha20-Poly1305)
    3. Inject credential into HTTP request
    4. Forward to external API
    5. Return response to guest
  <- Guest receives response (never sees plaintext credential)
```

The proxy is method-based (not a standalone server). It is called from the
sidecar daemon's HTTP handler, which listens on a Unix domain socket.

## Tests

12 tests covering keypair generation, seal/unseal round-trips, proxy request
handling, inject modes, and error cases.

```sh
cargo test -p tokenizer
```
