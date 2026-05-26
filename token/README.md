# token

Unified authorization token abstraction over two token formats: Macaroon
(HMAC-SHA256, symmetric) and Biscuit (Ed25519, Datalog authorization). The rest
of the `dregg` auth stack works through the `AuthToken` trait defined here.

## Overview

This crate bridges two fundamentally different token architectures behind a
single trait:

- **Macaroon** (`em2_` prefix): HMAC-SHA256 symmetric tokens. Verification
  takes ~0.5 microseconds. Requires the root secret key for both minting and
  verification. Best for internal service-to-service auth on hot paths.
- **Biscuit** (`eb2_` prefix): Ed25519 asymmetric tokens with Datalog
  authorization policies. Decentralized verification with just a public key.
  Best for distributed and delegated auth scenarios.

Token format is chosen at mint time. Verification auto-detects from the prefix.

## Key Types

| Type | Description |
|------|-------------|
| `AuthToken` | Trait: `verify`, `attenuate`, `to_encoded`, `to_bytes`, `seal` |
| `MacaroonToken` | Macaroon implementation of `AuthToken` |
| `BiscuitToken` | Biscuit implementation of `AuthToken` |
| `TokenFormat` | Enum: `Macaroon`, `Biscuit`; has `detect(encoded)` |
| `AuthRequest` | What the token is being asked to authorize (org, app, service, action, etc.) |
| `TokenClearance` | Verification result: matched policy + granted capabilities |
| `Attenuation` | Restriction spec for narrowing a token's permissions |
| `Capability` | A single granted permission: resource type, ID, actions |

## Features

| Feature | Default | Description |
|---------|---------|-------------|
| `macaroon` | yes | Enables `MacaroonToken` (depends on `macaroon` crate) |
| `biscuit` | yes | Enables `BiscuitToken` (depends on `biscuit-auth` v6) |

## Usage

```rust
use dregg_token::{AuthRequest, AuthToken, Attenuation, MacaroonToken, TokenFormat};

// Auto-detect format from prefix
let fmt = TokenFormat::detect("em2_base64data...")?; // -> TokenFormat::Macaroon

// Decode and verify
let token = MacaroonToken::from_encoded("em2_...", root_key)?;
let request = AuthRequest {
    service: Some("dns".into()),
    action: Some("r".into()),
    ..Default::default()
};
let clearance = token.verify(&request)?;

// Attenuate (restrict) -- can only narrow, never expand
let restricted = token.attenuate(&Attenuation {
    services: vec![("dns".into(), "r".into())],
    not_after: Some(1700000000),
    ..Default::default()
})?;
let encoded = restricted.to_encoded()?;
```

## Typed Macaroon Caveats

The `dregg_caveats` module defines typed caveat IDs (0-12) with MsgPack encoding:

| ID | Caveat | Verification |
|----|--------|-------------|
| 0 | Org | match-any |
| 1 | App | match-any |
| 2 | Service | match-any |
| 4 | Feature | set-containment (requested subset of granted) |
| 5 | ValidityWindow | all-must-pass |
| 8 | ConfineUser | match-any |
| 9 | OAuthProvider | match-any |
| 10 | OAuthScope | set-containment |
| 11 | FromMachine | match-any |
| 12 | Command | match-any |

## Architecture

This crate is the token abstraction layer. It depends on the `macaroon` crate for
the raw macaroon primitives and `biscuit-auth` for Biscuit/Datalog. The
auth service's `TokenDb` uses this trait for all mint/verify/attenuate
operations.

```
macaroon + biscuit-auth
  -> token (this crate: AuthToken trait)
    -> auth (TokenDb, RPC service)
      -> sidecar / JS module / Kotlin bridge
```

## Tests

46 tests covering both token formats, verification, attenuation, format
detection, typed caveat encoding, and round-trip serialization.

```sh
cargo test -p token
```
