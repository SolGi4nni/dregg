# macaroon

HMAC-SHA256 bearer tokens with cryptographic caveat attenuation, inspired by
[Google's macaroons paper](https://research.google/pubs/pub41892/) and
[Fly.io's implementation](https://fly.io/blog/macaroons-escalated-quickly/).

## Overview

Macaroons are bearer tokens where authorization caveats can only be added
(restricting access), never removed. This property is enforced by an HMAC-SHA256
chain: each caveat extends the chain, and removing one invalidates the tag.

Key properties:

- **Attenuation-only**: caveats restrict, never expand. Removing a caveat is
  cryptographically impossible.
- **Third-party delegation**: external services can discharge caveats without
  the verifier contacting them directly.
- **Offline verification**: no network calls required -- everything needed is
  in the token itself.
- **Composable**: multiple caveats stack with AND semantics.

## Key Types

| Type | Description |
|------|-------------|
| `Macaroon` | Core token: nonce, location, caveat chain, HMAC tail |
| `CaveatSet` | Ordered list of first-party and third-party caveats |
| `ThirdPartyCaveat` | Encrypted ticket for delegated discharge |
| `Action` | Bitmask for resource permissions (`r`, `w`, `c`, `d`, `C`, `*`) |
| `ResourceSet<ID, A>` | Typed map of resource identifiers to action masks |
| `WireCaveat` | MsgPack-encoded caveat for wire transport |

## Usage

```rust
use dregg_macaroon::{Macaroon, Action, encode_token, decode_token};

// Create a root macaroon
let root_key: [u8; 32] = /* your root secret */;
let mac = Macaroon::new(b"key-id-001", "https://auth.example.com", &root_key);

// Attenuate with first-party caveats
let mac = mac.add_first_party(&my_caveat);

// Verify against the root key
mac.verify(&root_key)?;

// Encode for transport (em2_ prefix + base64url)
let encoded: String = encode_token(&mac);
let decoded: Macaroon = decode_token(&encoded)?;
```

### Action Bitmask

Actions are single-character flags, not words:

```rust
use dregg_macaroon::Action;

let read = Action::parse("r");        // READ
let read_write = Action::parse("rw"); // READ | WRITE
let all = Action::parse("*");         // ALL
// WARNING: Action::parse("read") parses chars r, e, a, d -- not the word "read"
```

### Third-Party Caveats

```rust
// Issuer adds a third-party caveat
let mac = mac.add_third_party(
    "https://discharge.example.com",
    &shared_key,
    b"caveat-identifier",
)?;

// Third party mints a discharge macaroon
let discharge = dregg_macaroon::create_discharge(
    &shared_key,
    b"caveat-identifier",
    "https://discharge.example.com",
)?;

// Verifier binds discharge to the root macaroon and verifies
let bound = mac.bind_discharge(&discharge);
```

## Wire Format

Tokens are serialized as MsgPack, then base64url-encoded with the `em2_` prefix.
The prefix enables format auto-detection in the `token` crate.

## Architecture

This crate is the lowest layer in the `dregg` auth stack. It provides raw macaroon
primitives that the `token` crate wraps behind the `AuthToken` trait, which the
auth service then exposes via Cap'n Proto RPC.

```
macaroon (this crate)
  -> token (AuthToken trait)
    -> auth (RPC service, TokenDb)
      -> sidecar (IPC daemon)
```

## Tests

31 tests covering creation, attenuation, verification, third-party discharge,
serialization round-trips, and action bitmask parsing.

```sh
cargo test -p macaroon
```
