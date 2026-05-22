# Build Your First Pyana App: API Key Management Service

This tutorial walks you through building a working API key management service
that demonstrates pyana's core value proposition: **token minting, attenuation,
offline verification, and revocation** — no ZK proofs required.

You will build a service where:
- An admin mints a root API key (a capability token)
- The admin attenuates it for a specific customer (read-only, rate-limited, 24h expiry)
- The customer uses the attenuated key to access a protected endpoint
- The service verifies the key without contacting the admin (offline verification)
- The admin revokes the key and subsequent access is denied

## Prerequisites

- Rust 1.94+ (`rustup update stable`)
- A clone of the pyana repository:
  ```sh
  git clone https://github.com/pyana-dev/breadstuffs.git
  cd breadstuffs
  ```

## Create the project

From the repository root, create a new binary crate:

```sh
cargo new --name api-keys apps/api-keys
```

Replace `apps/api-keys/Cargo.toml` with:

```toml
[package]
name = "api-keys"
version = "0.1.0"
edition = "2024"

[dependencies]
pyana-sdk = { path = "../../sdk" }
token = { path = "../../token", default-features = false, features = ["macaroon", "datalog", "rand-deps"] }
blake3 = "1"
```

Now open `apps/api-keys/src/main.rs` and follow along.

---

## Step 1: Mint a root API key

The admin creates a wallet and mints an unrestricted root token for the
`"api"` service. This root token has full permissions — it is the master key.

```rust
use pyana_sdk::{AgentWallet, Attenuation, AuthRequest};
use pyana_token::{BudgetSpec, RevocationFilter};

fn main() {
    // The admin's 32-byte root secret. In production, generate this once and
    // store it in a secrets manager. Anyone with this key can forge tokens.
    let root_key: [u8; 32] = *blake3::hash(b"my-api-service-root-secret").as_bytes();

    // Create the admin's wallet and mint a root token.
    let mut admin_wallet = AgentWallet::new();
    let root_token = admin_wallet.mint_token(&root_key, "api");

    println!("Root token minted:");
    println!("  ID:      {}", root_token.id);
    println!("  Service: {}", root_token.service);
    println!("  Can mint: {}", root_token.can_mint());
```

The root token is an HMAC-chained macaroon. It grants unrestricted access to
the `"api"` service and can be attenuated into narrower tokens.

**Expected output:**
```
Root token minted:
  ID:      api:0
  Service: api
  Can mint: true
```

---

## Step 2: Attenuate for a customer

The admin creates a restricted key for a customer: read-only access,
rate-limited to 1000 requests per day, expiring in 24 hours.

```rust
    // Current time (Unix seconds). In production, use SystemTime::now().
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64;

    // Attenuate: read-only, 24h expiry, 1000 req/day budget.
    let customer_token = admin_wallet.attenuate(&root_token, &Attenuation {
        services: vec![("api".into(), "r".into())],  // read-only
        not_after: Some(now + 86_400),               // expires in 24h
        budget: Some(BudgetSpec {
            id: "customer-42:daily".into(),
            parent_id: None,
            class: "api_calls".into(),
            limit: 1000,
            window: Some("1d".into()),
        }),
        confine_user: Some("customer-42".into()),
        ..Default::default()
    }).expect("attenuation should succeed");

    println!("\nCustomer token created:");
    println!("  ID:       {}", customer_token.id);
    println!("  Can mint: {}", customer_token.can_mint());
    println!("  Service:  {}", customer_token.service);
```

Attenuation is one-way: the customer token is strictly weaker than the root.
The customer cannot remove the restrictions or widen permissions. No round-trip
to the admin is needed to create or verify this token.

**Expected output:**
```
Customer token created:
  ID:       api:0:att:1
  Can mint: false
  Service:  api
```

---

## Step 3: Verify at the edge (offline)

A downstream service verifies the customer's token against an `AuthRequest`.
This check runs entirely locally — no network call, no token introspection
endpoint, no shared Redis.

```rust
    // Simulate the customer presenting their key to a protected endpoint.
    let request = AuthRequest {
        service: Some("api".into()),
        action: Some("read".into()),
        user_id: Some("customer-42".into()),
        now: Some(now + 3600), // 1 hour after issuance (still valid)
        ..Default::default()
    };

    // The edge service verifies locally. It needs only the token — no
    // contact with the admin, no database lookup.
    let authorized = admin_wallet.verify_token(&customer_token, &request);
    println!("\nVerification (read, 1h after mint): {}", authorized);
    assert!(authorized, "read access should be granted");

    // Attempt a write — should be denied (token is read-only).
    let write_request = AuthRequest {
        service: Some("api".into()),
        action: Some("write".into()),
        user_id: Some("customer-42".into()),
        now: Some(now + 3600),
        ..Default::default()
    };
    let write_denied = !admin_wallet.verify_token(&customer_token, &write_request);
    println!("Verification (write attempt):      denied={}", write_denied);
    assert!(write_denied, "write access should be denied");

    // Attempt access after expiry — should be denied.
    let expired_request = AuthRequest {
        service: Some("api".into()),
        action: Some("read".into()),
        user_id: Some("customer-42".into()),
        now: Some(now + 100_000), // well past the 24h window
        ..Default::default()
    };
    let expired_denied = !admin_wallet.verify_token(&customer_token, &expired_request);
    println!("Verification (expired, +100000s):  denied={}", expired_denied);
    assert!(expired_denied, "expired access should be denied");
```

All three checks execute in microseconds with zero I/O. The verifier needs only
the token string and the root key to validate the HMAC chain and evaluate caveats.

**Expected output:**
```
Verification (read, 1h after mint): true
Verification (write attempt):      denied=true
Verification (expired, +100000s):  denied=true
```

---

## Step 4: Revoke the key

The admin adds the customer token's ID to a revocation filter. Any subsequent
verification that checks revocation status will reject the token.

```rust
    // Create a revocation filter (in production, this lives on your edge servers
    // and is synced periodically from a central revocation list).
    let revocation_filter = RevocationFilter::new();

    // Revoke the customer's token by its ID.
    revocation_filter.revoke(&customer_token.id);
    println!("\nRevoked token: {}", customer_token.id);
    println!("Revocation filter size: {}", revocation_filter.revoked_count());

    // Check revocation status before authorizing.
    let is_revoked = revocation_filter.is_revoked(&customer_token.id);
    println!("Is revoked: {}", is_revoked);
    assert!(is_revoked);

    // The full authorization check: verify caveats AND check revocation.
    let caveat_ok = admin_wallet.verify_token(&customer_token, &request);
    let final_decision = caveat_ok && !revocation_filter.is_revoked(&customer_token.id);
    println!("Final authorization (post-revocation): {}", final_decision);
    assert!(!final_decision, "revoked token must be denied");

    // Other tokens remain unaffected.
    let other_token = admin_wallet.attenuate(&root_token, &Attenuation {
        services: vec![("api".into(), "r".into())],
        confine_user: Some("customer-99".into()),
        ..Default::default()
    }).unwrap();

    let other_ok = admin_wallet.verify_token(&other_token, &AuthRequest {
        service: Some("api".into()),
        action: Some("read".into()),
        user_id: Some("customer-99".into()),
        now: Some(now + 3600),
        ..Default::default()
    }) && !revocation_filter.is_revoked(&other_token.id);
    println!("Other customer (not revoked):        {}", other_ok);
    assert!(other_ok);

    println!("\n--- All checks passed. ---");
}
```

The `RevocationFilter` is a cuckoo filter: O(1) lookups, zero false negatives,
sub-0.1% false positive rate. It can be serialized to bytes and distributed to
edge servers. Revocation propagation is as fast as your sync mechanism (push via
websocket, pull every N seconds, etc.) — no consensus required at this level.

**Expected output:**
```
Revoked token: api:0:att:1
Revocation filter size: 1
Is revoked: true
Final authorization (post-revocation): false
Other customer (not revoked):        true

--- All checks passed. ---
```

---

## Complete source

Here is the full `main.rs` in one copy-pasteable block:

```rust
use pyana_sdk::{AgentWallet, Attenuation, AuthRequest};
use pyana_token::{BudgetSpec, RevocationFilter};

fn main() {
    let root_key: [u8; 32] = *blake3::hash(b"my-api-service-root-secret").as_bytes();

    let mut admin_wallet = AgentWallet::new();
    let root_token = admin_wallet.mint_token(&root_key, "api");

    println!("Root token minted:");
    println!("  ID:      {}", root_token.id);
    println!("  Service: {}", root_token.service);
    println!("  Can mint: {}", root_token.can_mint());

    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64;

    let customer_token = admin_wallet.attenuate(&root_token, &Attenuation {
        services: vec![("api".into(), "r".into())],
        not_after: Some(now + 86_400),
        budget: Some(BudgetSpec {
            id: "customer-42:daily".into(),
            parent_id: None,
            class: "api_calls".into(),
            limit: 1000,
            window: Some("1d".into()),
        }),
        confine_user: Some("customer-42".into()),
        ..Default::default()
    }).expect("attenuation should succeed");

    println!("\nCustomer token created:");
    println!("  ID:       {}", customer_token.id);
    println!("  Can mint: {}", customer_token.can_mint());
    println!("  Service:  {}", customer_token.service);

    let request = AuthRequest {
        service: Some("api".into()),
        action: Some("read".into()),
        user_id: Some("customer-42".into()),
        now: Some(now + 3600),
        ..Default::default()
    };

    let authorized = admin_wallet.verify_token(&customer_token, &request);
    println!("\nVerification (read, 1h after mint): {}", authorized);
    assert!(authorized);

    let write_request = AuthRequest {
        service: Some("api".into()),
        action: Some("write".into()),
        user_id: Some("customer-42".into()),
        now: Some(now + 3600),
        ..Default::default()
    };
    let write_denied = !admin_wallet.verify_token(&customer_token, &write_request);
    println!("Verification (write attempt):      denied={}", write_denied);
    assert!(write_denied);

    let expired_request = AuthRequest {
        service: Some("api".into()),
        action: Some("read".into()),
        user_id: Some("customer-42".into()),
        now: Some(now + 100_000),
        ..Default::default()
    };
    let expired_denied = !admin_wallet.verify_token(&customer_token, &expired_request);
    println!("Verification (expired, +100000s):  denied={}", expired_denied);
    assert!(expired_denied);

    let revocation_filter = RevocationFilter::new();
    revocation_filter.revoke(&customer_token.id);
    println!("\nRevoked token: {}", customer_token.id);
    println!("Revocation filter size: {}", revocation_filter.revoked_count());

    let is_revoked = revocation_filter.is_revoked(&customer_token.id);
    println!("Is revoked: {}", is_revoked);
    assert!(is_revoked);

    let caveat_ok = admin_wallet.verify_token(&customer_token, &request);
    let final_decision = caveat_ok && !revocation_filter.is_revoked(&customer_token.id);
    println!("Final authorization (post-revocation): {}", final_decision);
    assert!(!final_decision);

    let other_token = admin_wallet.attenuate(&root_token, &Attenuation {
        services: vec![("api".into(), "r".into())],
        confine_user: Some("customer-99".into()),
        ..Default::default()
    }).unwrap();

    let other_ok = admin_wallet.verify_token(&other_token, &AuthRequest {
        service: Some("api".into()),
        action: Some("read".into()),
        user_id: Some("customer-99".into()),
        now: Some(now + 3600),
        ..Default::default()
    }) && !revocation_filter.is_revoked(&other_token.id);
    println!("Other customer (not revoked):        {}", other_ok);
    assert!(other_ok);

    println!("\n--- All checks passed. ---");
}
```

Run it:

```sh
cargo run -p api-keys
```

---

## What you just built

| Concern | How pyana handles it |
|---------|---------------------|
| **Key issuance** | `AgentWallet::mint_token()` — one line, one HMAC key |
| **Scope restriction** | `Attenuation` struct — services, actions, expiry, budget, user binding |
| **Offline verification** | `verify_token()` — local HMAC chain check, sub-microsecond |
| **Revocation** | `RevocationFilter` — O(1) cuckoo filter, zero false negatives |
| **No central authority at verify time** | The verifier never contacts the issuer |

This is pyana at trust level 0-1 (see `docs/web2-trust-integration.md`). No
ZK circuits, no federation consensus, no blockchain. Just HMAC keys and
Ed25519 signatures on commodity hardware.

---

## What's next

From this foundation you can progressively escalate trust guarantees:

1. **Add ZK privacy** — Use `wallet.authorize(&token, &request, VerificationMode::FullyPrivate)`
   to prove authorization without revealing the token contents or delegation
   chain to the verifier. The verifier learns only "authorized: yes/no."

2. **Add federation** — Deploy a `SiloServer` for BFT-ordered revocations.
   Edge servers sync the attested revocation root periodically. Revocation
   becomes tamper-evident and consensus-backed.

3. **Add selective disclosure** — Use `VerificationMode::SelectiveDisclosure`
   to reveal only specific facts (e.g., "service=api" but not "user=customer-42")
   while proving the rest in zero knowledge.

4. **Delegate to sub-agents** — Use `wallet.delegate(&token, &recipient_pubkey, &restrictions)`
   to hand an attenuated token to another agent. They can present it, further
   attenuate it, but never widen it.

5. **Add third-party caveats** — Require a discharge from an MFA gateway before
   the token is valid. See `sdk/src/discharge.rs` for the pattern.

Each upgrade is additive. Your existing tokens, verification logic, and
revocation infrastructure continue to work unchanged.
