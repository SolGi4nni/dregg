# dregg-auth

**Prove your agent cannot exceed the grant.**

Agents are being handed unscoped API keys today — MCP servers ship them straight
into environment variables, sub-agents inherit everything their parent can do, CI
bots run with the keys to the kingdom. dregg-auth is the aspirin: **scoped,
time-boxed, delegatable, revocable, auditable** agent access as a one-liner — and
the permission check is **verified offline, with nothing but a public key.**

No node. No wallet. No blockchain. No ontology. The whole point of L1 is that a
stranger can drop it in front of an agent in 60 seconds and *prove* the blast
radius is bounded.

## 60-second quickstart

```console
# 1. Create a root authority. Keep the private half; publish the public half.
$ dregg-auth init
root key written to ~/.dregg-auth/root.key
public key (publish this):
ed25519/8f3a...c1

# 2. Grant an agent exactly two tools, expiring in a week, at 30 calls/hour.
$ dregg-auth grant ci-bot --tools read,pr-create --until +7d --rate 30/h
eb2_CoYBCh0...   # a printable token — hand this to the agent

# 3. The gateway holds ONLY the public key. Verify a call — offline.
$ dregg-auth verify eb2_CoYBCh0... --tool pr-create
allowed (matched policy_0)
$ echo $?
0

# 4. A tool that was never granted is refused — with a reason.
$ dregg-auth verify eb2_CoYBCh0... --tool delete-repo
denied: tool `delete-repo` (action `use`) is outside this grant, or the grant has expired
$ echo $?
1
```

## Attenuation never amplifies

Hand a sub-agent strictly less than you hold. A token narrowed to `read` can
**never** regain `pr-create` — that's a structural property of the underlying
biscuit chain, not a policy you have to trust us to enforce.

```console
$ dregg-auth attenuate eb2_CoYBCh0... --tools read
eb2_CoYB...narrowed...

$ dregg-auth verify eb2_CoYBCh0...narrowed... --tool pr-create
denied: tool `pr-create` (action `use`) is outside this grant, or the grant has expired
```

## The MCP gateway profile

`gate` is the middleware shape: verify-or-deny each incoming tool call and emit a
receipt line (the audit seed). It depends on **nothing but this crate** — the
node's MCP layer can later implement the `ToolGate` trait to slot it in.

```console
$ dregg-auth gate eb2_CoYBCh0... --tool pr-create --args repo=acme/widgets
ALLOW subject=ci-bot tool=pr-create [repo=acme/widgets] :: allowed (matched policy_0)
```

```rust
use dregg_auth::mcp::{OfflineGate, ToolCall, ToolGate};

let gate = OfflineGate::new(public_key_hex);            // public key only
let gated = gate.admit(&agent_token, &ToolCall::new("pr-create").arg("repo", "acme/widgets"));
if gated.admitted() {
    dispatch_tool();
}
log::info!("{}", gated.receipt.line());                // or .json() for structured ingest
```

## Library API

```rust
use dregg_auth::{Root, Grant, Request, verify_offline};

let root = Root::generate();                            // an ed25519 issuer
let token = root.issue(
    &Grant::new("ci-bot").tools(["read", "pr-create"]).until(1_900_000_000),
)?;
let encoded = token.encode()?;                          // printable `eb2_...`

// Anyone holding ONLY the public key decides — offline:
let decision = verify_offline(&encoded, &root.public_key_hex(),
                              &Request::tool("read"));
assert!(decision.allowed());
# Ok::<(), dregg_auth::AuthError>(())
```

| Verb         | What it does                                                        |
| ------------ | ------------------------------------------------------------------- |
| `Root`       | the issuing ed25519 authority (`generate`, `from_private_hex`)      |
| `Grant`      | the fluent permission builder (`tools`, `until`, `rate`, `actions`) |
| `Root::issue`| sign a grant into a printable `Token`                               |
| `Token::attenuate` | narrow a token — never amplify                                |
| `verify_offline` | public-key-only allow/deny + a human reason                    |
| `mcp::OfflineGate` | the standalone MCP gateway profile + receipts                |

## The adoption-quotient commitment

L1 is **standalone, forever**. The dependency surface is `dregg-token` (its
biscuit / ed25519 / Datalog feature only) plus `biscuit-auth`. No `dregg-node`,
no `dregg-turn`, no `dregg-circuit`. The polis is **pull, never toll**: when
you're ready for receipts-as-a-chain, light-client verification, and proofs, the
upgrade path is there — but you never pay for it to start.

## Honest residuals (v0)

- **Rate limiting is advisory at L1.** L1 is stateless and offline, so it cannot
  itself count requests; the rate rides into the token as metadata and is
  surfaced in receipts for a stateful L2 gate to enforce.
- **Revocation is not yet wired** into the CLI. The token layer has a revocation
  registry (`dregg-token`'s `rand-deps` feature); L1 deliberately omits it to keep
  the offline path pure. Short expiries are the L1 revocation story; explicit
  revocation is an L2 concern.
- **`--until` accepts unix timestamps and `+<n><unit>` offsets** (`+7d`, `+24h`).
  Named dates ("friday") are a future ergonomic.
- **The compile-time dependency surface is fatter than the adoption-quotient
  target — for now.** The *runtime* path is genuinely standalone: verification is
  pure, offline, and touches no node/network/circuit code. But `dregg-auth`
  builds on `dregg-token`, and `dregg-token` *unconditionally* depends on
  `dregg-commit → dregg-circuit` (a transitive edge baked into the token crate
  today, not gated behind a feature). So a `cargo tree` shows the plonky3 circuit
  crates compiling, even though none of them run. **The clean fix is a one-line
  refactor in the token crate**: make `dregg-token`'s `dregg-commit`/`dregg-circuit`
  edge feature-gated (it is only needed by the macaroon zkvm + selective-
  disclosure paths, never by the biscuit offline path). Until that lands,
  dregg-auth keeps the *guarantee* (offline, public-key-only, no-amplify) while
  carrying a heavier build than the two-dependency promise. Tracked as the W4
  follow-up; deliberately not done here to keep this lane new-files-only and
  collision-free with other marathon lanes.
