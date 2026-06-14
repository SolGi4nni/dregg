# dregg-auth

**Capability tokens with machine-checked attenuation semantics.**

A credential is a small signed object that names exactly what it permits, as a
list of *caveats*. Holding one is the authority; narrowing one is appending a
caveat; verifying one is checking a signature chain and evaluating the caveats
against the request — offline, deterministically, with nothing but the
issuer's public key. The semantics of every operation — *attenuation only ever
narrows*, *verification is the fail-closed meet of all caveats*, *an unbound
third-party discharge is rejected*, *a discharge bound to one credential
cannot be replayed against another* — are the ones proven in the Lean
development under `metatheory/Dregg2/`, and each API surface names its Lean
counterpart in its doc comment. The same tokens settle on dregg if you ever
want a ledger; nothing here requires one.

## The credential core (`dregg_auth::credential`)

```rust
use dregg_auth::credential::{Caveat, Context, Credential, Pred, RootKey};

let root = RootKey::generate();          // ed25519; publish root.public()

// Mint: may use the `read` tool, until clock 2_000.
let cred = root.mint([
    Caveat::FirstParty(Pred::AttrEq { key: "tool".into(), value: "read".into() }),
    Caveat::FirstParty(Pred::NotAfter { at: 2_000 }),
]);

// Hand a sub-agent strictly less: attenuate appends caveats — the ONLY
// mutation there is. No API removes one; the signature chain + the
// proof-of-possession check make removal unforgeable on the wire.
let narrowed = cred.attenuate([Caveat::FirstParty(Pred::NotAfter { at: 1_500 })]);

// `dga1_…` — compact postcard bytes, base64url, header-safe, versioned by prefix.
let encoded = narrowed.encode();

// Verify OFFLINE: public key + caller-supplied request facts. Same context,
// same verdict — the clock is an explicit input, never wall-time.
let presented = Credential::decode(&encoded).unwrap();
let ctx = Context::new().at(1_400).attr("tool", "read");
assert!(presented.verify(&root.public(), &ctx).is_ok());

// Refusals carry their terms:
let late = Context::new().at(1_600).attr("tool", "read");
println!("{}", presented.verify(&root.public(), &late).unwrap_err());
// refused: block 1 requires not after clock 1500 (expiry gate)

// Tokens explain themselves:
println!("{}", presented.explain());
// credential (2 block(s))
//   block 0 (root grant): requires attribute `tool` = `read`; requires not after clock 2000 (expiry gate)
//   block 1 (attenuation): requires not after clock 1500 (expiry gate)
//   [tail 9f2c…]
```

### The caveat language

Every shape is a proven one; doc comments cite the Lean names. The composition
layer is a real Boolean algebra (`Dregg2.Exec.PredAlgebra.Pred`), fail-closed:
`AnyOf([])` refuses, and a caveat that mentions data the context does not bind
is a refusal — never `false`, so `Not` can never turn missing data into
authority.

| caveat | meaning | Lean counterpart |
|---|---|---|
| `Pred::AttrEq` | attribute equals value | `SimpleConstraint.fieldEquals` (Exec/Program.lean) |
| `Pred::AttrPrefix` | attribute starts with prefix | `SimpleConstraint.prefixOf` |
| `Pred::NotBefore` | vesting gate (upward-closed) | `TemporalAtom.afterHeight` (Authority/TemporalAlgebra.lean) |
| `Pred::NotAfter` | expiry gate (downward-closed) | `TemporalAtom.beforeHeight` |
| `Pred::Within` | validity window = meet of the two | `TemporalAtom.withinWindow` |
| `Pred::AllOf` / `AnyOf` / `Not` / `True` / `False` | Boolean composition | `Pred.allOf`/`anyOf`/`not`/`tt`/`ff` (Exec/PredAlgebra.lean) |
| `Caveat::FirstParty` | a local predicate | `Caveat.local` (Authority/Caveat.lean) |
| `Caveat::ThirdParty` | requires a gateway's discharge | `Caveat.thirdParty` + Authority/MacaroonDischarge.lean |

### Third-party caveats

A `Caveat::ThirdParty` names a gateway's public key and a caveat id; the
credential then only admits when the context presents a [`Discharge`] — the
gateway's own signed object, carrying its own conditions (an expiry on the
approval, say) and **bound** to the exact credential it discharges (the BLAKE3
hash of the credential's tail). The binding discipline is the proven macaroon
one: an unbound discharge is rejected unconditionally
(`unbound_discharge_rejected`), and a discharge bound to one credential is
rejected against any other (`binding_not_replayable_to_other_root`) — so
"strip the caveats, reuse the old approval" is not an attack, it's a refusal.

```rust,ignore
let d = gateway.discharge(caveat_id, credential.tail(), [Pred::NotAfter { at: 600 }]);
let ctx = Context::new().at(500).attr("tool", "read").discharge(d);
credential.verify(&root.public(), &ctx)?;
```

### Wire format

Postcard (compact, canonical for the fixed schema) under a version prefix,
base64url with no padding: credentials are `dga1_…`, discharges `dgd1_…`. An
unknown prefix is an error, never a fallback. The encoded credential is a
**bearer** object: it carries the tail key (the right to present *and* to
attenuate further) — transmit it like the capability it is. Bindings
(sdk-py/sdk-ts) wrap these exact bytes; golden vectors live in `tests/`.

### Dependency surface

`ed25519-dalek`, `blake3`, `postcard`, `base64`, `serde`, `getrandom`. The
credential core touches no cell, turn, node, or circuit code.

## The agent-grant surface (`policy`, CLI, verifying middleware)

The product wedge — the `dregg-auth` CLI, the grant builder, and the verifying
middleware — rides the **proven** credential core directly (`dregg_auth::policy`).
The token a grant issues *is* a machine-checked [`Credential`] (the `dga1_…`
form); the decision the gate makes *is* `Credential::verify`. So the headline
claim — *prove your agent cannot exceed the grant* — holds on the path a
stranger actually touches.

```rust
use dregg_auth::policy::{Grant, Policy, Verifier, Call};

let polis = Policy::generate();                       // keep the secret; publish the public key
let token = polis.issue(
    Grant::to("ci-bot").tools(["read", "pr-create"]).until(1_900_000_000),
).unwrap().encode();                                  // a proven `dga1_…` bearer token

// A gateway holding ONLY the public key admits/denies each tool call, offline:
let gate = Verifier::new(polis.public_key_hex());
assert!( gate.admit(&token, &Call::tool("read").at(1_800_000_000)).admitted());
assert!(!gate.admit(&token, &Call::tool("delete-repo").at(1_800_000_000)).admitted());
```

A grant `Grant::to("ci-bot").tools(["read","pr-create"]).until(t)` compiles to
three first-party caveats on the root block: `subject == "ci-bot"` (the agent
identity, pinned as a *checked* fact the `Verifier` binds from the token
itself), `tool ∈ {read, pr-create}` (the allowlist as the fail-closed
disjunction `AnyOf`), and `clock ≤ t` (the expiry, downward-closed). Narrowing
appends a confining block — dropped reach is gone for good (the proven
`attenuate_narrows`). Every decision is the fail-closed meet of all caveats, and
a denial names the violated caveat.

```console
$ dregg-auth init
$ dregg-auth grant ci-bot --tools read,pr-create --until friday
dga1_QdTp6HNgZxrvii5Ftf6m_x2nlQ...
$ dregg-auth verify dga1_QdTp... --tool delete-repo
refused: block 0 requires any of (attribute `tool` = `read`; attribute `tool` = `pr-create`)
$ dregg-auth gate dga1_QdTp... --tool pr-create --args repo=acme/widgets
ALLOW subject=ci-bot tool=pr-create [repo=acme/widgets] :: allowed
```

`--until` / `--at` accept a unix timestamp, a relative offset (`+7d`/`+24h`/
`+90m`/`+2w`), or a friendly day name (`friday`, `tomorrow`, `eod`, `eow`),
resolved against the wall clock at issue. `explain <token>` prints the grant's
terms block by block (the cold-reader audit).

The first-cut Datalog surface (`Root`/`Grant`/`Token`, the `eb2_` biscuit path,
and the `mcp::OfflineGate` gate built on it) remains in the library for
back-compat; the `policy` surface above is the product, and it is the proven
one.

## Honest residuals

- **Rate limiting is advisory**: verification is stateless and offline, so it
  cannot count requests. The grant surface records the intent (rate metadata)
  for a stateful gate to enforce; the `policy` surface is over tools + time.
- **Revocation** is expiry-shaped here: short windows + re-issue. (Third-party
  caveats give online revocation when you want it: a gateway that stops
  discharging has revoked.)
