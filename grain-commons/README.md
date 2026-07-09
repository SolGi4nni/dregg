# grain-commons

**The agent commons / grain app-store — package, publish, discover, rent, fork (with
pedigree), and hatch bounded sub-agent grains. Compose, don't reimplement: every load-bearing
guarantee is an existing proven dregg primitive wired into a market shape.**

| commons capability | composed primitive |
|---|---|
| `package` — sign & install | `sandstorm_bridge::{SpkBuilder, Spk, SpkManifest}` (App ID = signing key) |
| `registry` — the market | `sandstorm_bridge::{Umem, DataRoot}` listing cells + `GrainReceipt` reviews |
| `fork` — pedigree | `sandstorm_bridge::grain::{GrainBackup, restore_grain}` (re-witnessed root + owner attestation) |
| `hatchery` — genesis-agent | `dregg_sdk::hatchery_mint::MintedKind` + the `dga1_` powerbox cap rail |

## The four faces

1. **Package an agent** (`package.rs` — `publish` / `install`). An `AgentConfig` (cap bundle +
   budget + brain + roles) packaged as a real signed `.spk`. **Provenance IS the key**: the App
   ID is the author's Ed25519 signing key; `install` verifies the signature before it returns
   any config, so a single tampered byte yields **no installable grain**
   (`PackageError::Package`), and it cross-checks the signed manifest's facets against the
   embedded cap bundle (`ConfigManifestMismatch`).
2. **List & rent** (`registry.rs` — `GrainRegistry`). Listings are cells in a committed umem
   heap keyed by App ID; `discover` reads one back; `rent` prices a `RentQuote` bounded by the
   listing's `ListingTerms`; `review` is a receipted turn leaving a `GrainReceipt`. The registry
   root is its content commitment (order-free).
3. **Fork with pedigree** (`fork.rs` — `fork_from_package`). Restore a committed `/var` backup
   into a fresh grain under a new owner, minting a `Pedigree` Merkle path. Three teeth bound at
   mint: signature-verified author App ID, backup provably belongs to that app
   (`ProvenanceMismatch` + `data_root` re-witness), and — decisively — a valid OWNER SIGNATURE
   over `(app_id ‖ data_root)` (`BadBackupSignature`).
4. **Hatch bounded sub-agents** (`hatchery.rs` — `GenesisAgent`). Mint a `HatchedSubAgent` with
   a **forever-invariant** the executor re-evaluates on every turn of the child's life
   (`MintedKind::evaluate_transition` → a genuine `ConstraintViolated`), endowed with a **strict
   cryptographic attenuation** of the genesis agent's caps on the real `dga1_` powerbox rail.

## How it fits the economy

The registry's `RentQuote`/`ListingTerms` are **honestly a quote, not a lease** — no value
moves and nothing is funded here (`registry.rs` module docs). The numbers feed the REAL funded
lease (`hosted-lease::HostedLease` / `grain-fork::Grain::rent`); shipping a shadow lease that
pretends to hold funds is deliberately NOT done. That weld is the named reconcile once the
detached crates join one workspace.

## Honest limits

A `Pedigree` is a plain data record — `traces_to` is a bare field comparison, meaningful ONLY
because `fork_from_package` refuses to MINT a pedigree the fork does not genuinely descend from
(`a_hand_built_pedigree_is_not_authenticated_by_traces_to`). The two fork surfaces are not
duplicates: this crate forks the *hosting image* (provenance across owners); `grain-fork` forks
the *committed kernel mind* (divergence + proven stitch). The named weld is to make the backup's
`data_root` BE the mind's committed checkpoint root.

## Tests

```sh
cargo test -p grain-commons
```

`src/lib.rs::commons_e2e` walks the whole loop: author → package → list → rent → hatch a bounded
sub-agent → fork with pedigree.
