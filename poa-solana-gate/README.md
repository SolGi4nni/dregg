# PoA Solana `$DREGG` holding gate

An isolated server-side admission boundary for
`XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump`.

It has no HTTP framework dependency and deliberately does not define another
Solana verifier. It composes:

- `dregg_bridge::solana_holdings` for SPL decoding and holding types;
- `dregg_bridge::solana_feed` for the consensus-verified upgrade;
- `dregg_governance::holding_weight` for the existing owner-binding message;
- `dregg_pay::watcher::FetchedAccount` for the live account seam.

This crate does not implement HTTP or choose an RPC client. The production-shaped
beta adapter now lives in `node/src/poa_holding_api.rs`; other embedding servers
must perform the same two RPC calls and convert their responses into the narrow
`RpcHoldingSource` seam:

1. `getGenesisHash` and compare it with the configured cluster genesis hash.
2. `getTokenAccountsByOwner(wallet, { mint }, { commitment: "finalized",
   encoding: "base64", minContextSlot })`.

The mint's finalized mainnet account owner is pinned to Token-2022
(`TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb`), not legacy `Tokenkeg…`.

It converts the response to `RpcAccountSet`, then calls `validate_rpc_snapshot`
and `Gate::admit_beta`. The gate verifies the existing Dregg `OwnerBinding` signature
whose voter id is the SHA-256 commitment to the exact PoA challenge, consumes the
nonce, and returns a short-lived one-use `HoldingCapability`.

The server, not the browser, generates the nonzero 32-byte nonce with a CSPRNG.
Production must provide a durable `AdmissionStore` whose issue/consume operations
are atomic. The included in-memory store is only for tests and local development.
It records both issued and spent receipt IDs, so a never-issued ID is rejected as
forged and a previously issued-and-spent ID is rejected as replayed.

## Node HTTP integration

The node exposes three strict routes when its federation is configured and
`DREGG_POA_SOLANA_RPC_URL` names an HTTPS endpoint:

- `POST /api/poa/holding/challenge` with only `{ "wallet": "<base58>" }`;
- `POST /api/poa/holding/verify` with only the issued challenge id and wallet
  signature;
- `GET /api/poa/holding/status/{receipt_id}`.

On `beta.pathofangels.network` the browser reaches those routes through the
same-origin `/node/api/poa/holding/*` proxy. Challenge and capability state is
stored durably, pruned after expiry, and bounded. Capability/status responses
omit the observed balance and explicitly carry `governance_weight_bearing:
false`. A crash between consuming a challenge and saving its capability burns
that challenge fail-closed; the player requests a fresh one.

## Trust boundary

This proves wallet control cryptographically. `BetaRpcAttested` balance is
authoritative only relative to the configured RPC endpoint (or RPC quorum
adapter): ordinary Solana JSON-RPC does not include a consensus accounts-inclusion
proof. `finalized` and a named response slot prevent rollback/stale-context
mistakes, but do not make a malicious RPC honest. Beta credentials are suitable
for arcade access and never enter `grant_weight`; that existing API rejects
`StructureOnly`. `verify_consensus_source` is the separate upgrade through the
existing anchored `solana_feed` pipeline.

## Primary references

- [Solana `getTokenAccountsByOwner`](https://solana.com/docs/rpc/http/gettokenaccountsbyowner)
  defines the owner/mint filter, `minContextSlot`, commitment, and contextual slot.
- [Solana `getGenesisHash`](https://solana.com/docs/rpc/http/getgenesishash)
  supplies the cluster identity checked by the adapter.
- [Solana transaction structure](https://solana.com/docs/core/transactions/transaction-structure)
  specifies Ed25519 signatures over serialized message bytes; PoA uses the same
  raw Ed25519 wallet key with Dregg's existing domain-separated owner binding.
- [Solana RPC commitment](https://solana.com/docs/rpc#configuring-state-commitment)
  defines `finalized`; it is a finality selection, not an account-inclusion proof.
- [Anza Solana Kit](https://github.com/anza-xyz/kit) exposes wallet-byte
  `signBytes`/`verifySignature`, matching this gate's exact-byte signing boundary.
