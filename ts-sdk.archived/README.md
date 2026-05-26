# ts-sdk — ARCHIVED 2026-05-25

This package has been superseded by `../sdk-ts/` (`@dregg/sdk`).

## Why it was archived

`ts-sdk/` was a separate codebase that shared the `@dregg/sdk` package name but had no
WASM coupling. It modelled high-level CapTP, routing, governance, storage, and effects
client shapes as pure TypeScript interfaces — with no binding to `dregg-wasm`.

`sdk-ts/` is the canonical package. It wraps `dregg-wasm` directly, provides typed
wrappers for all WASM exports (`DreggRuntime`, `AgentCipherclerk`, `ProofEngine`,
`MerkleTree`, `PredicateEvaluator`, and the full peer-exchange / federation / delegation
graph surface added in the Refactor 3-7 wave), and is the package the Studio and
browser playground reference.

## If you need the types here

The abstract client interface types in `ts-sdk/src/` (CapTP refs, routing, governance,
effects, storage) may still be useful as design reference when building the network-layer
client over `sdk-ts`. They were never wired to a real transport, so nothing should
`import` from this package in production code.

## Canonical location

Source: `../sdk-ts/`
Package name: `@dregg/sdk`
