# Infrastructure Applications of `dregg` Capabilities

## What Exists Today

`dregg`'s core provides: capability sets (c-lists with slot-based lookup), attenuation-only delegation (`is_narrower_or_equal` enforcement), expiry heights on capability refs, breadstuff token-hash authentication, preconditions (nonce, balance, block height, time range), ZK proof authorization, and macaroon-style caveats (org, service, feature, validity window, machine binding, budget, revocation). The executor enforces all of this atomically with journal rollback.

The key primitives for infrastructure use:
- `CapabilityRef` with `target`, `permissions`, `breadstuff`, `expires_at`
- `CapabilitySet::attenuate()` -- monotone narrowing, never amplification
- `AuthRequired::{None, Signature, Proof, Either, Impossible}` per-action permission model
- `dregg` caveats: `FromMachine`, `Service`, `Command`, `ValidityWindow`, `FeatureGlob`, `Budget`
- Preconditions: time ranges, block height bounds, state assertions
- Revocation channels for capability invalidation without full re-issuance

## 1. Docker Container Permissions

**Model:** Each container gets a cell with a capability set scoped to its authorized resources. A CI/CD controller cell holds broad capabilities and attenuates them per-container.

**Integration:** The controller issues a breadstuff token to the container cell with caveats: `Service("registry.internal", "r")`, `FromMachine("ci-runner-7")`, `ValidityWindow(job_start, job_start + 3600)`, `FeatureGlob(include: ["secrets/project-x/*"], exclude: ["secrets/project-y/*"])`. The container presents this token to each service endpoint. Each service verifies the macaroon chain and checks its own caveat (service name match). The container cannot forge a token for another service because it lacks the HMAC key to extend the chain, and it cannot widen scope because caveats only attenuate.

**Privacy property:** The registry sees "valid token, grants read access to registry.internal" but not that the container also has access to secrets/project-x. Each service sees only the dimension relevant to it.

**What needs building:** A container runtime hook that mints a cell and breadstuff token at container start, injects it as an env var or mounted secret, and revokes on container exit. An OCI hook (~200 LOC) that calls the dregg SDK.

## 2. Filesystem ACLs with Attenuation

**Model:** Map filesystem paths to `FeatureGlob` caveats. A parent process holds `FeatureGlob(include: ["/data/project-x/**"])`. It attenuates to a child: `FeatureGlob(include: ["/data/project-x/results/**"])`. The child further delegates to a tool: `FeatureGlob(include: ["/data/project-x/results/*.csv"], exclude: ["/data/project-x/results/*.key"])`.

**Integration:** A FUSE layer or eBPF-based LSM hook intercepts open/read/write syscalls. The process presents its dregg token. The hook decodes caveats, checks the requested path against glob patterns. Since caveats are append-only (monotone narrowing), a child can only make the glob MORE restrictive -- it cannot widen `/results/**` back to `/data/**`.

**What exists:** The `FeatureGlob` caveat with include/exclude and globset matching is fully implemented. The `verify_caveats` function handles subset enforcement.

**What needs building:** A filesystem enforcement layer (FUSE shim or LSM module) that calls into the token verification path. Approximately a FUSE daemon wrapping `verify_caveats` with path-as-feature mapping.

## 3. Multi-Tenant Cloud with Privacy

**Model:** Org A holds a capability targeting Org B's API cell. Org A's workload presents a ZK proof (Authorization::Proof) that it holds a valid capability chain to Org B's endpoint. The cloud provider routes the request based on proof validity alone -- it sees `AuthRequired::Proof` passed, routes to Org B, but cannot extract which endpoint or what permissions from the proof.

**Integration:** The provider runs a verifier-only executor (no state, just proof checking against attested roots). Org A's workload generates a proof offline using the circuit crate. The proof's public inputs bind to the destination cell ID and action, but the witness (capability chain, delegation path) remains hidden.

**What exists:** `Authorization::Proof` with `bound_action` and `bound_resource` fields. The executor's `verify_zk_proof` path. The circuit crate's STARK prover for membership and derivation proofs.

**What needs building:** A "verifier-only routing mode" for the executor where it checks proof validity and routes without maintaining full ledger state. This is architecturally close to the existing `validate_without_apply` path but would need to accept proof-only authorization without ledger lookup.

## 4. Service Mesh Authorization

**Model:** Replace mTLS identity with capability tokens. Service A calls Service B by presenting a breadstuff token with caveats: `Service("payments-api", "rw")`, `Command("charge")`, `ValidityWindow(now, now+300)`. The mesh sidecar verifies the token chain. No SPIFFE ID needed -- authorization is the token, not the caller's identity.

**Unlinkability:** With ZK mode, Service A proves it holds a valid capability chain to `payments-api:charge` without revealing which service it is. The mesh sees "authorized caller for payments-api:charge" but cannot link requests across time or correlate with other service calls.

**Integration point:** Envoy/gRPC interceptor that extracts the dregg token from metadata, calls `verify_caveats`, and returns allow/deny. The `FromMachine` caveat can optionally pin to a specific pod for defense-in-depth without breaking unlinkability at the service level.

**What needs building:** A sidecar library (envoy WASM filter or gRPC interceptor) wrapping the token crate's verification. The token verification is already a pure function -- packaging it for sidecar use is integration work, not protocol work.

## 5. Kubernetes RBAC Replacement

**Model:** Instead of "user X has role Y which maps to verbs on resources," issue capability tokens: `Service("pods", "r"), FeatureGlob(include: ["namespace/team-a/**"]), ValidityWindow(now, now+8h), Budget("team-a:daily", "api_calls", 1000, "1d")`. The token IS the permission. No ClusterRoleBinding lookup needed.

**What's gained:** Attenuation without cluster-admin intervention (a team lead narrows their token for a CI bot). Time-bounded access without CronJobs deleting RoleBindings. Budget enforcement (rate limiting baked into the token). Offline verification -- a kubectl plugin can check its own token validity without hitting the API server.

**Integration story:** A webhook admission controller or API server authenticator that accepts dregg tokens as bearer credentials. Maps caveat verification results to Kubernetes allow/deny decisions. The `Budget` caveat handles rate limiting that currently requires separate tooling (OPA/Gatekeeper).

**What needs building:** An admission webhook (~500 LOC) that maps K8s resource/verb/namespace to dregg's service/action/feature-glob model. Token issuance tied to existing IdP via the `OAuthProvider` caveat.

## 6. The Semi-Trustless Cloud Vision

**Architecture:** Compute nodes run a verifier-only executor. They see proofs, check validity against attested roots, route requests. They never see the authorization topology (who delegated what to whom). Services authenticate via capability proofs. The orchestrator routes based on proof validity. Revocation propagates via federation roots (attested root updates contain revocation channel state).

**What exists today that enables this:**
- Federation consensus produces attested roots (trust anchor for offline verification)
- `RevocationChannelSet` for capability invalidation without re-issuance
- ZK proof authorization hides delegation chains from verifiers
- Cross-federation bridges for routing between trust domains
- `DelegatedRef` snapshots for offline capability evidence

**What's missing:**
- A "verifier-only node" mode that strips the executor to proof-checking + routing (no state application). Architecturally possible by removing Phase 2 from `TurnExecutor::execute` and keeping only authorization verification.
- Lightweight attested root distribution (currently assumes federation membership; a cloud would need a subscriber/observer mode).
- Proof generation latency for interactive use. Current STARK proofs are batch-oriented. Interactive authorization needs sub-100ms proof generation or precomputed proof caches.

**A dregg-native container runtime** would: (1) mint a cell per container at creation, (2) inject attenuated capability tokens scoped to declared resource needs, (3) run a verifier sidecar that gates all inter-container and external communication on token validity, (4) propagate revocation via attested root subscription rather than centralized policy push, (5) produce audit logs as turn receipts with Merkle-chained integrity.

The key insight: dregg's "private authorization, public execution" model maps directly to cloud infrastructure where the cloud provider (executor) processes requests but should not learn authorization topology. The provider sees "valid proof, apply this state transition" -- never "user X delegated to service Y which sub-delegated to container Z."
