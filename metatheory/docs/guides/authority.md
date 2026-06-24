# Guide: The Authority / Capability / Caveat Model

*A newcomer's orientation to dregg's security core — capabilities as constructive knowledge, the
generative cap-graph, caveat chains (macaroons), third-party discharge, credentials/revocation, and
how the token gates the executor.*

See also: [`../NAVIGATION.md`](../NAVIGATION.md) · [`executor.md`](executor.md).

> ⚠ **Stale-link note (2026-06-24):** links into `../rebuild/` (e.g. `_AUTHORIZATION-COMPLETE.md`)
> are **dead** — that stratum was harvested into [`../HARVEST-KEEPERS.md`](../HARVEST-KEEPERS.md) and
> removed (it lives in git history). The Lean `file:line` pointers below remain valid; line numbers
> drift between commits, so grep the *theorem name* rather than trusting the `:NNN`.

---

## The one-sentence model

A capability in dregg is **constructive knowledge**: to *hold* one is to be able to **exhibit a
witness that verifies** — never merely to assert. Authority is *generative* (Miller's "only
connectivity begets connectivity") and *attenuating* (you can only narrow what you hold, never
amplify it). The token **gates the executor's admission** — authorization is enforced *inline on the
critical path*, not checked out-of-band.

## The base seam: `Predicate ⊣ Witness`

The whole model rests on a single verify/find adjunction (`Dregg2/Laws.lean`, `Spec/Guard.lean`):

- **`Predicate`** (trusted, decidable) ⊣ **`Witness`** (untrusted, opaque `find`). Soundness comes
  from *verification*, never from trusting the finder. The find side is `Laws.search_sound` —
  undecidable **by design** (it's the interface boundary, not a hole).
- **`Spec/Guard.lean`** unifies ONE verify/find seam over authorization, preconditions,
  state-constraints, and caveats: `firstParty | witnessed | all(∧) | any(OneOf ∨) | gnot`.
  `attenuate_narrows` is the **meet-semilattice** narrowing (not a Heyting residual) — attenuation
  can only shrink the admitted set. Legacy constraints/auths return as derived smart-constructors.

## The generative capability graph — `Spec/Authority.lean`, `Authority/Positional.lean`

The characteristically-capability part: the operations that *create* and *transfer* authority.

- **Generative:** introduce / amplify / mint / endow.
- **Restrictive:** attenuate / revoke.
- `gen_step_traces` — per-step non-forgeability: every authority edge traces to a prior edge (you
  cannot conjure connectivity from nothing).
- `Positional.lossy_attenuation_only:200` — crossing the vat boundary is *lossy*: permission
  survives, authority does not (you get a revocable forward, not the underlying cap).

This is the dregg face of `Metatheory/ConstructiveKnowledge.lean`'s `no_forge_step` +
`knowledge_no_free_copy`.

## Caveat chains (macaroons) — `Authority/CaveatChain.lean`

A macaroon is an HMAC-chained capability that anyone can *attenuate* (append a caveat) but no one can
*forge*:

| Theorem | `file:line` | Guarantees |
|---|---|---|
| `append_narrows` | `:230` | appending a caveat only shrinks what the macaroon admits. |
| `chain_unforgeable` | `:402` | under `MacKernel.unforgeable`, the chain can't be forged. |
| `forgery_requires_mac_query` | `:302` | any forgery reduces to an HMAC query (the reduction). |
| `honest_unforgeable` | `:468` | the honest MAC kernel *is* unforgeable (non-vacuity witness). |
| `collapse_not_unforgeable` | `:509` | a degenerate kernel is *refuted* — the assumption is load-bearing, not vacuous. |

The Rust `macaroon/` crate is the real HMAC fold, pinned relative to `MacUnforgeable`.

## Third-party discharge — `Authority/ThirdPartyDischarge.lean`

Caveats that must be satisfied by a *separate* discharge macaroon from a third party (the "ask the
auth server" pattern):

- `honest_discharge_accepted:275` — a valid, bound discharge is accepted.
- `stale_discharge_rejected:303` — a stale discharge is rejected (freshness).
- `unbound_discharge_rejected:317` — a discharge not bound to this macaroon is rejected
  (no cut-and-paste).

The Rust crate is `discharge-gateway/`; see also `Authority/{Discharge,MacaroonDischarge}.lean`.

## Credentials & revocation — `Authority/Credential.lean`

Verifiable credentials with a revocation set:

- `credential_verifies_iff_issued_and_not_revoked:155` — a credential verifies **iff** it was issued
  **and** not revoked (both directions).
- `revoke_blocks_verify:180` / `verify_unrevoked_iff_issued:191` — revocation actually blocks
  verification; an unrevoked credential verifies iff issued.
- `Authority/CredentialAttenuation.lean`, `ClearanceGraph.lean` — attenuated/derived credentials +
  the clearance ordering. Rust: `token/`, `credentials/`.

## The caveat / attestation dial-cube

The richer attestation faces (a Disclosure × Transferability × Agreement dial-cube, per the dregg4
vision):

- `Authority/SelectiveDisclosure.lean` — reveal only what's needed.
- `Authority/DesignatedVerifier.lean` — proofs only a chosen verifier can check.
- `Authority/BiscuitGraph.lean`, `CDT.lean`, `CSpace.lean` — Datalog-style authorization
  (biscuit), capability-derivation-trees, the c-space.
- `Authority/CoordinatedCaveat` (in `Exec/CoordinatedCaveat.lean`) + `CrossCaveat.lean` — caveats
  coordinated across a joint turn.

## How the token gates the executor (the inline enforcement)

The whole point: the token
**gates EXECUTOR ADMISSION** and every caveat tier/operator is *executed*, not checked out-of-band.

- `Dregg2/Exec/Admission.lean`, `AdmissionWire.lean` — the admission predicate.
- `Dregg2/Exec/AuthModes.lean` — the 10-variant `Authorization` + `authModeAdmits`.
- `Dregg2/Exec/AuthTurn.lean` — the executable delegate/revoke transition (`recKDelegateAtten`:
  the proven `granted ≤ held` gate + attenuated derive-install).
- `Dregg2/Exec/Caps.lean` — the c-list (`Caps.derive`).
- `Dregg2/Exec/FullForestAuth.lean` — where it all lands: `execFullForestG` with `GatedCaveat`,
  `NodeAuth`, and `execFullForestG_unauthorized_fails:949` proving the gate is sound (an unauthorized
  turn returns `none`).

So the chain is: a turn carries an authorization + caveats → `execFullForestG` evaluates the
`Spec.Guard` inline → unauthorized ⇒ fail-closed `none`. There is no ungated escape hatch (the
ungated FFI export was removed — see [`executor.md`](executor.md)).

## Agent mandates — `Agent/Mandate.lean`

For autonomous agents: a *mandate* is a predicate the executor enforces on what the agent may do —
the same gate machinery, applied to agent authority. Rust: `intent/`, `demo-agent/`.

## Where to start reading

1. `Dregg2/Spec/Guard.lean` — the ONE verify/find seam (`attenuate_narrows`).
2. `Dregg2/Authority/CaveatChain.lean` — macaroons end to end (the five theorems above).
3. `Dregg2/Exec/AuthTurn.lean` + `FullForestAuth.lean` — how authority gates a real turn (the
   10-variant `Authorization` lives in `FullForestAuth.lean`).
