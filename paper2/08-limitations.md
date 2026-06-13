# 8 · Limitations

Present-tense facts about the system as it stands. Each is a property a
reader can check, not a roadmap.

**The host-context seam.** Some wire-effect families are executed by host
Rust whose verdicts are cross-checked against the Lean kernel turn-by-turn
rather than produced by it. For those families the host implementation is in
the trust base; the node reports the exact producer split live at
`/api/node/producer`, and guarantee R is stated over the verified entry, not
over the host arms.

**Composition security is not machine-checked end-to-end.** The
per-guarantee theorems are kernel-pinned, and the cross-corner welds
(executor ⟺ circuit) are theorems; a universal-composability statement for
the protocol stack as a whole — that the guarantees survive arbitrary
concurrent composition with adversarial environments — is not yet a Lean
artifact. The UC-shaped scaffolding exists (`Crypto/UCBridge.lean`); the
end-to-end statement does not.

**The global value law is per-turn, not yet per-issuer-global.** Exact
conservation (Σδ = 0 per asset, per turn, lifted to attested runs) is
proven. The stronger discipline — `AssetId` identified with the issuer cell,
the issuer carrying negative supply so every asset's system-wide total is
identically zero at all times — is specified (`docs/DREGG3.md` §2.2, risk
R2) and probed, but is not the deployed ledger discipline.

**Guard expressibility has stated edges.** The enforceable constraint
grammar is the relational/quantified closure of §3.2; its source-stated
limits (what a program cannot see) are quoted in the generated predicate
catalog. Causal/temporal guards — predicates over the receipt trace rather
than one transition — are designed (the causal-guard modules exist) but the
installable surface is the transition fragment; trace-shaped rules are
presently witnessed-predicate territory.

**The explain reading is rendering, not semantics.** The clerk's
human-facing explanation of a turn is a total, deterministic rendering of
the term IR. Totality and injectivity-on-semantics are the honest scope;
natural-language faithfulness is not a theorem and is not claimed as one.

**Liveness is exactly as strong as its carrier.** Safety guarantees are
unconditional modulo the cryptographic floor; liveness (finality,
revocation-at-finality) additionally rests on PostGSTProgress — eventual
synchrony. A partitioned network stalls finality; it cannot forge it.
