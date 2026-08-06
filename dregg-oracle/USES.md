# What you can build on dregg-oracle

`dregg-oracle` gives you one primitive: a **portable, independently-verifiable
proof that a specific HTTPS endpoint returned a specific value at a specific
time.** Anyone can check it offline, trusting no one. Here are three concrete
things that primitive unlocks — kept honest about what the proof does and doesn't
say.

## 1. Verifiable price feeds for contracts

A smart contract or settlement engine can't call `api.coinbase.com` itself, and it
shouldn't trust whoever hands it a number. With `dregg-oracle`, an off-chain
relayer runs `prove --endpoint coinbase --asset BTC-USD` and submits the resulting `proof.json`;
the on-chain (or on-ledger) verifier re-checks the authentic + well-formed + weld
legs and reads the amount straight out of the *authenticated* body. The contract
now acts on "Coinbase's endpoint quoted 64250.37 at this session time" without
trusting the relayer's honesty.

*Honest scope:* the proof binds the number to the origin server, not to a fair
market — it's a faithful relay of what Coinbase said, with a notary-signed
timestamp, not a manipulation-resistant price oracle by itself. Multiple sources
and freshness policy stay the consumer's job.

## 2. Provable "I saw this API response" for agents

An autonomous agent that reads the web can attach a `dregg-oracle` proof to any
claim it makes from an HTTPS source, so a downstream reviewer (or another agent)
can confirm the response was real rather than hallucinated or paraphrased. The
injection-free leg matters here: when the response body is spliced into a prompt,
the STARK-backed DFA proves the disclosed field carries no `{{` template breakout,
bound to the exact authenticated bytes — so an agent can't be tricked into
attesting a benign field while the real content injects.

*Honest scope:* it proves *the server returned these bytes*, which the agent then
used. It doesn't prove the agent's reasoning over them is correct — only that its
input was genuine.

## 3. Trustless fiat / receipt proofs

Prove you observed a specific API response — an order status, a payment receipt, a
balance, a shipment record — and share that proof with a counterparty, auditor, or
dispute-resolution system that trusts neither of you. Because the notary sees no
plaintext and no secret request header (e.g. an API key stays redacted), you can
prove *what the endpoint returned* without disclosing *how you authenticated to
it*. The proof file is the evidence; it re-verifies years later with no live access
to the original service.

*Honest scope:* the proof attests the endpoint's response, not the real-world fact
behind it (a "paid" receipt proves the API said paid, on a TLS-1.2 endpoint, via a
notary you chose to rely on). It's strong evidence of an observation, not a
substitute for the merchant's own books.

---

Each of these is the same move: **replace "trust me, the API said X" with a proof
anyone can check.** Depend on the `dregg-oracle` crate for the library API, or
shell out to the CLI and pass `proof.json` around — the proof is the interface.
