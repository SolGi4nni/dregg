# dregg-oracle — trustless web facts you can reuse

**Prove that a real HTTPS endpoint genuinely returned a value — then let anyone
re-verify it trusting no one.**

`dregg-oracle` turns a live HTTPS response into a small, portable proof file. You
run `prove` once; you hand the resulting `proof.json` to anyone; they run
`verify` and get `PASS` or `FAIL` — **without trusting you, without re-calling
the API, and without any shared secret.** The proof is self-contained: it carries
its own evidence that the bytes really came off a TLS session with the pinned
server, that the response body is well-formed, and (for endpoints with a
user-supplied field) that the field is injection-free.

It is built on `dregg-zkoracle-prove`, whose 3-leg attestation mirrors the Lean
theorem `zkOracle_sound`. A proof is only accepted when **all three legs** hold:

```text
authentic       — a genuine TLS session with the pinned server, co-witnessed by a
                  TLSNotary that saw no plaintext (MPC-TLS 2PC).
well-formed      — the response body is certified to lie in the JSON grammar, by a
                  replayable CFG parse certificate (not a regex, not a guess).
injection-free   — any user-supplied field is bound to a committed substring of the
                  authenticated body and proven to contain no `{{` breakout, with a
                  STARK over a verified DFA. (n/a for read-only facts.)
```

All three are welded to **one** response by a shared Poseidon2 content
commitment, so you cannot staple a well-formed cert or a clean field from response
A onto an authentic session for response B — the weld refuses it.

---

## The 3-command demo

```sh
# 1. PROVE — capture a real Coinbase BTC spot quote as a portable proof.
dregg-oracle prove price --asset BTC-USD --out proof.json

# 2. SEND — proof.json is just a file. Email it, paste it, commit it. No key,
#    no server, no live connection travels with it.

# 3. VERIFY — your friend runs this on their own machine, trusting no one:
dregg-oracle verify proof.json
#   → PASS  api.coinbase.com  BTC-USD = 64250.37  at 2023-11-14T22:13:20Z
```

`verify` exits `0` on `PASS` and non-zero on `FAIL`. A tampered proof — a flipped
digit in the amount, a swapped body, a forged notary signature — refuses:

```sh
dregg-oracle verify tampered.json
#   → FAIL  authentic leg refused: bad notary signature
```

Run the whole thing end to end with [`./demo.sh`](./demo.sh).

The GitHub commit oracle works the same way:

```sh
dregg-oracle prove github --owner octocat --repo hello-world \
    --sha 6dcb09b5b57875f334f61aebed695e2e4193db5e --out commit.json
dregg-oracle verify commit.json
#   → PASS  api.github.com  octocat/hello-world @ 6dcb09b…  by Monalisa Octocat
```

---

## The trust model — why a stranger can rely on this

A `dregg-oracle` proof lets the verifier trust the fact **without trusting the
prover.** Three things make that hold:

1. **The notary co-witnesses, but sees nothing.** The proof is produced through a
   TLSNotary MPC-TLS handshake: the notary and the prover jointly derive the TLS
   session keys in a 2-party computation, so the notary can attest that a genuine
   session with the pinned server happened — while **never seeing the plaintext**
   (and never seeing any secret request header). The verifier checks the notary's
   signature over the session, so a prover cannot fabricate a response the server
   never sent.

2. **The STARK / CFG certificate binds the disclosed fact.** The response body is
   not taken on faith: a replayable CFG parse certificate proves it is well-formed
   JSON, and the quoted fact (the amount, the commit sha) is parsed out of the
   *authenticated* bytes. For endpoints with a user-supplied field, a STARK over a
   verified injection DFA proves the field carries no `{{` template breakout,
   checked fail-closed — a forged or foreign STARK refuses the whole attestation.

3. **The weld pins everything to one response.** A single content commitment ties
   the authentic, well-formed, and injection-free legs to the *same* body, so
   evidence cannot be mixed and matched across sessions.

The verifier re-runs all of this locally from `proof.json`. Nothing in the
verification step calls out to the API, to you, or to the notary again.

---

## The honest boundary — what this does and does NOT claim

Read this before you build on it. The proof is only as strong as what it actually
attests.

- **It needs a notary.** Trustlessness here means *you* don't have to trust the
  prover — but the verifier does rely on the notary having honestly co-witnessed
  the session (it cannot see or alter the plaintext, but a notary colluding with
  the prover to sign a session that never happened is out of scope). Pin a notary
  key you're willing to rely on. The demo runs a **self-hosted, in-process**
  notary so there is no third party at all.

- **TLS 1.2 hosts only.** The MPC-TLS machinery negotiates TLS 1.2. Endpoints that
  require TLS 1.3-only are not yet supported.

- **It attests "this server returned these bytes at this time" — not that the
  server told the truth.** A proof over `api.coinbase.com` certifies that
  Coinbase's endpoint returned that amount at that session time. It does **not**
  certify that the amount is a fair market price, that Coinbase is honest, or that
  the value means anything beyond "this is what the endpoint said." The oracle
  moves trust from *you* to *the origin server* — it does not remove trust in the
  origin.

- **The timestamp is the session time,** signed by the notary — the moment the TLS
  session happened, not a clock inside the response body.

- **Live-host status.** The self-hosted notary + prover run the genuine MPC-TLS
  2PC today; the default build exercises the full prove → portable → verify →
  refuse-on-tamper pipeline over a self-hosted session. Pointing the same prover at
  the public `api.coinbase.com` / `api.github.com` (a real internet TLS session
  with a deployed, pinned notary) is the same machinery with the server swapped —
  see the live path behind the `live` feature.

---

## Build & run

`dregg-oracle` is a standalone crate (its own detached workspace) that path-depends
on `dregg-zkoracle-prove`.

```sh
cd dregg-oracle
cargo build --release            # the prover + verifier CLI
cargo run --release -- verify proof.json
```

There is no lighter build and no feature flag: the real internet-host MPC-TLS path (the
heavy `mpz` 2PC + tokio + rustls stack, in the `dregg-zkoracle-live` crate) is what this tool
IS. It used to sit behind `--features live`, whose "off" build compiled a CLI in which every
command was a `bail!` — and, because cargo features unify across a workspace resolve, whose
"on" state silently reached into `dregg-zkoracle-prove` and changed what that shared crate
compiled for every other member.

## Reuse

`dregg-oracle` is a library as well as a CLI: depend on the crate and call
`prove` / `verify` directly, or shell out to the binary and pass `proof.json`
around. See [`USES.md`](./USES.md) for concrete things worth building on it —
verifiable price feeds, provable API responses for agents, and trustless receipt
proofs.
