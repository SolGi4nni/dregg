# PoA Dark Bazaar protocol exercise

Status: executable protocol exercise; **not** a live PoA salvage market.

The heavy integration target `poa_dark_bazaar_protocol` answers one concrete
question: how much of DrEX can a Path of Angels expedition use today without
pretending that an issuer signature is a Lean-judged game result?

The answer is: the receipt can authenticate and scope a sealed-order identity,
and the existing private-clearing stack can prove and clear the resulting exact
book.  The flow then stops before asset creation, listing, or settlement.

## Protocol transcript exercised

1. Four PoA expedition envelopes are signed by the deployment issuer.  Each
   envelope names a distinct `player_key` and positive per-player counter.
2. The same four private keys sign the four canonical N=4,K=4 private-book BFV
   rows.  Possession of a valid PoA envelope without control of its named key is
   therefore insufficient to submit that trader slot.
3. A candidate, test-local Bazaar transcript begins with
   `pathofangels.network/bazaar-ingress/v1\0` and commits the federation,
   content session, mission, artifact, ordered player keys/counters, and exact
   signed-receipt digests.  A different domain, roster order, or independently
   valid substituted receipt produces a different session.
4. The ingress verifier checks every order signature and exact canonical-row
   reencryption.  Its canonical output is ordered message/ciphertext digests;
   the encryption seeds are absent from public order wires and the final
   clearing receipt.
5. One private witness produces both the real HidingFRI clearing proof and the
   transferable Bulletproof that the public BFV rows open to the same private
   book/root.
6. Those exact rows are homomorphically folded.  One of two BFV decryption
   shares is refused; a share for another ciphertext is refused; the full
   masked opening becomes two party-local mod-t shares.
7. Actual authenticated PartyMPC machines consume the local shares and reveal
   only `(p*, V*)`.  Their signed public frames reconstruct the exact
   reveal-only transcript; a changed receipt session or modified frame fails.
8. A 2-of-2 committee claim composes the transcript, HidingFRI proof,
   same-opening proof, exact row/root/source/fold inputs, BFV identity, and
   receipt-derived nonce.  One signature is refused, evidence tampering is
   refused, and the complete receipt is consumable once.
9. `PoaSalvageMinter` is called only after the successful clearing and still
   returns `MissingTransitionVerifier`.  The vault remains empty, so no
   listing, settlement, or ownership transfer can be constructed.

## Guarantee ledger

| Claim | Status in this exercise |
|---|---|
| PoA outer envelope authenticity and deployment scope | Real |
| Order signer equals the exact `player_key` named by its receipt | Real |
| Bazaar domain, ordered roster, counters, and signed receipt digests bind the session | Executable candidate transcript; not yet a production/Lean emitter |
| Canonical side-hiding BFV rows and exact operator-visible reencryption | Real |
| HidingFRI private clearing proof | Real |
| Transferable same-opening Bulletproof over the same book/root and BFV rows | Real, classical |
| Masked threshold boundary; one-share and wrong-target refusal | Real, two local parties |
| Authenticated reveal-only PartyMPC execution | Real, local machines with classical transport |
| Full clearing claim quorum and replay refusal | Real, classical 2-of-2 compatibility quorum |
| PoA `JudgedRun` / transition capability | Missing; fails closed |
| PoA salvage mint, listing, ledger settlement, or transfer | Not attempted because no asset exists |
| House-blind ingress | No; the exact-opening verifier sees order and seed |
| Hidden order side | No; side is public in the current signed ingress envelope |
| Dealer-free or malicious-secure MPC | No; test-local trusted-dealer triples |
| Independent-operator threshold deployment | No; local-process exercise |

The end-to-end privacy grade is
`operatorVisibleHidingFri`.  The masked threshold and PartyMPC stages are
stronger than that in isolation, but the source operator sees plaintext
openings during ingress and the public envelope exposes side.  Privacy grades
describe the weakest relevant boundary, not the most impressive component.

## Why clearing does not grant an asset

The current Rust PoA adapter can authenticate an issuer envelope, but it cannot
construct the opaque Lean `JudgedRun`/player-transition authority.  A private
market proof answers “what is the exact clearing of these committed orders?”;
it cannot answer “did this player legitimately earn this relic?”  Treating the
former as evidence of the latter would be authority laundering.

The intended next join is a Lean-emitted judged receipt whose exact identity is
consumed by both the salvage minter and the Bazaar session derivation.  Only
then should this exercise grow an asset input and cross the existing atomic
DrEX settlement boundary.

## Running it

The n=4096 same-opening proof makes this a heavy, release-only target:

```sh
cargo nextest list -p dreggnet-market --features private-attested-clearing \
  --test poa_dark_bazaar_protocol
cargo nextest run -p dreggnet-market --features private-attested-clearing \
  --test poa_dark_bazaar_protocol --profile heavy --release
```

The target is explicitly included in `.config/nextest.toml`'s `heavy` profile
and excluded from `default` and `ci`.
