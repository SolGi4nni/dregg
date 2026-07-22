# Dealerless fhEgg preprocessing

**Status:** executable cuts in progress; this document specifies the acceptance
boundary. `FHTRI004` remains the live, explicitly authority-generated format
until a new version satisfies every gate below.

## What the current sacrifice does—and does not—buy

`FHTRI004` has a real, useful malicious-error detector. It commits 129 binary
triple candidates per kept gate, authenticates the relevant openings under two
independent `GF(2^128)` MAC lanes, derives post-commit challenges, and releases a
row only after every sacrifice equation succeeds. Durable custody separately
prevents an accepted protected row from being spent twice.

The remaining dealer is nevertheless decisive. The current generator in
`fhegg-fhe/src/mpc_party/authenticated_preprocessing.rs` creates every candidate,
calls `trusted_mac_setup_for_bits`, and chooses the beacon from the same RNG. The
MAC setup in `authenticated_bits.rs` necessarily sees the reconstructed bits and
both complete MAC keys. Sacrifice can detect malformed correlations under its
premises; it cannot make a party forget valid correlations or keys it generated.

The replacement therefore changes the *source* of candidates, MAC material, and
randomness. It retains the sacrifice and one-use custody machinery as defense in
depth.

## Target trust statement

Fix an exact session, ordered roster, protocol version, circuit/gate count, BFV
parameter digest, collective-key digest, relinearization-key digest, candidate
count, and candidate manifest. Subject to the named proof obligations below:

1. no process ever constructs the collective BFV secret key or either complete
   authenticated-opening MAC key;
2. if at least one roster party samples its local candidate and mask shares
   honestly and keeps them private, the coordinator does not learn the kept
   Beaver triples;
3. a completed joint beacon is unpredictable before the fixed manifest if one
   reveal is honest; an abort is visible and cannot become a silent reroll;
4. an accepted row is bound to one session, roster, manifest, certificate, party,
   gate interval, and durable one-use record; and
5. a verifier can distinguish an old trusted-authority certificate from a new
   dealerless certificate. No parser or adapter promotes `FHTRI004` by relabeling
   it.

This is an at-least-one-honest-party statement. Availability for an `n`-of-`n`
ceremony still requires all parties. A later threshold/dropout profile needs its
own proof and wire version.

## Exact binary-triple factory over odd-modulus BFV

PartyMPC consumes XOR shares and binary triples. The deployed BFV plaintext
modulus is odd (the fold set is approximately 20 bits), so adding encrypted
local bits produces an integer sum modulo `t`, **not parity**. The construction
must use the exact bit identity

```text
x XOR y = x + y - 2xy
```

inside BFV. For more than two parties, fold that operation in a fixed balanced
tree whose geometry is part of the descriptor. Every intermediate is a bit when
the inputs are bits; the wrap guard must prove that the chosen expression and
depth remain inside the plaintext/noise envelope.

For each candidate and each party `i`:

1. `i` independently samples private bits `a_i`, `b_i`, and `r_i` and independent
   encryption randomness, then emits context-bound BFV ciphertexts plus proofs
   that each plaintext is a canonical bit encrypted under the exact collective
   key.
2. The evaluator computes encrypted global bits
   `A = XOR_i a_i`, `B = XOR_i b_i`, and `R = XOR_i r_i` with the identity above.
3. Using the multiparty relinearization key, it computes `C = A * B` and then
   `Z = C XOR R`.
4. Every party emits a context-bound partial decryption share for `Z`, with a
   proof of correct share formation. Only the masked bit `z` is opened.
5. Output shares are `c_i = r_i` for every party except the fixed distinguished
   party, whose share is `c_0 = r_0 XOR z`. Therefore
   `XOR_i c_i = C = (XOR_i a_i) AND (XOR_i b_i)`.
6. Candidate shares are committed, authenticated, and fed to the existing
   sacrifice. Candidate-local secrets are erased after certified rows enter
   one-use custody.

Opening `z` does not reveal `c` if one honest `r_i` is uniform and hidden. The
distinguished party is fixed by the protocol descriptor, not chosen after `z`
is known.

The first executable carrier may pin two parties to keep the exact multiplicative
depth small. Such a carrier is a two-party profile, not evidence that an
arbitrary-roster fold has been qualified.

## Collective BFV ceremonies already available

The repository already contains most of the non-dealer key substrate:

- `threshold::ThresholdParty` independently samples and retains a ternary secret
  share and exposes only a public-key contribution. `KeygenCoordinator` accepts
  each exact roster member once and has no secret-share input API.
- `threshold::relin` runs the two-round fhe.rs multiparty relinearization-key
  ceremony over the retained party shares, so ciphertext multiplication does
  not require assembling `sk` or `sk^2` in one process.
- `ThresholdParty::partial_decrypt` and `threshold::combine` implement collective
  decryption with the Lean-pinned smudging floor.
- `bfv_mul::MulEngine` performs wrap-guarded ciphertext multiplication using the
  public relinearization key.
- the exact BFV NTT and faithful-table work provide a path from the upstream
  arithmetic oracle to a Dregg-native proved implementation.

Those modules are presently honest-protocol/process-custody components. Their
wire messages are not, by themselves, malicious-share proofs. The dealerless
certificate must not erase that distinction.

## Distributed MAC custody is more than splitting alpha

For each MAC lane, let the global key be the field sum

```text
alpha = alpha_0 + ... + alpha_(n-1)
```

and require every `alpha_i` to remain inside party `i`. This removes the API that
constructs a complete MAC key, but it is not yet an authenticated-bit generator.
For a secret-shared bit `x = sum_j x_j`, the desired tag relation is

```text
sum_i gamma_i = alpha * x
                  = sum_i sum_j alpha_i * x_j.
```

Local terms `alpha_i * x_i` omit every cross term and are wrong. Those cross
terms need a secure multiplication primitive. Two admissible implementations
share the same certificate interface:

- a proof-first lattice baseline evaluates the 128-bit carry-less
  multiplication circuit with threshold BFV and distributes a masked result;
  or
- a malicious-secure post-quantum OLE/VOLE/PCG backend produces the same
  correlations more efficiently.

The BFV baseline is attractive because its semantics can reuse the exact NTT,
relinearization, HidingFRI, and Lean work. The VOLE backend is the likely high
throughput path. Neither may be represented by a constructor that receives all
key shares or all value shares.

## Joint post-manifest randomness

The minimal executable beacon is an ordered roster commit/reveal:

```text
commit_i = H(domain, context, party_i, nonce_i)
beacon   = H(domain, context, ordered commits, ordered reveals)
```

`context` includes the candidate and MAC manifests. All exact-roster commits
must be fixed before any reveal is accepted; every reveal must match its commit;
duplicates, omissions, reordering, cross-session substitution, and trailing
bytes fail closed.

If one completed reveal is honest, the completed beacon is unpredictable before
the manifest. A last revealer can still inspect the other reveals and abort.
That is a liveness/bias boundary, not a reason to hide the abort: persist a
signed abort receipt and make retry identity and policy deterministic. A
scheduled external beacon or a robust threshold beacon can later replace this
source behind the same transcript interface. Classical drand/BLS is not an
end-to-end post-quantum answer.

## Malicious-security proof obligations

A completed transport simulation is not enough. A dealerless acceptance claim
requires all of the following to be verifier-enforced:

- knowledge and canonical-bitness proofs for every encrypted `a_i`, `b_i`, and
  `r_i` under the exact collective key;
- exact DKG contribution and no-rogue-key validation;
- correct two-round relinearization-share proofs or an equivalent certified
  public key;
- correct, ciphertext-bound partial-decryption-share proofs;
- strict authenticated sender/roster/phase/sequence envelopes;
- exact homomorphic expression, wrap/noise bounds, and output-share derivation;
- split-MAC cross-term generation with a concrete active-security argument;
- manifest-bound joint challenge randomness;
- the existing 128-round sacrifice and two MAC lanes; and
- durable compare-and-set consumption before gate zero.

Until the bitness and decryption-share obligations are proved, a threshold-BFV
run is an executable honest-contributor correlation carrier. It removes the
single process that learns all candidates, but it is not yet a malicious-secure
replacement for the authority.

## Wire and cutover law

Use a fresh magic/version (provisionally `FHTRI005`) containing, or committing
canonically to:

- the complete base session, ordered roster, protocol descriptor, BFV/DKG/relin
  identities, gate range, and allocation ceilings;
- every public party contribution and its proof;
- the masked-opening transcript and verified opening result;
- candidate and authenticated-bit manifests;
- the complete joint-beacon commit/reveal or threshold-beacon evidence;
- the sacrifice transcript root and retained-row root; and
- the durable batch identity consumed by custody.

The decoder returns an unverified claim. Only a verifier that checks the complete
formation certificate may construct dealerless protected material. `FHTRI004`
continues to decode only as `TrustedAuthority`; legacy shape-only triples remain
incompatible with certified sessions.

## Acceptance teeth

The replacement is live only when focused gates demonstrate:

1. no production symbol or serialized state reconstructs a collective BFV or
   MAC key;
2. honest generated rows satisfy the binary triple equation and pass the current
   sacrifice;
3. changing any bit contribution, encryption proof, DKG/relin identity,
   decryption share, mask opening, manifest, beacon reveal, roster entry, gate
   interval, or version is rejected;
4. a coordinator restart preserves the exact public transcript without gaining
   party-local secrets;
5. the same protected row cannot be accepted twice, including after restart;
6. CPU/oracle and WGPU/proved arithmetic are byte- or field-identical at their
   declared boundary; and
7. the end-to-end Dark Bazaar decision consumes the new protected rows and its
   receipt names the dealerless formation certificate.

The final tooth is intentionally a game path. A preprocessing protocol that is
never selected by the Bazaar host is a laboratory artifact, not the removal of
the deployed dealer.
