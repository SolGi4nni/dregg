# Output-Boundary MPC — the ADVERSARIAL No-Viewer Crossing

*Codex Round-4's highest-value gold, built. The construction that makes Tier-0
"no viewer" a **cryptographic threshold bound** instead of a policy claim, and
**dissolves the BFV→TFHE scheme-switch seam** the fold-envelope flagged as the
crux. What-is, present tense; every edge names its grade; the honest threshold
caveat is stated, not buried. The PoC is real and cited (§7).*

Sources this refines: `FHEGG-CODEX-ROUND4.md` (the headline reframe + the
threshold-trust correction), `fhegg-fhe/ADDITIVE-FOLD-ENVELOPE.md` (the measured
additive fold + the named un-measured scheme-switch seam), `MEASURED-ENVELOPE.md`
(the exact-integer TFHE baseline), `DREGGFI-PRIVACY-TIERS.md` +
`DREX-NO-VIEWER-SURPASS.md` (the Tier-0 claims this note corrects).

---

## 0. Five-line summary

1. **The crossing's nonlinearity is irreducible; paying for it inside TFHE is
   not.** `p*` is deliberately public, so the comparison need not run under FHE at
   all. Keep the aggregate curve under the exact RLWE/BFV fold; at the OUTPUT
   BOUNDARY the `n` federation parties partial-decrypt only the aggregate into
   additive secret shares and run the crossing in MPC, revealing only `p*` + `V*`.
2. **This dissolves the scheme-switch seam.** Threshold-BFV partial decryption
   INTO additive shares is native to the scheme (each party applies its key
   share). There is no CHIMERA/PEGASUS BFV→TFHE adapter — the one un-measured seam
   of `ADDITIVE-FOLD-ENVELOPE.md` is replaced by an operation the threshold stack
   already has.
3. **The no-viewer becomes ADVERSARIAL.** Below the threshold `t`, no coalition of
   parties learns any order or any curve coefficient — a cryptographic bound, not
   a promise. No standing master decryption key exists (unlike threshold-FHE,
   where a colluding key-share subset can decrypt any submitted *order* forever).
4. **The revealed function is fixed to `p*` by the protocol.** The monotone sign
   vector `c[p]=[D[p]≥S[p]]` is a single downward step whose flip index *is* `p*`,
   so a simulator given only `p*` reproduces `c`: revealing it leaks nothing more.
5. **The honest caveat.** It is `t`-of-`n`: `≥ t` colluding parties CAN
   reconstruct. "Nobody ever, even if all collude" is impossible for clearing over
   hidden data. Output-boundary MPC shrinks trust to its minimum — a threshold,
   one clearing, reveal-only-`p*`, no standing key. **Grade: PoC built + measured
   (§7); the production partial-decrypt-into-shares + malicious security are the
   named frontier (§8).**

---

## 1. The problem this solves

`ADDITIVE-FOLD-ENVELOPE.md` measured the Tier-0 lever: swapping the exact-integer
TFHE fold for a carry-free additive BFV fold makes the aggregation **~10⁵× cheaper
and sub-10 ms**, recovering the kernel's "aggregation is the cheap part" thesis.
But it left two facts standing:

- **The crossing cannot be additive.** `sign`/`min`/`first-crossing` are not affine
  over the ciphertext ring; no additive scheme does the comparison. The crossing
  stays on TFHE (measured ~12–17 s, O(K), N-independent) — *or* it moves.
- **The BFV→TFHE scheme-switch is a named, un-measured seam.** To feed the
  BFV-folded curves into a TFHE comparator without decrypting them, a deployment
  needs a BFV→LWE/TFHE switch (CHIMERA ePrint 2018/758, PEGASUS 2020/1606). No
  clean Rust implementation exists; it is the one real residual of the fold path.

Output-boundary MPC removes *both*: the comparison leaves FHE entirely (no TFHE
crossing to pay for, no scheme-switch to build), and lands in a secret-shared MPC
whose only revealed output is `(p*, V*)`.

---

## 2. The construction

### (a) The additive RLWE/BFV fold (already built, measured)

Each trader locally expands its order into a **unary K-bucket increment vector** (a
bid of limit `L` puts its qty on buckets `0..=L`; an ask on `L..K`), SIMD-packs it
into ONE BFV ciphertext, and submits it. The server folds the N submissions into
two aggregate curve ciphertexts by native carry-free `+=`:

`Enc(D[p]) = Σ_bids inc[p]`,  `Enc(S[p]) = Σ_asks inc[p]`  — O(N) carry-free adds.

This is `fhegg-fhe/src/additive.rs::bfv_fold`, measured at 0.0003–0.0054 s for
N∈{32,512} (`ADDITIVE-FOLD-ENVELOPE.md`). `D` is non-increasing, `S`
non-decreasing (from the unary encoding). The limit `L` never leaves the trader;
the server only ever sums ciphertexts.

### (b) The output-boundary MPC crossing

The `n` parties (= the federation nodes, §5) hold key shares of the threshold-BFV
key. At the boundary they **partial-decrypt the aggregate curve INTO additive
shares** — each party `i` applies its key share to `Enc(D[p])`, producing a share
`⟦D[p]⟧_i` such that `Σ_i ⟦D[p]⟧_i = D[p]`; likewise `S[p]`. No party holds `D[p]`.
(This is the standard threshold-FHE partial-decryption, redirected to output
shares rather than a cleartext — the seam-dissolving move.)

They then run the crossing in a secret-shared MPC:

1. **Sign vector.** For each bucket, securely compute `c[p] = [D[p] ≥ S[p]]` and
   OPEN it. `c` is the monotone crossing indicator.
2. **`p*`.** `p* = (Σ_p c[p]) − 1` — the largest `p` at which demand still meets
   supply = `argmax_j min(D[j], S[j])` under monotonicity. Public arithmetic on the
   opened, `p*`-determined bits.
3. **`V*`.** At the now-public `p*`, securely compute `V* = min(D[p*], S[p*])` and
   OPEN only the min — never the two curve heights individually.

The public transcript is `{batch root, p*, V*}` plus the one-time-pad-masked MPC
messages. The STARK receipt then proves the two boundary inequalities
(`¬Clears(p*+1) ∧ Clears(p*)`) against the committed aggregate — the comparator is
untrusted search the proof re-checks (the `FHEGG-CODEX-ROUND4.md` §Q2
verified-core-boundary point), so an MPC comparator fault yields a wrong `p*` that
cannot receive a valid proof, never a soundness break.

### (c) Why the sign vector leaks nothing beyond `p*` (the leakage argument)

Because `D` is non-increasing and `S` non-decreasing, `c[p] = [D[p] ≥ S[p]]` is a
**single downward step** `1…1 0…0` whose flip index is exactly `p*`. So `c` is a
*deterministic function of `p*`*: the simulator `c[p] = [p ≤ p*]` reproduces it
with no other input. Revealing `c` (equivalently `p*`) therefore reveals no more
than `p*` itself. This is the codex "monotone sign vector is `p*`-determined under
a fixed tie rule" observation, and the PoC demonstrates it directly (§7B): two
different books with the same `p*` produce the identical opened sign vector.

---

## 3. The security model — adversarial no-viewer, stated precisely

**Adversary.** A coalition `C ⊂ {1..n}` of parties, `|C| < t`, plus the public
(everyone sees the batch root, the ciphertexts, the STARK, and `(p*, V*)`).

**Guarantee (the no-viewer bound).** The joint view of `C` — its key shares, its
additive shares of every curve coefficient, and every MPC message — is
*computationally independent of every individual order and of every curve
coefficient*, conditioned on the public output `(p*, V*)`. Concretely:

- Any `n−1` additive shares of a value are uniform and independent of it (the
  sharing is information-theoretically hiding below `n` parties).
- Every message opened in the online phase is a **one-time-pad-masked bit** (`x ⊕
  a`, `a` a fresh uniform Beaver-triple bit), so the message stream is uniform and
  input-independent.
- The only non-masked opened values are the sign vector (`= p*`) and `V*` — the
  intended public output.

Formally this is the semi-honest MPC guarantee: there is a **simulator** that,
given only `(p*, V*)`, produces a view identically distributed to the real one
(§7B implements and checks it). Hence the coalition learns *exactly* `(p*, V*)` and
nothing else — a cryptographic threshold bound.

**No standing master decryption key.** This is the load-bearing contrast with
plain threshold-FHE. A threshold-FHE committee holds shares of a decryption key
that can be applied to *any* ciphertext — so a colluding `≥ t` subset can decrypt
any submitted ORDER ciphertext, forever, and "nobody sees an order" is a *policy*
statement (they choose not to), not a cryptographic one. In output-boundary MPC
the parties partial-decrypt only the SELECTED aggregate coefficients into shares
for one clearing; there is no reusable key operation against order ciphertexts, and
the protocol's revealed function is fixed to `(p*, V*)` by its structure.

**What integrity requires (stated separately).** Privacy is unconditional below
`t`. *Correctness* is not: a malicious party can push a wrong `p*`/`V*` — caught by
the STARK boundary check (the comparator is outside the soundness TCB). Malicious
*privacy* (a party deviating to learn more) needs the maliciously-secure online
phase of §8; the semi-honest bound is what the PoC establishes.

### The honest caveat (no overclaim, no undersell)

- It **is** adversarial and cryptographic: below `t`, the bound holds by the math,
  not by trust. This is strictly stronger than the threshold-FHE Tier-0 posture.
- It is **`t`-of-`n`**: `≥ t` colluding parties reconstruct the shares and see the
  curve (and, with the key shares, could partial-decrypt orders). "Nobody even if
  all collude" is **impossible** for clearing over hidden data — the clearing is a
  function of the orders, so *someone* able to compute it can, in coalition,
  recompute its inputs' aggregate. Output-boundary MPC does not claim to escape
  that; it shrinks the trust to its irreducible minimum: a threshold, one
  clearing, reveal-only-`p*`, no standing key.

---

## 4. What the seam dissolution buys (vs. the pure-FHE crossing)

| | Pure-FHE crossing (`ADDITIVE-FOLD-ENVELOPE.md`) | Output-boundary MPC (this note) |
|---|---|---|
| Comparison carrier | TFHE `ge`+select, O(K) | secret-shared Beaver-triple `≥`, O(K) gates, O(b) rounds |
| Measured crossing cost | ~12–17 s (CPU) | **~1–7 ms** (§7C) |
| BFV→TFHE scheme-switch | **needed, un-measured seam** | **none** — partial-decrypt-into-shares is native |
| Who can see a coefficient | nobody (stays encrypted); committee holds a reusable order-decryption key | nobody below `t`; **no reusable order-decryption key** |
| Latency driver | PBS throughput (FPGA target) | network rounds ≈ `b · RTT` (bit-width, K-independent) |
| Online liveness | 1 threshold decrypt of `p*` | `t` parties online for one MPC (the added dependency) |

The cost is an **online `t`-party MPC dependency** for one clearing — which the
public-`p*`, threshold-decrypt posture already implies. In exchange the presumed
crossing bottleneck AND the scheme-switch both disappear.

---

## 5. The federation IS the MPC party set

The `n` parties are not a new committee — they are the **federation nodes** that
already run the threshold layer:

- `federation/src/threshold_decrypt.rs` is the built threshold stack: real Shamir
  secret sharing over **GF(256)** (`shamir_split_byte` / `shamir_reconstruct_byte`,
  Lagrange interpolation, MAC-verified shares), `t`-of-`n` `KeyShare`s, and a
  `ThresholdCiphertext` the validators jointly decrypt. `intent/src/trustless.rs`
  wires it into the batch: intents are threshold-encrypted, validators hold Shamir
  shares, `t`-of-`n` reconstruct. The party model, the sharing, and the
  reconstruction already exist.
- The natural `n` is the **live federation** — ember's `n=4` devnet and the
  five-validator C3 (memory: DEVNET). `t = ⌊n/2⌋+1` (honest majority) is the
  natural threshold, matching the existing threshold-decrypt configuration
  (`decrypt_threshold` / `num_validators` in `trustless.rs`).
- Output-boundary MPC **upgrades** this layer: today `trustless.rs` is threshold-
  *decrypt* (the committee sees the book after batch close — `DREX-NO-VIEWER-
  SURPASS.md` rung 3 names this exactly). The MPC crossing makes it threshold-
  *compute*: the parties compute the clearing on shares and open only `(p*, V*)`,
  so no party ever sees the book. This is the rung-3→"no single viewer" jump the
  ladder flagged as real work — and it reuses the Shamir/party infrastructure.

The additive shares of the curve coefficients are a re-sharing at the boundary; the
Beaver-triple online phase runs among the same `t` online validators.

---

## 6. The concrete MPC choice — secret-sharing + Beaver-triple comparison

**Chosen: boolean (GF(2)) additive secret sharing + a GMW/Beaver-triple secure
comparator**, over a garbled circuit. The justification:

- **The circuit is tiny and comparison-shaped.** The crossing is K independent
  `b`-bit `≥` comparisons (K∈{64,256}, `b≈16`) + one `min`. A `≥` is a ~3`b`-AND
  bit ripple; the whole crossing is ~`K·3b` ≈ 3k–12k AND gates. This is squarely
  in the cheap regime for secret-sharing MPC.
- **Multi-party by default.** The federation is `n=3–5` parties, not 2. GMW/SPDZ-
  style secret sharing is natively n-party; garbled circuits are cleanest for 2
  parties and need extra machinery (BMR) for n>2. The party set decides the tool.
- **The online phase is information-theoretically secure and non-interactive per
  gate up to the opens.** Given Beaver triples (offline/preprocessing), each AND is
  one opening round; XOR is free. The K comparisons are INDEPENDENT, so their AND
  gates **batch by circuit depth** — the whole crossing is **O(b) communication
  rounds regardless of K** (measured: 48 rounds = 3·16, K-independent, §7). Latency
  is `≈ b · RTT`, not `K · RTT`.
- **The masked opens are one-time pads**, which is exactly what makes the leakage
  argument (§3) clean: the message stream is uniform, so the simulator is trivial
  and the reveal-only-`p*` property is by construction.
- **Reveal-only-`V*` for the volume.** A `secure_min` at the public `p*` opens only
  the min, never the two heights — the sign-vector leakage argument does not cover
  the heights, so `min` is computed in MPC and only its result opens.

Garbled circuits would be a reasonable alternative for a **2-party** boundary
(e.g., a solver ⊕ a single custody node); for the n-party federation, secret
sharing is the fit. The preprocessing (Beaver triples) is the SPDZ offline phase:
in the PoC a simulated dealer produces them; in production they come from OT/HE
preprocessing among the parties (§8) — the online phase carries the security.

---

## 7. The PoC — real MPC, measured (cited run)

`fhegg-fhe/src/mpc.rs` (the protocol) + `src/bin/mpc_bench.rs` (the harness). Real
GF(2) secret sharing, real Beaver-triple AND gates (one-time-pad opens), a real
bit-sliced secure `≥`, the monotone crossing, a real secure `min`. **No mock, no
plaintext-pretending:** no party ever holds a plaintext curve coefficient; only
`(p*, V*)` open. Reproduce: `cargo run --release --bin fhe-mpc-bench` from
`fhegg-fhe/`. The run below is real (Apple M2 Max, CPU; the `n` parties are
simulated in one process, so the ms is compute, and the network-round count is
reported separately as the real-deployment latency driver).

### (A) Correctness — MPC `(p*,V*)` == the plaintext crossing, over REAL BFV curves

Every config runs the **real `bfv_fold`** (additive fold) → shares the folded
curves (models partial-decrypt-into-shares) → runs the MPC crossing, and checks
against `reference_clear`. All 12 configs match:

| N | K | n | BFV fold | MPC crossing | triples/ANDs | rounds | result |
|---|---|---|---|---|---|---|---|
| 32 | 64 | 3 | 0.0004 s | **1.15 ms** | 3136 | 48 | ✅ p*=14 V*=32 |
| 32 | 256 | 4 | 0.0003 s | **3.84 ms** | 12352 | 48 | ✅ p*=156 V*=29 |
| 128 | 64 | 4 | 0.0013 s | **0.99 ms** | 3136 | 48 | ✅ p*=31 V*=160 |
| 128 | 256 | 3 | 0.0031 s | **7.01 ms** | 12352 | 48 | ✅ p*=109 V*=138 |
| 512 | 64 | 3 | 0.0050 s | **0.90 ms** | 3136 | 48 | ✅ p*=31 V*=587 |
| 512 | 256 | 4 | 0.0051 s | **3.71 ms** | 12352 | 48 | ✅ p*=134 V*=584 |

(Full 12-row sweep in the run output.) `correctness across ALL configs: ALL MATCH
(MPC == plaintext)`.

### (B) Privacy — reveal-only-`(p*,V*)`: same-`(p*,V*)` → indistinguishable views

The harness searches random books for **two distinct aggregate curves with the
identical `(p*, V*)`** and compares party views over 200 fresh runs each:

```
found two DISTINCT aggregate curves with identical (p*,V*) = (Some(17), 10):
  book1 demand[..8]=[25,25,25,25,25,25,19,19]  supply[..8]=[0,0,0,0,0,5,10,10]
  book2 demand[..8]=[38,34,27,27,27,27,23,23]  supply[..8]=[0,0,0,0,0,8,8,8]
  (curves DIFFER: confirmed), yet both clear at the same (p*,V*).

party view over 200 fresh runs each (4 parties, K=32):
  P[opened protocol bit = 1]:  book1 = 0.4997   book2 = 0.5011   (uniform = 0.5)
  |bias1 - bias2|           =  0.0014
  opened sign vector equal  :  true
  revealed V* bits equal    :  true

simulator (given ONLY (p*,V*), no curves):
  P[simulated bit = 1]      =  0.4998
  simulated sign vector = real sign vector : true
  simulated V* bits     = real V* bits     : true

privacy verdict: views are STATISTICALLY INDISTINGUISHABLE -> the MPC reveals ONLY (p*,V*).
```

The two books' curves differ, but their party views are indistinguishable (opened
messages uniform and equal-biased to within 0.0014; sign vector and `V*` identical)
— the **same-leakage-as-reveal-nothing** property. The simulator, given only
`(p*,V*)`, reproduces the view distribution — the crisp statement that the view
reveals nothing beyond `(p*, V*)`.

### (C) Latency — the MPC crossing is MILLISECONDS

**0.9–7 ms** across all configs, vs the **~12–17 s** TFHE O(K) crossing it replaces
(`ADDITIVE-FOLD-ENVELOPE.md`) — ~**3–4 orders of magnitude** faster on the
comparison, and the BFV→TFHE scheme-switch cost is gone entirely. Rounds are **O(b)
= 48**, K-independent (the K comparisons batch by depth), so real-network latency is
`≈ b · RTT` — a handful of round-trips, not one per bucket.

**Honest PoC scope.** (i) the parties are simulated in one process — the ms is
compute; deployment latency is `b` network rounds among the `t` online validators
(each an all-to-all open). (ii) Beaver triples come from a simulated offline dealer
(SPDZ offline phase); the ONLINE phase is real and IT-secure given the triples.
(iii) the threshold-BFV partial-decrypt-INTO-shares is modelled by sharing the true
committed coefficients — the novel part (the MPC comparison on real shares) is what
runs; the RLWE→shares step is native threshold-FHE, not built here. (iv) semi-honest
security; malicious-secure online phase is §8.

### §7.5 MASKED DECRYPT-TO-SHARES — the decrypt-into-shares step, made real (measured)

The one modelled step above — "sharing the true committed coefficients" — is now a
real protocol (`fhegg-fhe/src/boundary.rs` + `fhe-boundary-bench`), and it dissolves
the missing primitive the same way §4 dissolved the scheme-switch: **mask, THEN
decrypt.** Each party homomorphically adds an encrypted uniform `Z_t` mask to the
folded curve ciphertext (`ct' = ct ⊞ Enc(r_0) ⊞ … ⊞ Enc(r_{n-1})` — n more
carry-free adds); the decryption then opens ONLY `y = (m + Σr_i) mod t`, an **exact
one-time pad** (enumeration-proven over the full mask space, even against a
coalition knowing all-but-one mask — `pad_is_exact_and_secret_independent`); each
party derives its mod-t share LOCALLY (`σ_0 = y − r_0`, `σ_i = −r_i`); one
`a2b_mod_t` bridge (exact secret-shared sum + n−1 oblivious conditional
subtractions of the public `t`) feeds the UNCHANGED crossing. So production needs
no new partial-decrypt primitive at all — the EXISTING federation threshold-decrypt
is pointed at `ct'`, because its output is now safe to open.

Measured (M2 Max, real BFV + real MPC, every row exactly equal to the plaintext
reference; `AGG→p*` = mask + decrypt + a2b + crossing — the R4 decisive metric):

| N | K | n | fold | mask | decrypt | a2b | crossing | **AGG→p\*** |
|---|---|---|---|---|---|---|---|---|
| 32 | 64 | 3 | 0.3 ms | 4.6 ms | 1.0 ms | 9.8 ms | 1.9 ms | **17.4 ms** |
| 128 | 64 | 4 | 1.4 ms | 6.4 ms | 1.0 ms | 13.5 ms | 2.1 ms | **23.1 ms** |
| 512 | 64 | 3 | 5.8 ms | 5.1 ms | 1.1 ms | 8.8 ms | 2.0 ms | **16.9 ms** |
| 128 | 256 | 4 | 1.4 ms | 6.5 ms | 1.0 ms | 59.4 ms | 8.7 ms | **75.6 ms** |

The Tier-0 value channel now has **no modelled step**: fold (carry-free BFV) →
masked opening (one-time pad) → mod-t shares → a2b → Beaver crossing → `(p*,V*)`,
all measured, tens of milliseconds of compute end-to-end after order encryption.
Honest scope: the PoC decrypts `ct'` with the in-process key (production = the
existing federation threshold decrypt); the decryption NOISE channel (IND-CPA-D)
still wants standard smudging noise in the threshold decrypt — named below.

---

## 8. The named frontier (honest residuals)

- **Threshold-BFV partial-decrypt-into-shares — CLOSED at PoC scope (§7.5).** The
  masked-decrypt construction removes the need for a dedicated primitive: masking
  makes the decryption's output a one-time-padded value, so the EXISTING
  threshold-decrypt stack (the in-house `federation/threshold_decrypt` pointed at
  BFV, or Zama TKMS) is the whole production requirement. Remaining: run that
  existing stack against `ct'` (deployment wiring, not a new primitive), and add
  smudging noise for the decryption-noise channel (below). **Grade: value channel
  built + measured + KAT'd; threshold wiring + noise smudging named.**
- **Malicious security.** The PoC online phase is semi-honest. Malicious security
  (a deviating party cannot learn more than `(p*,V*)` nor force an undetected wrong
  result beyond what the STARK catches) needs authenticated shares (SPDZ MACs) +
  verifiable partial decryption + noise smudging on the boundary shares. The
  building blocks exist (`threshold_decrypt.rs` already MAC-verifies shares).
- **Real preprocessing.** Beaver triples from OT/HE preprocessing among the parties
  (MASCOT/Overdrive), not a dealer. Standard; offline; off the latency path.
- **STARK boundary binding.** The receipt proves `¬Clears(p*+1) ∧ Clears(p*)` and
  `V* = min(D[p*],S[p*])` against the committed aggregate, binding `(p*,V*)` to the
  batch — the comparator stays outside the soundness TCB (`FHEGG-CODEX-ROUND4.md`
  §Q2). **Grade: the relation is the existing kernel; instantiating it for the
  boundary is named work.**

None of these overturn the construction; they sharpen the PoC toward deployment on
the labelled trajectory. The core claim — adversarial no-viewer via a `t`-of-`n`
threshold bound, seam dissolved, ms crossing — is real and measured today.

---

## 9. The claim, stated exactly

> **Tier-0's no-viewer is ADVERSARIAL, not a policy claim.** The aggregate demand/
> supply curve is folded under exact RLWE/BFV; at the output boundary the `n`
> federation parties partial-decrypt only the aggregate into additive secret
> shares and compute the crossing `p* = argmax_j min(D[j],S[j])` in a secret-shared
> MPC that reveals only `p*` and the cleared volume `V*`. Below the threshold `t`,
> **no coalition of parties learns any order or any curve coefficient** — a
> cryptographic bound, with no standing master decryption key and the revealed
> function fixed to `(p*,V*)` by the protocol. The honest caveat: it is `t`-of-`n`
> — `≥ t` colluding parties can reconstruct, because "nobody even if all collude"
> is impossible for clearing over hidden data. Output-boundary MPC shrinks the
> trust to its minimum, and it **dissolves the BFV→TFHE scheme-switch seam**: the
> comparison leaves FHE for a millisecond MPC, and partial-decrypt-into-shares
> replaces the exotic scheme adapter.

---

## 10. See also

- `fhegg-fhe/src/mpc.rs` — the protocol (secret sharing, Beaver-triple `≥`,
  crossing, `min`, simulator).
- `fhegg-fhe/src/bin/mpc_bench.rs` — the cited PoC harness.
- `fhegg-fhe/ADDITIVE-FOLD-ENVELOPE.md` — the additive fold + the (now dissolved)
  scheme-switch seam.
- `fhegg-fhe/src/additive.rs` — the real BFV fold this composes with.
- `federation/src/threshold_decrypt.rs`, `intent/src/trustless.rs` — the federation
  Shamir/threshold party set the MPC reuses and upgrades.
- `docs/deos/FHEGG-CODEX-ROUND4.md` §Q1.3.4 — the reframe + the threshold-trust
  correction this note builds.
- `docs/deos/DREGGFI-PRIVACY-TIERS.md`, `docs/deos/DREX-NO-VIEWER-SURPASS.md` — the
  Tier-0 claims corrected to the adversarial-threshold posture.
