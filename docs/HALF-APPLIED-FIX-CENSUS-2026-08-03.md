# HALF-APPLIED FIX CENSUS

**Swept 2026-08-04** (filename carries the campaign date `2026-08-03`, which is the seed commit's).
**Seed:** `f71f7f35e` — the 2026-08-01 `ContentCommit` widening (`BabyBear` → `[CommitLane; 8]`)
reached `deos-hermes/src/attest.rs` and `attested-dm/src/lib.rs` and missed the same digest
re-implemented in `commons-arbiter/src/lib.rs` and `confined-swarm/src/lib.rs`.

**The generalisable part of the seed, and the thing this census was built to test:** the missed
twins did not type-check against the widened type, so both crates went RED — and *a red crate reads
as "someone mid-refactor", not as "a security fix reached half its call sites."* The compile error
camouflaged the hole for two days.

> ⚠ **Scope discipline.** Every divergence below was found by reading **both** sides. Items where
> reading both sides showed the divergence was *correct* are listed under
> [Checked and NOT a divergence](#checked-and-not-a-divergence) — that section is load-bearing,
> because a census with no negatives is a list of suspicions.

---

## Summary

| # | Divergence | Copies that got the fix | Copies that did not | Missed copy compiles? | Disposition |
|---|---|---|---|---|---|
| 1 | `attestation_commitment` — the **two optional legs** (`tlsn_presentation`, `zk_injection`) | `deos-hermes`, `attested-dm` | `commons-arbiter`, `confined-swarm` | **yes, both** | ⚠ **cross-lane — live lane mid-repair** |
| 2 | `RECEIPT_COMMIT_DOMAIN` v1→v2 rotation | `attested-dm` (`…-v2`) | `commons-arbiter`, `confined-swarm` (both `…-v1`) | yes | report — same lane as #1 |
| 3 | `GradedMark::from_verified_zktls_session`'s **32-byte refusal** was unsatisfiable for 10 days | — (repaired *by accident* on 08-01) | — | yes, green today | report — fix needs a design call |
| 4 | `narrow_felt_from_slot_low4` — two stale citations left by the `node8` widening | the code | two comments in the widened file | yes | ✅ **FIXED** (this lane) |
| 5 | `scripts/mirror-gates/baseline.txt` carries a **stale** row the ratchet says to delete | — | — | n/a | report — `scripts/` has a live lane |

---

## 1. ⚠⚠ `attestation_commitment` — the SECOND half-applied fix in the SAME four-copy family

This is the seed's family, one fix earlier. It is the strongest finding in the census and it is
**not mine to land** — see *Disposition*.

**The fix.** `e1d0a028f` (2026-07-15, "fuse the REAL MPC-TLS presentation into the attested
narrator's authentic leg") added two optional legs to `ZkOracleAttestation` and, in its own words,
took *"(3) RECEIPT COMMITMENTS -> v2 (both crates): v1 fingerprinted only the fixture, leaving the
real presentation + STARK unbound on a landed turn."* The receipt digest must therefore absorb both
`att.tlsn_presentation` and `att.zk_injection`, each behind a domain-separating `[0]`/`[1]` tag.

**Who got it.**

* `deos-hermes/src/attest.rs:92` — has both `match` arms.
* `attested-dm/src/lib.rs:364` — has both.

**Who did not.**

* `commons-arbiter/src/lib.rs:174` — stops at `field_span`, then `*h.finalize().as_bytes()`.
* `confined-swarm/src/lib.rs:72` — same (repair **in the working tree**, not committed).

**What the divergence costs — and this is NOT a `2^k` bound.** State it plainly: the forgery costs
**one assignment**, not a search.

* `authentic_provenance` is *structural* — a bare `Some(_)` in `tlsn_presentation` reads as
  `MpcTls`. So a ruling/report that nothing notarized can be **upgraded** to "backed by a real
  MPC-TLS 2PC session" by setting one field, and the on-ledger receipt is unchanged.
* `zk_injection` can be **attached or stripped** with the same non-effect: a report whose
  injection-freedom was PROVEN in-circuit is indistinguishable, at the receipt, from one that only
  ran the host cleartext matcher.
* `verify_legs_over_session` consults neither field, so both edits survive `verify_zkoracle`.

No collision bound applies here at all; quoting one would flatter it. (The seed's `2^15.45` →
`2^123.63` figures are the *content-commit* widening's, a different fix in the same function.)

**Does the missed copy compile?** **Yes — both.** This is the inverse of the seed and worth naming:
the seed's gap was invisible *because* it was a compile error; this gap is invisible because it is
**not**. Adding a field a digest simply declines to absorb breaks nothing. There is no red crate, no
dark target, no ratchet row — the four twins have compiled green and disagreed for **20 days**.

**Disposition — ⚠ CROSS-LANE, NOT FIXED HERE.** A live lane owns this repair right now:

* `confined-swarm/src/lib.rs` — **dirty**, carrying the two `match` arms plus a comment that names
  `e1d0a028f` and both missed twins.
* `confined-swarm/src/tests.rs` — **dirty**, +52 lines.
* `commons-arbiter/src/tests.rs` — **dirty**, +59 lines: a test named
  `the_receipt_id_fingerprints_the_live_leg_and_the_stark_leg`, asserting exactly the three poles
  above.
* `commons-arbiter/src/lib.rs` — **clean, and still missing the fix.**

So that lane's `commons-arbiter` test is its RED-BEFORE and the `lib.rs` hunk is the half it has not
written yet. Editing through it would clobber a live working set. **Reported, not touched.**

---

## 2. `RECEIPT_COMMIT_DOMAIN` — the version rotation is itself half-applied

**The fix.** `e1d0a028f` rotated the receipt domain when the digest shape changed.

| Crate | Value | Read from |
|---|---|---|
| `attested-dm` | `b"attested-dm-narration-receipt-v2"` | `attested-dm/src/lib.rs:205` |
| `commons-arbiter` | `b"commons-arbiter-ruling-receipt-v1"` | `commons-arbiter/src/lib.rs:76` |
| `confined-swarm` | `b"confined-swarm-report-receipt-v1"` | `confined-swarm/src/lib.rs:60` |

**Cost.** *Lower than it looks, and I will not inflate it.* These are **per-crate namespaces** —
`commons-arbiter-…` can never collide with `attested-dm-…` — so there is no cross-crate confusion.
The real defect is narrower: one tag now covers **three different digest shapes** within its own
crate (pre-`e1d0a028f`; post-`f71f7f35e` content-commit widening; post-optional-legs), so a stored
v1-shape receipt and a v3-shape receipt are compared under the same domain. Greenfield: nothing
holds either, and `commons-arbiter`/`confined-swarm` have not compiled since 08-01 anyway.

**Compiles?** Yes. **Disposition:** report. Same files as #1; the owning lane should rotate to `-v2`
in the same commit that lands the legs, or state why not.

---

## 3. ⚑ A refusal threshold written against a width the value did not have — unsatisfiable for 10 days, then repaired **by accident**

This is the census's most interesting shape, because it is a half-applied fix running *backwards*: a
widening silently **fixed** a gate that had been dead, and nobody noticed the gate had been dead.

**The refusal.** `tee-verify/src/oracle_mark.rs:283`, in
`GradedMark::from_verified_zktls_session` (feature `zktls-producer`):

```rust
// A real zkoracle content commitment is a 32-byte digest; anything shorter is not one.
if content_commit.len() < 32 {
    return Err(MarkError::PriceDecode(format!(
        "zktls provenance requires a >=32-byte content commitment (the zkoracle connect \
         target); got {} bytes", content_commit.len())));
}
```

Introduced `b1b9331dd` (**2026-07-22**, *"wip: checkpoint PQ TEE and oracle hardening"*).

**Both sides, read.** Its only sanctioned caller is
`zkoracle-prove/tests/oracle_mark_zktls.rs:30`:

```rust
bincode::serialize(&att.content_commit).expect("BabyBear content commitment serializes")
```

At `b1b9331dd` the field was `pub content_commit: BabyBear` (verified:
`git show b1b9331dd:zkoracle-prove/src/attestation.rs` line 89), and `BabyBear`'s `Serialize` is
`serializer.serialize_u32(self.canonical_val())` (`circuit/src/field.rs:65-71`) — bincode fixint,
**4 bytes**. `4 < 32`, so the constructor refused **every honest input**, and
`a_genuine_zktls_price_mints_a_graded_mark` was RED from 2026-07-22 until the 08-01 widening made
the field `[BabyBear; 8]` = 8 × 4 = **32 bincode bytes exactly**.

**Measured today:** `cargo test -p dregg-zkoracle-prove --test oracle_mark_zktls` → `2 passed`.

**The residual, and it is current.** The refusal's stated reason is **false about the value it now
admits**. A `ContentCommit` is not a 32-byte digest; it is eight canonical BabyBear felts —
`8 × 30.906891 = 247.26` bits of image carried in 32 bytes. The gate passes by a **coincidence of
encoding arithmetic**, pinned against no independent source:

* `CONTENT_COMMIT_W = 7` → 28 bytes → silently refuses everything again (a dead fail-closed lane);
* `CONTENT_COMMIT_W = 9` (the `Digest9Key` shape the repo names for KEY injectivity) → 36 bytes →
  silently passes, and the message still says "32-byte digest".

That is *a pin against nothing* — the decoration shape, not a gate.

**Why I did not fix it.** `tee-verify` **deliberately** does not depend on `dregg-zkoracle-prove`
(its own doc: this crate "CANNOT verify the session … established UPSTREAM"), so it cannot name
`CONTENT_COMMIT_W`, and the honest fix is a design fork — invert the dependency, pass a typed
`ContentCommit` instead of `Vec<u8>`, or move the width assertion to the caller. **Judgement, so
reported rather than guessed.**

---

## 4. ✅ FIXED — `narrow_felt_from_slot_low4`: the `node8` widening left two false citations inside the file it widened

**The fix.** The adjacency / non-membership `node8` cutover widened every tree root in
`turn/src/executor/membership_verifier.rs` from ONE felt to an 8-felt `Digest8`:
`root_digest_from_slot` reads eight canonical 4-byte LE limbs, `adjacency_commitment_bytes`
(`:492`) emits all eight, `adjacency_compress` stopped projecting lane 0, `adjacency_leaf_cmp`
compares all eight lanes. The narrow reader `narrow_felt_from_slot_low4` (`:137`) survived for
**one** domain, and its own doc says so, emphatically:

> ⚠ **THE SURVIVING ONE-FELT SLOT CONVENTION — NOT a tree root.** … exactly ONE domain in this file
> still uses it: the **BridgePredicate `fact_commitment`**, which is a committed scalar and not a
> tree at all … **no tree root shares this byte convention any more, and a future reader must not
> "unify" them back.**

**Who did not get it — two comments in that same file, contradicting that paragraph directly:**

* `:1470` (the **production** call site, `BridgePredicateStarkVerifier::verify`) said the narrow
  form was *"the `narrow_felt_from_slot_low4` convention **shared with MerkleMembership**"*.
  MerkleMembership moved to `root_digest_from_slot` at the cutover. Flatly false, and it is the
  precise "unify them back" the definition forbids.
* `:2079` (test `e2e_consecutive_non_membership_accepts`) said *"The cell's predicate commitment is
  the set root **felt**'s LE bytes (the adjacency verifier **reads it via**
  `narrow_felt_from_slot_low4`)"* — while the line under it calls `adjacency_commitment_bytes(root8)`,
  which writes all eight limbs, and the adjacency verifier reads them with `root_digest_from_slot`.

**Cost.** **Zero to the executing path** — say that plainly; the code was already correct. The cost
is to the next reader, who is told the narrow convention is shared with a tree root. Acting on that
comment re-narrows the adjacency root from `p^8` to `p`, taking the **collision** bound (the
governing one: the attacker mints *both* leaves of the pair) from `2^123.63` to **`2^15.45`** —
~44,900 Poseidon2 evaluations, which is the exact forgery
`circuit/tests/adjacency_forge_tooth.rs` exists to exhibit, and it is a double spend
(`verify_nullifier_nonmembership` accepts a spent nullifier as fresh).

**Compiles?** Yes — the file is green and always was; that is why nothing caught this for the whole
life of the cutover.

**Detected by:** the repo's own `scripts/check-mirror-gates.sh`, rule `D2-cited-consumer-absent`,
firing **NEW** (not baselined).

**Fixed in:** `turn/src/executor/membership_verifier.rs` — both comments now state what the code
does and record what they used to say and when it stopped being true.

> ⚠ **A note against laundering.** The gate's Rule 2 fires on the phrase *"reads it via `F`"* when
> `F` has no caller outside its crate — and `narrow_felt_from_slot_low4` is crate-private, so it can
> **never** satisfy that rule. Silence is therefore achievable by rewording alone. That is not what
> happened: the original claim was false *in substance* (the adjacency verifier does not use that
> function at all), and the replacement asserts no external consumer because there is none. The
> mutation below is the evidence.

> ⚠ **A gate defect I did not fix.** The finding labels `:137` and `:1473` as `in-crate test
> caller`. `:137` is the **definition** and `:1473` is **production** code
> (`BridgePredicateStarkVerifier::verify`); `mirror_gates.py:770` hardcodes that label regardless of
> `is_test_at`. `scripts/` has a live lane (`local-gates.sh`, `check-doc-refs.sh`,
> `guard-discipline-baseline.txt` all dirty) — reported, not touched.

### Gate evidence

**RED BEFORE** (verbatim, `bash scripts/check-mirror-gates.sh`):

```
  findings: 40   baselined: 39   NEW: 1   stale baseline: 1   advisory leads: 83
  [D2/D2-cited-consumer-absent] the docs say a consumer "reads it via `narrow_felt_from_slot_low4`",
  but `narrow_felt_from_slot_low4` has no caller outside `dregg-turn`'s own tests — the cited
  consumer does not exist. Either a consumer reads it (cite that call), or the claim is a name, not
  a proof.
        turn/src/executor/membership_verifier.rs:1  the claim [dregg-turn]
        key: D2-reads:dregg-turn:narrow_felt_from_slot_low4
```

**GREEN AFTER:** `findings: 39   baselined: 39   NEW: 0`.

**MUTATION — the gate still bites.** Re-inserting the exact false sentence into the repaired comment
returned `NEW: 1` under the identical key `D2-reads:dregg-turn:narrow_felt_from_slot_low4`; the
probe was reverted from a byte-exact backup and the sweep re-confirmed `NEW: 0`. A gate that was not
tried against its own defect is a suspicion, not a gate.

**Where it runs:** `.github/workflows/mirror-gates.yml:43` (`./scripts/check-mirror-gates.sh
--report`) and `scripts/local-gates.sh:173` (`mirror-gates|900|…`). ⚠ Per
`minted-fail-open-gate-class`, `main` is not branch-protected — this **reports**, it does not block.

---

## 5. `scripts/mirror-gates/baseline.txt` carries a stale row

The same sweep reports, in both directions as designed:

```
STALE BASELINE — these no longer fire. The ratchet only turns one way: delete them
  A1:adjacency_membership_emit_gate.rs:GOLDEN_JSON:dregg-membership-adjacency::poseidon2-v1  # A/A1-second-author
```

Pre-existing (present before this lane's edit, and after). It is the same `node8`/adjacency cutover
that produced #4 — the emit gate stopped being a second author for that golden and nobody deleted
the row. **Not fixed:** `scripts/` has a live lane in it.

---

## Checked and NOT a divergence

Read both sides in each case; each is correct as it stands. Listed so this census can be falsified.

* **`sel4/dregg-pd/executor-pd/crypto-floor` — the model case, and the reason the census is not
  longer.** This crate is **outside the cargo workspace entirely** (its own `[workspace]` table and
  `Cargo.lock`; not a member, not even in `exclude`), is `no_std`, and **does not build on the host
  at all** — so `cargo check --workspace` never touches it and a `#[cfg(test)]` module inside it
  could never go red. It carries hand-maintained twins of `bytes_to_lanes`, `hash_2_to_1`,
  `hash_4_to_1`, `hash_many` and `hash_bytes`. **Both copies got the 2026-08-01 repair** (the
  aliasing `from_bytes_packed` is gone from both; both absorb `BabyBear::bytes_to_lanes`) — verified
  by reading both bodies, not by grep. And the drift detector lives **where it can run**:
  `circuit/tests/bytes_lanes_injective.rs::the_out_of_workspace_crypto_floor_twin_has_not_drifted`
  reads the out-of-workspace source from a crate that does build, and asserts the retired packer has
  not reappeared and the `2^16` radix + four-lane header survive. This is exactly the pattern the
  seed's twins lacked.
* **`NULLIFIER_DOMAIN` — a name collision, not a drift.** `circuit/src/descriptor_ir2.rs:343` is
  `u32 = 3`, a **wire domain code** for the universal-memory insert-only discipline;
  `crypto-floor/src/lib.rs:208` is `u64 = 0x6e_75_6c_6c` (`"null"`), a **Poseidon2 domain separator**
  for `dreggcf_nullifier`. Different objects that share a spelling.
* **`MIN_DIGEST_WORD_BITS` = 31 vs 0.** `circuit-prove/src/mina_pasta_fixture_suite.rs:409` = 31
  ("a Merkle root that fits in 31 bits is a root the Mina-Poseidon hash never touched");
  `circuit/src/mina_fixture_emit.rs:908` = 0, with the reason stated at the site — "the digest word
  field IS `Val` here, so there is nothing a bit floor could catch and the check is **skipped, not
  faked**." A floor of 0 is normally the "cannot fail" smell; here it is disclosed and correct.
* **`hash_string` / `hash_u64s` — BE vs LE, four copies, two conventions.**
  `dreggnet-adventure/src/lib.rs:704` and `dreggnet-offerings/src/overworld.rs:1277,1284` use
  `to_be_bytes` for the length prefix; `dreggnet-party/src/encounter.rs:1381,1386` and
  `dreggnet-party/src/lobby.rs:559` use `to_le_bytes`. Each digest is length-prefixed and consumed
  only inside its own crate, and **no cross-crate comparison of these digests exists**. A
  consistency drift with no bound attached — not a half-applied fix.
* **`leaf_hash` / `node_hash` / `merkle_path` in `cell/src/nullifier_set.rs` vs
  `token/src/revocation.rs`.** Near-identical bodies, correctly domain-separated:
  `blake3::Hasher::new_derive_key("dregg-nullifier-{leaf,node} v1")` against
  `"dregg-revocation-{leaf,node} v1"`, and leaf/node separated from each other in both.
* **`circuit/src/descriptor_ir2.rs` vs
  `docs/deos/artifacts/direct-logic-dregg-workloads-2026-07-22-stability-v2/inputs/rust/descriptor_ir2.rs`.**
  Several refusal tests differ (the artifact inlines `reason.contains(...)`; the live file uses the
  `assert_constraint_refusal` helper). The artifact is **frozen benchmark evidence**, pinned as it
  was run, and is on `.github/dark-targets.txt` by design. Recompiling it would destroy what it
  documents.
* **`assert_constraint_refusal`** — one definition (`circuit/src/descriptor_ir2.rs:7187`), 16
  callers, no twin.

---

## What the sweep covered, and what it does not license

* **`cargo check --workspace --all-targets --keep-going`** over the working tree: **exactly one red
  target** — `dregg-circuit` test `pasta_sound_mul_scaling_measure`, which is an **untracked** file
  (`?? circuit/tests/pasta_sound_mul_scaling_measure.rs`) belonging to a live lane, not a dark
  target and not mine. Every other target compiles. **So the seed's own mechanism — a red crate
  camouflaging a missed fix — has no other instance in the default resolve right now.**
* **4,286 tracked `.rs` files** clustered by function name; 705 names carry cross-crate bodies that
  are ≥80% similar but **not identical**. 155 of those have security-shaped names and were read.
* **388 constant names** hold different values under the same spelling in ≥2 crates; the
  security-shaped subset in `src/` was read.
* `scripts/check-mirror-gates.sh` — full run, canary suite 20/20, findings triaged above.

**⚠ What this does NOT cover, stated so the number is not over-read.** The default resolve is not
all features. `.github/dark-targets.txt` records **63 `never-run` targets** and **20 dark files**
that no `cargo check` reaches at all — a whole-file `#![cfg(feature = "x")]` target *builds, runs,
and prints `test result: ok. 0 passed`*, which is indistinguishable from a passing suite. A
half-applied fix living behind an off-by-default feature would not appear in this census. That
population is the natural next sweep, and it is where finding #3 was hiding (behind
`zktls-producer`, reachable only because a dev-dependency happened to unify the feature on).
