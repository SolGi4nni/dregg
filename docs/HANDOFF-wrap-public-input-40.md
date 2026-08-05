# HANDOFF — the wrap public input, 40 words, and what stands between us and them

**For the live wrap lanes** (W-FINALIZE's sponge, the step→wrap chain, the commitment stages, the
bucketed MSM). Written 2026-08-05 by the lane that ran Mina's own verifiers on our artifacts; the
verdicts are in `GOAL-MINA-SEMANTIC-LIGHTCLIENTS.md`, section 2026-08-05.

## Why this list exists

`kimchi::verifier::verify`, under the verifier index **Mina itself builds** from the 1796 bytes the
devnet account holds, refuses our proof with its own words:

```
Err(IncorrectPubicInputLength(40))   "the public input is of an unexpected size (expected 40)"
```

and accepts it the moment the public input is 40 words long. **The public input is the only thing
left between a proof of a Lean-emitted wrap rung and Mina's kimchi verifier at a key the chain
holds.** The 28 commitments, the SRS, the domain, `zk_rows`, `prev_challenges`, the feature flags and
the IPA opening already agree exactly (28/28).

⚠ **Do not close it by padding.** The probe that padded to 40 with zeros is labelled a probe for a
reason: **Pickles DERIVES all 40 from the statement** (`/Users/ember/dev/mina-rust/crates/ledger/src/proofs/public_input/prepared_statement.rs:53-182`,
consumed at `verification.rs:886`) and gives a prover no way to supply them. A padded vector
demonstrates the plumbing and proves nothing about the circuit.

## ⚑ It is not "18 missing". It is 16 — and the count is not the blocker

`shapeWrap.pubWords = 22` is `closingRows`' count only. `rungPub .close = pubWords + 2`
(`KimchiWrapMainCore.lean:5216-5235`), because `w9_prev` ties Mina slot 12 and `w11_wraphack` ties
Mina slot 11. **The emitted `w12_close` already carries 24.**

⚠ **Two stale strings to fix while you are in there** (this lane did not edit the Lean — six of you
are live in it):
- `KimchiWrapMainCore.lean:5395` — *"upstream's `PRIMARY_LEN` is 40 and the **18**-word gap"*. It is 16.
- `KimchiWrapMainCore.lean:1258-1259` and `:1306-1308` attribute slots 0–4 and 9 to **W-FINALIZE**.
  Superseded by `KimchiWrapMain.lean:581-584` (2026-08-05): they are *consumed* by
  **W-FTCOMM / W-COMBINE / W-BULLET**, and no wrap sub-circuit derives them at all.

**Three deltas, and the count is the smallest of them:**

1. **ORDER.** Our external slot `i` is Mina's slot `i` for **no** `i`. Our external 0 is β, which is
   Mina's slot **5**. Slot order is the whole correctness question — a right value at a wrong index
   is a wrong public input.
2. **WIDTH.** The emitted `public_input_size` is `rungPub` (22/23/24), never 40. `WRAP_PRIMARY_LEN := 40`
   exists at `KimchiWrapMainCore.lean:130` and **no emitted shape consumes it**.
3. **INSTANCE.** The exposed values are this assembly's transcript over *fixture* commitments
   (`ftcSVal := wrapFixtureQ 22 j` at `:1945-1947`, `combXiVal := wrapFixtureQ 30 0` at `:3562`,
   `bullScalVal := wrapFixtureQ (40+j) 0` at `:4020-4023`), not any real proof's. The Lean says so
   itself at `:1240`: *"THE PUBLIC VECTOR IS THIS ASSEMBLY'S, NOT MINA'S, AND THE DIFFERENCE IS STATED."*

## Mina's 40, in order

Authority: `prepared_statement.rs:53-182`. Arity 5 + 2 + 3 + 3 + **16** + 1 + 8 + 1 + 1 = 40; the 16
is `bulletproof_challenges`, the **step** proof's IPA rounds, matching `shapeWrap.ipaRounds = 16`.

| slot | word | kind |
|---|---|---|
| 0–4 | `combined_inner_product`, `b`, `zeta_to_srs_length`, `zeta_to_domain_size`, `perm` — each `.shifted` | full field |
| 5–6 | `beta`, `gamma` | 128-bit challenge |
| 7–9 | `alpha`, `zeta`, `xi` | 128-bit scalar challenge |
| 10–12 | `sponge_digest_before_evaluations`, `messages_for_next_wrap_proof`, `messages_for_next_step_proof` | 255-bit digest |
| 13–28 | `bulletproof_challenges[0..15]` | 128-bit each |
| 29 | `branch_data` = `(domain_log2 << 2) \| proofs_verified` | 10 bits |
| 30–37 | the eight kimchi feature flags | 1 bit each |
| 38 | `uses_lookup` (OR of rc0, rc1, ffmul, xor, rot, lookup) | 1 bit |
| 39 | the lookup challenge value, else `0` | 128 bits |

⚑ **β and γ come BEFORE α, ζ, ξ** — the `// Challenge` block at `:106-110` precedes `// Scalar
challenge` at `:112-117`. Our tree already learned this the hard way; it is recorded as a measured
correction at `Dregg2/Bridge/MinaWrapPublicInput.lean:187-200`.

## What we hold: 24 of the 40

| ours | word | Mina slot | derived at |
|---|---|---|---|
| 0–3 | β, γ, α′, ζ′ prechallenges | 5, 6, 7, 8 | `w4_bind` |
| 4 | `forkSqueeze` = `sponge_digest_before_evaluations` | 10 | `w4_bind` |
| 5–20 | 16 `bullet_reduce` prechallenges | 13–28 | `w4_bind` |
| 21 | `branchVars.packed` | 29 | `w4_bind` |
| 22 | `messages_for_next_step_proof` | **12** | `w9_prev` (`:2240-2242`) |
| 23 | `messages_for_next_wrap_proof` | **11** | `w11_wraphack` (`:2407-2408`, `:2426`) |

⚠ At the **smoke** shape (`pubWords = 6`, `ipaRounds = 3`) `branch_data` is not exposed at all —
slot 29 is absent. Anything testing against the smoke fixtures should know that.

## The 16, with owners

**Six to EXPOSE — none to compute.** `wrap_main` passes these through as `~advice`/`~plonk`/`~xi`
(`wrap_main.ml:405-414`) and never checks them; what checks them is the *next* proof's W-FINALIZE.
So the owner is the sub-circuit that **consumes** it:

| slot | word | consumer | the cell that already exists |
|---|---|---|---|
| 0 | `combined_inner_product` | **W-BULLET** (`w11_bullet`, §24) | `:3872-3875`, `:3786` |
| 1 | `b` | **W-BULLET** | `:3790`, `:4020-4023` |
| 2 | `zeta_to_srs_length` | **W-FTCOMM** (`w8_ftcomm`, §17) | `ftcS` at `ftcScalarIdx = 1`, `:1940-1943` |
| 3 | `zeta_to_domain_size` | **W-FTCOMM** | `ftcS` at `ftcScalarIdx = 2` |
| 4 | `perm` | **W-FTCOMM** | `ftcS` at `ftcScalarIdx = 0`, `:1845` |
| 9 | `xi` | **W-COMBINE** (`w10_combine`, §23) | `combXiV s sp`, `:3656`, all 46 endo ladders share it |

**Ten to emit as CONSTANT ZERO — slots 30–39.** No sub-circuit owner, and there must not be one:
`KimchiWrapMainCore.lean:1267-1268` records that upstream never constrains them either, and
`:1276-1281` pins all ten to zero on a real devnet wrap proof
(`MinaWrapPublicCommGate.PUBLIC_INPUT`, slot 29 = 67, slots 30–39 ten literal zeros) with the
warning that tying them to variables would be **"defect class 5 wearing a public vector."**

⚠ **One thing to settle first.** openmina's `to_public_input_cvar` **drops `feature_flags` entirely**
(`prepared_statement.rs:204`) and pads with 9 × `bits(1)` + 1 × `bits(128)`, `Constant` when
`hack_feature_flags = OptFlag::No`, **`Var` when `Maybe`**, `todo!()` when `Yes` — with upstream's own
`// TODO: Find out how this padding works` at `:290`. Which one the side-loaded path passes is not
settled in our tree and decides whether slots 30–39 are constants or variables.

## ⚑ A design fork, not a defect — surface it before anyone starts

`rungPub`'s own comment refuses the cheap win by name: *"W-COMBINE derives no NEW statement word …
**A public word on `xi` here would be a fixture**"* (`KimchiWrapMainCore.lean:5231-5232`). That
objection holds a **derivation** standard: a rung may expose only what it computes.

Upstream's standard is weaker — slots 0–4 and 9 *are* free pass-throughs in `wrap_main`, checked by
the next proof, never by this one. On the upstream standard, four of the six (2, 3, 4, 9) already
have circuit-read cells and are a closing `Generic` half each. On this file's standard they are
blocked until a *next* proof's W-FINALIZE exists.

**Both are defensible and they give different work. It is the operator's call, not a lane's**, and it
should be made before someone spends a night on the wrong one.

## Files a lane will touch

`metatheory/Dregg2/Circuit/Emit/KimchiWrapMainCore.lean` — `WRAP_PRIMARY_LEN` (:130), §10 census
(:1238-1343), `exposedVars` (:1319), `closingRows` (:1340), `AUXW` (:939), `rungPub` (:5216),
`exposedVarsAt` (:5240), `shapeWrap.pubWords` (:5399), and the ties at :2242 and :2426. §13's list is
`metatheory/Dregg2/Circuit/Emit/KimchiWrapMain.lean:440-689`. Ground truth for the 40 stays
`/Users/ember/dev/mina-rust/crates/ledger/src/proofs/public_input/prepared_statement.rs:53-182`.

## How you will know it worked

```
cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
  --bin mina_onchain_index_probe -- --vk <onchain-vk.json> --circuit <your-emission.json> --log2-domain 14
```

`[B]` stops saying `IncorrectPubicInputLength(40)` and starts saying `Ok` **on the circuit's own
public vector, with no padding**. `[A]` must stay 28/28 against a key derived from that same
emission, and `[C]`'s two word-moves must stay `OpenProof`.

---

## ⚑ CLOSED 2026-08-05 — the layout landed, and here is what the probe said

Commit `b75180149` (`feat(wrap): the public vector moves into Mina's own slot layout`) does items
1 and 2 of "Three deltas": ORDER and WIDTH. Item 3, INSTANCE, is untouched and stays open.

**22 vs 24 reconciled at source, and it was neither of the two candidates.** `pubWords = 22` is the
width of `exposedVars` — the CLOSING rung's derivation. `exposedVarsAt` appends slot 12 at `.prev`
and slot 11 at `.wraphack`; `22 + 1 + 1 = 24 = WRAP_PINNED_SLOTS.length`. No slot was missing and
`pubWords` counts exactly what its docblock says. **Pure layout, no new derivation.**

**What Mina's own kimchi verifier says now**, `mina_onchain_index_probe`, release, on the emitted
`wrapmain_smoke_w4_bind` (532 Lean rows, `public_input_size = 40`, domain 2^14), both directions run:

| `--vk` | [A] commitments | [B] `kimchi::verifier::verify` | [C] 40 slot-moves |
|---|---|---|---|
| key derived from THIS emission | **28 / 28** | **`Ok` — accepted** | **REFUSED 40/40** |
| the key devnet holds (`3406194937…`) | 4 / 28 | `Err(OpenProof)` | REFUSED 40/40 |

No padding leg remains: the emission IS forty words in Pickles' order, so the probe's `[B']` is
deleted rather than relabelled. `[C]` moved from two hand-picked words to all forty.

⚠ **THE DEVNET KEY IS STALE AND RE-REGISTRATION IS THE OPERATOR'S.** 40 public rows instead of 6
shifts every gate row, so the account's 1796 bytes no longer describe the circuit — the second row
above is that fact, measured. The new `w4_bind` key hashes
`3188784766661697483171188289432725486872584657562879441369053845609461086197`.

**The six pass-throughs are still unread, and the fork below is still open.** They are DECLARED
(`wrapInertOk`), the declaration is checked against the emission as an EQUALITY at every rung, and
`pickles-wrapmain-harness`'s polarity (5) MEASURES the split: the sigma leg refuses at every derived
slot and accepts at every declared-unread one. The attribution in the Lean was corrected in the same
commit — the six are read by W-FTCOMM / W-COMBINE / W-BULLET and checked by the next proof, not by
W-FINALIZE, exactly as this document said.

⚠ Still unsettled and untouched: which of `to_public_input_cvar`'s branches the side-loaded path
takes, i.e. whether slots 30–39 are constants or variables. They are emitted as constant zero.

---

## ⚑ CLOSED 2026-08-05 (second pass) — INSTANCE, the last of the three deltas

The first pass closed ORDER and WIDTH and left **INSTANCE** open: *"the exposed values are this
assembly's transcript over fixture commitments, not any real proof's."* That is closed for the six
words it was really about, and the fork above it is closed too.

### What the six now are

`ftcSVal`, `combXiVal` and `bullScalVal 0` were `wrapFixtureQ` draws — a deterministic filler. They
are now `expand_deferred`'s own outputs for a real step proof, read out of
`PreparedStatement::to_public_input(40)` and carried by
`metatheory/Dregg2/Circuit/Emit/MinaWrapDeferredWords.lean` (7 theorems, kernel-clean).

⚠ **Two corrections to this document's own list.** The handoff that generated this pass named six
*families* — `ftcSVal`, `combXiVal`, `bullScalVal`, `finColVal`, `finPZetaVal`, `finFtEval1Val`.
Read at source:

- **`finColVal` / `finPZetaVal` / `finFtEval1Val` are not among Mina's forty at all.** They are
  `Req.Evals` witnesses — the PREVIOUS proof's evaluation columns, `ft_eval1` and `p(ζ)` — which
  arrive on the wire as `prev_evals`, not in the public input. `wrap-public-input.json` has no such
  word and no fixture there could have come from it. They are untouched and still fixtures.
- **`bullScalVal 1` and `2` are `z₁`/`z₂`**, `openings_proof`'s, with no slot in the forty. Only
  index 0 (`advice.b`, slot 1) is a public word. They are untouched *deliberately* — measuring them
  would put a real value in a cell whose honesty is that it is free.
- **`bullCipVal` was never a fixture draw**: slot 0 reaches its cell through the transcript tape
  (`itemVal T_CIP`), which fell through to `wrapFixture`. That fall-through is now `DEF_CIP`, which
  is also the more faithful shape — `wrap_verifier.ml:395` absorbs `advice.combined_inner_product`,
  i.e. the public word itself.

So the real set is **five values across three families plus one transcript tape entry**, covering
Mina slots 0, 1, 2, 3, 4 and 9.

### ⚑ The fixture is REPRODUCIBLE now, and it had to become so first

`pickles_kimchi_marshal` proved with `OsRng`. Every run produced a different step proof and
therefore a different forty, so a Lean constant carrying them would have been stale the moment the
binary was re-run — the loop (run → read → bake → re-emit) had **no fixed point**. Both provers now
draw from a seeded `StdRng`. Two consecutive runs are byte-identical in `wrap-public-input.json`,
`marshalled.binprot` and `marshalled.o1js-proof.json`; `PROOF_MARSHAL_RESULT=GREEN` both times.

Nothing is hidden by seeding: the blinding protects a smoke circuit's witness, published next door,
and the proofs are still produced by the real prover and still checked by `batch_verify`.

### The fork is closed, and it was not a fork

`wrap_main` reads slots 0–4 and 9 and checks none. The derivation horn said "expose only what you
compute"; upstream's said "they are free pass-throughs". **Pickles recomputes all six and
substitutes them**, so the derivation horn describes a proof nobody intends to hand to Pickles. The
readers consume the public words now.

`WRAP_PASSTHROUGH_SLOTS` is a **third category** beside `WRAP_PINNED_SLOTS` and
`WRAP_UNPINNED_SLOTS` — read-but-not-checked. The forty split **24 constrained + 6 read + 10 dead**,
and `wraphack_closes_every_pinned_statement_word` states that as a real three-way partition. The
old statement was `PINNED != UNPINNED` over the forty and is now FALSE, not stale: six slots were in
neither list.

⚠ **This removes six free witnesses.** A prover could previously choose `perm`, `ξ`, `b` and the
rest freely. The harness's polarity (5) sigma leg measures the change: those slots move from
"accepts a cell flip" to "refuses one".

### What Mina's own verifier says — `mina_onchain_index_probe`, release, on `w11_bullet`

3691 Lean rows, `public_input_size = 40`, domain 2^14, all six tied. Both directions run:

| `--vk` | [A] commitments | [B] `kimchi::verifier::verify` | [C] 40 slot-moves |
|---|---|---|---|
| key derived from THIS emission | **28 / 28** | **`Ok` — MINA'S OWN VERIFIER ACCEPTED IT** | REFUSED **40 / 40** |
| a mismatched key (`w4_bind`'s) | 1 / 28 | **`Err(OpenProof)`** *"the opening proof failed to verify"* | REFUSED 40 / 40 |

`PROBE_RESULT same_index=true control=true mina_40words=true falsifiers_refused=40/40`.

⚠ **[C] is the VECTOR leg and does not discriminate read from unread** — the binary says so itself.
Moving any public word changes the public commitment, so 40/40 was already true when six of the
slots were inert. **The discriminating instrument is polarity (5)'s SIGMA leg**, and quoting [C] as
evidence that the six are bound would be quoting the flattering number of a pair.

### ⚑ How far this actually gets us — the emitted vector against Mina's

At `w12_close`, emitted public vector vs `to_public_input(40)`: **16 of 40 agree** — slots 0, 1, 2,
3, 4, 9 (the six, exactly) and 30–39 (the ten zeros). **The other 24 do not, and that is the honest
residue**: they are the words this circuit DERIVES from its own transcript, which runs over fixture
commitments rather than over the step proof those forty words came from.

So: **`kimchi::verifier::verify` accepts. Pickles would not.** A Pickles wrap proof's slots 5–8, 10
and 13–28 are the step proof's own challenges, asserted equal in-circuit; ours are our fixture
transcript's. Closing THAT is the next thing, and it is a bigger object than this pass: it means the
wrap assembly's sponge absorbing the real step proof's commitments, not a fixture's.

### A red this pass found and did not cause

`KimchiStepWrapChain.the_bend_moves_every_transcript_derived_public_word` was **already failing at
HEAD**. `wrapPublicAt` returns a vector indexed by MINA'S SLOT since the layout commit, while the
theorem still read `(List.range 21)` — `exposedVars`' POSITION indexing from when the vector was
dense. Those agree for no index: `range 21` names slots 0–20, eight of which (0, 1, 2, 3, 4, 9, 11,
12) `w4_bind` does not derive and which are therefore ZERO in both emissions, so a conjunct asserted
that a zero differs from itself. `wrapSlots` and `wrapSlotsAt`'s `.bind` branch are untouched by
this pass, so the eight are the same eight before and after it. Restated over
`wrapSlotsAt … .bind` with `branch_data` excluded by SLOT.

### What re-emits

Every rung's witness from `w4_bind` up — `itemVal T_CIP` moved, and the 16 IPA prechallenges and `c`
are squeezed after it (β/γ/α/ζ and the fork digest are squeezed before, and do not move). All 30
smoke fixtures come from one run. `w3_branch` and `w4_bind` keep their VK hashes
(`3188784766661697483171188289432725486872584657562879441369053845609461086197` for `w4_bind`) —
they sit below `w8_ftcomm` and tie none of the six, so their gates are unchanged.

⚠ **The devnet key is still stale and re-registration is still the operator's.** Untouched here.
