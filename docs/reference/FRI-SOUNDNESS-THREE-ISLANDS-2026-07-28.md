# The FRI soundness floor is three non-communicating islands, and the "51" is a leaf

*Surveyed 2026-07-28. No Lean was written — this is a map, and the reason it is only a map is
recorded in §5.*

The repo's standing record says the deployed FRI floor is **51 calculator bits**, an informal reading
**not attached to `verifyAlgo`**. That is true, and the situation underneath it is both more finished
and more precisely disjoint than the record suggests.

---

## 1. The ledger is a LEAF, and its one real theorem is arithmetic

`FriCommitPow.lean` and `FriDeployedHeightPairing.lean` are exactly what their docstrings claim — no
daylight between the prose and the Lean. Every theorem in them is `Nat`/bracket arithmetic over a
formula transcribed from BCIKS20 (eprint 2020/654, Lemma 8.2 / Thm 8.3) and ethSTARK eq. (20).

`deployed_wrap_commitBits` (`FriDeployedHeightPairing.lean:142`) proves `commitBits = 51` by
exhibiting the two-sided `Nat.log2` bracket. **That arithmetic step is genuinely machine-checked.
Nothing else is.** There is no `Strategy`, no `OracleComp`, no ε quantified over an adversary, and
`verifyAlgo` is never mentioned in either file.

This is not an oversight — it is structural, and it was measured rather than assumed:

    grep -l "commitBits\|epsC\b\|friCommitLedger"  →  ONLY the ledger family
    (FriLedger, FriLedgerSound, FriCommitPow, FriDeployedHeightPairing + ledger-internal callers)
    ZERO hits in any file that also mentions verifyAlgo / verifyAlgoO / Strategy / OracleComp

The ledger is a leaf, exactly as its own docstring says.

---

## 2. Three islands, and only one of them owns the 51

### Island A — the deterministic apex the light client actually runs
`CircuitSoundness.lean` (`verifyBatch:450`, `lightclient_unfoolable:571`) imports only `FriVerifier`
and `FriTranscriptBind`; `ClosureFinalAvail` / `KernelConfigSoundnessAvail` /
`AlgoStarkSoundKernelAvail` sit on top. The whole chain carries `[StarkSound]` /
`FriLdtExtractV3Cons` / `FriLdtExtractV3Faithful` as **Boolean, undischarged Props**. No probability
anywhere.

✅ **Side finding, and it is good news**: the vacuity wound recorded three days ago —
`friLdtExtractV3_makes_verifyBatch_reject_everything` (`FriLdtExtractDeployed.lean:304`) — **is now
repaired**, by the 07-25/07-28 cutover to `FriLdtExtractV3Faithful`, with its own non-vacuity
receipts at `:855-947`. Real progress since that note was written. Still Boolean repair, not a
probability.

### Island B — the adversary-quantified chain, and it DOES reach the real `verifyAlgo`
This is the good surprise. `FriVerifierO.lean` proves `verifyAlgoO_run_eq` (`:537`):

    (verifyAlgoO …).eval perm = verifyAlgo perm …

— a **machine-checked faithfulness bridge** from an oracle-model verifier back to the literal
`FriVerifier.verifyAlgo`. `FriVerifierQuery/Merkle/FS.lean` build real ε-bounds on that bridge, and
`FriVerifierCompose` → `FriEpsFriComposedAdversary` compose them into
`εFriᵃ = εFS + εGrind + εMerkle + εQueryᵃ`, delivering `friLdtExtractV3_rom_adv_of_legs` (`:155`) in
exactly the shape one wants: `condProb C accepts_and_fails ≤ epsFriAdv …`.

Three things about it matter:

- Its `hcover` hypothesis — the one line connecting the abstract Boolean events to "`verifyAlgoO`
  accepted a proof whose extraction bundle actually fails" — is **named and explicitly left
  undischarged**, with the file saying so in as many words: *"this file does NOT discharge `hcover`
  and does not pretend to."* That is the word↔proof bridge, carried as a visible hypothesis rather
  than an axiom. **The tree's own authors already did the honest thing here.**
- ⚑ **`ε_C` / `commitBits` is NOT one of the four legs.** There is no commit-phase term in this
  composition at all. The 51 does not enter the only chain that reaches `verifyAlgo`.
- ⚑ **And its own headline theorem, `epsFriAdv_deployed_vacuous_at_2_31`, proves the whole composed
  bound is `≥ 1` at a 2^31-query adversary.** So even where the attachment IS real, it currently
  certifies nothing at deployed parameters.

### Island C — the L0–L6 correlated-agreement ladder reaches a different column
`CorrelatedAgreement/Interface.lean` is explicit and self-critical. The landed ladder (BCIKS20
**Thm 4.1**, UD regime) feeds `FriDecodedTraceWitness`'s `DecodedLdtLink` — the batch→column
trace-decode requirement — and its own text says the per-fold bits it yields (**≈101** over the
quartic extension) are *"NOT the ledger's 109/111. Those remain separate objects; reporting them as
one column was the error `FriJohnsonRadiusGap` already named."*

Verified not stale: the ladder never references `commitBits`/`friCommitLedger`, and it addresses
**Thm 4.1** (correlated agreement for RS codes), not **Lemma 8.2 / Thm 8.3** (the round-by-round
commit-phase term the 51 is). **It does not reach ε_C, and the consumer interface already says so.**

---

## 3. ⚑ The piece closest to what ε_C is FOR is proved, and wired to nothing

`FriFoldConsistencyDichotomy.lean` — **974 lines, fully proved, no `sorry`** — proves exactly the
dichotomy BCIKS20's commit-phase term exists to cover: *either* a prover's fold stays consistent
(farness propagates as a combinatorial fact, no probability needed) *or* it deviates and is caught by
the query phase with a proven, priced probability. Its docstring says the other branch "*is NOT
proved here or anywhere in-tree*" — and then proves it.

    grep -rl "FriFoldConsistencyDichotomy"  →  itself, and FriPositiveRadiusSchedule.lean

**It is not a fifth leg in `FriEpsFriComposedAdversary`'s composition.**

⚑ If it were wired up through the same `hcover`-shaped bridge, **BCIKS20's separate ε_C addend may
not even be logically necessary for this codebase's actual proof strategy.** That is a genuinely
different resolution from "formalize Lemma 8.2", and the tree has not attempted it.

---

## 4. Where the chain stops — named precisely

Not one clean missing lemma. A stack of two, both already scaffolded in-tree, neither closeable at
lemma scale:

1. **The word↔proof bridge** — `FriVerifierCompose`'s `WordProofBridge` /
   `DeployedTraceExtract.DeployedFriEmbedding`, and `FriEpsFriComposedAdversary`'s `hcover`: a
   structure connecting `BatchProofData`'s committed columns to the abstract `(f : ι→F, f' : κ→F)`
   FRI-setup word pair the counting lemmas are stated over. Already named in-tree as a **carrier, not
   a theorem**, and flagged there as *"not a lemma-sized gap: it is the FRI-proximity-to-`VmTrace`
   decode."*
2. **A fifth, commit-phase leg** in the composed bound — a probability statement of Lemma 8.2's shape
   stated over `Strategy`/`OracleComp` rather than as bare `Nat` arithmetic. Two routes: formalize
   Lemma 8.2 (no attempt exists anywhere in the tree — only the `pdfs/` citation and the arithmetic
   transcription), or wire `FriFoldConsistencyDichotomy` in as that leg, which is tractable but needs
   `epsFriAdv_compose`'s union-bound proof extended.

---

## 5. Why this is a map and not a fix

Route (1) is an acknowledged multi-day formalization project by the tree's own authors. Route (2)
needs either the same scale of new mathematics or non-trivial surgery on an existing composed-bound
proof.

Attempting either under a single lane's budget risked producing **exactly the shape the task existed
to prevent: a new named carrier that looks like an attachment and isn't one.** So no Lean was
written, no edits were made, and `lake build Dregg2` is unaffected.

That is the right trade, and it is recorded here so the next reader starts from the map rather than
re-deriving it.
