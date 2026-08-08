/-
# Dregg2.Circuit.Emit.PicklesVerifyPreamble — the seven upstream verifier legs of
`verify_block` that this tree had NOT authored: `run_checks`' three, the two message/packing
legs of `verify_impl`, and `to_batch`'s two length legs.

## Provenance — READ AT SOURCE, not from a docblock

Everything here is transcribed from **`mina-rust @ 82480cd468f1963b73dc0b700161036411449e4c`**
(`/Users/ember/dev/mina-rust`, v0.19.0) and its pinned `kimchi` — `proof-systems` tag `0.3.0`,
rev `a73ca6ed580a346344ba80a88137b100237070dc` (`Cargo.lock`), unpacked at
`~/.cargo/git/checkouts/proof-systems-c874fc66c693964b/a73ca6e/kimchi`.

⚠ **`~/dev/openmina @ 8e68037a` is a STUB TWIN** — its `verify_impl` returns literal `true` with
the body commented out. It is not the object described here. `~/dev/mina` (OCaml) has no `.git`
and is corroboration only.

`verify_block` (`verification.rs:750-784`) is exactly

```
accumulator_check(srs, [proof])   AND   verify_impl(state_hash, proof, vk)
```

and `verify_impl` (`verification.rs:857-894`) is `compute_deferred_values` · `run_checks` ·
`get_message_for_next_step_proof` · `get_message_for_next_wrap_proof` · `get_prepared_statement`
· `to_public_input` · `verify_with`, conjoined with `run_checks`' verdict at `:893`.

## The seven legs, with the line that asserts each

| # | leg | source |
|---|---|---|
| **B1** | `non_chunking` — every evaluation vector length `≤ 1` | `verification.rs:568-629`, the verdict at `:628` |
| **B2** | `validate_feature_flags` consistent with the evaluations | `verification.rs:631-642`, body at `:74-142` |
| **B3** | step domain log2 `≤ BACKEND_TICK_ROUNDS_N` | `verification.rs:644-651` |
| **C2** | `messages_for_next_wrap_proof.hash()` | `verification.rs:875-876`; `messages.rs:57-63,84-107` |
| **C3** | `prepared_statement.to_public_input(npublic_input)` | `verification.rs:885-886`; `prepared_statement.rs:53-181` |
| **D1** | `prev_challenges.len()`, `public_input.len()` | `kimchi/src/verifier.rs:810-820` |
| **D2** | `check_proof_evals_len` | `kimchi/src/verifier.rs:822-831`, body at `:640-779` |

## ⚑ WHAT THIS FILE IS FOR — the finding that motivated it

`KimchiVerify.shapeOkRec`'s docblock calls it "**every** length/shape assert of `to_batch`'s
preamble". It is not. Measured 2026-08-08 against the two upstream lines it cites:

  * `shapeOkRec`'s second conjunct is `decide (0 < publicLen)` and its comment cites
    `verifier.rs:816-820`. That line is `public_input.len() != verifier_index.public` — an
    **equality between two independently-derived quantities**. `0 < publicLen` is not a weak
    version of it; it is a different predicate, and on the deployed path `publicLen` is
    **trusted config** (`mina_pickles::MinaWrapIndexParams::DEVNET_BLOCKCHAIN.public_len = 40`),
    so the conjunct compares a constant against zero and **cannot fail**.
    `the_deployed_gate_admits_a_public_input_it_should_refuse` below exhibits the accept.
  * `check_proof_evals_len` (D2) has no counterpart at all. `shapeOkRec` pins `chunkSize = 1`
    and the COUNTS of columns, but no evaluation vector's LENGTH is ever compared to it.

This matters because the two blindnesses compose with a third already proven in this tree:
`MinaWrapVkDigestChain.the_index_digest_cannot_see_the_circuit_shape` shows kimchi's index
`digest()` binds `public` to `_`, so an index taking 41 public inputs has the SAME digest, and
the pair is exhibited there. Nothing on the deployed path pins the public-input count to 40.

## CLOSURE KIND — say it plainly, per leg

None of these is closed **by constraint**: no AIR row forces any of them, and adding a column
whose value the prover picks and pinning it to 1 would force a claim, not a check. They are
authored here as the Lean-side DECISION and close by **consumer refusal** — the node evaluates
the compiled Lean and refuses the block — which is the same mechanism `shapeOkRec` itself has
always had. §6 states where each forcing lives. Nothing in this file is described as an AIR.
-/
import Dregg2.Circuit.Emit.KimchiVerify

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Dregg2.Circuit.Emit.PicklesVerifyPreamble

/-! ## §1 — B1: `non_chunking` (`verification.rs:568-629`).

The iterator at `:600-628` walks `w` (15), `coefficients` (15), `z`, `s` (6), the six unconditional
selectors, then `.iter()` over each OPTIONAL selector and each lookup evaluation — `Option::iter`
yields the element when `Some` and nothing when `None`, so absent evaluations contribute no pair.
Every yielded item is a `(zeta, zeta_omega)` pair of vectors, and the verdict at `:628` is

```rust
iter.all(|(a, b)| a.len() <= 1 && b.len() <= 1)
```

⚠ `≤ 1`, not `= 1`: an evaluation that is *absent* (length 0) passes B1. B1 is a **chunking**
bound, not a presence check — presence is B2's job, and reading B1 as "every column is present"
is the misreading this comment exists to stop. -/

/-- **`nonChunking`** — `verification.rs:628`. Each entry is one yielded pair's
`(zeta.len(), zeta_omega.len())`, in the iterator's order. -/
def nonChunking (evalLens : List (Nat × Nat)) : Bool :=
  evalLens.all (fun p => decide (p.1 ≤ 1) && decide (p.2 ≤ 1))

/-- The empty walk is vacuously non-chunked, exactly as `Iterator::all` is. Stated so the accept
below cannot be mistaken for evidence that anything was inspected. -/
theorem nonChunking_nil : nonChunking [] = true := rfl

/-- **`nonChunking_iff`** — the decision IS the upstream universal, so it is not a paraphrase. -/
theorem nonChunking_iff (evalLens : List (Nat × Nat)) :
    nonChunking evalLens = true ↔ ∀ p ∈ evalLens, p.1 ≤ 1 ∧ p.2 ≤ 1 := by
  unfold nonChunking
  simp [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-- **`nonChunking_refuses_a_chunked_column`** — BOTH sides of a pair are load-bearing: a proof
chunked only at `zeta_omega` is refused too. A one-sided transcription would pass the second. -/
theorem nonChunking_refuses_a_chunked_column :
    nonChunking [(1, 1), (1, 1), (0, 0)] = true
    ∧ nonChunking [(1, 1), (2, 1)] = false
    ∧ nonChunking [(1, 1), (1, 2)] = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### B1 as a wire summary — and why that is not a paraphrase.

The deployed gate speaks a `key=Nat` wire, so it cannot carry the list of pair lengths. It carries
the **maximum** instead, and the two theorems below make that a REDUCTION rather than a
restatement: `maxPairLen` bounds every element (`le_maxPairLen`), and the summary decision is
EQUIVALENT to the list decision (`maxPairLen_le_one_iff_nonChunking`). The count travels beside it
so an empty walk — which `nonChunking_nil` shows is vacuously true — is refused at the gate rather
than read as an accept. -/

/-- The largest length any evaluation vector in the walk reports. -/
def maxPairLen (l : List (Nat × Nat)) : Nat := (l.map (fun p => max p.1 p.2)).foldr max 0

/-- **`le_maxPairLen`** — the summary really is an upper bound on every element it summarises. -/
theorem le_maxPairLen (l : List (Nat × Nat)) {p : Nat × Nat} (hp : p ∈ l) :
    p.1 ≤ maxPairLen l ∧ p.2 ≤ maxPairLen l := by
  induction l with
  | nil => cases hp
  | cons q rest ih =>
      rcases List.mem_cons.mp hp with rfl | hrest
      · unfold maxPairLen
        simp only [List.map_cons, List.foldr_cons]
        exact ⟨le_trans (le_max_left _ _) (le_max_left _ _),
               le_trans (le_max_right _ _) (le_max_left _ _)⟩
      · have := ih hrest
        unfold maxPairLen at this ⊢
        simp only [List.map_cons, List.foldr_cons]
        exact ⟨le_trans this.1 (le_max_right _ _), le_trans this.2 (le_max_right _ _)⟩

/-- ⚑ **`maxPairLen_le_one_iff_nonChunking`** — the wire summary decides EXACTLY what the list
predicate decides. Without this the gate would be checking a number that merely travels with the
object it is supposed to be about. -/
theorem maxPairLen_le_one_iff_nonChunking (l : List (Nat × Nat)) :
    maxPairLen l ≤ 1 ↔ nonChunking l = true := by
  rw [nonChunking_iff]
  constructor
  · intro h p hp
    exact ⟨le_trans (le_maxPairLen l hp).1 h, le_trans (le_maxPairLen l hp).2 h⟩
  · intro h
    induction l with
    | nil => simp [maxPairLen]
    | cons q rest ih =>
        have hq := h q (by simp)
        have hrest : ∀ p ∈ rest, p.1 ≤ 1 ∧ p.2 ≤ 1 := fun p hp => h p (by simp [hp])
        have := ih hrest
        unfold maxPairLen at this ⊢
        simp only [List.map_cons, List.foldr_cons, max_le_iff]
        exact ⟨⟨hq.1, hq.2⟩, this⟩

/-! ## §2 — B2: `validate_feature_flags` (`verification.rs:631-642`; body `:74-142`).

The body pairs each OPTIONAL evaluation with the flag that must govern it, through

```rust
fn enable_if<T>(x: &Option<T>, flag: bool) -> bool { x.is_some() == flag }
```

so it is an `iff`, not an implication: a present evaluation with its flag clear is refused, and so
is an absent one with its flag set.

⚠ The three derived flags at `:110-113` are

```rust
let range_check_lookup = f.range_check0 || f.range_check1 || f.rot;
let lookups_per_row_4  = f.xor || range_check_lookup || f.foreign_field_mul;
let lookups_per_row_3  = lookups_per_row_4 || f.lookup;
let lookups_per_row_2  = lookups_per_row_3;
```

`lookups_per_row_2` and `lookups_per_row_3` are the **same value** — `the_two_lookup_rows_coincide`
proves it rather than leaving it as a reading of the source. `foreign_field_add` governs only its
own selector and enters none of the derived flags. -/

/-- The eight `feature_flags` of `…DeferredValuesPlonkFeatureFlags`, in the order
`prepared_statement.rs:147-156` destructures them. -/
structure FeatureFlags where
  rangeCheck0 : Bool
  rangeCheck1 : Bool
  foreignFieldAdd : Bool
  foreignFieldMul : Bool
  xor : Bool
  rot : Bool
  lookup : Bool
  runtimeTables : Bool
deriving Repr, DecidableEq

/-- Which optional evaluations are PRESENT (`Option::is_some`) in
`prev_evals.evals.evals`. `lookupSorted` is upstream's `[Option<_>; 5]`; its length is part of the
data because `:120-127` `panic!()`s on any other index. -/
structure OptEvalPresence where
  rangeCheck0Sel : Bool
  rangeCheck1Sel : Bool
  foreignFieldAddSel : Bool
  foreignFieldMulSel : Bool
  xorSel : Bool
  rotSel : Bool
  lookupAggregation : Bool
  lookupTable : Bool
  lookupSorted : List Bool
  runtimeLookupTable : Bool
  runtimeLookupTableSel : Bool
  xorLookupSel : Bool
  lookupGateLookupSel : Bool
  rangeCheckLookupSel : Bool
  foreignFieldMulLookupSel : Bool
deriving Repr, DecidableEq

/-- `range_check_lookup` (`verification.rs:110`). -/
def rangeCheckLookup (f : FeatureFlags) : Bool := f.rangeCheck0 || f.rangeCheck1 || f.rot
/-- `lookups_per_row_4` (`verification.rs:111`). -/
def lookupsPerRow4 (f : FeatureFlags) : Bool := f.xor || rangeCheckLookup f || f.foreignFieldMul
/-- `lookups_per_row_3` (`verification.rs:112`). -/
def lookupsPerRow3 (f : FeatureFlags) : Bool := lookupsPerRow4 f || f.lookup
/-- `lookups_per_row_2` (`verification.rs:113`). -/
def lookupsPerRow2 (f : FeatureFlags) : Bool := lookupsPerRow3 f

/-- ⚑ **`the_two_lookup_rows_coincide`** — `lookups_per_row_2` is *defined as*
`lookups_per_row_3` at `:113`, so slots 0..3 of `lookup_sorted` are all governed by the same
flag and only slot 4 differs. Asserted rather than left to the reader, because a transcription
that gave slot 3 its own flag would still look like the source. -/
theorem the_two_lookup_rows_coincide (f : FeatureFlags) : lookupsPerRow2 f = lookupsPerRow3 f :=
  rfl

/-- The per-slot flag of `lookup_sorted[i]` (`verification.rs:120-127`). Slot indices `≥ 5` do not
occur: upstream `panic!()`s, and `validateFeatureFlags` refuses any other length outright. -/
def lookupSortedFlag (f : FeatureFlags) (i : Nat) : Bool :=
  if i ≤ 2 then lookupsPerRow2 f
  else if i = 3 then lookupsPerRow3 f
  else lookupsPerRow4 f

/-- **`validateFeatureFlags`** — `verification.rs:74-142`, the BODY. Every `enable_if` is an
equality between a presence bit and its governing flag.

⚠ **FAIL-CLOSED ON THE ARRAY LENGTH.** Upstream's fold `panic!()`s when `lookup_sorted` has an
index outside `0..=4`; a panic is not a verdict this decision can return, so a length other than
five is a REFUSAL here. That is strictly safer than upstream and it is stated, not silent. -/
def validateFeatureFlags (f : FeatureFlags) (e : OptEvalPresence) : Bool :=
  decide (e.lookupSorted.length = 5)
  && (e.rangeCheck0Sel == f.rangeCheck0)
  && (e.rangeCheck1Sel == f.rangeCheck1)
  && (e.foreignFieldAddSel == f.foreignFieldAdd)
  && (e.foreignFieldMulSel == f.foreignFieldMul)
  && (e.xorSel == f.xor)
  && (e.rotSel == f.rot)
  && (e.lookupAggregation == lookupsPerRow2 f)
  && (e.lookupTable == lookupsPerRow2 f)
  && ((List.range 5).all (fun i => e.lookupSorted.getD i false == lookupSortedFlag f i))
  && (e.runtimeLookupTable == f.runtimeTables)
  && (e.runtimeLookupTableSel == f.runtimeTables)
  && (e.xorLookupSel == f.xor)
  && (e.lookupGateLookupSel == f.lookup)
  && (e.rangeCheckLookupSel == rangeCheckLookup f)
  && (e.foreignFieldMulLookupSel == f.foreignFieldMul)

/-- All eight flags clear — the devnet blockchain Wrap index
(`mina_pickles::decode_proof_at` REFUSES any proof with a flag set, `mina_pickles.rs:619-627`). -/
def NO_FEATURES : FeatureFlags :=
  ⟨false, false, false, false, false, false, false, false⟩

/-- Every optional evaluation absent. -/
def NO_OPT_EVALS : OptEvalPresence :=
  ⟨false, false, false, false, false, false, false, false,
   [false, false, false, false, false], false, false, false, false, false, false⟩

/-- **`allOptEvalsAbsent`** — the CONTRACT the extractor at
`metatheory/fixtures/pickles-extractors/src/gates.rs:175-176` states as prose: "with every flag
`false`, every optional evaluation must be absent" (plus the five-slot array length). Written
independently of `validateFeatureFlags` so the equation below has content. -/
def allOptEvalsAbsent (e : OptEvalPresence) : Bool :=
  decide (e.lookupSorted.length = 5)
  && (e.rangeCheck0Sel == false)
  && (e.rangeCheck1Sel == false)
  && (e.foreignFieldAddSel == false)
  && (e.foreignFieldMulSel == false)
  && (e.xorSel == false)
  && (e.rotSel == false)
  && (e.lookupAggregation == false)
  && (e.lookupTable == false)
  && ((List.range 5).all (fun i => e.lookupSorted.getD i false == false))
  && (e.runtimeLookupTable == false)
  && (e.runtimeLookupTableSel == false)
  && (e.xorLookupSel == false)
  && (e.lookupGateLookupSel == false)
  && (e.rangeCheckLookupSel == false)
  && (e.foreignFieldMulLookupSel == false)

/-- ⚑⚑ **`the_flagless_contract_is_a_theorem`** — the extractor states that contract as PROSE
and reproduces it *instead of* the body. Here it is DERIVED **from** the body: with every flag
clear, `validate_feature_flags` reduces DEFINITIONALLY to "every optional evaluation absent".
`rfl`, over a universally quantified `e` — so it is a fact about the function, not about a case. -/
theorem the_flagless_contract_is_a_theorem (e : OptEvalPresence) :
    validateFeatureFlags NO_FEATURES e = allOptEvalsAbsent e := rfl

/-- **`the_flagless_contract_is_not_vacuous`** — the contract ACCEPTS the all-absent record and
REFUSES each single presence bit, including one from each of the three derived-flag groups. A
predicate that accepted everything would satisfy the `rfl` above just as well. -/
theorem the_flagless_contract_is_not_vacuous :
    allOptEvalsAbsent NO_OPT_EVALS = true
    ∧ allOptEvalsAbsent { NO_OPT_EVALS with xorSel := true } = false
    ∧ allOptEvalsAbsent { NO_OPT_EVALS with lookupAggregation := true } = false
    ∧ allOptEvalsAbsent { NO_OPT_EVALS with rangeCheckLookupSel := true } = false
    ∧ allOptEvalsAbsent
        { NO_OPT_EVALS with lookupSorted := [false, false, false, false, true] } = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`validateFeatureFlags_is_an_iff_not_an_implication`** — `enable_if` refuses BOTH
directions. A transcription using `flag → present` would pass the first line and fail the
second. -/
theorem validateFeatureFlags_is_an_iff_not_an_implication :
    -- flag set, evaluation absent → REFUSED
    validateFeatureFlags { NO_FEATURES with xor := true } NO_OPT_EVALS = false
    -- flag clear, evaluation present → REFUSED
    ∧ validateFeatureFlags NO_FEATURES { NO_OPT_EVALS with xorSel := true } = false
    -- and the honest all-clear pair is ACCEPTED
    ∧ validateFeatureFlags NO_FEATURES NO_OPT_EVALS = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`the_lookup_sorted_array_length_is_load_bearing`** — a four- or six-slot `lookup_sorted`
is REFUSED rather than folded over, which is where upstream `panic!()`s. -/
theorem the_lookup_sorted_array_length_is_load_bearing :
    validateFeatureFlags NO_FEATURES { NO_OPT_EVALS with lookupSorted := List.replicate 4 false }
      = false
    ∧ validateFeatureFlags NO_FEATURES
        { NO_OPT_EVALS with lookupSorted := List.replicate 6 false } = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`foreign_field_add` governs its OWN selector and nothing else** — it is absent from all
three derived flags (`:110-112`), so setting it moves exactly one presence bit. Pins the one
asymmetry in the table that a careless transcription would smooth over. -/
theorem foreign_field_add_governs_only_its_own_selector :
    validateFeatureFlags { NO_FEATURES with foreignFieldAdd := true }
        { NO_OPT_EVALS with foreignFieldAddSel := true } = true
    ∧ rangeCheckLookup { NO_FEATURES with foreignFieldAdd := true } = false
    ∧ lookupsPerRow4 { NO_FEATURES with foreignFieldAdd := true } = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §3 — B3: the step domain bound (`verification.rs:644-651`).

```rust
let step_domain: u8 = branch_data.domain_log2.as_u8();
let step_domain = Domain::Pow2RootsOfUnity(step_domain as u64);
checks(step_domain.log2_size() as usize <= BACKEND_TICK_ROUNDS_N, "domain size is small enough");
```

`Domain::log2_size` on `Pow2RootsOfUnity(k)` is `k` (`wrap.rs:1084-1087`), so the whole leg is
`branch_data.domain_log2 ≤ 16` — `BACKEND_TICK_ROUNDS_N = 16` (`proofs/mod.rs:33`).

⚠ The number is the **STEP** side's. The real devnet block carries `domain_log2 = 16` while the
Wrap VK's own domain is `2^14`; conflating them is the error `docs/MINA-REAL-BLOCK-GATE.md` §4.2
records, and it is why this bound is `16` and not `14`. -/

/-- `BACKEND_TICK_ROUNDS_N` (`mina-rust/crates/ledger/src/proofs/mod.rs:33`). -/
def BACKEND_TICK_ROUNDS_N : Nat := 16
/-- `BACKEND_TOCK_ROUNDS_N` (`mod.rs:34`) — the Wrap side, carried so the two are never confused. -/
def BACKEND_TOCK_ROUNDS_N : Nat := 15

/-- **`stepDomainOk`** — `verification.rs:648-651`. -/
def stepDomainOk (branchDomainLog2 : Nat) : Bool := decide (branchDomainLog2 ≤ BACKEND_TICK_ROUNDS_N)

/-- **`stepDomainOk_at_the_real_block`** — the real devnet block 539508 carries `domain_log2 = 16`
and is ACCEPTED **at the boundary**; `17` is REFUSED. A bound transcribed as `< 16` rather than
`≤ 16` would reject every real Mina block, so the boundary case is the whole test. -/
theorem stepDomainOk_at_the_real_block :
    stepDomainOk 16 = true ∧ stepDomainOk 17 = false ∧ stepDomainOk 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`the_step_bound_is_not_the_wrap_bound`** — `16 ≠ 15`, and the real block's `16` would be
REFUSED by the Tock number. Stated because both constants are in scope one line apart. -/
theorem the_step_bound_is_not_the_wrap_bound :
    BACKEND_TICK_ROUNDS_N ≠ BACKEND_TOCK_ROUNDS_N
    ∧ decide (16 ≤ BACKEND_TOCK_ROUNDS_N) = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### B3's neighbours — the wrap-domain bracket (`verification.rs:653-667`).

The same block checks the VERIFIER INDEX's own domain against a hardcoded triple. It reads

```rust
let all_possible_domains = [13, 14, 15];
let [greatest_wrap_domain, _, least_wrap_domain] = all_possible_domains;
checks(actual_wrap_domain <= least_wrap_domain,    "…(least_wrap_domain)");
checks(actual_wrap_domain >= greatest_wrap_domain, "…(greatest_wrap_domain)");
```

⚠ **The two names are the wrong way round in upstream** — `greatest_wrap_domain` is bound to
`13` and `least_wrap_domain` to `15`. The predicate is therefore the bracket `13 ≤ d ≤ 15`, and
reading the identifiers instead of the destructuring gives the empty interval `15 ≤ d ≤ 13`. -/

/-- **`wrapDomainOk`** — `verification.rs:653-667`, read off the destructuring rather than the
identifier names. -/
def wrapDomainOk (actualWrapDomainLog2 : Nat) : Bool :=
  decide (13 ≤ actualWrapDomainLog2) && decide (actualWrapDomainLog2 ≤ 15)

/-- **`wrapDomainOk_brackets_the_real_index`** — the devnet blockchain Wrap VK's domain is `2^14`
and is accepted; both ends of the bracket refuse. -/
theorem wrapDomainOk_brackets_the_real_index :
    wrapDomainOk 14 = true ∧ wrapDomainOk 13 = true ∧ wrapDomainOk 15 = true
    ∧ wrapDomainOk 12 = false ∧ wrapDomainOk 16 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`the_swapped_names_give_the_empty_interval`** — if the identifiers were believed over
the destructuring, the conjunction would be `15 ≤ d ∧ d ≤ 13`, which NOTHING satisfies. Proven
rather than remarked, because a verifier leg that accepts nothing refuses every real block and
would look like a working check right up until it ran. -/
theorem the_swapped_names_give_the_empty_interval :
    ∀ d : Nat, ¬ (15 ≤ d ∧ d ≤ 13) := by
  intro d h; omega

/-! ## §4 — B1+B2+B3 composed: `run_checks` (`verification.rs:557-674`).

`run_checks` pushes a string per failed condition and returns `errors.is_empty()` (`:673`), so
the verdict is the CONJUNCTION of its five conditions — B1, B2, B3 and the two wrap-domain
bounds. `verify_impl` conjoins it at `:893` (`Ok(result.is_ok() && checks)`). -/

/-- **`runChecks`** — `verification.rs:673`, the conjunction the string-collecting shape computes. -/
def runChecks (evalLens : List (Nat × Nat)) (f : FeatureFlags) (e : OptEvalPresence)
    (branchDomainLog2 actualWrapDomainLog2 : Nat) : Bool :=
  nonChunking evalLens
  && validateFeatureFlags f e
  && stepDomainOk branchDomainLog2
  && wrapDomainOk actualWrapDomainLog2

/-- **`runChecks_discriminates`** — the flagless devnet shape is ACCEPTED and each of the four
conjuncts is INDEPENDENTLY load-bearing: moving exactly one input refuses. Without this the
accept would be compatible with a decision that accepts everything. -/
theorem runChecks_discriminates :
    runChecks [(1, 1), (1, 1)] NO_FEATURES NO_OPT_EVALS 16 14 = true
    -- B1: a chunked evaluation
    ∧ runChecks [(1, 1), (2, 1)] NO_FEATURES NO_OPT_EVALS 16 14 = false
    -- B2: an evaluation present with no flag to govern it
    ∧ runChecks [(1, 1), (1, 1)] NO_FEATURES { NO_OPT_EVALS with rotSel := true } 16 14 = false
    -- B3: a step domain above the tick rounds
    ∧ runChecks [(1, 1), (1, 1)] NO_FEATURES NO_OPT_EVALS 17 14 = false
    -- the wrap-domain bracket, both ends
    ∧ runChecks [(1, 1), (1, 1)] NO_FEATURES NO_OPT_EVALS 16 12 = false
    ∧ runChecks [(1, 1), (1, 1)] NO_FEATURES NO_OPT_EVALS 16 16 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §5 — C3 and D1: the field packing and the length it must equal.

`to_public_input` (`prepared_statement.rs:53-181`) appends, in this order:

| block | count | line |
|---|---|---|
| `Fp` shifted: `combined_inner_product`, `b`, `zeta_to_srs_length`, `zeta_to_domain_size`, `perm` | 5 | `:100-104` |
| Challenge: `beta`, `gamma` | 2 | `:108-109` |
| Scalar challenge: `alpha`, `zeta`, `xi` | 3 | `:113-115` |
| Digest: `sponge_digest_before_evaluations`, `messages_for_next_wrap_proof`, `messages_for_next_step_proof` | 3 | `:119-121` |
| `bulletproof_challenges` | `n` | `:124` |
| `branch_data` = `(domain_log2 << 2) \| proofs_verified` | 1 | `:140` |
| `feature_flags.to_field_elements` | 8 | `:145` |
| `uses_lookup` | 1 | `:170` |
| the joint combiner, or zero | 1 | `:172-176` |

and closes with `assert_eq!(fields.len(), npublic_input)` at `:179`. So the packing produces
`24 + n` field elements and **asserts** that equals the index's `public`.

⚑ The same equality is then checked AGAIN, as a returned error rather than a panic, at
`verifier.rs:816-820` (`VerifyError::IncorrectPubicInputLength`) and once more at `:834-839`.
D1's public half and C3's terminal assert are **the same equation**, reached twice. -/

/-- The fixed part of `to_public_input`'s schedule: everything except `bulletproof_challenges`. -/
def PUBLIC_INPUT_FIXED_WORDS : Nat := 5 + 2 + 3 + 3 + 1 + 8 + 1 + 1

/-- **`toPublicInputLen`** — `prepared_statement.rs:100-176`, as a function of
`bulletproof_challenges.len()`. -/
def toPublicInputLen (nBulletproofChallenges : Nat) : Nat :=
  PUBLIC_INPUT_FIXED_WORDS + nBulletproofChallenges

/-- ⚑ **`the_packing_produces_forty_words_at_the_tick_rounds`** — the Wrap public input is
`24 + 16 = 40`, which is the devnet blockchain Wrap index's declared `public`, and the `16` is
`BACKEND_TICK_ROUNDS_N` rather than a coincidence. Ties C3's schedule to B3's constant. -/
theorem the_packing_produces_forty_words_at_the_tick_rounds :
    PUBLIC_INPUT_FIXED_WORDS = 24
    ∧ toPublicInputLen BACKEND_TICK_ROUNDS_N = 40 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`the_packing_length_moves_with_the_challenge_count`** — one challenge short is 39 words, and
the whole point of D1 is that 39 ≠ 40. A schedule that ignored `n` would pass the line above. -/
theorem the_packing_length_moves_with_the_challenge_count :
    toPublicInputLen 15 = 39 ∧ toPublicInputLen 17 = 41
    ∧ ∀ m n : Nat, toPublicInputLen m = toPublicInputLen n → m = n := by
  refine ⟨by decide, by decide, ?_⟩
  intro m n h; unfold toPublicInputLen at h; omega

/-- **`prevChallengesLenOk`** — `verifier.rs:810-815`,
`VerifyError::IncorrectPrevChallengesLength`. This half is already in
`KimchiVerify.shapeOkRec`'s first conjunct; it is restated here so D1 is one object. -/
def prevChallengesLenOk (proofPrevLen idxPrevLen : Nat) : Bool := decide (proofPrevLen = idxPrevLen)

/-- **`publicInputLenOk`** — `verifier.rs:816-820`, `VerifyError::IncorrectPubicInputLength`
(upstream's spelling). ⚑ An EQUALITY between the length `to_public_input` PRODUCED and the
length the index DECLARES — the leg `shapeOkRec` does not have. -/
def publicInputLenOk (producedLen idxPublic : Nat) : Bool := decide (producedLen = idxPublic)

/-- **`d1Ok`** — `verifier.rs:810-820`, both legs, with the produced length DERIVED from the
challenge count rather than accepted as a second opinion. Handing this an independently supplied
`producedLen` would be the "absorb a value as a chip input to quiet a census" move; it is
computed. -/
def d1Ok (proofPrevLen idxPrevLen nBulletproofChallenges idxPublic : Nat) : Bool :=
  prevChallengesLenOk proofPrevLen idxPrevLen
  && publicInputLenOk (toPublicInputLen nBulletproofChallenges) idxPublic

/-- **`d1Ok_at_the_real_block`** — the devnet blockchain index (`prev_challenges = 2`,
`public = 40`) against block 539508's proof (`prev_challenges = 2`, 16 IPA challenges) ACCEPTS,
and every single-count tamper REFUSES. -/
theorem d1Ok_at_the_real_block :
    d1Ok 2 2 16 40 = true
    -- the proof carries a different recursion count than the index declares
    ∧ d1Ok 1 2 16 40 = false
    ∧ d1Ok 2 1 16 40 = false
    -- one challenge short: the packing produces 39 words against a `public = 40` index
    ∧ d1Ok 2 2 15 40 = false
    -- ⚑ and the 41-word index, which is the pair `the_index_digest_cannot_see_the_circuit_shape`
    -- exhibits: same VK digest, different public count. D1 is what separates them.
    ∧ d1Ok 2 2 16 41 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6 — D2: `check_proof_evals_len` (`verifier.rs:822-831`; body `:640-779`).

`to_batch` computes

```rust
let chunk_size = { let d1_size = verifier_index.domain.size();
                   if d1_size < verifier_index.max_poly_size { 1 }
                   else { d1_size / verifier_index.max_poly_size } };
check_proof_evals_len(proof, chunk_size)?;
```

and the body compares, for EVERY `PointEvaluations` in `proof.evals`,

```rust
if eval.zeta.len() != expected_size { Err(IncorrectEvaluationsLength(..)) }
else if eval.zeta_omega.len() != expected_size { Err(..) } else { Ok(()) }
```

⚠ **`=`, not `≤`.** This is the leg B1 is NOT: B1 bounds `prev_evals` at `≤ 1`, D2 pins THIS
proof's `evals` at exactly `chunk_size`. `chunkSizeOf` is transcribed with upstream's integer
division and its `<` guard, so the `d1_size = max_poly_size` boundary lands where upstream puts
it. -/

/-- **`chunkSizeOf`** — `verifier.rs:823-830`, including the `<` guard and the truncating
division. -/
def chunkSizeOf (domainSize maxPolySize : Nat) : Nat :=
  if domainSize < maxPolySize then 1 else domainSize / maxPolySize

/-- **`checkProofEvalsLen`** — `verifier.rs:678-693`, applied to every entry. -/
def checkProofEvalsLen (evalLens : List (Nat × Nat)) (expectedSize : Nat) : Bool :=
  evalLens.all (fun p => decide (p.1 = expectedSize) && decide (p.2 = expectedSize))

/-- **`chunkSizeOf_at_the_devnet_wrap_index`** — domain `2^14`, `max_poly_size = 2^15`, so the
guard fires and `chunk_size = 1`. ⚑ The boundary matters: at `d1_size = max_poly_size` upstream
takes the ELSE branch and the quotient is also `1`, so the two branches agree there — but one
step above, `2^16 / 2^15 = 2`, and the index is chunked. -/
theorem chunkSizeOf_at_the_devnet_wrap_index :
    chunkSizeOf (2 ^ 14) (2 ^ 15) = 1
    ∧ chunkSizeOf (2 ^ 15) (2 ^ 15) = 1
    ∧ chunkSizeOf (2 ^ 16) (2 ^ 15) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`d2_is_an_equality_and_b1_is_a_bound`** — the distinction that makes D2 a separate leg.
An ABSENT evaluation (length 0) satisfies B1 and is REFUSED by D2 at `chunk_size = 1`. A tree
that had B1 and called D2 covered would accept a proof missing its evaluations entirely. -/
theorem d2_is_an_equality_and_b1_is_a_bound :
    nonChunking [(0, 0)] = true
    ∧ checkProofEvalsLen [(0, 0)] 1 = false
    ∧ checkProofEvalsLen [(1, 1)] 1 = true
    -- and at a chunked index D2 demands the chunks, where B1 would refuse them
    ∧ checkProofEvalsLen [(2, 2)] 2 = true
    ∧ nonChunking [(2, 2)] = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`checkProofEvalsLen_refuses_a_one_sided_chunk`** — `zeta` and `zeta_omega` are checked
separately (`:679`, `:685`), so a proof correct at `zeta` alone is refused. -/
theorem checkProofEvalsLen_refuses_a_one_sided_chunk :
    checkProofEvalsLen [(1, 1), (1, 0)] 1 = false
    ∧ checkProofEvalsLen [(1, 1), (0, 1)] 1 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §7 — C2: `messages_for_next_wrap_proof.hash()` (`verification.rs:875-876`).

`get_message_for_next_wrap_proof` (`:457-475`) builds the record and
`get_prepared_statement` (`:493`) takes its `.hash()`, whose result becomes public-input word 11
(`prepared_statement.rs:120`, the second Digest).

`MessagesForNextWrapProof::to_fields` (`messages.rs:84-107`) is:

```rust
const NFIELDS: usize = 32;
let padding = 2usize.checked_sub(self.old_bulletproof_challenges.len())
                    .expect("old_bulletproof_challenges must be of length <= 2");
for _ in 0..padding { fields.extend_from_slice(&Self::dummy_padding()); }   // 15 each
for challenges in &self.old_bulletproof_challenges { fields.extend_from_slice(challenges); }
let Affine { x, y, .. } = self.challenge_polynomial_commitment.to_affine();
fields.extend([x, y]);
assert_eq!(fields.len(), NFIELDS);
```

⚑ Three facts a paraphrase loses, and each is a theorem below: the padding goes **FIRST**, the
slots are **Tock**-sized (15 = `BACKEND_TOCK_ROUNDS_N`, not the step side's 16), and
`checked_sub(…).expect(…)` makes **more than two slots a REFUSAL** rather than a truncation.

**SCOPE — what is and is not built here.** The PREIMAGE SCHEDULE is built and proven. The
DIGEST is `hash_fields` = Mina Poseidon over **Fq**, and it is not in this file. That is not a
statement that the machinery is missing: `MinaPhase2Chain` is the Fq-side absorb chain and
`MinaWrapVkDigestChain` shows the pattern (28 links riding `dregg-pasta-fp-chainlink::v1`, no
new AIR). C2's digest is 32 elements — 16 links — on the Fq side, and it is UNDONE WORK, not a
theorem of the model. §8 records it as such. -/

/-- `NFIELDS` (`messages.rs:85`). -/
def WRAP_MSG_NFIELDS : Nat := 32
/-- Slots the record is padded to (`messages.rs:89`). -/
def WRAP_MSG_SLOTS : Nat := 2

/-- **`wrapMessagesPreimageLen`** — `messages.rs:88-105`. `none` is upstream's `expect` on
`checked_sub` underflow: more than two slots does not hash, it aborts. -/
def wrapMessagesPreimageLen (nSlots : Nat) : Option Nat :=
  if nSlots ≤ WRAP_MSG_SLOTS then
    some (WRAP_MSG_SLOTS * BACKEND_TOCK_ROUNDS_N + 2)
  else none

/-- **`wrapMessagesPreimage`** — the schedule itself, padding FIRST. `pad` is
`dummy_padding()`'s 15 constants (`messages.rs:112-133`) and each slot is a 15-vector; the two
trailing entries are the commitment's affine `x, y`. -/
def wrapMessagesPreimage (pad : List Nat) (slots : List (List Nat)) (x y : Nat) :
    Option (List Nat) :=
  if slots.length ≤ WRAP_MSG_SLOTS then
    some ((List.replicate (WRAP_MSG_SLOTS - slots.length) pad).flatten ++ slots.flatten ++ [x, y])
  else none

/-- **`the_wrap_preimage_is_thirty_two_fields`** — at every admissible slot count, and only at
those. The `expect` at `messages.rs:90` is a refusal here. -/
theorem the_wrap_preimage_is_thirty_two_fields :
    wrapMessagesPreimageLen 0 = some 32
    ∧ wrapMessagesPreimageLen 1 = some 32
    ∧ wrapMessagesPreimageLen 2 = some 32
    ∧ wrapMessagesPreimageLen 3 = none
    ∧ WRAP_MSG_NFIELDS = 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`the_wrap_slots_are_tock_sized`** — 15, the WRAP round count, against the step side's 16.
`2 * 16 + 2 = 34 ≠ 32`, so a preimage built with the step number is the wrong length and would
be caught; this pins which of the two constants the schedule uses. -/
theorem the_wrap_slots_are_tock_sized :
    WRAP_MSG_SLOTS * BACKEND_TOCK_ROUNDS_N + 2 = WRAP_MSG_NFIELDS
    ∧ WRAP_MSG_SLOTS * BACKEND_TICK_ROUNDS_N + 2 ≠ WRAP_MSG_NFIELDS := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`the_wrap_preimage_schedule_is_padding_first`** — the emitted order is
`[padding…] ++ [real slots…] ++ [x, y]`, exhibited on a one-slot record so the padding is
visible. A schedule that appended the padding would produce the same LENGTH and a different
digest, which is exactly the kind of error a length check cannot see. -/
theorem the_wrap_preimage_schedule_is_padding_first :
    wrapMessagesPreimage [7, 8] [[1, 2]] 9 10 = some [7, 8, 1, 2, 9, 10]
    ∧ wrapMessagesPreimage [7, 8] [[1, 2], [3, 4]] 9 10 = some [1, 2, 3, 4, 9, 10]
    ∧ wrapMessagesPreimage [7, 8] [[1, 2], [3, 4], [5, 6]] 9 10 = none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`the_wrap_preimage_length_is_the_schedule_length`** — the two §7 objects agree, so the
count theorem is about the list the digest would actually absorb rather than about a number
carried beside it. -/
theorem the_wrap_preimage_length_is_the_schedule_length
    (pad : List Nat) (slots : List (List Nat)) (x y : Nat) (out : List Nat)
    (hpad : pad.length = BACKEND_TOCK_ROUNDS_N)
    (hslot : ∀ s ∈ slots, s.length = BACKEND_TOCK_ROUNDS_N)
    (h : wrapMessagesPreimage pad slots x y = some out) :
    out.length = WRAP_MSG_NFIELDS := by
  unfold wrapMessagesPreimage WRAP_MSG_SLOTS at h
  match slots with
  | [] =>
      split at h
      · injection h with h'; subst h'
        simp [hpad, WRAP_MSG_NFIELDS, BACKEND_TOCK_ROUNDS_N]
      · simp at h
  | [s] =>
      have hs : s.length = BACKEND_TOCK_ROUNDS_N := hslot s (by simp)
      split at h
      · injection h with h'; subst h'
        simp [hpad, hs, WRAP_MSG_NFIELDS, BACKEND_TOCK_ROUNDS_N]
      · simp at h
  | [s, t] =>
      have hs : s.length = BACKEND_TOCK_ROUNDS_N := hslot s (by simp)
      have ht : t.length = BACKEND_TOCK_ROUNDS_N := hslot t (by simp)
      split at h
      · injection h with h'; subst h'
        simp [hs, ht, WRAP_MSG_NFIELDS, BACKEND_TOCK_ROUNDS_N]
      · simp at h
  | _ :: _ :: _ :: _ =>
      split at h
      · next hc => simp only [List.length_cons] at hc; omega
      · simp at h

/-! ## §8 — WHERE EACH FORCING LIVES, and what is still undone.

**Closure kind, per leg.** None of the seven is closed BY CONSTRAINT: no AIR row in this tree
forces any of them, and this file emits no descriptor.

| leg | closure | where the forcing lives |
|---|---|---|
| B1 `nonChunking` | **consumer refusal** | `PicklesWrapShapeGate.picklesWrapShapeOk` → `@[export] dregg_mina_wrap_shape_ok` → `bridge/src/mina_observer.rs::check_block_proofs` |
| B2 `validateFeatureFlags` | **consumer refusal, in two places** | the enclosing class is refused in the CODEC (`mina_pickles.rs:619-627` refuses any set flag, `:616` refuses a `Some` joint combiner); the remaining flagless obligation — every optional evaluation ABSENT — is `the_flagless_contract_is_a_theorem` conjoined into the gate |
| B3 `stepDomainOk` | **consumer refusal** | the same gate; `branch_domain_log2` was already decoded (`mina_pickles.rs:640`) and previously fed nothing |
| C2 wrap-message hash | **VALUE LAYER only** | preimage schedule proven here; the digest is `gates::gate_c` in the offline extractor (`pickles_kimchi_marshal.rs:1337`), which the node does not run. **UNDONE WORK**, not a theorem of the model — see below |
| C3 `to_public_input` | **consumer refusal** (length); **value layer** (the words) | the length is `toPublicInputLen`, conjoined into the gate via D1; the 40 WORDS are `gates::wrap_public_input` in the same extractor |
| D1 prev-challenges | **consumer refusal** | already closed before this file — `KimchiVerify.shapeOkRec`'s first conjunct, same gate |
| D1 public-input length | **consumer refusal (NEW)** | was `decide (0 < publicLen)` against trusted config; now `publicInputLenOk (toPublicInputLen n) idxPublic` |
| D2 `checkProofEvalsLen` | **consumer refusal** | the same gate |

**C2's digest, priced rather than labelled.** It is 32 Fq elements = 16 absorb links of the same
shape `MinaWrapVkDigestChain` runs at 28 links, and that file's own theorem
`the_descriptor_is_the_deployed_phase1_link` shows such a chain needs NO NEW AIR. What is
genuinely absent is the Fq-side instantiation and its fixture, not a mechanism. It is the next
item, not a boundary.

**What this file does NOT claim.** It does not verify a Mina block. It composes the preamble and
the packing SHAPE; the arithmetic (C3's word VALUES, C2's digest, the transcript, the group
assembly, the IPA opening) is `MinaRealBlockGate` / `MinaWrap*` and is fixture-bound, as
`bridge/src/mina_observer.rs`'s table states. An accept here means the proof has the shape the
pinned index demands and the packing that index's `public` count describes. -/

/-! ## §9 — axiom hygiene. -/

#assert_axioms nonChunking_iff
#assert_axioms le_maxPairLen
#assert_axioms maxPairLen_le_one_iff_nonChunking
#assert_axioms nonChunking_refuses_a_chunked_column
#assert_axioms the_two_lookup_rows_coincide
#assert_axioms the_flagless_contract_is_a_theorem
#assert_axioms the_flagless_contract_is_not_vacuous
#assert_axioms validateFeatureFlags_is_an_iff_not_an_implication
#assert_axioms the_lookup_sorted_array_length_is_load_bearing
#assert_axioms foreign_field_add_governs_only_its_own_selector
#assert_axioms stepDomainOk_at_the_real_block
#assert_axioms the_step_bound_is_not_the_wrap_bound
#assert_axioms wrapDomainOk_brackets_the_real_index
#assert_axioms the_swapped_names_give_the_empty_interval
#assert_axioms runChecks_discriminates
#assert_axioms the_packing_produces_forty_words_at_the_tick_rounds
#assert_axioms the_packing_length_moves_with_the_challenge_count
#assert_axioms d1Ok_at_the_real_block
#assert_axioms chunkSizeOf_at_the_devnet_wrap_index
#assert_axioms d2_is_an_equality_and_b1_is_a_bound
#assert_axioms checkProofEvalsLen_refuses_a_one_sided_chunk
#assert_axioms the_wrap_preimage_is_thirty_two_fields
#assert_axioms the_wrap_slots_are_tock_sized
#assert_axioms the_wrap_preimage_schedule_is_padding_first
#assert_axioms the_wrap_preimage_length_is_the_schedule_length

#print axioms the_flagless_contract_is_a_theorem
#print axioms d1Ok_at_the_real_block
#print axioms the_wrap_preimage_length_is_the_schedule_length

end Dregg2.Circuit.Emit.PicklesVerifyPreamble
