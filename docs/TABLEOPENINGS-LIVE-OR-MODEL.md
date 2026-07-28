# `tableOpenings = []` — live verifier defect, or modelling gap?

**2026-07-27. Read-only investigation. VERDICT: MODEL GAP ONLY.**

This settles the ⚑ REQUIRED CHECK of `docs/PLAN-fri-proximity-apex-connection.md` §4 (Slice A), which
said: *"Do not state which it is until that file is read."* The file has now been read. Every claim
below cites the declaration, not a grep hit.

---

## VERDICT

> **MODEL GAP ONLY.** A proof with an empty or absent table-openings list is **structurally
> impossible to construct** for the deployed Rust verifier. The openings list is not walked from a
> prover-supplied collection at all — it is **zipped against a verifier-constructed AIR list whose
> length is at least 3 unconditionally**, and a length disagreement is a hard `InstanceCountMismatch`
> reject *before any cryptography runs*. The Lean `batchTablesCheck` is **weaker than the shipped
> Rust**, not a mirror of a shipped hole.
>
> **Slice A is a model fix. Nothing re-emits. No descriptor, VK, schema, or wire format changes. No
> flag day.**

---

## 1. Where the real verifier lives (so the next reader does not re-hunt it)

It is **not** vendored in this repo and **not** on crates.io — it is a git-pinned dependency, in two
crates from two different pins:

| piece | pin | on-disk path |
|---|---|---|
| `verify_all_tables`, AIR reconstruction | `emberian/plonky3-recursion` rev `0a4a554` (`Cargo.toml:284-287`) | `~/.cargo/git/checkouts/plonky3-recursion-2254dc838bc79d6b/0a4a554/circuit-prover/src/batch_stark_prover.rs` |
| `verify_batch`, the shape gate | `Plonky3/Plonky3` rev `82cfad73` (`Cargo.toml:263,277`) | `~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/batch-stark/src/verifier/mod.rs` |
| LogUp global-sum check | same `82cfad73` | `.../82cfad7/lookup/src/logup.rs` |
| shape-error enum | same `82cfad73` | `.../82cfad7/uni-stark/src/error.rs` |

The dregg-side callers are `circuit-prove/src/plonky3_recursion_impl.rs:815`,
`circuit-prove/src/apex_shrink.rs:313`, `circuit-prove/src/gpu_backend.rs:4650,5261`.

---

## 2. The two predicates, side by side

### The Lean predicate (the one the plan flagged)

`metatheory/Dregg2/Circuit/FriVerifier.lean:803-808`:

```lean
def batchTablesCheck {F : Type} [DecidableEq F]
    (A : FieldArith F) (proof : BatchProofData F) : Bool :=
  match proof.oodPoint with
  | ood :: _ => proof.tableOpenings.all (tableOk A ood)
      && decide (busSum A proof.tableOpenings = A.zero)
  | [] => false
```

`proof.tableOpenings` is a field of `BatchProofData` with **default `[]`**
(`FriVerifier.lean:450-452`). `List.all [] = true` and `busSum A [] = A.zero` by
`foldr … A.zero` (`FriVerifier.lean:789-790`), so an empty list passes both conjuncts. The finding as
reported is **correct about the Lean**: `deployed_accepting_pole_has_no_tableOpenings`
(`FriLdtExtractDeployed.lean:902`) walks straight through, and its `decide`-backed run `poleProof`
never sets the field.

The nonempty check that *does* exist is on the **other** list —
`batchTablesCheckExt`, `metatheory/Dregg2/Circuit/ExtFieldChallenge.lean:734-738`:

```lean
def batchTablesCheckExt … (os : List (ExtSingleAirOpening F)) : Bool :=
  decide (os ≠ [])
    && os.all (singleAirOkExt E W D alpha zeta)
    && decide (busSumExt E D os = extOfBase E.base D E.base.zero)
```

applied at `ExtFieldChallenge.lean:767` to `view.singleAirOpenings`. The plan's diagnosis of the seam
is exact: **two lists, nothing tying them together.**

### The Rust verifier

`verify_all_tables` (`batch_stark_prover.rs:978-993`) → `validate()` (`:490-501`) → `verify::<D>`
(`:1403-1413`) → `rebuild_airs_pvs_common` (`:1433-1522`) → `p3_batch_stark::verify_batch`
(`verifier/mod.rs:30`).

The decisive lines are these two, and they are what makes the answer *model gap*:

**(a) The AIR list is built by the verifier and is never empty** —
`batch_stark_prover.rs:1485`:

```rust
let mut airs = vec![const_air, public_air, alu_air];
```

Unconditional. Three primitive AIRs (`Const`, `Public`, `Alu`) exist on **every** proof regardless of
anything the prover supplies; only the *tail* of the list (`:1490-1503`) comes from
`proof.non_primitives`. There is no code path on which `airs.len() < 3`.

**(b) The openings list length is pinned to the AIR list, up front, before any crypto** —
`verifier/mod.rs:61-72`:

```rust
if airs.len() != opened_values.instances.len()
    || airs.len() != public_values.len()
    || airs.len() != degree_bits.len()
    || airs.len() != global_lookup_data.len()
    || airs.len() != all_lookups.len()
    || common.preprocessed.as_ref()
        .is_some_and(|global| global.instances.len() != airs.len())
{
    return Err(InvalidProofShapeError::InstanceCountMismatch.into());
}
```

`InstanceCountMismatch` is a hard error (`uni-stark/src/error.rs:13`). So
`opened_values.instances` — the real object the Lean `tableOpenings` models — **must have length
≥ 3**, and an empty one is rejected at line 71 before the transcript is even seeded (transcript
observation starts at `:144`).

---

## 3. The three real-verifier checks `batchTablesCheck` fails to model

These are the model fixes. Each is a check the shipped Rust performs and the Lean predicate does not.

1. **The openings list is verifier-driven, not prover-driven.**
   Every per-table loop in `verify_batch` iterates `airs` and *indexes into* the openings
   (`verifier/mod.rs:96-141` shape/degree, `:146-275` widths and lookup metadata, `:507-621` the
   quotient/constraint identity). The Lean does `proof.tableOpenings.all …` — it walks the prover's
   list. **That inversion is the entire defect.** A vacuous `List.all []` has no Rust counterpart
   because Rust never asks the prover how many tables to check.

2. **A minimum of three tables is structural.** `batch_stark_prover.rs:1485`. The Lean model has no
   notion of a mandatory table set; `BatchProofData.tableOpenings` defaults to `[]`
   (`FriVerifier.lean:452`).

3. **The two Lean lists are one real object.** `BatchProofData.tableOpenings`
   (`FriVerifier.lean:450-452`) and `BatchProofData.singleAirOpenings` (`:471-475`) are both mirrors
   of `BatchProof.opened_values.instances`. The Rust has exactly one openings list; the Lean split it
   into a legacy scalar mirror and an extension-faithful mirror, put the nonemptiness pin on one and
   the bus/quotient walk on the other, and left the seam unbound. **The unbound seam is an artifact of
   a duplication that reality does not have.**

### Consequence for Slice A

Per `CLAUDE.md` — *"prefer deleting the old thing to keeping both"* — the right model fix is
**not** merely bolting `decide (proof.tableOpenings ≠ [])` onto `batchTablesCheck`. Two shapes that
agree today are two shapes that will disagree later, and here they already disagree. The faithful
repair is to **collapse the duplication**: make the legacy scalar list either derived from
`singleAirOpenings` or deleted, so there is one modelled openings list matching the one real one, and
give it the length pin that the Rust actually enforces (`length = the AIR count`, minimum 3), not just
nonemptiness.

The plan's acceptance bar still holds unchanged and is still the right canary: the fix is only real if
`deployed_accepting_pole_has_no_tableOpenings` (`FriLdtExtractDeployed.lean:902`) goes **red**, and
`deployed_accepting_pole_nonempty` (`:854`) is re-established at a pole that actually opens tables.
Both are `decide` witnesses, so both flips are mechanical.

**Deployment consequence: none.** No AIR changes, no VK rotation, no descriptor re-emit, no schema
bump, no re-genesis. The Rust is already stricter than the model in exactly this respect.

---

## 4. Exploitability of the *modelled* hole: zero, and here is why at each layer

Even setting aside the up-front shape gate, a zero-table proof has nothing left to stand on. Recorded
so nobody re-opens this as "but could it slip past downstream?":

- **PCS/FRI.** `coms_to_verify` is assembled per-instance from `opened_values.instances`
  (`verifier/mod.rs:331-356` trace round, `:388-406` quotient round, `:474-499` permutation round) and
  handed to `pcs.verify` at `:502`. With no instances there is nothing to open and no commitment to
  test — but control never reaches here, because `:71` already returned.
- **Quotient identity.** `verify_constraints_with_lookups` (`:613-614`) runs once per `airs` entry.
  Skipping it requires shrinking `airs`, which the prover cannot do below 3.
- **LogUp bus.** `verify_global_sum` (`logup.rs:314-324`) sums the per-instance cumulative sums and
  requires zero. Empirically this is the check that has caught a genuinely-missing table in this repo
  before: a W24 permutation table absent from the aggregation layer produced
  `GlobalCumulativeMismatch` (`metatheory/docs/CODEX-BUS-BALANCE-FIX.md:3`). The Lean `busSum` conjunct
  models this one correctly — it is only the *empty* case that is vacuous, and the empty case is
  unreachable.
- **Which tables must be present.** Pinned outside `verify_batch`, by
  `recursion_vk_fingerprint` (`circuit-prove/src/plonky3_recursion_impl.rs:711-778`), which hashes
  `proof.non_primitives.len()` and every entry's `op_type`/`rows`/`lanes`/`air_variant` (`:741-747`)
  along with `rows`, `table_packing`, `degree_bits` and the preprocessed commitment (`:727-735,758`).
  A prover that drops a non-primitive table changes the fingerprint and fails the caller's VK
  comparison.

---

## 5. Adjacent, real, and already documented — do not confuse it with this

`verify_all_tables` reads its `CommonData` from **the proof itself** —
`batch_stark_prover.rs:983`, `let common = &proof.stark_common;`. On its own, therefore,
`verify_all_tables` answers *"is this proof internally consistent for the circuit it declares itself
to be?"*, not *"is this a proof of OUR circuit?"* The circuit binding is the separate
`recursion_vk_fingerprint` anchor comparison performed by the caller (see `grain-verify/src/r3.rs:57`).

This is **not** the `tableOpenings` question, it is **not** new, and it is already stated with
precision in the fork's own doc comment at `plonky3_recursion_impl.rs:666-695`, including the honest
limit that child-proof circuit identity is *not* pinned through the root and needs fork work. Recorded
here only so a future reader does not mistake it for a finding of this investigation.

---

## 6. What was read

Read in full or in the cited ranges, on disk, at the pinned revs:

- `~/.cargo/git/checkouts/plonky3-recursion-2254dc838bc79d6b/0a4a554/circuit-prover/src/batch_stark_prover.rs`
  — `:100-120`, `:255-330`, `:420-549`, `:920-1000`, `:1403-1522`
- `~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/batch-stark/src/verifier/mod.rs` — all 646 lines
- `~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/lookup/src/logup.rs:305-325`
- `~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/uni-stark/src/error.rs:10-20`
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/FriVerifier.lean:425-480`, `:780-880`
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/ExtFieldChallenge.lean:687-790`
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/FriLdtExtractDeployed.lean:840-910`
- `/Users/ember/dev/breadstuffs/circuit-prove/src/plonky3_recursion_impl.rs:670-830`
- `/Users/ember/dev/breadstuffs/Cargo.toml:195-290` (the pins), `Cargo.lock:15726-15732` (the resolve)

Cross-refs: `docs/PLAN-fri-proximity-apex-connection.md` §4 Slice A (this document discharges its
⚑ REQUIRED CHECK), `docs/OPENING-SOUNDNESS-DECONFLATED.md`.
