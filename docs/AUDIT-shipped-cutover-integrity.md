# AUDIT — shipped-cutover integrity at HEAD (2026-07-24)

Read-only integrity audit of everything the E1 / E8 / L0-L2-L3 campaign landed, measured
against the live tree rather than against the commit messages. Nothing was fixed; every
finding below is a report, because a repair here can collide with a live lane.

## 0. Method and baseline

The tree moved under the audit. HEAD advanced **five times** while measuring:

| when | HEAD | note |
|---|---|---|
| audit start | `16662e7c73` | our L2 commit |
| +4 min | `6d4b480cc5` | intent predicate-forgery lane |
| +25 min | `9648759c79` | **E7 by-name narrowing** — re-stamped 2 PROVENANCE rows mid-audit |
| +30 min | `2b44e2f39d` | |
| audit end | `fab26a85a8` | ~60 files dirty, ~10 lanes live |

Byte measurements were taken against the working tree; every shipped artifact below was
re-checked at the final HEAD and none of our bytes moved. Where a number changed because a
lane landed mid-audit it is called out.

Three evidence classes are used, in increasing strength:

1. **self-consistency** — `sha256(file) == committed pin`. Proves only that a file matches a
   hash committed beside it.
2. **stamp agreement** — `sha256(file) == PROVENANCE.json row`.
3. **Lean agreement** — `file == lake env lean --run <emitter>` output, byte-for-byte. This is
   the only one that catches a committed JSON gone stale while the Lean moved underneath it.

Class 3 was obtained by running the emitters read-only into a scratch dir, and by running
`scripts/emit-descriptors.sh` with **no** `DREGG_VK_REGEN_ACK` — the design guarantees a
byte-changing install is refused with the tree untouched (`emit_descriptors.py:379`,
`install_and_stamp` at `:921`; `write_file` only buffers). Verified empirically: a 147-file
sha256 snapshot of every guarded path was **byte-identical before and after** the run.

Caveat, stated plainly: `scripts/check-descriptor-drift.sh` additionally does
`lake build Dregg2 <emitter modules>` *first*, so its verdict is over **fresh** oleans. I did
not run that build — it would take the lake lock and recompile ~25 other lanes' dirty Lean
files. Every class-3 result below is therefore **"against the currently-warm oleans"**, which
is weaker than a cold-checkout drift run. It is strong enough to catch a moved descriptor; it
is not strong enough to catch a Lean edit that has not been compiled yet.

---

## 1. VERDICT TABLE

| # | shipped item | verdict | evidence |
|---|---|---|---|
| 1 | **E1 cutover** `bd21266e6b` (+ fix `3ebf42e25f`) | **HOLDS** — compaction live and byte-exact | see §2 |
| 1a | └ `e1_compact_generated.rs` bytes | **DRIFTED (cosmetic, OURS)** | rustfmt-wrapped vs generator output; semantically identical |
| 1b | └ PROVENANCE rows for both wide TSVs + the FP file | **DRIFTED (stale, OURS)** | stamped at the *pre-fix* E1 values |
| 2 | **E8 bilateral** `316982c0d1` | **HOLDS** — fully, all three evidence classes | see §3 |
| 3 | **L3 shielded emit-wiring** `9c50fc934e` | **HOLDS** — fully, all three evidence classes | see §4 |
| 4 | **L0 accumulator** `0121dc283b` | **HOLDS** — present, wired, compiles | see §5 |
| 5 | **L2 grow-gate** `16662e7c73` | **HOLDS** — present, registered, builds green | see §5 |
| 6 | `check-descriptor-drift.sh` | **RED** — 2 artifacts, 1 ours (cosmetic), 1 not | see §6 |
| 7 | `check-lean-orphans.sh` | **RED** — 3 failures, **none ours** | see §7 |
| 8 | `PROVENANCE.json` internal consistency | **RED** — 9 rows, 3 ours | see §8 |

All five shipped commits are ancestors of HEAD. Nothing was reverted, clobbered, or lost.

---

## 2. E1 cutover — HOLDS

The concern was that a later concurrent regen (`3ebf42e25f`, 07-23 16:30, *"FIX the E1
compaction break that silently un-ran EVERY game's fold"*) had moved the transfer to 1610 and
re-pinned the WIDE FP, possibly un-running the compaction. It did not. It **narrowed the
kill-set** — the E1 compaction is still applied, just no longer reaching into the
post-compaction gentian block.

**Compaction still in the emit path** (both probes, clean at HEAD):

- `metatheory/EmitWideRegistryProbe.lean:141-142` — `if …RotWideCompactE1.transitionCeilingOk cm e1Floor then let e1cm := …RotWideCompactE1.compactE1 cm ks`
- `metatheory/EmitWideUMemWeldRegistryProbe.lean:142-143` — same, gated at ceiling 90

**Widths — compacted, not back at 1704:**

| member | pre-E1 (S2 flag-day) | at `bd21266e6b` | **at HEAD** |
|---|---|---|---|
| `transferVmDescriptor2R24` (bare wide) | 1704 | 1601 | **1610** |
| welded transfer | — | 1608 | **1617** |

Kill-set for transfer at HEAD is `[(90,98), (101,186), (187,188)]` = **94 columns**, and
`1704 − 94 = 1610` exactly. The 9 columns the fix gave back are precisely the gentian reach.

**Byte-exact against the live Lean emission (class 3):**

| artifact | disk sha256 | live re-emit sha256 | Rust FP pin |
|---|---|---|---|
| `circuit/descriptors/rotation-wide-registry-staged.tsv` | `4e7bf856096ff322…` | `4e7bf856096ff322…` ✓ | `effect_vm_descriptors.rs:1219` = `4e7bf856…` ✓ |
| `circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` | `39805f70d569b70e…` | `39805f70d569b70e…` ✓ | `effect_vm_descriptors.rs:1245` = `39805f70…` ✓ |

(Both are git-LFS — `.gitattributes` maps `circuit/descriptors/*staged*.tsv` to `filter=lfs`.
The committed LFS pointer OIDs equal the on-disk content hashes, so the deployed bytes at HEAD
really are these.) **FP == sha256(descriptor) today.**

**Kill-set table is single-sourced and correct:** `circuit/src/effect_vm/e1_compact_generated.rs`
carries **57/57** registry members (no member missing, none extra), and every member's kill-set
runs match the live `e1compact` emitter lines **exactly, 0/57 mismatches**. No run reaches past
its member's committed width, so the deployed producer's pre-gentian `compact_e1` cannot panic
on a short row — the exact failure `3ebf42e25f` fixed.

**Producer wiring intact and clean:** `circuit/src/effect_vm/trace_rotated.rs:4155` (the
function), `:4771`, `:4826`, `:5905` (call sites); `sdk/src/full_turn_proof.rs:1851`, `:2015`,
`:3232`, `:3474`, `:3507` (5 sites, as shipped).

### 2a. DRIFTED (cosmetic, OURS) — `e1_compact_generated.rs` is rustfmt-wrapped

`circuit/src/effect_vm/e1_compact_generated.rs` is header-identical and **semantically
identical** to the generator's output — every `(key → kill-set runs)` pair matches — but the
bytes differ:

```
--- GENERATED (emit_descriptors.py:735-761)      59 body lines
+++ ON-DISK                                     219 body lines
-    ("transferVmDescriptor2R24", &[(90, 98), (101, 186), (187, 188)]),
+    (
+        "transferVmDescriptor2R24",
+        &[(90, 98), (101, 186), (187, 188)],
+    ),
```

**Root cause — a structural conflict, not a mistake.** `.git/hooks/pre-commit` →
`scripts/git-hooks/pre-commit` *"rustfmt every STAGED .rs file on its way into the commit"*.
It does not exempt `@generated … DO NOT EDIT BY HAND` files, and `emit_descriptors.py` has no
rustfmt step. So the file was reformatted on its way into `bd21266e6b` (613 lines / 57 wrapped
rows) and again into `3ebf42e25f` (238 lines / 51 wrapped rows) — **rustfmt'd from birth**.

Consequence: `check-descriptor-drift.sh` can **never** go green for this file, no matter how
correct the E1 work is. `s2_compact_generated.rs` escapes only by luck — its rows are short
enough that rustfmt leaves them on one line (0 wrapped rows).

### 2b. DRIFTED (stale, OURS) — PROVENANCE still stamps the pre-fix E1 build

| row | PROVENANCE says | disk actually is |
|---|---|---|
| `rotation-wide-registry-staged.tsv` (`PROVENANCE.json:99`) | `5329ead701d21299…` | `4e7bf856096ff322…` |
| `rotation-wide-umem-welded-registry-staged.tsv` (`:101`) | `2c2b949e8b63a369…` | `39805f70d569b70e…` |
| `circuit/src/effect_vm_descriptors.rs` (fp-file) | `888567f5185d…` | `94d479b3891c…` |

`5329ead7…` / `2c2b949e…` are the **E1-cutover-era** hashes — the build whose kill-set reached
into the gentian block. They exist nowhere on disk now. `bd21266e6b` deliberately excluded
PROVENANCE (documented in its message, to avoid a regen collision); `3ebf42e25f` then moved the
bytes **and the FP constants** without re-stamping. E8 and L3 later made targeted minimal edits
to PROVENANCE and carried the stale rows forward unnoticed.

The deployed bytes are fine and self-consistent with the Rust FP pins. It is the **provenance
record that lies**: read literally, it attests that the deployed wide registry is the
fold-breaking build.

---

## 3. E8 bilateral — HOLDS (fully)

| check | result |
|---|---|
| `dregg-bilateral-aggregation-v3.json` sha256 | `6b8b58dbdd461154…` |
| == PROVENANCE `descriptor_sha256` row | ✓ |
| == live `lake env lean --run EmitBilateralLegs.lean` | ✓ byte-exact, 4716 B |
| == `#guard emitVmJson2 bilateralAggDescriptorV3 == …` GOLDEN in `BilateralAggregationCompact.lean:204` | ✓ byte-exact, 4716 B |
| shape | `trace_width` 52, 48 constraints (`#guard`s at `:108`, `:196`, `:198`, `:199`) |
| v2 JSON | **deleted from disk**; no lane re-introduced it |
| Rust twin | `circuit/src/bilateral_aggregation_air.rs:137` `include_str!("…-v3.json")`, `:140` name `-v3`, width 52 (`:71`, `:361`); file clean |
| fp-file row `bilateral_aggregation_air.rs` | ✓ matches PROVENANCE |

Three independent evidence classes agree. This is the cleanest of the shipped items.

**Residual debt (not a break, not urgent).** The superseded v2 Lean objects were never deleted:

- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitBilateralAgg.lean:252` still defines
  `bilateralAggDescriptor` with `name := "dregg-bilateral-aggregation-v2"`, and `:274` still
  `#guard`s its v2 JSON prefix.
- `metatheory/Dregg2/Circuit/Emit/BilateralAggregationEmit.lean:54` still carries the full
  **width-87 v2 GOLDEN** string literal, `#guard`ed at `:58`.
- Two doc-comments now point at a file that does not exist:
  `BilateralAggregationCompact.lean:40` and `BilateralAggregationEmit.lean:13` both name
  `circuit/descriptors/dregg-bilateral-aggregation-v2.json`.

Neither v2 object is emitted to any file and no Rust references v2, so nothing deployed is
affected. But per *"delete the superseded object"* this is exactly the additive residue that
later gets mistaken for a live surface — and the two doc-comments are now false.

---

## 4. L3 shielded emit-wiring — HOLDS (fully)

All three by-name JSONs verified in all three classes:

| descriptor | sha256 | == PROVENANCE row | == live `EmitByName` | == module GOLDEN | shape |
|---|---|---|---|---|---|
| `dregg-shielded-spend-pinned-root-v1.json` | `244f14e0d6bd4f78…` | ✓ | ✓ | ✓ 3997 B | tw 48, PI 4, 19 cons |
| `dregg-shielded-value-link-conserve-ranged-v1.json` | `28d05922f8137a81…` | ✓ | ✓ | ✓ 2107 B | tw 23, PI 2, 11 cons |
| `dregg-shielded-wide-value-link-conserve-v1.json` | `6c5a8cbd1f051b7f…` | ✓ | ✓ | ✓ 3952 B | tw 30, PI 9, 18 cons |

GOLDEN literals live at `ShieldedSpendDescriptor.lean:518`,
`ShieldedValueRangeDischarge.lean:483`, `ShieldedWideValueLinkDescriptor.lean:1052`.
All three are bare (no trailing newline), consistent with the emitter convention
(`BY_NAME_NEWLINE_TERMINATED`, 22 entries, does not include them).

`metatheory/EmitByName.lean:251` `#guard byNameDescriptors.length == 62` holds; the table parses
to exactly 62 entries with the three shielded arms at `:228-233`.

**Whole by-name surface re-derived from Lean:** of the 62 emitted names, **61 exist on disk and
every single one is byte-identical to the live Lean emission** (39 exact; 22 differ only by the
trailing newline the installer adds for exactly the 22-name `BY_NAME_NEWLINE_TERMINATED` set).
**Zero real content drift in the by-name surface.** One name has no file — see §6.

L3's claim that `descriptor_by_name.rs` gets no new arm is accurate: the Rust dispatch has 34
`include_str!` arms against EmitByName's 62, a deliberate superset.

---

## 5. L0 accumulator / L2 grow-gate — HOLD

**L0 `0121dc283b`** — `cell/src/shielded_note_set.rs` (27,289 B) present and clean; wired at
`cell/src/lib.rs:63` (`pub mod shielded_note_set;`) and `:192` (`pub use …::ShieldedNoteSet;`).
All 11 files of the commit are clean at HEAD. `cargo check -p dregg-cell` **finishes clean**
(36 s, no errors).

**L2 `16662e7c73`** — `metatheory/Dregg2/Circuit/Emit/ShieldedNoteAppendDescriptor.lean`
(50,201 B) present and clean; registered at `metatheory/Dregg2.lean:1024`.
`lake build Dregg2.Circuit.Emit.ShieldedNoteAppendDescriptor` → **Build completed successfully
(3167 jobs)**. No `sorry` / `admit` / `native_decide` (the 5 grep hits are the English word
*"admits"* in prose and one doc-comment naming the three).

Neither module is an orphan; L2 is reachable from the `Dregg2` root.

---

## 6. `check-descriptor-drift.sh` — RED. Whole-tree drift is exactly TWO artifacts.

Measured by running `scripts/emit-descriptors.sh` with no ACK (exit **3 = REGEN REFUSED**, tree
verified untouched across all 147 guarded files). All 15 emitters ran. Verbatim:

```
emit_descriptors: REGEN REFUSED — this emission would change 2 artifact(s) …
  Would change:
    by-name/guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json
    circuit/src/effect_vm/e1_compact_generated.rs
```

That is the entire drift surface of the repository. Attribution:

| artifact | whose | nature |
|---|---|---|
| `by-name/guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json` | **NOT OURS** — hidden-span lane | Listed in `EmitByName.lean:243` since `9f2bd1266a` (07-23 21:23, *"start .spw"*, a sweep-up). The file has **never been committed in any ref**. Emit module `GuardedHidingSpanWideBlindEmit` last touched by `20b9d9a20f` (07-24 14:52, hidden-span cutover) — and is itself an unlisted **orphan** (§7). |
| `circuit/src/effect_vm/e1_compact_generated.rs` | **OURS (E1)** | rustfmt-wrapping only; semantically identical (§2a). |

**Nothing E8 or L3 shipped drifts.** The E1 *descriptor bytes* do not drift either — only the
generated Rust projection's formatting.

Two structural notes on this gate:

- It is **ungreenable while the rustfmt conflict stands** (§2a). A gate that cannot go green
  hides the next real break, which is precisely the failure mode this gate exists to prevent.
- A second, independent trip-wire sits behind it: `require_regen_ack` also refuses whenever
  `metatheory/Dregg2` is dirty (`emit_descriptors.py:379`). With ~25 dirty Lean files across
  live lanes, the gate cannot reach a *clean* verdict at all right now, even once the two
  artifacts above are settled. This is by design ("minted from an UNREVIEWABLE source tree")
  but it means the gate is structurally unrunnable during a wide swarm.

---

## 7. `check-lean-orphans.sh` — RED, three separate failures, **none ours**

```
1697 Dregg2/**.lean files; 1563 reachable, 134 orphan (95 allowlisted, 39 UNLISTED);
123 allowlist entries
```

| failure | count | attribution |
|---|---|---|
| **UNLISTED orphans** (compile in no CI target) | **39** | none ours — see cluster table |
| **STALE allowlist (now-reachable)** | **23** | Predicates\*/Presentation\*/AccumulatorNonRevocation\* (17), Circuit (2), Bridge (4) — pre-existing bookkeeping debt |
| **STALE allowlist (no such file)** | **5** | `QuantifiedAbsenceRefineAudit`, `QuantifiedAbsenceRung2`, `RotatedLayoutBridge`, `TemporalPredicateRung2`, `PresentationBindingFromFold` |

The 39 unlisted orphans by lane:

| cluster | n | example → owning commit |
|---|---|---|
| PQ / Keccak / ML-DSA / ML-KEM / ACVP | ~19 | `Dregg2.Crypto.MlKemKeygen` → `6fec4b8283` |
| `GuardedHidingSpan*` (hidden-span) | 5 | → `20b9d9a20f` (07-24 14:52) |
| FRI / correlated agreement | 3 | `CorrelatedAgreement.Interface` → `d2ecbf38fe`; `FriIncidenceDesign` → `28337c8ae3`; `ForMathlib.PolishchukSpielman` **untracked, live** |
| Peephole | 2 | **untracked, live WIP** |
| automatafl | 2 | `AutomataflNGenGolden` → `bc3bdb3f1a`; `Games.AutomataflDifferential` → `930da7a570` |
| shielded sibling | 1 | `Dregg2.Circuit.ShieldedOnRampPin` — from the on-ramp lane, **not one of our 5 commits** |
| misc emit/model | rest | `DfaRoutingTableEmit` → `20b9d9a20f`; `AttestedFactsRootModel` → `8282fca377` |

**Our L2 module is correctly registered** and does not appear. E1/E8/L3 added no orphans.

Because the allowlist itself is 28 entries wrong (23 + 5), this gate currently fails for
bookkeeping reasons *before* it can report on real orphans — the same "red gate hides the next
break" disease as §6.

---

## 8. `PROVENANCE.json` internal consistency — 9 mismatching rows

`--verify-provenance` exits **1**. (It reported **11** rows at audit start; the E7 lane landed
`9648759c79` mid-audit and correctly re-stamped `merkle-membership-depth2.json` and
`poseidon2-hash-arity2.json`, taking it to 9.)

| # | row | whose | why |
|---|---|---|---|
| 1 | `rotation-wide-registry-staged.tsv` mismatch | **OURS (E1)** | stale at pre-fix `5329ead7…`; bytes moved at `3ebf42e25f` without re-stamp |
| 2 | `rotation-wide-umem-welded-registry-staged.tsv` mismatch | **OURS (E1)** | same |
| 3 | fp-file `circuit/src/effect_vm_descriptors.rs` mismatch | **OURS (E1)** | same |
| 4-7 | `automatafl-{step-marks-n11, resolve-marks-n11, resolve-marks-n2, step-marks-n2}.json` on disk but **not covered by the stamp** | automatafl BRAID | committed by `b545aaddf0` / `953a746cab`, never stamped |
| 8-9 | `automatafl-legc-{n11, n5}.json` not covered | automatafl BRAID | **untracked**, live lane WIP |

**Ours: 3 of 9. Other lanes: 6 of 9.**

Root cause of the whole class: **there has been no canonical full re-stamp since
2026-07-23T06:17:46Z.** `PROVENANCE.json` still carries `generated_utc
2026-07-23T06:17:46Z`, `repo_head 2e7f6e65c3…`, `source_dirty: true` — and
`docs/VK-REGEN-LOG.md` confirms it (last full row 07-23 06:17; the only later row is E7's
*targeted* by-name entry). Every descriptor landing since — E1 cutover (11:54), E1 fix (16:30),
automatafl BRAID, E8, L3, E7 — has been a targeted hand-edit to the stamp or no edit at all.
The stamp is now a patchwork rather than a machine-generated attestation, which is why it
drifts silently.

Counts: `descriptor_sha256` 76 rows (0 missing files, 2 mismatch), `by_name_sha256` 55 rows
(0 missing files, 0 mismatch at final HEAD, 6 files uncovered), `fp_file_sha256` 5 rows (1
mismatch).

---

## 9. FIX LIST (prioritized)

### P0 — safe to do NOW, narrow, ours

**F1. Un-block `check-descriptor-drift.sh`: make the generator emit rustfmt-stable Rust.**
Owner: E1 lane (us). Files: `scripts/emit_descriptors.py` (the `e1_module` assembly at
`:735-761`, and ideally the `s2_module` at `:697-724` for the same reason) — run the buffered
generated-Rust content through `rustfmt --edition <ed>` before `GENERATED_RS[…] = …`, then
re-install so committed bytes == generator output. This closes the loop for *all* generated
modules permanently; `s2_compact_generated.rs` survives today only by line-length luck.
Complementary (weaker) alternatives: exempt `*_generated.rs` in `scripts/git-hooks/pre-commit`,
or add a `rustfmt.toml` `ignore` entry — both leave the two producers disagreeing, so prefer
the generator fix.
*Safe now:* it touches only the emit script + one `@generated` file, and the install is
byte-safe (generated-Rust-only changes take the non-ack `GENERATED-RUST UPDATE` path at
`install_and_stamp`). No descriptor bytes, no VK, no re-key.
**This is the single most urgent repair** — not because anything is broken, but because while
it stands the descriptor drift gate is *ungreenable*, so it cannot catch the next real break.

**F2. Delete the superseded E8 v2 objects + fix the two false doc-comments.**
Owner: E8 lane (us). `EffectVmEmitBilateralAgg.lean:252,274`,
`BilateralAggregationEmit.lean:13,54,58`, `BilateralAggregationCompact.lean:40`.
*Safe now:* additive-removal in Lean only; nothing emits or includes v2. Verify with
`lake build` + a re-run of `EmitBilateralLegs` (must stay byte-identical to v3.json).

### P1 — needs a clean(er) window, ours

**F3. Re-stamp the three stale PROVENANCE rows to the truth.**
Owner: E1 lane (us). Rows: `rotation-wide-registry-staged.tsv` → `4e7bf856096ff322…`,
`rotation-wide-umem-welded-registry-staged.tsv` → `39805f70d569b70e…`, fp-file
`circuit/src/effect_vm_descriptors.rs` → `94d479b3891c…`. All three values are *verified against
the live Lean emission* in §2, so the correct values are known with certainty.
*Why a window:* a full canonical `emit_descriptors.py` re-stamp is the right instrument but it
rewrites the whole stamp and would sweep other lanes' in-flight bytes (and needs
`DREGG_VK_REGEN_ALLOW_DIRTY=1` today, which records `source_dirty=true` and is then refused by
`--verify-provenance --strict`). A *targeted* three-row edit is safe now and is what E8/L3/E7
each did; it keeps the patchwork going but removes an actively false attestation. Recommend the
targeted edit now, canonical re-stamp at the next quiet window.

### P2 — other lanes, report only

**F4.** `by-name/guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json` — hidden-span lane.
Either emit + commit the file (the `EmitByName.lean:243` entry has been dangling since `9f2bd1266a`
on 07-23 21:23 and the file has never existed) or remove the entry and drop the count guard to 61.
**Do not fix this from our side** — it will collide with the live hidden-span lane.

**F5.** Six unstamped `automatafl-*` by-name rows — automatafl BRAID lane; two of them are still
untracked WIP. Rides the next canonical stamp.

**F6.** `scripts/lean-orphans-allow.txt` — 28 wrong entries (23 now-reachable, 5 deleted files).
Pure bookkeeping, no owner conflict, but it is not ours and it is what makes the orphan gate red
independent of the 39 real orphans.

**F7.** Workspace **test profile** is red at HEAD (reported by the E7 lane, confirmed by
inspection): `circuit/src/exact_cap_root.rs:522` (E0369) and `circuit/src/descriptor_ir2.rs:6471`
(non-exhaustive `Ir2Air::ExactPublicRow` match) are **both inside `#[cfg(test)]` blocks**
(nearest preceding `#[cfg(test)]` at `:486` and `:6290`). So `cargo build` / `cargo check` of the
libs is fine — `cargo check -p dregg-cell` passes — but `cargo test -p dregg-circuit` does not
compile. Not ours; affects any lane trying to run circuit tests.

---

## 10. Bottom line

Every byte this campaign shipped is intact and byte-exact against the live Lean emission. E8
and L3 are clean on all three evidence classes. E1's *descriptors* are clean too — the later
concurrent regen narrowed the kill-set rather than un-running the compaction, and the FP pins
were moved with it. L0 compiles, L2 builds green.

What drifted is **record-keeping around E1, not E1**: a `@generated` Rust file that the
pre-commit rustfmt hook reformats on every commit (permanently reddening the drift gate), and
three PROVENANCE rows still attesting the superseded pre-fix build. Both are ours and both are
repairable without touching a single deployed byte.

The gates are red mostly for other lanes' reasons — 6 of 9 provenance rows and all 39 unlisted
orphans belong elsewhere — but that is not comfort. Two gates that cannot go green are two
gates that will not catch the next real break.
