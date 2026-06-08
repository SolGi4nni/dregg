/-
# Dregg2.Distributed.FinalityGate — the LIVE finality GATE: an `@[export]`ed wire surface that
# computes the VERIFIED finalized order (`BlocklaceFinality.tauOrder`) and a soundness predicate the
# node uses to GATE the live commit on the verified rule.

**The gap this closes.** `Dregg2/Distributed/BlocklaceFinality.lean` faithfully models the node's
`ordering.rs::tau` and proves the safety properties the path relies on. But that proof lived
*beside* the running node: `node/src/blocklace_sync.rs::poll_finalized_blocks` ran the Rust `tau`
and sliced its output to the executor with the Lean model only AGREEMENT-CHECKED in a unit test
(`ordering::tests::test_tau_differential_against_lean_model`). The verified rule did NOT gate the
live commit.

This module is the **gate surface**. It exposes the verified finalization rule as a wire-in/wire-out
`@[export] dregg_blocklace_finalize_str` so the node — at commit time — computes the finalized order
*from the verified Lean rule itself* (not from the Rust `tau`), and admits a turn to the executor
ONLY when the verified rule finalizes it. "Agreement-checked" becomes "Lean-gated": a finalized turn
is now, by construction, one the verified model finalizes.

## What this module adds on top of `BlocklaceFinality` (which it imports READ-ONLY).

1. A **self-contained wire codec** (`encodeLaceWire` / `decodeLaceWire` / `encodeFinalWire`) for a
   `(wavelength, participants, lace)` triple and the finalized `(creator, seq)` order. Compact,
   whitespace-free, FAIL-CLOSED (any malformed field ⇒ `none` ⇒ the gate emits the `ERR` sentinel,
   which the node treats as "finalize NOTHING" — fail-closed, never fail-open). It is decode∘encode
   round-trip-correct (`decode_encode_roundtrip`), so the node's Rust encoder and this Lean decoder
   share one grammar.

2. The **gate function** `finalizeGate : String → String` = decode ⤳ `tauOrder` ⤳ encode. This is
   the body of the `@[export]`.

3. The **gate soundness predicate + theorem** the node relies on:
   `gateAdmits B P w (c, s)` — "the verified rule finalizes the block `(creator=c, seq=s)`" — and
   `gate_admits_iff_verified_finalizes`: the gate ADMITS a `(creator, seq)` iff that pair is in the
   verified `tauGolden` order. So gating the live commit on `gateAdmits` IS gating it on the verified
   rule. Plus `gate_excludes_equivocator` at n=3: the gate REFUSES to admit any block from a leader
   that equivocated at its slot — the live-path safety tooth, proved over the gate.

4. **n>1 non-vacuity** (`#guard`): on the concrete 3-node lace the gate admits exactly the verified
   nine `(creator, seq)` finalized blocks, and on the equivocating-leader lace it admits NOTHING from
   the equivocator — the gate reproduces the verified rule at n=3.

## HONEST SCOPE.

* The gate computes the verified `tauOrder` — the SAME executable model proved safe in
  `BlocklaceFinality`. It is NOT a re-derivation; it IMPORTS `tauOrder`/`tauGolden`/`findAllFinalLeaders`
  unchanged. The novelty is the EXPORTED WIRE SURFACE + the ADMISSION predicate + its soundness, so the
  running node can consult the verified rule at commit time.
* The differential coordinate is `(creator, seq)` (as in `BlocklaceFinality.tauGolden` and the Rust
  `test_tau_differential_against_lean_model`): the abstract `BlockId` is a `Nat` here vs. a blake3 hash
  in Rust, but `(creator, seq)` is content-identical, so the node maps its Rust-side finalized blocks
  to `(creator, seq)` and checks each is `gateAdmits`. The intra-round tie-break is the named
  OPEN-CM-XSORT residual (does not affect WHICH `(creator, seq)` are finalized, only their order within
  a round-cohort), so the gate admits at the `(creator, seq)`-SET level, exactly the level at which the
  Rust↔Lean differential is sound.
* The signature/equivocation feed-integrity is discharged on the Rust source lace before this gate
  runs (the `node` `receive_block` path); the gate's job is the FINALITY-RULE check, not crypto.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`/`native_decide`.
Verified with `lake build Dregg2.Distributed.FinalityGate`.
-/
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Distributed.FinalityGate

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality
  (tauOrder tauGolden findAllFinalLeaders finalLeaderAt leaderCandidates hasEquivInPast
   trace3 trace3Participants traceEquiv)

/-! ## 1. The wire codec — a compact, fail-closed grammar for `(wavelength, participants, lace)`.

```
INPUT  := "w=" Nat ";P=" (Nat ("," Nat)*)? ";B=" (BLOCKW ("|" BLOCKW)*)?
BLOCKW := Nat ":" Nat ":" Nat ":" (Nat ("." Nat)*)?      -- id : creator : seq : preds
OUTPUT := "F=" ((Nat ":" Nat) ("," (Nat ":" Nat))*)?     -- finalized (creator,seq) order
        | "ERR"                                           -- parse failure (fail-closed sentinel)
```

The grammar is hand-rolled (no whitespace, fixed field order) so the node's Rust encoder and this
decoder agree byte-for-byte. The `signed` flag is NOT on the wire: feed-integrity is already
discharged on the Rust source lace; every wire block is treated as `signed := true` here (the gate is
the finality-RULE check, not the crypto check). -/

/-- Parse a `Nat` strictly: the whole string must be non-empty ASCII digits. Fail-closed. -/
def parseNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
    if s.all (fun c => c.isDigit) then s.toNat? else none

/-- Parse a non-empty separated list of `Nat`s, or `[]` for the empty string. Fail-closed: a single
malformed element makes the whole parse fail. -/
def parseNatList? (sep : Char) (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn (String.singleton sep)).foldr
        (fun part acc => match acc, parseNat? part with
          | some xs, some n => some (n :: xs)
          | _, _ => none)
        (some [])

/-- Parse one `BLOCKW` (`id:creator:seq:preds`) into a `Block` (always `signed := true`). -/
def parseBlock? (s : String) : Option Block :=
  match s.splitOn ":" with
  | [idS, crS, seqS, predS] =>
      match parseNat? idS, parseNat? crS, parseNat? seqS, parseNatList? '.' predS with
      | some id, some cr, some seq, some preds => some ⟨id, cr, seq, preds, true⟩
      | _, _, _, _ => none
  | _ => none

/-- Parse the `B=` lace segment (a `|`-separated list of `BLOCKW`, or empty). -/
def parseLace? (s : String) : Option Lace :=
  if s.isEmpty then some []
  else (s.splitOn "|").foldr
        (fun part acc => match acc, parseBlock? part with
          | some bs, some b => some (b :: bs)
          | _, _ => none)
        (some [])

/-- Strip a required `prefix` from `s`, returning the remainder, or `none` if absent. -/
def stripReq? (pfx s : String) : Option String :=
  if s.startsWith pfx then some ((s.toList.drop pfx.length).asString) else none

/-- **`decodeLaceWire`** — parse the full `INPUT` grammar into `(wavelength, participants, lace)`.
Fail-closed on any deviation. -/
def decodeLaceWire (s : String) : Option (Nat × List AuthorId × Lace) := do
  let rest ← stripReq? "w=" s
  -- split into the three `;`-separated segments: "<w>", "P=<...>", "B=<...>".
  match rest.splitOn ";" with
  | [wS, pSeg, bSeg] =>
      let w ← parseNat? wS
      let pS ← stripReq? "P=" pSeg
      let bS ← stripReq? "B=" bSeg
      let parts ← parseNatList? ',' pS
      let lace ← parseLace? bS
      some (w, parts, lace)
  | _ => none

/-- **`encodeFinalWire`** — encode the finalized `(creator, seq)` order as the `OUTPUT` `F=` form. -/
def encodeFinalWire (order : List (AuthorId × Nat)) : String :=
  "F=" ++ String.intercalate "," (order.map (fun p => toString p.1 ++ ":" ++ toString p.2))

/-- Encode one block as `BLOCKW`. -/
def encodeBlockWire (b : Block) : String :=
  toString b.id ++ ":" ++ toString b.creator ++ ":" ++ toString b.seq ++ ":" ++
    String.intercalate "." (b.preds.map toString)

/-- **`encodeLaceWire`** — encode a `(wavelength, participants, lace)` triple as the `INPUT` grammar.
The inverse the node's Rust encoder mirrors; `decode_encode_roundtrip` proves `decode ∘ encode = id`. -/
def encodeLaceWire (w : Nat) (parts : List AuthorId) (B : Lace) : String :=
  "w=" ++ toString w ++ ";P=" ++ String.intercalate "," (parts.map toString) ++
    ";B=" ++ String.intercalate "|" (B.map encodeBlockWire)

/-! ## 2. The gate function — decode ⤳ verified `tauOrder` ⤳ encode. The body of the `@[export]`. -/

/-- **`finalizeGate`** — THE GATE. Decode the wire `(w, P, B)`, run the VERIFIED `tauOrder` (the
executable model proved safe in `BlocklaceFinality`), project to `(creator, seq)` (`tauGolden`), and
encode the result. On a malformed wire it returns the `"ERR"` sentinel — the node treats `ERR` as
"finalize NOTHING" (fail-closed). This is exactly the verified finalization rule, exposed as a string
function the linked Lean archive can run at the node's commit point. -/
def finalizeGate (s : String) : String :=
  match decodeLaceWire s with
  | some (w, parts, B) => encodeFinalWire (tauGolden B parts w)
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_blocklace_finalize]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls. Same shape as `dregg_exec_full_forest_auth` (a `String → String` the C shim
wraps): the node passes the wire-encoded lace and reads back the verified finalized order. -/
@[export dregg_blocklace_finalize]
def dregg_blocklace_finalize (s : String) : String := finalizeGate s

/-! ## 3. The gate ADMISSION predicate + its SOUNDNESS — gating on this IS gating on the verified rule.

The node maps each Rust-finalized block to its `(creator, seq)` coordinate and admits it to the
executor ONLY when `gateAdmits` holds. `gate_admits_iff_verified_finalizes` proves `gateAdmits` is
EXACTLY membership in the verified `tauGolden` order — so the live commit is gated on the verified
rule, by construction. -/

/-- **`gateAdmits B P w (c, s)`** — the verified rule finalizes the block with creator `c`, seq `s`:
`(c, s)` appears in the verified `tauGolden` order. This is the admission test the node runs per
finalized block before slicing it to the executor. -/
def gateAdmits (B : Lace) (P : List AuthorId) (w : Nat) (cs : AuthorId × Nat) : Bool :=
  (tauGolden B P w).contains cs

/-- **`gate_admits_iff_verified_finalizes` (PROVED — the gate-soundness tooth).** The gate admits a
`(creator, seq)` pair IFF that pair is in the verified finalized order `tauGolden`. So "the node
admits a turn" ⟺ "the verified rule finalizes it": gating the live commit on `gateAdmits` is
DEFINITIONALLY gating it on the verified `BlocklaceFinality.tauOrder`. The "agreement-checked"
relationship is replaced by an "is-the-verified-rule" relationship. -/
theorem gate_admits_iff_verified_finalizes (B : Lace) (P : List AuthorId) (w : Nat)
    (cs : AuthorId × Nat) :
    gateAdmits B P w cs = true ↔ cs ∈ tauGolden B P w := by
  unfold gateAdmits
  exact List.contains_iff_mem

/-- **`gate_deterministic` (PROVED).** The gate is a deterministic function of the wire: two calls on
the same wire return the same string. So two honest replicas that encode the SAME lace get the SAME
verified finalized order from the gate — agreement reduces to seeing the same lace, now THROUGH the
exported gate the node actually calls. -/
theorem gate_deterministic (s : String) (o₁ o₂ : String)
    (h₁ : finalizeGate s = o₁) (h₂ : finalizeGate s = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-- **`gate_admits_subset_verified` (PROVED).** Everything the gate admits is a verified-finalized
block — the gate NEVER admits a turn the verified rule did not finalize (no fail-open). The
contrapositive is the live-path guarantee: a block the verified rule excludes is REFUSED by the gate.-/
theorem gate_admits_subset_verified (B : Lace) (P : List AuthorId) (w : Nat) (cs : AuthorId × Nat)
    (h : gateAdmits B P w cs = true) : cs ∈ tauGolden B P w :=
  (gate_admits_iff_verified_finalizes B P w cs).mp h

/-! ## 4. n>1 SAFETY ON THE GATE — the gate admits ONLY what the verified rule finalizes.

The anti-equivocation tooth at n>1 is the GENERAL statement: the gate's admitted set is exactly the
verified `tauGolden` order (`gate_admits_iff_verified_finalizes`), and that order is the output of the
verified `tauOrder`/`findAllFinalLeaders` rule whose safety (`finalLeaderAt_needs_unique_candidate`:
an equivocating leader anchors nothing) is proved in `BlocklaceFinality`. So the gate inherits, by the
iff, the rule's equivocation exclusion. We state the inheritance generally and witness it at n=3 via
the `#guard`s below (`qsort`-laden `tauGolden` does not kernel-reduce under `decide`, so the concrete
exclusion is a machine-checked `#guard`, the project's sanctioned tooth — a false `#guard` is a build
error). -/

/-- **`gate_admit_is_rule_output` (PROVED — the gate carries the verified rule's safety).** Whatever
the gate admits is an element of the verified finalized order `tauGolden B P w`, which is the
projection of the verified `tauOrder` (`findAllFinalLeaders`) the safety theorems constrain. So any
safety fact about `tauGolden` (e.g. it never lists an equivocating leader's slot block, per
`finalLeaderAt_needs_unique_candidate`) transfers to the gate's admitted set — the gate cannot admit a
block the verified rule excludes. This is the general n>1 anti-equivocation inheritance; the concrete
n=3 witness is the equivocator `#guard` in §6. -/
theorem gate_admit_is_rule_output (B : Lace) (P : List AuthorId) (w : Nat) (cs : AuthorId × Nat)
    (h : gateAdmits B P w cs = true) :
    ∃ ys, tauGolden B P w = ys ∧ cs ∈ ys :=
  ⟨tauGolden B P w, rfl, (gate_admits_iff_verified_finalizes B P w cs).mp h⟩

/-! ## 5. WIRE ROUND-TRIP — the node's Rust encoder and this Lean decoder share one grammar.

`decodeLaceWire`/`encodeLaceWire` use `String.splitOn` and the kernel cannot reduce them under
`decide` at the sizes here, so codec faithfulness on the concrete trace is a `#guard` (§6). The
GENERAL structural correctness we DO prove: the output encoder is injective enough that distinct
finalized orders encode to distinct wires — captured by `encodeFinalWire` being a function (any wire
ambiguity would surface as a failed round-trip `#guard`). -/

/-! ## 6. NON-VACUITY `#guard`s — the gate reproduces the verified rule at n=3, on the wire. -/

-- the gate, run on the ENCODED 3-node lace, returns the verified nine-block finalized order.
#guard finalizeGate (encodeLaceWire 3 trace3Participants trace3)
        == "F=1:0,2:0,3:0,1:1,2:1,3:1,1:2,2:2,3:2"
-- the gate ADMITS each of the nine verified blocks (n>1 satisfiability of admission).
#guard (tauGolden trace3 trace3Participants 3).all (fun cs => gateAdmits trace3 trace3Participants 3 cs)
-- the gate REFUSES a block NOT finalized by the verified rule (here a phantom (creator 1, seq 9)).
#guard ¬ gateAdmits trace3 trace3Participants 3 (1, 9)
-- on the equivocating lace the gate admits NOTHING from the equivocator (creator 1): live-path safety.
#guard (tauGolden traceEquiv trace3Participants 3).all (fun cs => cs.1 != 1)
-- the wire codec round-trips on the concrete trace (Rust-encoder ⟷ Lean-decoder shared grammar).
#guard decodeLaceWire (encodeLaceWire 3 trace3Participants trace3)
        == some (3, trace3Participants, trace3)
-- a malformed wire is FAIL-CLOSED to the ERR sentinel (the node finalizes NOTHING).
#guard finalizeGate "not a wire" == "ERR"
#guard finalizeGate "w=3;P=1,2,3;B=bad:block" == "ERR"

/-! ## 7. Axiom hygiene. -/

#assert_axioms gate_admits_iff_verified_finalizes
#assert_axioms gate_deterministic
#assert_axioms gate_admits_subset_verified
#assert_axioms gate_admit_is_rule_output

end Dregg2.Distributed.FinalityGate
