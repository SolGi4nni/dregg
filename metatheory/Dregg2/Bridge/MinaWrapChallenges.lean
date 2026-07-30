/-
# Dregg2.Bridge.MinaWrapChallenges — **a Mina Wrap proof's own Fiat–Shamir challenges, DERIVED
PER BLOCK from wire data, in COMPILED Lean.**

⚑ **SUBSTRATE.** No AIR. Two sponge schedules and a squeeze, authored in Lean because a transcript
IS semantics — which coordinate is absorbed in which order is the entire content of "these are the
proof's own challenges".

## The refusal this exists to retire

`bridge/src/mina_opening_check.rs` `PINNED_CHALLENGES` carries **one height** — devnet 539508 — and
every other height returns `ChallengesUnavailable` and proves nothing. The stated reason:

> A Wrap proof's own IPA opening challenges are Fiat–Shamir outputs of **its own transcript** … That
> needs the verifier index, the SRS and the 47 commitments — none of which are on the wire, and the
> in-kernel cost is 153 s per block.

Both halves of that need correcting, and the correction is this file.

**On the wire.** Of the six absorbed objects, five ARE on the wire and `mina_pickles.rs`
`decode_proof_at` already walks past every one — `challenge_polynomial_commitments` (kept),
`w_comm` (15 points, walked), `z_comm`, `t_comm` (7 chunks), and the opening's `lr`/`delta`. The
verifier-index DIGEST is one `Fp` element of trusted config, not "the verifier index". The only
absorbed object that is neither wire nor config is `public_comm` — a 40-point Lagrange MSM over the
public input, whose census is `Dregg2.Bridge.MinaWrapPublicInput` and whose remaining gap is the six
`expand_deferred` words.

**The 153 s is a KERNEL cost, not the function's cost.** `MinaWrapOpeningGate.ipaTranscript` is
already a plain compiled function `#guard`-evaluated in milliseconds; the 153 s is the ten kernel
`decide` instances of the opening RELATION in the same module. A sibling took a 3.5 h kernel MSM to a
20 s compiled path by exactly this move, and the same move here is: state the sponge schedules as
functions of wire arguments, evaluate them compiled, and keep the kernel for the CHECKER rather than
the INSTANCE.

## ⚑ Why this file is split from its reality gate, and it is a real cost decision

The anchor literals (`FQ_DIGEST`, `IPA_PRECHALS`, `C_PRE`, `T_FQ`, the tape) live in
`MinaRealBlockTranscript` / `MinaWrapOpeningGate` — five modules whose kernel `decide`s cost ~4 min
(82 s + 153 s + the rest). **Measured on the import graph: rooting them in `Dregg2/FFI.lean` would
add exactly those 5 modules to the archive's closure**, i.e. put four minutes of ONE BLOCK's kernel
proof into every build of the node's archive, forever, to obtain a compiled function that does not
need them at runtime.

So: **this file imports nothing but the sponge** (measured: 0 new modules in the FFI closure) and is
rooted in `Dregg2/FFI.lean`; `Dregg2.Bridge.MinaWrapChallengesWeld` imports the fixtures and
`#guard`s that these functions reproduce them on the real block, and is NOT rooted — the same
"same guarantee, off the hot path" split `mina_opening_check.rs` uses for descriptor drift.

## What this file establishes and what it does NOT

**Establishes:** given the absorbed objects, the 15 IPA prechallenges, `c′` and `t` of a Wrap
proof's opening argument are computable per block, compiled, at sponge cost.

**Does not:** it does not verify anything. Deriving a proof's challenges is the front half of a
verifier; the equations they feed (`MinaWrapOpeningGate.opening_relation_holds`, the `⟨s, srs.g⟩`
leg) are what a verification is, and they are not here. And the derivation is only as good as
`public_comm`, which is only as good as `expand_deferred`, which **does not exist in this tree**.
Until it does, this file's `pu` argument has to come from the extractor and the per-block path is
NOT closed. Said plainly rather than implied by a green build.

## Trusted, named

`vkDigest` is `index.digest::<EFqSponge>()` of the devnet blockchain verifier index — one `Fp`
element of CONFIG. It is the compressed form of the 56 `VK_INDEX` elements, the largest trusted
object under this whole story. A wrong digest produces a complete, self-consistent, entirely wrong
challenge vector, and nothing downstream can tell.
-/
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.PastaField

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaWrapChallenges

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq
  (SpongeSt fpParams newSponge absorbMany challenge squeeze1 digestInto)

/-! ## §1 — PHASE 1: the Fq-sponge, as a function of the absorbed objects.

`verifier.rs:161-283`, in order: the index digest, the `RecursionChallenge` commitments, the public
commitment, the 15 witness commitments, squeeze β, squeeze γ, absorb `z_comm`, squeeze α′, absorb
`t_comm`, squeeze ζ′. `oracles(...)` then takes `digest()` on a CLONE, so the state SRS::verify
receives is the one right after ζ′ — which is why this returns the state and not the digest. -/

/-- What phase 1 produces. -/
structure Phase1 where
  /-- The sponge state right after ζ′ — the state `SRS::verify` receives. -/
  st : SpongeSt
  /-- β, the first raw 128-bit squeeze. -/
  beta : Nat
  /-- γ, the second. -/
  gamma : Nat
  /-- α′, the quotient prechallenge. -/
  alphaChal : Nat
  /-- ζ′, the evaluation-point prechallenge. -/
  zetaChal : Nat
  /-- `fq_sponge.digest()`, reinterpreted in the SCALAR field — phase 2 chains on this. -/
  fqDigest : Nat
deriving Repr, DecidableEq

/-- **`wrapPhase1Of`** — phase 1 over the block's own absorbed coordinates.

Every argument is a flat list of `Fp` coordinates in absorb order (`absorb_g` absorbs `x` then `y`).
`prevComm` is `2 × 2` at `prev_challenges = 2`; `pubComm` is `2`; `wComm` is `2 × 15`; `zComm` is
`2`; `tComm` is `2 × 7`. The shapes are checked by `phase1WireOk`, not assumed. -/
def wrapPhase1Of (vkDigest : Nat) (prevComm pubComm wComm zComm tComm : List Nat) : Phase1 :=
  let s0 := absorbMany fpParams newSponge (vkDigest :: (prevComm ++ pubComm ++ wComm))
  let b := challenge fpParams s0
  let g := challenge fpParams b.1
  let s3 := absorbMany fpParams g.1 zComm
  let a := challenge fpParams s3
  let s5 := absorbMany fpParams a.1 tComm
  let z := challenge fpParams s5
  { st := z.1, beta := b.2, gamma := g.2, alphaChal := a.2, zetaChal := z.2
    fqDigest := digestInto fpParams z.1 qN }

/-- ⚑ **THE SHAPE REFUSAL.** binprot is positional and so is an absorb tape: a tape with the wrong
number of coordinates does not fail, it silently produces a different, perfectly well-formed
challenge vector. At `prev_challenges = 0` the tape is 33 elements instead of 37 and the four
leading coordinates do not exist — the Wrap object is not that object, and `shapeOkRec`'s
`prevLen = 0` freeze is exactly the error this refuses.

Also: every coordinate must be a CANONICAL `Fp` element. Poseidon's `absorbAt` enters inputs through
`(state + x) % p`, so `x` and `x + p` are one element at the digest and admitting both is admitting
two encodings of one transcript. -/
def phase1WireOk (prevComm pubComm wComm zComm tComm : List Nat) : Bool :=
  prevComm.length == 4 && pubComm.length == 2 && wComm.length == 30
    && zComm.length == 2 && tComm.length == 14
    && (prevComm ++ pubComm ++ wComm ++ zComm ++ tComm).all (fun x => decide (x < pN))

/-! ## §2 — THE OPENING ARGUMENT'S OWN CHALLENGES.

`ipa.rs:186-201` + `OpeningProof::challenges` (`ipa.rs:1013-1035`): absorb `shift_scalar(cip)`,
squeeze `t` in FULL (`challenge_fq`, the group map's preimage — NOT the 128-bit `challenge`), then
per round absorb `L` and `R` and squeeze a 128-bit prechallenge, then absorb `delta` and squeeze
`c′`. -/

/-- `absorb_fr` on the Pallas Fq-sponge (`sponge.rs:221-252`). Pallas's SCALAR modulus `q` EXCEEDS
its base modulus `p`, so the branch taken is the SPLITTING one: absorb the high bits, then the low
bit. **Two absorbs, not one** — `MinaWrapOpeningGate` pins that absorbing `cip` unsplit is a
different transcript, so the branch is load-bearing rather than cosmetic. -/
def absorbFr (s : SpongeSt) (x : Nat) : SpongeSt := absorbMany fpParams s [x / 2, x % 2]

/-- What the opening transcript produces. -/
structure IpaChallenges where
  /-- `challenge_fq()`'s output — the group map's preimage, a FULL `Fp` element. -/
  t : Nat
  /-- The 15 RAW 128-bit prechallenges, one per IPA round. -/
  prechals : List Nat
  /-- `c′`, squeezed after `delta`. -/
  cPre : Nat
deriving Repr, DecidableEq

/-- **`ipaChallengesOf`** — the transcript continuation, over a phase-1 state and the opening's own
wire values.

`rounds` is one `[L.x, L.y, R.x, R.y]` per IPA round, in round order; `dxy` is `delta`'s `(x, y)`.
Both are on the wire and both are walked-and-discarded by `decode_proof_at` today. `cipS` is
`shift_scalar(combined_inner_product)`, which is `expand_deferred`'s output and is the ONE argument
here that is not decodable. -/
def ipaChallengesOf (st : SpongeSt) (cipS : Nat) (rounds : List (List Nat)) (dxy : List Nat) :
    IpaChallenges :=
  let s := absorbFr st cipS
  let ts := squeeze1 fpParams s
  let r := rounds.foldl
    (fun (acc : SpongeSt × List Nat) blk =>
      let s' := absorbMany fpParams acc.1 blk
      let ch := challenge fpParams s'
      (ch.1, acc.2 ++ [ch.2])) (ts.1, [])
  let sd := absorbMany fpParams r.1 dxy
  { t := ts.2, prechals := r.2, cPre := (challenge fpParams sd).2 }

/-- The opening's wire shape: 15 rounds of 4 coordinates, a 2-coordinate `delta`, all canonical. -/
def openingWireOk (rounds : List (List Nat)) (dxy : List Nat) : Bool :=
  rounds.length == 15 && rounds.all (fun b => b.length == 4 && b.all (fun x => decide (x < pN)))
    && dxy.length == 2 && dxy.all (fun x => decide (x < pN))

/-! ⚑ The endomorphism lift — `ScalarChallenge(prechal).to_field(endo_r)`, from a 128-bit
prechallenge to the `Fq` scalar the relation multiplies by — is deliberately NOT here. It is
`Circuit.Emit.KimchiVerify.endoMap`, there is exactly one of it in this tree, and it belongs with the
CONSUMER because the opening relation and the `⟨s, srs.g⟩` leg want different forms of the same
prechallenge. This gate returns the RAW 128-bit squeezes, which is what
`MinaWrapOpeningGate.IPA_PRECHALS` is and what `derived_ipa_challenges` lifts. -/

/-! ## §3 — THE WHOLE PER-BLOCK DERIVATION, and what it refuses. -/

/-- Everything the derivation needs, named by its wire field so a slot cannot be swapped silently. -/
structure WrapAbsorbed where
  /-- `index.digest::<EFqSponge>()` — ⚑ TRUSTED CONFIG, one `Fp` element. -/
  vkDigest : Nat
  /-- `messages_for_next_step_proof.challenge_polynomial_commitments`, 2 × (x, y). WIRE. -/
  prevComm : List Nat
  /-- `public_comm`'s (x, y). ⚑ NOT on the wire — `MinaWrapPublicInput.publicCommOf` over the 40
  words, six of which need `expand_deferred`. This is the per-block path's only remaining gap. -/
  pubComm : List Nat
  /-- `commitments.w_comm`, 15 × (x, y). WIRE. -/
  wComm : List Nat
  /-- `commitments.z_comm`'s (x, y). WIRE. -/
  zComm : List Nat
  /-- `commitments.t_comm`, 7 × (x, y). WIRE. -/
  tComm : List Nat
  /-- `shift_scalar(combined_inner_product)`. ⚑ `expand_deferred`'s output. -/
  cipShifted : Nat
  /-- `bulletproof.lr`, 15 × [L.x, L.y, R.x, R.y]. WIRE. -/
  lr : List (List Nat)
  /-- `bulletproof.delta`'s (x, y). WIRE. -/
  delta : List Nat
  /-- The Pallas `endo_r`. CONFIG. -/
  endoR : Nat

/-- **`deriveWrapChallenges`** — the whole per-block derivation, or `none`.

`none` is the fail-closed answer and every caller treats it as a REFUSAL: a wrong-shaped tape, a
non-canonical coordinate, a short round list. Never a derivation "on what did arrive". -/
def deriveWrapChallenges (A : WrapAbsorbed) : Option (Phase1 × IpaChallenges) :=
  if phase1WireOk A.prevComm A.pubComm A.wComm A.zComm A.tComm
     && openingWireOk A.lr A.delta
     && decide (A.cipShifted < qN) then
    let p1 := wrapPhase1Of A.vkDigest A.prevComm A.pubComm A.wComm A.zComm A.tComm
    some (p1, ipaChallengesOf p1.st A.cipShifted A.lr A.delta)
  else none

/-- The shape gate really refuses: `prev_challenges = 0` (a 2-coordinate `prevComm`), a truncated
witness list and a non-canonical coordinate are all `false`, and the real shape is `true`. Kernel
`decide` over lengths and comparisons — no sponge is run. -/
theorem phase1_shape_discriminates :
    phase1WireOk (List.replicate 4 1) (List.replicate 2 1) (List.replicate 30 1)
      (List.replicate 2 1) (List.replicate 14 1) = true
    -- ⚑ prev_challenges = 0: the tape is four coordinates short and the object is not a Mina Wrap
    ∧ phase1WireOk [] (List.replicate 2 1) (List.replicate 30 1)
        (List.replicate 2 1) (List.replicate 14 1) = false
    -- 14 witness commitments instead of 15
    ∧ phase1WireOk (List.replicate 4 1) (List.replicate 2 1) (List.replicate 28 1)
        (List.replicate 2 1) (List.replicate 14 1) = false
    -- a single non-canonical coordinate
    ∧ phase1WireOk (List.replicate 4 pN) (List.replicate 2 1) (List.replicate 30 1)
        (List.replicate 2 1) (List.replicate 14 1) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- …and the opening shape likewise. A 14-round `lr` is a proof for a different index. -/
theorem opening_shape_discriminates :
    openingWireOk (List.replicate 15 [1, 1, 1, 1]) [1, 1] = true
    ∧ openingWireOk (List.replicate 14 [1, 1, 1, 1]) [1, 1] = false
    ∧ openingWireOk (List.replicate 15 [1, 1, 1]) [1, 1] = false
    ∧ openingWireOk (List.replicate 15 [1, 1, 1, 1]) [1] = false
    ∧ openingWireOk (List.replicate 15 [1, 1, 1, pN]) [1, 1] = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4 — THE WIRE + `@[export]`.

```text
INPUT  := "vk=" Nat ";er=" Nat ";pc=" NATS ";pu=" NATS ";wc=" NATS ";zc=" NATS ";tc=" NATS
          ";cs=" Nat ";lr=" NATS ";dl=" NATS
NATS   := Nat ("," Nat)*        -- possibly empty
OUTPUT := "b=" Nat ";g=" Nat ";a=" Nat ";z=" Nat ";fq=" Nat ";t=" Nat ";c=" Nat ";ch=" NATS
        | "ERR"
```

`lr` arrives FLAT — 60 numbers, re-chunked into 15 rounds of 4 here rather than by the caller,
because a caller that chunks is a caller that can mis-chunk. `ch` is the 15 RAW prechallenges;
`endoLift` is applied by whoever consumes them, since the relation and the `⟨s, srs.g⟩` leg want
different forms.

`"ERR"` is a refusal. There is no arm that derives challenges from a tape it could not shape-check.
-/

/-- Parse `"a,b,c"`. An empty string is the empty list; anything non-numeric is a refusal. -/
def parseNats? (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn ",").foldr
    (fun part acc => match part.toNat?, acc with
      | some n, some r => some (n :: r)
      | _, _ => none) (some [])

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- `chunk`'s worker, structurally recursive on FUEL rather than well-founded on the list — the
kernel reduces the former and this function runs inside a `#guard`. -/
def chunkAux (n : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, xs =>
      let h := xs.take n
      if h.length < n then [] else h :: chunkAux n fuel (xs.drop n)

/-- Split a flat list into `n`-element chunks; a remainder that is not a whole chunk is DROPPED, and
`openingWireOk` then refuses the short round list rather than deriving on it. -/
def chunk (n : Nat) (xs : List Nat) : List (List Nat) := chunkAux n (xs.length + 1) xs

/-- Render the answer. -/
def renderChallenges (p1 : Phase1) (ic : IpaChallenges) : String :=
  "b=" ++ toString p1.beta ++ ";g=" ++ toString p1.gamma ++ ";a=" ++ toString p1.alphaChal
    ++ ";z=" ++ toString p1.zetaChal ++ ";fq=" ++ toString p1.fqDigest
    ++ ";t=" ++ toString ic.t ++ ";c=" ++ toString ic.cPre
    ++ ";ch=" ++ String.intercalate "," (ic.prechals.map toString)

/-- A fully parsed wire — the ten fields, still flat. -/
structure ChallengeWire where
  /-- `vk` — the verifier-index digest. ⚑ TRUSTED CONFIG. -/
  vk : Nat
  /-- `er` — the Pallas `endo_r`. CONFIG. -/
  er : Nat
  /-- `pc` — the 2 accumulator commitments, flat. -/
  pc : List Nat
  /-- `pu` — `public_comm`'s (x, y). ⚑ The one argument that is not decodable. -/
  pu : List Nat
  /-- `wc` — the 15 witness commitments, flat. -/
  wc : List Nat
  /-- `zc` — `z_comm`'s (x, y). -/
  zc : List Nat
  /-- `tc` — the 7 `t_comm` chunks, flat. -/
  tc : List Nat
  /-- `cs` — `shift_scalar(combined_inner_product)`. ⚑ `expand_deferred`'s output. -/
  cs : Nat
  /-- `lr` — the opening's 15 rounds, FLAT (60 numbers). Re-chunked by [`absorbedOf`]. -/
  lr : List Nat
  /-- `dl` — `delta`'s (x, y). -/
  dl : List Nat
deriving Repr, DecidableEq

/-- **`parseChallengeWire`** — the WHOLE parse, as ONE function of the split parts.

⚑ Factored out for a proof obligation rather than for taste: see
`challengesGate_is_the_derivation`. -/
def parseChallengeWire (parts : List String) : Option ChallengeWire :=
  match parts with
  | [v, e, pc, pu, wc, zc, tc, cs, lr, dl] =>
      match (parseField? "vk" v).bind String.toNat?,
            (parseField? "er" e).bind String.toNat?,
            (parseField? "pc" pc).bind parseNats?,
            (parseField? "pu" pu).bind parseNats?,
            (parseField? "wc" wc).bind parseNats?,
            (parseField? "zc" zc).bind parseNats?,
            (parseField? "tc" tc).bind parseNats?,
            (parseField? "cs" cs).bind String.toNat?,
            (parseField? "lr" lr).bind parseNats?,
            (parseField? "dl" dl).bind parseNats? with
      | some vk, some er, some pcv, some puv, some wcv, some zcv, some tcv,
        some csv, some lrv, some dlv =>
          some { vk, er, pc := pcv, pu := puv, wc := wcv, zc := zcv, tc := tcv,
                 cs := csv, lr := lrv, dl := dlv }
      | _, _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- The absorbed objects a parsed wire describes. ⚑ The flat `lr` is re-chunked HERE, not by the
caller: a caller that chunks is a caller that can mis-chunk, and `openingWireOk` then refuses a short
round list rather than deriving fifteen challenges from fourteen rounds. -/
def absorbedOf (W : ChallengeWire) : WrapAbsorbed :=
  { vkDigest := W.vk, prevComm := W.pc, pubComm := W.pu, wComm := W.wc, zComm := W.zc,
    tComm := W.tc, cipShifted := W.cs, lr := chunk 4 W.lr, delta := W.dl, endoR := W.er }

/-- The derivation on a parsed wire, rendered. Nothing else in this file decides. -/
def renderFromWire (W : ChallengeWire) : String :=
  match deriveWrapChallenges (absorbedOf W) with
  | some (p1, ic) => renderChallenges p1 ic
  | none => "ERR"

/-- **`minaWrapChallengesGate`** — THE GATE. One scrutinee; every refusal is inside the parse or
inside `deriveWrapChallenges`' shape gate. -/
def minaWrapChallengesGate (s : String) : String :=
  match parseChallengeWire (s.splitOn ";") with
  | some W => renderFromWire W
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_wrap_challenges]`. Rust decodes binprot to numbers and
hands them over; the ARCHIVE runs the transcript. There is no Rust sponge to drift. -/
@[export dregg_mina_wrap_challenges]
def dregg_mina_wrap_challenges (s : String) : String := minaWrapChallengesGate s

/-- **The gate string IS `renderFromWire` of the parse** — the string layer adds no arm.

⚑ One scrutinee, one rewrite. A gate that matched on the ten parts and then again on ten parsed
fields cannot be welded in a rewrite at all: the outer matcher does not iota-reduce, so the inner
scrutinees stay buried and the second rewrite finds nothing. That is why the parse is a separate
function, and it is the shape `MinaForkChoiceGate.minaBetterTipGate_eq_decision` uses. -/
theorem challengesGate_is_the_derivation (s : String) (W : ChallengeWire)
    (hp : parseChallengeWire (s.splitOn ";") = some W) :
    minaWrapChallengesGate s = renderFromWire W := by
  unfold minaWrapChallengesGate
  rw [hp]

/-- …and `renderFromWire` IS `deriveWrapChallenges`, rendered — with the flat `lr` re-chunked HERE
rather than by a caller, because a caller that chunks is a caller that can mis-chunk.

Chained with the theorem above: the exported symbol runs `deriveWrapChallenges` on
`absorbedOf` the parse and nothing else, so §3's shape refusals are refusals of the thing Rust
actually calls. -/
theorem renderFromWire_is_deriveWrapChallenges (W : ChallengeWire) :
    renderFromWire W =
      (match deriveWrapChallenges (absorbedOf W) with
       | some (p1, ic) => renderChallenges p1 ic
       | none => "ERR") := rfl

/-- The re-chunking really is the gate's, and it is the `lr` field that feeds it. -/
theorem absorbedOf_chunks_the_flat_lr (W : ChallengeWire) :
    (absorbedOf W).lr = chunk 4 W.lr ∧ (absorbedOf W).pubComm = W.pu
    ∧ (absorbedOf W).cipShifted = W.cs := ⟨rfl, rfl, rfl⟩

/-! ### §4b — the wire REFUSES. Compiled, milliseconds. -/

#guard minaWrapChallengesGate "" == "ERR"
#guard minaWrapChallengesGate "garbage" == "ERR"
-- a short field list
#guard minaWrapChallengesGate "vk=1;er=1;pc=;pu=;wc=;zc=;tc=;cs=1;lr=" == "ERR"
-- a full-arity wire whose tape is the WRONG SHAPE: refused, not derived on
#guard minaWrapChallengesGate "vk=1;er=1;pc=1,2;pu=1,2;wc=1;zc=1,2;tc=1;cs=1;lr=1;dl=1,2" == "ERR"
-- a non-numeric coordinate
#guard minaWrapChallengesGate "vk=1;er=1;pc=x;pu=1,2;wc=1;zc=1,2;tc=1;cs=1;lr=1;dl=1,2" == "ERR"
-- a key in the wrong position
#guard minaWrapChallengesGate "er=1;vk=1;pc=;pu=;wc=;zc=;tc=;cs=1;lr=;dl=" == "ERR"

/-- `chunk` really chunks, and a short tail is dropped rather than padded — which is what makes
`openingWireOk`'s length check the refusal rather than a silent 14-round derivation. -/
theorem chunk_is_exact :
    chunk 4 [1, 2, 3, 4, 5, 6, 7, 8] = [[1, 2, 3, 4], [5, 6, 7, 8]]
    ∧ chunk 4 [1, 2, 3, 4, 5] = [[1, 2, 3, 4]]
    ∧ chunk 4 ([] : List Nat) = [] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5 — axiom hygiene. -/

#assert_axioms phase1_shape_discriminates
#assert_axioms opening_shape_discriminates
#assert_axioms chunk_is_exact
#assert_axioms challengesGate_is_the_derivation
#assert_axioms renderFromWire_is_deriveWrapChallenges
#assert_axioms absorbedOf_chunks_the_flat_lr

#print axioms phase1_shape_discriminates
#print axioms challengesGate_is_the_derivation

end Dregg2.Bridge.MinaWrapChallenges
