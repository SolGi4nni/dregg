/-
# Dregg2.Bridge.PicklesProofChainGate — the RUNTIME-CALLABLE **proof↔proof** chain gate,
`@[export] dregg_mina_proof_chain_ok`: block N's Pickles Wrap proof must NAME block N−1's
Pickles Wrap proof.

## The hole this is aimed at, and the exact part of it that closes

`bridge/src/mina_observer.rs` reached 2026-07-29 doing a great deal per block — the Lean finality
gate's decision, depth witnessed, Base58Check state-hash decode and canonicality, parent linkage
and height contiguity over decoded field elements, and a byte-exact `Mina_base.Proof.Stable.V2`
decode feeding `dregg_mina_wrap_shape_ok` — and **all of it could be satisfied with a proof that
belongs to a different block**. Its own header named the residual:

> the proof↔block BINDING — NOT CHECKED. ⚑ A Wrap proof is not self-binding to its block.

That is true and it stays true. A Wrap proof's `messages_for_next_step_proof.app_state` is
literally `()` on the wire (`bridge/src/mina_pickles.rs`, the `r.unit()?` at that field), and the
block enters only through the **verifier-supplied** `app_state`: openmina's `verify_block`
overwrites the wire `()` with `MinaHash::hash(&protocol_state)`, hashes
`index_to_field_elements(dlog_plonk_index) ++ [state_hash] ++ accumulators` into ONE Poseidon
digest, and that digest is **public-input slot 12 of 40**
(`crates/ledger/src/proofs/public_input/prepared_statement.rs`, `to_public_input`). Slot 12 is the
ONLY block-dependent slot; the other 39 are functions of the proof alone. So the state-hash binding
is not a comparison anyone can make — it is a conjunct of the full Wrap verification, and reaching
it needs the six wire-DROPPED public-input words (`combined_inner_product`, `b`,
`zeta_to_srs_length`, `zeta_to_domain_size`, `perm`, `xi`), i.e. `expand_deferred`, plus a 40-point
MSM and two sponges. `docs/MINA-REAL-BLOCK-GATE.md` §6 is where that lives; it is NOT here.

**What IS here is the other binding, and nothing in this tree had it.** Pickles recursion makes
block N's *Step* proof verify block N−1's *Wrap* proof, so block N's proof carries, in its own
bytes, an accumulator FOR that verification — and that accumulator is block N−1's own IPA
commitment. Two independent fingerprints of the parent's proof are therefore sitting in the child's
proof, in the clear, comparable with no arithmetic at all:

  * `statement.messages_for_next_step_proof.challenge_polynomial_commitments[0]`
    **=** the parent's `bulletproof.challenge_polynomial_commitment` (`sg`), and
  * `statement.messages_for_next_step_proof.old_bulletproof_challenges[0]`
    **=** the parent's `statement.proof_state.deferred_values.bulletproof_challenges` (16).

## MEASURED, on real chain data — not inferred from the type

40 consecutive Mina **devnet** blocks (539761…539800), fetched 2026-07-29 from
`api.minascan.io/node/devnet/v1/graphql`, giving 39 adjacent pairs:

| observation | result |
|---|---|
| `child.acc0 = parent.sg` | **39 / 39** |
| `child.acc0Challenges = parent.bpChallenges` | **39 / 39** |
| distinct `sg` across the 40 blocks | **40 / 40** — no proof is served twice |
| self-naming blocks (`acc0 = sg`) | **0 / 40** |
| NON-adjacent coincidences (`b.acc0 = a.sg`, `|i−j| ≠ 1`) | **0** |

Five of those blocks (539795…539799) are tracked at
`metatheory/fixtures/pickles-extractors/mina_devnet_run.json`, and §2 pins three of them here as
literal constants. The single-block fixture could not have exhibited this: one block has no parent
proof to name.

## EXPORTED + PROVEN vs TRUSTED vs NOT CLOSED — say it plainly

  * EXPORTED + PROVEN (this gate): the child's exhibited parent-accumulator IS the parent's `sg`,
    the child's exhibited parent-challenges ARE the parent's own 16, both challenge vectors have
    length 16, and the accumulator is not the degenerate `(0,0)` (which is not on `y² = x³ + 5`,
    so it is never a real `sg`; it is what `prev_challenges = 0` decodes to). Over that,
    `chainOk_adjacent_proofs_differ` proves the anti-replay property: **an accepted segment cannot
    serve the same proof twice in a row**, and `chainOk_pins_every_seam` proves every ADJACENCY is
    checked, not just the first — accepted runs cannot be spliced, shuffled or padded.
  * TRUSTED, and named: that `acc0` is the BLOCKCHAIN parent's accumulator rather than the
    transaction SNARK's. That is index `[0]` of a 2-element vector and it is an empirical
    reading of the 39 pairs above, not a theorem about Pickles. Index `[1]` is deliberately not
    projected — it took only 4 distinct values over the measured 40 blocks, so it carries no
    positional information.
  * **NOT CLOSED, and this gate must never be described as closing it**: the proof↔`stateHash`
    binding. This gate ties a proof to its POSITION IN THE PROOF CHAIN, not to a header. An
    adversary holding a genuine consecutive run of real Mina proofs can still re-label the headers
    those proofs are served under, because a `stateHash` is a freely-mintable Base58 string and
    nothing here reaches slot 12. What it costs the adversary is everything cheaper than that: one
    real proof replayed under 290 fabricated headers is refused, a shuffled run is refused, a
    spliced run is refused, a padded run is refused, and depth beyond the real chain's own
    production is refused.
  * NOT A MINA LIGHT CLIENT, still. Fork choice is formalized NOWHERE in this tree, and a sibling
    proved Samasika `select` is a TOURNAMENT rather than an order (genuine 3-cycles at real
    mainnet constants), so a chain follower needs strictly more than a better binding.
-/
import Dregg2.Circuit.Emit.KimchiVerify

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Dregg2.Bridge.PicklesProofChainGate

/-! ## §1 — THE DECISION. -/

/-- **One block's chain-relevant projection of its Wrap proof.** Every field is a value the Rust
codec reads straight out of `Mina_base.Proof.Stable.V2` with no arithmetic
(`bridge/src/mina_pickles.rs`, `WrapProofShape`'s chain projection).

`sgX`/`sgY`/`bpCh` describe THIS proof; `accX`/`accY`/`accCh` are what this proof SAYS about its
parent's proof. A chain link compares the second triple of the child against the first of the
parent. -/
structure Link where
  /-- `messages_for_next_step_proof.challenge_polynomial_commitments[0].x` — the parent's
  claimed accumulator. -/
  accX : Nat
  /-- …`.y`. -/
  accY : Nat
  /-- `messages_for_next_step_proof.old_bulletproof_challenges[0]` — the parent's claimed 16 IPA
  challenges, as the 128-bit wire values. -/
  accCh : List Nat
  /-- `bulletproof.challenge_polynomial_commitment.x` — THIS proof's own accumulator. -/
  sgX : Nat
  /-- …`.y`. -/
  sgY : Nat
  /-- `statement.proof_state.deferred_values.bulletproof_challenges` — THIS proof's own 16. -/
  bpCh : List Nat
deriving Repr, DecidableEq

/-- Pickles' IPA round count on the Wrap side, `log₂ max_poly_size = 15`… but the STEP-side
challenge vectors a Wrap proof carries are `Backend.Tick.Rounds.n = 16`
(`kimchi_pasta_basic.ml:17`, `module Step = Nat.N16`). Both `accCh` and `bpCh` are Step-side. -/
def STEP_ROUNDS : Nat := 16

/-- **`selfNaming`** — a proof that claims ITS OWN accumulator as its parent's. No real Mina block
does this (0 of the 40 measured), and it is exactly the degenerate shape that would let one proof
stand in for a whole segment. -/
def selfNaming (b : Link) : Bool :=
  decide (b.accX = b.sgX) && decide (b.accY = b.sgY)

/-- **`accumulatorPresent`** — the exhibited parent-accumulator is not the degenerate `(0, 0)`.

`(0, 0)` is NOT on `y² = x³ + 5` (`0 ≠ 5`), so it is never a real Pallas `sg`; it is what a proof
carrying NO accumulator (`prev_challenges = 0`) decodes to, and admitting it would let a proof with
no recursion claim any parent. Refusing it here is the same posture as refusing an absent
`protocolStateProof` rather than treating it as neutral. -/
def accumulatorPresent (b : Link) : Bool :=
  !(decide (b.accX = 0) && decide (b.accY = 0))

/-- **`linkOk parent child`** — THE DECISION for one adjacent pair: the child's proof names the
parent's proof, on both fingerprints, at the right arity, non-degenerately. -/
def linkOk (parent child : Link) : Bool :=
  accumulatorPresent child
  && decide (child.accCh.length = STEP_ROUNDS)
  && decide (parent.bpCh.length = STEP_ROUNDS)
  && decide (child.accX = parent.sgX)
  && decide (child.accY = parent.sgY)
  && decide (child.accCh = parent.bpCh)

/-- **`chainOk`** — the whole exhibited segment chains, oldest-first (the order real Mina
`bestChain` returns). A segment of 0 or 1 blocks has no adjacent pair and so imposes nothing;
that is honest rather than convenient, and it is why the observer's depth conjunct — not this one —
is what makes a one-block segment useless. -/
def chainOk : List Link → Bool
  | [] => true
  | [_] => true
  | p :: c :: rest => linkOk p c && chainOk (c :: rest)

@[simp] theorem chainOk_nil : chainOk [] = true := rfl
@[simp] theorem chainOk_single (b : Link) : chainOk [b] = true := rfl
@[simp] theorem chainOk_cons₂ (p c : Link) (rest : List Link) :
    chainOk (p :: c :: rest) = (linkOk p c && chainOk (c :: rest)) := rfl

/-! ## §2 — WHAT AN ACCEPT ENTAILS. These are the theorems that make the gate worth deploying;
without them `chainOk` is an equality test with a nice name. -/

/-- An accepted link entails BOTH coordinate agreements and the challenge-vector agreement. -/
theorem linkOk_entails {p c : Link} (h : linkOk p c = true) :
    c.accX = p.sgX ∧ c.accY = p.sgY ∧ c.accCh = p.bpCh := by
  unfold linkOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-- ⚑ **THE ANTI-REPLAY THEOREM.** In an accepted segment, **two adjacent blocks cannot exhibit
the same proof.** This is the property the old observer lacked entirely: before this gate, ONE real
Mina proof served under every header in a 290-block window satisfied every check, so the
"availability obligation" the `NEUTRAL_PICKLES_OK` retirement claimed to buy cost an adversary one
proof rather than a chain.

The side condition is `selfNaming c = false`, and it is not a smuggled assumption: it is a
DECIDABLE property of the exhibited child, checked on real blocks in §3
(`real_devnet_blocks_are_not_self_naming`) and false on 0 of the 40 measured. -/
theorem chainOk_adjacent_proofs_differ {p c : Link} {rest : List Link}
    (hchain : chainOk (p :: c :: rest) = true) (hself : selfNaming c = false) :
    ¬ (p.sgX = c.sgX ∧ p.sgY = c.sgY) := by
  rw [chainOk_cons₂, Bool.and_eq_true] at hchain
  obtain ⟨hx, hy, _⟩ := linkOk_entails hchain.1
  rintro ⟨hsx, hsy⟩
  have hs : selfNaming c = true := by
    simp only [selfNaming, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by rw [hx, hsx], by rw [hy, hsy]⟩
  rw [hs] at hself
  exact Bool.noConfusion hself

/-- The leading pair of an accepted chain links. -/
theorem chainOk_head_link {p c : Link} {rest : List Link}
    (h : chainOk (p :: c :: rest) = true) : linkOk p c = true := by
  rw [chainOk_cons₂, Bool.and_eq_true] at h
  exact h.1

/-- Dropping the oldest block of an accepted chain leaves an accepted chain. -/
theorem chainOk_tail : ∀ {b : Link} {rest : List Link},
    chainOk (b :: rest) = true → chainOk rest = true
  | _, [], _ => rfl
  | _, (_ :: _), h => by rw [chainOk_cons₂, Bool.and_eq_true] at h; exact h.2

/-- …hence EVERY suffix of an accepted chain is accepted. -/
theorem chainOk_drop : ∀ (n : Nat) (L : List Link), chainOk L = true → chainOk (L.drop n) = true
  | 0, _, h => h
  | (_ + 1), [], _ => by rw [List.drop_nil]; exact chainOk_nil
  | (n + 1), (_ :: rest), h => by
      rw [List.drop_succ_cons]
      exact chainOk_drop n rest (chainOk_tail h)

/-- ⚑ **EVERY SEAM IS PINNED**, not merely the first: wherever an accepted segment continues, the
pair at that position links. So an adversary cannot splice two genuine runs, reorder within a run,
or pad one out — every adjacency is a link and every link is checked. -/
theorem chainOk_pins_every_seam {L : List Link} (h : chainOk L = true) (i : Nat)
    {p c : Link} {rest : List Link} (hd : L.drop i = p :: c :: rest) : linkOk p c = true := by
  have hs := chainOk_drop i L h
  rw [hd] at hs
  exact chainOk_head_link hs

/-- A chain accepts only if EVERY adjacent pair links — the contrapositive an observer relies on
when it reports which block broke the segment. -/
theorem chainOk_cons₂_of_false {p c : Link} {rest : List Link} (h : linkOk p c = false) :
    chainOk (p :: c :: rest) = false := by
  rw [chainOk_cons₂, h, Bool.false_and]

/-! ## §3 — REAL MINA DEVNET BLOCKS. Three consecutive blocks of the tracked run
`metatheory/fixtures/pickles-extractors/mina_devnet_run.json`, decoded to these literals by TWO
independent walkers (the Rust codec `bridge/src/mina_pickles.rs`, which asserts these exact values
in `real_devnet_run_exhibits_the_proof_chain`, and the extraction script that produced this file).
A drift in either is a red test, not a silent disagreement about what a Mina proof IS. -/

/-- Devnet block **539795**. -/
def B539795 : Link where
  accX := 11428410925816913506610365860092154004855637921793254932591368414556882648254
  accY := 4763307846681476580388639909966025348170173933965675324385559297959462521252
  accCh := [72035921323571512916077457375741685595, 70208905622944468829208587440908917952,
            128423915032176163227286680535572298443, 60307147527997906074090829997486060048,
            47427900930106613881914910852640650788, 212066282300975204951671900950049771340,
            221034287805541814397569009134438006286, 28533581682042071345398400404410129104,
            225783681514268135183386861673032037936, 8059697744431276760855356154918365459,
            34922868815133029035679508065472543754, 315466395016599930024873672786234398949,
            200962057504958373910217963667978084832, 235984974881241479573414236738719739240,
            157445681758695605881418904098631215257, 178614061432052759196470873114782525615]
  sgX := 20146518149961985083673632976085115247649480898755654722356774610313624222264
  sgY := 7490304815649096610077713774932066967911710097704988014691714322967665756103
  bpCh := [9627185902892173217607580080386729855, 4336098561175419728789413467860630307,
           92712709370329007486562287305031997120, 259011311049670554039999068426516291802,
           64085316469983503205716610340294791808, 50262037354679539067254785062838888456,
           255544403595366803630794858863976489939, 322001635536632271294811674249056689130,
           239998343012664096881391723926646336170, 19491843453295450690246656237994500068,
           254416156163485583432104943834491129192, 13613896410212618218738646906287963034,
           287016089930776834738046343907049385485, 17647175520905721394314026247819769641,
           220138837492712180477929380327098558484, 146811381677834959262438491317330758493]

/-- Devnet block **539796** — its `acc*` is 539795's `sg*`/`bpCh`, and that is the whole point. -/
def B539796 : Link where
  accX := 20146518149961985083673632976085115247649480898755654722356774610313624222264
  accY := 7490304815649096610077713774932066967911710097704988014691714322967665756103
  accCh := [9627185902892173217607580080386729855, 4336098561175419728789413467860630307,
            92712709370329007486562287305031997120, 259011311049670554039999068426516291802,
            64085316469983503205716610340294791808, 50262037354679539067254785062838888456,
            255544403595366803630794858863976489939, 322001635536632271294811674249056689130,
            239998343012664096881391723926646336170, 19491843453295450690246656237994500068,
            254416156163485583432104943834491129192, 13613896410212618218738646906287963034,
            287016089930776834738046343907049385485, 17647175520905721394314026247819769641,
            220138837492712180477929380327098558484, 146811381677834959262438491317330758493]
  sgX := 15310153193890092743508059921596149565213446588665909599267615499973707681130
  sgY := 28199024049865301389474973869834450019135650980849302435293961358196141658551
  bpCh := [218408055290985145035903112101508395330, 173272506522728021047382451043160777770,
           242683543404286643457150975991045900005, 62962806683991597199240562810424825673,
           202855740216409035634178087791461168948, 732419042995166788159606010198805622,
           307874814180303625140683707145617177834, 23529655796675242103062506363797202672,
           123256198687754012600973618305412465381, 303884097646606962784560645628423447981,
           122541025159812342585552781856224017043, 318611922742627522294656133428809911017,
           15983100416965294025729602521951901562, 153968350262947823467990674825197229598,
           176152078218848751822303740817650696127, 362382648079139906461794051506333902]

/-- Devnet block **539797**. -/
def B539797 : Link where
  accX := 15310153193890092743508059921596149565213446588665909599267615499973707681130
  accY := 28199024049865301389474973869834450019135650980849302435293961358196141658551
  accCh := [218408055290985145035903112101508395330, 173272506522728021047382451043160777770,
            242683543404286643457150975991045900005, 62962806683991597199240562810424825673,
            202855740216409035634178087791461168948, 732419042995166788159606010198805622,
            307874814180303625140683707145617177834, 23529655796675242103062506363797202672,
            123256198687754012600973618305412465381, 303884097646606962784560645628423447981,
            122541025159812342585552781856224017043, 318611922742627522294656133428809911017,
            15983100416965294025729602521951901562, 153968350262947823467990674825197229598,
            176152078218848751822303740817650696127, 362382648079139906461794051506333902]
  sgX := 14872446649294467362168055103889119102732875308817333203618322337998985212663
  sgY := 2913186664279928827956749453688381383681572417952207572483920913979540149404
  bpCh := [18128915500100521226769975132484580475, 144190848018661517131426675480520894525,
           134365929751870975225564441718044638177, 329733121463903039422352458175631499117,
           78338990297044125358187278038723409092, 149720653364845929253325095473894477742,
           31961434761677191185005199560269370700, 95169307984986661433630500709615392836,
           320057381095587026097275635980688678749, 76487137139668246394941707945769942779,
           265930622788020649839175589111221631812, 141490827599485134313658283814663394867,
           235859558020460774389353837035548945855, 26793711490542955804270245091380734583,
           321169620687307709922505505256135679219, 326383075325966786852965853867407778797]

/-- ⚑ **THE ACCEPT.** The genuine consecutive devnet run 539795→539796→539797 CHAINS. -/
theorem real_devnet_run_chains : chainOk [B539795, B539796, B539797] = true := by decide

/-- ⚑ The anti-replay side condition HOLDS on real data: no measured block names its own
accumulator as its parent's. Without this the theorem above is compatible with a chain of clones. -/
theorem real_devnet_blocks_are_not_self_naming :
    selfNaming B539795 = false ∧ selfNaming B539796 = false ∧ selfNaming B539797 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE FALSIFIER FAMILY**, on real bytes. Every way an endpoint can serve real Mina proofs
under the wrong headers is REFUSED. Without this block the accept above is compatible with a
decision that accepts everything. -/
theorem real_devnet_chain_discriminates :
    -- the genuine run
    chainOk [B539795, B539796, B539797] = true
    -- ⚑ REPLAY: one real proof served for every block of the segment
    ∧ chainOk [B539795, B539795] = false
    ∧ chainOk [B539796, B539796] = false
    -- ⚑ SWAP: a real proof from the wrong height, i.e. block A's proof under block B's header
    ∧ chainOk [B539795, B539797] = false
    -- ⚑ REORDER: the same real proofs, permuted
    ∧ chainOk [B539796, B539795] = false
    ∧ chainOk [B539797, B539796, B539795] = false
    -- ⚑ SPLICE: a genuine link followed by a fabricated seam
    ∧ chainOk [B539795, B539796, B539795] = false
    -- a one-coordinate tamper of the exhibited accumulator
    ∧ chainOk [B539795, { B539796 with accX := B539796.accX + 1 }] = false
    ∧ chainOk [B539795, { B539796 with accY := B539796.accY + 1 }] = false
    -- a one-entry tamper of the exhibited challenge vector
    ∧ chainOk [B539795, { B539796 with accCh := B539796.accCh.set 0 0 }] = false
    ∧ chainOk [B539795, { B539796 with accCh := B539796.accCh.set 15 0 }] = false
    -- a short / long challenge vector (the arity conjunct)
    ∧ chainOk [B539795, { B539796 with accCh := B539796.accCh.take 15 }] = false
    ∧ chainOk [B539795, { B539796 with accCh := B539796.accCh ++ [0] }] = false
    -- ⚑ the DEGENERATE accumulator a `prev_challenges = 0` proof decodes to
    ∧ chainOk [B539795, { B539796 with accX := 0, accY := 0 }] = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- And the anti-replay theorem INSTANTIATED on the real object, so the general statement is known
to have a nonempty premise: 539795's and 539796's proofs are genuinely different proofs. -/
theorem real_devnet_adjacent_proofs_differ :
    ¬ (B539795.sgX = B539796.sgX ∧ B539795.sgY = B539796.sgY) :=
  chainOk_adjacent_proofs_differ
    (rest := []) (by decide) real_devnet_blocks_are_not_self_naming.2.1

/-! ## §4 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as
`dregg_mina_wrap_shape_ok`. Fail-closed on any malformed wire (`"ERR"` ⇒ the caller treats it as
REJECT). One call per ADJACENT PAIR, so an `n`-block segment costs `n − 1` calls. -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a `,`-separated `Nat` list, fail-closed on any non-numeral. The EMPTY string is `none`,
not `some []`: an absent challenge vector must not read as a well-formed empty one. -/
def parseNats? (s : String) : Option (List Nat) :=
  match s.splitOn "," with
  | [] => none
  | parts => parts.foldr (fun p acc => do
      let rest ← acc
      let n ← p.toNat?
      pure (n :: rest)) (some [])

/-- **`decodeChainWire`** — parse the `INPUT` grammar into the parent's own fingerprint and the
child's claim about it. Fail-closed (`none`) on any deviation.

```
INPUT := "px=" Nat ";py=" Nat ";pc=" Nat("," Nat)*
       ";cx=" Nat ";cy=" Nat ";cc=" Nat("," Nat)*
```
(`px`/`py`/`pc` = the PARENT block's own `sg` and its 16 IPA challenges; `cx`/`cy`/`cc` = the CHILD
block's exhibited parent-accumulator and parent-challenges.) -/
def decodeChainWire (s : String) : Option (Link × Link) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5] => do
      let px ← (parseField? "px" p0).bind String.toNat?
      let py ← (parseField? "py" p1).bind String.toNat?
      let pc ← (parseField? "pc" p2).bind parseNats?
      let cx ← (parseField? "cx" p3).bind String.toNat?
      let cy ← (parseField? "cy" p4).bind String.toNat?
      let cc ← (parseField? "cc" p5).bind parseNats?
      -- The parent contributes only `sg*`/`bpCh` and the child only `acc*`/`accCh`; the unused
      -- halves are zeroed rather than mirrored, so a wire cannot smuggle a value into the side
      -- of the comparison it does not belong to.
      some ({ accX := 0, accY := 0, accCh := [], sgX := px, sgY := py, bpCh := pc },
            { accX := cx, accY := cy, accCh := cc, sgX := 0, sgY := 0, bpCh := [] })
  | _ => none

/-- **`minaProofChainGate`** — THE GATE. Decode the wire, run `linkOk`, encode `"1"` (ACCEPT) /
`"0"` (REJECT). A malformed wire returns `"ERR"` (fail-closed: the caller treats it as REJECT). -/
def minaProofChainGate (s : String) : String :=
  match decodeChainWire s with
  | some (p, c) => if linkOk p c then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_proof_chain_ok]` — the C-ABI entry `dregg-lean-ffi` calls
once per adjacent pair of exhibited blocks. -/
@[export dregg_mina_proof_chain_ok]
def dregg_mina_proof_chain_ok (s : String) : String := minaProofChainGate s

/-- **`minaProofChainGate_eq_decision`** — the gate string IS the decision, by construction. -/
theorem minaProofChainGate_eq_decision (s : String) (p c : Link)
    (hd : decodeChainWire s = some (p, c)) :
    minaProofChainGate s = (if linkOk p c then "1" else "0") := by
  unfold minaProofChainGate
  rw [hd]

/-! ## §5 — NON-VACUITY at the wire, in the interpreter (the STRING layer uses well-founded
recursion the kernel cannot reduce under `decide`; `minaProofChainGate_eq_decision` ties the string
surface to the decision §2/§3 prove about). The numbers below are the REAL 539795→539796 pair. -/

/-- The real adjacent pair's wire, built here so the `#guard`s below and the Rust wire builder
(`dregg-lean-ffi`'s `mina_proof_chain_wire`) are checkable against one another. -/
def REAL_WIRE : String :=
  "px=20146518149961985083673632976085115247649480898755654722356774610313624222264;" ++
  "py=7490304815649096610077713774932066967911710097704988014691714322967665756103;" ++
  "pc=9627185902892173217607580080386729855,4336098561175419728789413467860630307," ++
  "92712709370329007486562287305031997120,259011311049670554039999068426516291802," ++
  "64085316469983503205716610340294791808,50262037354679539067254785062838888456," ++
  "255544403595366803630794858863976489939,322001635536632271294811674249056689130," ++
  "239998343012664096881391723926646336170,19491843453295450690246656237994500068," ++
  "254416156163485583432104943834491129192,13613896410212618218738646906287963034," ++
  "287016089930776834738046343907049385485,17647175520905721394314026247819769641," ++
  "220138837492712180477929380327098558484,146811381677834959262438491317330758493;" ++
  "cx=20146518149961985083673632976085115247649480898755654722356774610313624222264;" ++
  "cy=7490304815649096610077713774932066967911710097704988014691714322967665756103;" ++
  "cc=9627185902892173217607580080386729855,4336098561175419728789413467860630307," ++
  "92712709370329007486562287305031997120,259011311049670554039999068426516291802," ++
  "64085316469983503205716610340294791808,50262037354679539067254785062838888456," ++
  "255544403595366803630794858863976489939,322001635536632271294811674249056689130," ++
  "239998343012664096881391723926646336170,19491843453295450690246656237994500068," ++
  "254416156163485583432104943834491129192,13613896410212618218738646906287963034," ++
  "287016089930776834738046343907049385485,17647175520905721394314026247819769641," ++
  "220138837492712180477929380327098558484,146811381677834959262438491317330758493"

-- ⚑ The REAL adjacent devnet pair 539795→539796 ACCEPTS at the wire.
#guard minaProofChainGate REAL_WIRE == "1"
-- ⚑ …and the wire really is the pair §3 pins, not a lookalike.
#guard (decodeChainWire REAL_WIRE).map (fun pc =>
          pc.1.sgX == B539795.sgX && pc.1.sgY == B539795.sgY && pc.1.bpCh == B539795.bpCh
          && pc.2.accX == B539796.accX && pc.2.accY == B539796.accY
          && pc.2.accCh == B539796.accCh) == some true
-- ⚑ One digit changed in the parent's accumulator x REFUSES.
#guard minaProofChainGate (REAL_WIRE.replace "px=201465181" "px=201465182") == "0"
-- ⚑ One digit changed in the child's claimed accumulator y REFUSES.
#guard minaProofChainGate (REAL_WIRE.replace "cy=749030481" "cy=749030482") == "0"
-- ⚑ One entry changed in the child's claimed challenge vector REFUSES.
#guard minaProofChainGate (REAL_WIRE.replace "cc=9627185902892173217607580080386729855"
                                            "cc=9627185902892173217607580080386729854") == "0"
-- A degenerate `(0,0)` accumulator REFUSES (`prev_challenges = 0`).
#guard minaProofChainGate "px=1;py=2;pc=1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16;cx=0;cy=0;\
cc=1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16" == "0"
-- A short challenge vector REFUSES (15 entries, not 16).
#guard minaProofChainGate "px=1;py=2;pc=1,2,3,4,5,6,7,8,9,10,11,12,13,14,15;cx=1;cy=2;\
cc=1,2,3,4,5,6,7,8,9,10,11,12,13,14,15" == "0"
-- A minimal well-formed ACCEPT, so the `#guard`s above are not all one polarity.
#guard minaProofChainGate "px=7;py=9;pc=1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16;cx=7;cy=9;\
cc=1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16" == "1"
-- A malformed wire is `"ERR"`, never an accept: a truncated field list, a wrong key, a
-- non-numeral in a list, and garbage.
#guard minaProofChainGate "px=1;py=2;pc=1;cx=1;cy=2" == "ERR"
#guard minaProofChainGate "qx=1;py=2;pc=1;cx=1;cy=2;cc=1" == "ERR"
#guard minaProofChainGate "px=1;py=2;pc=1,x;cx=1;cy=2;cc=1,2" == "ERR"
#guard minaProofChainGate "px=1;py=2;pc=;cx=1;cy=2;cc=" == "ERR"
#guard minaProofChainGate "garbage" == "ERR"
#guard minaProofChainGate "" == "ERR"

/-! ## §6 — axiom hygiene. -/

#assert_axioms linkOk_entails
#assert_axioms chainOk_adjacent_proofs_differ
#assert_axioms chainOk_head_link
#assert_axioms chainOk_tail
#assert_axioms chainOk_drop
#assert_axioms chainOk_pins_every_seam
#assert_axioms chainOk_cons₂_of_false
#assert_axioms real_devnet_run_chains
#assert_axioms real_devnet_blocks_are_not_self_naming
#assert_axioms real_devnet_chain_discriminates
#assert_axioms real_devnet_adjacent_proofs_differ
#assert_axioms minaProofChainGate_eq_decision

#print axioms real_devnet_chain_discriminates
#print axioms chainOk_adjacent_proofs_differ

end Dregg2.Bridge.PicklesProofChainGate
