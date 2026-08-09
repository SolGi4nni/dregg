import Dregg2.Games.MultiwayTug

/-!
# `Dregg2.Games.MultiwayTugFFI` — the RUNTIME-CALLABLE multiway-tug rules oracle

⚑ SUBSTRATE. The multiway-tug game semantics are **Lean-authored** (`Dregg2.Games.MultiwayTug`, the
proven pure-transition spec) and the deployed teeth are Lean-emitted
(`Dregg2.Games.MultiwayTugProgram`). This module adds NO semantics: it is a wire codec around the
existing spec functions plus the `@[export]` the deployed Rust surface calls, so
`dregg-multiway-tug` adjudicates a play BY CALLING THE PROVEN LEAN instead of by consulting a Rust
re-expression of the same rules.

## What this replaces, and why it is a repair rather than a refactor

`dregg-multiway-tug/src/reference.rs` is a SPEC-TWIN: 1000+ lines of Rust that re-decide, in Rust,
what `MultiwayTug.lean` proves. It is a different shape of twin from the one the twin-deletion sweep
hunted (`docs/TWIN-DELETION-MAP-2026-07-23.md` looked for twins of Lean **AIR**), which is exactly
why it survived that sweep — see `dregg-automatafl`'s sibling landing (`a1e4abb1dc`).

⚑ **AND THE TWIN HAD ALREADY DRIFTED.** `reference.rs::winner_of` is the model's `roundWinner`
TRUNCATED TO ITS FIRST FOUR BRANCHES: it tests the two absolute thresholds and then answers "no
winner". The model's `roundWinner` (§7B) continues — higher TOTAL CHARM, then higher ROW COUNT, and
only an exact dead heat is a draw. That tail is the fix that took the game's draw rate from 66.1% to
5.1%, and the Rust never had it. So on every round where neither seat clears the bar the two objects
give DIFFERENT answers, and the Lean model already carries the witness: `undecidedState`, with
`undecidedState_not_Won` (no threshold win) beside `undecidedState_adjudicates`
(`roundWinner = some .p1`). §5's teeth pin that pair, so a pass of this codec is evidence about WHICH
OBJECT ANSWERED, not merely that something answered.

## What this codec does NOT cover (the honest boundary)

`MultiwayTug.lean` models cards at **guild-row resolution** (`Geisha := Fin 7`, a hand is a
`Multiset Geisha`). It has no notion of a distinct card id, and no deal, shuffle or draw. So these
`reference.rs` responsibilities have NO Lean spec to route to and are NOT verbs below:

* the deal — 21 distinct ids, the Fisher-Yates shuffle from a seed, the one card removed face-down,
  the two 6-card openings;
* the per-action-turn draw and the choice-independent draw assignment (`round_inventory`);
* the id→row projection (`deck_guild`) and the id-level hand bookkeeping;
* the enumeration of legal decisions over concrete ids (only its RULES half is a verb — see `kinds`
  and `legalB_iff_kindOpen`, which factor the card-containment conjunct out of `legalB` so a Rust
  enumerator supplies combinatorics and NEVER a rule);
* `greedy_policy`, which is one example agent, not semantics.

## The wire (`String → String`), fail-closed

Single line, space-separated tokens, verb first. A malformed wire answers `"0"` — REFUSE. Every
success answers `"1"` followed by the verb's payload. No token is ever empty (an empty card zone is
written `-`).

```
CARDS  := digits in {0..6}, one per card, or `-` when the zone is empty
          (multiplicity is REPETITION; the encoder emits them grouped ascending, which is
           canonical because the model's zones are MULTISETS with no order to preserve)
USED   := 4 chars in {0,1}, in the ActionKind order  secret discard gift competition
PEND   := 0                        -- no offer on the table
        | 1 proposer c₀ c₁ c₂      -- a Gift in escrow
        | 2 proposer a₀ a₁ b₀ b₁   -- a Competition in escrow, ALREADY PAIRED
SEAT   := 0 (p1) | 1 (p2)
STATE  := removed deck hand₁ hand₂ secret₁ secret₂ disc₁ disc₂ placed₁ placed₂
          USED₁ USED₂ PEND SEAT turns          -- 10 CARDS, 2 USED, PEND, seat, turn stamp
ACTION := 0 c | 1 c c | 2 c c c | 3 c c c c    -- secret | discard | gift | comp, kind-tagged
RESP   := 0 pick | 1 pick                      -- gift (pick < 3) | comp (pick < 2)
```

Card digits are the guild rows themselves, the same `Geisha` index the emitted program's per-row
score keys are cut against (`MultiwayTugProgram`), so the oracle and the teeth speak one alphabet.
A digit outside `0..6`, or any non-digit, REFUSES — unlike the automatafl codec's cell alphabet
there is no "vacuum" card for an unknown glyph to mean, so fail-closed is the only faithful decode.

**Operand order: the STATE always comes first.** There is no size-dependency here as there is in the
automatafl codec, so this is uniformity rather than necessity — but `STATE` is the one operand whose
length varies (via `PEND`), it is self-delimiting, and putting it first keeps every grammar below
parseable in one left-to-right pass.

The `ActionKind` tag order `secret 0, discard 1, gift 2, competition 3` is the SAME order
`reference.rs::ActionKind::idx` cuts the eight used-flag heap keys against, so a caller marshals its
flags without a translation table.

### Verbs

| request                   | response                          | the model function that answers          |
|---------------------------|-----------------------------------|------------------------------------------|
| `charm`                   | `1 7 2 2 2 3 3 4 5`               | `charm` — the influence table            |
| `turns`                   | `1 12`                            | 8 actions + 4 responses                  |
| `legal STATE SEAT ACTION` | `1 0` / `1 1`                     | `legalB`                                 |
| `legalresp STATE SEAT RESP` | `1 0` / `1 1`                   | `legalRespB`                             |
| `kinds STATE SEAT`        | `1 k₀ k₁ k₂ k₃ resp`              | `kindOpen` / `respOpen` (see below)       |
| `split PEND RESP`         | `1 CARDS CARDS` (taker, cutter)   | `takerShare` / `cutterShare`             |
| `act STATE SEAT ACTION`   | `1 STATE`                         | `applyAction`                            |
| `respond STATE SEAT RESP` | `1 STATE`                         | `applyResponse`                          |
| `control STATE`           | `1 7 o₀ … o₆` (`0` none, `1`/`2`) | `control`                                |
| `count STATE SEAT g`      | `1 n`                             | `geishaCount` (the Secret IS scored)     |
| `score STATE`             | `1 charm₁ rows₁ charm₂ rows₂`     | `charmScore` / `geishaScore`             |
| `won STATE SEAT`          | `1 0` / `1 1`                     | `Won` (via the proven reflection `wonB`) |
| `winner STATE`            | `1 0` / `1 1` / `1 2`             | ⚑ `roundWinner` — `0` is a DRAW          |
| `branch STATE`            | `1 b w` (`b` in `0..8`)           | ⚑ `roundWinnerBranch` + its seat         |
| `total STATE`             | `1 CARDS`                         | `totalCards` — the conserved multiset    |

`kinds` answers the RULES half of "what may this seat do": `kᵏ = 1` iff action-kind `k` is open for
`SEAT` (`kindOpen`: the seat is to move, no offer is pending, the flag is unused), and `resp = 1` iff
a response by `SEAT` is open (`respOpen`: an offer is pending and `SEAT` is not the proposer). The
factorization is EXACT — `legalB_iff_kindOpen` proves `legalB` is `kindOpen` AND the card
containment, and `legalRespB_iff_respOpen` proves `legalRespB` is `respOpen` AND the shape match — so
a caller that filters kinds by this verb and then supplies only card combinatorics has not kept a
rule in Rust.

`winner`'s `0` means DRAW (an exact dead heat, `roundWinner_draw_iff`), NOT "unadjudicated". The
deleted Rust returned "no winner" for every sub-threshold round; this verb returns a seat there.

`branch` answers WHICH of `roundWinner`'s nine clauses fired, and the seat that clause names
(`winnerTok_branch_agrees`: the seat is the same one `winner` reports). It exists because the
DEPLOYED teeth need it: the tug constraint vocabulary has no register-vs-register comparison
inside a disjunction, so `MultiwayTugProgram` gives each clause its own transition case and a
scoring turn NAMES its clause. Without this verb the caller would have to re-derive the clause —
i.e. re-implement the precedence in Rust, which is the exact twin this module exists to delete.

## Faithfulness of the codec

Mirroring the automatafl codec: the ALPHABET-level inverse is a theorem (`cardOf?_digitOf`), and the
composite round-trips are pinned on real states — as named theorems in `MultiwayTugFFIFixtures.lean`
(§7) — rather than by a general `parse ∘ encode = id` induction. That is the same strength of claim,
said the same way.

## Import discipline

Imports only `Dregg2.Games.MultiwayTug`. The module sits OUTSIDE the `Dregg2.FFI` boundary closure
(like the automatafl oracle), so `lean_init.c` initializes it explicitly — `charm` and the §7
witness states read module globals, so its initializer must have run before the first call.
-/

namespace Dregg2.Games.MultiwayTugFFI

open Dregg2.Games.MultiwayTug

/-! ## §1 — tokens and the card alphabet -/

/-- Parse an unsigned decimal token. -/
@[inline] def natOf? (s : String) : Option Nat := s.toNat?

/-- Parse a bounded index token (`Fin n`), refusing anything out of range. -/
def finOf? (n : Nat) (s : String) : Option (Fin n) :=
  match natOf? s with
  | some k => if h : k < n then some ⟨k, h⟩ else none
  | none => none

/-- The wire digit of a guild row. -/
def digitOf (g : Geisha) : Char := Char.ofNat (48 + g.val)

/-- The guild row a wire digit denotes. A character outside `'0'..'6'` REFUSES: there is no
default card, so a silent decode would answer for a position nobody sent. (Note the explicit
range test — `Char.toNat - 48` alone would truncate every character below `'0'` to row `0`.) -/
def cardOf? (c : Char) : Option Geisha :=
  if '0' ≤ c && c ≤ '6' then
    let n := c.toNat - 48
    if h : n < 7 then some ⟨n, h⟩ else none
  else none

/-- `cardOf?` inverts `digitOf` — the wire alphabet is faithful. -/
theorem cardOf?_digitOf (g : Geisha) : cardOf? (digitOf g) = some g := by
  fin_cases g <;> decide

/-- The seven guild rows, in index order. -/
def allGuilds : List Geisha := [0, 1, 2, 3, 4, 5, 6]

/-- The four action kinds, in the used-flag index order `reference.rs::ActionKind::idx` uses. -/
def allKinds : List ActionKind := [.secretK, .discardK, .giftK, .competitionK]

/-- A `Bool` as its wire token. -/
def boolTok (b : Bool) : String := if b then "1" else "0"

/-- A seat as its wire token. -/
def seatTok : Player → String
  | .p1 => "0"
  | .p2 => "1"

/-- Decode a seat token. -/
def seatOf? (s : String) : Option Player :=
  match s with
  | "0" => some .p1
  | "1" => some .p2
  | _ => none

/-! ## §2 — the card-zone codec -/

/-- Encode a card zone: each row's digit repeated by its multiplicity, rows ascending. Canonical
by construction (the zones are MULTISETS, so there is no order to lose), and `-` when empty. -/
def encodeCards (m : Multiset Geisha) : String :=
  let s : String := allGuilds.foldl
    (fun acc g => acc ++ String.ofList (List.replicate (m.count g) (digitOf g))) ""
  if s == "" then "-" else s

/-- Decode a card zone, refusing any character that is not a row digit. -/
def cardsOf? (s : String) : Option (Multiset Geisha) :=
  if s == "-" then some 0
  else s.toList.foldl
    (fun acc c =>
      match acc, cardOf? c with
      | some m, some g => some (m + {g})
      | _, _ => none)
    (some 0)

/-! ## §3 — the state codec -/

/-- Build a per-seat function from its two values. -/
def bySeat (a b : Multiset Geisha) : Player → Multiset Geisha
  | .p1 => a
  | .p2 => b

/-- Encode a seat's four used-flags. -/
def encodeUsed (f : ActionKind → Bool) : String :=
  String.ofList (allKinds.map (fun k => if f k then '1' else '0'))

/-- Decode one flag character. -/
def bitOf? (c : Char) : Option Bool :=
  if c == '0' then some false else if c == '1' then some true else none

/-- Decode a seat's four used-flags. -/
def usedOf? (s : String) : Option (ActionKind → Bool) :=
  match s.toList with
  | [a, b, c, d] =>
    match bitOf? a, bitOf? b, bitOf? c, bitOf? d with
    | some va, some vb, some vc, some vd =>
      some (fun k =>
        match k with
        | .secretK => va
        | .discardK => vb
        | .giftK => vc
        | .competitionK => vd)
    | _, _, _, _ => none
  | _ => none

/-- Encode the escrow (`PEND`). -/
def encodePending : Option Offer → String
  | none => "0"
  | some (.gift p c₀ c₁ c₂) =>
    String.intercalate " " ["1", seatTok p, String.ofList [digitOf c₀], String.ofList [digitOf c₁],
      String.ofList [digitOf c₂]]
  | some (.comp p a₀ a₁ b₀ b₁) =>
    String.intercalate " " ["2", seatTok p, String.ofList [digitOf a₀], String.ofList [digitOf a₁],
      String.ofList [digitOf b₀], String.ofList [digitOf b₁]]

/-- Decode a single-digit card TOKEN. -/
def cardTok? (s : String) : Option Geisha :=
  match s.toList with
  | [c] => cardOf? c
  | _ => none

/-- Decode `PEND`, returning the trailing tokens. -/
def pendingOf? : List String → Option (Option Offer × List String)
  | "0" :: rest => some (none, rest)
  | "1" :: pT :: c0 :: c1 :: c2 :: rest =>
    match seatOf? pT, cardTok? c0, cardTok? c1, cardTok? c2 with
    | some p, some x0, some x1, some x2 => some (some (.gift p x0 x1 x2), rest)
    | _, _, _, _ => none
  | "2" :: pT :: a0 :: a1 :: b0 :: b1 :: rest =>
    match seatOf? pT, cardTok? a0, cardTok? a1, cardTok? b0, cardTok? b1 with
    | some p, some y0, some y1, some z0, some z1 => some (some (.comp p y0 y1 z0 z1), rest)
    | _, _, _, _, _ => none
  | _ => none

/-- Encode a whole `GState`. -/
def encodeState (s : GState) : String :=
  String.intercalate " "
    [ encodeCards s.removed, encodeCards s.deck,
      encodeCards (s.hand .p1), encodeCards (s.hand .p2),
      encodeCards (s.secret .p1), encodeCards (s.secret .p2),
      encodeCards (s.discardPile .p1), encodeCards (s.discardPile .p2),
      encodeCards (s.placed .p1), encodeCards (s.placed .p2),
      encodeUsed (s.used .p1), encodeUsed (s.used .p2),
      encodePending s.pending, seatTok s.current, toString s.turns ]

/-- Decode a whole `GState`, returning the trailing tokens. -/
def stateOf? : List String → Option (GState × List String)
  | rT :: dT :: h1 :: h2 :: s1 :: s2 :: d1 :: d2 :: p1 :: p2 :: u1 :: u2 :: rest => do
    let removed ← cardsOf? rT
    let deck ← cardsOf? dT
    let hand1 ← cardsOf? h1
    let hand2 ← cardsOf? h2
    let sec1 ← cardsOf? s1
    let sec2 ← cardsOf? s2
    let dis1 ← cardsOf? d1
    let dis2 ← cardsOf? d2
    let pl1 ← cardsOf? p1
    let pl2 ← cardsOf? p2
    let used1 ← usedOf? u1
    let used2 ← usedOf? u2
    let (pend, rest') ← pendingOf? rest
    match rest' with
    | curT :: turnsT :: tl => do
      let cur ← seatOf? curT
      let turns ← natOf? turnsT
      some ({ removed := removed
              deck := deck
              hand := bySeat hand1 hand2
              secret := bySeat sec1 sec2
              discardPile := bySeat dis1 dis2
              placed := bySeat pl1 pl2
              used := fun p => match p with | .p1 => used1 | .p2 => used2
              pending := pend
              current := cur
              turns := turns }, tl)
    | _ => none
  | _ => none

/-! ## §4 — the action / response codec -/

/-- Decode an `ACTION`, returning the trailing tokens. -/
def actionOf? : List String → Option (Action × List String)
  | "0" :: c :: rest =>
    match cardTok? c with
    | some x => some (.secret x, rest)
    | none => none
  | "1" :: c1 :: c2 :: rest =>
    match cardTok? c1, cardTok? c2 with
    | some x1, some x2 => some (.discard x1 x2, rest)
    | _, _ => none
  | "2" :: c0 :: c1 :: c2 :: rest =>
    match cardTok? c0, cardTok? c1, cardTok? c2 with
    | some x0, some x1, some x2 => some (.offerGift x0 x1 x2, rest)
    | _, _, _ => none
  | "3" :: a0 :: a1 :: b0 :: b1 :: rest =>
    match cardTok? a0, cardTok? a1, cardTok? b0, cardTok? b1 with
    | some y0, some y1, some z0, some z1 => some (.offerComp y0 y1 z0 z1, rest)
    | _, _, _, _ => none
  | _ => none

/-- Decode a `RESP`, returning the trailing tokens. A pick out of its shape's range REFUSES. -/
def responseOf? : List String → Option (Response × List String)
  | "0" :: kT :: rest =>
    match finOf? 3 kT with
    | some k => some (.gift k, rest)
    | none => none
  | "1" :: kT :: rest =>
    match finOf? 2 kT with
    | some k => some (.comp k, rest)
    | none => none
  | _ => none

/-! ## §5 — the RULES half of legality, factored out of `legalB`

`legal_decisions` in the Rust twin does two things at once: it applies the game's legality rules and
it enumerates card combinations. Only the first is the model's. These two definitions are exactly
`legalB`/`legalRespB` with the card conjunct removed, and the two theorems below prove the
factorization is EXACT — which is what lets a caller enumerate combinations without owning a rule. -/

/-- Is action-kind `k` OPEN for `p`: `p` is to move, no offer is pending, the flag is unused. -/
def kindOpen (s : GState) (p : Player) (k : ActionKind) : Bool :=
  decide (s.current = p) && s.pending.isNone && (! s.used p k)

/-- Is a RESPONSE open for `p`: an offer is pending, `p` is to move, `p` did not cut it. -/
def respOpen (s : GState) (p : Player) : Bool :=
  match s.pending with
  | none => false
  | some o => decide (s.current = p) && decide (o.proposer = p.other)

/-- **`legalB_iff_kindOpen`** — `legalB` is EXACTLY `kindOpen` at the action's kind AND the card
containment. So a caller may gate on `kindOpen` and then supply only combinatorics. -/
theorem legalB_iff_kindOpen (s : GState) (p : Player) (a : Action) :
    legalB s p a = (kindOpen s p a.kind && decide (actionCards a ≤ s.hand p)) := by
  simp only [legalB, kindOpen, Bool.and_assoc]

/-- **`legalRespB_iff_respOpen`** — `legalRespB` is EXACTLY `respOpen` AND the shape match. -/
theorem legalRespB_iff_respOpen (s : GState) (p : Player) (r : Response) :
    legalRespB s p r =
      (respOpen s p && (match s.pending with | none => false | some o => o.accepts r)) := by
  unfold legalRespB respOpen
  cases s.pending with
  | none => rfl
  | some o => simp only [Bool.and_assoc]

/-- **`wonB`** — the `Bool` reflection of the model's `Won` predicate. -/
def wonB (s : GState) (p : Player) : Bool :=
  decide (charmWinThreshold ≤ charmScore s p) || decide (guildWinThreshold ≤ geishaScore s p)

/-- **`wonB_iff_Won`** — the reflection is FAITHFUL, so the `won` verb answers the model's own
win predicate and not a restatement of it. -/
theorem wonB_iff_Won (s : GState) (p : Player) : wonB s p = true ↔ Won s p := by
  simp only [wonB, Bool.or_eq_true, decide_eq_true_eq, Won]

/-- The winner token: `0` is a DRAW (`roundWinner_draw_iff`), not "unadjudicated". -/
def winnerTok : Option Player → String
  | none => "0"
  | some .p1 => "1"
  | some .p2 => "2"

/-- **`winnerTok_branch_agrees`** — reading the seat off the CLAUSE gives the same token as reading
it off `roundWinner`. So a caller that takes the `branch` verb's answer and a caller that takes the
`winner` verb's answer cannot disagree; `branch` carries strictly more information (WHICH clause),
never different information. -/
theorem winnerTok_branch_agrees (s : GState) :
    winnerTok (branchWinner (roundWinnerBranch s)) = winnerTok (roundWinner s) := by
  rw [roundWinner_eq_branchWinner]

/-- The controller token for one row. -/
def controlTok : Option Player → String
  | none => "0"
  | some .p1 => "1"
  | some .p2 => "2"

/-- A full round's committed turn count: 8 action-turns + 4 responses (`MultiwayTug`'s
`full_round_is_twelve_turns`, pinned in `MultiwayTugFixtures`). -/
def roundTurns : Nat := 8 + 4

/-! ## §6 — verb dispatch -/

/-- The verb table. `none` is the fail-closed refusal. -/
def decide? : List String → Option String
  | ["charm"] =>
    some (String.intercalate " " ("7" :: allGuilds.map (fun g => toString (charm g))))
  | ["turns"] => some (toString roundTurns)
  | "legal" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | pT :: r2 => do
      let p ← seatOf? pT
      let (a, _) ← actionOf? r2
      some (boolTok (legalB s p a))
    | _ => none
  | "legalresp" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | pT :: r2 => do
      let p ← seatOf? pT
      let (r, _) ← responseOf? r2
      some (boolTok (legalRespB s p r))
    | _ => none
  | "kinds" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | [pT] => do
      let p ← seatOf? pT
      some (String.intercalate " "
        (allKinds.map (fun k => boolTok (kindOpen s p k)) ++ [boolTok (respOpen s p)]))
    | _ => none
  | "split" :: rest => do
    let (pend, r1) ← pendingOf? rest
    let (r, r2) ← responseOf? r1
    if r2.isEmpty then
      match pend with
      | none => none
      | some o =>
        some (String.intercalate " " [encodeCards (takerShare o r), encodeCards (cutterShare o r)])
    else none
  | "act" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | pT :: r2 => do
      let p ← seatOf? pT
      let (a, r3) ← actionOf? r2
      if r3.isEmpty then some (encodeState (applyAction s p a)) else none
    | _ => none
  | "respond" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | pT :: r2 => do
      let p ← seatOf? pT
      let (r, r3) ← responseOf? r2
      if r3.isEmpty then some (encodeState (applyResponse s p r)) else none
    | _ => none
  | "control" :: rest => do
    let (s, r1) ← stateOf? rest
    if r1.isEmpty then
      some (String.intercalate " " ("7" :: allGuilds.map (fun g => controlTok (control s g))))
    else none
  | "count" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | [pT, gT] => do
      let p ← seatOf? pT
      let g ← finOf? 7 gT
      some (toString (geishaCount s p g))
    | _ => none
  | "score" :: rest => do
    let (s, r1) ← stateOf? rest
    if r1.isEmpty then
      some (String.intercalate " "
        [ toString (charmScore s .p1), toString (geishaScore s .p1),
          toString (charmScore s .p2), toString (geishaScore s .p2) ])
    else none
  | "won" :: rest => do
    let (s, r1) ← stateOf? rest
    match r1 with
    | [pT] => do
      let p ← seatOf? pT
      some (boolTok (wonB s p))
    | _ => none
  | "winner" :: rest => do
    let (s, r1) ← stateOf? rest
    if r1.isEmpty then some (winnerTok (roundWinner s)) else none
  | "branch" :: rest => do
    let (s, r1) ← stateOf? rest
    if r1.isEmpty then
      some (String.intercalate " "
        [toString (roundWinnerBranch s), winnerTok (branchWinner (roundWinnerBranch s))])
    else none
  | "total" :: rest => do
    let (s, r1) ← stateOf? rest
    if r1.isEmpty then some (encodeCards (totalCards s)) else none
  | _ => none

/-- The whole `String → String` oracle: `"1 …"` on success, `"0"` fail-closed. -/
def rulesWire (s : String) : String :=
  match decide? ((s.splitOn " ").filter (fun t => t != "")) with
  | some out => "1 " ++ out
  | none => "0"

/-- **`@[export dregg_multiway_tug_rules]`** — the FFI entry `dregg-multiway-tug` calls. Every
legality verdict, escrow split, row control, tally and round winner the deployed multiway-tug
surface reports is COMPUTED HERE, by `Dregg2.Games.MultiwayTug`. -/
@[export dregg_multiway_tug_rules]
def rulesFFI (s : String) : String := rulesWire s

/-! ## §7 — teeth (named pins in `MultiwayTugFFIFixtures` FAIL the build on regression)

The states below are the MODEL's OWN witnesses (`demo`, `undecidedState`, `winState`, `blankState`),
so a tooth is pinned to the same object the theorems are about.

⚑ **THE TEETH NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and the 60 `#guard` wire pins that used to
run at elaboration here made every game-fixture regression a hard failure of every Rust proving
target. The witness STATES stay here; the EVALUATION — each pin as a NAMED theorem per
GUARD-DISCIPLINE, `native_decide` + `#assert_compiled` — lives in
`MultiwayTugFFIFixtures.lean`, rooted in the central guard library: a plain `lake build` still
runs every pin, and a stale fixture reds the guard library instead of the archive. Every pinned
expression here mentions only PUBLIC names, so the pins moved verbatim — the influence table,
the codec round-trips, the anti-self-deal tooth and interlock, `kinds`, the split table,
conservation, control/score/won/winner, the CLAUSE (`branch`), the ⚑⚑ provenance tooth
(`undecidedState`), the deepest branch (`rowTieState`), and every fail-closed refusal — with
the section narratives beside the pins they justify. -/

/-- A sub-threshold round where the charm TIES and only the ROW COUNT separates the seats: p1 holds
row `6` (charm `5`, one row), p2 holds rows `0` and `4` (charm `2 + 3 = 5`, two rows). This reaches
`roundWinner`'s DEEPEST branch — the one the deleted Rust was furthest from having. -/
def rowTieState : GState :=
  { blankState with
    placed := fun p => if p = .p1 then ({6} : Multiset Geisha) else ({0, 4} : Multiset Geisha) }

/-- The pending-Gift position: p1 has cut rows `3 3 5` out of `demo`'s hand. -/
def demoCut : GState := applyAction demo .p1 (Action.offerGift 3 3 5)

/-! ## §8 — axiom hygiene for this module's own claims -/

#assert_axioms legalB_iff_kindOpen
#assert_axioms legalRespB_iff_respOpen
#assert_axioms wonB_iff_Won
#assert_axioms cardOf?_digitOf
#assert_axioms winnerTok_branch_agrees

end Dregg2.Games.MultiwayTugFFI
