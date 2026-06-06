import Dregg2.Exec.CodecRoundtrip.Leaves
import Dregg2.Exec.CodecRoundtrip.Value
import Dregg2.Exec.CodecRoundtrip.Auth

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide
open Dregg2.Exec.TurnExecutorFull (QueueTxOpA)

/-! ## §8 — the narrow `AUTHS` list (`parseAuths`) roundtrip — the INPUT-LENGTH-FUEL `let rec` loop
pattern (the gateway reused by every remaining FILL-J production: `parseNats`/`parseEscrow`/`parseQueue`/
`parseSwiss`/`parseForest` all share it). `parseAuths`'s inner `loop` runs on `cs.length + 1` fuel; the
adequacy is carried by the invariant `input.length < fuel` (each iteration consumes ≥1 char while fuel
drops by 1, so it is self-maintaining) — NO separate length-bound lemma is needed. Tags are single
digits (`0..6`) and `authOfTag_authTag` (§0f) is already proved, so the per-element parse is trivial. -/

/-- The `AUTHS` tail encoder (the `foldl` body in cons-recursive form, mirroring §6d). -/
private def encodeAuthsTail (as : List Authority.Auth) : String :=
  as.foldl (fun acc x => acc ++ "," ++ toString (authTag x)) ""

/-- The accumulator pulls OUT of the tail fold (`List Char`-level, mirroring `foldl_authtail`). -/
private theorem foldl_authsTail (as : List Authority.Auth) : ∀ (acc : String),
    as.foldl (fun s x => s ++ "," ++ toString (authTag x)) acc
      = acc ++ as.foldl (fun s x => s ++ "," ++ toString (authTag x)) "" := by
  induction as with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ toString (authTag b)), ih ("" ++ "," ++ toString (authTag b))]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

/-- Rebracket a NON-EMPTY tag TAIL into comma-then-tag-then-tail (peelable). -/
private theorem encAuthsTail_cons_shape (b : Authority.Auth) (bs : List Authority.Auth) (rest : PState) :
    (encodeAuthsTail (b :: bs)).toList ++ rest
      = ',' :: ((toString (authTag b)).toList ++ ((encodeAuthsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeAuthsTail (b :: bs)
      = ("" ++ "," ++ toString (authTag b)) ++ encodeAuthsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ toString (authTag x)) "" = _
      rw [List.foldl_cons]; exact foldl_authsTail bs ("" ++ "," ++ toString (authTag b))]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

/-- Rebracket a NON-EMPTY tag LIST into open-`[`-then-body form. -/
private theorem encodeAuths_cons_shape (a : Authority.Auth) (as : List Authority.Auth) (rest : PState) :
    (encodeAuths (a :: as)).toList ++ rest
      = '[' :: ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest))) := by
  simp only [encodeAuths]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ toString (authTag x)) "") = encodeAuthsTail as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-- A tag's `toString` is a nonempty digit string (length ≥ 1) — the per-iteration consume bound. -/
private theorem tag_toString_len (a : Authority.Auth) : 1 ≤ (toString (authTag a)).toList.length := by
  obtain ⟨h0, t0, ht0, _, _, _⟩ := repr_cons (authTag a)
  rw [ht0]; simp

/-- **The loop recovers the candidate list**, given the `input.length < fuel` invariant. By induction
on the tail (the head `a` generalized); the recursive call lands at `fuel-1` with a strictly-shorter
input, so the invariant is preserved (`omega`, using `tag_toString_len`). -/
private theorem parseAuths_loop_works : ∀ (as : List Authority.Auth) (a : Authority.Auth) (rest : PState) (fuel : Nat),
    ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest))).length < fuel →
    parseAuths.loop fuel
        ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeAuthsTail ([] : List Authority.Auth)).toList = [] from rfl, List.nil_append]
      unfold parseAuths.loop
      rw [parseNat_toString (authTag a) (']' :: rest) (nd_brack rest)]
      simp only []
      rw [authOfTag_authTag]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      have hlen : 1 ≤ (toString (authTag a)).toList.length := tag_toString_len a
      rw [encAuthsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseAuths.loop
      rw [parseNat_toString (authTag a) _ (nd_comma _)]
      simp only []
      rw [authOfTag_authTag]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((toString (authTag a2)).toList ++ ((encodeAuthsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (d): the narrow `AUTHS` list roundtrip** (`parseAuths ∘ encodeAuths = id`). The
`oneOf`-free `Auth` tag array the wide `cA` action field carries; the gateway for the length-fuel loops. -/
theorem parseAuths_encode (rs : List Authority.Auth) (rest : PState) :
    parseAuths ((encodeAuths rs).toList ++ rest) = some (rs, rest) := by
  cases rs with
  | nil =>
      unfold parseAuths
      simp only [encodeAuths]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseAuths
      rw [encodeAuths_cons_shape a as rest]
      obtain ⟨h0, t0, ht0, hh0dig, _, _⟩ := repr_cons (authTag a)
      have hempty : lit "[]"
          ('[' :: ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest)))) = none := by
        rw [ht0, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] h0 _ (by intro heq; subst heq; exact absurd hh0dig (by decide))]
      rw [hempty]; simp only []
      rw [show ('[' :: ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseAuths_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

/-- `cA` (read `,` then an `AUTHS` tag array) on an `encodeAuthsW`-led tail — via §8's `parseAuths_encode`.
This is the combinator that lets the 4 AUTHS-bearing action arms join the `simple` sweep. -/
theorem cA_step (rs : List Authority.Auth) (rest : PState) :
    cA ((",":String).toList ++ ((encodeAuthsW rs).toList ++ rest)) = some (rs, rest) := by
  unfold cA; rw [lit_append]; simp only []
  unfold parseAuthsW encodeAuthsW
  exact parseAuths_encode rs rest

/-! ## §9 — the `[N,N,…]` Nat-list (`parseNats`) roundtrip — the SAME length-fuel loop as §8 (the
`nullifiers`/`commitments` `WState` fields). This CONFIRMS §8's recipe is reusable verbatim for every
length-fuel list: it is §8 with the element `toString (authTag a)`→`toString a` and the `authOfTag`
step dropped (the element is the `Nat` directly). The first STATE-decoder sub-production. -/

private def encodeNatsTail (ns : List Nat) : String :=
  ns.foldl (fun acc x => acc ++ "," ++ toString x) ""

private theorem foldl_natsTail (ns : List Nat) : ∀ (acc : String),
    ns.foldl (fun s x => s ++ "," ++ toString x) acc
      = acc ++ ns.foldl (fun s x => s ++ "," ++ toString x) "" := by
  induction ns with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ toString b), ih ("" ++ "," ++ toString b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encNatsTail_cons_shape (b : Nat) (bs : List Nat) (rest : PState) :
    (encodeNatsTail (b :: bs)).toList ++ rest
      = ',' :: ((toString b).toList ++ ((encodeNatsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeNatsTail (b :: bs) = ("" ++ "," ++ toString b) ++ encodeNatsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ toString x) "" = _
      rw [List.foldl_cons]; exact foldl_natsTail bs ("" ++ "," ++ toString b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeNats_cons_shape (a : Nat) (as : List Nat) (rest : PState) :
    (encodeNats (a :: as)).toList ++ rest
      = '[' :: ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest))) := by
  simp only [encodeNats]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ toString x) "") = encodeNatsTail as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem nat_toString_len (a : Nat) : 1 ≤ (toString a).toList.length := by
  obtain ⟨h0, t0, ht0, _, _, _⟩ := repr_cons a
  rw [ht0]; simp

private theorem parseNats_loop_works : ∀ (as : List Nat) (a : Nat) (rest : PState) (fuel : Nat),
    ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest))).length < fuel →
    parseNats.loop fuel ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeNatsTail ([] : List Nat)).toList = [] from rfl, List.nil_append]
      unfold parseNats.loop
      rw [parseNat_toString a (']' :: rest) (nd_brack rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      have hlen : 1 ≤ (toString a).toList.length := nat_toString_len a
      rw [encNatsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseNats.loop
      rw [parseNat_toString a _ (nd_comma _)]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((toString a2).toList ++ ((encodeNatsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (e): the `[N,N,…]` Nat-list roundtrip** (`parseNats ∘ encodeNats = id`) — the
`nullifiers`/`commitments` `WState` fields, and the first confirmation that §8's length-fuel recipe is a
verbatim template. -/
theorem parseNats_encode (ns : List Nat) (rest : PState) :
    parseNats ((encodeNats ns).toList ++ rest) = some (ns, rest) := by
  cases ns with
  | nil =>
      unfold parseNats
      simp only [encodeNats]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseNats
      rw [encodeNats_cons_shape a as rest]
      obtain ⟨h0, t0, ht0, hh0dig, _, _⟩ := repr_cons a
      have hempty : lit "[]"
          ('[' :: ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest)))) = none := by
        rw [ht0, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] h0 _ (by intro heq; subst heq; exact absurd hh0dig (by decide))]
      rw [hempty]; simp only []
      rw [show ('[' :: ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseNats_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

/-! ## §10 — the `BAL` ledger-list (`parseBal`) roundtrip — the CONSERVED-MEASURE `WState` field (what
the executor's per-asset conservation laws range over). The length-fuel loop of §8/§9, but the element
is the SELF-DELIMITING `[c,a,amt]` entry (`parseBalEntry`, already proved in §2) — so it round-trips for
ANY tail, with NO non-digit post-byte condition. A `bal`-list codec bug is now caught. -/

/-- One `BALENTRY` `[c,a,amt]` (matching `encodeBal`'s local `one`). -/
private def balOne (p : CellId × AssetId × Int) : String :=
  "[" ++ toString p.1 ++ "," ++ toString p.2.1 ++ "," ++ toString p.2.2 ++ "]"

private def encodeBalTail (es : List (CellId × AssetId × Int)) : String :=
  es.foldl (fun acc p => acc ++ "," ++ balOne p) ""

/-- One entry round-trips for ANY tail (self-delimiting) — from §2's `parseBalEntry_encode`. -/
private theorem parseBalEntry_one (e : CellId × AssetId × Int) (rest : PState) :
    parseBalEntry ((balOne e).toList ++ rest) = some (e, rest) := by
  obtain ⟨c, a, amt⟩ := e
  exact parseBalEntry_encode c a amt rest

/-- A `BALENTRY` opens with `'['` (so the `bal` list body is `[[…`, making `lit "[]"` fail). Explicit
witness ⇒ no metavar; `simp` normalizes the left-assoc append on both sides. -/
private theorem balOne_head (a : CellId × AssetId × Int) : ∃ t, (balOne a).toList = '[' :: t := by
  refine ⟨((toString a.1 ++ "," ++ toString a.2.1 ++ "," ++ toString a.2.2 ++ "]" : String)).toList, ?_⟩
  unfold balOne
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_balTail (es : List (CellId × AssetId × Int)) : ∀ (acc : String),
    es.foldl (fun s p => s ++ "," ++ balOne p) acc
      = acc ++ es.foldl (fun s p => s ++ "," ++ balOne p) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ balOne b), ih ("" ++ "," ++ balOne b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encBalTail_cons_shape (b : CellId × AssetId × Int) (bs : List (CellId × AssetId × Int))
    (rest : PState) :
    (encodeBalTail (b :: bs)).toList ++ rest
      = ',' :: ((balOne b).toList ++ ((encodeBalTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeBalTail (b :: bs) = ("" ++ "," ++ balOne b) ++ encodeBalTail bs from by
      show (b :: bs).foldl (fun s p => s ++ "," ++ balOne p) "" = _
      rw [List.foldl_cons]; exact foldl_balTail bs ("" ++ "," ++ balOne b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeBal_cons_shape (a : CellId × AssetId × Int) (as : List (CellId × AssetId × Int))
    (rest : PState) :
    (encodeBal (a :: as)).toList ++ rest
      = '[' :: ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest))) := by
  rw [show encodeBal (a :: as) = "[" ++ balOne a ++ encodeBalTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseBal_loop_works : ∀ (as : List (CellId × AssetId × Int)) (a : CellId × AssetId × Int)
    (rest : PState) (fuel : Nat),
    ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest))).length < fuel →
    parseBal.loop fuel ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeBalTail ([] : List (CellId × AssetId × Int))).toList = [] from rfl, List.nil_append]
      unfold parseBal.loop
      rw [parseBalEntry_one a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encBalTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseBal.loop
      rw [parseBalEntry_one a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((balOne a2).toList ++ ((encodeBalTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (f): the `BAL` ledger-list roundtrip** (`parseBal ∘ encodeBal = id`) — the
CONSERVED-MEASURE `WState` field. The self-delimiting `[c,a,amt]` element makes this the cleanest
length-fuel instance (no post-byte condition). -/
theorem parseBal_encode (es : List (CellId × AssetId × Int)) (rest : PState) :
    parseBal ((encodeBal es).toList ++ rest) = some (es, rest) := by
  cases es with
  | nil =>
      unfold parseBal
      rw [show (encodeBal ([] : List (CellId × AssetId × Int))) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseBal
      rw [encodeBal_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := balOne_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [show ('[' :: ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseBal_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

/-! ## §11 — the `ESCROWS` side-table (`parseEscrows`) roundtrip. Length-fuel loop (§10 template), but
the element `parseEscrow` is a 7-field `do`-block with two 0/1 FLAGS (`parseFlag_bool`, §0f). The first
side-table whose element itself needs a `do`-block roundtrip proof. -/

/-- `lit "[" ('[' :: rest) = some rest` — GENERIC (proved once, no per-element defeq), so consuming the
list-open `[` never whnf-reduces a big element term. -/
theorem lit_lbrack (rest : PState) : lit "[" ('[' :: rest) = some rest := by
  unfold lit; rw [show ("[":String).toList = ['['] from by decide, litGo_cons_match]; rfl

/-- **The optional-`Nat` leaf** (`parseOptNat ∘ encodeOptNat = id`). Shared by `EscrowRecord` queue
bindings and `SwissRecord.cert`. -/
theorem parseOptNat_encode (o : Option Nat) (rest : PState) :
    parseOptNat ((encodeOptNat o).toList ++ rest) = some (o, rest) := by
  cases o with
  | none =>
      unfold parseOptNat encodeOptNat
      rw [show (("{\"none\":0}":String).toList ++ rest) = ("{\"none\":0}":String).toList ++ rest from rfl,
        lit_append]
  | some n =>
      unfold parseOptNat encodeOptNat
      rw [show (("{\"some\":" ++ toString n ++ "}":String).toList ++ rest)
            = ("{\"some\":":String).toList ++ ((toString n).toList ++ ('}' :: rest)) from by
          simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
            List.append_assoc, List.cons_append, List.nil_append]]
      rw [lit_ne_pre "{\"none\":0}" "{\"some\":" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only []
      rw [parseNat_toString n ('}' :: rest) (nd_brace rest)]
      simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}' :: rest) = ("}":String).toList ++ rest from by
              simp only [show ("}":String).toList = ['}'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "}" rest]
      simp only [Option.map_some]

set_option maxHeartbeats 1000000 in
/-- **The `ESC` entry roundtrip** — the 9-field record `[id,creator,recipient,amount,resolved,asset,
bridge,queueDep,queueMsg]` (flags via §0f's `parseFlag_bool`; queue fields via `parseOptNat_encode`);
self-delimiting, so round-trips for ANY tail. -/
theorem parseEscrow_encode (e : EscrowRecord) (rest : PState) :
    parseEscrow ((encodeEscrow e).toList ++ rest) = some (e, rest) := by
  unfold parseEscrow encodeEscrow
  simp only [String.toList_append, List.append_assoc]
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    cI_step _ _ (nd_litComma _), parseFlag_bool _ _ (nd_litComma _), parseFlag_bool _ _ (nd_litComma _),
    parseOptNat_encode, Option.bind_eq_bind, Option.bind]

private def encodeEscrowsTail (es : List EscrowRecord) : String :=
  es.foldl (fun acc x => acc ++ "," ++ encodeEscrow x) ""

/-- An `ESC` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeEscrow_head (e : EscrowRecord) : ∃ t, (encodeEscrow e).toList = '[' :: t := by
  refine ⟨(toString e.id ++ "," ++ toString e.creator ++ "," ++ toString e.recipient ++ ","
    ++ toString e.amount ++ "," ++ (if e.resolved then "1" else "0") ++ "," ++ toString e.asset ++ ","
    ++ (if e.bridge then "1" else "0") ++ "," ++ encodeOptNat e.queueDep ++ ","
    ++ encodeOptNat e.queueMsg ++ "]" : String).toList, ?_⟩
  unfold encodeEscrow
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_escrowsTail (es : List EscrowRecord) : ∀ (acc : String),
    es.foldl (fun s x => s ++ "," ++ encodeEscrow x) acc
      = acc ++ es.foldl (fun s x => s ++ "," ++ encodeEscrow x) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeEscrow b), ih ("" ++ "," ++ encodeEscrow b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encEscrowsTail_cons_shape (b : EscrowRecord) (bs : List EscrowRecord) (rest : PState) :
    (encodeEscrowsTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeEscrow b).toList ++ ((encodeEscrowsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeEscrowsTail (b :: bs) = ("" ++ "," ++ encodeEscrow b) ++ encodeEscrowsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeEscrow x) "" = _
      rw [List.foldl_cons]; exact foldl_escrowsTail bs ("" ++ "," ++ encodeEscrow b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeEscrows_cons_shape (a : EscrowRecord) (as : List EscrowRecord) (rest : PState) :
    (encodeEscrows (a :: as)).toList ++ rest
      = '[' :: ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest))) := by
  rw [show encodeEscrows (a :: as) = "[" ++ encodeEscrow a ++ encodeEscrowsTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseEscrows_loop_works : ∀ (as : List EscrowRecord) (a : EscrowRecord)
    (rest : PState) (fuel : Nat),
    ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest))).length < fuel →
    parseEscrows.loop fuel ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeEscrowsTail ([] : List EscrowRecord)).toList = [] from rfl, List.nil_append]
      unfold parseEscrows.loop
      rw [parseEscrow_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encEscrowsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseEscrows.loop
      rw [parseEscrow_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeEscrow a2).toList ++ ((encodeEscrowsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (g): the `ESCROWS` side-table roundtrip** (`parseEscrows ∘ encodeEscrows = id`). -/
theorem parseEscrows_encode (es : List EscrowRecord) (rest : PState) :
    parseEscrows ((encodeEscrows es).toList ++ rest) = some (es, rest) := by
  cases es with
  | nil =>
      unfold parseEscrows
      rw [show (encodeEscrows ([] : List EscrowRecord)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseEscrows
      rw [encodeEscrows_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeEscrow_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseEscrows_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §11b — the `QUEUES` side-table (`parseQueues`) roundtrip. Length-fuel loop (§11 template), and
the element `parseQueue` is a 4-field `do`-block `[id,owner,capacity,buffer]` whose LAST field `buffer`
is a NESTED `Nat`-list — reusing §9's `parseNats_encode` for that field (the first side-table whose
element embeds another array codec). Self-delimiting, so it round-trips for ANY tail. -/

set_option maxHeartbeats 1000000 in
/-- **The `Q` entry roundtrip** — the 4-field record `[id,owner,capacity,buffer]`, where `buffer` is a
nested `[N,N,…]` array discharged by §9's `parseNats_encode`. The three leading `Nat`s walk via
`parseNat_toString`/`cN_step` (post-byte `,`); the `,` before `buffer` and the closing `]` are plain
`lit_append`s (the buffer's `parseNats` leaves its argument `rest`, so the outer `]` is a clean literal
consume). Self-delimiting, so it round-trips for ANY tail. -/
theorem parseQueue_encode (q : QueueRecord) (rest : PState) :
    parseQueue ((encodeQueue q).toList ++ rest) = some (q, rest) := by
  unfold parseQueue encodeQueue
  simp only [String.toList_append, List.append_assoc]
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    parseNats_encode, Option.bind_eq_bind, Option.bind]

private def encodeQueuesTail (qs : List QueueRecord) : String :=
  qs.foldl (fun acc x => acc ++ "," ++ encodeQueue x) ""

/-- A `Q` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeQueue_head (q : QueueRecord) : ∃ t, (encodeQueue q).toList = '[' :: t := by
  refine ⟨(toString q.id ++ "," ++ toString q.owner ++ "," ++ toString q.capacity ++ ","
    ++ encodeNats q.buffer ++ "]" : String).toList, ?_⟩
  unfold encodeQueue
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_queuesTail (qs : List QueueRecord) : ∀ (acc : String),
    qs.foldl (fun s x => s ++ "," ++ encodeQueue x) acc
      = acc ++ qs.foldl (fun s x => s ++ "," ++ encodeQueue x) "" := by
  induction qs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeQueue b), ih ("" ++ "," ++ encodeQueue b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encQueuesTail_cons_shape (b : QueueRecord) (bs : List QueueRecord) (rest : PState) :
    (encodeQueuesTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeQueue b).toList ++ ((encodeQueuesTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeQueuesTail (b :: bs) = ("" ++ "," ++ encodeQueue b) ++ encodeQueuesTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeQueue x) "" = _
      rw [List.foldl_cons]; exact foldl_queuesTail bs ("" ++ "," ++ encodeQueue b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeQueues_cons_shape (a : QueueRecord) (as : List QueueRecord) (rest : PState) :
    (encodeQueues (a :: as)).toList ++ rest
      = '[' :: ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest))) := by
  rw [show encodeQueues (a :: as) = "[" ++ encodeQueue a ++ encodeQueuesTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseQueues_loop_works : ∀ (as : List QueueRecord) (a : QueueRecord)
    (rest : PState) (fuel : Nat),
    ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest))).length < fuel →
    parseQueues.loop fuel ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeQueuesTail ([] : List QueueRecord)).toList = [] from rfl, List.nil_append]
      unfold parseQueues.loop
      rw [parseQueue_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encQueuesTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseQueues.loop
      rw [parseQueue_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeQueue a2).toList ++ ((encodeQueuesTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (h): the `QUEUES` side-table roundtrip** (`parseQueues ∘ encodeQueues = id`) —
the storage-queue FIFO side-table whose element embeds a nested `buffer` array (closed via §9). -/
theorem parseQueues_encode (qs : List QueueRecord) (rest : PState) :
    parseQueues ((encodeQueues qs).toList ++ rest) = some (qs, rest) := by
  cases qs with
  | nil =>
      unfold parseQueues
      rw [show (encodeQueues ([] : List QueueRecord)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseQueues
      rw [encodeQueues_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeQueue_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseQueues_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §11c — the `SWISS` side-table (`parseSwissTable`) roundtrip. Length-fuel loop (§11/§11b template),
and the element `parseSwiss` is a 6-field `do`-block `[swiss,exporter,target,rights,refcount,cert]` whose
4th field `rights` is an AUTHS tag array (reusing §8's `parseAuths_encode` via §7's `cA_step`) and whose
LAST field `cert` is an OPTIONAL `Nat` (`{"none":0}`/`{"some":N}`, discharged by the `parseOptNat_encode`
leaf below). The first side-table element combining an AUTHS field AND an Option field. Self-delimiting,
so it round-trips for ANY tail. -/

set_option maxHeartbeats 1000000 in
/-- **The `SW` entry roundtrip** — the 6-field record `[swiss,exporter,target,rights,refcount,cert]`,
where `rights` is an AUTHS array discharged by §7's `cA_step` (→ §8) and `cert` is an `Option Nat`
discharged by `parseOptNat_encode`. The three leading `Nat`s walk via `parseNat_toString`/`cN_step`
(post-byte `,`); the `,` before `cert` and the closing `]` are plain `lit_append`s (`parseOptNat`
leaves its argument `rest`, so the outer `]` is a clean literal consume). Self-delimiting. -/
theorem parseSwiss_encode (e : SwissRecord) (rest : PState) :
    parseSwiss ((encodeSwiss e).toList ++ rest) = some (e, rest) := by
  unfold parseSwiss encodeSwiss
  simp only [String.toList_append, List.append_assoc]
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    cA_step _ _, parseOptNat_encode, Option.bind_eq_bind, Option.bind]

private def encodeSwissTail (es : List SwissRecord) : String :=
  es.foldl (fun acc x => acc ++ "," ++ encodeSwiss x) ""

/-- A `SW` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeSwiss_head (e : SwissRecord) : ∃ t, (encodeSwiss e).toList = '[' :: t := by
  refine ⟨(toString e.swiss ++ "," ++ toString e.exporter ++ "," ++ toString e.target ++ ","
    ++ encodeAuthsW e.rights ++ "," ++ toString e.refcount ++ "," ++ encodeOptNat e.cert ++ "]"
    : String).toList, ?_⟩
  unfold encodeSwiss
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_swissTail (es : List SwissRecord) : ∀ (acc : String),
    es.foldl (fun s x => s ++ "," ++ encodeSwiss x) acc
      = acc ++ es.foldl (fun s x => s ++ "," ++ encodeSwiss x) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeSwiss b), ih ("" ++ "," ++ encodeSwiss b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encSwissTail_cons_shape (b : SwissRecord) (bs : List SwissRecord) (rest : PState) :
    (encodeSwissTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeSwiss b).toList ++ ((encodeSwissTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeSwissTail (b :: bs) = ("" ++ "," ++ encodeSwiss b) ++ encodeSwissTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeSwiss x) "" = _
      rw [List.foldl_cons]; exact foldl_swissTail bs ("" ++ "," ++ encodeSwiss b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeSwissTable_cons_shape (a : SwissRecord) (as : List SwissRecord) (rest : PState) :
    (encodeSwissTable (a :: as)).toList ++ rest
      = '[' :: ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest))) := by
  rw [show encodeSwissTable (a :: as) = "[" ++ encodeSwiss a ++ encodeSwissTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseSwissTable_loop_works : ∀ (as : List SwissRecord) (a : SwissRecord)
    (rest : PState) (fuel : Nat),
    ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest))).length < fuel →
    parseSwissTable.loop fuel ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeSwissTail ([] : List SwissRecord)).toList = [] from rfl, List.nil_append]
      unfold parseSwissTable.loop
      rw [parseSwiss_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encSwissTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseSwissTable.loop
      rw [parseSwiss_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeSwiss a2).toList ++ ((encodeSwissTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (i): the `SWISS` side-table roundtrip** (`parseSwissTable ∘ encodeSwissTable =
id`) — the CapTP swiss-table side-table whose element carries an AUTHS rights array (closed via §8) and
an optional handoff `cert` (closed via `parseOptNat_encode`). -/
theorem parseSwissTable_encode (ss : List SwissRecord) (rest : PState) :
    parseSwissTable ((encodeSwissTable ss).toList ++ rest) = some (ss, rest) := by
  cases ss with
  | nil =>
      unfold parseSwissTable
      rw [show (encodeSwissTable ([] : List SwissRecord)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseSwissTable
      rw [encodeSwissTable_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeSwiss_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseSwissTable_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §12 — the WIDE `CELLS` array (`parseCellsW`) roundtrip — the STATE DECODER's cell store.

The `CELLS` field is `[[id,valueW],…]`: a length-fuel loop (§8 recipe) whose element `parseCellW`
embeds the FULL recursive wide-`Value` codec (§5's `parseValueW_roundtrip`) for the payload. The one
genuinely-new obligation versus the side-tables: the loop calls `parseCellW (cs.length+1) cs` —
re-deriving the element's value-fuel from the REMAINING input length — so the per-element
`parseValueW` adequacy is `valueSize v ≤ (remaining).length + 1`, which the byte-length lower bound
`valueSize_le_encodeLen` (the parse-depth never exceeds the encoded width) discharges with slack. The
codec boundary is §1's `WfValue` (digests `< 2^256`, names escape-free), so the list roundtrip carries
a per-cell `WfCells` hypothesis (the SAME non-vacuous boundary the value roundtrip lives on). -/

/-! A structural-size LOWER bound on the encoded width: the parse-depth `valueSize v` never exceeds the
byte length of `encodeValueW v` (so the loop's `(remaining).length + 1` element-fuel always suffices).
By the §5 mutual induction; every constructor emits strictly more bytes than its size counts. -/
mutual
theorem valueSize_le_encodeLen (v : Value) : valueSize v ≤ (encodeValueW v).toList.length := by
  cases v with
  | int i => simp only [valueSize, encodeValueW, String.toList_append]; simp
  | dig d => simp only [valueSize, encodeValueW, String.toList_append]; simp
  | sym s => simp only [valueSize, encodeValueW, String.toList_append]; simp
  | record fs =>
      simp only [valueSize, encodeValueW, String.toList_append, List.length_append]
      have := fieldsSize_le_encodeLen fs
      simp only [show ("{\"rec\":":String).toList.length = 7 from by decide,
        show ("}":String).toList.length = 1 from by decide]
      omega
theorem fieldsSize_le_encodeLen (fs : List (FieldName × Value)) :
    fieldsSize fs ≤ (encodeFieldsW fs).toList.length := by
  cases fs with
  | nil => simp [fieldsSize, encodeFieldsW]
  | cons p gs =>
      obtain ⟨n, v⟩ := p
      simp only [fieldsSize, encodeFieldsW, String.toList_append, List.length_append]
      have hv := valueSize_le_encodeLen v
      have ht := fieldsTailSize_le_encodeLen gs
      simp only [show ("[":String).toList.length = 1 from by decide,
        show ("]":String).toList.length = 1 from by decide,
        show ("[\"":String).toList.length = 2 from by decide,
        show ("\",":String).toList.length = 2 from by decide]
      omega
theorem fieldsTailSize_le_encodeLen (fs : List (FieldName × Value)) :
    fieldsSize fs ≤ (encodeFieldsTailW fs).toList.length := by
  cases fs with
  | nil => simp [fieldsSize, encodeFieldsTailW]
  | cons p gs =>
      obtain ⟨n, v⟩ := p
      simp only [fieldsSize, encodeFieldsTailW, String.toList_append, List.length_append]
      have hv := valueSize_le_encodeLen v
      have ht := fieldsTailSize_le_encodeLen gs
      simp only [show (",[\"":String).toList.length = 3 from by decide,
        show ("\",":String).toList.length = 2 from by decide,
        show ("]":String).toList.length = 1 from by decide]
      omega
end

/-- Well-formed `CELLS`: every cell's payload satisfies the §1 `WfValue` boundary. -/
def WfCells : List (CellId × Value) → Prop
  | []          => True
  | p :: ps     => WfValue p.2 ∧ WfCells ps

/-- The wide-cell encoder (the inline `one` lambda of `encodeCellsW`, named for the proof). -/
def encodeCellW (p : CellId × Value) : String :=
  "[" ++ toString p.1 ++ "," ++ encodeValueW p.2 ++ "]"

/-- **One wide `CELL` `[id,valueW]` round-trips** for ANY sufficient value-fuel — the `id` `Nat`
(post-byte `,`) then the recursive payload via §5's `parseValueW_roundtrip`, then the closing `]`
(`parseValueW` leaves its argument `rest`). Self-delimiting. -/
theorem parseCellW_encode (p : CellId × Value) (rest : PState) (hwf : WfValue p.2)
    (fuel : Nat) (hf : valueSize p.2 ≤ fuel) :
    parseCellW fuel ((encodeCellW p).toList ++ rest) = some (p, rest) := by
  obtain ⟨id, v⟩ := p
  unfold parseCellW encodeCellW
  -- After `String.toList_append`, the input is the right-associated
  -- `"[".toList ++ (id.toList ++ (",".toList ++ ((encodeValueW v).toList ++ ("]".toList ++ rest))))`;
  -- each literal is consumed via `lit_append` in its `"…".toList ++ _` form (NO `show` over the big
  -- `encodeValueW v` body — that would WHNF-reduce it and time out; the §11/parseBalEntry recipe).
  simp only [String.toList_append, List.append_assoc]
  rw [lit_append]
  simp only []
  rw [parseNat_toString id _ (nd_litComma _)]
  simp only []
  rw [lit_append]
  simp only []
  rw [parseValueW_roundtrip v (("]":String).toList ++ rest) hwf fuel hf]
  simp only []
  rw [lit_append]
  simp only [Option.map_some]

private def encodeCellsTail (ps : List (CellId × Value)) : String :=
  ps.foldl (fun acc x => acc ++ "," ++ encodeCellW x) ""

/-- A wide `CELL` opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeCellW_head (p : CellId × Value) : ∃ t, (encodeCellW p).toList = '[' :: t := by
  refine ⟨(toString p.1 ++ "," ++ encodeValueW p.2 ++ "]" : String).toList, ?_⟩
  unfold encodeCellW
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_cellsTail (ps : List (CellId × Value)) : ∀ (acc : String),
    ps.foldl (fun s x => s ++ "," ++ encodeCellW x) acc
      = acc ++ ps.foldl (fun s x => s ++ "," ++ encodeCellW x) "" := by
  induction ps with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCellW b), ih ("" ++ "," ++ encodeCellW b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCellsTail_cons_shape (b : CellId × Value) (bs : List (CellId × Value)) (rest : PState) :
    (encodeCellsTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCellW b).toList ++ ((encodeCellsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCellsTail (b :: bs) = ("" ++ "," ++ encodeCellW b) ++ encodeCellsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCellW x) "" = _
      rw [List.foldl_cons]; exact foldl_cellsTail bs ("" ++ "," ++ encodeCellW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCellsW_cons_shape (a : CellId × Value) (as : List (CellId × Value)) (rest : PState) :
    (encodeCellsW (a :: as)).toList ++ rest
      = '[' :: ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCellsW (a :: as) = "[" ++ encodeCellW a ++ encodeCellsTail as ++ "]" from by
        show "[" ++ encodeCellW a ++ (as.foldl (fun acc p => acc ++ "," ++ encodeCellW p) "") ++ "]" = _
        rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseCellsW_loop_works : ∀ (as : List (CellId × Value)) (a : CellId × Value)
    (rest : PState) (fuel : Nat) (hwf : WfCells (a :: as)),
    ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest))).length < fuel →
    parseCellsW.loop fuel ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hwf hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCellsTail ([] : List (CellId × Value))).toList = [] from rfl, List.nil_append]
      unfold parseCellsW.loop
      rw [parseCellW_encode a (']' :: rest) hwf.1 _ (le_trans (valueSize_le_encodeLen a.2) (by
        rw [show ((encodeCellW a).toList ++ (']' :: rest)).length + 1
              = (encodeCellW a).toList.length + ((']' :: rest).length + 1) from by
            simp only [List.length_append]; omega]
        unfold encodeCellW
        simp only [String.toList_append, List.length_append]; omega))]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hwf hf
      rw [encCellsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCellsW.loop
      rw [parseCellW_encode a _ hwf.1 _ (le_trans (valueSize_le_encodeLen a.2) (by
        rw [show ((encodeCellW a).toList ++ (',' :: ((encodeCellW a2).toList ++ ((encodeCellsTail as2).toList ++ (']' :: rest))))).length + 1
              = (encodeCellW a).toList.length + ((',' :: ((encodeCellW a2).toList ++ ((encodeCellsTail as2).toList ++ (']' :: rest)))).length + 1) from by
            simp only [List.length_append]; omega]
        -- expose that `(encodeValueW a.2).length` is a summand of `(encodeCellW a).length`
        -- (else omega treats the cell-encoding as an opaque atom — same step the nil branch uses).
        unfold encodeCellW
        simp only [String.toList_append, List.length_append]; omega))]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCellW a2).toList ++ ((encodeCellsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hwf.2 hrec]

/-- **FILL J production (j): the WIDE `CELLS` array roundtrip** (`parseCellsW ∘ encodeCellsW = id`) — the
STATE DECODER's cell store, each element embedding the recursive `Value` payload (§5). Carries the §1
`WfCells` boundary (digests `< 2^256`, names escape-free); fuel-adequate whenever the OUTER loop fuel
exceeds the encoded width (the `parseWState` caller passes the whole-input length, so this is met). -/
theorem parseCellsW_encode (cs : List (CellId × Value)) (rest : PState) (hwf : WfCells cs)
    (fuel : Nat) (hf : ((encodeCellsW cs).toList ++ rest).length ≤ fuel) :
    parseCellsW fuel ((encodeCellsW cs).toList ++ rest) = some (cs, rest) := by
  cases cs with
  | nil =>
      unfold parseCellsW
      rw [show (encodeCellsW ([] : List (CellId × Value))) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseCellsW
      rw [encodeCellsW_cons_shape a as rest] at hf ⊢
      have hempty : lit "[]"
          ('[' :: ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCellW_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCellsW_loop_works as a rest _ hwf
      -- `hf` charges the `'['`-prefixed body; the loop wants the body itself (one byte shorter).
      -- Expose both as sums of the same length-atoms (`simp only`, leaf lengths) so omega aligns them.
      simp only [List.length_cons, List.length_append] at hf ⊢; omega

/-! ## §13 — the `CAPS` table (`parseCapsEntries`) roundtrip — the STATE DECODER's capability store.

Three NESTED length-fuel loops: the `CAPS` array `[[holder,CAPLIST],…]` whose element `parseCapEntry`
embeds a `CAPLIST` array `[CAP,…]` whose element `parseCap` is the 3-arm capability sum
(`{"null":0}`/`{"node":N}`/`{"ep":[N,AUTHS]}`) — the `ep` arm carrying a narrow `AUTHS` tag array
(§8's `parseAuths_encode`). No `Wf` hypothesis: `Cap` carries only `Nat` targets + narrow-`Auth` tags
(all total). Each loop is the §8 length-fuel recipe; the `CAP` element dispatches fail-closed via
`lit_ne_pre` over the three concrete tags, mirroring §6's `parseAuthW` arm walk. -/

/-- **One `CAP` round-trips** (`parseCap ∘ encodeCap = id`) — the 3-arm capability sum. `null` is a
single literal consume; `node`/`ep` fail the earlier tags (`lit_ne_pre`), open their tag, read the
target `Nat`, and (for `ep`) the rights `AUTHS` array via §8's `parseAuths_encode`, then close. The `ep`
encoder's trailing `]}` is the AUTHS-array close (consumed by `parseAuths`) then the two literal
closers. Self-delimiting. -/
theorem parseCap_encode (c : Authority.Cap) (rest : PState) :
    parseCap ((encodeCap c).toList ++ rest) = some (c, rest) := by
  cases c with
  | null =>
      unfold parseCap encodeCap
      rw [show (("{\"null\":0}":String).toList ++ rest) = ("{\"null\":0}":String).toList ++ rest from rfl,
        lit_append]
  | node t =>
      unfold parseCap encodeCap
      rw [show (("{\"node\":" ++ toString t ++ "}":String).toList ++ rest)
            = ("{\"node\":":String).toList ++ ((toString t).toList ++ ('}' :: rest)) from by
          simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
            List.append_assoc, List.cons_append, List.nil_append]]
      rw [lit_ne_pre "{\"null\":0}" "{\"node\":" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only []
      rw [parseNat_toString t ('}' :: rest) (nd_brace rest)]
      simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}' :: rest) = ("}":String).toList ++ rest from by
              simp only [show ("}":String).toList = ['}'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "}" rest]
      simp only [Option.map_some]
  | endpoint t r =>
      unfold parseCap encodeCap
      rw [show (("{\"ep\":[" ++ toString t ++ "," ++ encodeAuths r ++ "]}":String).toList ++ rest)
            = ("{\"ep\":[":String).toList ++ ((toString t).toList ++ (',' :: ((encodeAuths r).toList
                ++ (']' :: ('}' :: rest))))) from by
          simp only [String.toList_append, show (",":String).toList = [','] from by decide,
            show ("]}":String).toList = [']', '}'] from by decide, List.append_assoc, List.cons_append,
            List.nil_append]]
      rw [lit_ne_pre "{\"null\":0}" "{\"ep\":[" _ (by decide) (by decide)]
      simp only []
      rw [lit_ne_pre "{\"node\":" "{\"ep\":[" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only []
      rw [parseNat_toString t _ (nd_comma _)]
      simp only []
      rw [show lit "," (',' :: ((encodeAuths r).toList ++ (']' :: ('}' :: rest))))
            = some ((encodeAuths r).toList ++ (']' :: ('}' :: rest))) from by
          rw [show (',' :: ((encodeAuths r).toList ++ (']' :: ('}' :: rest))))
                = ("," : String).toList ++ ((encodeAuths r).toList ++ (']' :: ('}' :: rest))) from by
              simp only [show (",":String).toList = [','] from by decide, List.cons_append,
                List.nil_append]]
          exact lit_append "," _]
      simp only []
      rw [parseAuths_encode r (']' :: ('}' :: rest))]
      simp only []
      rw [show lit "]" (']' :: ('}' :: rest)) = some ('}' :: rest) from by
            rw [show (']' :: ('}' :: rest)) = ("]" : String).toList ++ ('}' :: rest) from by
              simp only [show ("]":String).toList = [']'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "]" _]
      simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}' :: rest) = ("}" : String).toList ++ rest from by
              simp only [show ("}":String).toList = ['}'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "}" rest]
      simp only [Option.map_some]
private def encodeCapListTail (cs : List Authority.Cap) : String :=
  cs.foldl (fun acc x => acc ++ "," ++ encodeCap x) ""

/-- Every `CAP` opens with `'{'` — the head char that makes `lit "[]"` fail on a `[{`-led `CAPLIST`. -/
private theorem encodeCap_head (c : Authority.Cap) : ∃ t, (encodeCap c).toList = '{' :: t := by
  cases c with
  | null => exact ⟨"\"null\":0}".toList, by unfold encodeCap; rfl⟩
  | node t => refine ⟨("\"node\":" ++ toString t ++ "}" : String).toList, ?_⟩
              unfold encodeCap
              simp only [String.toList_append, show ("{\"node\":":String).toList = '{' :: "\"node\":".toList from by decide,
                List.cons_append, List.nil_append, List.append_assoc]
  | endpoint t r => refine ⟨("\"ep\":[" ++ toString t ++ "," ++ encodeAuths r ++ "]}" : String).toList, ?_⟩
                    unfold encodeCap
                    simp only [String.toList_append, show ("{\"ep\":[":String).toList = '{' :: "\"ep\":[".toList from by decide,
                      List.cons_append, List.nil_append, List.append_assoc]

private theorem foldl_capListTail (cs : List Authority.Cap) : ∀ (acc : String),
    cs.foldl (fun s x => s ++ "," ++ encodeCap x) acc
      = acc ++ cs.foldl (fun s x => s ++ "," ++ encodeCap x) "" := by
  induction cs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCap b), ih ("" ++ "," ++ encodeCap b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCapListTail_cons_shape (b : Authority.Cap) (bs : List Authority.Cap) (rest : PState) :
    (encodeCapListTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCap b).toList ++ ((encodeCapListTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCapListTail (b :: bs) = ("" ++ "," ++ encodeCap b) ++ encodeCapListTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCap x) "" = _
      rw [List.foldl_cons]; exact foldl_capListTail bs ("" ++ "," ++ encodeCap b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCapList_cons_shape (a : Authority.Cap) (as : List Authority.Cap) (rest : PState) :
    (encodeCapList (a :: as)).toList ++ rest
      = '[' :: ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCapList (a :: as) = "[" ++ encodeCap a ++ encodeCapListTail as ++ "]" from by
        show "[" ++ encodeCap a ++ (as.foldl (fun acc x => acc ++ "," ++ encodeCap x) "") ++ "]" = _
        rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseCapList_loop_works : ∀ (as : List Authority.Cap) (a : Authority.Cap)
    (rest : PState) (fuel : Nat),
    ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest))).length < fuel →
    parseCapList.loop fuel ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCapListTail ([] : List Authority.Cap)).toList = [] from rfl, List.nil_append]
      unfold parseCapList.loop
      rw [parseCap_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encCapListTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCapList.loop
      rw [parseCap_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCap a2).toList ++ ((encodeCapListTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **The `CAPLIST` array roundtrip** (`parseCapList ∘ encodeCapList = id`) — a holder's cap list. -/
theorem parseCapList_encode (cs : List Authority.Cap) (rest : PState) :
    parseCapList ((encodeCapList cs).toList ++ rest) = some (cs, rest) := by
  cases cs with
  | nil =>
      unfold parseCapList
      rw [show (encodeCapList ([] : List Authority.Cap)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseCapList
      rw [encodeCapList_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCap_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '{' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCapList_loop_works as a rest
      simp only [List.length_cons]; omega

/-- The `CAPENTRY` encoder (the inline `one` lambda of `encodeCapsEntries`, named for the proof). -/
def encodeCapEntry (p : CellId × List Authority.Cap) : String :=
  "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]"

/-- **One `CAPENTRY` `[holder,CAPLIST]` round-trips** — the holder `Nat` (post-byte `,`) then the
`CAPLIST` via `parseCapList_encode`, then the closing `]` (`parseCapList` leaves its argument `rest`).
Self-delimiting. -/
theorem parseCapEntry_encode (p : CellId × List Authority.Cap) (rest : PState) :
    parseCapEntry ((encodeCapEntry p).toList ++ rest) = some (p, rest) := by
  obtain ⟨holder, cl⟩ := p
  unfold parseCapEntry encodeCapEntry
  rw [show (("[" ++ toString holder ++ "," ++ encodeCapList cl ++ "]":String).toList ++ rest)
        = ("[":String).toList ++ ((toString holder).toList ++ (',' :: ((encodeCapList cl).toList
            ++ (']' :: rest)))) from by
      simp only [String.toList_append, show (",":String).toList = [','] from by decide,
        show ("]":String).toList = [']'] from by decide, List.append_assoc, List.cons_append,
        List.nil_append]]
  rw [lit_append]
  simp only []
  rw [parseNat_toString holder _ (nd_comma _)]
  simp only []
  rw [show lit "," (',' :: ((encodeCapList cl).toList ++ (']' :: rest)))
        = some ((encodeCapList cl).toList ++ (']' :: rest)) from by
      rw [show (',' :: ((encodeCapList cl).toList ++ (']' :: rest)))
            = ("," : String).toList ++ ((encodeCapList cl).toList ++ (']' :: rest)) from by
          simp only [show (",":String).toList = [','] from by decide, List.cons_append,
            List.nil_append]]
      exact lit_append "," _]
  simp only []
  rw [parseCapList_encode cl (']' :: rest)]
  simp only []
  rw [show lit "]" (']' :: rest) = some rest from by
        rw [show (']' :: rest) = ("]" : String).toList ++ rest from by
          simp only [show ("]":String).toList = [']'] from by decide, List.cons_append,
            List.nil_append]]
        exact lit_append "]" rest]
  simp only [Option.map_some]

private def encodeCapsEntriesTail (es : List (CellId × List Authority.Cap)) : String :=
  es.foldl (fun acc x => acc ++ "," ++ encodeCapEntry x) ""

/-- A `CAPENTRY` opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeCapEntry_head (p : CellId × List Authority.Cap) : ∃ t, (encodeCapEntry p).toList = '[' :: t := by
  refine ⟨(toString p.1 ++ "," ++ encodeCapList p.2 ++ "]" : String).toList, ?_⟩
  unfold encodeCapEntry
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_capsEntriesTail (es : List (CellId × List Authority.Cap)) : ∀ (acc : String),
    es.foldl (fun s x => s ++ "," ++ encodeCapEntry x) acc
      = acc ++ es.foldl (fun s x => s ++ "," ++ encodeCapEntry x) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCapEntry b), ih ("" ++ "," ++ encodeCapEntry b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCapsEntriesTail_cons_shape (b : CellId × List Authority.Cap)
    (bs : List (CellId × List Authority.Cap)) (rest : PState) :
    (encodeCapsEntriesTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCapEntry b).toList ++ ((encodeCapsEntriesTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCapsEntriesTail (b :: bs) = ("" ++ "," ++ encodeCapEntry b) ++ encodeCapsEntriesTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCapEntry x) "" = _
      rw [List.foldl_cons]; exact foldl_capsEntriesTail bs ("" ++ "," ++ encodeCapEntry b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCapsEntries_cons_shape (a : CellId × List Authority.Cap)
    (as : List (CellId × List Authority.Cap)) (rest : PState) :
    (encodeCapsEntries (a :: as)).toList ++ rest
      = '[' :: ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCapsEntries (a :: as) = "[" ++ encodeCapEntry a ++ encodeCapsEntriesTail as ++ "]" from by
        show "[" ++ (fun (p : CellId × List Authority.Cap) => "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]") a
            ++ (as.foldl (fun acc p => acc ++ "," ++ (fun (p : CellId × List Authority.Cap) => "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]") p) "") ++ "]" = _
        rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseCapsEntries_loop_works : ∀ (as : List (CellId × List Authority.Cap))
    (a : CellId × List Authority.Cap) (rest : PState) (fuel : Nat),
    ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest))).length < fuel →
    parseCapsEntries.loop fuel ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCapsEntriesTail ([] : List (CellId × List Authority.Cap))).toList = [] from rfl, List.nil_append]
      unfold parseCapsEntries.loop
      rw [parseCapEntry_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encCapsEntriesTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCapsEntries.loop
      rw [parseCapEntry_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCapEntry a2).toList ++ ((encodeCapsEntriesTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (k): the `CAPS` table roundtrip** (`parseCapsEntries ∘ encodeCapsEntries = id`) —
the STATE DECODER's capability store: `(holder, capList)` entries, each cap a `null`/`node`/`ep` sum (the
`ep` arm carrying a narrow AUTHS rights array via §8). No `Wf` hypothesis (all `Nat`/narrow-tag). -/
theorem parseCapsEntries_encode (es : List (CellId × List Authority.Cap)) (rest : PState) :
    parseCapsEntries ((encodeCapsEntries es).toList ++ rest) = some (es, rest) := by
  cases es with
  | nil =>
      unfold parseCapsEntries
      rw [show (encodeCapsEntries ([] : List (CellId × List Authority.Cap))) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseCapsEntries
      rw [encodeCapsEntries_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCapEntry_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCapsEntries_loop_works as a rest
      simp only [List.length_cons]; omega
/-! ## §11d — the per-node `CAVEATS` array (`parseCaveatsW`) roundtrip — the SOUNDNESS-FIX discharge leg
(§W5c). The transported tiered caveat thread that gives `caveatsDischarged` real teeth over the swap
boundary. Length-fuel loop (§10/§11 template); the element is the SELF-DELIMITING `[tier,cell,asset,min]`
tuple (`parseCaveatW`), where `tier ∈ {0,1,2,3}` (the `DriftStable.DriftTier` ordinal) is the codec's ONE
boundary constraint — the parser's `if tier > 3 then none` guard rejects an out-of-range tier, so the
roundtrip carries a per-element `WfCaveat` (`c.tier ≤ 3`), exactly the §1-`WfValue`/§6-`WfAuthList`
boundary discipline. (`cell`/`asset` are unconstrained `Nat`; `min` is signed `Int` via `cI`.) A
caveat-codec bug — a dropped tier, a sign flip on the threshold, a mis-bracketed body — is now caught. -/

/-- The per-caveat well-formedness boundary: the `tier` ordinal is in `{0,1,2,3}` (the four
`DriftStable.DriftTier` levels). This is exactly the constraint `parseCaveatW`'s `if tier > 3` guard
pins; the encoder writes the tier verbatim, so the round-trip holds precisely on well-formed tiers. -/
def WfCaveat (c : WCaveat) : Prop := c.tier ≤ 3

/-- A `CAVEATS` array is well-formed iff every caveat is (every `tier ∈ {0,1,2,3}`). -/
def WfCaveats : List WCaveat → Prop
  | []      => True
  | c :: cs => WfCaveat c ∧ WfCaveats cs

set_option maxHeartbeats 1000000 in
/-- **The `WCAVEAT` entry roundtrip** — the 4-field tuple `[tier,cell,asset,min]`. The leading `tier`
walks via `parseNat` (post-byte `,`); its `if tier > 3` guard is discharged `else`-ward by `htier`
(`c.tier ≤ 3`, so `¬ (3 < c.tier)`). The `cell`/`asset` `Nat`s and signed `min` `Int` walk via
`cN_step`/`cI_step` (post-byte `,`/`]`); self-delimiting, so it round-trips for ANY tail. -/
theorem parseCaveatW_encode (c : WCaveat) (rest : PState) (htier : WfCaveat c) :
    parseCaveatW ((encodeCaveatW c).toList ++ rest) = some (c, rest) := by
  unfold parseCaveatW encodeCaveatW WfCaveat at *
  simp only [String.toList_append, List.append_assoc]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString c.tier _ (nd_litComma _)]; simp only [Option.bind]
  rw [if_neg (by omega : ¬ c.tier > 3)]
  simp only [cN_step _ _ (nd_litComma _), cI_step _ _ (nd_litBrack _), Option.bind_eq_bind, Option.bind]
  rw [lit_append]

private def encodeCaveatsWTail (cs : List WCaveat) : String :=
  cs.foldl (fun acc x => acc ++ "," ++ encodeCaveatW x) ""

/-- A `WCAVEAT` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). Explicit
witness ⇒ no metavar. -/
private theorem encodeCaveatW_head (c : WCaveat) : ∃ t, (encodeCaveatW c).toList = '[' :: t := by
  refine ⟨(toString c.tier ++ "," ++ toString c.cell ++ "," ++ toString c.asset ++ ","
    ++ toString c.min ++ "]" : String).toList, ?_⟩
  unfold encodeCaveatW
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_caveatsWTail (cs : List WCaveat) : ∀ (acc : String),
    cs.foldl (fun s x => s ++ "," ++ encodeCaveatW x) acc
      = acc ++ cs.foldl (fun s x => s ++ "," ++ encodeCaveatW x) "" := by
  induction cs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCaveatW b), ih ("" ++ "," ++ encodeCaveatW b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCaveatsWTail_cons_shape (b : WCaveat) (bs : List WCaveat) (rest : PState) :
    (encodeCaveatsWTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCaveatW b).toList ++ ((encodeCaveatsWTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCaveatsWTail (b :: bs) = ("" ++ "," ++ encodeCaveatW b) ++ encodeCaveatsWTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCaveatW x) "" = _
      rw [List.foldl_cons]; exact foldl_caveatsWTail bs ("" ++ "," ++ encodeCaveatW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCaveatsW_cons_shape (a : WCaveat) (as : List WCaveat) (rest : PState) :
    (encodeCaveatsW (a :: as)).toList ++ rest
      = '[' :: ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCaveatsW (a :: as) = "[" ++ encodeCaveatW a ++ encodeCaveatsWTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The loop recovers the caveat list**, given the `input.length < fuel` invariant AND that every
caveat is well-formed (each `tier ≤ 3`, threaded through `parseCaveatW_encode`). By induction on the
tail (the head `a` generalized); the recursive call lands at `fuel-1` with strictly-shorter input. -/
private theorem parseCaveatsW_loop_works : ∀ (as : List WCaveat) (a : WCaveat)
    (rest : PState) (fuel : Nat), WfCaveat a → WfCaveats as →
    ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest))).length < fuel →
    parseCaveatsW.loop fuel ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hwfa _ hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCaveatsWTail ([] : List WCaveat)).toList = [] from rfl, List.nil_append]
      unfold parseCaveatsW.loop
      rw [parseCaveatW_encode a (']' :: rest) hwfa]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hwfa hwfas hf
      obtain ⟨hwfa2, hwfas2⟩ : WfCaveat a2 ∧ WfCaveats as2 := hwfas
      rw [encCaveatsWTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCaveatsW.loop
      rw [parseCaveatW_encode a _ hwfa]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCaveatW a2).toList ++ ((encodeCaveatsWTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hwfa2 hwfas2 hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (l): the per-node `CAVEATS` array roundtrip** (`parseCaveatsW ∘ encodeCaveatsW =
id`) — the SOUNDNESS-FIX discharge leg (§W5c). The transported tiered caveat thread, round-tripped
FAITHFULLY (every `tier ∈ {0,1,2,3}` via `WfCaveats`; a dropped tier / sign-flipped threshold is caught),
so a violated caveat fail-closes the gate over the swap boundary. -/
theorem parseCaveatsW_encode (cs : List WCaveat) (rest : PState) (hwf : WfCaveats cs) :
    parseCaveatsW ((encodeCaveatsW cs).toList ++ rest) = some (cs, rest) := by
  cases cs with
  | nil =>
      unfold parseCaveatsW
      rw [show (encodeCaveatsW ([] : List WCaveat)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      obtain ⟨hwfa, hwfas⟩ : WfCaveat a ∧ WfCaveats as := hwf
      unfold parseCaveatsW
      rw [encodeCaveatsW_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCaveatW_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCaveatsW_loop_works as a rest _ hwfa hwfas
      simp only [List.length_cons]; omega

/-- NON-VACUITY: a real tiered caveat list round-trips (a `.locked`/tier-2 threshold and a `.monotone`/
tier-0 read, the `min` a NEGATIVE bound — the sign is load-bearing). -/
example : parseCaveatsW ((encodeCaveatsW
    [{ tier := 2, cell := 7, asset := 3, min := -5 }, { tier := 0, cell := 1, asset := 1, min := 9 }]).toList
      ++ ['x'])
    = some ([{ tier := 2, cell := 7, asset := 3, min := -5 }, { tier := 0, cell := 1, asset := 1, min := 9 }], ['x']) :=
  -- `WfCaveats [c₁,c₂]` is DEFINITIONALLY `c₁.tier ≤ 3 ∧ c₂.tier ≤ 3 ∧ True`; give each leaf as the
  -- bare `≤` (whnf checks it against the folded `WfCaveat` — avoids needing a `Decidable (WfCaveat …)`).
  parseCaveatsW_encode _ ['x'] ⟨(by decide : (2:Nat) ≤ 3), (by decide : (0:Nat) ≤ 3), trivial⟩

end Dregg2.Exec.CodecRoundtrip
