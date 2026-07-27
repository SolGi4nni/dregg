import Reactor.Pipeline
import Reactor.Stage.MultiRange
import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.HttpDateOrder — the HTTP-date total order (RFC 9110 §5.6.7)

The pure kernel behind the date-driven conditional requests (`If-Modified-Since`
/ `If-Unmodified-Since`, RFC 9110 §13.1.3/§13.1.4): a parser from the IMF-fixdate
wire form (`Sun, 06 Nov 1994 08:49:37 GMT`) to a single `Nat` **order scalar**,
so every date comparison the conditional stages need is `Nat.le` — a genuine
total order (reflexive, transitive, antisymmetric, total) for free.

The scalar is the lexicographic packing of `(year, month, day, hour, min, sec)`
with per-field radixes strictly above each field's calendar range (`12+`, `32 >
31`, `24`, `60`, `60`), so scalar order coincides with chronological order for
every valid calendar date (`encode_lt_of_year_lt` and its field siblings state
the monotonicity; the packing is injective on in-range fields).

Fail-closed: anything that is not a well-formed IMF-fixdate parses to `none`,
and a `none` never fires a conditional (RFC 9110 §13.1.3: "A recipient MUST
ignore the If-Modified-Since header field if … not a valid HTTP-date"). The
obsolete RFC 850 / asctime forms (§5.6.7 obs-date) parse to `none` — a NAMED
residual: they are ignored rather than honored, which is the conservative
(condition-not-firing) direction.

Everything here is `by decide` / `omega` on explicit ASCII byte lists — pure
kernel, no `native_decide`, no `ofReduceBool`.
-/

namespace Reactor.Stage.HttpDateOrder

open Proto (Bytes)
open Reactor.Stage.MultiRange (parseNatB lower)
open Reactor.Stage.FramingValidation (splitOn trimOWS)

/-! ## Tokens -/

/-- ASCII space. -/
def bSP : UInt8 := 32
/-- ASCII colon. -/
def bCOLON : UInt8 := 58
/-- `gmt` (lowercase — the zone token, matched case-insensitively). -/
def gmtTok : Bytes := [103, 109, 116]

/-- The 1-based calendar index of a (lowercased) month token (`jan` … `dec`);
`none` otherwise. -/
def monthIdx (m : Bytes) : Option Nat :=
  if m == [106, 97, 110] then some 1        -- jan
  else if m == [102, 101, 98] then some 2   -- feb
  else if m == [109, 97, 114] then some 3   -- mar
  else if m == [97, 112, 114] then some 4   -- apr
  else if m == [109, 97, 121] then some 5   -- may
  else if m == [106, 117, 110] then some 6  -- jun
  else if m == [106, 117, 108] then some 7  -- jul
  else if m == [97, 117, 103] then some 8   -- aug
  else if m == [115, 101, 112] then some 9  -- sep
  else if m == [111, 99, 116] then some 10  -- oct
  else if m == [110, 111, 118] then some 11 -- nov
  else if m == [100, 101, 99] then some 12  -- dec
  else none

/-! ## The order scalar -/

/-- Lexicographic packing of the six calendar fields. Each radix strictly
exceeds its field's calendar range (months 1–12 < 13, days 1–31 < 32, hours
0–23 < 24, minutes/seconds 0–59 < 60), so packed order = field-lex order =
chronological order on valid dates. -/
def encode (y mo d h mi s : Nat) : Nat :=
  ((((y * 13 + mo) * 32 + d) * 24 + h) * 60 + mi) * 60 + s

/-- Parse `hh:mm:ss` (already OWS-trimmed) to its three fields. -/
def parseTime (t : Bytes) : Option (Nat × Nat × Nat) :=
  match splitOn bCOLON t with
  | [th, tm, ts] =>
    match parseNatB th, parseNatB tm, parseNatB ts with
    | some h, some mi, some s => some (h, mi, s)
    | _, _, _ => none
  | _ => none

/-- **Parse an IMF-fixdate HTTP-date to its order scalar.** Wire form
`Day, dd Mon yyyy hh:mm:ss GMT` — the day-name is ignored (it is redundant
data; RFC 9110 §5.6.7), month and zone match case-insensitively, and every
malformed shape is `none` (fail-closed). -/
def dateVal (v : Bytes) : Option Nat :=
  match splitOn bSP (trimOWS v) with
  | [_day, dd, mon, yyyy, time, zone] =>
    if lower zone == gmtTok then
      match parseNatB dd, monthIdx (lower mon), parseNatB yyyy, parseTime time with
      | some d, some mo, some y, some (h, mi, s) => some (encode y mo d h mi s)
      | _, _, _, _ => none
    else none
  | _ => none

/-! ## The total order (inherited from `Nat` — the point of the scalar) -/

/-- Scalar comparison — the decision the conditional stages run. -/
def dateLe (a b : Nat) : Bool := decide (a ≤ b)

theorem dateLe_refl (a : Nat) : dateLe a a = true := by simp [dateLe]

theorem dateLe_trans {a b c : Nat} (h1 : dateLe a b = true)
    (h2 : dateLe b c = true) : dateLe a c = true := by
  simp only [dateLe, decide_eq_true_eq] at *
  exact Nat.le_trans h1 h2

theorem dateLe_antisymm {a b : Nat} (h1 : dateLe a b = true)
    (h2 : dateLe b a = true) : a = b := by
  simp only [dateLe, decide_eq_true_eq] at *
  exact Nat.le_antisymm h1 h2

/-- **Totality** — every pair of parsed HTTP-dates is comparable. -/
theorem dateLe_total (a b : Nat) : dateLe a b = true ∨ dateLe b a = true := by
  simp only [dateLe, decide_eq_true_eq]
  exact Nat.le_total a b

/-! ## Chronological faithfulness (field monotonicity, in-range) -/

/-- A later year is a later scalar, for ANY in-range remaining fields. -/
theorem encode_lt_of_year_lt {y1 y2 mo1 mo2 d1 d2 h1 h2 mi1 mi2 s1 s2 : Nat}
    (hy : y1 < y2)
    (hmo1 : mo1 ≤ 12) (hd1 : d1 ≤ 31) (hh1 : h1 ≤ 23) (hmi1 : mi1 ≤ 59) (hs1 : s1 ≤ 59)
    (hmo2 : 1 ≤ mo2) (hd2 : 1 ≤ d2) :
    encode y1 mo1 d1 h1 mi1 s1 < encode y2 mo2 d2 h2 mi2 s2 := by
  unfold encode; omega

/-- Same year, later month ⇒ later scalar, for ANY in-range remaining fields. -/
theorem encode_lt_of_month_lt {y mo1 mo2 d1 d2 h1 h2 mi1 mi2 s1 s2 : Nat}
    (hmo : mo1 < mo2)
    (hd1 : d1 ≤ 31) (hh1 : h1 ≤ 23) (hmi1 : mi1 ≤ 59) (hs1 : s1 ≤ 59)
    (hd2 : 1 ≤ d2) :
    encode y mo1 d1 h1 mi1 s1 < encode y mo2 d2 h2 mi2 s2 := by
  unfold encode; omega

/-- Same year+month, later day ⇒ later scalar, in-range. -/
theorem encode_lt_of_day_lt {y mo d1 d2 h1 h2 mi1 mi2 s1 s2 : Nat}
    (hd : d1 < d2) (hh1 : h1 ≤ 23) (hmi1 : mi1 ≤ 59) (hs1 : s1 ≤ 59) :
    encode y mo d1 h1 mi1 s1 < encode y mo d2 h2 mi2 s2 := by
  unfold encode; omega

/-! ## Concrete wire witnesses (the probe's exact date bytes) -/

/-- `Sat, 01 Jan 2050 00:00:00 GMT` — the far-future probe date. -/
def wireFuture : Bytes :=
  [83, 97, 116, 44, 32, 48, 49, 32, 74, 97, 110, 32, 50, 48, 53, 48, 32,
   48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84]

/-- `Thu, 01 Jan 1970 00:00:00 GMT` — the far-past probe date. -/
def wirePast : Bytes :=
  [84, 104, 117, 44, 32, 48, 49, 32, 74, 97, 110, 32, 49, 57, 55, 48, 32,
   48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84]

/-- Both probe dates parse, and past < future in the scalar order — the exact
comparison the `If-Modified-Since`/`If-Unmodified-Since` verdicts run. -/
theorem wire_dates_ordered :
    ∃ p f, dateVal wirePast = some p ∧ dateVal wireFuture = some f ∧ p < f := by
  refine ⟨encode 1970 1 1 0 0 0, encode 2050 1 1 0 0 0, by decide, by decide, ?_⟩
  exact encode_lt_of_year_lt (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)

/-- `Sun Nov  6 08:49:37 1994` — the obsolete asctime shape. -/
def wireAsctime : Bytes :=
  [83, 117, 110, 32, 78, 111, 118, 32, 32, 54, 32, 48, 56, 58, 52, 57, 58,
   51, 55, 32, 49, 57, 57, 52]

/-- A non-fixdate never parses (fail-closed): the asctime form is ignored,
never honored — the conservative, condition-not-firing direction. -/
theorem wire_asctime_rejected : dateVal wireAsctime = none := by decide

end Reactor.Stage.HttpDateOrder
