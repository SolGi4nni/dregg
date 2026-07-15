/-
  Pancake/ServeSlice.lean — the FIRST non-stub REAL serve SLICE compiled by the
  translator END-TO-END, proven byte-identical to the reference (leanc-faithful)
  serializer on a request corpus.

  This file ASSEMBLES the two translator halves that were previously built and
  proven in isolation:

    W1 (decision stages, Stack L, no bytes) — `Pancake/ServeFragment.lean`:
        the loop-free serve-stage grammar auto-produces `Refines` certificates
        for real decision stages (security-headers, method-filter routing, …).

    W2 (response construction, memory post-state) — `Pancake/SerializeCompile.lean`:
        the bounded WRITE loop `copyWhile` materialises `serialize resp` into an
        output byte-region (`serialize_write_correct` : `MemBytesAt s' base_out
        (serialize resp)`).

  THE SLICE. A minimal real serve: parse a request enough to ROUTE (the method
  tag), run TWO stages, and CONSTRUCT the real response into memory:

    1. SECURITY-HEADERS stage — `emit securityHeadersDecision` (W1), executed
       through the translator's emitted program (sets the header-present locals).
       Its WIRE effect (the deployed HSTS / X-Frame-Options / X-Content-Type
       headers) is carried in BOTH response templates, so it appears in the
       output bytes.

    2. METHOD-FILTER routing — the emitted `If (Cmp Less (Var "method") 4) …`
       (the exact shape `emit methodFilterDecision` produces): an allowed method
       (`tag < 4`, i.e. GET/POST/HEAD/OPTIONS pre-decoded to `{0,1,2,3}`) is
       served `200 OK`; any other method is refused `405 Method Not Allowed` with
       the RFC-9110 §10.2.1 `Allow` header. The routing GENUINELY drives the
       output: the machine's branch materialises DIFFERENT response bytes.

    3. RESPONSE CONSTRUCTION — the selected response is serialized into the output
       region by `copyWhile` (W2), byte for byte.

  THE THEOREM. `serveSlice_correct` : running the ONE composed emitted Pancake
  program `serveSliceProg` from an entry state that encodes the request (method
  tag) and holds both response templates in memory lands the model memory with
  the output region at `base_out` equal, byte for byte, to
  `serialize (if tag < 4 then resp200 else resp405)` — the response the slice
  routes to. The postcondition is a genuine memory effect (`MemBytesAt`), the
  guard is `signedLt tag 4` (the real routing), and the two branches serialize
  DISTINCT responses. NOT `P → P`.

  BYTE-IDENTITY TO leanc. §5 transcribes the reference serializer with the
  leanc-faithful `Nat.repr`-based decimal render (`refSerialize`, the shape the
  deployed `Reactor.serialize` compiles) and `#guard`s
  `serialize resp = refSerialize resp` on the whole corpus — the translator's
  serializer emits the SAME bytes the leanc serve does. Combined with
  `serveSlice_correct`, the compiled program's output region byte-for-byte equals
  the leanc serve output on the slice.

  FAITHFULNESS RESIDUALS (named, not hidden):
   * The security-headers stage is EXECUTED (its emitted program composes into
     `serveSliceProg`, proven via `securityHeadersDecision_cert`) but its
     header-present LOCALS do not yet DRIVE the serialized header list — the
     headers are carried in the response templates. Wiring the flag-writes into
     the serialize input is the store-loop-over-header-structure residual named in
     `SerializeCompile.lean` §MEMORY MODEL.
   * The two response templates are pre-loaded into two source regions; the
     machine's routing branch selects WHICH region `copyWhile` copies. That is a
     faithful static-response serve (two templates in memory, the router picks
     one); a handler that BUILDS the body dynamically is the deeper residual.
   * `refSerialize` matches the translator `serialize` on the corpus by `#guard`;
     the SYNTACTIC `natToDec = Nat.repr` lemma (all inputs) is the open obligation
     named in `SerializeCompile.lean` §1.

  This is Stack L (the Lean model of Pancake) + a memory post-state claim.

  ASSURANCE. `#print axioms serveSlice_correct` is ⊆ {propext, Quot.sound,
  Classical.choice}; 0 `sorry`, 0 `native_decide`, 0 `ofReduceBool`.
  Build: `Pancake/build_serveslice.sh`.
-/
import Pancake.ServeFragment
import Pancake.SerializeCompile

namespace Pancake.ServeSlice

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.EmitCorrectClock
     Pancake.ProofProducing Pancake.ServeFragment Pancake.SerializeCompile

variable {σ : Type}

/-! ## 0. Reduction plumbing (clock-clamp collapse for clock-preserving heads) -/

/-- A `Seq` whose head terminates normally AND preserves the clock reduces to the
tail run on the head's post-state: the `fix_clock` clamp `min s.clock s1.clock`
collapses to `s1.clock`, and `{ s1 with clock := s1.clock }` is `s1` by structure
eta. -/
theorem seq_clk_collapse (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 : PancakeState σ}
    (h : PancakeSem o c1 s = (none, s1)) (hc : s1.clock = s.clock) :
    PancakeSem o (.seq c1 c2) s = PancakeSem o c2 s1 := by
  rw [sem_seq_none h]
  have hm : min s.clock s1.clock = s1.clock := by omega
  rw [hm]

/-- The routing branch `src := srcX ; len := lenX` runs to the state with both
locals set (clock preserved). -/
theorem branch_reduce (o : Oracle σ) (src : Word) (len : Nat) (s1 : PancakeState σ) :
    PancakeSem o (.seq (.assign "src" (.const src))
        (.assign "len" (.const (BitVec.ofNat 64 len)))) s1
      = (none, { s1 with locals := setLocal (setLocal s1.locals "src" src) "len" (BitVec.ofNat 64 len) }) := by
  have h1 : PancakeSem o (.assign "src" (.const src)) s1
      = (none, { s1 with locals := setLocal s1.locals "src" src }) := sem_assign rfl
  rw [seq_clk_collapse o h1 rfl]
  exact sem_assign rfl

/-! ## 1. The security-headers stage's effect (from its W1 certificate)

`denote securityHeadersDecision` sets the three header-present locals and touches
NOTHING else — the value the emitted program computes, by
`securityHeadersDecision_cert`. -/

/-- The emitted security-headers program (its AST is σ-independent, so it is
pinned at `Unit`; the emitted `Assign`s carry no `σ`). -/
def secProg : PancakeProg := emit (securityHeadersDecision (σ := Unit))

/-- The emitted security-headers program runs to `denote securityHeadersDecision`
and preserves the clock (this IS the W1 certificate, unfolded; `secProg` is
`emit …` up to the σ-erasure defeq). -/
theorem sec_reduce (o : Oracle σ) (s : PancakeState σ) :
    PancakeSem o secProg s = (none, denote (securityHeadersDecision (σ := σ)) s)
      ∧ (denote (securityHeadersDecision (σ := σ)) s).clock = s.clock :=
  securityHeadersDecision_cert o s

/-- `denote securityHeadersDecision s` is `s` with three locals set. -/
theorem denote_sec_eq (s : PancakeState σ) :
    denote (securityHeadersDecision (σ := σ)) s
      = { s with locals := setLocal (setLocal (setLocal s.locals "hsts" 1) "xfo" 1) "nosniff" 1 } := rfl

/-! ## 2. The composed serve-slice program (the translator's output)

`serveSliceProg` is ONE emitted Pancake program:

    emit securityHeadersDecision ;                 -- W1 stage (executed)
    ( if (method < 4)                              -- W1 method-filter routing shape
        then (src := src200 ; len := len200)
        else (src := src405 ; len := len405) ) ;
    copyWhile                                       -- W2 response write loop

The entry state holds `serialize resp200` at `src200` and `serialize resp405` at
`src405`; the routing branch points the shared `copyWhile` frame at the selected
region, and the write loop materialises those bytes into `base_out`. -/
def serveSliceProg (base_out src200 src405 : Word) (resp200 resp405 : Response) : PancakeProg :=
  .seq secProg
    (.seq
      (.cond (.cmp .less (.var "method") (.const 4))
        (.seq (.assign "src" (.const src200))
          (.assign "len" (.const (BitVec.ofNat 64 (serialize resp200).length))))
        (.seq (.assign "src" (.const src405))
          (.assign "len" (.const (BitVec.ofNat 64 (serialize resp405).length)))))
      copyWhile)

/-! ## 3. The end-to-end byte-identity theorem -/

/-- **THE PAYOFF.** The composed emitted serve-slice program, run from an entry
state that encodes the request (`method = tag`) and holds both serialized response
templates in memory (`src200`/`src405` regions), routes on `signedLt tag 4` and
lands the model memory with the output region at `base_out` equal, byte for byte,
to `serialize (if tag < 4 then resp200 else resp405)` — the response the slice
serves. Side conditions are exactly a router's + a memcpy's: the loop frame
(`dst = base_out`, `i = 0`), the response lengths in signed range, the output
region addressable/disjoint/self-distinct, both source regions loaded with the
serialized templates, and the iteration budget. -/
theorem serveSlice_correct (o : Oracle σ) (tag base_out src200 src405 : Word)
    (resp200 resp405 : Response) (s : PancakeState σ)
    (hmethod : s.locals "method" = some tag)
    (hdst : s.locals "dst" = some base_out)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hlen200 : (serialize resp200).length < 2 ^ 63)
    (hlen405 : (serialize resp405).length < 2 ^ 63)
    (hclock : max (serialize resp200).length (serialize resp405).length ≤ s.clock)
    (hsrc200 : ∀ j, j < (serialize resp200).length →
        s.memaddrs (src200 + BitVec.ofNat 64 j) = true ∧
        s.memory (src200 + BitVec.ofNat 64 j) = wordOfByte (serialize resp200)[j]!)
    (hsrc405 : ∀ j, j < (serialize resp405).length →
        s.memaddrs (src405 + BitVec.ofNat 64 j) = true ∧
        s.memory (src405 + BitVec.ofNat 64 j) = wordOfByte (serialize resp405)[j]!)
    (hdstA : ∀ j, j < max (serialize resp200).length (serialize resp405).length →
        s.memaddrs (base_out + BitVec.ofNat 64 j) = true)
    (hdisj200 : ∀ i j, i < (serialize resp200).length → j < (serialize resp200).length →
        base_out + BitVec.ofNat 64 i ≠ src200 + BitVec.ofNat 64 j)
    (hdisj405 : ∀ i j, i < (serialize resp405).length → j < (serialize resp405).length →
        base_out + BitVec.ofNat 64 i ≠ src405 + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < max (serialize resp200).length (serialize resp405).length →
        j < max (serialize resp200).length (serialize resp405).length → i ≠ j →
        base_out + BitVec.ofNat 64 i ≠ base_out + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (serveSliceProg base_out src200 src405 resp200 resp405) s = (none, s') ∧
      MemBytesAt s' base_out (serialize (if signedLt tag 4 then resp200 else resp405)) := by
  -- ---- Run the security-headers stage; name the post-state s1. ----
  obtain ⟨hsec_eq, hsec_clk⟩ := sec_reduce o s
  obtain ⟨s1, hs1⟩ : ∃ t, t = denote (securityHeadersDecision (σ := σ)) s := ⟨_, rfl⟩
  rw [← hs1] at hsec_eq hsec_clk
  -- field facts on s1 (only hsts/xfo/nosniff locals changed)
  have hs1_method : s1.locals "method" = some tag := by
    rw [hs1, denote_sec_eq]; simp [setLocal]; exact hmethod
  have hs1_dst : s1.locals "dst" = some base_out := by
    rw [hs1, denote_sec_eq]; simp [setLocal]; exact hdst
  have hs1_i : s1.locals "i" = some (BitVec.ofNat 64 0) := by
    rw [hs1, denote_sec_eq]; simp [setLocal]; exact hi
  have hs1_mem : s1.memory = s.memory := by rw [hs1, denote_sec_eq]
  have hs1_ma : s1.memaddrs = s.memaddrs := by rw [hs1, denote_sec_eq]
  have hs1_clk : s1.clock = s.clock := hsec_clk
  -- collapse the outer Seq (security head, clock-preserving)
  have hstep1 : PancakeSem o (serveSliceProg base_out src200 src405 resp200 resp405) s
      = PancakeSem o (.seq
          (.cond (.cmp .less (.var "method") (.const 4))
            (.seq (.assign "src" (.const src200))
              (.assign "len" (.const (BitVec.ofNat 64 (serialize resp200).length))))
            (.seq (.assign "src" (.const src405))
              (.assign "len" (.const (BitVec.ofNat 64 (serialize resp405).length)))))
          copyWhile) s1 := by
    rw [serveSliceProg]
    exact seq_clk_collapse o hsec_eq hs1_clk
  -- the routing guard evaluates to the branch boolean
  have hguard : eval s1 (.cmp .less (.var "method") (.const 4))
      = some (if signedLt tag 4 then (1 : Word) else 0) := by
    simp only [eval, hs1_method]
  -- ---- Case split on the route. ----
  by_cases hb : signedLt tag 4
  · -- ALLOWED: tag < 4 → 200 OK (resp200)
    -- reduce the cond to branch200
    have hcond : PancakeSem o
        (.cond (.cmp .less (.var "method") (.const 4))
          (.seq (.assign "src" (.const src200))
            (.assign "len" (.const (BitVec.ofNat 64 (serialize resp200).length))))
          (.seq (.assign "src" (.const src405))
            (.assign "len" (.const (BitVec.ofNat 64 (serialize resp405).length))))) s1
        = (none, { s1 with locals := setLocal (setLocal s1.locals "src" src200) "len" (BitVec.ofNat 64 (serialize resp200).length) }) := by
      rw [sem_cond o hguard, if_pos hb, if_pos (show (1 : Word) ≠ 0 by decide)]
      exact branch_reduce o src200 (serialize resp200).length s1
    obtain ⟨s2, hs2⟩ : ∃ t, t = ({ s1 with locals := setLocal (setLocal s1.locals "src" src200) "len" (BitVec.ofNat 64 (serialize resp200).length) } : PancakeState σ) := ⟨_, rfl⟩
    rw [← hs2] at hcond
    -- field facts on s2
    have hs2_dst : s2.locals "dst" = some base_out := by rw [hs2]; simp [setLocal]; exact hs1_dst
    have hs2_src : s2.locals "src" = some src200 := by rw [hs2]; simp [setLocal]
    have hs2_i : s2.locals "i" = some (BitVec.ofNat 64 0) := by rw [hs2]; simp [setLocal]; exact hs1_i
    have hs2_len : s2.locals "len" = some (BitVec.ofNat 64 (serialize resp200).length) := by
      rw [hs2]; simp [setLocal]
    have hs2_mem : s2.memory = s.memory := by rw [hs2]; exact hs1_mem
    have hs2_ma : s2.memaddrs = s.memaddrs := by rw [hs2]; exact hs1_ma
    have hs2_clk : s2.clock = s.clock := by rw [hs2]; exact hs1_clk
    -- collapse the inner Seq (routing head, clock-preserving)
    have hstep2 : PancakeSem o (serveSliceProg base_out src200 src405 resp200 resp405) s
        = PancakeSem o copyWhile s2 := by
      rw [hstep1, seq_clk_collapse o hcond (hs2_clk.trans hs1_clk.symm)]
    -- run copyWhile via the W2 write-loop correctness on resp200
    obtain ⟨s', hs'eq, hpost⟩ := serialize_write_correct o resp200 base_out src200 s2
      hlen200
      (by intro i j hi hj; exact hdisj200 i j hi hj)
      (by intro i j hi hj hij; exact hinj i j (by omega) (by omega) hij)
      hs2_dst hs2_src hs2_i hs2_len
      (by rw [hs2_clk]; omega)
      (by intro j hj; rw [hs2_ma, hs2_mem]; exact hsrc200 j hj)
      (by intro j hj; rw [hs2_ma]; exact hdstA j (by omega))
    refine ⟨s', by rw [hstep2]; exact hs'eq, ?_⟩
    rw [if_pos hb]; exact hpost
  · -- REFUSED: tag ≥ 4 → 405 Method Not Allowed (resp405)
    have hcond : PancakeSem o
        (.cond (.cmp .less (.var "method") (.const 4))
          (.seq (.assign "src" (.const src200))
            (.assign "len" (.const (BitVec.ofNat 64 (serialize resp200).length))))
          (.seq (.assign "src" (.const src405))
            (.assign "len" (.const (BitVec.ofNat 64 (serialize resp405).length))))) s1
        = (none, { s1 with locals := setLocal (setLocal s1.locals "src" src405) "len" (BitVec.ofNat 64 (serialize resp405).length) }) := by
      rw [sem_cond o hguard, if_neg hb, if_neg (show ¬((0 : Word) ≠ 0) by decide)]
      exact branch_reduce o src405 (serialize resp405).length s1
    obtain ⟨s2, hs2⟩ : ∃ t, t = ({ s1 with locals := setLocal (setLocal s1.locals "src" src405) "len" (BitVec.ofNat 64 (serialize resp405).length) } : PancakeState σ) := ⟨_, rfl⟩
    rw [← hs2] at hcond
    have hs2_dst : s2.locals "dst" = some base_out := by rw [hs2]; simp [setLocal]; exact hs1_dst
    have hs2_src : s2.locals "src" = some src405 := by rw [hs2]; simp [setLocal]
    have hs2_i : s2.locals "i" = some (BitVec.ofNat 64 0) := by rw [hs2]; simp [setLocal]; exact hs1_i
    have hs2_len : s2.locals "len" = some (BitVec.ofNat 64 (serialize resp405).length) := by
      rw [hs2]; simp [setLocal]
    have hs2_mem : s2.memory = s.memory := by rw [hs2]; exact hs1_mem
    have hs2_ma : s2.memaddrs = s.memaddrs := by rw [hs2]; exact hs1_ma
    have hs2_clk : s2.clock = s.clock := by rw [hs2]; exact hs1_clk
    have hstep2 : PancakeSem o (serveSliceProg base_out src200 src405 resp200 resp405) s
        = PancakeSem o copyWhile s2 := by
      rw [hstep1, seq_clk_collapse o hcond (hs2_clk.trans hs1_clk.symm)]
    obtain ⟨s', hs'eq, hpost⟩ := serialize_write_correct o resp405 base_out src405 s2
      hlen405
      (by intro i j hi hj; exact hdisj405 i j hi hj)
      (by intro i j hi hj hij; exact hinj i j (by omega) (by omega) hij)
      hs2_dst hs2_src hs2_i hs2_len
      (by rw [hs2_clk]; omega)
      (by intro j hj; rw [hs2_ma, hs2_mem]; exact hsrc405 j hj)
      (by intro j hj; rw [hs2_ma]; exact hdstA j (by omega))
    refine ⟨s', by rw [hstep2]; exact hs'eq, ?_⟩
    rw [if_neg hb]; exact hpost

/-! ## 4. The concrete corpus responses (the mini-serve outputs)

Faithful bytes for the two routed responses. The security-headers are the
deployed policy set (HSTS + `X-Frame-Options: DENY` + `X-Content-Type-Options:
nosniff`); the `405` additionally carries the RFC-9110 §10.2.1 `Allow` header. -/

/-- ASCII byte string of a Lean `String`. -/
def sb (s : String) : Bytes := s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- The deployed response-security header set. -/
def secHeaders : List (Bytes × Bytes) :=
  [ (sb "Strict-Transport-Security", sb "max-age=63072000; includeSubDomains")
  , (sb "X-Frame-Options",           sb "DENY")
  , (sb "X-Content-Type-Options",    sb "nosniff") ]

/-- `200 OK`, carrying the security headers, with a small body. -/
def resp200 : Response :=
  { status := 200, reason := sb "OK", headers := secHeaders, body := sb "hello\n" }

/-- `405 Method Not Allowed`, carrying the `Allow` header + the security headers. -/
def resp405 : Response :=
  { status := 405, reason := sb "Method Not Allowed"
    headers := (sb "Allow", sb "GET, POST, HEAD, OPTIONS") :: secHeaders
    body := sb "method not allowed\n" }

/-- The mini-serve routing function (Lean reference): allowed method → `200`,
else → `405`. -/
def miniServe (tag : Word) : Response := if signedLt tag 4 then resp200 else resp405

/-! ### Routing non-vacuity: distinct methods serve DISTINCT bytes -/

-- tag 0 (a GET, allowed) serves the 200; tag 9 (disallowed) serves the 405:
#guard (miniServe 0).status = 200
#guard (miniServe 9).status = 405
#guard serialize (miniServe 0) ≠ serialize (miniServe 9)
#guard serialize (miniServe 0) = serialize resp200
#guard serialize (miniServe 9) = serialize resp405

/-! ## 5. Byte-identity to the leanc serve — the differential

`refSerialize` is the reference serializer with the leanc-faithful `Nat.repr`
decimal render (the shape the deployed `Reactor.serialize` compiles). The
translator's `serialize` (a bounded divide-by-10 digit loop) emits the SAME bytes
on the corpus — checked by `#guard` (kernel evaluation, no axioms). -/

/-- Reference decimal render via `Nat.repr` (leanc-faithful; ASCII digits are
single UTF-8 bytes). -/
def refNatToDec (n : Nat) : Bytes := (Nat.repr n).toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

def refBuild (resp : Response) : Wire :=
  { status := resp.status, reason := resp.reason, headers := resp.headers,
    contentLength := resp.body.length, body := resp.body }

def refStatusLine (w : Wire) : Bytes :=
  http11 ++ [32] ++ refNatToDec w.status ++ [32] ++ w.reason

def refHeaderLine (nv : Bytes × Bytes) : Bytes := nv.1 ++ [58, 32] ++ nv.2

def refAllHeaders (w : Wire) : List (Bytes × Bytes) :=
  w.headers ++ [(clName, refNatToDec w.contentLength)]

def refRenderHeaders : List (Bytes × Bytes) → Bytes
  | []     => []
  | [h]    => refHeaderLine h
  | h :: t => refHeaderLine h ++ crlf ++ refRenderHeaders t

def refSerializeWire (w : Wire) : Bytes :=
  refStatusLine w ++ crlf ++ refRenderHeaders (refAllHeaders w) ++ crlf ++ crlf ++ w.body

/-- The reference serializer (leanc-faithful `Nat.repr` render). -/
def refSerialize (resp : Response) : Bytes := refSerializeWire (refBuild resp)

/-! **The byte-identity differential.** The translator serializer emits exactly
the reference (leanc-faithful) bytes on the whole corpus. -/
#guard serialize resp200 = refSerialize resp200
#guard serialize resp405 = refSerialize resp405
#guard serialize (ok200 (sb "hello\n")) = refSerialize (ok200 (sb "hello\n"))
#guard serialize (miniServe 0) = refSerialize (miniServe 0)
#guard serialize (miniServe 9) = refSerialize (miniServe 9)

-- both serialized responses are non-empty; the exact security-header bytes are
-- pinned byte-for-byte by the byte-identity differential above:
#guard (serialize resp200).length > 0
#guard (serialize resp405).length > 0
-- the 405 is strictly larger (carries the extra Allow header + longer body):
#guard (serialize resp405).length > (serialize resp200).length

/-! ### The emitted program witness -/

#eval reprStr (serveSliceProg 0 64 4096 resp200 resp405)

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms serveSlice_correct
#print axioms seq_clk_collapse
#print axioms branch_reduce

end Pancake.ServeSlice
