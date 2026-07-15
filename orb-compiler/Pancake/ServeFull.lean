/-
  Pancake/ServeFull.lean — the serve slice GROWN toward the full serve: MORE real
  decision stages executed through the translator, and the flat response copy of
  the slice replaced by the STRUCTURED serialize (status line / header block /
  body written as a segment sequence), so the compiled serve materializes the
  COMPLETE response bytes — status + every header + body.

  This ASSEMBLES three already-built, already-proven translator pieces (nothing in
  them is modified or re-proven):

    * The decision-stage certificates (`Pancake/ServeFragment.lean`): each real
      deployed decision — connection-limit admission, IP-filter admission,
      body-size limit, the response-security header set — is lowered into the
      loop-free `{prim, seq, cond}` grammar and its `Refines` certificate is
      auto-produced by `wf_auto`. Here FOUR of them are composed into one prefix
      program via `refines_seq` (sequential-composition of refinements).

    * The method-filter ROUTE (`Pancake/ServeSlice.lean`): the emitted
      `If (Cmp Less (Var "method") 4) …` that a real request's method drives to a
      `200 OK` (allowed) or a `405 Method Not Allowed` (refused), selecting DISTINCT
      response bytes. The slice's `seq_clk_collapse` peels the decision prefix.

    * The STRUCTURED serialize (`Pancake/SerializeFull.lean`): `writeSegs` /
      `serialize_structured_correct` — the response wire image written NOT by one
      flat copy but by a sequence of per-segment writes (status line, header block,
      body) at cumulative offsets, landing the whole `serialize resp` byte-for-byte
      into the output region.

  THE GROWN SERVE. `serveFullProg` is ONE emitted program:

      emit securityHeadersDecision ;      -- response-security header flags
      emit connLimitDecision       ;      -- connection-limit admission
      emit ipfilterDecision        ;      -- IP-filter admission
      emit bodyLimitDecision       ;      -- body-size limit
      ( if (method < 4)                   -- method-filter route
          then writeSegs … (respSegs resp200 …)   -- 200 OK, structured
          else writeSegs … (respSegs resp405 …) ) -- 405, structured

  Five real deployed decisions are represented (four executed as a composed prefix
  through their certificates, the fifth — the method filter — drives the response
  selection), versus the slice's two; and the response is materialized by the
  three-segment structured serialize (status line + full header block + body)
  rather than a single flat copy.

  THE THEOREM. `serveFull_correct` : running `serveFullProg` from an entry state
  that encodes the request (the `method` tag) and holds each routed response's
  three segment sources in memory lands the model memory with the output region at
  `base_out` equal, byte for byte, to `serialize (if tag < 4 then resp200 else
  resp405)` — the routed response's COMPLETE wire image (status line, every header
  including the derived `Content-Length`, blank-line separator, body). The
  postcondition is a genuine byte-exact memory effect (`MemBytesAt`), the guard is
  the real routing `signedLt tag 4`, and the branches serialize DISTINCT responses.
  NOT `P → P`.

  BYTE-IDENTITY TO the reference serve. §5 re-uses the slice's leanc-faithful
  reference serializer (`refSerialize`, `Nat.repr`-based decimal render) and
  `#guard`s `serialize resp = refSerialize resp` on the routed responses — the
  translator serializer emits the SAME bytes the reference serve does. Combined
  with `serveFull_correct`, the compiled program's output region byte-for-byte
  equals the reference serve output.

  FAITHFULNESS RESIDUALS (named, not hidden):
   * The four decision stages are EXECUTED (their emitted programs compose into
     `serveFullProg`, proven via their certificates) but their `result` locals do
     not yet SHORT-CIRCUIT the response: an admission failure (connection-limit /
     IP-filter / body-size) should route to `503` / `403` / `413`; here only the
     method filter drives the response selection. Wiring `result` into a multi-way
     error route is the residual — the analog of the slice's "header flags do not
     yet drive the serialized header list".
   * Each data-dependent decision carries ONE named input-scoping hypothesis (the
     local its guard reads is bound) — the A0 input contract, exactly as the
     redirect-status certificate carries `hcode`. That is DATA, not a hand proof.
   * The three response segment sources are pre-loaded into memory; the routing
     branch selects WHICH response's segments `writeSegs` materializes. A handler
     that BUILDS the header block dynamically (the nested OUTER `While` over the
     header list) is the deeper residual named in `SerializeFull.lean` §RESIDUALS.
   * Output region is WORD-addressed (`wordOfByte`); packed byte layout needs the
     `StoreByte` primitive — the bytes-lowering residual shared with the write loop.
   * This is Stack L (the Lean model of Pancake) + a memory post-state claim; the
     machine-code A1 differential for the WHOLE composed serve is the residual (as
     the slice itself is Stack L only).

  ASSURANCE. `#print axioms serveFull_correct` is ⊆ {propext, Quot.sound,
  Classical.choice}; 0 `sorry`, 0 `native_decide`, 0 `ofReduceBool`.
  Build: `Pancake/build_servefull.sh`.
-/
import Pancake.ServeSlice
import Pancake.SerializeFull

namespace Pancake.ServeFull

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.EmitCorrectClock
     Pancake.ProofProducing Pancake.ServeFragment Pancake.SerializeCompile
     Pancake.SerializeFull Pancake.ServeSlice

variable {σ : Type}

/-! ## 0. The serve-frame invariant a decision stage preserves

A decision stage may set its own locals, but for it to compose in FRONT of the
route + structured serialize it must leave untouched: the whole memory (so the
segment sources survive), the address set (so the output region stays
addressable), and the `method` local (so the route still sees the request). -/

/-- A state-transformer preserves the serve frame: memory, address set, and the
`method` local are all untouched. -/
def FrameServe (φ : PancakeState σ → PancakeState σ) : Prop :=
  ∀ s : PancakeState σ,
    (φ s).memory = s.memory ∧ (φ s).memaddrs = s.memaddrs ∧
    (φ s).locals "method" = s.locals "method"

/-- The frame is closed under composition (the shape `denote (seq …)` produces). -/
theorem frame_comp {φ ψ : PancakeState σ → PancakeState σ}
    (hφ : FrameServe φ) (hψ : FrameServe ψ) : FrameServe (fun s => ψ (φ s)) := by
  intro s
  obtain ⟨hm1, ha1, hl1⟩ := hφ s
  obtain ⟨hm2, ha2, hl2⟩ := hψ (φ s)
  exact ⟨hm2.trans hm1, ha2.trans ha1, hl2.trans hl1⟩

/-! ## 1. Each decision stage's denotation preserves the serve frame -/

/-- Security-headers: sets three header-present flags, nothing else. -/
theorem frame_sec : FrameServe (denote (securityHeadersDecision (σ := σ))) := by
  intro s
  rw [denote_sec_eq]
  refine ⟨rfl, rfl, ?_⟩
  simp [setLocal]

/-- Connection-limit admission: writes only `result`. -/
theorem frame_conn (av : PancakeState σ → Word) :
    FrameServe (denote (connLimitDecision av)) := by
  intro s
  simp only [connLimitDecision, denote, assignPrim]
  refine ⟨?_, ?_, ?_⟩ <;> split <;> simp [setLocal]

/-- IP-filter admission: nested cond, writes only `result`. -/
theorem frame_ipf (ov : PancakeState σ → Word) :
    FrameServe (denote (ipfilterDecision ov)) := by
  intro s
  simp only [ipfilterDecision, denote, assignPrim]
  refine ⟨?_, ?_, ?_⟩ <;> (split <;> try split) <;> simp [setLocal]

/-- Body-size limit: writes only `result`. -/
theorem frame_body (cv : PancakeState σ → Word) :
    FrameServe (denote (bodyLimitDecision cv)) := by
  intro s
  simp only [bodyLimitDecision, denote, assignPrim]
  refine ⟨?_, ?_, ?_⟩ <;> split <;> simp [setLocal]

/-! ## 2. The composed decision prefix and its combined denotation -/

/-- The four-stage decision prefix (the emitted programs, sequenced). -/
def decisionPrefixProg (activeVal octetVal clVal : PancakeState σ → Word) : PancakeProg :=
  .seq (emit (securityHeadersDecision (σ := σ)))
   (.seq (emit (connLimitDecision activeVal))
    (.seq (emit (ipfilterDecision octetVal)) (emit (bodyLimitDecision clVal))))

/-- The combined denotation of the prefix (the four transformers, composed). -/
def prefixDenote (activeVal octetVal clVal : PancakeState σ → Word) :
    PancakeState σ → PancakeState σ :=
  fun s => denote (bodyLimitDecision clVal)
    (denote (ipfilterDecision octetVal)
      (denote (connLimitDecision activeVal)
        (denote (securityHeadersDecision (σ := σ)) s)))

/-- The prefix's emitted program refines the composed denotation — the four
auto-produced certificates, glued by `refines_seq`. Each data-dependent stage
carries its named input-scoping fact (the A0 input contract). -/
theorem decisionPrefix_cert (o : Oracle σ) (activeVal octetVal clVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s))
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s))
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    Refines o (decisionPrefixProg activeVal octetVal clVal)
      (prefixDenote activeVal octetVal clVal) := by
  -- build the composed refinement bottom-up (so the transformer is inferred from
  -- the sub-certificates), then check it against `prefixDenote` by defeq
  have h := refines_seq o (securityHeadersDecision_cert o)
    (refines_seq o (connLimitDecision_cert o activeVal hactive)
      (refines_seq o (ipfilterDecision_cert o octetVal hoctet)
        (bodyLimitDecision_cert o clVal hcl)))
  exact h

/-- The composed prefix preserves the serve frame. -/
theorem prefix_frame (activeVal octetVal clVal : PancakeState σ → Word) :
    FrameServe (prefixDenote activeVal octetVal clVal) := by
  have h := frame_comp (frame_comp (frame_comp (frame_sec (σ := σ)) (frame_conn activeVal))
    (frame_ipf octetVal)) (frame_body clVal)
  exact h

/-! ## 3. `SourcesOK` transport under a serve-frame change

The structured-serialize precondition `SourcesOK` reads only `memaddrs` and
`memory`; a transformer that preserves both (the serve frame) transports it. -/

theorem SourcesOK_congr (base : Word) (N : Nat) {s1 s2 : PancakeState σ}
    (hma : s2.memaddrs = s1.memaddrs) (hmem : s2.memory = s1.memory) :
    ∀ segs : List Seg, SourcesOK base N segs s1 → SourcesOK base N segs s2
  | [], h => h
  | (sr, bs) :: rest, h => by
    obtain ⟨hload, hdisj, hrest⟩ := h
    refine ⟨?_, hdisj, SourcesOK_congr base N hma hmem rest hrest⟩
    intro j hj
    rw [hma, hmem]
    exact hload j hj

/-! ## 4. The route + structured serialize, and the end-to-end theorem -/

/-- The method-filter route to the structured serialize of the selected response.
Both branches materialize the full three-segment wire image of their response. -/
def routeSerialize (base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 : Word)
    (resp200 resp405 : Response) : PancakeProg :=
  .cond (.cmp .less (.var "method") (.const 4))
    (writeSegs base_out 0 (respSegs resp200 srcS2 srcH2 srcB2))
    (writeSegs base_out 0 (respSegs resp405 srcS4 srcH4 srcB4))

/-- The grown serve: the decision prefix, then the route to the structured
serialize. -/
def serveFullProg (base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 : Word)
    (resp200 resp405 : Response) (activeVal octetVal clVal : PancakeState σ → Word) :
    PancakeProg :=
  .seq (decisionPrefixProg activeVal octetVal clVal)
    (routeSerialize base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 resp200 resp405)

/-- **THE PAYOFF.** The grown serve — four executed decision stages, then the
method-filter route to the structured serialize — run from an entry state that
encodes the request (`method = tag`) and holds each routed response's three
segment sources in memory, routes on `signedLt tag 4` and lands the model memory
with the output region at `base_out` equal, byte for byte, to the COMPLETE wire
image `serialize (if tag < 4 then resp200 else resp405)` (status line, every
header, blank-line separator, body). Side conditions are exactly the four A0
input contracts (a bound local per data-dependent decision) plus, per routed
response, a segmented memcpy's: the output region fits the signed range and is
injective/addressable, and every segment source is loaded disjoint from the output
(`SourcesOK`); plus the iteration budget. The conclusion names the real
`serialize` and is a genuine byte-exact memory post-state. NOT `P → P`. -/
theorem serveFull_correct (o : Oracle σ) (tag base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 : Word)
    (resp200 resp405 : Response) (s : PancakeState σ)
    (activeVal octetVal clVal : PancakeState σ → Word)
    -- A0 input contracts (one bound local per data-dependent decision):
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s))
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s))
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s))
    -- the request's method tag:
    (hmethod : s.locals "method" = some tag)
    -- allowed-route (200) segmented-memcpy side conditions:
    (hN2 : (serialize resp200).length < 2 ^ 63)
    (hOinj2 : ∀ p q, p < (serialize resp200).length → q < (serialize resp200).length →
      base_out + BitVec.ofNat 64 p = base_out + BitVec.ofNat 64 q → p = q)
    (hOaddr2 : ∀ p, p < (serialize resp200).length →
      s.memaddrs (base_out + BitVec.ofNat 64 p) = true)
    (hSrc2 : SourcesOK base_out (serialize resp200).length (respSegs resp200 srcS2 srcH2 srcB2) s)
    (hclock2 : (serialize resp200).length ≤ s.clock)
    -- refused-route (405) segmented-memcpy side conditions:
    (hN4 : (serialize resp405).length < 2 ^ 63)
    (hOinj4 : ∀ p q, p < (serialize resp405).length → q < (serialize resp405).length →
      base_out + BitVec.ofNat 64 p = base_out + BitVec.ofNat 64 q → p = q)
    (hOaddr4 : ∀ p, p < (serialize resp405).length →
      s.memaddrs (base_out + BitVec.ofNat 64 p) = true)
    (hSrc4 : SourcesOK base_out (serialize resp405).length (respSegs resp405 srcS4 srcH4 srcB4) s)
    (hclock4 : (serialize resp405).length ≤ s.clock) :
    ∃ s', PancakeSem o (serveFullProg base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4
              resp200 resp405 activeVal octetVal clVal) s = (none, s') ∧
      MemBytesAt s' base_out (serialize (if signedLt tag 4 then resp200 else resp405)) := by
  -- run the decision prefix; name the post-state Φ s
  have hpre := decisionPrefix_cert o activeVal octetVal clVal hactive hoctet hcl
  obtain ⟨hpre_eq, hpre_clk⟩ := hpre s
  obtain ⟨hΦmem, hΦma, hΦmeth⟩ := prefix_frame activeVal octetVal clVal s
  -- name the prefix post-state Φs and fold the occurrences
  obtain ⟨Φs, hΦs⟩ : ∃ t, t = prefixDenote activeVal octetVal clVal s := ⟨_, rfl⟩
  rw [← hΦs] at hpre_eq hpre_clk hΦmem hΦma hΦmeth
  -- peel the prefix (clock-preserving) off the top Seq
  have hstep : PancakeSem o (serveFullProg base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4
                  resp200 resp405 activeVal octetVal clVal) s
      = PancakeSem o (routeSerialize base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 resp200 resp405) Φs :=
    seq_clk_collapse o hpre_eq hpre_clk
  -- the route guard sees the request method (preserved by the prefix)
  have hΦmethod : Φs.locals "method" = some tag := by rw [hΦmeth]; exact hmethod
  have hguard : eval Φs (.cmp .less (.var "method") (.const 4))
      = some (if signedLt tag 4 then (1 : Word) else 0) := by
    simp only [eval, hΦmethod]
  by_cases hb : signedLt tag 4
  · -- ALLOWED → 200, structured
    have hrun : PancakeSem o (routeSerialize base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 resp200 resp405) Φs
        = PancakeSem o (writeSegs base_out 0 (respSegs resp200 srcS2 srcH2 srcB2)) Φs := by
      rw [routeSerialize, sem_cond o hguard, if_pos hb, if_pos (show (1 : Word) ≠ 0 by decide)]
    obtain ⟨s', hs'eq, hpost⟩ :=
      serialize_structured_correct o resp200 base_out srcS2 srcH2 srcB2 Φs hN2 hOinj2
        (by intro p hp; rw [hΦma]; exact hOaddr2 p hp)
        (SourcesOK_congr base_out (serialize resp200).length hΦma hΦmem _ hSrc2)
        (by rw [hpre_clk]; exact hclock2)
    exact ⟨s', by rw [hstep, hrun]; exact hs'eq, by rw [if_pos hb]; exact hpost⟩
  · -- REFUSED → 405, structured
    have hrun : PancakeSem o (routeSerialize base_out srcS2 srcH2 srcB2 srcS4 srcH4 srcB4 resp200 resp405) Φs
        = PancakeSem o (writeSegs base_out 0 (respSegs resp405 srcS4 srcH4 srcB4)) Φs := by
      rw [routeSerialize, sem_cond o hguard, if_neg hb, if_neg (show ¬((0 : Word) ≠ 0) by decide)]
    obtain ⟨s', hs'eq, hpost⟩ :=
      serialize_structured_correct o resp405 base_out srcS4 srcH4 srcB4 Φs hN4 hOinj4
        (by intro p hp; rw [hΦma]; exact hOaddr4 p hp)
        (SourcesOK_congr base_out (serialize resp405).length hΦma hΦmem _ hSrc4)
        (by rw [hpre_clk]; exact hclock4)
    exact ⟨s', by rw [hstep, hrun]; exact hs'eq, by rw [if_neg hb]; exact hpost⟩

/-! ## 5. Non-vacuity + byte-identity to the reference serve

The routed responses are the slice's real `resp200` (200 OK, security headers,
body) and `resp405` (405 with the RFC-9110 `Allow` header + security headers). -/

/-- The mini-serve routing (reference): allowed method → 200, else → 405. Reused
from the slice. -/
def routedResp (tag : Word) : Response := if signedLt tag 4 then resp200 else resp405

-- routing is genuine: distinct methods serve DISTINCT complete responses:
#guard (routedResp 0).status = 200
#guard (routedResp 9).status = 405
#guard serialize (routedResp 0) ≠ serialize (routedResp 9)

-- the STRUCTURED serialize's three-segment concatenation IS `serialize resp` for
-- both routed responses (the structured build reconstructs the whole wire image):
#guard concatSegs (respSegs resp200 0 0 0) = serialize resp200
#guard concatSegs (respSegs resp405 0 0 0) = serialize resp405
#guard totalLen (respSegs resp200 0 0 0) = (serialize resp200).length
#guard totalLen (respSegs resp405 0 0 0) = (serialize resp405).length

-- the segment decomposition is a genuine, non-trivial three-way split (each of the
-- three segments non-empty and the status/header segments distinct):
#guard (statusSeg resp200).length > 0
#guard (headerSeg resp200).length > 0
#guard resp200.body.length > 0
#guard (statusSeg resp200) ≠ (headerSeg resp200)

-- BYTE-IDENTITY: the translator serializer emits exactly the reference
-- (leanc-faithful `Nat.repr`) bytes on both routed responses — the compiled serve's
-- output region byte-for-byte equals the reference serve output:
#guard serialize resp200 = refSerialize resp200
#guard serialize resp405 = refSerialize resp405
#guard serialize (routedResp 0) = refSerialize (routedResp 0)
#guard serialize (routedResp 9) = refSerialize (routedResp 9)

/-! ### The emitted program witness -/

#eval reprStr (serveFullProg (σ := Unit) 0 64 4096 8192 16384 20480 24576 resp200 resp405
                (fun s => (s.locals "active").getD 0)
                (fun s => (s.locals "octet").getD 0)
                (fun s => (s.locals "cldigits").getD 0))

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms serveFull_correct
#print axioms decisionPrefix_cert
#print axioms prefix_frame
#print axioms SourcesOK_congr

end Pancake.ServeFull
