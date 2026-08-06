/-
# `mina_fp_chain_emit` — the PHASE-1 (Fp) witnesses: the Fq leg's twin, at `fp_kimchi`.

Renders, from the Lean interpreters and nothing else:

  * the **round** and **absorption** fixtures of `Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp` —
    one full Kimchi round at the `fp_kimchi` constants, and the two-element absorption whose squeeze
    public input is `Core.hash fpParams [1,2]`, the digest o1-labs' own `ArithmeticSponge` returns
    (`metatheory/fp_kimchi_params.json`);
  * the **27 chain links** of `Dregg2.Circuit.Emit.MinaPhase1Chain` — Mina devnet block 539508's
    phase-1 transcript, whose link 26 OUTPUT LANE 1 is the `fq_digest` the phase-2 chain absorbs as
    tape element 0;
  * the **28 VK-digest links** of `Dregg2.Circuit.Emit.MinaWrapVkDigestChain` — the sha256-pinned
    devnet blockchain Wrap verifier index's 28 commitments, whose link 27 OUTPUT LANE 0 is
    `VKDIGEST`, the element the phase-1 tape *starts* with. ⚑ **THE SAME DESCRIPTOR**
    (`vkChainDesc = MinaPhase1Chain.chainDesc`, by `rfl`): 28 more witnesses, no new AIR.

⚠ **COMPILED FOR A MEASURED REASON**, the same one `MinaChainEmit` records: one 2 048×469 trace
costs **9 min 20 s** through `lake env lean --run` (Lean's INTERPRETER). That is a codegen cost, not
a cost of the chain. Same objects, `leanc`.

    lake build mina_fp_chain_emit
    ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 1   # round + absorb + link 26
    ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures     # …and all 27 links

It authors nothing. Every cell comes from `runRowsVecAt` — the STRICT generator
`runRowsVecAt_is_runRowsAt` welds to `runRowsAt` — and every public input from `chainPIs`/
`fpRoundPIs`/`fpAbsorbPIs`. House Law #1.

⚠ DELIBERATELY NOT IN `defaultTargets`, like `mina_chain_emit`: it drags the whole Pasta sponge cone
through C codegen. Build it explicitly.

The 27 traces are ~90 MB and are NOT tracked; the 27 PI vectors (~25 KB) ARE, because they are the
objects the continuity claim and the digest weld are about. The three fixtures the `dregg-circuit`
harness `include_str!`s — the round trace, the absorb trace and link 26's trace — are tracked.
-/
import Dregg2.Circuit.Emit.MinaPhase1Chain
import Dregg2.Circuit.Emit.MinaWrapVkDigestChain

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.MinaPhase1Chain
open Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp

def render (r : List Int) : String := String.intercalate " " (r.map toString)

/-- `mina_fp_chain_emit <dir> [count]` — `count` defaults to all 27 chain traces.

⚑ **THE DEFAULT ARTIFACTS ARE THE THREE THE HARNESS NEEDS**: the 32-row round, the 2 048-row
absorption, and **link 26** — the link whose second outgoing lane IS `fq_digest`. Those three are
written whatever `count` is, so `mina_fp_chain_emit <dir> 0` reproduces every tracked fixture and
costs three traces rather than twenty-nine. -/
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "fp-witness"
  let count := match args.drop 1 with
    | c :: _ => min 27 (c.toNat!)
    | [] => 27
  IO.FS.createDirAll dir

  -- ── the round instance (32 rows) ────────────────────────────────────────────────
  IO.FS.writeFile (dir ++ "/pasta-fp-round-pis.txt") (render fpRoundPIs ++ "\n")
  IO.FS.writeFile (dir ++ "/pasta-fp-round-trace.txt")
    (String.intercalate "\n" (fpRoundTrace.map render) ++ "\n")
  IO.println s!"round (32 rows) -> {dir}/pasta-fp-round-trace.txt + -pis.txt"

  -- ── the two-element absorption (2 048 rows) ─────────────────────────────────────
  IO.FS.writeFile (dir ++ "/pasta-fp-absorb-pis.txt") (render fpAbsorbPIs ++ "\n")
  IO.FS.writeFile (dir ++ "/pasta-fp-absorb-trace.txt")
    (String.intercalate "\n" (fpAbsorbTrace.map render) ++ "\n")
  IO.println s!"absorption (2048 rows) -> {dir}/pasta-fp-absorb-trace.txt + -pis.txt"

  -- ── all 27 links' public inputs, always ─────────────────────────────────────────
  let allPis := (List.range 27).map (fun j => render (chainPIs j))
  IO.FS.writeFile (dir ++ "/pasta-fp-chainlink-pis.txt") (String.intercalate "\n" allPis ++ "\n")
  IO.println s!"all 27 public-input vectors -> {dir}/pasta-fp-chainlink-pis.txt"

  -- ── link 26: the one the digest weld is about, always ───────────────────────────
  IO.FS.writeFile (dir ++ "/pasta-fp-chainlink-26-pis.txt") (allPis.getD DIGEST_LINK "" ++ "\n")
  IO.FS.writeFile (dir ++ "/pasta-fp-chainlink-26-trace.txt")
    (String.intercalate "\n" ((chainTrace DIGEST_LINK).map render) ++ "\n")
  IO.println s!"link {DIGEST_LINK} (the fq_digest link) -> {dir}/pasta-fp-chainlink-26-trace.txt"

  -- ── ⚑ the VK-DIGEST chain: 28 links over the pinned Wrap VK's 56 coordinates ────
  -- `Dregg2.Circuit.Emit.MinaWrapVkDigestChain`. THE SAME DESCRIPTOR — no new AIR, 28 more
  -- witnesses. Link 27's OUTGOING LANE 0 is `VKDIGEST`, the phase-1 tape's element 0.
  let vkPis := (List.range Dregg2.Circuit.Emit.MinaWrapVkDigestChain.NVK).map
    (fun j => render (Dregg2.Circuit.Emit.MinaWrapVkDigestChain.vkChainPIs j))
  IO.FS.writeFile (dir ++ "/pasta-fp-vkchain-pis.txt") (String.intercalate "\n" vkPis ++ "\n")
  IO.println s!"all 28 VK-chain public-input vectors -> {dir}/pasta-fp-vkchain-pis.txt"

  let vkDigestLink := Dregg2.Circuit.Emit.MinaWrapVkDigestChain.VK_DIGEST_LINK
  IO.FS.writeFile (dir ++ "/pasta-fp-vkchain-27-trace.txt")
    (String.intercalate "\n"
      ((Dregg2.Circuit.Emit.MinaWrapVkDigestChain.vkChainTrace vkDigestLink).map render) ++ "\n")
  IO.println s!"VK-chain link {vkDigestLink} (the index-digest link) \
    -> {dir}/pasta-fp-vkchain-27-trace.txt"

  -- ── the remaining links, on demand ──────────────────────────────────────────────
  IO.FS.createDirAll (dir ++ "/pasta-fp-chainlink")
  for j in [0:count] do
    IO.FS.writeFile s!"{dir}/pasta-fp-chainlink/link-{j}-pis.txt" (allPis.getD j "" ++ "\n")
    let rows := (chainTrace j).map render
    IO.FS.writeFile s!"{dir}/pasta-fp-chainlink/link-{j}-trace.txt"
      (String.intercalate "\n" rows ++ "\n")
    IO.println s!"link {j}/{count} emitted ({rows.length} rows)"

  if count < 27 then
    IO.println s!"⚠ PARTIAL: {count}/27 chain traces (the three tracked fixtures are complete)."
  return 0
