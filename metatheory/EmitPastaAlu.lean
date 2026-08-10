/-
SCRATCH executable: emit the Pasta ALU descriptor (the in-AIR Kimchi/Wrap verifier's ROW) and its
honest three-operation trace fixture.

  lake env lean --run EmitPastaAlu.lean fp    > ../circuit/descriptors/by-name/pasta-alu-sound.json
  lake env lean --run EmitPastaAlu.lean fq    > ../circuit/descriptors/by-name/pasta-alu-fq-sound.json
  lake env lean --run EmitPastaAlu.lean fpsz  > ../circuit/descriptors/by-name/pasta-alu-sz.json
  lake env lean --run EmitPastaAlu.lean fqsz  > ../circuit/descriptors/by-name/pasta-alu-fq-sz.json
  lake env lean --run EmitPastaAlu.lean trace > ../circuit/tests/fixtures/pasta-alu-sound-trace.txt

The descriptors are `Dregg2.Circuit.Emit.MinaWrapVerifierAir.{fpAluDesc, fqAluDesc}`, each
`EffectLower.lowerAir` of the source `EffectAir` `pastaAluAir` — House Law #1's endpoint form:
there is no hand-written `VmConstraint2` list for a re-emission to drift from. This file only
RENDERS; it authors nothing.

⚑ The trace is EIGHT rows: the honest multiply, add and sub rows, padded to a power-of-two height
by repeating the multiply. Every declared range lookup constrains its wire on EVERY row
(`LookupSpec` carries no guard), so the padding is a copy of a legal row rather than zeros.
`SEL_CHAIN` is `0` on every row, so the emitted fixture is eight UNRELATED Pasta operations — which
is `unchained_transition_relates_nothing` on the wire, not a shortcut.

⚑ **AND THE MACHINE** (`MinaWrapVerifierProgram`): the register-file + instruction-ROM descriptor
and its honest S-box run, which is the first emitted object in this cone whose PUBLIC INPUTS say
what it computes.

  lake env lean --run EmitPastaAlu.lean sbox      > ../circuit/descriptors/by-name/pasta-sbox-prog.json
  lake env lean --run EmitPastaAlu.lean sboxtrace > ../circuit/tests/fixtures/pasta-sbox-prog-trace.txt
  lake env lean --run EmitPastaAlu.lean sboxpis   > ../circuit/tests/fixtures/pasta-sbox-prog-pis.txt

⚑ **AND THE Fq TRANSCRIPT SPONGE** (`MinaWrapVerifierSponge`): one full Kimchi round over the REAL
`fq_kimchi` constants at `qLimb`, and a two-element ABSORPTION — 55 rounds — whose output public
input is `PastaPoseidonFq.Core.hash fqParams [1,2]`, the digest o1-labs' own `ArithmeticSponge`
returns.

  lake env lean --run EmitPastaAlu.lean fqround       > ../circuit/descriptors/by-name/pasta-fq-round.json
  lake env lean --run EmitPastaAlu.lean fqroundtrace  > ../circuit/tests/fixtures/pasta-fq-round-trace.txt
  lake env lean --run EmitPastaAlu.lean fqroundpis    > ../circuit/tests/fixtures/pasta-fq-round-pis.txt
  lake env lean --run EmitPastaAlu.lean fqabsorb      > ../circuit/descriptors/by-name/pasta-fq-absorb.json
  lake env lean --run EmitPastaAlu.lean fqabsorbtrace > ../circuit/tests/fixtures/pasta-fq-absorb-trace.txt
  lake env lean --run EmitPastaAlu.lean fqabsorbpis   > ../circuit/tests/fixtures/pasta-fq-absorb-pis.txt

⚑ **AND THE REAL MINA BLOCK'S TRANSCRIPT LINK** (`MinaBlockFqTranscript`): the SAME 2 048-instruction
program, pinned at seven blocks instead of six, whose input state and absorbed element are the 91st
link of the phase-2 (`fq_kimchi`) absorption tape of the Wrap proof of Mina devnet block 539508, and
whose two output lanes' low 128 bits are the `v′`/`u′` that block's `proof.oracles(...)` returned.

  lake env lean --run EmitPastaAlu.lean fqlink       > ../circuit/descriptors/by-name/pasta-fq-wraplink.json
  lake env lean --run EmitPastaAlu.lean fqlinktrace  > ../circuit/tests/fixtures/pasta-fq-wraplink-trace.txt
  lake env lean --run EmitPastaAlu.lean fqlinkpis    > ../circuit/tests/fixtures/pasta-fq-wraplink-pis.txt
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierAir
import Dregg2.Circuit.Emit.MinaWrapVerifierProgram
import Dregg2.Circuit.Emit.MinaWrapVerifierSponge
import Dregg2.Circuit.Emit.MinaBlockFqTranscript
import Dregg2.Circuit.Emit.MinaPhase2Chain
import Dregg2.Circuit.Emit.MinaPhase1Chain

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.MinaWrapVerifierAir

def render (r : List Int) : String := String.intercalate " " (r.map toString)

/-- mul · add · sub · mul · mul · add · sub · mul — eight rows, all three operations exercised,
and a power-of-two height. Every `SEL_CHAIN` is `0`. -/
def traceText : String :=
  let m := render aluMulRow
  let a := render aluAddRow
  let s := render aluSubRow
  String.intercalate "\n" [m, a, s, m, m, a, s, m] ++ "\n"

/-- ⚑ The CHAINED fixture: row 0 multiplies with `SEL_CHAIN = 1` and row 1 adds `Z + 0 = Z`, so the
32 chain legs hold with the selector ON. Rows 2..7 are unchained filler at a power-of-two height. -/
def chainTraceText : String :=
  let c0 := render aluChainRow0
  let c1 := render aluChainRow1
  let m := render aluMulRow
  let a := render aluAddRow
  let s := render aluSubRow
  String.intercalate "\n" [c0, c1, m, a, s, m, a, s] ++ "\n"

/-- ⚑ The MACHINE's honest S-box run: eight rows, `x ↦ x⁷` at the `PastaField` KAT operand, with
the register file, the program counter and the ROM-pinned immediates all filled by
`MinaWrapVerifierProgram.runRows` — the Lean interpreter, from the instruction list. No cell here
is asserted from what the program was supposed to do; every one is computed from the inputs. -/
def sboxTraceText : String :=
  String.intercalate "\n"
    ((Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxTrace
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.SBOX_X).map render) ++ "\n"

/-- The `2^10` run of the same machine: four S-box multiplies then 1 020 padding adds, so the
per-instruction price is a measured slope and not an 8-row fixed cost divided by eight. -/
def longTraceText : String :=
  String.intercalate "\n"
    ((Dregg2.Circuit.Emit.MinaWrapVerifierProgram.longTrace
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.SBOX_X).map render) ++ "\n"

/-- The 64 public inputs: the input's 32 limbs then the claimed output's. -/
def sboxPisText : String :=
  render Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxPIs ++ "\n"

/-- ⚑ The Fq SPONGE runs: one full Kimchi round and a two-element absorption, filled by
`MinaWrapVerifierSponge.runRowsAt` at `qN`/`qLimb` — the SAME row generator as the Fp machine
(`rowAsgAt_is_the_program_one`), from the instruction list. No cell is asserted from what the
program was supposed to do; every one is computed from the inputs. -/
def fqRoundTraceText : String :=
  String.intercalate "\n"
    (Dregg2.Circuit.Emit.MinaWrapVerifierSponge.roundTrace.map render) ++ "\n"

def fqRoundPisText : String :=
  render Dregg2.Circuit.Emit.MinaWrapVerifierSponge.roundPIs ++ "\n"

def fqAbsorbTraceText : String :=
  String.intercalate "\n"
    (Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbTrace.map render) ++ "\n"

def fqAbsorbPisText : String :=
  render Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbPIs ++ "\n"

/-- ⚑ The REAL BLOCK's link: the same `absorbProg`, filled from the register file
`MinaBlockFqTranscript.linkInitVec` — three state lanes DERIVED from the block's own 91-element
phase-2 tape, the tape's last element, and the zero second absorb slot. No cell is asserted. -/
def fqLinkTraceText : String :=
  String.intercalate "\n"
    (Dregg2.Circuit.Emit.MinaBlockFqTranscript.linkTrace.map render) ++ "\n"

def fqLinkPisText : String :=
  render Dregg2.Circuit.Emit.MinaBlockFqTranscript.linkPIs ++ "\n"

/-! ## ⚑ THE 46-LINK CHAIN (`MinaPhase2Chain`).

The WHOLE phase-2 transcript, one witness per permutation. The descriptor is emitted once
(`fqchain`); each link's 256 public inputs and 2 048-row trace are emitted by index, so the 46
traces (~150 MB) are generated into a scratch directory rather than tracked. The PI vectors ARE
small enough to track, and they are the objects the fold's continuity claim is about. -/

def fqChainPisText (j : Nat) : String :=
  render (Dregg2.Circuit.Emit.MinaPhase2Chain.chainPIs j) ++ "\n"

def fqChainTraceText (j : Nat) : String :=
  String.intercalate "\n"
    ((Dregg2.Circuit.Emit.MinaPhase2Chain.chainTrace j).map render) ++ "\n"

/-- All 46 links' public inputs, one line per link, in chain order. -/
def fqChainPisAllText : String :=
  String.intercalate "\n"
    ((List.range 46).map (fun j => render (Dregg2.Circuit.Emit.MinaPhase2Chain.chainPIs j))) ++ "\n"

/-! ## ⚑ THE PHASE-1 (Fp) LEG (`MinaWrapVerifierSpongeFp`, `MinaPhase1Chain`).

The SAME machine at `pLimb` and the `fp_kimchi` constants: one full round, a two-element absorption
whose squeeze is `Core.hash fpParams [1,2]` (o1-labs' own `ArithmeticSponge` value, pinned in
`metatheory/fp_kimchi_params.json`), and the 27-link chain that DERIVES `fq_digest` — the element
phase 2's tape starts with and nothing used to derive.

  lake env lean --run EmitPastaAlu.lean fpround        > ../circuit/descriptors/by-name/pasta-fp-round.json
  lake env lean --run EmitPastaAlu.lean fproundtrace   > ../circuit/tests/fixtures/pasta-fp-round-trace.txt
  lake env lean --run EmitPastaAlu.lean fproundpis     > ../circuit/tests/fixtures/pasta-fp-round-pis.txt
  lake env lean --run EmitPastaAlu.lean fpabsorb       > ../circuit/descriptors/by-name/pasta-fp-absorb.json
  lake env lean --run EmitPastaAlu.lean fpabsorbtrace  > ../circuit/tests/fixtures/pasta-fp-absorb-trace.txt
  lake env lean --run EmitPastaAlu.lean fpabsorbpis    > ../circuit/tests/fixtures/pasta-fp-absorb-pis.txt
  lake env lean --run EmitPastaAlu.lean fpchain        > ../circuit/descriptors/by-name/pasta-fp-chainlink.json
  lake env lean --run EmitPastaAlu.lean fpchainpisall  > ../circuit/tests/fixtures/pasta-fp-chainlink-pis.txt
  lake env lean --run EmitPastaAlu.lean fpchaintrace 26 > ../circuit/tests/fixtures/pasta-fp-chainlink-26-trace.txt
-/

def fpRoundTraceText : String :=
  String.intercalate "\n"
    (Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpRoundTrace.map render) ++ "\n"

def fpRoundPisText : String :=
  render Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpRoundPIs ++ "\n"

def fpAbsorbTraceText : String :=
  String.intercalate "\n"
    (Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpAbsorbTrace.map render) ++ "\n"

def fpAbsorbPisText : String :=
  render Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpAbsorbPIs ++ "\n"

def fpChainPisText (j : Nat) : String :=
  render (Dregg2.Circuit.Emit.MinaPhase1Chain.chainPIs j) ++ "\n"

def fpChainTraceText (j : Nat) : String :=
  String.intercalate "\n"
    ((Dregg2.Circuit.Emit.MinaPhase1Chain.chainTrace j).map render) ++ "\n"

/-- All 27 links' public inputs, one line per link, in chain order. -/
def fpChainPisAllText : String :=
  String.intercalate "\n"
    ((List.range 27).map (fun j => render (Dregg2.Circuit.Emit.MinaPhase1Chain.chainPIs j))) ++ "\n"

def main (args : List String) : IO Unit :=
  match args with
  | ["fp"]         => IO.println (emitVmJson2 fpAluDesc)
  | ["fq"]         => IO.println (emitVmJson2 fqAluDesc)
  -- ⚑ The SZ ALU rows. Identical layout and identical honest trace — `trace` serves both.
  | ["fpsz"]       => IO.println (emitVmJson2 fpAluSzDesc)
  | ["fqsz"]       => IO.println (emitVmJson2 fqAluSzDesc)
  | ["trace"]      => IO.print traceText
  | ["chaintrace"] => IO.print chainTraceText
  | ["sbox"]       => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxDesc)
  | ["sboxtrace"]  => IO.print sboxTraceText
  | ["sboxpis"]    => IO.print sboxPisText
  | ["long"]       => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierProgram.longDesc)
  | ["longtrace"]  => IO.print longTraceText
  | ["fqround"]       => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierSponge.roundDesc)
  | ["fqroundtrace"]  => IO.print fqRoundTraceText
  | ["fqroundpis"]    => IO.print fqRoundPisText
  | ["fqabsorb"]      => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbDesc)
  | ["fqabsorbtrace"] => IO.print fqAbsorbTraceText
  | ["fqabsorbpis"]   => IO.print fqAbsorbPisText
  | ["fqlink"]        => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaBlockFqTranscript.linkDesc)
  | ["fqlinktrace"]   => IO.print fqLinkTraceText
  | ["fqlinkpis"]     => IO.print fqLinkPisText
  | ["fqchain"]        => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaPhase2Chain.chainDesc)
  | ["fqchainpisall"]  => IO.print fqChainPisAllText
  | ["fqchainpis", j]  => IO.print (fqChainPisText j.toNat!)
  | ["fqchaintrace", j] => IO.print (fqChainTraceText j.toNat!)
  | ["fpround"]        => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpRoundDesc)
  | ["fproundtrace"]   => IO.print fpRoundTraceText
  | ["fproundpis"]     => IO.print fpRoundPisText
  | ["fpabsorb"]       => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.fpAbsorbDesc)
  | ["fpabsorbtrace"]  => IO.print fpAbsorbTraceText
  | ["fpabsorbpis"]    => IO.print fpAbsorbPisText
  | ["fpchain"]        => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc)
  | ["fpchainpisall"]  => IO.print fpChainPisAllText
  | ["fpchainpis", j]  => IO.print (fpChainPisText j.toNat!)
  | ["fpchaintrace", j] => IO.print (fpChainTraceText j.toNat!)
  | _              => IO.eprintln
      "usage: EmitPastaAlu.lean (fp|fq|fpsz|fqsz|trace|chaintrace|sbox|sboxtrace|sboxpis|long|longtrace\n\
       |fqround|fqroundtrace|fqroundpis|fqabsorb|fqabsorbtrace|fqabsorbpis\n\
       |fqlink|fqlinktrace|fqlinkpis\n\
       |fqchain|fqchainpisall|fqchainpis <j>|fqchaintrace <j>\n\
       |fpround|fproundtrace|fproundpis|fpabsorb|fpabsorbtrace|fpabsorbpis\n\
       |fpchain|fpchainpisall|fpchainpis <j>|fpchaintrace <j>)"
