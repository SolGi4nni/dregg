/-
# crew_playable_handoff — the PoA crew field mission, driven end to end through BOTH exports

⚑ 2026-08-09.  This drives the ADMITTED crew — `CrewFieldMissionAdmission.admittedRaw`, the
module's own demonstration world — through the two `@[export]`s in the order a player would:

1. `dregg_poa_crew_field_seat_preimage` (`seatPreimageWire`) — world + manifest + seat index in,
   the canonical `POA-CREW-SEAT-SIGNING-1` bytes that seat must sign out.  This is the ENTRY
   POINT; before it landed there was no way to take a seat at all.
2. the seat signs those bytes under `POA-CREW-SEAT-MLDSA65-1` (real `fips204` 0.4.6);
3. `dregg_poa_crew_field_step` (`stepWire`) — that admission envelope plus the transcript so far
   in, the exact `POA-CREW-HANDOFF-SIGNING-1` bytes out;
4. the seat signs THOSE under `POA-CREW-HANDOFF-MLDSA65-1`, and the trace built from them is one
   the kernel replays;
5. step again with the transcript one entry longer — and the answer is the NEXT seat's preimage.
   That is the handoff: one seat's signed action becoming the next seat's starting state.

⚠ **TEST MATERIAL.**  All four of the admitted crew's secret keys are derivable by anyone from
the xi seeds pinned beside the roster in `CrewFieldMissionAdmission.lean`.  This crew exists so
the accepting pole of the organ is checkable and for no other purpose; never deploy it.

## What this replaced

The first version of this script authored a SEPARATE "playable" crew, because the admitted crew
could not play: its roster carried `digestFilled 10..13` against a production `verifySeat` that
demands `SHAKE256(publicKey, 32) = playerKey`, so it minted, was admitted, and refused every
step.  That is fixed at the source now — the admitted roster is four real ML-DSA-65 keys — so
this script drives the real fixture instead of a twin of it beside the real fixture.

## Measured 2026-08-09 on the ADMITTED crew, after the roster fix (77eeed7fd)

```
[emit ] seat 0..3 admission preimage : 6202 bytes each, answer 6959 bytes each
        the four answers are pairwise DISTINCT (sha256 prefixes 183f6fd1 / 5171c359
        / e430866e / d41e99b5) — the entry point is not one blob under four names
[sign ] fips204 0.4.6, POA-CREW-SEAT-MLDSA65-1, envelope = pk 1952 ‖ sig 3309 = 5261
[step ] envelope 34690 bytes -> answer 13770 bytes
        seat 0 handoff preimage: 12343 bytes
```

⚑ The `[step ]` line is the two-source result that matters: `stepWire` answered, which
means `authenticateSeat?` — the production `verifyEnvelope`, SHAKE-256 key pin plus
executable FIPS 204 verify — ACCEPTED a `fips204` signature over the bytes the NEW export
emitted.  The entry point is checked against the gate it feeds, not merely against itself.

## Running it

```
lake env lean --run scripts/crew_playable_handoff.lean emit  <dir>
crewsign seat0 seat    <dir>/seat0_msg.hex     <dir>/seat0_env.hex
crewsign seat1 seat    <dir>/seat1_msg.hex     <dir>/seat1_env.hex
lake env lean --run scripts/crew_playable_handoff.lean step  <dir>
crewsign seat0 handoff <dir>/handoff0_msg.hex  <dir>/handoff0_env.hex
lake env lean --run scripts/crew_playable_handoff.lean step2 <dir>
```

`crewsign` is the `crew-kat-gen` harness of `CrewSigningVectors` — same `fips204 = "0.4.6"` /
`rand_core = "0.6"` Cargo.toml, same `KatRng`, same contexts — with `main` taking
`<seat0|seat1|seat2|seat3> <seat|handoff> <msg.hex> <out_env.hex>`, four xi seeds
(`POA-CREW-KAT-SEAT0-XI-SEED-0001!`, `POA-CREW-KAT-WRONG-XI-SEED-0002!`,
`POA-CREW-ADMITTED-SEAT2-XI-0003!`, `POA-CREW-ADMITTED-SEAT3-XI-0004!`), and a body that reads
the Lean-emitted message and writes `publicKey ‖ signature` (1952 + 3309 = 5261 bytes) — the
envelope the Lean production verifier splits:

```rust
let xi = match which.as_str() {
    "seat0" => SEAT0_XI, "seat1" => WRONG_XI, "seat2" => SEAT2_XI, _ => SEAT3_XI };
let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(xi);
let ctx: &[u8] = if ctxname == "seat" { CTX_SEAT } else { CTX_HANDOFF };
let msg = unhex(&std::fs::read_to_string(msgpath).unwrap());
let sig = sk.try_sign_with_rng(&mut KatRng(0x504f_4145_0000_0001), &msg, ctx).unwrap();
assert!(pk.verify(&msg, &sig, ctx));          // the crate's OWN verify, before Lean sees it
let mut env = pk.into_bytes().to_vec(); env.extend_from_slice(&sig);
std::fs::write(outpath, hex(&env)).unwrap();
```

⚠ This is a GENERATOR, not a proof.  It runs the real exports over real signatures and prints
what comes back; it pins nothing.  The accepting poles that a GATE checks are the
`native_decide` pins in `CrewFieldMissionAdmissionFixtures.lean`
(`the_entry_point_answers_for_every_admitted_seat` and its siblings).  ⚑ STILL OWED: the three
signature envelopes this produces, pinned as vectors beside `CrewSigningVectors`, so that the
HANDOFF itself — not just the preimage emission — is a named theorem rather than a run I did.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

def hexOf (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let d : Nat → String := fun n =>
      if n < 10 then toString n else
        match n with
        | 10 => "a" | 11 => "b" | 12 => "c" | 13 => "d" | 14 => "e" | _ => "f"
    d hi ++ d lo)

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def bytesOfHex? (s : String) : Option (List UInt8) :=
  let cs := s.toList.filter (fun c => c != '\n' && c != ' ' && c != '\r')
  if cs.length % 2 != 0 then none else
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
        let hi ← hexVal? a
        let lo ← hexVal? b
        let tail ← go rest
        some (UInt8.ofNat (hi * 16 + lo) :: tail)
    | _ => none
  go cs

def mkSigBytes (env : List UInt8) : Option CrewFieldMission.SignatureBytes :=
  let fins : List (Fin 256) := env.map fun b => ⟨b.toNat, b.toFin.isLt⟩
  if h : fins.length = CrewFieldMission.SIGNATURE_BYTE_LENGTH then some ⟨fins, h⟩ else none

/-- The signing message field of either export's canonical answer. -/
def signingMessageOf (answer : String) : Option String :=
  (Lean.Json.parse answer >>= (·.getObjValAs? String "signing_message")).toOption

def main (args : List String) : IO UInt32 := do
  let dir := (args[1]?).getD "."
  let readEnv (name : String) : IO (Option CrewFieldMission.SignatureBytes) := do
    let h ← IO.FS.readFile (dir ++ "/" ++ name)
    pure (bytesOfHex? h >>= mkSigBytes)
  IO.println s!"admitted mint succeeds       : {admittedMember?.isSome}"
  match args[0]? with
  | some "emit" =>
      -- ⚑ Through the REAL entry point export, not a Lean-internal call.
      for i in [0, 1, 2, 3] do
        let answer := seatPreimageWire (admittedSeatEnvelope i).toJson
        match signingMessageOf answer with
        | none => IO.println s!"seat {i}: ENTRY POINT REFUSED (answer {answer.length} bytes)"
        | some msg =>
            IO.FS.writeFile (dir ++ s!"/seat{i}_msg.hex") (hexOf msg.toUTF8.toList)
            IO.println s!"seat {i} admission preimage    : {msg.toUTF8.size} bytes (answer {answer.length})"
      IO.FS.writeFile (dir ++ "/world.json") admittedWorld.toJson
      IO.FS.writeFile (dir ++ "/manifest.json") admittedManifest.toJson
      pure 0
  | some "step" =>
      let some sig0 ← readEnv "seat0_env.hex" | do IO.println "bad seat0_env"; pure 1
      let req : CrewFieldMissionRuntime.StepRequestWire := {
        activationId := admittedRaw.activationId
        rosterBinding := admittedRaw.rosterBinding
        transcript := []
        seatSignature := sig0
        decision := "specialist"
        decidedRoute := "signal-gallery"
        extraction := "none"
        command := "chart-pressure-route" }
      let bytes := StepEnvelopeWire.toJson
        { world := admittedWorld, manifestJson := admittedManifest.toJson,
          stepRequestJson := req.toJson }
      let out := stepWire bytes
      IO.println s!"[step ] envelope {bytes.length} bytes -> answer {out.length} bytes"
      match signingMessageOf out with
      | none => do IO.println "[step ] REFUSED"; pure 1
      | some msg => do
          IO.FS.writeFile (dir ++ "/handoff0_msg.hex") (hexOf msg.toUTF8.toList)
          IO.FS.writeFile (dir ++ "/step0_out.json") out
          IO.println s!"[step ] seat 0 handoff preimage: {msg.toUTF8.size} bytes"
          pure 0
  | some "step2" =>
      let some sig0 ← readEnv "seat0_env.hex" | do IO.println "bad seat0_env"; pure 1
      let some hs0 ← readEnv "handoff0_env.hex" | do IO.println "bad handoff0_env"; pure 1
      let some sig1 ← readEnv "seat1_env.hex" | do IO.println "bad seat1_env"; pure 1
      let trace0 : CrewFieldMissionRuntime.TraceWire := {
        sequence := 0, seat := 0, previousCounter := 10, counter := 11
        observation := "pathfinder", observedRoute := "signal-gallery"
        decision := "specialist", decidedRoute := "signal-gallery"
        extraction := "none", command := "chart-pressure-route"
        seatSignature := sig0, handoffSignature := hs0 }
      let mkEnv (tr : List CrewFieldMissionRuntime.TraceWire)
          (seatSig : CrewFieldMission.SignatureBytes) : String :=
        let req : CrewFieldMissionRuntime.StepRequestWire := {
          activationId := admittedRaw.activationId
          rosterBinding := admittedRaw.rosterBinding
          transcript := tr
          seatSignature := seatSig
          decision := "specialist"
          decidedRoute := "signal-gallery"
          extraction := "none"
          command := "brace-transit" }
        StepEnvelopeWire.toJson
          { world := admittedWorld, manifestJson := admittedManifest.toJson,
            stepRequestJson := req.toJson }
      let good := mkEnv [trace0] sig1
      let out := stepWire good
      IO.println s!"[HANDOFF] seat1 answer length : {out.length}"
      if out.isEmpty then
        IO.println "[HANDOFF] REFUSED — the chain did not advance"
      else
        IO.FS.writeFile (dir ++ "/step1_out.json") out
        match Lean.Json.parse out with
        | .ok j =>
            let fld : String -> String := fun k =>
              match j.getObjValAs? Nat k with
              | .ok v => toString v
              | .error _ => "?"
            IO.println ("[HANDOFF] sequence            : " ++ fld "sequence")
            IO.println ("[HANDOFF] next_seat           : " ++ fld "next_seat")
            IO.println ("[HANDOFF] next_counter        : " ++ fld "next_counter")
            IO.println ("[HANDOFF] budget remaining    : " ++ fld "operational_budget_remaining")
        | .error _ => IO.println "[HANDOFF] answer not JSON?"
      let wrongSeat := mkEnv [trace0] sig0
      IO.println s!"[REFUSE wrong-seat envelope] mutation present: {wrongSeat != good}"
      IO.println s!"[REFUSE wrong-seat envelope] answer length   : {(stepWire wrongSeat).length}"
      let flip (sb : CrewFieldMission.SignatureBytes) : CrewFieldMission.SignatureBytes :=
        let old := sb.bytes[2000]!
        let nv : Fin 256 := ⟨(old.val + 1) % 256, Nat.mod_lt _ (by omega)⟩
        ⟨sb.bytes.set 2000 nv, by simp [List.length_set, sb.length_eq]⟩
      let tampered := mkEnv [trace0] (flip sig1)
      IO.println s!"[REFUSE tampered signature] mutation present : {tampered != good}"
      IO.println s!"[REFUSE tampered signature] answer length    : {(stepWire tampered).length}"
      let forged := mkEnv [{ trace0 with handoffSignature := sig1 }] sig1
      IO.println s!"[REFUSE forged trace sig] mutation present   : {forged != good}"
      IO.println s!"[REFUSE forged trace sig] answer length      : {(stepWire forged).length}"
      pure 0
  | _ => do IO.println "usage: emit|step|step2 <dir>"; pure 1
