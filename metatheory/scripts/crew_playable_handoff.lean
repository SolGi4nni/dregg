/-
# crew_playable_handoff — the PoA crew field mission's handoff, driven end to end

⚑ **WHAT THIS EXISTS TO SHOW.**  `@[export dregg_poa_crew_field_step]` landed on 2026-08-07
(`ca986ccfd`) and the C bridge in `7497a9dcb`, and the organ was written up as needing only "a
Rust FFI arm, a route, a store and a client".  It needs one thing UPSTREAM of all four, and this
script is how that was measured:

* `CrewFieldMissionAdmission.admittedRawConfig` — the module's own admitted world — carries
  `CrewRelayExpedition.fixtureRoster`, whose player keys are `digestFilled 10..13`
  (`0a0a0a…`, `0b0b0b…`).  It also names the PRODUCTION signing suite, whose `verifySeat`
  demands `SHAKE256(publicKey, 32) = playerKey`.  **No ML-DSA-65 public key digests to
  `0a0a0a…`**, so no seat of that world can ever be authenticated and `stepWire` over it is the
  `""` refusal for every input.  MEASURED: mint succeeds, step refuses.
* The organ IS reachable — but only for a roster of REAL ML-DSA-65 keys, and only for a caller
  who already knows the SEAT-ADMISSION preimage bytes.  Nothing exports those.  `stepWire` hands
  a client the HANDOFF preimage and tells it to "sign THESE BYTES"; the seat-admission preimage,
  which a seat must sign FIRST to be admitted at all, has no export and no route.  A browser
  that re-encoded it would be building the very body the module forbids clients to build.
  **That is the gap, and it is a Lean gap, not a plumbing gap.**

So this script authors a crew that CAN play: seats 0 and 1 hold the two real ML-DSA-65 keypairs
already pinned in `CrewSigningVectors` (xi seeds `POA-CREW-KAT-SEAT0-XI-SEED-0001!` and
`POA-CREW-KAT-WRONG-XI-SEED-0002!`).  ⚠ Both secrets are derivable by anyone from those seeds.
This crew is TEST material and must never be deployed — same status as the KAT crew.

## Measured 2026-08-09, through the real `@[export]` (`stepWire`), on this tree

```
playable mint succeeds        : true
seat0 admission message bytes : 6202      seat1 admission message bytes : 6202
[step ] envelope 34743 bytes -> answer 13770 bytes
        sequence 0, next_seat 0, next_counter 11, budget 13
        seat 0 handoff preimage: 12343 bytes
[step2] transcript = [seat 0 signed handoff] -> answer 51553 bytes
        sequence 1, next_seat 1, next_counter 21, budget 12
        the pre_root seat 1 signs carries seat 0's trace, seat 0's counter 10 -> 11
[REFUSE wrong-seat envelope]  mutation present: true   answer length: 0
[REFUSE tampered signature]   mutation present: true   answer length: 0
[REFUSE forged trace sig]     mutation present: true   answer length: 0
```

That is the handoff: one seat's signed action becoming the next seat's starting state, with
every byte either emitted or judged by Lean.

## Running it

```
lake env lean --run scripts/crew_playable_handoff.lean emit  <dir>
crewsign seat0 seat    <dir>/seat0_msg.hex     <dir>/seat0_env.hex
crewsign seat1 seat    <dir>/seat1_msg.hex     <dir>/seat1_env.hex
lake env lean --run scripts/crew_playable_handoff.lean step  <dir>
crewsign seat0 handoff <dir>/handoff0_msg.hex  <dir>/handoff0_env.hex
lake env lean --run scripts/crew_playable_handoff.lean step2 <dir>
```

`crewsign` is the `crew-kat-gen` harness of `CrewSigningVectors` with one subcommand shape —
`<seat0|seat1> <seat|handoff> <msg.hex> <out_env.hex>` — reading the Lean-emitted message and
writing `publicKey ‖ signature` (1952 + 3309 = 5261 bytes), the envelope the Lean production
verifier splits.  Its `Cargo.toml` is `fips204 = "0.4.6"`, `rand_core = "0.6"`; its body is the
generator reproduced at the bottom of `Dregg2/Games/PathOfAngels/CrewSigningVectors.lean` with
`main` replaced by:

```rust
let (which, ctxname, msgpath, outpath) = (&a[1], &a[2], &a[3], &a[4]);
let xi = if which == "seat0" { SEAT0_XI } else { WRONG_XI };
let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(xi);
let ctx: &[u8] = if ctxname == "seat" { CTX_SEAT } else { CTX_HANDOFF };
let msg = unhex(&std::fs::read_to_string(msgpath).unwrap());
let sig = sk.try_sign_with_rng(&mut KatRng(0x504f_4145_0000_0001), &msg, ctx).unwrap();
assert!(pk.verify(&msg, &sig, ctx));          // the crate's OWN verify, before Lean sees it
let mut env = pk.into_bytes().to_vec(); env.extend_from_slice(&sig);
std::fs::write(outpath, hex(&env)).unwrap();
```

⚠ This is a GENERATOR, not a proof.  It runs the real export over real signatures and prints what
comes back; it pins nothing and asserts nothing to the kernel.  The named-theorem version of the
reachability fact wants the three envelopes pinned as vectors beside `CrewSigningVectors`.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

namespace Playable


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

/-! ### The roster: seat 0 and seat 1 hold REAL ML-DSA-65 keypairs.

Seat 0's key is `CrewSigningVectors.katSeat0PublicKey` (xi = `POA-CREW-KAT-SEAT0-XI-SEED-0001!`)
and seat 1's is `katWrongPublicKey` (xi = `POA-CREW-KAT-WRONG-XI-SEED-0002!`).  Both secrets are
derivable by anyone from the pinned seeds; this crew is TEST material and must never be deployed. -/

def seat0Key : Digest32 := CrewFieldMission.ProductionSigning.katPlayerKey

def seat1Key : Digest32 :=
  (CrewFieldMission.ProductionSigning.shakeDigest32? CrewSigningVectors.katWrongPublicKey.toList).getD
    (CrewFieldMission.digestFilled 0xEE)

def pSeat0 : CrewRelayExpedition.Seat :=
  { CrewRelayExpedition.fixtureSeat0 with playerKey := seat0Key }
def pSeat1 : CrewRelayExpedition.Seat :=
  { CrewRelayExpedition.fixtureSeat1 with playerKey := seat1Key }

def playableRoster : List CrewRelayExpedition.Seat :=
  [ pSeat0
  , pSeat1
  , CrewRelayExpedition.fixtureSeat2
  , CrewRelayExpedition.fixtureSeat3 ]

def baseConfig : CrewFieldMission.RawConfig :=
  { admittedRawConfigBase with roster := playableRoster }

def playableConfig : CrewFieldMission.RawConfig :=
  { baseConfig with
    briefingCommitment := CrewFieldMission.ProductionSigning.productionBriefingDigest.digest
      (CrewFieldMission.briefingDeckPreimage baseConfig CrewFieldMission.fixtureBriefings) }

def playableRaw : CrewFieldMissionRuntime.RawActivation :=
  { admittedRaw with
    fieldSession := playableConfig.sessionDigest
    rosterBinding := CrewFieldMissionRuntime.rosterBindingOf playableRoster }

def playableComponent : ActivatedContent.Component where
  name := ACTIVATION_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (activationJson playableRaw)).getD
    (CrewFieldMission.digestFilled 0)
  bytesUtf8 := activationJson playableRaw

def playableManifest : ActivatedContent.Manifest :=
  { admittedManifest with components := [playableComponent] }

def playableWorld : WorldActivation.WorldIdentity :=
  { admittedWorld with
    contentRoot := (ActivatedContent.manifestRoot? playableManifest).getD
      (CrewFieldMission.digestFilled 0) }

def playableMember? : Option WorldScopedCrewActivation := do
  let manifest ← ActivatedContent.decodeManifest playableManifest.toJson
  authorizeCrewActivationForWorld? playableWorld manifest

/-- The exact bytes a seat's ML-DSA-65 key must sign under `POA-CREW-SEAT-MLDSA65-1`
to be admitted to this crew.  ⚑ Nothing exports this today — see the report. -/
def seatMessage (seat : CrewRelayExpedition.Seat) : List UInt8 :=
  CrewFieldMission.ProductionSigning.seatPreimageMessage
    ((CrewFieldMission.SeatAdmissionBody.mk playableConfig.sessionDigest seat).signingPreimage
      playableConfig.messageDigestSuiteId playableConfig.signingSuiteId)

end Playable

open Playable

def mkSigBytes (env : List UInt8) : Option CrewFieldMission.SignatureBytes :=
  let fins : List (Fin 256) := env.map fun b => ⟨b.toNat, b.toFin.isLt⟩
  if h : fins.length = CrewFieldMission.SIGNATURE_BYTE_LENGTH then
    some ⟨fins, h⟩
  else none

def main (args : List String) : IO UInt32 := do
  let dir := (args[1]?).getD "."
  IO.println s!"playable mint succeeds       : {playableMember?.isSome}"
  IO.println s!"seat0 playerKey              : {Emit.bytes32Hex seat0Key}"
  IO.println s!"seat1 playerKey              : {Emit.bytes32Hex seat1Key}"
  match args[0]? with
  | some "emit" =>
      let m0 := seatMessage pSeat0
      let m1 := seatMessage pSeat1
      IO.FS.writeFile (dir ++ "/seat0_msg.hex") (hexOf m0)
      IO.FS.writeFile (dir ++ "/seat1_msg.hex") (hexOf m1)
      IO.FS.writeFile (dir ++ "/world.json") playableWorld.toJson
      IO.FS.writeFile (dir ++ "/manifest.json") playableManifest.toJson
      IO.println s!"seat0 admission message bytes: {m0.length}"
      IO.println s!"seat1 admission message bytes: {m1.length}"
      IO.println s!"wrote {dir}/seat0_msg.hex, seat1_msg.hex, world.json, manifest.json"
      pure 0
  | some "step" =>
      let s0hex ← IO.FS.readFile (dir ++ "/seat0_env.hex")
      let some s0 := bytesOfHex? s0hex | do IO.println "seat0 env not hex"; pure 1
      let some sig0 := mkSigBytes s0
        | do IO.println s!"seat0 env wrong length {s0.length}, want {CrewFieldMission.SIGNATURE_BYTE_LENGTH}"; pure 1
      let req : CrewFieldMissionRuntime.StepRequestWire := {
        activationId := playableRaw.activationId
        rosterBinding := playableRaw.rosterBinding
        transcript := []
        seatSignature := sig0
        decision := "specialist"
        decidedRoute := "signal-gallery"
        extraction := "none"
        command := "chart-pressure-route" }
      let envelope : StepEnvelopeWire := {
        world := playableWorld
        manifestJson := playableManifest.toJson
        stepRequestJson := req.toJson }
      let bytes := envelope.toJson
      IO.FS.writeFile (dir ++ "/envelope0.json") bytes
      let out := stepWire bytes
      IO.println s!"envelope bytes               : {bytes.length}"
      IO.println s!"stepWire answer length       : {out.length}"
      if out.isEmpty then
        IO.println "stepWire answer              : REFUSED (empty sentinel)"
        pure 1
      else
        IO.FS.writeFile (dir ++ "/step0_out.json") out
        match Lean.Json.parse out >>= (·.getObjValAs? String "signing_message") with
        | .error e => do IO.println s!"could not read signing_message: {e}"; pure 1
        | .ok msg => do
            IO.FS.writeFile (dir ++ "/handoff0_msg.hex") (hexOf msg.toUTF8.toList)
            IO.println s!"seat 0 handoff preimage bytes: {msg.toUTF8.size}"
            IO.println "SEAT 0 HAS ITS ORDERS. Sign handoff0_msg.hex, then run step2."
            pure 0
  | some "step2" =>
      -- transcript = [seat 0's completed, signed handoff]; asks: what does SEAT 1 sign?
      let readEnv (name : String) : IO (Option CrewFieldMission.SignatureBytes) := do
        let h ← IO.FS.readFile (dir ++ "/" ++ name)
        pure (bytesOfHex? h >>= mkSigBytes)
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
          activationId := playableRaw.activationId
          rosterBinding := playableRaw.rosterBinding
          transcript := tr
          seatSignature := seatSig
          decision := "specialist"
          decidedRoute := "signal-gallery"
          extraction := "none"
          command := "brace-transit" }
        StepEnvelopeWire.toJson
          { world := playableWorld, manifestJson := playableManifest.toJson,
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
      -- ---- REFUSAL POLE 1: seat 1's turn, presented with SEAT 0's admission envelope.
      let wrongSeat := mkEnv [trace0] sig0
      IO.println s!"[REFUSE wrong-seat envelope] mutation present: {wrongSeat != good}"
      IO.println s!"[REFUSE wrong-seat envelope] answer length   : {(stepWire wrongSeat).length}"
      -- ---- REFUSAL POLE 2: seat 1's admission envelope with ONE byte flipped.
      let flip (sb : CrewFieldMission.SignatureBytes) : CrewFieldMission.SignatureBytes :=
        let old := sb.bytes[2000]!
        let nv : Fin 256 := ⟨(old.val + 1) % 256, Nat.mod_lt _ (by omega)⟩
        ⟨sb.bytes.set 2000 nv, by simp [List.length_set, sb.length_eq]⟩
      let tampered := mkEnv [trace0] (flip sig1)
      IO.println s!"[REFUSE tampered signature] mutation present : {tampered != good}"
      IO.println s!"[REFUSE tampered signature] answer length    : {(stepWire tampered).length}"
      -- ---- REFUSAL POLE 3: the transcript replays, but the handoff signature is seat 1's admission.
      let forgedTrace := { trace0 with handoffSignature := sig1 }
      let forged := mkEnv [forgedTrace] sig1
      IO.println s!"[REFUSE forged trace sig] mutation present   : {forged != good}"
      IO.println s!"[REFUSE forged trace sig] answer length      : {(stepWire forged).length}"
      pure 0
  | _ => do IO.println "usage: emit|step <dir>"; pure 1
