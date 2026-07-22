(* Independent Standard ML twin of the HOL4 DREW-v1 witness checker. *)

datatype witnessBundle =
  WitnessBundle of {liveBytes : int list, row : int list}

val witnessVersion = 1

fun witnessBitsValid row =
  case row of
      [] => true
    | byte :: rest =>
        (byte = 0 orelse byte = 1) andalso witnessBitsValid rest

fun witnessLookup (row, atom) =
  case (row, atom) of
      ([], _) => false
    | (byte :: _, 0) => byte = 1
    | (_ :: rest, n) =>
        if n < 0 then false else witnessLookup (rest, n - 1)

fun sourceEval row source =
  case source of
      Atom atom => witnessLookup (row, atom)
    | Top => true
    | Bot => false
    | Not p => not (sourceEval row p)
    | And (p, q) => sourceEval row p andalso sourceEval row q
    | Or (p, q) => sourceEval row p orelse sourceEval row q

fun decodeWitnessBundle bytes =
  if not (bytesValid bytes) then NONE
  else
    case bytes of
        68 :: 82 :: 69 :: 87 :: version :: body =>
          if version <> witnessVersion then NONE
          else
            (case decodeU32 body of
                 SOME (liveLength, afterLiveLength) =>
                   (case decodeU32 afterLiveLength of
                        SOME (witnessLength, payload) =>
                          if liveLength > maxSectionBytes orelse
                             witnessLength > maxSectionBytes then NONE
                          else
                            (case splitExact liveLength payload of
                                 SOME (liveBytes, afterLive) =>
                                   (case splitExact witnessLength afterLive of
                                        SOME (row, []) =>
                                          SOME (WitnessBundle
                                            {liveBytes = liveBytes, row = row})
                                      | _ => NONE)
                               | NONE => NONE)
                      | NONE => NONE)
               | NONE => NONE)
      | _ => NONE

fun checkWitnessBundle
    (WitnessBundle {liveBytes, row}) =
  checkLiveBytes liveBytes andalso
  (case decodeLiveBundle liveBytes of
       SOME (LiveBundle {atomCount, v1Bytes, ...}) =>
         listLength row = atomCount andalso
         witnessBitsValid row andalso
         (case decodeBundle v1Bytes of
              SOME {source, ...} => sourceEval row source
            | NONE => false)
     | NONE => false)

fun checkWitnessBytes bytes =
  case decodeWitnessBundle bytes of
      SOME bundle => checkWitnessBundle bundle
    | NONE => false

fun packWitnessUnchecked (liveBytes, row) =
  case (encodeU32 (listLength liveBytes), encodeU32 (listLength row)) of
      (SOME liveLength, SOME witnessLength) =>
        SOME ([68, 82, 69, 87, witnessVersion] @@ liveLength @@
              witnessLength @@ liveBytes @@ row)
    | _ => NONE

fun certifyWitnessBytes (liveBytes, row) =
  if not (checkLiveBytes liveBytes) orelse not (witnessBitsValid row) then NONE
  else
    case decodeLiveBundle liveBytes of
        SOME (LiveBundle {atomCount, ...}) =>
          if listLength row <> atomCount orelse
             listLength liveBytes > maxSectionBytes orelse
             listLength row > maxSectionBytes then NONE
          else packWitnessUnchecked (liveBytes, row)
      | NONE => NONE
