(*
 * DREG live direct-logic certificate checker, wire version 2.
 *
 * Version 2 composes, rather than replaces, the version-1 checker.  Its first
 * payload is a complete length-delimited DREG-v1 certificate.  The second is
 * the exact ASCII JSON emitted for the live EffectVmDescriptor2.  Acceptance
 * checks v1, extracts its source, checks the atom bound, reconstructs every
 * gate and layout byte, and compares the supplied JSON byte-for-byte.
 *)

datatype liveBundle =
  LiveBundle of {atomCount : int, v1Bytes : int list, descriptorBytes : int list}

val liveVersion = 2
val maxAtomCount = 256
val maxSectionBytes = 1048576

fun append (left, right) =
  case left of
      [] => right
    | x :: xs => x :: append (xs, right)

infixr 5 @@
fun left @@ right = append (left, right)

fun ascii text = List.map Char.ord (String.explode text)

fun reverseOnto (xs, acc) =
  case xs of
      [] => acc
    | x :: rest => reverseOnto (rest, x :: acc)

fun reverse xs = reverseOnto (xs, [])

fun natDigitsRev fuel n =
  if fuel = 0 then []
  else
    let
      val digit = 48 + (n mod 10)
    in
      if n < 10 then [digit]
      else digit :: natDigitsRev (fuel - 1) (n div 10)
    end

fun natAscii n =
  if n < 0 then [] else reverse (natDigitsRev (n + 1) n)

fun jsonConst value =
  ascii "{\"t\":\"const\",\"v\":" @@ ascii value @@ ascii "}"

val jsonZero = jsonConst "0"
val jsonOne = jsonConst "1"
val jsonNegOne = jsonConst "-1"

fun jsonLoc column =
  ascii "{\"t\":\"loc\",\"c\":" @@ natAscii column @@ ascii "}"

fun jsonMul (left, right) =
  ascii "{\"t\":\"mul\",\"l\":" @@ left @@
  ascii ",\"r\":" @@ right @@ ascii "}"

fun jsonAdd (left, right) =
  ascii "{\"t\":\"add\",\"l\":" @@ left @@
  ascii ",\"r\":" @@ right @@ ascii "}"

fun jsonNeg value = jsonMul (jsonNegOne, value)
fun jsonOneMinus value = jsonAdd (jsonOne, jsonNeg value)

fun sourcePolynomial source =
  case source of
      Atom atom => jsonLoc atom
    | Top => jsonOne
    | Bot => jsonZero
    | Not p => jsonOneMinus (sourcePolynomial p)
    | And (p, q) => jsonMul (sourcePolynomial p, sourcePolynomial q)
    | Or (p, q) =>
        let
          val left = sourcePolynomial p
          val right = sourcePolynomial q
        in
          jsonAdd (jsonAdd (left, right), jsonNeg (jsonMul (left, right)))
        end

fun binaryBody column =
  jsonMul (jsonLoc column, jsonAdd (jsonLoc column, jsonNegOne))

fun windowGate body =
  ascii "{\"t\":\"window_gate\",\"on_transition\":false,\"body\":" @@
  body @@ ascii "}"

fun binaryGatesFrom (column, atomCount) =
  if column >= atomCount then []
  else windowGate (binaryBody column) :: binaryGatesFrom (column + 1, atomCount)

fun joinComma values =
  case values of
      [] => []
    | [value] => value
    | value :: rest => value @@ ascii "," @@ joinComma rest

fun descriptorBytes (atomCount, source) =
  let
    val atomText = natAscii atomCount
    val accept = windowGate (jsonAdd (sourcePolynomial source, jsonNegOne))
    val constraints =
      ascii "[" @@ joinComma (binaryGatesFrom (0, atomCount) @ [accept]) @@ ascii "]"
  in
    ascii "{\"name\":\"dregg-finite-logic-v2-" @@ atomText @@
    ascii "\",\"ir\":2,\"trace_width\":" @@ atomText @@
    ascii ",\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":" @@
    atomText @@ ascii ",\"sem\":\"main\"}],\"constraints\":" @@ constraints @@
    ascii ",\"hash_sites\":[],\"ranges\":[]}" 
  end

fun atomsBelow (atomCount, source) =
  case source of
      Atom atom => 0 <= atom andalso atom < atomCount
    | Top => true
    | Bot => true
    | Not p => atomsBelow (atomCount, p)
    | And (p, q) => atomsBelow (atomCount, p) andalso atomsBelow (atomCount, q)
    | Or (p, q) => atomsBelow (atomCount, p) andalso atomsBelow (atomCount, q)

fun encodeSource source =
  case source of
      Atom atom => [0, atom]
    | Top => [1]
    | Bot => [2]
    | Not p => 3 :: encodeSource p
    | And (p, q) => 4 :: (encodeSource p @@ encodeSource q)
    | Or (p, q) => 5 :: (encodeSource p @@ encodeSource q)

fun encodeTarget target =
  case target of
      Input atom => [16, atom]
    | Truth => [17]
    | Falsity => [18]
    | Inv p => 19 :: encodeTarget p
    | Conj (p, q) => 20 :: (encodeTarget p @@ encodeTarget q)
    | Disj (p, q) => 21 :: (encodeTarget p @@ encodeTarget q)

fun certifyV1 source =
  let val bytes = [68, 82, 69, 71, 1] @@ encodeSource source @@ encodeTarget (lower source)
  in if bytesValid bytes then SOME bytes else NONE end

fun u32Valid n = 0 <= n andalso n < 4294967296

fun encodeU32 n =
  if not (u32Valid n) then NONE
  else SOME [n div 16777216,
             (n div 65536) mod 256,
             (n div 256) mod 256,
             n mod 256]

fun decodeU32 bytes =
  case bytes of
      a :: b :: c :: d :: rest =>
        SOME (a * 16777216 + b * 65536 + c * 256 + d, rest)
    | _ => NONE

fun splitExact count bytes =
  if count = 0 then SOME ([], bytes)
  else if count < 0 then NONE
  else
    case bytes of
        [] => NONE
      | byte :: rest =>
          (case splitExact (count - 1) rest of
               SOME (prefix, trailing) => SOME (byte :: prefix, trailing)
             | NONE => NONE)

fun decodeLiveBundle bytes =
  if not (bytesValid bytes) then NONE
  else
    case bytes of
        68 :: 82 :: 69 :: 71 :: version :: body =>
          if version <> liveVersion then NONE
          else
            (case decodeU32 body of
                 SOME (atomCount, afterAtomCount) =>
                   (case decodeU32 afterAtomCount of
                        SOME (v1Length, afterV1Length) =>
                          (case decodeU32 afterV1Length of
                               SOME (descriptorLength, payload) =>
                                 if atomCount > maxAtomCount orelse
                                    v1Length > maxSectionBytes orelse
                                    descriptorLength > maxSectionBytes then NONE
                                 else
                                   (case splitExact v1Length payload of
                                        SOME (v1Bytes, afterV1) =>
                                          (case splitExact descriptorLength afterV1 of
                                               SOME (descriptorBytes, []) =>
                                                 SOME (LiveBundle
                                                   {atomCount = atomCount,
                                                    v1Bytes = v1Bytes,
                                                    descriptorBytes = descriptorBytes})
                                             | _ => NONE)
                                      | NONE => NONE)
                             | NONE => NONE)
                      | NONE => NONE)
               | NONE => NONE)
      | _ => NONE

fun checkLiveBundle (LiveBundle {atomCount, v1Bytes, descriptorBytes = claimedDescriptor}) =
  checkBytes v1Bytes andalso
  (case decodeBundle v1Bytes of
       SOME ({source, ...} : bundle) =>
         atomsBelow (atomCount, source) andalso
         claimedDescriptor = descriptorBytes (atomCount, source)
     | NONE => false)

fun checkLiveBytes bytes =
  case decodeLiveBundle bytes of
      SOME bundle => checkLiveBundle bundle
    | NONE => false

fun certifyLiveBytes (atomCount, source) =
  if atomCount < 0 orelse atomCount > maxAtomCount orelse
     not (atomsBelow (atomCount, source)) then NONE
  else
    case certifyV1 source of
        NONE => NONE
      | SOME v1Bytes =>
          let
            val json = descriptorBytes (atomCount, source)
          in
            if listLength v1Bytes > maxSectionBytes orelse
               listLength json > maxSectionBytes then NONE
            else
              case (encodeU32 atomCount,
                    encodeU32 (listLength v1Bytes),
                    encodeU32 (listLength json)) of
                  (SOME atomBytes, SOME v1Length, SOME jsonLength) =>
                    SOME ([68, 82, 69, 71, liveVersion] @@ atomBytes @@
                          v1Length @@ jsonLength @@ v1Bytes @@ json)
                | _ => NONE
          end
