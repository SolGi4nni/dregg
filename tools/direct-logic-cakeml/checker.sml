(*
 * DREG direct-logic certificate checker, wire version 1.
 *
 * This is an intentionally small, independent Standard ML implementation of
 * the wire contract fixed by
 * Dregg2.Logic.CompilationCertificateBundle.  It has no JSON parser, no proof
 * system, and no trusted target supplied out of band: acceptance reconstructs
 * the unique target tree from the decoded source and compares it structurally.
 *
 * The code uses only first-order datatypes, lists, integer comparison, and
 * structural recursion.  That keeps it in the fragment represented directly
 * by the sibling HOL4 definitions and CakeML's proof-producing translator.
 *)

datatype source =
    Atom of int
  | Top
  | Bot
  | Not of source
  | And of source * source
  | Or of source * source

datatype target =
    Input of int
  | Truth
  | Falsity
  | Inv of target
  | Conj of target * target
  | Disj of target * target

type bundle = {version : int, source : source, target : target}

val currentVersion = 1

fun lower source =
  case source of
      Atom atom => Input atom
    | Top => Truth
    | Bot => Falsity
    | Not p => Inv (lower p)
    | And (p, q) => Conj (lower p, lower q)
    | Or (p, q) => Disj (lower p, lower q)

fun targetEqual (left, right) =
  case (left, right) of
      (Input a, Input b) => a = b
    | (Truth, Truth) => true
    | (Falsity, Falsity) => true
    | (Inv a, Inv b) => targetEqual (a, b)
    | (Conj (a, b), Conj (c, d)) =>
        targetEqual (a, c) andalso targetEqual (b, d)
    | (Disj (a, b), Disj (c, d)) =>
        targetEqual (a, c) andalso targetEqual (b, d)
    | _ => false

fun checkBundle ({version, source, target} : bundle) =
  version = currentVersion andalso targetEqual (target, lower source)

fun byteValid byte = 0 <= byte andalso byte < 256

fun bytesValid bytes =
  case bytes of
      [] => true
    | byte :: rest => byteValid byte andalso bytesValid rest

fun listLength xs =
  case xs of
      [] => 0
    | _ :: rest => 1 + listLength rest

(* A successful canonical term needs at most its byte length as depth.  Fuel
 * also makes every malformed recursive input terminate in the logical model. *)
fun decodeSourceFuel fuel bytes =
  if fuel = 0 then NONE
  else
    case bytes of
        [] => NONE
      | tag :: rest =>
          if tag = 0 then
            (case rest of
                 atom :: tail => SOME (Atom atom, tail)
               | [] => NONE)
          else if tag = 1 then SOME (Top, rest)
          else if tag = 2 then SOME (Bot, rest)
          else if tag = 3 then
            (case decodeSourceFuel (fuel - 1) rest of
                 SOME (p, tail) => SOME (Not p, tail)
               | NONE => NONE)
          else if tag = 4 then
            (case decodeSourceFuel (fuel - 1) rest of
                 SOME (p, tail) =>
                   (case decodeSourceFuel (fuel - 1) tail of
                        SOME (q, tail') => SOME (And (p, q), tail')
                      | NONE => NONE)
               | NONE => NONE)
          else if tag = 5 then
            (case decodeSourceFuel (fuel - 1) rest of
                 SOME (p, tail) =>
                   (case decodeSourceFuel (fuel - 1) tail of
                        SOME (q, tail') => SOME (Or (p, q), tail')
                      | NONE => NONE)
               | NONE => NONE)
          else NONE

fun decodeTargetFuel fuel bytes =
  if fuel = 0 then NONE
  else
    case bytes of
        [] => NONE
      | tag :: rest =>
          if tag = 16 then
            (case rest of
                 atom :: tail => SOME (Input atom, tail)
               | [] => NONE)
          else if tag = 17 then SOME (Truth, rest)
          else if tag = 18 then SOME (Falsity, rest)
          else if tag = 19 then
            (case decodeTargetFuel (fuel - 1) rest of
                 SOME (a, tail) => SOME (Inv a, tail)
               | NONE => NONE)
          else if tag = 20 then
            (case decodeTargetFuel (fuel - 1) rest of
                 SOME (a, tail) =>
                   (case decodeTargetFuel (fuel - 1) tail of
                        SOME (b, tail') => SOME (Conj (a, b), tail')
                      | NONE => NONE)
               | NONE => NONE)
          else if tag = 21 then
            (case decodeTargetFuel (fuel - 1) rest of
                 SOME (a, tail) =>
                   (case decodeTargetFuel (fuel - 1) tail of
                        SOME (b, tail') => SOME (Disj (a, b), tail')
                      | NONE => NONE)
               | NONE => NONE)
          else NONE

fun decodeBundle bytes =
  if not (bytesValid bytes) then NONE
  else
    case bytes of
        68 :: 82 :: 69 :: 71 :: version :: body =>
          if version <> currentVersion then NONE
          else
            (case decodeSourceFuel (listLength bytes) body of
                 SOME (source, rest) =>
                   (case decodeTargetFuel (listLength bytes) rest of
                        SOME (target, []) =>
                          SOME {version = version,
                                source = source,
                                target = target}
                      | _ => NONE)
               | NONE => NONE)
      | _ => NONE

fun checkBytes bytes =
  case decodeBundle bytes of
      SOME bundle => checkBundle bundle
    | NONE => false

