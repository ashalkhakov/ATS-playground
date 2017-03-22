#include
"share/atspre_staload.hats"

staload "prelude/SATS/string.sats"

(* ****** ****** *)

extern
fun base64_encode : uint -> uchar

extern
fun base64_decode : uchar -> int

(* ****** ****** *)

local

val encoding = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

in

implement
base64_encode (x) = let
  val i = g1uint2int(g1ofg0(x))
in
  if i > 63 then char2uchar0('=') // error?
  else char2uchar0(string_get_at_gint(encoding, i))
end // end of [base64_encode]

end // end of [local]

(* ****** ****** *)

local

val decoding = @[int](62,~1,~1,~1,63,52,53,54,55,56,57,58,59,60,61,~1,~1,~1,~2,~1,~1,~1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,~1,~1,~1,~1,~1,~1,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51)

in // end of [in]

implement
base64_decode (x) = let
  val c = g1ofg0 (uchar2int0 (x) - 43)
in
  if c >= 0 then (if c < 80 then decoding.[c] else ~1)
  else ~1
end

end // end of [local]

(* ****** ****** *)
