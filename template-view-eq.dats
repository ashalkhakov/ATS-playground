(*
 * view equalities in templates
 *)
#include
"share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

#define N 5

extern
fun{env:vt@ype}
loop$fwork (natLt(N), &(env) >> _): void

extern
fun{env:vt@ype}
loop (&(env) >> _): void

implement{env}
loop (env) = {
  var ix : int = 0
  val () =
  // please disregard the [while] loop,
  // just an exercise
  while* {i:nat | i <= N} .<N-i>. (ix: int i) =>
    (ix < N) {
    val () = loop$fwork<env> (ix, env)
    val () = ix := ix + 1
  } // end of [val]
} (* end of [loop] *)

implement
main0 () = {
//
var A = @[int][N](0,1,2,3,4,5,6,7,8,9)
var B = @[int][N](9,8,7,6,5,6,7,8,9,0)
var C = @[int][N](0)
//
absvt@ype VT = void
assume VT = (@[int][N] @ A, @[int][N] @ B, @[int][N] @ C | void)
//
implement
loop$fwork<VT> (i, env) = {
  val x = A.[i] + B.[i]
  val () = C.[i] := x
  val () = println!(x)
}
//
var env = (view@A, view@B, view@C | ())
val () = loop<VT> (env)
//
prval () = view@A := env.0
and () = view@B := env.1
and () = view@C := env.2
//
} (* end of [main0] *)
