(*
** Hello, world!
** Q: what's a good way to *not* mix up = and == operators in a conditional?
** A: a good way is via typed programming
*)

(* ****** ****** *)

#include
"share/atspre_define.hats"
#include
"{$LIBATSCC2JS}/staloadall.hats"

(* ****** ****** *)

staload
"{$LIBATSCC2JS}/SATS/print.sats"

(* ****** ****** *)

#define ATS_MAINATSFLAG 1
#define ATS_DYNLOADNAME "my_dynload"

(* ****** ****** *)
//
extern
fun
hello(): void = "mac#"
implement
hello() = let

val x = ref {int} 5 (* create mutable reference *)
val () = println!("x = ", x[]) (* check what value it contains *)
val () = x[] := 10 (* assign new value *)
val () = println!("x = ", x[])
val () =
  if x[] = 5 then println!("wow") (* equality check *)
  else println!("nope")
(*
 * fails type-checking ("void" not the same as "bool"):
val () =
  if x[] := 5 then println!("wow")
  else println!("nope")
*)
in
  // empty
end
//
(* ****** ****** *)
//
val () = hello()
//
(* ****** ****** *)

%{$
//
ats2jspre_the_print_store_clear();
my_dynload();
alert(ats2jspre_the_print_store_join());
//
%} // end of [%{$]
