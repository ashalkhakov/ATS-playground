(*
** Hello, world!
**
** Q: how to extract substring of input string ending at the first unclosed parens?
**    ex. sldfkjsf(sldfkj)lskdjff(sdfsdf) -- this is balanced, return as-is
**    ex. (sldfkj(sdfsdf(sdfsdf(sdfsdf)sdf)sdf)sdfsdf -- this is NOT balanced, first paren is unclosed (result should be empty)
**    ex. esdfd((esdf)(esdf -- first paren is unclosed, should give esdfd
** A: see below
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

%{^
function
EXT_string_is_atend (s, i) {
  return (i < s.length)? false : true;
}
function
EXT_string_substring (s, beg_, end_) {
  //alert("substring from: " + beg_ + " to " + end_);
  var res = s.substring (beg_, end_);
  //alert("Input : " + s);
  //alert("Result: " + res);
  return res;
}
function
EXT_prompt(msg) {
  return prompt(msg);
}
%}
extern
fun
string_is_atend {n,i:nat}
  (string (n), int i): bool (i >= n) = "mac#EXT_string_is_atend"
extern
fun
string_substring {n,i1,i2:nat | i1 <= n; i2 <= n; i1 <= i2}
  (string (n), int i1, int i2): string (i2-i1) = "mac#EXT_string_substring"
extern
fun
prompt (msg: string): string = "mac#"
//
(* ****** ****** *)
//
extern
fun
peculiar_split (string): Option string = "mac#"
implement
peculiar_split (s) = let
  fun
  myfun {n,i:nat | i <= n}
  (s: string n, i: int i, stk: List (natLt(n))): Option string =
    if string_is_atend (s, i) then let
      val stk = list_reverse (stk)
    in
      case+ stk of
      | list_nil () => None ()
      | list_cons (i, _) => Some (string_substring (s, 0, i))
    end else let
      val c = string_charAt (s, i)
      //val () = print(c)
      prval () = lemma_list_param (stk)
    in
      case+ c of
      | "(" => myfun (s, succ(i), list_cons (i, stk))
      | ")" => (
          case+ stk of
          | list_nil () => None ()
          | list_cons (_, stk) => myfun (s, succ(i), stk)
        )
      | _ => myfun (s, succ(i), stk)
    end
  // end of [myfun]
  val s = (g1ofg0)s
  prval () = lemma_string_param (s)
in
  myfun (s, 0, list_nil ())
end // end of [peculiar_split]
//
extern
fun
hello(): void = "mac#"
implement
hello() = let
  val s = prompt "Input string with unbalanced parens"
in
  case+ peculiar_split s of
  | None () => print("none!")
  | Some sub => print sub
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