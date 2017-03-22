// nullable unboxed datatype
// inspired by Boost.RDB

#include
"share/atspre_define.hats"
#include
"share/atspre_staload.hats"

(* ****** ****** *)
//
absviewt@ype nullable(a:t@ype+, bool) = @(a, bool)
//
viewtypedef nullable (a:t@ype) = [b:bool] nullable (a, b)
//
(* ****** ****** *)
//
extern
fun{a:t@ype}
nullable_make_some (x: a): nullable (a, true)
//
extern
fun{a:t@ype}
nullable_make_none (): nullable (a, false)
//
extern
castfn
nullable_free {a:t@ype} {b:bool} (x: !nullable (a) >> nullable (a, b)?): void
//
extern
fun{a:t@ype}
nullable_has_value {b:bool} (x: &nullable (a, b)): bool b
//
extern
fun{a:t@ype}
nullable_get_value (x: &nullable (a, true)): a
//
extern
fun{a:t@ype}
nullable_set_value {b:bool} (x: &nullable (a, b) >> nullable (a, true), y: a): void
//
extern
fun{a:t@ype}
nullable_clear_value (x: &nullable (a) >> nullable (a, false)): void
//
(* ****** ****** *)

// it would be better to store nilable bits in a bitvector,
// once per record, rather than once per datum, even if
// the datum is unboxed, right?
// - some data is inherently nilable (e.g. strings)

local

assume nullable (a:vt@ype, b:bool) = @(opt (a, b), bool b)

in

implement{a}
nullable_make_some (x) = let
//
  var tup = @(x, true)
  prval () = opt_some {a} (tup.0)
  val res = tup
  prval () = opt_unsome {a} (tup.0)
//
in
  res
end // end of [nullable_make_some]

implement{a}
nullable_make_none () = let
//
  var tup : @(a, bool) // uninitialized
  val () = tup.1 := false
  prval () = opt_none {a} (tup.0)
  val res = tup
  prval () = opt_unnone {a} (tup.0)
//
in
  res
end // end of [nullable_make_none]

(*
// NOTE: cannot be implemented because
// opt (a, b) is linear, even though a is non-linear in this case
implement{a}
nullable_free (x) = {
  prval () = opt_clear {a} (x.0)
  prval () = opt_none {a} (x.0)
  prval () = topize {opt (a, false)} (x)
} // end of [nullable_free]
*)

implement{a}
nullable_has_value {b} (x) = x.1

implement{a}
nullable_get_value (x) = let
  prval () = opt_unsome {a} (x.0)
  val res = x.0
  prval () = opt_some {a} (x.0)
in
  res
end // end of [nullable_get_value]

implement{a}
nullable_set_value {b} (x, y) = {
  prval () = opt_clear {a} (x.0)
  val () = x.0 := y
  prval () = opt_some {a} (x.0)
  val () = x.1 := true
} (* end of [nullable_set_value] *)

implement{a}
nullable_clear_value (x) = {
  prval () = opt_clear {a} (x.0)
  prval () = opt_none {a} (x.0)
  val () = x.1 := false
}

end

(* ****** ****** *)

implement
main (argc, arg) = let
  var x = nullable_make_some<int> (5)
  var y = nullable_make_none<int> ()
  val () = println! ("x has value = ", nullable_has_value (x))
  val () = println! ("x = ", nullable_get_value<int> (x))
  val () = println! ("y has value = ", nullable_has_value (y))
  val () = nullable_set_value (y, 3)
  val () = println! ("y = ", nullable_get_value<int> (y))
  val () = nullable_clear_value (x)
  val () = println! ("x has value = ", nullable_has_value<int> (x))
  val () = nullable_free (y)
  val () = nullable_free (x)
in
  0
end // end of [main]
