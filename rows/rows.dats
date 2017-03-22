#include
"share/atspre_define.hats"
#include
"share/atspre_staload.hats"

// TODO: generic functions on top of flat tuples
// - print, fprint (should be simple?)
// - comparison, equality (only compare two tuples if they have the same type)
// - other stuff
//   - replace an element (done)
//   - concat two tuples (shouldn't be too hard to do)
// - complex stuff of limited utility
//   - project out fields from a tuple (kind of like D4's over/except)
//   - rows (tuples with named fields)
// - other stuff (useful for data access/database interaction)
//   - efficient optional fields in tuples (flat Option_vt, or even better, a separate bitset)
//   - tuple schemas (tuple types)
//   - tuple difference/"patch" for change tracking: given two instances of T,
//     x and y, find out how to get y from x
// - nested tuples? how would that work? ideally, we want zero overhead from that
//   - lenses... because we can't be bothered to repeat stuff
// - variadic function call with such a tuple?
//   - yup, that's right!
//   - fun apply: (t0ypes (T, ts), (&T)->R, &T): R // isn't the same as usual fun.app?
//   - e.g., invoking a database select

(*
// NOTE: actually, we can make things simpler!
// - identify the repeated tupling with HX's approach to compile-time integers (typeval)

dataprop tupeq (type, int, t@ype, t@ype) =
  | TUPEQZ (Z(), 0, empty, empty)
  | {t:type}{n:nat}{a,b,c:t@ype}
    TUPEQS (S(t), n+1, @(a, b), a) of tupeq (t, n, b, c)

extern
fun{t:t@ype}{N:type}{a:t@ype}
tup_get_at_val {n:int} (
  tupeq (N, n, t, a)
| tup: &t, int n
) :<!wrt> a

extern
fun{t:t@ype}{N:type}{a:t@ype}
tup_set_at_val {n:int} (
  tupeq (N, n, t, a)
| tup: &t, int n, a
) :<!wrt> void

*)

abstype t0ype_t (t@ype) // some unknown representation
// some constructors
extern
val t0ype_int : t0ype_t (int)
extern
val t0ype_float : t0ype_t (float)
extern
val t0ype_string : t0ype_t (string)

dataprop TypeEq (t@ype, t@ype) =
  | {a:t@ype} TErefl (a, a)

// some functions
extern
fun eq_t0ype_t0ype : {a,b:t@ype} (t0ype_t (a), t0ype_t (b)) -> [r:bool] (option_p (TypeEq (a, b), r) | bool r)
overload = with eq_t0ype_t0ype

datasort t0ypes = t0ypes_nil | t0ypes_cons of (t@ype, t0ypes)

dataprop t0ypes_length (t0ypes, int) =
  | t0ypes_length_zero (t0ypes_nil, 0)
  | {ts:t0ypes;t:t@ype;n:nat}
      t0ypes_length_succ (t0ypes_cons (t, ts), n+1) of t0ypes_length (ts, n)

dataprop in_t0ypes (t@ype, t0ypes, int) =
  | {ts:t0ypes;t:t@ype} in_t0ypes_zero (t, t0ypes_cons (t, ts), 0)
  | {ts:t0ypes;t,t':t@ype;i:nat}
      in_t0ypes_succ (t, t0ypes_cons (t', ts), i+1) of in_t0ypes (t, ts, i)

// NOTE: we could expose this as an abstract type
// not very efficient (just an a-list)
datatype t0ypes_t (t0ypes) = // types representation
  | t0ypes_t_nil (t0ypes_nil)
  | {ts:t0ypes; t:t@ype}
      t0ypes_t_cons (t0ypes_cons (t, ts)) of (t0ype_t (t), t0ypes_t (ts))

// NOTE: we could expose this as an abstract type
// not very efficient (just an a-list)
datatype labt0ypes_t (t0ypes) = // labeled types representation
  | labt0ypes_t_nil (t0ypes_nil)
  | {ts:t0ypes;t:t@ype}
      labt0ypes_t_cons (t0ypes_cons (t, ts)) of
        (string, t0ype_t t, labt0ypes_t ts)

// given t0ypes_t, we can hopefully write some functions?
// at run-time: go over the spine of [inf]
// tuple_t is a just a pointer to a flat tuple
// also at run-time, we must somehow always use the right type sizes to account
// for padding in the structure (or use offsetof...)

// the empty tuple
datatype empty = Empty

// simple mapping from t0ypes to a concrete type
// (think Ur/Web's $ operator of kind {Type} -> Type)
dataprop tuple_of_t0ypes (t0ypes, t@ype) =
  // just for simplicity! judging by relational stuff, we will need empty tuples too
  | tuple_nil (t0ypes_nil, empty)
  | {t:t@ype} {t':t@ype} {ts:t0ypes} tuple_cons (t0ypes_cons (t, ts), @(t, t')) of tuple_of_t0ypes (ts, t')

extern
prfun tuple_of_t0ypes_is_fun : {ts:t0ypes;t1,t2:t@ype}
  (tuple_of_t0ypes (ts, t1), tuple_of_t0ypes (ts, t2)) -<prf> TypeEq (t1, t2)

dataprop t0ypes_eq (t0ypes, t0ypes) =
  | {ts:t0ypes} t0ypes_eq_refl (ts, ts)

extern
prfun tuple_of_t0ypes_is_one_to_one : {ts1,ts2:t0ypes;t:t@ype}
  (tuple_of_t0ypes (ts1, t), tuple_of_t0ypes (ts2, t)) -<prf> t0ypes_eq (ts1, ts2)

#define nil t0ypes_nil
#define cons t0ypes_cons

extern
prfun in_t0ypes_index_lemma :
  {a:t@ype;ts:t0ypes;i:int}
  in_t0ypes (a, ts, i) -<prf> [i >= 0] void

// revisiting the general selection function:

// t0ype_in_t0ypes (a, ts, x, i) means:
// a is i'th element of tuple x
dataprop t0ype_in_t0ypes (t@ype, t0ypes, t@ype, int) =
  | {t,t':t@ype} {ts:t0ypes} t0ype_in_t0ypes_zero (t, t0ypes_cons (t, ts), @(t, t'), 0)
  | {x:t@ype} {t,t':t@ype} {ts:t0ypes;i:nat;ofs:int}
      t0ype_in_t0ypes_succ (t, t0ypes_cons (t', ts), @(t', x), i+1) of
        t0ype_in_t0ypes (t, ts, x, i)

extern
prfun t0ype_in_t0ypes_index_lemma :
  {a,b:t@ype;ts:t0ypes;i:int}
  t0ype_in_t0ypes (a, ts, b, i) -<prf> [i >= 0] void

extern
fun{t:t@ype}{a:t@ype}
tuple_get_at {ts:t0ypes;i:int}
(pf_in: t0ype_in_t0ypes (a, ts, t, i) | tup: &t, i: int i, res: &a? >> a): void

(* ****** ****** *)
//
// offset_at (a, b, o) is read "offset of a embedded in b is o"
absprop offset_at (t@ype, t@ype, int)
//
extern
fun{a:t@ype}{b:t@ype}
  offset_pair_snd {l:addr} (pfat: !(@(a,b) @ l) | p: ptr l)
  : [o:int] (offset_at (b, @(a,b), o) | size_t o)
//
extern
prfun
  offset_at_elim :
  {a,t:t@ype} {l:addr} {o:int}
  (offset_at (a, t, o), t @ l) -<prf> vtakeout (t @ l, a @ (l+o))
//
extern
prfun
  offset_at_zero :
  {a,b:t@ype}
  () -<prf> offset_at (a, @(a, b), 0)
//
extern
prfun
  offset_at_cons :
  {a,b,c:t@ype} {o_bc,o_a:int} (
    offset_at (c, @(b, c), o_bc), offset_at (a, c, o_a)
  ) -<prf> offset_at (a, @(b, c), o_bc + o_a)
//
extern
prfun offset_at_lemma :
  {a,t:t@ype} {o:int}
  offset_at (a, t, o) -<prf> [o >= 0] void
//
(* ****** ****** *)
//
implement{a}{b}
offset_pair_snd {l} (pfat | p) = (pf | diff1) where {
//
val diff0 = g0ofg1(addr@((!p).1) - p)
val () = assert_errmsg (diff0 >= 0, "offset_pair_snd: negative offset!")
val diff1 = g1ofg0 (g0int2uint_ssize_size diff0)
prval pf = _proof () where {
  extern prfun _proof {o: int} () : offset_at (b, @(a,b), o)
} // end of [prval]
//
} (* end of [offset_pair_snd] *)
//
(* ****** ****** *)
//
// external API
//
abst@ype offset_t (t@ype+, t@ype+, int) = size_t
typedef Offset_t (a:t@ype, b:t@ype) = [o:int] offset_t (a, b, o)
//
extern
fun{t:t@ype}{a:t@ype}
offset_of {ts:t0ypes;i:int} (
  pf_in: t0ype_in_t0ypes (a, ts, t, i)
| tup: &t, i: int i
) : Offset_t (a, t)
//
//
extern
fun{t:t@ype}{a:t@ype}
tup_get_at (tup: &t, ofs: Offset_t (a, t), res: &a? >> a)
  :<!wrt> void
//
extern
fun{t:t@ype}{a:t@ype}
tup_get_at_val (tup: &t, ofs: Offset_t (a, t)):<!wrt> a
//
extern
fun{t:t@ype}{a:t@ype}
tup_set_at (tup: &t, ofs: Offset_t (a, t), x: &a)
  :<!wrt> void
//
extern
fun{t:t@ype}{a:t@ype}
tup_set_at_val (tup: &t, ofs: Offset_t (a, t), a):<!wrt> void
//
(* ****** ****** *)

extern
fun{t:t@ype}
tup_fprint {ts:t0ypes} (tuple_of_t0ypes (ts, t) | FILEref, tup: &t): void

extern
fun{t:t@ype}
tup_print {ts:t0ypes} (tuple_of_t0ype (ts, t) | &t): void

(* ****** ****** *)
//
// implementation of the external API
//
local
//
assume
offset_t (a:t@ype, t:t@ype, o:int) = (
  offset_at (a, t, o)
| size_t o
) (* end of [offset_t] *)
//
in // of [local]
//
implement{t}{a}
offset_of {ts,i} (pfin | tup, i) = let
  // TODO: make tail-recursive!
  // TODO: just make it a compile-time operation,
  // by making sure [i] is static (see more recent
  // work on expression templates/compile-time indexing)
  fun{t:t@ype}{a:t@ype}
    aux {ts:t0ypes;i:nat} {l:addr} .<i>. (
      pfat: !(t @ l)
    , pfin: t0ype_in_t0ypes (a, ts, t, i)
    | p: ptr l, i: int i
    ) : [o:int] (offset_at (a, t, o) | size_t o) =
  (
    if i = 0 then let
      prval t0ype_in_t0ypes_zero {a,b'} () = pfin
    in
      (offset_at_zero () | (i2sz)0)
    end else let
      prval t0ype_in_t0ypes_succ {x} {b,b'} (pfin1) = pfin
      val (pfofs1 | ofs1) = offset_pair_snd<b'><x> (pfat | p)
      prval (pfat1, pf_funat) = offset_at_elim (pfofs1, pfat)
      val p1 = add_ptr1_bsz (p, ofs1)
      val (pfofs2 | ofs2) = aux<x><a> (pfat1, pfin1 | p1, i-1)
      prval () = pfat := pf_funat (pfat1)
      prval pfres = offset_at_cons (pfofs1, pfofs2)
    in
      (pfres | (ofs1 + ofs2))
    end
  ) // end of [aux]
  prval () = t0ype_in_t0ypes_index_lemma (pfin)
  val (pf_ofs0 | ofs0) = aux<t><a> (view@(tup), pfin | addr@(tup), i)
in
  (pf_ofs0 | ofs0)
end // end of [offset_of]

(* ****** ****** *)

implement{t}{a}
tup_get_at (tup, ofs, res) = {
//
val p = addr@(tup)
prval (pfat, pffunat) = offset_at_elim {a,t} (ofs.0, view@(tup))
val p = add_ptr1_bsz (p, ofs.1)
val () = res := !p
prval () = view@(tup) := pffunat(pfat)
//
} (* end of [tup_get_at] *)

implement{t}{a}
tup_get_at_val (tup, ofs) = res where {
//
val p = addr@(tup)
prval (pfat, pffunat) = offset_at_elim {a,t} (ofs.0, view@(tup))
val p = add_ptr1_bsz (p, ofs.1)
val res = !p
prval () = view@(tup) := pffunat(pfat)
} (* end of [tup_get_at_val] *)

implement{t}{a}
tup_set_at (tup, ofs, x) = {
//
val p = addr@(tup)
prval (pfat, pffunat) = offset_at_elim {a,t} (ofs.0, view@(tup))
val p = add_ptr1_bsz (p, ofs.1)
val () = !p := x
prval () = view@(tup) := pffunat(pfat)
//
} (* end of [tup_set_at] *)

implement{t}{a}
tup_set_at_val (tup, ofs, x) = {
//
val p = addr@(tup)
prval (pfat, pffunat) = offset_at_elim {a,t} (ofs.0, view@(tup))
val p = add_ptr1_bsz (p, ofs.1)
val () = !p := x
prval () = view@(tup) := pffunat(pfat)
//
} (* end of [tup_set_at_val] *)

(* ****** ****** *)

local

extern
fun{t:t@ype}
aux {ts:t0ypes} {l:addr} (
  !(t @ l), tuple_of_t0ypes (ts, t) | FILEref, ptr l
) : void

implement
aux<empty> (pfat, pftup | out, p) = fprint (out, ")")

implement(a,b)
aux<(@(a,b))> {ts} (pfat, pftup | out, p) = (
//
prval tuple_cons {a,b} (pftup1) = pftup
val (pfofs1 | ofs1) = offset_pair_snd<a,b> (pfat | p)
prval (pfat1, pf_funat) = offset_at_elim (pfofs1, pfat)
val p1 = add_ptr1_bsz (p, ofs1)
// TODO: print separator?
val () = fprint_ref<a> (out, !p)
val (pfofs2 | ofs2) = aux<b> (pfat1, pftup1 | p1)
prval () = pfat := pf_funat (pfat1)
//
) // end of [aux]

in // in of [local]

implement{t}
tup_fprint {ts} (pf | out, tup) = let
  val () = fprint (out, "(")
  prval () = t0ype_in_t0ypes_index_lemma (pfin)
  val () = aux<t> (view@(tup), pf | addr@(tup))
in
end

end // end of [local]

implement{t}
tup_print {ts} (pf | tup) = tup_fprint<t> (pf | stdout_ref, tup)

end // end of [local]

(* ****** ****** *)

implement
main0 () = let
//
typedef T = @(string, @(float, @(int, empty)))
prval pf = tuple_cons {string} (tuple_cons {float} (tuple_cons {int} (tuple_nil ())))
var t: T = @("hello", @(3.14f, @(1, Empty)))
//
prval pf_in1 = t0ype_in_t0ypes_succ (t0ype_in_t0ypes_zero ())
prval pf_in2 = t0ype_in_t0ypes_succ (t0ype_in_t0ypes_succ (t0ype_in_t0ypes_zero ()))
//
val ofs_f = offset_of<T><float> (pf_in1 | t, 1)
val ofs_i = offset_of<T><int> (pf_in2 | t, 2)
//
var res: float
val () = tup_get_at<T><float> (t, ofs_f, res)
val () = println!("at 1 (bef): ", res)
var _1 = 1.0f
val () = tup_set_at<T><float> (t, ofs_f, _1)
val () = tup_get_at<T><float> (t, ofs_f, res)
val () = println!("at 1 (aft): ", res)
//
val () = println!("at 2 (bef): ", tup_get_at_val<T><int> (t, ofs_i))
val () = tup_set_at_val<T><int> (t, ofs_i, 3)
val () = println!("at 2 (aft): ", tup_get_at_val<T><int> (t, ofs_i))
//
// now, given ts:t0ypes, such that we have t0ypes_t (ts)
// and some t:t@ype, such that tuple_of_t0ypes (ts, t),
// we can at run-time peek inside the structure of [t]!
//
// also of note: with a bit more machinery, we can implement projection
// and union operations on such tuples
// - what about labels? if we can do with labelled tuples, then we can
//   surely embed relational algebra, right?
// - what's a label at runtime? just some atom, providing cheap O(1) equality
//   (certainly not a string!)
// - do we need to keep labels alphabetically sorted in a record? for cheap
//   searching/selection

//
in
end // end of [main0]

// http://www.fing.edu.uy/~mviera/papers/pepm13.pdf
