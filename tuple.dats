#include
"share/atspre_define.hats"
#include
"share/atspre_staload.hats"

staload "libats/SATS/typeval.sats"
staload _ = "libats/DATS/typeval.dats"

// TODO: generic functions on top of flat tuples
// - print, fprint (should be simple?)
// - comparison, equality (only compare two tuples if they have the same type)
// - other stuff
//   - replace an element (done)
//   - concat two tuples (shouldn't be too hard to do)
// - complex stuff of limited utility
//   - project out fields from a tuple (kind of like D4's over/except)
//   - rows (tuples with named fields)
//     - every label is a type or a constant of a given sort
//     - lookup?
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

dataprop TypeEq2 (t@ype, t@ype, bool) =
  | {a:t@ype} TErefl2 (a, a, true)
  | {a,b:t@ype} TEfalse (a, b, false)

// some functions
extern
fun eq_t0ype_t0ype : {a,b:t@ype} (t0ype_t (a), t0ype_t (b)) -> [r:bool] (option_p (TypeEq (a, b), r) | bool r)
overload = with eq_t0ype_t0ype

datasort t0ypes = t0ypes_nil | t0ypes_cons of (t@ype, t0ypes)
datasort lt0ypes = lt0ypes_nil | lt0ypes_cons of (t@ype(*lab*), t@ype(*val*), lt0ypes)

dataprop t0ypes_length (t0ypes, int) =
  | t0ypes_length_zero (t0ypes_nil, 0)
  | {ts:t0ypes;t:t@ype;n:nat}
      t0ypes_length_succ (t0ypes_cons (t, ts), n+1) of t0ypes_length (ts, n)

dataprop lt0ypes_length (lt0ypes, int) =
  | lt0ypes_length_zero (lt0ypes_nil, 0)
  | {ts:lt0ypes;l,t:t@ype;n:nat}
      lt0ypes_length_succ (lt0ypes_cons (l, t, ts), n+1) of lt0ypes_length (ts, n)

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
  | TUPZ (t0ypes_nil, empty)
  | {t:t@ype} {t':t@ype} {ts:t0ypes} TUPS (t0ypes_cons (t, ts), @(t, t')) of tuple_of_t0ypes (ts, t')

dataprop tuple_of_lt0ypes (lt0ypes, t@ype) =
  | LTUPZ (lt0ypes_nil, empty)
  // FIXME: label has not been used already?
  // - proof burden too
  // TODO: get/set: use type equality between a label searched for and the label present
  // - a template function
  // - need a separate judgment for ensuring the label exists in the tuple (there is no way to do otherwise)
  | {l,t:t@ype} {t':t@ype} {ts:lt0ypes} LTUPS (lt0ypes_cons (l, t, ts), @(t, t')) of tuple_of_lt0ypes (ts, t')

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
  | {t,t':t@ype} {ts:t0ypes} TINZ (t, t0ypes_cons (t, ts), @(t, t'), 0)
  | {x:t@ype} {t,t':t@ype} {ts:t0ypes;i:nat;ofs:int}
      TINS (t, t0ypes_cons (t', ts), @(t', x), i+1) of
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
%{^
#define mysub_ptr_ptr(x,y) (((atstype_int)x) - (atstype_int)y)
%}
extern
fun sub_ptr_ptr (ptr, ptr): int = "mac#mysub_ptr_ptr"
//
implement{a}{b}
offset_pair_snd {l} (pfat | p) = (pf | diff1) where {
//
val () = println!("p.0 = ", addr@(!p.0))
val () = println!("p.1 = ", addr@(!p.1))
//
val diff0 = sub_ptr_ptr (addr@(p->1), addr@(p->0))
val diff1 = g1ofg0 (g0int2uint_int_size diff0)
(*
//
val diff0 = g0ofg1(addr@(p->1) - addr@(p->0))
val () = assert_errmsg (diff0 >= 0, "offset_pair_snd: negative offset!")
val () = println!("diff0 = ", diff0)
val diff1 = g1ofg0 (g0int2uint_ssize_size diff0)
*)
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
extern
fun
fprint_offset {a,b:t@ype} (FILEref, Offset_t (a, b)): void
//
extern
fun
print_offset {a,b:t@ype} (Offset_t (a, b)): void
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

overload fprint with fprint_offset
overload print with print_offset

(* ****** ****** *)

extern
fun{t:t@ype}
tup_fprint {ts:t0ypes} (tuple_of_t0ypes (ts, t) | FILEref, tup: &t): void

extern
fun{t:t@ype}
tup_print {ts:t0ypes} (tuple_of_t0ypes (ts, t) | &t): void

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
      prval TINZ {a,b'} () = pfin
      val () = println!("i = 0, ofs = 0")
    in
      (offset_at_zero () | (i2sz)0)
    end else let
      prval TINS {x} {b,b1} (pfin1) = pfin
      val () = $effmask_all (println!("offset_pair_snd called", p, ", i = ", i))
      val (pfofs1 | ofs1) = offset_pair_snd<b1><x> (pfat | p)
      val () = println!("ofs1 = ", ofs1)
      prval (pfat1, pf_funat) = offset_at_elim (pfofs1, pfat)
      val p1 = add_ptr1_bsz (p, ofs1)
      val (pfofs2 | ofs2) = aux<x><a> (pfat1, pfin1 | p1, i-1)
      val () = println!("ofs2 = ", ofs2)
      prval () = pfat := pf_funat (pfat1)
      prval pfres = offset_at_cons (pfofs1, pfofs2)
    in
      (pfres | (ofs1 + ofs2))
    end
  ) // end of [aux]
  val () = println!("aux(p=", addr@(tup), ")")
  prval () = t0ype_in_t0ypes_index_lemma (pfin)
  val (pf_ofs0 | ofs0) = aux<t><a> (view@(tup), pfin | addr@(tup), i)
in
  (pf_ofs0 | ofs0)
end // end of [offset_of]

(* ****** ****** *)

implement
fprint_offset {a,b} (out, ofs) = fprint (out, ofs.1)
implement
print_offset {a,b} (ofs) = fprint_offset (stdout_ref, ofs)

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

(*
local

extern
fun{t:t@ype}
aux {ts:t0ypes} {l:addr} (
  !(t @ l), tuple_of_t0ypes (ts, t) | FILEref, ptr l
) : void

implement
aux<empty> (pfat, pftup | out, p) = fprint (out, ")")

implement(a,b)
aux<(@(a,b))> {ts} (pfat, pftup | out, p) = {
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
} // end of [aux]

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
*)

end // end of [local]

(* ****** ****** *)

// so, seems like the above can't work reliably due to C compiler
// optimizations

extern
fun{t:t@ype}{a:t@ype}{N:type}
tup_get {ts:t0ypes} {i:int} (tieq (N, i), t0ype_in_t0ypes (a, ts, t, i) | &t): a
extern
fun{t:t@ype}{a:t@ype}{N:type}
tup_set {ts:t0ypes} {i:int} (tieq (N, i), t0ype_in_t0ypes (a, ts, t, i) | &t, a): void

typedef tup2 (a:t@ype, b:t@ype) = @(a, b)

implement(A,b)
tup_get<tup2 (A, b)><A><Z()> {ts} {i} (pfti, pfin | tup) = let
  prval TIEQZ() = pfti
  prval TINZ () = pfin
in
  tup.0
end // end of [tup_get]
implement(B,b,A,N)
tup_get<tup2 (B,b)><A><S(N)> {ts} {i} (pfti, pfin | tup) = let
  prval TIEQS(pfti) = pfti
  prval TINS {x} {t,t'} (pfin) = pfin
  prval TErefl () = __trustme () where {
    extern
    prfun
    __trustme (): TypeEq (x, b)
  }
  val res = tup_get<b><A><N> (pfti, pfin | tup.1)
  val () = ignoret(0) // to circumvent a tail-call optimization bug in patsopt!
in
  res
end // end of [tup_get]

implement(A,b)
tup_set<tup2 (A, b)><A><Z()> {ts} {i} (pfti, pfin | tup, x) = let
  prval TIEQZ() = pfti
  prval TINZ () = pfin
in
  tup.0 := x
end // end of [tup_set]
implement(B,b,A,N)
tup_set<tup2 (B,b)><A><S(N)> {ts} {i} (pfti, pfin | tup, x) = let
  prval TIEQS(pfti) = pfti
  prval TINS {x} {t,t'} (pfin) = pfin
  prval TErefl () = __trustme () where {
    extern
    prfun
    __trustme (): TypeEq (x, b)
  }
  val () = tup_set<b><A><N> (pfti, pfin | tup.1, x)
  val () = ignoret(0) // to circumvent a tail-call optimization bug in patsopt!
in
  (*empty*)
end // end of [tup_set]

// t0ype_in_t0ypes (a, ts, x, i) means:
// a is i'th element of tuple x
dataprop lab_in_lt0ypes (t@ype, lt0ypes, int) =
  | {l,t:t@ype} {ts:lt0ypes} LTINZ (l, lt0ypes_cons (l, t, ts), 0)
  | {l,l2:t@ype} {t:t@ype} {ts:lt0ypes;i:nat}
      LTINS (l, lt0ypes_cons (l2, t, ts), i+1) of
        (TypeEq2 (l, l2, false), lab_in_lt0ypes (l, ts, i))

extern
fun{lab:t@ype}
label_tostring (): string

// TODO: getter/setter
extern
fun{t:t@ype}{l:t@ype}{N:type}
ltup_lookup {lts:lt0ypes} {i:int} (lab_in_lt0ypes (l, (*value,*) lts, i), tieq (N, i), tuple_of_lt0ypes (lts, t) | &t): int i

implement(t,l)
ltup_lookup<t><l><Z()> {ts} {i} (pflin, pfti, pftup | tup) = let
  prval TIEQZ() = pfti
  prval LTINZ () = pflin
in
  0
end // end of [ltup_lookup]
implement(a,b,l,N)
ltup_lookup<tup2 (a, b)><l><S(N)> {ts} {i} (pflin, pfti, pftup | tup) = let
  prval TIEQS(pfti) = pfti
  prval LTINS(pfeq, pflin) = pflin
  prval TEfalse() = pfeq
  prval LTUPS {l1,t} {t1} {ts1}  (pftup) = pftup
  prval TErefl () = __trustme () where {
    extern
    prfun
    __trustme (): TypeEq (b, t1)
  }
in
  1 + ltup_lookup<b><l><N> (pflin, pfti, pftup | tup.1)
end // end of [ltup_lookup]

(* ****** ****** *)

local

#define nil t0ypes_nil
#define :: t0ypes_cons

// another idea: introduce some axioms about
// type lists?
// or another one: introduce abstract row sort + axioms
// - ordered!
// - labels are pairwise distinct

stacst eq_t0ype_t0ype : (t@ype, t@ype) -> bool
stadef == = eq_t0ype_t0ype

extern
praxi t0ype_eq_refl {x:t@ype} (): [x == x] void
extern
praxi t0ype_eq_symm {x,y:t@ype | x == y} (): [y == x] void
extern
praxi t0ype_eq_trans {x,y,z:t@ype | x == y; y == z} (): [x == z] void

extern
praxi t0ypes_eq_cons {x:t@ype} {xs1,xs2:t0ypes | xs1 == xs2} (): [x::xs1 == x::xs2] void
extern
praxi t0ypes_eq_refl {xs:t0ypes} (): [xs == xs] void
extern
praxi t0ypes_eq_symm {xs,ys:t0ypes | xs == ys} (): [ys == xs] void
extern
praxi t0ypes_eq_trans {xs,ys,zs:t0ypes | xs == ys; ys == zs} (): [xs == ys] void
//
// what else? membership? t0ypeset?

dataprop mem_t0ypes (t@ype, t0ypes, bool) =
  | {a:t@ype} MEMz (a, nil, false)
  | {a,b:t@ype} {ts:t0ypes} {m1:bool} MEMs (a, b :: ts, a==b || m1) of
      mem_t0ypes (a, ts, m1)

// FIXME: how to derive (int==float) == false?
// int==int
// float==float
// ->?
// if int==float then kaboom!

prval test_mem = MEMs {int,float} (
    MEMz () : mem_t0ypes (int, nil, false)
  ) : mem_t0ypes (int, float::nil, false)

dataprop Void = // NOTE: no cases!
dataprop Unit = Unit of () // NOTE: one case!

stadef Not (p:prop) = p -> Void

// need a function which computes as:
// true -> Unit
// false -> Void
dataprop Dec (p:prop, bool) =
  | yes (p, true) of p
  | no (p, false) of Not (p)

dataprop mem_t0ypes_2 (t@ype, t0ypes, bool) =
  | {a:t@ype} mem_t0ypes_2z (a, nil, false)
  | {a,b:t@ype} {ts:t0ypes} {m,m1:bool} mem_t0ypes_2s (a, b :: ts, a == b || m) of mem_t0ypes_2 (a, ts, m)

dataprop even (int) =
  | Ez (0)
  | {n:nat} Es (n+1) of odd (n)

and odd (int) =
  | {n:nat} Os (n+1) of even (n)

//stadef EvenDec = {n:nat} ():<> Dec (even n)

prfun
lemma1 {n:nat} .<n>. (pf: even (n)): [n >= 0] void =
case+ pf of
| Ez () => ()
| Es (Os pf) => lemma1 (pf)

prfn
lemma2 (pf: even 1): Void =
  case+ pf of
  | Ez () =/=> () // when typechecking this clause, false is assumed, so anything goes
  | Es (Os _) =/=> ()

extern
praxi void_discr : {X:prop} Void -> X

prfun
lemma_odd {n:nat | n == 0} .<n>. (pfn: Not (even n)): even (n+1) =
  //sif n == 0 then
  let
    prval pf = Ez () : even 0
  in
    // can't match on Void!
    // however, in Agda, it seems that the type-checker will simply assume false,
    // but in ATS, it won't! hence this strategy can't work, or so it seems
    void_discr (pfn(pf))
  end
  //else sif n == 1 then 
(*
prfun
bad {n:nat} .<n>. (pf1: even(n), pf2: even(n+1)):<> Void =
  sif n == 0 then (
    case+ pf2 of
    | Ez () =/=> ()
    | Es (Os pf) =/=> (
      case+ pf of
      | Ez () =/=> ()
      | Es (_) =/=> ()
    )
  )
  else sif n == 1 then (
    case+ pf1 of
    | Ez () =/=> ()
    | Es (Os _) =/=> ()
  )
  else let
    prval Es (Os pf1) = pf1
    prval Es (Os pf2) = pf2
  in
    bad {n-2} (pf1, pf2)
  end*)

(*
prfun
refute {X:prop | int == char} (): X =
  // int == char
  // int == int
*)
dataprop in_t0ypes (l:t@ype, a:t@ype, t0ypes, (*t0ypes,*) int) =
  | {ls(*,ts*):t0ypes} INTz (l, a, l::ls, (*a::ts,*) 0)
  | {l1,b:t@ype} {ls(*,ts*):t0ypes} {n:nat} INTs (l, a, l1::ls, (*b::ts,*) n+1) of in_t0ypes (l, a, ls, (*ts,*) n)

(*
extern
prfun
mem_lemma1 {a:t@ype} {ts:t0ypes}
(mem (a, ts, true)): [i:int] in_t0ypes (a, ts, i)
*)

// at length(pre) you can also locate the type of said label

dataprop t0ypeset (t0ypes) =
  | TSnil (nil)
  | {a:t@ype} {ts:t0ypes} TScons (a::ts) of
      (mem_t0ypes (a, ts, false), t0ypeset (ts))

dataprop zip_t0ypes (t0ypes, t0ypes) =
  | ZIPnil (nil, nil)
  | {a1,a2:t@ype} {ts1,ts2:t0ypes} ZIPcons (a1::ts1, a2::ts2) of zip_t0ypes (ts1, ts2)
(*
datasort row =
  | row_nil of ()
  | row_cons of (t@ype(*lab*), t@ype(*value*), row)

dataprop lab_disjoint (t@ype, row) =
  | {l:t@ype} LDnil (l, row_nil)
  | {l1,l2:t@ype;r:row | l1 == l2} LDcons (l1, row_cons (l2, r)) of lab_disjoint (l1, r)

// row is well-formed
dataprop row_wf (row) =
  | RWFnil (row_nil)
  | {l,a:t@ype;r:row} RWFcons (row_cons (l, a, r)) of (lab_disjoint (l, r), row_wf (r))

// how does the type change with the row?
dataprop row_type (row, t@ype) =
  | RTnil (row_nil, empty)
  | {l,a,t:t@ype;r:row} RTcons (row_cons (l, a, r), @(a, t)) of row_type (r, t)

propdef row_p (ls:t0ypes, ts:t0ypes, l:t@ype, r:t@ype) = '{
  pflab= t0ypeset (ls)
, pfls= tuple_of_t0ypes (ls, l)
, pfts= tuple_of_t0ypes (ts, r)
, pfzip= zip_t0ypes (ls, ts)
} // end of [row_p]

extern
fun{r:t@ype}{l:t@ype}{L:t@ype}{A:t@ype}{N:type}
row_get_imp {ls,ts:t0ypes} {n:int} (row_p (ls, ts, l, r), in_t0ypes (L, A, ls, (*ts,*) n), tieq (N, n) | &r): A
//
implement(r,L,Ls,l2,a,b)
row_get_imp<tup2(a,b)><tup2(L, Ls)><L><a><Z()> {ls,ts} (pfr, pfin, pfti | tup) = let
  prval TIEQZ () = pfti
  prval INTz () = pfin
in
  tup.0
end // end of [row_get_imp]
implement(r,L1,L2,Ls,l2,a,b,c,N)
row_get_imp<tup2(b,c)><tup2(L1,Ls)><L2><a><S(N)> {ls,ts} (pfr, pfin, pfti | tup) = let
  prval TIEQS (pfti) = pfti
  prval INTs (pfin) = pfin
  // transform the row too!
  prval TScons(pfmem, pflab1) = pfr.pflab
  prval TUPS {L1_} {Ls_} {ls1} (pfls1) = pfr.pfls
  prval ZIPcons(pfzip1) = pfr.pfzip
  prval TUPS {b_} {c_} {ts1} (pfts1) = pfr.pfts
  prval pfr1 = '{pflab= pflab1, pfls= pfls1, pfts= pfts1, pfzip= pfzip1}
  prval TErefl () = __trustme () where {
    extern prfun __trustme (): TypeEq (c, c_)
  }
  prval TErefl () = __trustme () where {
    extern prfun __trustme (): TypeEq (Ls, Ls_)
  }
in
  row_get_imp<c><Ls><L2><a><N> (pfr1, pfin, pfti | tup.1)
end // end of [row_get_imp]

typedef row_t (r:t@ype, ls:t0ypes, ts:t0ypes) = [l:t@ype] @(row_p (ls, ts, l, r) | r)

// another idea: just use proof objects as labels, seriously
// or like this: prfun template (label to proof object)
// and then client supplies labels (of different kinds), and we get back the proofs

// another, similar idea: fuse labels+types together
// then we need one less index into the row
// 

extern
fun{r:t@ype}{l:t@ype}{L:t@ype}{A:t@ype}
row_get {ls,ts:t0ypes} {n:int} (in_t0ypes (L, A, ls, (*ts,*) n) | &row_t (r, ls, ts)): A


//
datatype L1 = L1
datatype L2 = L2
datatype L3 = L3
//
*)

in // in of [local]

fun
test_new (): void = ()

end // end of [local]

(* ****** ****** *)

implement
main0 () = let
//
typedef T = @(string, @(float, @(int, empty)))
prval pf = TUPS {string} (TUPS {float} (TUPS {int} (TUPZ ())))
var t: T = @("hello", @(3.14f, @(1, Empty)))
//
prval pf_in0 = TINZ ()
prval pf_in1 = TINS (TINZ ())
prval pf_in2 = TINS (TINS (TINZ ()))
//
#define _t0 TIEQZ()
#define _t1 TIEQS(_t0)
#define _t2 TIEQS(_t1)
//
val () = {
//
val () = println!("new code BEG")
val () = println!("tup_get(0) = ", tup_get<T> (_t0, pf_in0 | t))
val () = println!("tup_get(1) = ", tup_get<T> (_t1, pf_in1 | t))
val () = println!("tup_get(2) = ", tup_get<T> (_t2, pf_in2 | t))
//
val () = tup_set<T> (_t0, pf_in0 | t, "world")
val () = tup_set<T> (_t1, pf_in1 | t, 0.1f)
val () = tup_set<T> (_t2, pf_in2 | t, 5)
//
val () = println!("assignments done")
//
val () = println!("tup_get(0) = ", tup_get<T> (_t0, pf_in0 | t))
val () = println!("tup_get(1) = ", tup_get<T> (_t1, pf_in1 | t))
val () = println!("tup_get(2) = ", tup_get<T> (_t2, pf_in2 | t))
//
val () = println!("new code END")
} // end of [val]
//
val () = {
//
val () = println!("labelled tuples BEG")
// define labels
abstype L1
abstype L2
abstype L3
//
implement
label_tostring<L1> () = "L1"
implement
label_tostring<L2> () = "L2"
implement
label_tostring<L3> () = "L3"
//
// defined the labelled 3-tuple
prval pf = LTUPS {L1,string} (LTUPS {L2,float} (LTUPS {L3,int} (LTUPZ ())))
//
prval pf_in0 = LTINZ ()
prval pf_in1 = LTINS (TEfalse(), LTINZ ())
prval pf_in2 = LTINS (TEfalse(), LTINS (TEfalse (), LTINZ ()))
//
val () = println!(label_tostring<L3>(), " at ", ltup_lookup (pf_in2, _t2, pf | t))
val () = println!(label_tostring<L2>(), " at ", ltup_lookup (pf_in1, _t1, pf | t))
val () = println!(label_tostring<L1>(), " at ", ltup_lookup (pf_in0, _t0, pf | t))
//
val () = println!("labelled tuples END")
//
} // end of [val]
//
val () = println!("sizeof(T) = ", sizeof<T>)
//
val ofs_s = offset_of<T><string> (pf_in0 | t, 0)
val ofs_f = offset_of<T><float> (pf_in1 | t, 1)
val ofs_i = offset_of<T><int> (pf_in2 | t, 2)
//
val () = println!("offsetof(T,0) = ", ofs_s)
val () = println!("offsetof(T,1) = ", ofs_f)
val () = println!("offsetof(T,2) = ", ofs_i)
//
var it: int
val () = tup_get_at<T><int> (t, ofs_i, it)
val () = println!("at 2 (bef): ", it)
val () = it := 3
val () = tup_set_at<T><int> (t, ofs_i, it)
val () = tup_get_at<T><int> (t, ofs_i, it)
val () = println!("at 2 (aft): ", it)
//
var res: float
val () = tup_get_at<T><float> (t, ofs_f, res)
val () = println!("at 1 (bef): ", res)
var _1 = 1.0f
val () = tup_set_at<T><float> (t, ofs_f, _1)
val () = tup_get_at<T><float> (t, ofs_f, res)
val () = println!("at 1 (aft): ", res)
(*
//
val () = println!("at 0 (bef): ", tup_get_at_val<T><string> (t, ofs_s))
val () = tup_set_at_val<T><string> (t, ofs_s, "world")
val () = println!("at 0 (aft): ", tup_get_at_val<T><string> (t, ofs_s))
*)
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
