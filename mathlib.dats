(*
** A templated vector lib
*)

(* ****** ****** *)

#include
"share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "libats/SATS/typeval.sats"

(* ****** ****** *)

staload _ = "libats/DATS/typeval.dats"

(* ****** ****** *)

vtypedef
RD(a:vt0p) = a // for commenting: read-only

(* ****** ****** *)

// TODO: wrap the array into a struct,
// so that we can return it from functions by value?
// (until the ATS2 compiler supports this)
abst@ype vec_t (a:t@ype, n:int) = @[a][n]

extern
prfun
vec_from_arr_v
  {a:t@ype}{n:int}{l:addr}
  (array_v (a, l, n)): vec_t (a, n) @ l
extern
prfun
arr_from_vec_v
  {a:t@ype}{n:int}{l:addr}
  (vec_t (a, n) @ l): array_v (a, l, n)

extern
fun{a:t@ype}
vec_init2 (&vec_t (a, 2)? >> _, a, a): void
extern
fun{a:t@ype}
vec_init3 (&vec_t (a, 3)? >> _, a, a, a): void
extern
fun{a:t@ype}
vec_init4 (&vec_t (a, 4)? >> _, a, a, a, a): void

extern
fun{a:t@ype}
vec_get_x {n:pos} (&RD(vec_t (INV(a), n))): a
extern
fun{a:t@ype}
vec_get_y {n:nat | n > 1} (&RD(vec_t (INV(a), n))): a
extern
fun{a:t@ype}
vec_get_z {n:nat | n > 2} (&RD(vec_t (INV(a), n))): a
extern
fun{a:t@ype}
vec_get_w {n:nat | n > 3} (&RD(vec_t (INV(a), n))): a

extern
fun{a:t@ype}
vec_set_x {n:pos} (&vec_t (INV(a), n), a): void
extern
fun{a:t@ype}
vec_set_y {n:nat | n > 1} (&vec_t (INV(a), n), a): void
extern
fun{a:t@ype}
vec_set_z {n:nat | n > 2} (&vec_t (INV(a), n), a): void
extern
fun{a:t@ype}
vec_set_w {n:nat | n > 3} (&vec_t (INV(a), n), a): void

extern
fun{a:t@ype}
vec_get_at_int {n:nat} (&RD(vec_t (INV(a), n)), natLt (n)): a
extern
fun{a:t@ype}
vec_set_at_int {n:nat} (&RD(vec_t (INV(a), n)), natLt (n), a):<!wrt> void

// AS: note that as HX said, we are better off
// capturing the unrolled loop as a common template,
// and then just providing separate functions for 2, 3, 4 elements
// (these would be implemented as just instantiations
// of the template)
//
// finally, the functions vec_add2, vec_add3, vec_add4
// can be given a common name
extern
fun{a:t@ype}{N:type}
vec_add {n:nat} (
  pf: tieq (N, n)
| &RD(vec_t (INV(a), n)), &RD(vec_t (INV(a), n)), &vec_t (a, n)? >> _
): void

extern
fun{a:t@ype}{N:type}
vec_sub {n:nat} (
  pf: tieq (N, n)
| &RD(vec_t (INV(a), n)), &RD(vec_t (INV(a), n)), &vec_t (a, n)? >> _
): void

extern
fun{a:t@ype}{N:type}
vec_scale {n:nat} (
  pf: tieq (N, n)
| a, &RD(vec_t (INV(a), n)), &vec_t (a, n)? >> _
): void

// what about composing operations like the above?
// e.g.:
//   c = a + f * b
// maps to:
//   scale (f, b, tmp);
//   add (a, tmp, c)
// or even (as in expr. templates):
//   implement vec_move4$fwork<float> (i) = a.[i] + f * b.[i]
//   val () = vec_move4<float> (c) // fun{a:t@ype} vec_move4 : (&vec_t (a, 4)? >> _): void
// or actually (the way it's currently done):
//   implement vec_map2<float> (a, b) = a + f * b
//   val () = vec_map2<float><_> (_ | a, b, c)
//
// assuming scale have the type
//   (scalar, &INV(vec3), &vec3? >> _): void

// c = a + f * b -->
// eval (add (a, scale (f, b)), c)
// 1. for exptemps we want to put arrays as pointers/references
// 2. we don't want no memory allocation, please
//    @(float, arrayref (float, 4))
// 3. make the expression a linear object?
//    - temporarily consume vec_t operands?
// 4. arrayref is non-linear, but we are bound to have some issues with it
//    - involves GC
//    - the expression object must not outlive any of the arrays it has links to
//    - solution? @(float, ptr l)

(*implement
vec_move_env$fwork<float> {env} (pf, env | i) = {
  val () = vec_get_i<float> (v1, i) + 2.0f * vec_get_i<float> (v2, i)
} // end of [vec_move_env]

so OK, seems like the above plan won't quite pan out
- proofs need to be threaded through the computation
- I need a way to lift n-ary functions over vectors then
- n-ary function like f: (a, a) -> a
  - implement apply$fwork<float> (v1, v2) = v1 + f * v2
  - val () = apply (v1, v2, v3)
- we just need to give the user a tuple! e.g.
extern
fun testtup (@(int, int)): void
implement
testtup (@(x, y)) = println!(x, y)

What if the user just gave as an expression (as an object), and we'd apply it ourselves
to all elements of a vector, producing the corresponding element of an output vector?
- that might work!
- the arrays still have to be accessed somehow (environment)

<$> : (a->b) -> F a -> F b
pure : a -> F a
<*> : F (a -> b) -> F a -> F b

f : a -> a -> a
x, y : F a

(f <$> x) : F (a -> a)
((f <$> x) <*> y) : F a

fmap : (a->b, F a) -> F b
pure : a -> F a
app : (F (a -> b), F a) -> F b
*)

extern
fun{a:t@ype}
vec_map1$fwork (a): a
extern
fun{a:t@ype}{N:type}
vec_map1 {n:int} (
  pf: tieq (N, n)
| &RD(vec_t (INV(a), n)), &vec_t (a, n)? >> _
) : void

extern
fun{a:t@ype}
vec_map2$fwork (a, a): a
extern
fun{a:t@ype}{N:type}
vec_map2 {n:int} (
  pf: tieq (N, n)
| &RD(vec_t (INV(a), n)), &RD(vec_t (INV(a), n)),  &vec_t (a, n)? >> _
) : void

extern
fun{a:t@ype}
vec_map3$fwork (a, a, a): a
extern
fun{a:t@ype}{N:type}
vec_map3 {n:int} (
  pf: tieq (N, n)
| &RD(vec_t (INV(a), n)), &RD(vec_t (INV(a), n)), &RD(vec_t (INV(a), n)), &vec_t (a, n)? >> _
) : void

(*
another idea, taken from ATS2 book, chapter on loop construction
http://ats-lang.sourceforge.net/DOCUMENT/INT2PROGINATS/CODE/CHAP_FNTMPINT/loopcons.dats

// we can't tell if the passed in index is inside the bounds of the array...
extern
fun{a:t@ype}{env:int->vt@ype}
vec_map_env$fwork {i,n:int | i >= n; i < n} (int(i), &(env(n)) >> _): a
// we could, I think, use stack-allocated closures for this, though

TODO: wrap arrays into structs so we can return them directly from functions
*)

extern
fun{a:t@ype}{N:type}
vec_map_clo
  {v:view}
  {n:int}
(
  pf: tieq (N, n),
  pfv: !v
| vec: &vec_t (a, n)? >> _, f: &(!v | natLt(n)) -<clo1> a
) : void // end of [vec_map_clo]

extern
fun{a:t@ype}
vec_map_clo2 {v:view} {n:int} (
  !v | &vec_t (a, 2)? >> _, &(!v | natLt(2)) -<clo1> a
) : void // end of [vec_map_clo2]

extern
fun{a:t@ype}
vec_map_clo3 {v:view} {n:int} (
  !v | &vec_t (a, 3)? >> _, &(!v | natLt(3)) -<clo1> a
) : void // end of [vec_map_clo3]

extern
fun{a:t@ype}
vec_map_clo4 {v:view} {n:int} (
  !v | &vec_t (a, 4)? >> _, &(!v | natLt(4)) -<clo1> a
) : void // end of [vec_map_clo4]

// the final solution is also the most obvious one
extern
fun{
a:t@ype}{env:vt@ype
} vec_map_env3$fwork
(natLt(3), &(env) >> _): a

extern
fun{
a:t@ype}{env:vt@ype
} vec_map_env3 (
  vec: &vec_t (a, 3)? >> _
, env: &(env) >> _
) : void // end of [vec_map_env3]

(* ****** ****** *)

local

assume vec_t (a:t@ype, n:int) = @[a][n]

in // in of [local]

implement{a}
vec_init2 (v, x, y) = {
//
#define :: array_v_cons
//
var pv = addr@(v)
prval (pf1_at, pf1_arr) = array_v_uncons {a?} (view@(v))
val () = ptr_set<a> (pf1_at | pv, x)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf2_at, pf2_arr) = array_v_uncons {a?} (pf1_arr)
val () = ptr_set<a> (pf2_at | pv, y)
//
prval pf2_arr = array_v_unnil_nil (pf2_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf2_arr
//
} (* end of [vec_init2] *)
implement{a}
vec_init3 (v, x, y, z) = {
//
#define :: array_v_cons
//
var pv = addr@(v)
prval (pf1_at, pf1_arr) = array_v_uncons {a?} (view@(v))
val () = ptr_set<a> (pf1_at | pv, x)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf2_at, pf2_arr) = array_v_uncons {a?} (pf1_arr)
val () = ptr_set<a> (pf2_at | pv, y)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf3_at, pf3_arr) = array_v_uncons {a?} (pf2_arr)
val () = ptr_set<a> (pf3_at | pv, z)
//
prval pf3_nil = array_v_unnil_nil (pf3_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf3_at :: pf3_nil
//
} (* end of [vec_init3] *)
//
implement{a}
vec_init4 (v, x, y, z, w) = {
//
#define :: array_v_cons
//
var pv = addr@(v)
prval (pf1_at, pf1_arr) = array_v_uncons {a?} (view@(v))
val () = ptr_set<a> (pf1_at | pv, x)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf2_at, pf2_arr) = array_v_uncons {a?} (pf1_arr)
val () = ptr_set<a> (pf2_at | pv, y)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf3_at, pf3_arr) = array_v_uncons {a?} (pf2_arr)
val () = ptr_set<a> (pf3_at | pv, z)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf4_at, pf4_arr) = array_v_uncons {a?} (pf3_arr)
val () = ptr_set<a> (pf4_at | pv, z)
//
prval pf4_nil = array_v_unnil_nil (pf4_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf3_at :: pf4_at :: pf4_nil
//
} (* end of [vec_init4] *)
//
(* ****** ****** *)
//
implement{a} vec_get_x (v) = v.[0]
implement{a} vec_get_y (v) = v.[1]
implement{a} vec_get_z (v) = v.[2]
implement{a} vec_get_w (v) = v.[3]
//
implement{a} vec_set_x (v, a) = v.[0] := a
implement{a} vec_set_y (v, a) = v.[1] := a
implement{a} vec_set_z (v, a) = v.[2] := a
implement{a} vec_set_w (v, a) = v.[3] := a
//
implement{a}
vec_get_at_int {n} (v, i) = v.[i]
implement{a}
vec_set_at_int {n} (v, i, x) = v.[i] := x
//
(* ****** ****** *)
//
implement{a}{N} vec_add (pf | a, b, c) = {
//
implement vec_map2$fwork<a> (a, b) = gadd_val_val<a> (a, b)
val () = vec_map2<a><N> (pf | a, b, c)
//
} (* end of [vec_add] *)
//
implement{a}{N} vec_scale (pf | s, v, b) = {
//
implement vec_map1$fwork<a> (a) = gmul_val_val<a> (s, a)
val () = vec_map1<a><N> (pf | v, b)
//
} (* end of [vec_scale] *)
//
(* ****** ****** *)
//
implement{a}{N0}
vec_map1 {n0} (pf0 | v0, res) = {
//
extern
fun{N:type}
loop {n:int} (
  pf: tieq (N, n) | &INV(vec_t (a, n)), &vec_t (a, n)? >> _
): void
//
implement
loop<Z()> {n} (pf | va, res) = {
//
prval TIEQZ() = pf
and () = view@(res) := array_v_unnil_nil (view@(res))
//
} (* end of [loop<Z()>] *)
//
implement(N)
loop<S(N)> {n} (pf | va, res) = {
//
prval TIEQS(pf) = pf
//
val pva = addr@(va)
and pres = addr@(res)
//
prval (pfva_at, pfva_arr1) = array_v_uncons (view@(va))
and (pfres_at, pfres_arr1) = array_v_uncons (view@(res))
//
val () = !pres := vec_map1$fwork<a> (!pva)
//
val (pfva_arr1 | pva_1) = viewptr_match (pfva_arr1 | ptr1_succ<a> (pva))
and (pfres_arr1 | pres_1) = viewptr_match (pfres_arr1 | ptr1_succ<a> (pres))
//
val () = loop<N> (pf | !pva_1, !pres_1)
//
prval () = view@(va) := array_v_cons (pfva_at, pfva_arr1)
and () = view@(res) := array_v_cons (pfres_at, pfres_arr1)
//
} (* end of [loop<S(N)>] *)
//
val () = loop<N0> (pf0 | v0, res)
//
} // end of [vec_map1]
//
(* ****** ****** *)
//
local
//
extern
fun{a:t@ype}{N:type}
loop {n:int} (
  pf: tieq (N, n) | &RD(vec_t (INV(a), n)), &RD(vec_t (INV(a), n)), &vec_t (a, n)? >> _
): void
//
implement(a)
loop<a><Z()> {n} (pf | va, vb, res) = {
//
prval TIEQZ() = pf
and () = view@(res) := array_v_unnil_nil (view@(res))
//
} (* end of [loop<Z()>] *)
//
implement(a,N)
loop<a><S(N)> {n} (pf | va, vb, res) = {
//
prval TIEQS(pf) = pf
//
val pva = addr@(va)
and pvb = addr@(vb)
and pres = addr@(res)
//
prval (pfva_at, pfva_arr1) = array_v_uncons (view@(va))
and (pfvb_at, pfvb_arr1) = array_v_uncons (view@(vb))
and (pfres_at, pfres_arr1) = array_v_uncons (view@(res))
//
val () = !pres := vec_map2$fwork<a> (!pva, !pvb)
//
val (pfva_arr1 | pva_1) = viewptr_match (pfva_arr1 | ptr1_succ<a> (pva))
and (pfvb_arr1 | pvb_1) = viewptr_match (pfvb_arr1 | ptr1_succ<a> (pvb))
and (pfres_arr1 | pres_1) = viewptr_match (pfres_arr1 | ptr1_succ<a> (pres))
//
val () = loop<a><N> (pf | !pva_1, !pvb_1, !pres_1)
//
prval () = view@(va) := array_v_cons (pfva_at, pfva_arr1)
and () = view@(vb) := array_v_cons (pfvb_at, pfvb_arr1)
and () = view@(res) := array_v_cons (pfres_at, pfres_arr1)
//
} (* end of [loop<S(N)>] *)
//
in // in of [local]
//
implement{a}{N0}
vec_map2 {n0} (pf0 | v0, v1, res) = {
//
val () = loop<a><N0> (pf0 | v0, v1, res)
//
} // end of [vec_map2]
//
end // end of [local]
//
(* ****** ****** *)
//
implement{a}{N0}
vec_map3 {n0} (pf0 | v0, v1, v2, res) = {
//
extern
fun{N:type}
loop {n:int} (
  pf: tieq (N, n)
| &INV(vec_t (a, n)), &INV(vec_t (a, n)), &INV(vec_t (a, n)), &vec_t (a, n)? >> _
): void
//
implement
loop<Z()> {n} (pf | va, vb, vc, res) = {
//
prval TIEQZ() = pf
and () = view@(res) := array_v_unnil_nil (view@(res))
//
} (* end of [loop<Z()>] *)
//
implement(N)
loop<S(N)> {n} (pf | va, vb, vc, res) = {
//
prval TIEQS(pf) = pf
//
val pva = addr@(va)
and pvb = addr@(vb)
and pvc = addr@(vc)
and pres = addr@(res)
//
prval (pfva_at, pfva_arr1) = array_v_uncons (view@(va))
and (pfvb_at, pfvb_arr1) = array_v_uncons (view@(vb))
and (pfvc_at, pfvc_arr1) = array_v_uncons (view@(vc))
and (pfres_at, pfres_arr1) = array_v_uncons (view@(res))
//
val () = !pres := vec_map3$fwork<a> (!pva, !pvb, !pvc)
//
val (pfva_arr1 | pva_1) = viewptr_match (pfva_arr1 | ptr1_succ<a> (pva))
and (pfvb_arr1 | pvb_1) = viewptr_match (pfvb_arr1 | ptr1_succ<a> (pvb))
and (pfvc_arr1 | pvc_1) = viewptr_match (pfvc_arr1 | ptr1_succ<a> (pvc))
and (pfres_arr1 | pres_1) = viewptr_match (pfres_arr1 | ptr1_succ<a> (pres))
//
val () = loop<N> (pf | !pva_1, !pvb_1, !pvc_1, !pres_1)
//
prval () = view@(va) := array_v_cons (pfva_at, pfva_arr1)
and () = view@(vb) := array_v_cons (pfvb_at, pfvb_arr1)
and () = view@(vc) := array_v_cons (pfvc_at, pfvc_arr1)
and () = view@(res) := array_v_cons (pfres_at, pfres_arr1)
//
} (* end of [loop<S(N)>] *)
//
val () = loop<N0> (pf0 | v0, v1, v2, res)
//
} // end of [vec_map3]
//
(* ****** ****** *)
//
implement{a}{N}
vec_map_clo {v}{n} (pf, pfv | res, f) = {
//
fun
loop {v:view} {i,n:nat | i <= n} (
  pfv: !v
| res: &vec_t (INV(a), n-i)? >> _, f: &(!v | natLt(n)) -<clo1> a, i: int i, n: int n
) : void =
if i < n then {
  val pres = addr@(res)
  prval (pfres_at, pfres_arr1) = array_v_uncons (view@(res))
  val () = !pres := f (pfv | i)
  val (pfres_arr1 | pres_1) = viewptr_match (pfres_arr1 | ptr1_succ<a> (pres))
  val () = loop (pfv | !pres_1, f, i+1, n)
  prval () = view@(res) := array_v_cons (pfres_at, pfres_arr1)
} else {
  prval () = view@(res) := array_v_unnil_nil (view@(res))
} (* end of [loop] *)
//
val n = tieq_to_int1<N> (pf | (*void*))
prval () = lemma_tieq_param (pf)
val () = loop (pfv | res, f, 0, n)
//
} // end of [vec_map_clo]
//
implement{a}
vec_map_clo2 {v} (pfv | res, f) = {
  prval pf = TIEQS(TIEQS(TIEQZ()))
  val () = vec_map_clo<a><fS(2)> (pf, pfv | res, f)
} (* end of [vec_map_clo2] *)
//
implement{a}
vec_map_clo3 {v} (pfv | res, f) = {
  prval pf = TIEQS(TIEQS(TIEQS(TIEQZ())))
  val () = vec_map_clo<a><fS(3)> (pf, pfv | res, f)
} (* end of [vec_map_clo3] *)
//
implement{a}
vec_map_clo4 {v} (pfv | res, f) = {
  prval pf = TIEQS(TIEQS(TIEQS(TIEQS(TIEQZ()))))
  val () = vec_map_clo<a><fS(4)> (pf, pfv | res, f)
} (* end of [vec_map_clo3] *)
//
(* ****** ****** *)
//
implement{a}{env}
vec_map_env3 (v, env) = {
//
#define :: array_v_cons
//
var pv = addr@(v)
prval (pf1_at, pf1_arr) = array_v_uncons {a?} (view@(v))
val x = vec_map_env3$fwork (0, env)
val () = ptr_set<a> (pf1_at | pv, x)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf2_at, pf2_arr) = array_v_uncons {a?} (pf1_arr)
val y = vec_map_env3$fwork (1, env)
val () = ptr_set<a> (pf2_at | pv, y)
//
val () = pv := ptr_succ<a?> (pv)
prval (pf3_at, pf3_arr) = array_v_uncons {a?} (pf2_arr)
val z = vec_map_env3$fwork (2, env)
val () = ptr_set<a> (pf3_at | pv, z)
//
prval pf3_nil = array_v_unnil_nil (pf3_arr)
prval () = view@(v) := pf1_at :: pf2_at :: pf3_at :: pf3_nil
//
} (* end of [vec_map_env3] *)
//
(* ****** ****** *)
//
end // end of [local]
//
(* ****** ****** *)

overload .init with vec_init2
overload .init with vec_init3
overload .init with vec_init4

overload .x with vec_get_x
overload .y with vec_get_y
overload .z with vec_get_z
overload .w with vec_get_w

overload .x with vec_set_x
overload .y with vec_set_y
overload .z with vec_set_z
overload .w with vec_set_w

overload [] with vec_get_at_int of 0
overload [] with vec_set_at_int of 0

(* ****** ****** *)
//
typedef i2 = natLt(2)
typedef i3 = natLt(3)
typedef i4 = natLt(4)
//
typedef vec2_t (a:t@ype) = vec_t (a, 2)
typedef vec3_t (a:t@ype) = vec_t (a, 3)
typedef vec4_t (a:t@ype) = vec_t (a, 4)
//
typedef vec2f = vec2_t (float)
typedef vec3f = vec3_t (float)
typedef vec4f = vec4_t (float)
//
(* ****** ****** *)
//
fun foo
(
  res: &vec3f? >> _
) : void = {
//
var v1: vec3f
val () = v1.init (1.0f, 0.0f, 0.0f)
var v2: vec3f
val () = v2.init (0.0f, 1.0f, 0.0f)
var v3: vec3f
val () = v3.init (0.0f, 0.0f, 1.0f)
//
prval pfv = (view@(v1), view@(v2), view@(v3))
val () = vec_map_clo3 {V} (pfv | res, f) where {
  viewdef V = (vec3f @ v1, vec3f @ v2, vec3f @ v3)
  var f = lam@ (pf: !V >> _ | i: i3): float =>
    10.0f * v1[i] + 2.0f * v2[i] + 0.5f * v3[i]
  // end of [f]
} // end of [val]
prval () = view@(v1) := pfv.0
and () = view@(v2) := pfv.1
and () = view@(v3) := pfv.2
//
} // end of [foo]
//
fun bar
(
): void = {
//
var v1: vec3f
val () = v1.init (1.0f, 0.0f, 0.0f)
var v2: vec3f
val () = v2.init (0.0f, 1.0f, 0.0f)
var v3: vec3f
//
// I think this is much better than the previous solution!
// - we don't have to annotate the types of arguments or results
// - there is no use of closures, even the stack allocated ones
// - it (should) compile to a simple loop; no vector temporaries involved
// - it is fully type-safe
// - it is more flexible than the lifting-based approach
// INV:
// - "Read-only data types (sources) can be covariant;
//   write-only data types (sinks) can be contravariant.
//   Mutable data types which act as both sources and
//   sinks should be invariant."
// from HX:
(*
INV is for invariant.

It is essentially marker for typechecking.

For instance, say you have a funtion foo
declared as follows:

fun{a:t@ype} foo (xs: list0 (INV(a))): void

Assume that mylst is of the type list0 (T) for some T.
When typechecking foo(mylst), the typechecker will expand
the expression as follows by picking a placeholder T1:

foo<T1>(mylst)

where T <= T1 is assumed.

Say that foo2 is declared as follows:

fun{a:t@ype} foo2 (xs: list0 (INV(a))): void

When foo2(mylst) is typechecked, the typechecker simply
expands the expression to foo2<T>(mylst).
*)
var env = @(view@ v1, view@ v2 | ())
vtypedef VT = @(vec3f @ v1, vec3f @ v2 | void)
(*
// FIXME: this template is not found!
implement
vec_map_env3$fwork<float><VT> (i, env) =
  10.0f * v1[i] + 2.0f * v2[i]
// end of [vec_map_env3$fwork]
val () = vec_map_env3<float><VT> (v3, env)
*)
prval () = view@ v1 := env.0
and () = view@ v2 := env.1
//
} // end of [bar]
//
(* ****** ****** *)
//
implement
main0 () = {
//
//var v = @[float][4](1.0f, 0.0f, 0.0f, 1.0f)
//prval pfvec = vec_from_arr_v {float} (view@(v))
//
var v1: vec4f and v2: vec4f
var v3: vec4f
val () = v1.init (1.0f, 0.0f, 0.0f, 1.0f)
val () = v2.init (0.0f, 1.0f, 0.0f, 1.0f)
//
val () = println!("x = ", v1.x())
val () = println!("y = ", v1.y())
val () = println!("z = ", v1.z())
val () = println!("w = ", v1.w())
//
(*
// gives segfault, why???
// seems like stack overflow: the compiled function loops indefinitely
// _057_home_057_artyom_057_proj_057_ATS_055_playground_057_mathlib_056_dats__loop__22__1
// - there is condition at the start of the loop
prval pf4 = TIEQS (TIEQS (TIEQS (TIEQS (TIEQZ ()))))
val () = vec_map2<float><fS(4)> (pf4 | v1, v2, v3) where {
  implement vec_map2$fwork<float> (v1, v2) = v1 + 2.0f * v2
} // end of [val]
*)
//
var v3_2: vec3f
val () = foo (v3_2)
val () = println! ("[foo] exited")
val () = println! ("x = ", v3_2.x())
val () = println! ("y = ", v3_2.y())
val () = println! ("z = ", v3_2.z())
val () = bar ()
//
//prval () = view@(v) := arr_from_vec_v (pfvec)
//
} (* end of [main0] *)
